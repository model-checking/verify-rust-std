// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
import { readFileSync, realpathSync } from 'node:fs';
import { resolve, sep } from 'node:path';
import { createHash } from 'node:crypto';

export function check(condition, message) {
  if (!condition) throw new Error(message);
}
export const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
export const text = value => typeof value === 'string' && value.length > 0;
export const integer = value => Number.isSafeInteger(value) && value >= 0;
export const compare = (a, b) => a < b ? -1 : a > b ? 1 : 0;
export const canonical = value => Array.isArray(value) ? value.map(canonical)
  : object(value) ? Object.fromEntries(Object.keys(value).sort(compare).map(k => [k, canonical(value[k])])) : value;
export const serialize = value => `${JSON.stringify(canonical(value), null, 2)}\n`;
export const readJSON = path => {
  try { return JSON.parse(readFileSync(path, 'utf8')); }
  catch (error) { throw new Error(`${path}: ${error.message}`); }
};
export function args(names, flags = []) {
  const result = {};
  for (let i = 2; i < process.argv.length; i++) {
    const key = process.argv[i];
    check(names.includes(key) || flags.includes(key), `Unknown argument ${key}`);
    check(!(key in result), `Repeated argument ${key}`);
    result[key] = flags.includes(key) ? true : process.argv[++i];
    check(result[key] && !String(result[key]).startsWith('--'), `Missing value for ${key}`);
  }
  for (const name of names) check(result[name], `Required argument: ${name}`);
  return result;
}
export function reasonInfo(raw) {
  check(text(raw) || (object(raw) && Object.keys(raw).length === 1), 'Invalid skip reason structure');
  const kind = typeof raw === 'string' ? raw : Object.keys(raw)[0];
  const payload = typeof raw === 'string' ? undefined : raw[kind];
  if (kind === 'GenericFn' && payload !== undefined) check(typeof payload === 'string', 'GenericFn payload must be a string');
  if (['MissingArbitraryImpl', 'RequiresBoundedArguments'].includes(kind)) {
    check(Array.isArray(payload) && payload.every(p => Array.isArray(p) && p.length === 2 && p.every(text)), `${kind} requires argument/type pairs`);
  }
  if (['KaniImpl', 'NoBody', 'UserFilter'].includes(kind)) check(payload === undefined, `${kind} must be a unit reason`);
  const categories = { GenericFn: 'Generic function', MissingArbitraryImpl: 'Missing Arbitrary',
    RequiresBoundedArguments: 'Requires bounded arguments', NoBody: 'No function body', UserFilter: 'User filter', KaniImpl: 'Kani internal' };
  return { kind, reason: Object.hasOwn(categories, kind) ? categories[kind] : 'Other', detail: typeof raw === 'string' ? raw : JSON.stringify(canonical(raw)) };
}
export function terminalTotals(log) {
  const patterns = {
    selected: /^(?:Kani generated automatic harnesses for (\d+) function\(s\):|Selected Functions: None\. Kani did not generate automatic harnesses for any functions in the available crate\(s\)\.)\s*$/gm,
    skipped: /^(?:Kani did not generate automatic harnesses for (\d+) function\(s\)\.|Skipped Functions: None\. Kani generated automatic harnesses for all functions in the available crate\(s\)\.)\s*$/gm,
  };
  return Object.fromEntries(Object.entries(patterns).map(([key, pattern]) => {
    const matches = [...log.matchAll(pattern)];
    check(matches.length === 1, `metrics.log: expected exactly one ${key} total, found ${matches.length}`);
    return [key, Number(matches[0][1] ?? 0)];
  }));
}
export function summarize(functions) {
  const byCrate = new Map(), byReason = new Map();
  for (const fn of functions) {
    const row = byCrate.get(fn.crate) ?? { name: fn.crate, selected: 0, skipped: 0 };
    row[fn.status === 'generated' ? 'selected' : 'skipped']++;
    byCrate.set(fn.crate, row);
    if (fn.status === 'skipped') byReason.set(fn.reason, (byReason.get(fn.reason) ?? 0) + 1);
  }
  const crates = [...byCrate.values()].sort((a,b) => compare(a.name,b.name)).map(row => ({ ...row,
    total: row.selected + row.skipped,
    coverage: row.selected + row.skipped ? row.selected / (row.selected + row.skipped) : null }));
  const automaticHarnesses = functions.filter(f => f.status === 'generated').length;
  const skipped = functions.length - automaticHarnesses;
  return { summary: { automaticHarnesses, skipped, candidateFunctions: functions.length,
    coverage: functions.length ? automaticHarnesses / functions.length : null }, crates,
    skipReasons: [...byReason].map(([reason,count]) => ({reason,count,share:skipped ? count/skipped : null}))
      .sort((a,b) => b.count-a.count || compare(a.reason,b.reason)) };
}
const sha = value => typeof value === 'string' && /^[a-f0-9]{40}$/.test(value);
const timestamp = value => text(value) && /^\d{4}-\d\d-\d\dT.*Z$/.test(value) && Number.isFinite(Date.parse(value));
export function validateRun(run) {
  check(object(run) && run.schemaVersion === 1, 'run.json: unsupported schemaVersion');
  for (const key of ['runId','repository','kaniVersion','target','host','rustcVersion','toolchain','scannerSource']) check(text(run[key]), `run.json: missing ${key}`);
  for (const key of ['verifyRustStdCommit','libraryTree','kaniCommit','expectedKaniCommit']) check(sha(run[key]), `run.json: invalid ${key}`);
  check(run.kaniCommit === run.expectedKaniCommit, 'run.json: Kani SHA does not match configured pin');
  check(timestamp(run.startedAt) && timestamp(run.completedAt) && Date.parse(run.completedAt) >= Date.parse(run.startedAt), 'run.json: invalid run times');
  check(Array.isArray(run.command) && run.command.length > 0 && run.command.every(text), 'run.json: missing command');
  check(/^https:\/\/github\.com\/[A-Za-z0-9-]+\/[A-Za-z0-9_.-]+$/.test(run.repository), 'run.json: invalid source repository URL');
  check(run.workflow === null || (object(run.workflow) && ['name','runId','attempt','url'].every(k => text(run.workflow[k]))
    && /^\d+$/.test(run.workflow.runId) && /^\d+$/.test(run.workflow.attempt)
    && run.workflow.url === `${run.repository}/actions/runs/${run.workflow.runId}`), 'run.json: invalid workflow');
  check(Array.isArray(run.files) && run.files.length > 0, 'run.json: missing input manifest');
  const paths = new Set();
  for (const file of run.files) {
    check(object(file) && text(file.path) && /^[a-f0-9]{64}$/.test(file.sha256), 'run.json: invalid input digest');
    check(!paths.has(file.path), `run.json: duplicate input ${file.path}`); paths.add(file.path);
  }
}
export function importRun(inputDir) {
  const root = realpathSync(inputDir), run = readJSON(resolve(root, 'run.json'));
  validateRun(run);
  const inputs = new Map();
  for (const file of run.files) {
    check(!file.path.startsWith('/') && !file.path.split('/').includes('..'), `Unsafe input path ${file.path}`);
    const path = realpathSync(resolve(root, file.path));
    check(path.startsWith(`${root}${sep}`), `Input escapes run directory: ${file.path}`);
    const bytes = readFileSync(path);
    check(createHash('sha256').update(bytes).digest('hex') === file.sha256, `SHA-256 mismatch: ${file.path}`);
    inputs.set(file.path, bytes.toString('utf8'));
  }
  const input = name => { check(inputs.has(name), `Missing input ${name}`); return inputs.get(name); };
  const json = name => { try { return JSON.parse(input(name)); } catch(e) { throw new Error(`${name}: ${e.message}`); } };
  const listing = json('kani-list.json');
  check(listing['file-version'] === '0.1', 'kani-list.json: unsupported file-version');
  check(listing['kani-version'] === run.kaniVersion, 'kani-list.json: Kani version mismatch');
  for (const key of ['standard-harnesses','contract-harnesses']) {
    check(object(listing[key]) && Object.values(listing[key]).every(v => Array.isArray(v) && v.every(text)), `kani-list.json: invalid ${key}`);
    check(integer(listing.totals?.[key]), `kani-list.json: missing total ${key}`);
    // Pinned Kani counts harness instances but deduplicates displayed names.
    // These contextual totals need not equal the number of displayed names.
  }
  check(Array.isArray(listing.contracts) && listing.contracts.length === listing.totals?.['functions-under-contract'], 'kani-list.json: invalid contracts total');
  for (const crate of ['core','alloc','std']) {
    for (const suffix of ['overall','functions','input_tys']) input(`scanner/${crate}_scan_${suffix}.csv`);
    check(Array.isArray(json(`metrics/metrics-data-${crate}.json`).results), `Invalid metrics for ${crate}`);
  }
  const totals = terminalTotals(input('metrics.log'));
  const metadata = [...inputs.keys()].filter(p => /^metadata\/[^/]+\.kani-metadata\.json$/.test(p)).sort(compare);
  check(metadata.length > 0, 'Missing Kani metadata');
  const functions = [], seen = new Set(), crates = new Set();
  let excludedKaniInternalFunctions = 0;
  for (const path of metadata) {
    const md = json(path);
    check(text(md.crate_name) && object(md.autoharness_md), `${path}: missing crate_name/autoharness_md`);
    const crate = md.crate_name, { chosen, skipped } = md.autoharness_md;
    check(!crates.has(crate), `${path}: duplicate crate metadata ${crate}`); crates.add(crate);
    check(Array.isArray(chosen) && chosen.every(text) && object(skipped), `${path}: invalid chosen/skipped`);
    const add = (fn, status, raw) => {
      check(text(fn), `${path}: empty function name`);
      const key = JSON.stringify([crate,fn]);
      check(!seen.has(key), `${path}: duplicate/conflicting function ${crate}::${fn}`); seen.add(key);
      const info = status === 'skipped' ? reasonInfo(raw) : null;
      if (info?.kind === 'KaniImpl') { excludedKaniInternalFunctions++; return; }
      functions.push({ crate, function: fn, status, reason: info?.reason ?? null,
        detail: info?.detail ?? null, rawReason: raw === undefined ? null : canonical(raw) });
    };
    chosen.forEach(fn => add(fn,'generated'));
    Object.entries(skipped).forEach(([fn,raw]) => add(fn,'skipped',raw));
  }
  functions.sort((a,b) => compare(a.crate,b.crate) || compare(a.function,b.function));
  const aggregate = summarize(functions);
  check(aggregate.summary.automaticHarnesses === totals.selected && aggregate.summary.skipped === totals.skipped,
    `Listing totals mismatch: metadata selected=${aggregate.summary.automaticHarnesses}, skipped=${aggregate.summary.skipped}; terminal selected=${totals.selected}, skipped=${totals.skipped}`);
  const common = { schemaVersion: 1, dataStatus: 'ready', runId: run.runId, generatedAt: run.completedAt };
  const dashboard = { ...common, meta: { ...run, excludedKaniInternalFunctions,
    scope: 'Functions reported by Kani autoharness listing; KaniImpl excluded; all emitted crates retained, including build scaffolding if reported.' },
    ...aggregate, verification: {status:'not-collected'}, notes: [
      'Generated harnesses do not imply successful verification.',
      'Coverage uses listed generated and skipped candidates, not all standard-library functions.',
      'Scanner analyzes the Kani toolchain standard library, not this repository library snapshot.',
      'Different Kani, rustc, library snapshots, targets or arguments are not directly comparable.' ] };
  const inventory = { ...common, functions };
  validateData(dashboard, inventory, true);
  return { dashboard, inventory };
}
export function validateData(d, f, requireReady = false, requireOfficial = false) {
  check(object(d) && object(f), 'Expected two JSON objects');
  for (const key of ['schemaVersion','dataStatus','runId','generatedAt']) check(d[key] === f[key], `Data pair mismatch: ${key}`);
  check(d.schemaVersion === 1, 'Unsupported dashboard schemaVersion');
  check(['pending','ready'].includes(d.dataStatus), 'Invalid dataStatus');
  check(!requireReady || d.dataStatus === 'ready', 'Data is not ready');
  check(object(d.verification) && d.verification.status === 'not-collected' && Object.keys(d.verification).length === 1, 'Invalid verification status');
  check(Array.isArray(d.notes) && d.notes.every(text), 'Invalid notes');
  check(Array.isArray(f.functions), 'Invalid functions');
  const checkFinite = value => {
    if (typeof value === 'number') check(Number.isFinite(value), 'Data contains NaN or Infinity');
    else if (Array.isArray(value)) value.forEach(checkFinite);
    else if (object(value)) Object.values(value).forEach(checkFinite);
  };
  checkFinite(d); checkFinite(f);
  for (const key of ['legacyComparison','improvementComparison','contributions']) check(!(key in d), `Unsupported personal snapshot field ${key}`);
  if (d.dataStatus === 'pending') {
    check(d.runId === null && d.generatedAt === null && d.meta === null && d.summary === null && f.functions.length === 0
      && Array.isArray(d.crates) && d.crates.length === 0 && Array.isArray(d.skipReasons) && d.skipReasons.length === 0, 'Invalid pending data');
    return;
  }
  validateRun(d.meta);
  check(!requireOfficial || d.meta.repository === 'https://github.com/model-checking/verify-rust-std', 'Official publication requires official repository provenance');
  check(d.runId === d.meta.runId && d.generatedAt === d.meta.completedAt, 'Provenance does not match data');
  check(integer(d.meta.excludedKaniInternalFunctions) && text(d.meta.scope), 'Missing exclusion/scope metadata');
  const seen = new Set(); let previous = null;
  for (const fn of f.functions) {
    check(object(fn) && text(fn.crate) && text(fn.function) && ['generated','skipped'].includes(fn.status), 'Invalid function record');
    const key = JSON.stringify([fn.crate,fn.function]); check(!seen.has(key), `Duplicate function ${key}`); seen.add(key);
    if (previous) check(compare(previous.crate, fn.crate) < 0 || (previous.crate === fn.crate && compare(previous.function, fn.function) < 0), 'Functions are not stably sorted');
    previous = fn;
    if (fn.status === 'generated') check(fn.reason === null && fn.detail === null && fn.rawReason === null, 'Generated function has skip reason');
    else { const info = reasonInfo(fn.rawReason); check(info.kind !== 'KaniImpl' && fn.reason === info.reason && fn.detail === info.detail, 'Skip reason mismatch'); }
  }
  const expected = summarize(f.functions);
  for (const key of ['summary','crates','skipReasons']) check(serialize(d[key]) === serialize(expected[key]), `Inconsistent ${key}`);
}
