// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { tmpdir } from 'node:os';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { importRun, validateData, serialize, reasonInfo } from '../scripts/data.mjs';
const md = JSON.parse(readFileSync(new URL('fixtures/metadata.json',import.meta.url)));
const log = (selected, skipped) => `${selected ? `Kani generated automatic harnesses for ${selected} function(s):` : 'Selected Functions: None. Kani did not generate automatic harnesses for any functions in the available crate(s).'}\n${skipped ? `Kani did not generate automatic harnesses for ${skipped} function(s).` : 'Skipped Functions: None. Kani generated automatic harnesses for all functions in the available crate(s).'}\n`;
function bundle(t, edit = () => {}) {
  const dir = mkdtempSync(join(tmpdir(),'dashboard-test-')); t.after(() => rmSync(dir,{recursive:true,force:true}));
  const files = {'metrics.log':log(2,6), 'metadata/core.kani-metadata.json':structuredClone(md),
    'kani-list.json':{'file-version':'0.1','kani-version':'0.67.0','standard-harnesses':{},'contract-harnesses':{},contracts:[],totals:{'standard-harnesses':0,'contract-harnesses':0,'functions-under-contract':0}}};
  for (const crate of ['core','alloc','std']) {
    files[`metrics/metrics-data-${crate}.json`] = {results:[]};
    for (const kind of ['overall','functions','input_tys']) files[`scanner/${crate}_scan_${kind}.csv`] = 'fixture\n';
  }
  const run = {schemaVersion:1,runId:'fixture-run',repository:'https://github.com/model-checking/verify-rust-std',verifyRustStdCommit:'1'.repeat(40),libraryTree:'2'.repeat(40),expectedKaniCommit:'3'.repeat(40),kaniCommit:'3'.repeat(40),kaniVersion:'0.67.0',host:'x86_64-unknown-linux-gnu',target:'x86_64-unknown-linux-gnu',rustcVersion:'fixture rustc',toolchain:'fixture nightly',startedAt:'2026-09-27T00:00:00Z',completedAt:'2026-09-27T01:00:00Z',workflow:null,command:['fixture'],scannerSource:'toolchain rust-src'};
  edit(files,run);
  run.files = Object.entries(files).map(([path,value]) => {
    const bytes = typeof value === 'string' ? value : JSON.stringify(value);
    mkdirSync(join(dir,path,'..'),{recursive:true}); writeFileSync(join(dir,path),bytes);
    return {path,sha256:createHash('sha256').update(bytes).digest('hex')};
  });
  writeFileSync(join(dir,'run.json'),JSON.stringify(run)); return dir;
}
test('imports structured reasons and excludes Kani internal functions', t => {
  const {dashboard:d,inventory:f} = importRun(bundle(t));
  assert.equal(d.summary.automaticHarnesses,2); assert.equal(d.summary.skipped,6);
  assert.equal(d.meta.excludedKaniInternalFunctions,1);
  assert.equal(f.functions.find(f=>f.function==='unknown').reason,'Other');
  assert.deepEqual(f.functions.find(f=>f.function==='unknown').rawReason,{FutureReason:{a:2,z:1}});
  assert.equal(d.verification.status,'not-collected');
});
for (const [selected,skipped] of [[0,0],[0,1],[1,0]]) test(`zero handling ${selected}/${skipped}`, t => {
  const result = importRun(bundle(t, files => {
    files['metadata/core.kani-metadata.json'].autoharness_md = {chosen:selected?['f']:[],skipped:skipped?{g:'NoBody'}:{}};
    files['metrics.log']=log(selected,skipped);
  }));
  assert.equal(result.dashboard.summary.coverage,selected+skipped ? selected/(selected+skipped):null);
});
const failures = [
  ['missing file', f=>delete f['kani-list.json'],/Missing input/],
  ['invalid JSON', f=>f['kani-list.json']='{',/kani-list.json/],
  ['unknown list version', f=>f['kani-list.json']['file-version']='99',/file-version/],
  ['invalid list total', f=>f['kani-list.json'].totals['standard-harnesses']='2',/missing total/],
  ['missing scanner input', f=>delete f['scanner/std_scan_functions.csv'],/Missing input/],
  ['missing metadata', f=>delete f['metadata/core.kani-metadata.json'],/Missing Kani metadata/],
  ['missing field', f=>delete f['metadata/core.kani-metadata.json'].autoharness_md.chosen,/chosen/],
  ['total mismatch', f=>f['metrics.log']=log(100,6),/totals mismatch/],
  ['absent totals', f=>f['metrics.log']='new output',/expected exactly one/],
  ['duplicate totals', f=>f['metrics.log']+=log(2,6),/expected exactly one/],
  ['duplicate function', f=>f['metadata/core.kani-metadata.json'].autoharness_md.chosen.push('a'),/duplicate/],
  ['state conflict', f=>f['metadata/core.kani-metadata.json'].autoharness_md.skipped.a='NoBody',/conflicting/],
  ['malformed reason', f=>f['metadata/core.kani-metadata.json'].autoharness_md.skipped.generic={GenericFn:42},/payload/],
  ['malformed arguments', f=>f['metadata/core.kani-metadata.json'].autoharness_md.skipped.missing={MissingArbitraryImpl:[42]},/argument/],
  ['version mismatch', f=>f['kani-list.json']['kani-version']='wrong',/version mismatch/],
];
for (const [name,edit,error] of failures) test(name,t=>assert.throws(()=>importRun(bundle(t,edit)),error));
test('pin mismatch',t=>assert.throws(()=>importRun(bundle(t,(_,r)=>r.kaniCommit='4'.repeat(40))),/SHA/));
test('listing totals may count multiple harness instances per displayed name',t=>{
  const {dashboard:d}=importRun(bundle(t,f=>{
    f['kani-list.json']['standard-harnesses']={'source.rs':['proof']};
    f['kani-list.json'].totals['standard-harnesses']=2;
  }));
  assert.equal(d.summary.automaticHarnesses,2);
});
test('fork provenance is accepted for preview but rejected for official publication',t=>{
  const {dashboard:d,inventory:f}=importRun(bundle(t,(_,r)=>{
    r.repository='https://github.com/example/verify-rust-std';
    r.workflow={name:'dry run',runId:'123',attempt:'1',url:`${r.repository}/actions/runs/123`};
  }));
  validateData(d,f,true);
  assert.throws(()=>validateData(d,f,true,true),/official repository provenance/);
  const official=importRun(bundle(t));
  validateData(official.dashboard,official.inventory,true,true);
});
test('non-finite values cannot be silently serialized as null',t=>{
  const {dashboard:d,inventory:f}=importRun(bundle(t));
  for(const coverage of [NaN,Infinity,-Infinity])
    assert.throws(()=>validateData({...d,summary:{...d.summary,coverage}},f),/NaN or Infinity/);
});
test('tampered input hash',t=>{const dir=bundle(t);writeFileSync(join(dir,'metrics.log'),'tampered');assert.throws(()=>importRun(dir),/SHA-256/);});
test('same function in different crates is independent',t=>{
  const result=importRun(bundle(t,f=>{f['metadata/alloc.kani-metadata.json']={crate_name:'alloc',autoharness_md:{chosen:['a'],skipped:{}}};f['metrics.log']=log(3,6);}));
  assert.equal(result.dashboard.crates.length,2);
});
test('scanner snapshot differences do not change generation coverage',t=>{
  const a=importRun(bundle(t)), b=importRun(bundle(t,f=>{f['scanner/core_scan_functions.csv']='name;is_unsafe\nextra;false\n';}));
  assert.deepEqual(a.dashboard.summary,b.dashboard.summary);
});
test('input ordering and repeated conversion are stable',t=>{
  const dir=bundle(t); const a=importRun(dir);
  assert.equal(serialize(a),serialize(importRun(dir)));
  const b=importRun(bundle(t,f=>f['metadata/core.kani-metadata.json'].autoharness_md.chosen.reverse()));
  // Provenance hashes intentionally reflect changed input bytes.
  assert.equal(serialize(a.inventory),serialize(b.inventory));
  assert.equal(serialize(a.dashboard.summary),serialize(b.dashboard.summary));
});
test('data pair mismatch, aggregate corruption, ordering, pending publication',t=>{
  const {dashboard:d,inventory:f}=importRun(bundle(t));
  assert.throws(()=>validateData(d,{...f,runId:'other'}),/mismatch/);
  assert.throws(()=>validateData({...d,summary:{...d.summary,skipped:100}},f),/summary/);
  assert.throws(()=>validateData(d,{...f,functions:[...f.functions].reverse()}),/sorted/);
  const pending=JSON.parse(readFileSync(new URL('../public/data/autoharness-dashboard.json',import.meta.url)));
  const empty=JSON.parse(readFileSync(new URL('../public/data/autoharness-functions.json',import.meta.url)));
  // Checked-in data can become ready on a data-update PR.
  validateData(pending,empty);
  if(pending.dataStatus==='pending') assert.throws(()=>validateData(pending,empty,true),/not ready/);
});
test('unknown unit reason is retained, unknown structural shape is rejected',()=>{
  assert.equal(reasonInfo('FutureReason').reason,'Other');
  assert.equal(reasonInfo('toString').reason,'Other');
  assert.throws(()=>reasonInfo({A:1,B:2}),/structure/);
});
test('CLI writes a valid pair and does not touch output on failed import',t=>{
  const dir=bundle(t), out=join(dir,'out');
  const command=[fileURLToPath(new URL('../scripts/build-autoharness-dashboard.mjs',import.meta.url)),'--input-dir',dir,'--output-dir',out];
  assert.equal(spawnSync(process.execPath,command,{encoding:'utf8'}).status,0);
  const before=readFileSync(join(out,'autoharness-dashboard.json'),'utf8');
  writeFileSync(join(dir,'metrics.log'),'bad');
  assert.notEqual(spawnSync(process.execPath,command,{encoding:'utf8'}).status,0);
  assert.equal(readFileSync(join(out,'autoharness-dashboard.json'),'utf8'),before);
  assert.equal(readdirSync(out).length,2);
});

test('reject unsafe manifest paths and invalid workflow URLs',t=>{
  const dir=bundle(t); const path=join(dir,'run.json'); const run=JSON.parse(readFileSync(path));
  run.files[0].path='../outside';writeFileSync(path,JSON.stringify(run));
  assert.throws(()=>importRun(dir),/Unsafe input path/);
  assert.throws(()=>importRun(bundle(t,(_,r)=>r.workflow={name:'test',runId:'1',attempt:'1',url:'javascript:alert(1)'})),/invalid workflow/);
});
