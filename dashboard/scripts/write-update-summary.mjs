// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { args, readJSON, validateData } from './data.mjs';
const options = args(['--previous-dir','--data-dir','--output']);
const old = readJSON(join(options['--previous-dir'],'autoharness-dashboard.json'));
const data = readJSON(join(options['--data-dir'],'autoharness-dashboard.json'));
validateData(data, readJSON(join(options['--data-dir'],'autoharness-functions.json')), true);
const before = old.dataStatus === 'ready' ? old.summary : null;
const meta = data.meta;
writeFileSync(options['--output'], `Generation inventory and existing Kani metrics from one analysis run. Generated harnesses do not imply successful verification. Dry runs only upload artifacts; publication requires official main with dry_run disabled.\n
- Source: ${meta.repository}/commit/${meta.verifyRustStdCommit}
- Kani: ${meta.kaniCommit} (${meta.kaniVersion})
- Target: ${meta.target}
- Completed: ${data.generatedAt}
- Raw artifacts and checks: ${meta.workflow?.url ?? 'Local run'}

| Metric | Previously published | This run |
| --- | ---: | ---: |
| Generated | ${before?.automaticHarnesses ?? 'Pending'} | ${data.summary.automaticHarnesses} |
| Skipped | ${before?.skipped ?? 'Pending'} | ${data.summary.skipped} |
| Listed candidates | ${before?.candidateFunctions ?? 'Pending'} | ${data.summary.candidateFunctions} |

Counts describe each snapshot, not attributed improvements. Different Kani, rustc, library, target or command settings are not directly comparable. Scanner metrics use toolchain rust-src; generation coverage uses only the listing candidates. Kani internal functions excluded: ${meta.excludedKaniInternalFunctions}.

Toolchain:
\`\`\`toml
${meta.toolchain.trim()}
\`\`\`

Command:
\`\`\`text
${meta.command.join(' ')}
\`\`\`

Approve any pending workflow runs, review the data, and merge normally. This workflow does not approve or merge its own PR.
`);
