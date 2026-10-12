// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { args, importRun, serialize } from './data.mjs';
try {
  const options = args(['--input-dir','--output-dir']);
  const { dashboard, inventory } = importRun(options['--input-dir']);
  mkdirSync(options['--output-dir'], {recursive:true});
  // Validation finishes before either public file is replaced.
  writeFileSync(join(options['--output-dir'],'autoharness-dashboard.json'), serialize(dashboard));
  writeFileSync(join(options['--output-dir'],'autoharness-functions.json'), serialize(inventory));
  console.log(`Imported ${inventory.functions.length} candidate functions from ${dashboard.runId}`);
} catch (error) { console.error(error.message); process.exitCode = 1; }
