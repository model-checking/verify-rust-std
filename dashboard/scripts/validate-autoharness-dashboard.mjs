// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
import { join } from 'node:path';
import { args, readJSON, validateData } from './data.mjs';
try {
  const options = args(['--data-dir'], ['--require-ready', '--require-official']);
  validateData(readJSON(join(options['--data-dir'],'autoharness-dashboard.json')),
    readJSON(join(options['--data-dir'],'autoharness-functions.json')), options['--require-ready'], options['--require-official']);
  console.log('Dashboard schema and consistency validation passed');
} catch (error) { console.error(error.message); process.exitCode = 1; }
