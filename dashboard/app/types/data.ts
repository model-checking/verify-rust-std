export type FunctionDatum = {
  crate: string; function: string; status: 'generated' | 'skipped';
  reason: string | null; detail: string | null; rawReason: unknown;
};
export type CommonData = { schemaVersion: 1; dataStatus: 'ready' | 'pending'; runId: string | null; generatedAt: string | null };
export type FunctionsData = CommonData & { functions: FunctionDatum[] };
export type DashboardData = CommonData & {
  meta: null | { repository: string; verifyRustStdCommit: string; kaniCommit: string; kaniVersion: string;
    target: string; toolchain: string; rustcVersion: string; excludedKaniInternalFunctions: number;
    workflow: null | { url: string }; scope: string };
  summary: null | { automaticHarnesses: number; skipped: number; candidateFunctions: number; coverage: number | null };
  crates: { name: string; selected: number; skipped: number; total: number; coverage: number | null }[];
  skipReasons: { reason: string; count: number; share: number }[];
  verification: { status: 'not-collected' }; notes: string[];
};
