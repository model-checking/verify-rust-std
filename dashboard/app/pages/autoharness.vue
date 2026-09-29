<script setup lang="ts">
import type { DashboardData } from '~/types/data';

const baseURL = useRuntimeConfig().app.baseURL;
const { data, error, status } = await useAsyncData("autoharness-dashboard", () =>
  $fetch<DashboardData>(`${baseURL}data/autoharness-dashboard.json`),
);

const nf = new Intl.NumberFormat("en-US");
const pct = (value: number | null) => value === null ? '—' : `${(value * 100).toFixed(1)}%`;

</script>

<template>
  <main class="autoharness-page">
    <div v-if="error" class="error-state">Could not load dashboard data: {{ error.message }}</div>
    <section v-else-if="status === 'pending'" class="panel">Loading dashboard…</section>
    <section v-else-if="data?.dataStatus === 'pending'" class="panel">
      <h1>Rust std autoharness generation</h1>
      <h2>Awaiting the first official analysis</h2>
      <p class="subtitle">No official dataset has been published yet. Verification results are not collected.</p>
    </section>
    <template v-else-if="data?.summary && data.meta">
      <header class="hero">
        <div>
          <p class="eyebrow">{{ data.meta.repository === 'https://github.com/model-checking/verify-rust-std' ? 'Latest published analysis' : 'Fork analysis' }} · {{ data.generatedAt }}</p>
          <h1>Rust std autoharness generation</h1>
          <p class="subtitle">Every function in the run's listing is classified as generated or skipped, with the reason for each skip. Generated means Kani could build a harness for the function; it does not mean the function verified.</p>
        </div>
        <div class="run-meta">
          <span>Kani <code :title="data.meta.kaniCommit">{{ data.meta.kaniCommit.slice(0, 9) }}</code></span>
          <span>{{ data.meta.target }}</span>
        </div>
      </header>

      <section class="metrics" aria-label="Baseline summary">
        <article class="metric primary-metric">
          <span>Automatic harnesses</span>
          <strong>{{ nf.format(data.summary.automaticHarnesses) }}</strong>
          <small>{{ pct(data.summary.coverage) }} generation rate</small>
        </article>
        <article class="metric">
          <span>Skipped functions</span>
          <strong>{{ nf.format(data.summary.skipped) }}</strong>
          <small>Grouped by reason below</small>
        </article>
        <article class="metric">
          <span>Candidate functions</span>
          <strong>{{ nf.format(data.summary.candidateFunctions) }}</strong>
          <small>Generated plus skipped, as listed by this run</small>
        </article>
        <article class="metric">
          <span>Generation rate</span>
          <strong>{{ pct(data.summary.coverage) }}</strong>
          <small>Generated ÷ candidate functions</small>
        </article>
      </section>

      <section class="panel coverage-panel">
        <div class="section-heading">
          <div>
            <p class="eyebrow">Generation coverage</p>
            <h2>Autoharness generation by crate</h2>
          </div>
          <div class="legend" aria-label="Legend"><span class="chosen-dot" /> chosen <span class="skipped-dot" /> skipped</div>
        </div>
        <div class="crate-list">
          <div v-for="crate in data.crates" :key="crate.name" class="crate-row">
            <div class="crate-label"><strong>{{ crate.name }}</strong><span>{{ pct(crate.coverage) }}</span></div>
            <div class="stacked-bar" :aria-label="`${crate.name}: ${crate.selected} chosen, ${crate.skipped} skipped`">
              <div class="chosen" :style="{ width: `${(crate.coverage ?? 0) * 100}%` }" />
              <div class="skipped" :style="{ width: `${crate.coverage === null ? 0 : (1 - crate.coverage) * 100}%` }" />
            </div>
            <div class="crate-values"><span>{{ nf.format(crate.selected) }}</span><span>{{ nf.format(crate.skipped) }}</span></div>
          </div>
        </div>
      </section>

      <div class="two-column">
        <section class="panel">
          <div class="section-heading">
            <div><p class="eyebrow">Blockers</p><h2>Why functions were skipped</h2></div>
          </div>
          <div class="reason-list">
            <div v-for="reason in data.skipReasons" :key="reason.reason" class="reason-row">
              <div class="reason-label"><span>{{ reason.reason }}</span><strong>{{ nf.format(reason.count) }}</strong></div>
              <div class="reason-track"><div :style="{ width: `${reason.share * 100}%` }" /></div>
            </div>
          </div>
        </section>

        <section class="panel provenance-panel">
          <div class="section-heading"><div><p class="eyebrow">Source run</p><h2>Provenance</h2></div></div>
          <p v-if="data.meta.repository !== 'https://github.com/model-checking/verify-rust-std'" class="caveat">Fork analysis: {{ data.meta.repository }}. This is not an official published dataset.</p>
          <dl>
            <dt>Library checkout</dt><dd><a :href="`${data.meta.repository}/commit/${data.meta.verifyRustStdCommit}`">{{ data.meta.verifyRustStdCommit }}</a></dd>
            <dt>Kani</dt><dd>{{ data.meta.kaniVersion }} · <a :href="`https://github.com/model-checking/kani/commit/${data.meta.kaniCommit}`">{{ data.meta.kaniCommit }}</a></dd>
            <dt>Target</dt><dd>{{ data.meta.target }}</dd>
            <dt>Compiler</dt><dd><pre>{{ data.meta.rustcVersion }}</pre></dd>
            <dt>Toolchain</dt><dd><pre>{{ data.meta.toolchain }}</pre></dd>
            <dt v-if="data.meta.workflow">Source run</dt><dd v-if="data.meta.workflow"><a :href="data.meta.workflow.url">GitHub Actions run and raw artifacts</a></dd>
          </dl>
        </section>
      </div>

      <section class="method">
        <div><p class="eyebrow">Measurement rule</p><h2>What these counts mean</h2></div>
        <ol>
          <li>Coverage = generated / (generated + skipped), using only the listing candidates.</li>
          <li>Verification results: not collected. Kani internal functions excluded: {{ nf.format(data.meta.excludedKaniInternalFunctions) }}.</li>
          <li v-for="note in data.notes" :key="note">{{ note }}</li>
        </ol>
      </section>
    </template>
  </main>
</template>

<style scoped>
.autoharness-page { --ink: #17211d; --muted: #66736c; --paper: #f5f3ed; --surface: #fffdf8; --green: #087f5b; --green-soft: #cce9dc; --orange: #e87528; --line: #dedbd2; min-height: 100vh; overflow-y: auto; background: var(--paper); color: var(--ink); padding: 44px clamp(20px, 5vw, 76px) 72px; font-family: Inter, ui-sans-serif, system-ui, sans-serif; }
.hero { display: flex; align-items: flex-end; justify-content: space-between; gap: 32px; max-width: 1180px; margin: 0 auto 32px; }
.eyebrow { margin: 0 0 8px; color: var(--green); font-size: 12px; font-weight: 700; letter-spacing: .11em; text-transform: uppercase; }
h1 { margin: 0; max-width: 760px; font-family: Georgia, serif; font-size: clamp(40px, 6vw, 72px); font-weight: 500; letter-spacing: -.045em; line-height: .98; }
h2 { margin: 0; font-family: Georgia, serif; font-size: 26px; font-weight: 500; letter-spacing: -.025em; }
.subtitle { max-width: 700px; margin: 18px 0 0; color: var(--muted); font-size: 17px; line-height: 1.55; }
.run-meta { display: flex; flex-direction: column; align-items: flex-end; gap: 7px; flex: 0 0 auto; color: var(--muted); font-size: 13px; }
.run-meta code { color: var(--ink); }
.metrics { max-width: 1180px; margin: 0 auto 20px; display: grid; grid-template-columns: repeat(4, 1fr); gap: 12px; }
.metric { min-height: 148px; padding: 20px; background: var(--surface); border: 1px solid var(--line); border-radius: 8px; display: flex; flex-direction: column; }
.metric span { color: var(--muted); font-size: 13px; }
.metric strong { margin: auto 0 2px; font-family: Georgia, serif; font-size: 36px; font-weight: 500; letter-spacing: -.03em; }
.metric small { color: var(--muted); font-size: 12px; }
.primary-metric { background: var(--green); border-color: var(--green); color: white; }
.primary-metric span, .primary-metric small { color: rgba(255,255,255,.78); }
.panel { max-width: 1180px; margin: 0 auto 20px; padding: 26px; background: var(--surface); border: 1px solid var(--line); border-radius: 8px; }
.section-heading { display: flex; align-items: flex-end; justify-content: space-between; gap: 20px; margin-bottom: 26px; }
.legend { color: var(--muted); font-size: 12px; display: flex; align-items: center; gap: 7px; }
.chosen-dot, .skipped-dot { width: 9px; height: 9px; border-radius: 50%; background: var(--green); }.skipped-dot { margin-left: 8px; background: var(--green-soft); }
.crate-list { display: grid; gap: 18px; }
.crate-row { display: grid; grid-template-columns: 150px 1fr 145px; gap: 18px; align-items: center; }
.crate-label { display: flex; justify-content: space-between; align-items: baseline; }.crate-label strong { font-size: 14px; }.crate-label span { color: var(--muted); font-size: 12px; }
.stacked-bar { display: flex; height: 18px; overflow: hidden; background: var(--green-soft); border-radius: 3px; }.stacked-bar .chosen { background: var(--green); }.stacked-bar .skipped { background: var(--green-soft); }
.crate-values { display: flex; justify-content: space-between; color: var(--muted); font-size: 12px; font-variant-numeric: tabular-nums; }.crate-values span:first-child { color: var(--green); font-weight: 700; }
.two-column { max-width: 1180px; margin: 0 auto; display: grid; grid-template-columns: 1.25fr .75fr; gap: 20px; }.two-column .panel { width: 100%; margin: 0 0 20px; }
.reason-list { display: grid; gap: 17px; }.reason-label { display: flex; justify-content: space-between; gap: 18px; margin-bottom: 7px; font-size: 13px; }.reason-label strong { font-variant-numeric: tabular-nums; }.reason-track { height: 7px; background: #ebe8df; border-radius: 2px; overflow: hidden; }.reason-track div { height: 100%; background: var(--orange); }
.comparison-row { display: grid; grid-template-columns: 1fr 64px 16px 64px 72px; align-items: center; gap: 8px; padding: 13px 0; border-bottom: 1px solid var(--line); font-size: 13px; font-variant-numeric: tabular-nums; }.comparison-row span { text-align: right; }.comparison-row i { color: var(--muted); font-size: 11px; }.comparison-row b { color: var(--green); text-align: right; }
.comparison-row b.negative { color: var(--orange); }
.comparison-row b.pending { color: var(--muted); font-weight: 500; }
.comparison-stack { display: grid; gap: 20px; align-content: start; }.two-column .comparison-stack .panel { margin: 0; }
.caveat { margin: 18px 0 0; color: var(--muted); font-size: 12px; line-height: 1.55; }
.pr-panel { margin-top: 0; }.pr-row { display: grid; grid-template-columns: 72px 1fr 72px; align-items: baseline; gap: 14px; padding: 11px 0; border-bottom: 1px solid var(--line); font-size: 13px; }.pr-row strong a { color: var(--green); text-decoration: none; }.pr-row small { color: var(--muted); }.pr-row b { text-align: right; font-variant-numeric: tabular-nums; }
.method { max-width: 1180px; margin: 34px auto 0; display: grid; grid-template-columns: .75fr 1.25fr; gap: 60px; padding: 30px 0; border-top: 1px solid var(--line); }.method ol { margin: 0; padding-left: 22px; color: var(--muted); line-height: 1.7; list-style: decimal; }.method li { padding-left: 8px; margin-bottom: 8px; }
.error-state { max-width: 760px; margin: 80px auto; color: #b42318; }
.provenance-panel { min-width: 0; }.provenance-panel dl { margin: 0; font-size: 13px; }.provenance-panel dt { margin-top: 14px; font-weight: 700; }.provenance-panel dd, .provenance-panel pre { margin: 4px 0 0; white-space: pre-wrap; overflow-wrap: anywhere; color: var(--muted); }.provenance-panel a { color: var(--green); }.crate-label strong { overflow-wrap: anywhere; }
@media (max-width: 900px) { .hero { align-items: flex-start; flex-direction: column; }.run-meta { align-items: flex-start; }.metrics { grid-template-columns: repeat(2, 1fr); }.two-column { grid-template-columns: 1fr; }.method { grid-template-columns: 1fr; gap: 22px; } }
@media (max-width: 620px) { .autoharness-page { padding: 28px 14px 48px; }.metrics { grid-template-columns: 1fr; }.metric { min-height: 124px; }.crate-row { grid-template-columns: 1fr; gap: 7px; }.crate-values { max-width: 180px; }.section-heading { align-items: flex-start; flex-direction: column; }.comparison-row { grid-template-columns: 1fr 52px 12px 52px 58px; }.panel { padding: 20px 16px; } }
:global(.my-app-dark) .autoharness-page { --ink: #eef4ef; --muted: #a8b3ac; --paper: #111714; --surface: #18201c; --green: #4dd5a4; --green-soft: #263b32; --orange: #ff9b57; --line: #344039; }
:global(.my-app-dark) .reason-track { background: #29332e; }
</style>
