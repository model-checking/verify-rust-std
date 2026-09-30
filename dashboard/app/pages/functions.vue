<script setup lang="ts">
import type { FunctionsData, FunctionDatum } from '~/types/data';
import Tooltip from 'primevue/tooltip';
const vTooltip = Tooltip;
type FunctionStatus = FunctionDatum['status'];

useHead({ title: "Autoharness Functions" });

const baseURL = useRuntimeConfig().app.baseURL;
const { data, error, status } = await useAsyncData("autoharness-functions", () =>
  $fetch<FunctionsData>(`${baseURL}data/autoharness-functions.json`),
);

const query = ref("");
const selectedCrate = ref("all");
const selectedStatus = ref<"all" | FunctionStatus>("all");
const selectedReason = ref("all");
watch(selectedStatus, value => {
  if (value === "generated") selectedReason.value = "all";
});

const crateOptions = computed(() => [
  { label: "All crates", value: "all" },
  ...[...new Set((data.value?.functions ?? []).map((item) => item.crate))]
    .sort()
    .map((value) => ({ label: value, value })),
]);
const statusOptions = [
  { label: "All statuses", value: "all" },
  { label: "Generated", value: "generated" },
  { label: "Skipped", value: "skipped" },
];
const reasonOptions = computed(() => [
  { label: "All skip reasons", value: "all" },
  ...[...new Set((data.value?.functions ?? []).map((item) => item.reason).filter((reason): reason is string => Boolean(reason)))]
    .sort()
    .map((value) => ({ label: value, value })),
]);

const filtered = computed(() => {
  const needle = query.value.trim().toLowerCase();
  return (data.value?.functions ?? []).filter((item) => {
    if (selectedCrate.value !== "all" && item.crate !== selectedCrate.value) return false;
    if (selectedStatus.value !== "all" && item.status !== selectedStatus.value) return false;
    if (selectedReason.value !== "all" && item.reason !== selectedReason.value) return false;
    if (needle && !item.function.toLowerCase().includes(needle) && !item.crate.toLowerCase().includes(needle)) return false;
    return true;
  });
});

const generatedCount = computed(() => filtered.value.filter((item) => item.status === "generated").length);
const skippedCount = computed(() => filtered.value.length - generatedCount.value);
const nf = new Intl.NumberFormat("en-US");
</script>

<template>
  <main class="functions-page">
    <header>
      <div>
        <p class="eyebrow">Per-function explorer · {{ data?.generatedAt }}</p>
        <h1>Autoharness functions</h1>
        <p>Every function in the latest published run's listing, classified by whether Kani generated an automatic harness. Generated does not mean verified.</p>
      </div>
      <div v-if="data?.dataStatus === 'ready'" class="counts" aria-live="polite">
        <span><strong>{{ nf.format(generatedCount) }}</strong> generated</span>
        <span><strong>{{ nf.format(skippedCount) }}</strong> skipped</span>
      </div>
    </header>

    <section v-if="data?.dataStatus === 'ready'" class="controls" aria-label="Function filters">
      <IconField class="search-field">
        <InputIcon><i class="pi pi-search" /></InputIcon>
        <InputText v-model="query" placeholder="Search function name" aria-label="Search function name" />
      </IconField>
      <Select aria-label="Crate" v-model="selectedCrate" :options="crateOptions" option-label="label" option-value="value" />
      <Select aria-label="Autoharness status" v-model="selectedStatus" :options="statusOptions" option-label="label" option-value="value" />
      <Select aria-label="Skip reason" v-model="selectedReason" :options="reasonOptions" option-label="label" option-value="value" :disabled="selectedStatus === 'generated'" />
      <span class="result-count">{{ nf.format(filtered.length) }} functions</span>
    </section>

    <div v-if="error" class="state error">Could not load function data: {{ error.message }}</div>
    <div v-else-if="status === 'pending'" class="state">Loading function inventory…</div>
    <div v-else-if="data?.dataStatus === 'pending'" class="state">Awaiting the first official analysis. No official function inventory has been published.</div>
    <DataTable
      v-else
      :value="filtered"
      paginator
      :rows="50"
      :rows-per-page-options="[20, 50, 100]"
      striped-rows
      removable-sort
      sort-field="crate"
      :sort-order="1"
      class="function-table"
    >
      <Column field="status" header="Autoharness" sortable style="width: 11rem">
        <template #body="{ data: row }">
          <Tag :severity="row.status === 'generated' ? 'success' : 'secondary'" :value="row.status === 'generated' ? 'Generated' : 'Skipped'" />
        </template>
      </Column>
      <Column field="crate" header="Crate" sortable style="width: 10rem" />
      <Column field="function" header="Function" sortable>
        <template #body="{ data: row }"><code>{{ row.function }}</code></template>
      </Column>
      <Column field="reason" header="Skip reason" sortable style="width: 17rem">
        <template #body="{ data: row }">
          <span v-if="row.reason" v-tooltip.top="row.detail ?? undefined">{{ row.reason }}</span>
          <span v-else class="not-applicable">—</span>
        </template>
      </Column>
      <template #empty>No functions match these filters.</template>
    </DataTable>
  </main>
</template>

<style scoped>
.functions-page { --ink: #17211d; --muted: #66736c; --paper: #f5f3ed; --surface: #fffdf8; --green: #087f5b; --line: #dedbd2; min-height: calc(100vh - 52px); overflow-y: auto; padding: 38px clamp(18px, 4vw, 62px) 60px; background: var(--paper); color: var(--ink); font-family: Inter, ui-sans-serif, system-ui, sans-serif; }
header { max-width: 1320px; margin: 0 auto 26px; display: flex; align-items: flex-end; justify-content: space-between; gap: 32px; }
.eyebrow { margin: 0 0 8px; color: var(--green); font-size: 12px; font-weight: 700; letter-spacing: .11em; text-transform: uppercase; }
h1 { margin: 0; font-family: Georgia, serif; font-size: clamp(36px, 5vw, 60px); font-weight: 500; letter-spacing: -.04em; }
header p:last-child { max-width: 760px; margin: 12px 0 0; color: var(--muted); line-height: 1.5; }
.counts { display: flex; gap: 20px; flex: 0 0 auto; color: var(--muted); font-size: 13px; }.counts strong { color: var(--ink); font-size: 18px; font-variant-numeric: tabular-nums; }
.controls { max-width: 1320px; margin: 0 auto 14px; display: grid; grid-template-columns: minmax(260px, 1fr) 180px 180px 250px auto; gap: 10px; align-items: center; }.search-field, .search-field input { width: 100%; }.result-count { color: var(--muted); font-size: 13px; text-align: right; white-space: nowrap; }
.function-table { max-width: 1320px; margin: 0 auto; border: 1px solid var(--line); border-radius: 8px; overflow: hidden; background: var(--surface); }
.function-table code { color: var(--ink); font-size: 12px; white-space: normal; overflow-wrap: anywhere; }.not-applicable { color: var(--muted); }.state { max-width: 1320px; margin: 40px auto; color: var(--muted); }.state.error { color: #b42318; }
@media (max-width: 1000px) { .controls { grid-template-columns: 1fr 1fr; }.result-count { text-align: left; } }
@media (max-width: 680px) { header { align-items: flex-start; flex-direction: column; }.counts { flex-wrap: wrap; }.controls { grid-template-columns: 1fr; }.functions-page { padding: 28px 12px 48px; } }
:global(.my-app-dark) .functions-page { --ink: #eef4ef; --muted: #a8b3ac; --paper: #111714; --surface: #18201c; --green: #4dd5a4; --line: #344039; }
</style>
