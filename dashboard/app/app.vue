<script setup lang="ts">
const appBaseURL = useRuntimeConfig().app.baseURL;
const docsURL = appBaseURL === '/'
  ? '/'
  : appBaseURL.replace(/dashboard\/?$/, '');
const dark = ref(false);
onMounted(() => {
  dark.value = localStorage.getItem('autoharness-theme') === 'dark';
  document.documentElement.classList.toggle('my-app-dark', dark.value);
});
function toggleTheme() {
  dark.value = !dark.value;
  document.documentElement.classList.toggle('my-app-dark', dark.value);
  localStorage.setItem('autoharness-theme', dark.value ? 'dark' : 'light');
}
</script>

<template>
  <nav class="site-nav" aria-label="Main navigation">
    <div><a :href="docsURL">Documentation</a><NuxtLink to="/autoharness">Overview</NuxtLink><NuxtLink to="/functions">Functions</NuxtLink></div>
    <Button :label="dark ? 'Light mode' : 'Dark mode'" :icon="dark ? 'pi pi-sun' : 'pi pi-moon'" text @click="toggleTheme" />
  </nav>
  <NuxtPage />
</template>
