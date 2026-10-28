#!/usr/bin/env node
// Real browser qualification against the private native route, with no mocks.
// Inputs are local private copies; an operator owns the SSH port forward.
import {readFile, writeFile, rename, stat} from 'node:fs/promises';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';

const [readyPath, tokenPath, resultPath] = process.argv.slice(2);
if (!readyPath || !tokenPath || !resultPath || process.argv.length !== 5)
  throw new Error('usage: browser_probe.mjs READY_JSON PRIVATE_TOKEN RESULT_JSON');
const ready = JSON.parse(await readFile(readyPath, 'utf8'));
const origin = new URL(ready.url);
if (ready.protocol !== 'mini-oracle-browser-ready-v1' || origin.protocol !== 'https:' ||
    origin.hostname !== 'localhost' || !origin.port || origin.pathname !== '/' ||
    origin.search || origin.hash || origin.username || origin.password ||
    !/^[0-9a-f]{64}$/.test(ready.route_custodian_sha256))
  throw new Error('readiness must name the private localhost TLS route');
const tokenMeta = await stat(tokenPath);
if (!tokenMeta.isFile() || tokenMeta.mode & 0o077 || tokenMeta.size > 128)
  throw new Error('token must be a private bounded file');
const {chromium} = createRequire(import.meta.url)(process.env.ORACLE_PLAYWRIGHT_MODULE || 'playwright');
const browser = await chromium.launch({headless: true});
try {
  const context = await browser.newContext({ignoreHTTPSErrors: true, viewport: {width: 1100, height: 900}});
  const page = await context.newPage();
  page.setDefaultTimeout(30_000);
  page.setDefaultNavigationTimeout(120_000);
  const errors = [];
  page.on('pageerror', error => errors.push(error.message));
  const result = {
    protocol: 'mini-oracle-browser-probe-v1', url: ready.url,
    route_custodian_sha256: ready.route_custodian_sha256,
    browser: 'chromium', browser_version: browser.version(),
  };
  const anonymous = await page.goto(ready.url);
  result.anonymous_status = anonymous.status();
  if (![401, 403].includes(result.anonymous_status)) throw new Error('anonymous route was not refused');
  await page.goto(new URL('/__mini/bootstrap', origin).href);
  await page.getByLabel('Private bootstrap token').fill((await readFile(tokenPath, 'utf8')).trim());
  const rootReply = page.waitForResponse(response => response.url() === ready.url &&
    response.request().isNavigationRequest(), {timeout: 120_000});
  await page.getByRole('button', {name: 'Sign in', exact: true}).click();
  result.root_status = (await rootReply).status();
  result.bootstrap_used = page.url() === ready.url && result.root_status === 200;
  result.root_ui_rendered = await page.getByRole('heading', {name: 'Ask a question', exact: true}).isVisible();
  if (!result.bootstrap_used || !result.root_ui_rendered) throw new Error('bootstrap did not reach the rendered Oracle page');

  const catalogReply = page.waitForResponse(response => new URL(response.url()).pathname === '/operations', {timeout: 120_000});
  await page.locator('#search-button').click();
  result.catalog_status = (await catalogReply).status();
  await page.locator('#operations li').first().waitFor();
  result.rendered_operation_count = await page.locator('#operations li').count();
  console.log('Browser bootstrap and rendered operation catalog passed.');

  await page.locator('#question').fill(ready.question);
  const queryReply = page.waitForResponse(response => new URL(response.url()).pathname === '/query', {timeout: 120_000});
  await page.locator('#ask').click();
  result.query_status = (await queryReply).status();
  const card = page.locator('#history article.result').first();
  if (await card.locator('p.answer').innerText() !== ready.question)
    throw new Error('rendered request card differs from the submitted question');
  const answer = card.locator('div.answer');
  await answer.filter({hasText: 'Whitman'}).waitFor();
  result.query_answer = await answer.innerText();
  const wrongOrigin = await context.request.get(ready.url, {headers: {Origin: 'https://wrong-origin.invalid'}, timeout: 120_000});
  result.wrong_origin_status = wrongOrigin.status();
  if (![result.root_status, result.catalog_status, result.query_status].every(status => status === 200) ||
      !result.query_answer.includes('Whitman') || ![401, 403].includes(result.wrong_origin_status) || errors.length)
    throw new Error('browser qualification failed: ' + JSON.stringify({...result, page_errors: errors}));
  // Save only the authenticated application page; never the bootstrap form.
  await page.screenshot({path: resolve(resultPath) + '.png', fullPage: true});
  result.page_errors = errors;
  const temporary = resolve(resultPath) + '.pending';
  await writeFile(temporary, JSON.stringify(result, null, 2) + '\n', {flag: 'wx', mode: 0o600});
  await rename(temporary, resultPath);
  console.log(JSON.stringify(result));
} finally {
  await browser.close();
}
