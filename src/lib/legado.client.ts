/* eslint-disable @typescript-eslint/no-explicit-any */
import * as cheerio from 'cheerio/slim';
import crypto from 'crypto';
import he from 'he';

import { getConfig } from './config';
import {
  BookAcquisitionLink,
  BookCatalogResult,
  BookChapter,
  BookChapterContent,
  BookDetail,
  BookListItem,
  BookSearchFailure,
  BookSearchResult,
  BookSource,
  BookSourceCapabilities,
  LegadoBookSourceRule,
} from './book.types';
import { validateProxyUrlServerSide } from './server/ssrf';
import { legadoSubscriptionStore } from './legado/subscription-store';

interface ResolvedLegadoConfig {
  enabled: boolean;
  sources: BookSource[];
  cacheTTL: number;
}

const DEFAULT_TIMEOUT_MS = Number(process.env.LEGADO_TIMEOUT_MS || process.env.OPDS_TIMEOUT_MS || 20000);
const MAX_TEXT_BYTES = Number(process.env.LEGADO_MAX_TEXT_BYTES || 3 * 1024 * 1024);
const LEGADO_CACHE_VERSION = 'v5';
const DEFAULT_LEGADO_SEARCH_PAGES = Number(process.env.LEGADO_SEARCH_PAGES || 5);
const textCache = new Map<string, { expiresAt: number; data: string }>();
const searchCache = new Map<string, { expiresAt: number; data: BookListItem[] }>();
const detailCache = new Map<string, { expiresAt: number; data: BookDetail }>();
const tocCache = new Map<string, { expiresAt: number; data: BookChapter[] }>();
const chapterCache = new Map<string, { expiresAt: number; data: BookChapterContent }>();

function stableId(input: string) {
  return crypto.createHash('sha1').update(input).digest('hex').slice(0, 16);
}

function asObjectHeader(value?: string | Record<string, string>): Record<string, string> {
  if (!value) return {};
  if (typeof value === 'object') return value;
  try {
    const parsed = JSON.parse(value);
    return parsed && typeof parsed === 'object' ? parsed : {};
  } catch {
    return value.split('\n').reduce<Record<string, string>>((headers, line) => {
      const index = line.indexOf(':');
      if (index > 0) headers[line.slice(0, index).trim()] = line.slice(index + 1).trim();
      return headers;
    }, {});
  }
}

function buildHeaders(source: BookSource): HeadersInit {
  const rule = source.legado;
  const headers: Record<string, string> = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0 Safari/537.36',
    Accept: 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
    ...asObjectHeader(rule?.header),
  };
  if (source.authMode === 'header' && source.headerName && source.headerValue) headers[source.headerName] = source.headerValue;
  if (source.authMode === 'basic' && source.username) headers.Authorization = `Basic ${Buffer.from(`${source.username}:${source.password || ''}`).toString('base64')}`;
  delete headers.Host;
  delete headers.host;
  delete headers['Content-Length'];
  delete headers['content-length'];
  return headers;
}

function sourceBase(source: BookSource) {
  return source.legado?.bookSourceUrl || source.url;
}

function normalizeUrl(base: string, href?: string): string {
  if (!href) return base;
  const trimmed = href.trim();
  if (!trimmed) return base;
  if (/^javascript:/i.test(trimmed)) return '';
  return new URL(trimmed, base).toString();
}

function encodeRuleParam(value: string) {
  return encodeURIComponent(value).replace(/%20/g, '+');
}

function buildUrlFromTemplate(template: string, source: BookSource, keyword?: string, page = 1, baseOverride?: string) {
  const base = baseOverride || sourceBase(source);
  let raw = template || base;
  raw = raw.replace(/\{\{(?:key|keyword|searchTerms)\}\}/g, encodeRuleParam(keyword || ''));
  raw = raw.replace(/\{\{(?:page|pageIndex)\}\}/g, String(page));
  raw = raw
    .replace(/\{searchTerms\}/g, encodeRuleParam(keyword || ''))
    .replace(/\{key\}/g, encodeRuleParam(keyword || ''))
    .replace(/\{keyword\}/g, encodeRuleParam(keyword || ''))
    .replace(/\{page\}/g, String(page))
    .replace(/\{pageIndex\}/g, String(page));
  if (raw.includes('{{') && keyword) raw = raw.replace(/\{\{.*?\}\}/g, encodeRuleParam(keyword));
  return normalizeUrl(base, raw);
}

function parseJsonMaybe(value: string): any | null {
  try {
    return JSON.parse(value);
  } catch {
    return null;
  }
}

function jsonPrimitiveToString(value: any): string {
  if (value === undefined || value === null) return '';
  if (typeof value === 'string') return value.trim();
  if (typeof value === 'number' || typeof value === 'boolean') return String(value);
  if (Array.isArray(value)) return value.map(jsonPrimitiveToString).filter(Boolean).join(', ');
  try {
    return JSON.stringify(value);
  } catch {
    return String(value);
  }
}

function readJsonPath(input: any, path?: string): any {
  if (!path) return input;
  let normalized = path.trim();
  if (normalized.startsWith('@json:')) normalized = normalized.slice(6);
  if (normalized.startsWith('-@json:')) normalized = normalized.slice(7);
  if (!normalized || normalized === '$') return input;

  const recursive = normalized.match(/^\$\.\.([A-Za-z0-9_$-]+)\[\*\]$/);
  if (recursive) {
    const key = recursive[1];
    const out: any[] = [];
    const walk = (node: any) => {
      if (!node || typeof node !== 'object') return;
      if (Array.isArray(node)) {
        node.forEach(walk);
        return;
      }
      if (Array.isArray(node[key])) out.push(...node[key]);
      Object.values(node).forEach(walk);
    };
    walk(input);
    return out;
  }

  normalized = normalized.replace(/^\$\.?/, '');
  const tokens = normalized.match(/[^.[\]]+|\[\*\]|\[\d+\]/g) || [];
  let current = input;
  for (const token of tokens) {
    if (current === undefined || current === null) return undefined;
    if (token === '[*]') {
      if (!Array.isArray(current)) return [];
      current = current.flat();
    } else if (/^\[\d+\]$/.test(token)) {
      current = Array.isArray(current) ? current[Number(token.slice(1, -1))] : undefined;
    } else if (Array.isArray(current)) {
      current = current.map((item) => item?.[token]).filter((item) => item !== undefined);
    } else {
      current = current[token];
    }
  }
  return current;
}

function ruleIsJson(rule?: string) {
  return !!rule && /@json:|-@json:|^\$\./.test(rule.trim());
}

function selectJsonItems(json: any, rule?: string): any[] {
  const reverse = !!rule?.trim().startsWith('-');
  const value = readJsonPath(json, rule);
  const list = Array.isArray(value) ? value : value ? [value] : [];
  return reverse ? [...list].reverse() : list;
}

function renderTemplateWithJson(template: string, json: any, source: BookSource, baseUrl: string) {
  const rendered = template.replace(/\{\{(.*?)\}\}/g, (_, expr) => {
    const normalizedExpr = String(expr).trim().replace(/^@json:/, '');
    const value = readJsonPath(json, normalizedExpr);
    return encodeRuleParam(jsonPrimitiveToString(value));
  });
  return normalizeUrl(baseUrl || sourceBase(source), rendered);
}

function readJsonRule(json: any, rule?: string, source?: BookSource, baseUrl?: string): string {
  if (!rule) return '';
  const trimmed = rule.trim();
  if (trimmed.includes('{{')) return renderTemplateWithJson(trimmed, json, source as BookSource, baseUrl || sourceBase(source as BookSource));
  if (trimmed.startsWith('@js:')) {
    if (/result\s*=\s*['"]([^'"]+)['"]\s*\+\s*result\.([A-Za-z0-9_$-]+)/.test(trimmed)) {
      const match = trimmed.match(/result\s*=\s*['"]([^'"]+)['"]\s*\+\s*result\.([A-Za-z0-9_$-]+)/);
      return normalizeUrl(baseUrl || sourceBase(source as BookSource), `${match?.[1] || ''}${jsonPrimitiveToString(json?.[match?.[2] || ''])}`);
    }
    if (/item\.img|\.reverse\(\)/.test(trimmed)) {
      const data = Array.isArray(json?.data) ? [...json.data].reverse() : Array.isArray(json) ? [...json].reverse() : [];
      return data
        .map((item) => item?.img ? `<img src="${String(item.img)}" style="max-width:100%; display:block;" referrerpolicy="no-referrer">` : '')
        .filter(Boolean)
        .join('');
    }
    return '';
  }
  const value = readJsonPath(json, trimmed);
  const text = jsonPrimitiveToString(value);
  if ((/url|href|pic|cover/i.test(trimmed) || /^https?:\/\//i.test(text)) && text && baseUrl) return normalizeUrl(baseUrl, text);
  return text;
}

function fallbackChapterHrefFromItem(item: any, rule?: string, baseUrl?: string): string {
  const id = jsonPrimitiveToString(item?.id || item?.cid || item?.chapter_id || item?.chapterId);
  if (!id) return '';
  const match = (rule || '').match(/['"]([^'"]*(?:pic|chapter)[^'"]*(?:cid|id)=)['"]/i);
  if (match?.[1]) return normalizeUrl(baseUrl || '', `${match[1]}${id}`);
  return '';
}

function splitAlternatives(rule?: string): string[] {
  return (rule || '').split('||').map((item) => item.trim()).filter(Boolean);
}

function parseStep(step: string): { selector: string; attr: string } {
  const trimmed = step.trim();
  const attrMatch = trimmed.match(/(?:@|::)(text|textNodes|html|href|src|content|value|data-[\w-]+|[\w-]+)$/i);
  if (attrMatch) {
    return { selector: trimmed.slice(0, attrMatch.index).trim(), attr: attrMatch[1] };
  }
  const dotAttr = trimmed.match(/\.(text|html|href|src)$/i);
  if (dotAttr) return { selector: trimmed.slice(0, dotAttr.index).trim(), attr: dotAttr[1] };
  return { selector: trimmed, attr: '' };
}

function stripFilters(rule: string) {
  return rule.split('##')[0].trim();
}

function selectElements($: cheerio.CheerioAPI, root: cheerio.Cheerio<any>, rule?: string): cheerio.Cheerio<any> {
  const normalized = stripFilters(rule || '');
  if (!normalized) return root;
  const steps = normalized.split(/&&|@css:/).map((item) => item.trim()).filter(Boolean);
  let current = root;
  for (const rawStep of steps) {
    const { selector, attr } = parseStep(rawStep);
    if (!selector || attr) break;
    current = current.find(selector);
  }
  return current;
}

function readValue($: cheerio.CheerioAPI, root: cheerio.Cheerio<any>, rule?: string, baseUrl?: string): string {
  for (const alternative of splitAlternatives(rule)) {
    const normalized = stripFilters(alternative);
    const steps = normalized.split(/&&|@css:/).map((item) => item.trim()).filter(Boolean);
    let current = root;
    let attr = '';
    for (const rawStep of steps) {
      const parsed = parseStep(rawStep);
      if (parsed.selector) current = current.find(parsed.selector);
      if (parsed.attr) attr = parsed.attr;
    }
    if (current.length === 0 && steps.length === 1) {
      const parsed = parseStep(steps[0]);
      if (!parsed.selector && parsed.attr) current = root;
    }
    const node = current.first();
    let value = '';
    const normalizedAttr = attr.toLowerCase();
    if (!attr || normalizedAttr === 'text' || normalizedAttr === 'textnodes') value = node.text();
    else if (normalizedAttr === 'html') value = node.html() || '';
    else value = node.attr(attr) || '';
    value = he.decode(value || '').replace(/\u00a0/g, ' ').trim();
    if ((normalizedAttr === 'href' || normalizedAttr === 'src') && value && baseUrl) value = normalizeUrl(baseUrl, value);
    if (value) return value;
  }
  return '';
}

function contentFromRule(raw: string, rule?: string, baseUrl?: string): string {
  const json = parseJsonMaybe(raw);
  if (json && (ruleIsJson(rule) || rule?.trim().startsWith('@js:'))) {
    return readJsonRule(json, rule, undefined, baseUrl);
  }
  const $ = cheerio.load(raw);
  return readValue($, $.root(), rule, baseUrl);
}

function cleanContent(value: string) {
  const decoded = he.decode(value || '').trim();
  if (/<img\b/i.test(decoded)) return decoded;
  return decoded
    .replace(/<br\s*\/?>/gi, '\n')
    .replace(/<\/p>/gi, '\n')
    .replace(/<[^>]+>/g, '')
    .replace(/\r/g, '')
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean)
    .join('\n\n');
}

async function resolveLegadoConfig(): Promise<ResolvedLegadoConfig> {
  let enabled = process.env.OPDS_ENABLED === 'true' || process.env.LEGADO_ENABLED === 'true';
  let sources: BookSource[] = [];
  const cacheTTL = Number(process.env.LEGADO_CACHE_TTL_MS || process.env.OPDS_CACHE_TTL_MS || 10 * 60 * 1000);

  const envJson = process.env.LEGADO_SOURCES_JSON;
  if (envJson) {
    try {
      const parsed = JSON.parse(envJson);
      sources = normalizeImportedSources(parsed);
    } catch {}
  }

  try {
    const config = await getConfig();
    if (config.OPDSConfig) {
      enabled = config.OPDSConfig.Enabled ?? enabled;
      const subscriptionSources = await legadoSubscriptionStore.getSourcesForSubscriptions(config.OPDSConfig.LegadoSubscriptions || []);
      sources = [...sources, ...subscriptionSources];
    }
  } catch {}

  return { enabled, cacheTTL, sources: sources.filter((source) => !!source.url && source.enabled !== false) };
}

export function normalizeImportedSources(input: unknown): BookSource[] {
  const list = Array.isArray(input) ? input : [input];
  return list
    .filter((item): item is LegadoBookSourceRule => !!item && typeof item === 'object')
    .map((rule, index) => {
      const name = rule.bookSourceName || `Legado 书源 ${index + 1}`;
      const url = rule.bookSourceUrl || '';
      return {
        id: `legado_${stableId(`${name}|${url}|${index}`)}`,
        name,
        type: 'legado' as const,
        url,
        enabled: rule.enabled !== false,
        authMode: 'none' as const,
        preferFormat: ['epub' as const],
        language: '',
        legado: rule,
      };
    })
    .filter((source) => !!source.url);
}

function normalizeConfiguredLegadoSource(item: any, index: number): BookSource | null {
  if (!item || typeof item !== 'object') return null;
  if (item.type === 'legado' || item.legado) {
    const rule = item.legado || item;
    const name = item.name || rule.bookSourceName || `Legado 书源 ${index + 1}`;
    const url = item.url || rule.bookSourceUrl || '';
    if (!url) return null;
    return {
      ...item,
      id: item.id || `legado_${stableId(`${name}|${url}|${index}`)}`,
      name,
      type: 'legado',
      url,
      enabled: item.enabled !== false && rule.enabled !== false,
      authMode: item.authMode || 'none',
      legado: { ...rule, bookSourceName: rule.bookSourceName || name, bookSourceUrl: rule.bookSourceUrl || url },
    };
  }
  if (item.bookSourceUrl || item.searchUrl || item.ruleSearch) {
    return normalizeImportedSources([item])[0] || null;
  }
  return null;
}

function wait(ms: number) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function fetchText(source: BookSource, url: string): Promise<string> {
  if (!url?.trim()) throw new Error('书源请求地址为空');
  const safe = await validateProxyUrlServerSide(url);
  if (!safe) throw new Error(`书源地址未通过安全校验: ${url}`);
  const cacheKey = `${LEGADO_CACHE_VERSION}|text|${source.id}|${url}`;
  const cached = textCache.get(cacheKey);
  const { cacheTTL } = await resolveLegadoConfig();
  if (cached && cached.expiresAt > Date.now()) return cached.data;

  let lastError: unknown;
  for (let attempt = 0; attempt < 3; attempt += 1) {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), DEFAULT_TIMEOUT_MS);
    try {
      const response = await fetch(url, { headers: buildHeaders(source), signal: controller.signal, cache: 'no-store' });
      if (!response.ok) throw new Error(`请求失败: ${response.status}`);
      const contentLength = Number(response.headers.get('content-length') || '0');
      if (contentLength > MAX_TEXT_BYTES) throw new Error('响应内容过大');
      const text = await response.text();
      if (text.length > MAX_TEXT_BYTES) throw new Error('响应内容过大');
      textCache.set(cacheKey, { data: text, expiresAt: Date.now() + cacheTTL });
      return text;
    } catch (error) {
      lastError = error;
      if (attempt < 2) await wait(300 * (attempt + 1));
    } finally {
      clearTimeout(timeout);
    }
  }
  throw lastError instanceof Error ? lastError : new Error('请求失败');
}

async function getSourceById(sourceId: string): Promise<BookSource> {
  const config = await resolveLegadoConfig();
  const source = config.sources.find((item) => item.id === sourceId);
  if (!source) throw new Error('未找到对应的 Legado 书源');
  return source;
}

function getRule(source: BookSource): LegadoBookSourceRule {
  if (!source.legado) throw new Error('Legado 书源缺少规则');
  return source.legado;
}

function makeItem(source: BookSource, partial: Partial<BookListItem> & { detailHref?: string; title?: string }): BookListItem {
  const detailHref = partial.detailHref || '';
  return {
    id: partial.id || stableId(`${source.id}|${detailHref || partial.title || Date.now()}`),
    sourceId: source.id,
    sourceName: source.name,
    title: partial.title || '未命名电子书',
    author: partial.author,
    cover: partial.cover,
    summary: partial.summary,
    tags: partial.tags,
    detailHref,
    acquisitionLinks: partial.acquisitionLinks || [],
  };
}

export class LegadoClient {
  async getSources(): Promise<BookSource[]> {
    const config = await resolveLegadoConfig();
    if (!config.enabled) return [];
    return config.sources.map((source) => ({
      ...source,
      capabilities: {
        searchSupported: !!source.legado?.searchUrl,
        catalogSupported: false,
        searchMode: source.legado?.searchUrl ? 'legado' : 'disabled',
        catalogMode: 'legado',
        acquisitionTypes: ['application/x-legado-chapters+json'],
        lastCheckedAt: Date.now(),
      },
    }));
  }

  async getSearchSources(sourceId?: string): Promise<BookSource[]> {
    return sourceId ? [await getSourceById(sourceId)] : (await resolveLegadoConfig()).sources;
  }

  async searchBooksSource(q: string, source: BookSource): Promise<{ source: BookSource; results: BookListItem[] }> {
    const rule = getRule(source);
    if (!rule.searchUrl || !rule.ruleSearch?.bookList) throw new Error('该 Legado 书源不支持搜索');
    const cacheKey = `${LEGADO_CACHE_VERSION}|search|${source.id}|${q}`;
    const { cacheTTL } = await resolveLegadoConfig();
    const cached = searchCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) return { source, results: cached.data };

    const results: BookListItem[] = [];
    const seen = new Set<string>();
    for (let page = 1; page <= DEFAULT_LEGADO_SEARCH_PAGES; page += 1) {
      const targetUrl = buildUrlFromTemplate(rule.searchUrl, source, q, page);
      const html = await fetchText(source, targetUrl);
      let pageCount = 0;
      const json = parseJsonMaybe(html);
      if (json && ruleIsJson(rule.ruleSearch.bookList)) {
        const items = selectJsonItems(json, rule.ruleSearch.bookList);
        pageCount = items.length;
        items.forEach((item) => {
          const detailHref = readJsonRule(item, rule.ruleSearch?.bookUrl, source, targetUrl);
          const title = readJsonRule(item, rule.ruleSearch?.name, source, targetUrl);
          if (!title && !detailHref) return;
          const cover = readJsonRule(item, rule.ruleSearch?.coverUrl, source, targetUrl);
          const itemId = jsonPrimitiveToString(item?.id) || undefined;
          const dedupeKey = itemId || detailHref || `${title}|${cover}`;
          if (dedupeKey && seen.has(dedupeKey)) return;
          if (dedupeKey) seen.add(dedupeKey);
          results.push(makeItem(source, {
            id: itemId,
            title,
            author: readJsonRule(item, rule.ruleSearch?.author, source, targetUrl),
            summary: readJsonRule(item, rule.ruleSearch?.intro, source, targetUrl),
            cover: cover || undefined,
            detailHref,
            tags: readJsonRule(item, rule.ruleSearch?.kind, source, targetUrl).split(/[,，\s]+/).filter(Boolean),
          }));
        });
      } else {
        const $ = cheerio.load(html);
        const items = selectElements($, $.root(), rule.ruleSearch.bookList);
        pageCount = items.length;
        items.each((_, element) => {
          const root = $(element);
          const detailHref = readValue($, root, rule.ruleSearch?.bookUrl, targetUrl);
          const title = readValue($, root, rule.ruleSearch?.name, targetUrl);
          if (!title && !detailHref) return;
          const cover = readValue($, root, rule.ruleSearch?.coverUrl, targetUrl);
          const dedupeKey = detailHref || `${title}|${cover}`;
          if (dedupeKey && seen.has(dedupeKey)) return;
          if (dedupeKey) seen.add(dedupeKey);
          results.push(makeItem(source, {
            id: detailHref || undefined,
            title,
            author: readValue($, root, rule.ruleSearch?.author, targetUrl),
            summary: readValue($, root, rule.ruleSearch?.intro, targetUrl),
            cover: cover || undefined,
            detailHref,
            tags: readValue($, root, rule.ruleSearch?.kind, targetUrl).split(/[,，\s]+/).filter(Boolean),
          }));
        });
      }
      if (pageCount === 0) break;
    }
    searchCache.set(cacheKey, { data: results, expiresAt: Date.now() + cacheTTL });
    return { source, results };
  }

  async searchBooks(q: string, sourceId?: string): Promise<BookSearchResult> {
    const sources = await this.getSearchSources(sourceId);
    const results: BookListItem[] = [];
    const failedSources: BookSearchFailure[] = [];
    await Promise.all(sources.map(async (source) => {
      try {
        const sourceResult = await this.searchBooksSource(q, source);
        results.push(...sourceResult.results);
      } catch (error) {
        failedSources.push({ sourceId: source.id, sourceName: source.name, error: (error as Error).message });
      }
    }));
    return { results, failedSources };
  }

  async getCatalog(sourceId: string, href?: string): Promise<BookCatalogResult> {
    const source = await getSourceById(sourceId);
    return {
      sourceId: source.id,
      sourceName: source.name,
      title: source.name,
      href: href || source.url,
      entries: [],
      navigation: [],
    };
  }

  async getChaptersByBookId(sourceId: string, bookId: string): Promise<BookChapter[]> {
    const source = await getSourceById(sourceId);
    const rule = getRule(source);
    const base = sourceBase(source);
    const searchBookUrlRule = rule.ruleSearch?.bookUrl || '';
    const detailHref = /^https?:\/\//i.test(bookId) || bookId.startsWith('/')
      ? normalizeUrl(base, bookId)
      : /\{\{\s*(?:\$\.id|id)\s*\}\}|\{id\}/.test(searchBookUrlRule)
        ? normalizeUrl(base, searchBookUrlRule
          .replace(/\{\{\s*\$\.id\s*\}\}/g, encodeURIComponent(bookId))
          .replace(/\{\{\s*id\s*\}\}/g, encodeURIComponent(bookId))
          .replace(/\{id\}/g, encodeURIComponent(bookId)))
        : '';
    if (!detailHref) throw new Error('该 Legado 书源无法通过 bookId 定位详情，请重新搜索后打开');
    const detail = await this.getBookDetail(sourceId, detailHref, { id: bookId, detailHref });
    const tocHref = detail.acquisitionLinks.find((item) => item.rel === 'legado:chapters' || item.type.toLowerCase().includes('legado-chapters'))?.href;
    if (!tocHref) return [];
    return this.getChapters(sourceId, tocHref);
  }

  async getBookDetail(sourceId: string, href: string, fallback?: Partial<BookDetail>): Promise<BookDetail> {
    const source = await getSourceById(sourceId);
    const rule = getRule(source);
    const detailHref = href || fallback?.detailHref || '';
    const cacheKey = `${LEGADO_CACHE_VERSION}|detail|${source.id}|${detailHref}`;
    const { cacheTTL } = await resolveLegadoConfig();
    const cached = detailCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) return { ...cached.data, ...(!href && fallback ? fallback : {}) };

    let detail: BookDetail | null = null;
    if (detailHref && rule.ruleBookInfo) {
      const targetUrl = rule.bookInfoUrl ? buildUrlFromTemplate(rule.bookInfoUrl, source, undefined, 1, detailHref).replace(/\{bookUrl\}/g, encodeURIComponent(detailHref)) : detailHref;
      const html = await fetchText(source, targetUrl);
      const json = parseJsonMaybe(html);
      const $ = json ? null : cheerio.load(html);
      const root = $?.root();
      const read = (itemRule?: string) => json
        ? readJsonRule(json, itemRule, source, targetUrl)
        : readValue($ as cheerio.CheerioAPI, root as cheerio.Cheerio<any>, itemRule, targetUrl);
      const tocUrl = read(rule.ruleBookInfo.tocUrl) || (rule.tocUrl ? buildUrlFromTemplate(rule.tocUrl, source, undefined, 1, detailHref).replace(/\{bookUrl\}/g, encodeURIComponent(detailHref)) : targetUrl);
      const cover = read(rule.ruleBookInfo.coverUrl) || fallback?.cover;
      const title = read(rule.ruleBookInfo.name) || fallback?.title || '未命名电子书';
      const chapterCountText = json
        ? jsonPrimitiveToString(readJsonPath(json, '@json:$.data.nums') ?? readJsonPath(json, '@json:$.data.chapter_nums'))
        : '';
      const chapterCount = chapterCountText ? Number(chapterCountText) : NaN;
      const hasKnownEmptyChapters = Number.isFinite(chapterCount) && chapterCount <= 0;
      const acquisitionLinks: BookAcquisitionLink[] = hasKnownEmptyChapters ? [] : [{ rel: 'legado:chapters', type: 'application/x-legado-chapters+json', href: tocUrl, title: '章节目录' }];
      detail = {
        id: fallback?.id || stableId(`${source.id}|${detailHref || title}`),
        sourceId,
        sourceName: source.name,
        title,
        author: read(rule.ruleBookInfo.author) || fallback?.author,
        cover: cover || undefined,
        summary: read(rule.ruleBookInfo.intro) || fallback?.summary,
        tags: read(rule.ruleBookInfo.kind).split(/[,，\s]+/).filter(Boolean),
        categories: read(rule.ruleBookInfo.kind).split(/[,，\s]+/).filter(Boolean),
        detailHref,
        acquisitionLinks,
        navigation: hasKnownEmptyChapters ? [] : [{ title: '目录', href: tocUrl, rel: 'legado:toc', type: 'application/x-legado-chapters+json' }],
      };
    }

    if (!detail) {
      const tocUrl = fallback?.acquisitionLinks?.[0]?.href || detailHref;
      detail = {
        id: fallback?.id || stableId(`${source.id}|${detailHref || fallback?.title || ''}`),
        sourceId,
        sourceName: source.name,
        title: fallback?.title || '未命名电子书',
        author: fallback?.author,
        cover: fallback?.cover,
        summary: fallback?.summary,
        detailHref,
        acquisitionLinks: [{ rel: 'legado:chapters', type: 'application/x-legado-chapters+json', href: tocUrl, title: '章节目录' }],
        navigation: [{ title: '目录', href: tocUrl, rel: 'legado:toc', type: 'application/x-legado-chapters+json' }],
      };
    }
    detailCache.set(cacheKey, { data: detail, expiresAt: Date.now() + cacheTTL });
    return detail;
  }

  async getChapters(sourceId: string, tocHref: string): Promise<BookChapter[]> {
    const source = await getSourceById(sourceId);
    const rule = getRule(source);
    if (!rule.ruleToc?.chapterList) throw new Error('该 Legado 书源缺少目录规则');
    const cacheKey = `${LEGADO_CACHE_VERSION}|toc|${source.id}|${tocHref}`;
    const { cacheTTL } = await resolveLegadoConfig();
    const cached = tocCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) return cached.data;

    const targetUrl = normalizeUrl(sourceBase(source), tocHref);
    const html = await fetchText(source, targetUrl);
    const chapters: BookChapter[] = [];
    const json = parseJsonMaybe(html);
    if (json && ruleIsJson(rule.ruleToc.chapterList)) {
      const items = selectJsonItems(json, rule.ruleToc.chapterList);
      items.forEach((item, index) => {
        const title = readJsonRule(item, rule.ruleToc?.chapterName, source, targetUrl) || `第 ${index + 1} 章`;
        const href = readJsonRule(item, rule.ruleToc?.chapterUrl, source, targetUrl)
          || fallbackChapterHrefFromItem(item, rule.ruleToc?.chapterUrl, targetUrl);
        if (!href) return;
        const normalizedHref = normalizeUrl(targetUrl, href);
        chapters.push({ id: stableId(`${source.id}|${normalizedHref}`), title, href: normalizedHref, order: index });
      });
    } else {
      const $ = cheerio.load(html);
      const items = selectElements($, $.root(), rule.ruleToc.chapterList);
      items.each((index, element) => {
        const root = $(element);
        const title = readValue($, root, rule.ruleToc?.chapterName, targetUrl) || `第 ${index + 1} 章`;
        const href = readValue($, root, rule.ruleToc?.chapterUrl, targetUrl) || root.attr('href') || '';
        if (!href) return;
        const normalizedHref = normalizeUrl(targetUrl, href);
        chapters.push({ id: stableId(`${source.id}|${normalizedHref}`), title, href: normalizedHref, order: index });
      });
    }
    tocCache.set(cacheKey, { data: chapters, expiresAt: Date.now() + cacheTTL });
    return chapters;
  }

  async getChapterContent(sourceId: string, chapterHref: string, tocHref?: string): Promise<BookChapterContent> {
    const source = await getSourceById(sourceId);
    const rule = getRule(source);
    if (!rule.ruleContent?.content) throw new Error('该 Legado 书源缺少正文规则');
    const targetUrl = normalizeUrl(sourceBase(source), chapterHref);
    const cacheKey = `${LEGADO_CACHE_VERSION}|chapter|${source.id}|${targetUrl}`;
    const cached = chapterCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) return cached.data;

    const html = await fetchText(source, targetUrl);
    const rawContent = contentFromRule(html, rule.ruleContent.content, targetUrl);
    const chapters = tocHref ? await this.getChapters(sourceId, tocHref).catch(() => []) : [];
    const index = chapters.findIndex((item) => item.href === targetUrl || item.href === chapterHref);
    const content: BookChapterContent = {
      id: stableId(`${source.id}|${targetUrl}`),
      title: index >= 0 ? chapters[index].title : '',
      href: targetUrl,
      content: cleanContent(rawContent),
      previousHref: index > 0 ? chapters[index - 1].href : undefined,
      nextHref: index >= 0 && index + 1 < chapters.length ? chapters[index + 1].href : undefined,
    };
    chapterCache.set(cacheKey, { data: content, expiresAt: Date.now() + 24 * 60 * 60 * 1000 });
    return content;
  }

  async getSourceById(sourceId: string): Promise<BookSource> {
    return getSourceById(sourceId);
  }

  async detectCapabilitiesFromSource(source: BookSource): Promise<BookSourceCapabilities> {
    return {
      searchSupported: !!source.legado?.searchUrl,
      catalogSupported: false,
      searchMode: source.legado?.searchUrl ? 'legado' : 'disabled',
      catalogMode: 'legado',
      acquisitionTypes: ['application/x-legado-chapters+json'],
      lastCheckedAt: Date.now(),
    };
  }
}

export const legadoClient = new LegadoClient();
