/* Análisis de servicios educativos (SSEE) con pocos usuarios dentro de los ítems del PAE.
   Datos: data/2026.js, data/2027.js, data/ubigeo.js. Mapa propio en canvas (sin dependencias). */
{
'use strict';
const $ = s => document.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const fmt = n => Math.round(n).toLocaleString('es-PE');
const f1 = n => (Number.isFinite(n) ? n : 0).toLocaleString('es-PE', { minimumFractionDigits: 1, maximumFractionDigits: 1 });
const pc = (a, b) => b ? f1(100 * a / b) + '%' : '—';
const tcase = s => String(s).toLowerCase().replace(/(^|[\s(\-/])([a-záéíóúñ])/g, (m, a, b) => a + b.toUpperCase());
const median = a => { if (!a.length) return NaN; const b = [...a].sort((x, y) => x - y), m = b.length >> 1; return b.length % 2 ? b[m] : (b[m - 1] + b[m]) / 2; };

const RAW = window.SAE_DATA || {}, UBI = window.SAE_UBIGEO || {};
const TY = ['A', 'B', 'C', 'D'];
const TCOL = { A: '#257DE0', B: '#00B894', C: '#F2A600', D: '#EE7FAC' };
const TNAME = { A: 'Comparte local', B: 'Vecino cercano', C: 'Distancia media', D: 'Aislado (validar ruta)' };
const tWhat = t => ({ A: 'Comparte el local con otro servicio educativo.', B: `Local propio, a ${f1(S.kb)} km o menos de otro SSEE del ítem.`, C: `Local propio, a entre ${f1(S.kb)} y ${f1(S.kc)} km de la IE más cercana del mismo ítem.`, D: `Aislado, a más de ${f1(S.kc)} km de otro SSEE del mismo ítem (o sin coordenadas).` }[t]);
const TALT = { A: 'Está en la ruta: mantener la entrega en su local, como está costeado.', B: 'Está en la ruta del ítem: mantener la entrega en su local, sin viaje adicional.', C: 'Validar con la ruta de distribución; si queda fuera, kit con periodo ampliado.', D: 'Validar con la ruta (terrestre o fluvial); si queda fuera, kit con periodo ampliado.' };
const RAMP = ['#C9DDF6', '#9CC1EE', '#6BA2E5', '#3B7FD6', '#1B5DB0', '#123F7A'];
const rampOf = n => RAMP[n >= 20 ? 5 : n >= 10 ? 4 : n >= 5 ? 3 : n >= 3 ? 2 : n >= 2 ? 1 : 0];
const BASES = {
  osm: ['https://tile.openstreetmap.org/{z}/{x}/{y}.png', '© OpenStreetMap'],
  topo: ['https://a.tile.opentopomap.org/{z}/{x}/{y}.png', '© OpenStreetMap · OpenTopoMap'],
  sat: ['https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', '© Esri'],
};

/* ---------- estado ---------- */
const S = { y: '2027', n: 1, mode: 'eq', kb: 2, kc: 5, f: { ut: '', dep: '', fo: '', ds: '', fon: '' }, tf: '', geo: 'hull',
  lyr: { items: true, core: true, lines: true, bg: true, mer: true, bn: true }, base: 'osm', focus: -1, sel: -1,
  isort: { k: 'nc', d: -1 }, ssort: { k: 't', d: 1 }, ilim: 25, slim: 50, iq: '', sq: '' };
try { const sv = JSON.parse(localStorage.getItem('sae-pocos') || '{}'); for (const k of ['y', 'n', 'mode', 'kb', 'kc', 'geo', 'base']) if (sv[k] != null) S[k] = sv[k]; if (sv.lyr) Object.assign(S.lyr, sv.lyr); if (!['none', 'osm', 'topo', 'sat'].includes(S.base)) S.base = 'osm'; } catch (e) { }
const save = () => { try { localStorage.setItem('sae-pocos', JSON.stringify({ y: S.y, n: S.n, mode: S.mode, kb: S.kb, kc: S.kc, geo: S.geo, base: S.base, lyr: S.lyr })); } catch (e) { } };

/* ---------- preparación por año ---------- */
const merc = (lat, lon) => { const s = Math.sin(lat * Math.PI / 180); return [(lon + 180) / 360 * 256, (0.5 - Math.log((1 + s) / (1 - s)) / (4 * Math.PI)) * 256]; };
const PREP = {};
function prep(y) {
  if (PREP[y]) return PREP[y];
  const D = RAW[y], c = D.col, n = D.n, LAT = new Float64Array(n), LON = new Float64Array(n), WX = new Float64Array(n), WY = new Float64Array(n), has = new Uint8Array(n);
  for (let i = 0; i < n; i++) { if (c.la[i]) { LAT[i] = c.la[i] / 1e4; LON[i] = c.lo[i] / 1e4; const w = merc(LAT[i], LON[i]); WX[i] = w[0]; WY[i] = w[1]; has[i] = 1; } }
  const ubA = D.dict.ub.map(u => UBI[u] || ['Sin dato', 'Sin dato', 'Sin dato', 0, 'Sin dato']);
  const lcN = new Map(); for (const l of c.lc) if (l >= 0) lcN.set(l, (lcN.get(l) || 0) + 1);
  const mem = D.dict.it.map(() => []); for (let i = 0; i < n; i++) if (c.it[i] >= 0) mem[c.it[i]].push(i);
  const itUT = mem.map(m => m.length ? D.dict.ut[c.ut[m[0]]] : '');
  return PREP[y] = { D, c, n, LAT, LON, WX, WY, has, ubA, lcN, mem, itUT, gcache: {} };
}
let P = prep(S.y in RAW ? S.y : (S.y = '2027'));

/* ---------- capas de entorno: mercados y Banco de la Nación (data/mercados.js, data/bn.js) ---------- */
const POI = window.SAE_POI || {};
const PL = { mer: { col: '#6A1B9A', shape: 'sq', name: 'Mercados' }, bn: { col: '#C62828', shape: 'dia', name: 'Banco de la Nación' } };
const hav = (a, b, c, d) => { const r = Math.PI / 180, x = Math.sin((c - a) * r / 2) ** 2 + Math.cos(a * r) * Math.cos(c * r) * Math.sin((d - b) * r / 2) ** 2; return 12742 * Math.asin(Math.sqrt(x)); };
for (const k in PL) {
  const L = POI[k] && Array.isArray(POI[k].rows) ? POI[k] : { rows: [], cats: [] }, p = PL[k], n = L.rows.length;
  Object.assign(p, { L, n, WX: new Float64Array(n), WY: new Float64Array(n), g: new Map() });
  L.rows.forEach((r, i) => { const w = merc(r[0], r[1]); p.WX[i] = w[0]; p.WY[i] = w[1]; if (k === 'bn' && r[2] > 1) return; const key = Math.floor(r[0] * 4) + ',' + Math.floor(r[1] * 4); if (!p.g.has(key)) p.g.set(key, []); p.g.get(key).push(i); });
}
const poiCat = (k, r) => (PL[k].L.cats || [])[r[2]] || '';
function nearestPOI(k, lat, lon) {
  const p = PL[k]; if (!p.n) return null; const ci = Math.floor(lat * 4), cj = Math.floor(lon * 4); let best = -1, bd = Infinity;
  for (let rad = 0; rad <= 10; rad++) {
    for (let a = ci - rad; a <= ci + rad; a++) for (let b = cj - rad; b <= cj + rad; b++) {
      if (Math.max(Math.abs(a - ci), Math.abs(b - cj)) !== rad) continue; const arr = p.g.get(a + ',' + b); if (!arr) continue;
      for (const i of arr) { const r = p.L.rows[i], d = hav(lat, lon, r[0], r[1]); if (d < bd) { bd = d; best = i; } } }
    if (best >= 0 && bd <= rad * 26) break; }
  return best >= 0 ? { i: best, d: bd, r: p.L.rows[best] } : null;
}
const NPC = {}; const nearOf = (k, i) => { const key = S.y + k; const m = NPC[key] || (NPC[key] = new Map()); if (!m.has(i)) m.set(i, P.has[i] ? nearestPOI(k, P.LAT[i], P.LON[i]) : null); return m.get(i); };
const itName = k => { const s = P.D.dict.it[k] || '', p = s.split(' | '); return { item: p[1] || s, com: p[0] || '' }; };
const dep = i => P.ubA[P.c.ub[i]][0], dist = i => P.ubA[P.c.ub[i]][2], prov = i => P.ubA[P.c.ub[i]][1];
const ds149 = i => P.ubA[P.c.ub[i]][3] === 1, fondes = i => P.ubA[P.c.ub[i]][4];
const forma = i => P.D.dict.fo[P.c.fo[i]], ut = i => P.D.dict.ut[P.c.ut[i]];

/* ---------- geometría: Minimum Bounding Geometry ---------- */
function hull(p) {
  const s = [...new Map(p.map(q => [q[0].toFixed(4) + ',' + q[1].toFixed(4), q])).values()].sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  if (s.length < 3) return s;
  const cr = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]), lo = [], up = [];
  for (const q of s) { while (lo.length > 1 && cr(lo[lo.length - 2], lo[lo.length - 1], q) <= 0) lo.pop(); lo.push(q); }
  for (let k = s.length - 1; k >= 0; k--) { const q = s[k]; while (up.length > 1 && cr(up[up.length - 2], up[up.length - 1], q) <= 0) up.pop(); up.push(q); }
  return lo.slice(0, -1).concat(up.slice(0, -1));
}
const bbox = Q => { let a = 1e18, b = 1e18, c = -1e18, d = -1e18; for (const q of Q) { a = Math.min(a, q[0]); b = Math.min(b, q[1]); c = Math.max(c, q[0]); d = Math.max(d, q[1]); } return [a, b, c, d]; };
function minCircle(pts) {
  const p = pts.slice(); for (let i = p.length - 1; i > 0; i--) { const j = (Math.random() * (i + 1)) | 0;[p[i], p[j]] = [p[j], p[i]]; }
  const inC = (c, q) => c && Math.hypot(q[0] - c[0], q[1] - c[1]) <= c[2] + 1e-7;
  const c2 = (a, b) => [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2, Math.hypot(a[0] - b[0], a[1] - b[1]) / 2];
  const c3 = (a, b, c) => { const d = 2 * (a[0] * (b[1] - c[1]) + b[0] * (c[1] - a[1]) + c[0] * (a[1] - b[1])); if (Math.abs(d) < 1e-12) { const o = [c2(a, b), c2(a, c), c2(b, c)]; return o.sort((x, y) => y[2] - x[2])[0]; }
    const A = a[0] ** 2 + a[1] ** 2, B = b[0] ** 2 + b[1] ** 2, C = c[0] ** 2 + c[1] ** 2, x = (A * (b[1] - c[1]) + B * (c[1] - a[1]) + C * (a[1] - b[1])) / d, y = (A * (c[0] - b[0]) + B * (a[0] - c[0]) + C * (b[0] - a[0])) / d; return [x, y, Math.hypot(a[0] - x, a[1] - y)]; };
  let c = null;
  for (let i = 0; i < p.length; i++) if (!inC(c, p[i])) { c = [p[i][0], p[i][1], 0]; for (let j = 0; j < i; j++) if (!inC(c, p[j])) { c = c2(p[i], p[j]); for (let k = 0; k < j; k++) if (!inC(c, p[k])) c = c3(p[i], p[j], p[k]); } }
  return c;
}
const circlePoly = (c, r) => Array.from({ length: 72 }, (_, k) => [c[0] + r * Math.cos(k * Math.PI / 36), c[1] + r * Math.sin(k * Math.PI / 36)]);
function geom(idx, type) {
  const v = idx.filter(i => P.has[i]); if (!v.length) return null;
  let la0 = 0, lo0 = 0; for (const i of v) { la0 += P.LAT[i]; lo0 += P.LON[i]; } la0 /= v.length; lo0 /= v.length;
  const kx = 111.32 * Math.cos(la0 * Math.PI / 180), ky = 110.574, xy = v.map(i => [(P.LON[i] - lo0) * kx, (P.LAT[i] - la0) * ky]);
  const h = hull(xy); let poly;
  if (type === 'circ' || h.length < 3) { const c = minCircle(h.length ? h : xy); poly = circlePoly(c, Math.max(c[2], h.length < 3 ? 0.6 : 0)); }
  else if (type === 'env') { const [a, b, c, d] = bbox(h); poly = [[a, b], [c, b], [c, d], [a, d]]; }
  else if (type === 'rect') { let best = 1e18; for (let k = 0; k < h.length; k++) { const p = h[k], q = h[(k + 1) % h.length], t = Math.atan2(q[1] - p[1], q[0] - p[0]), co = Math.cos(t), si = Math.sin(t), R = h.map(z => [z[0] * co + z[1] * si, -z[0] * si + z[1] * co]), [a, b, c, d] = bbox(R), A = (c - a) * (d - b); if (A < best) { best = A; poly = [[a, b], [c, b], [c, d], [a, d]].map(z => [z[0] * co - z[1] * si, z[0] * si + z[1] * co]); } } }
  else poly = h;
  let area = 0; for (let k = 0; k < poly.length; k++) { const p = poly[k], q = poly[(k + 1) % poly.length]; area += p[0] * q[1] - q[0] * p[1]; }
  const ring = poly.map(z => merc(z[1] / ky + la0, z[0] / kx + lo0));
  return { ring, area: Math.abs(area) / 2, bb: bbox(ring), n: v.length };
}
const fullGeom = it => { const key = S.geo; const gc = P.gcache[key] || (P.gcache[key] = new Map()); if (!gc.has(it)) gc.set(it, geom(P.mem[it], key)); return gc.get(it); };

/* ---------- cálculo principal ---------- */
let R = null;
function pass(i) {
  const f = S.f, c = P.c;
  if (f.ut && P.D.dict.ut[c.ut[i]] !== f.ut) return false;
  if (f.dep && dep(i) !== f.dep) return false;
  if (f.fo && P.D.dict.fo[c.fo[i]] !== f.fo) return false;
  if (f.ds && (ds149(i) ? '1' : '0') !== f.ds) return false;
  if (f.fon && fondes(i) !== f.fon) return false;
  return true;
}
function compute() {
  const c = P.c, n = P.n, hist = new Array(16).fill(0), cand = [], pos = new Int32Array(n).fill(-1);
  for (let i = 0; i < n; i++) {
    if (!pass(i)) continue; const u = c.us[i]; hist[Math.min(u, 16) - 1]++;
    if (S.mode === 'eq' ? u === S.n : u <= S.n) { pos[i] = cand.length; cand.push(i); }
  }
  const m = cand.length, t = new Uint8Array(m), nn = new Int32Array(m).fill(-1), d = new Float64Array(m).fill(NaN), comp = new Uint8Array(m);
  for (let k = 0; k < m; k++) {
    const i = cand[k], it = c.it[i]; comp[k] = c.lc[i] >= 0 && P.lcN.get(c.lc[i]) > 1 ? 1 : 0;
    if (it >= 0 && P.has[i]) { const la = P.LAT[i], lo = P.LON[i], kx = 111.32 * Math.cos(la * Math.PI / 180); let b = 1e9, bj = -1;
      for (const j of P.mem[it]) { if (j === i || !P.has[j]) continue; const dx = (P.LON[j] - lo) * kx, dy = (P.LAT[j] - la) * 110.574, dd = dx * dx + dy * dy; if (dd < b) { b = dd; bj = j; } }
      if (bj >= 0) { nn[k] = bj; d[k] = Math.sqrt(b); } }
    t[k] = comp[k] ? 0 : !(d[k] >= 0) ? 3 : d[k] <= S.kb ? 1 : d[k] <= S.kc ? 2 : 3;
  }
  const items = new Map();
  for (let k = 0; k < m; k++) { const it = c.it[cand[k]]; if (it < 0) continue; let o = items.get(it); if (!o) items.set(it, o = { it, ks: [], cnt: [0, 0, 0, 0], usc: 0 }); o.ks.push(k); o.cnt[t[k]]++; o.usc += c.us[cand[k]]; }
  const candSet = new Set(cand);
  for (const o of items.values()) {
    const mem = P.mem[o.it]; o.n = mem.length; o.nc = o.ks.length; o.us = 0; for (const j of mem) o.us += c.us[j];
    o.g = fullGeom(o.it); o.core = geom(mem.filter(j => !candSet.has(j)), S.geo);
    o.a = o.g ? o.g.area : 0; o.ac = o.core ? o.core.area : 0; o.red = o.a > 0 ? Math.max(0, 100 * (1 - o.ac / o.a)) : 0;
    const nm = itName(o.it); o.item = nm.item; o.com = nm.com; o.ut = P.itUT[o.it];
    const fc = {}, pe = new Set(); for (const j of mem) { const f = forma(j); fc[f] = (fc[f] || 0) + 1; pe.add(P.D.dict.pe[c.pe[j]]); }
    o.hoy = Object.entries(fc).sort((a, b) => b[1] - a[1]).map(([f, v]) => f + ' ' + v).join(' · ') + ' · periodo ' + [...pe].join('/').toLowerCase();
  }
  const cnt = [0, 0, 0, 0], us = [0, 0, 0, 0]; let usT = 0, kit = 0, dsN = 0; const dl = [];
  for (let k = 0; k < m; k++) { const i = cand[k]; cnt[t[k]]++; us[t[k]] += c.us[i]; usT += c.us[i]; if (forma(i) === 'CC-KIT') kit++; if (ds149(i)) dsN++; if (d[k] >= 0) dl.push(d[k]); }
  R = { cand, pos, t, nn, d, comp, items, hist, cnt, us, usT, kit, dsN, dmed: median(dl), m };
}
const vis = k => !S.tf || TY[R.t[k]] === S.tf;
const itemsArr = () => [...R.items.values()].filter(o => !S.tf || o.cnt[TY.indexOf(S.tf)] > 0);

/* ---------- encabezado y KPI ---------- */
const nLabel = () => S.mode === 'eq' ? (S.n === 1 ? 'con 1 usuario' : `con ${S.n} usuarios`) : `con hasta ${S.n} usuarios`;
function renderHead() {
  const m = R.m, ab = R.cnt[0] + R.cnt[1], nIt = R.items.size, tot = P.D.dict.it.length;
  $('#title').innerHTML = m ? `${fmt(m)} servicios educativos ${nLabel()} en ${fmt(nIt)} ítems: <b>${pc(ab, m)}</b> está en la ruta del ítem` : `No hay servicios educativos ${nLabel()} con estos filtros`;
  $('#sub').textContent = `${P.D.label} · ${P.D.fecha}. Tipo B hasta ${f1(S.kb)} km y tipo C hasta ${f1(S.kc)} km del servicio más cercano del mismo ítem.`;
  const K = [['Servicios educativos', fmt(m), pc(m, P.n) + ' del listado'], ['Usuarios', fmt(R.usT), 'Promedio ' + f1(R.usT / (m || 1)) + ' por SSEE'],
    ['Ítems con casos', fmt(nIt), 'de ' + fmt(tot) + ' ítems'], ['En el D.S. N° 149', pc(R.dsN, m), fmt(R.dsN) + ' SSEE'],
    ['Ya en kit de alimentos', pc(R.kit, m), fmt(R.kit) + ' SSEE'], ['Distancia mediana', Number.isFinite(R.dmed) ? f1(R.dmed) + ' km' : '—', 'al SSEE más cercano del ítem']];
  $('#kpis').innerHTML = K.map(k => `<div class="kpi"><small>${k[0]}</small><span class="num">${k[1]}</span><span>${esc(k[2])}</span></div>`).join('');
  $('#pkpi').innerHTML = [[fmt(m), 'SSEE ' + nLabel()], [fmt(nIt), 'ítems'], ...TY.map((x, j) => [fmt(R.cnt[j]), 'Tipo ' + x])].map(k => `<div><span class="num">${k[0]}</span><small>${esc(k[1])}</small></div>`).join('');
  $('#tbar').innerHTML = TY.map((x, j) => R.cnt[j] ? `<i style="flex-grow:${R.cnt[j]};background:${TCOL[x]}" title="Tipo ${x}: ${fmt(R.cnt[j])}">${R.cnt[j] / (m || 1) > .05 ? x + ' · ' + pc(R.cnt[j], m) : ''}</i>` : '').join('');
  $('#tleg').innerHTML = TY.map((x, j) => `<span><em style="background:${TCOL[x]}"></em>${x}. ${TNAME[x]}: <b>${fmt(R.cnt[j])}</b></span>`).join('');
  $('#legend').innerHTML = `<b>Servicios ${esc(nLabel())}</b><br>${TY.map(x => `<span class="dot" style="background:${TCOL[x]}"></span>${x}. ${TNAME[x]}`).join('<br>')}<div style="margin-top:6px"><b>Casos por ítem (MBG)</b></div><div class="ramp">${RAMP.map(c => `<i style="background:${c}"></i>`).join('')}</div><div><span>1</span><span>2</span><span>3–4</span><span>5–9</span><span>10–19</span><span>20+</span></div>${Object.keys(PL).filter(k => S.lyr[k]).map(k => !PL[k].n ? `<div style="margin-top:6px"><span class="poi ${PL[k].shape}" style="background:${PL[k].col}"></span><b>${PL[k].name}</b> · <span class="muted">sin datos: copia data/${k === 'mer' ? 'mercados' : 'bn'}.js</span></div>` : `<div style="margin-top:6px"><span class="poi ${PL[k].shape}" style="background:${PL[k].col}"></span><b>${PL[k].name}</b> · ${fmt(PL[k].n)} puntos<br><small>${(PL[k].L.cats || []).map((c, j) => [c, PL[k].L.rows.filter(r => r[2] === j).length]).filter(x => x[1]).map(x => esc(x[0]) + ': ' + fmt(x[1])).join('<br>')}</small></div>`).join('')}`;
}

/* ---------- tarjetas de tipología ---------- */
function renderCards() {
  const m = R.m;
  $('#cards').innerHTML = TY.map((x, j) => {
    let kit = 0, dsn = 0; const its = new Set(), dl = [];
    for (let k = 0; k < m; k++) if (R.t[k] === j) { const i = R.cand[k]; if (forma(i) === 'CC-KIT') kit++; if (ds149(i)) dsn++; if (P.c.it[i] >= 0) its.add(P.c.it[i]); if (R.d[k] >= 0) dl.push(R.d[k]); }
    const md = median(dl);
    return `<button class="card${S.tf === x ? ' on' : ''}" data-t="${x}" aria-pressed="${S.tf === x}">
      <div class="hd"><span class="badge" style="background:${TCOL[x]}">${x}</span><div><b>${TNAME[x]}</b><div class="what">${esc(tWhat(x))}</div></div></div>
      <div><span class="num">${fmt(R.cnt[j])}</span> <span class="muted">SSEE · ${pc(R.cnt[j], m)}</span></div>
      <dl><dt>Usuarios</dt><dd>${fmt(R.us[j])}</dd><dt>Ítems</dt><dd>${fmt(its.size)}</dd><dt>Ya en kit</dt><dd>${pc(kit, R.cnt[j])}</dd><dt>En D.S. N° 149</dt><dd>${pc(dsn, R.cnt[j])}</dd><dt>Distancia mediana</dt><dd>${Number.isFinite(md) ? f1(md) + ' km' : '—'}</dd></dl>
      <div class="alt"><b>Alternativa:</b> ${TALT[x]}</div></button>`;
  }).join('');
}

/* ---------- gráficos ---------- */
function renderCharts() {
  const h = R.hist, mx = Math.max(...h.slice(0, 15), 1) * 1.08;
  $('#chN').innerHTML = h.map((v, j) => { const u = j + 1, on = j < 15 && (S.mode === 'eq' ? u === S.n : u <= S.n);
    return `<button data-n="${u}" class="${on ? 'on' : ''}" ${j === 15 ? 'disabled' : ''} title="${fmt(v)} SSEE con ${j === 15 ? '16 o más' : u} usuario(s)"><i style="height:${Math.min(100, Math.max(2, 100 * v / mx))}%"><span>${fmt(v)}</span></i>${j === 15 ? '16+' : u}</button>`; }).join('');
  const by = new Map(); for (let k = 0; k < R.m; k++) { const u = ut(R.cand[k]); let o = by.get(u); if (!o) by.set(u, o = [0, 0, 0, 0]); o[R.t[k]]++; }
  const rows = [...by.entries()].map(([u, a]) => [u, a, a[0] + a[1] + a[2] + a[3]]).sort((a, b) => b[2] - a[2]).slice(0, 14), mm = Math.max(1, ...rows.map(r => r[2]));
  $('#chUT').innerHTML = rows.length ? rows.map(r => `<div class="hb" data-ut="${esc(r[0])}" role="button" tabindex="0"><span>${esc(tcase(r[0]))}</span><div class="st" style="width:${100 * r[2] / mm}%">${r[1].map((v, j) => v ? `<i style="flex:${v};background:${TCOL[TY[j]]}" title="Tipo ${TY[j]}: ${v}"></i>` : '').join('')}</div><b>${fmt(r[2])}</b></div>`).join('') : '<div class="empty">Sin casos</div>';
}

/* ---------- tablas ---------- */
const ICOLS = [['item', 'Ítem'], ['com', 'Comité de compra'], ['ut', 'Unidad territorial'], ['n', 'SSEE del ítem', 1], ['nc', 'Casos', 1], ['pct', '% casos', 1], ['A', 'A', 1], ['B', 'B', 1], ['C', 'C', 1], ['D', 'D', 1], ['a', 'Área MBG (km²)', 1], ['ac', 'Área sin casos (km²)', 1], ['red', 'Reducción', 1]];
const ival = (o, k) => k === 'pct' ? o.nc / o.n : TY.includes(k) ? o.cnt[TY.indexOf(k)] : o[k];
function itemRows() {
  const q = S.iq.trim().toLowerCase(); let a = itemsArr();
  if (q) a = a.filter(o => (o.item + ' ' + o.com + ' ' + o.ut).toLowerCase().includes(q));
  const { k, d } = S.isort; return a.sort((x, y) => { const p = ival(x, k), r = ival(y, k); return (typeof p === 'string' ? p.localeCompare(r) : p - r) * d; });
}
function renderItems() {
  const a = itemRows(), v = a.slice(0, S.ilim);
  $('#itab').innerHTML = `<thead><tr>${ICOLS.map(([k, l, nn]) => `<th data-s="${k}" class="${nn ? 'n ' : ''}${S.isort.k === k ? (S.isort.d > 0 ? 'asc' : 'desc') : ''}">${l}</th>`).join('')}</tr></thead><tbody>${v.length ? v.map(o => `<tr data-it="${o.it}"><td><b>${esc(o.item)}</b></td><td>${esc(o.com)}</td><td>${esc(tcase(o.ut))}</td><td class="n">${fmt(o.n)}</td><td class="n"><b>${fmt(o.nc)}</b></td><td class="n">${pc(o.nc, o.n)}</td>${o.cnt.map(x => `<td class="n">${x || ''}</td>`).join('')}<td class="n">${fmt(o.a)}</td><td class="n">${fmt(o.ac)}</td><td class="n">${f1(o.red)}%</td></tr>`).join('') : `<tr><td colspan="13" class="empty">Sin ítems para estos filtros</td></tr>`}</tbody>`;
  $('#imore').hidden = a.length <= S.ilim; $('#imore').textContent = `Mostrar más (${fmt(a.length - S.ilim)} restantes)`;
}
const SCOLS = [['cm', 'Código modular'], ['nm', 'Institución educativa'], ['dist', 'Distrito'], ['item', 'Ítem'], ['nv', 'Nivel'], ['fo', 'Forma'], ['us', 'Usuarios', 1], ['t', 'Tipo'], ['vec', 'SSEE más cercano del ítem'], ['d', 'Distancia (km)', 1], ['ds', 'D.S. 149'], ['fon', 'FONDES'], ['dm', 'Mercado más cercano (km)', 1], ['db', 'Agencia BN más cercana (km)', 1]];
function sRow(k) {
  const i = R.cand[k], c = P.c, j = R.nn[k], it = c.it[i];
  return { k, cm: String(c.cm[i]).padStart(7, '0') + '-' + c.ax[i], nm: c.nm[i], dist: tcase(dist(i)) + ', ' + tcase(prov(i)) + ' (' + tcase(dep(i)) + ')', item: it >= 0 ? itName(it).item : 'Sin ítem', ut: ut(i),
    nv: tcase(P.D.dict.nv[c.nv[i]]), fo: forma(i), us: c.us[i], t: TY[R.t[k]], vec: j >= 0 ? c.nm[j] + ' (' + c.us[j] + ' us.)' : '—', d: R.d[k] >= 0 ? R.d[k] : NaN, ds: ds149(i) ? 'Sí' : 'No', fon: fondes(i), comp: R.comp[k], ...(() => { const a = nearOf('mer', i), b = nearOf('bn', i); return { dm: a ? a.d : NaN, nm_m: a ? a.r[3] : '', db: b ? b.d : NaN, nm_b: b ? b.r[3] : '' }; })() };
}
function ssRows() {
  const q = S.sq.trim().toLowerCase(), out = [];
  for (let k = 0; k < R.m; k++) { if (!vis(k)) continue; if (S.focus >= 0 && P.c.it[R.cand[k]] !== S.focus) continue; const r = sRow(k); if (q && !(r.cm + ' ' + r.nm + ' ' + r.dist + ' ' + r.item + ' ' + r.ut).toLowerCase().includes(q)) continue; out.push(r); }
  const { k, d } = S.ssort; return out.sort((x, y) => { const p = x[k], r = y[k]; if (typeof p === 'number') return ((Number.isFinite(p) ? p : 1e9) - (Number.isFinite(r) ? r : 1e9)) * d; return String(p).localeCompare(String(r)) * d || (x.d || 0) - (y.d || 0); });
}
function renderSSEE() {
  const a = ssRows(), v = a.slice(0, S.slim);
  $('#stab').innerHTML = `<thead><tr>${SCOLS.map(([k, l, nn]) => `<th data-s="${k}" class="${nn ? 'n ' : ''}${S.ssort.k === k ? (S.ssort.d > 0 ? 'asc' : 'desc') : ''}">${l}</th>`).join('')}</tr></thead><tbody>${v.length ? v.map(r => `<tr data-k="${r.k}"><td>${r.cm}</td><td>${esc(r.nm)}</td><td>${esc(r.dist)}</td><td>${esc(r.item)}</td><td>${esc(r.nv)}</td><td>${esc(r.fo)}</td><td class="n">${r.us}</td><td><span class="pill" style="background:${TCOL[r.t]}">${r.t}</span></td><td>${esc(r.vec)}</td><td class="n">${Number.isFinite(r.d) ? f1(r.d) : '—'}</td><td>${r.ds}</td><td>${esc(r.fon)}</td><td class="n" title="${esc(r.nm_m)}">${Number.isFinite(r.dm) ? f1(r.dm) : '—'}</td><td class="n" title="${esc(r.nm_b)}">${Number.isFinite(r.db) ? f1(r.db) : '—'}</td></tr>`).join('') : `<tr><td colspan="14" class="empty">Sin servicios para estos filtros</td></tr>`}</tbody>`;
  $('#smore').hidden = a.length <= S.slim; $('#smore').textContent = `Mostrar más (${fmt(a.length - S.slim)} restantes)`;
}
function toast(t) { const e = $('#toast'); e.textContent = t; e.classList.add('on'); clearTimeout(toast.h); toast.h = setTimeout(() => e.classList.remove('on'), 2200); }
const csvOf = (head, rows) => [head, ...rows].map(r => r.map(x => { const s = String(x ?? ''); return /[",;\n]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s; }).join(',')).join('\n');
const itemCSV = () => csvOf(['Ítem', 'Comité', 'Unidad territorial', 'SSEE del ítem', 'Usuarios del ítem', 'Casos', 'Usuarios casos', 'A', 'B', 'C', 'D', 'Área MBG km2', 'Área sin casos km2', 'Reducción %'], itemRows().map(o => [o.item, o.com, o.ut, o.n, o.us, o.nc, o.usc, ...o.cnt, o.a.toFixed(1), o.ac.toFixed(1), o.red.toFixed(1)]));
const ssCSV = () => csvOf(['Código modular-anexo', 'IE', 'Distrito', 'Unidad territorial', 'Ítem', 'Nivel', 'Forma', 'Usuarios', 'Tipo', 'Comparte local', 'SSEE más cercano', 'Distancia km', 'D.S. 149', 'FONDES', 'Mercado más cercano', 'Distancia mercado km', 'Agencia BN más cercana', 'Distancia agencia BN km'], ssRows().map(r => [r.cm, r.nm, r.dist, r.ut, r.item, r.nv, r.fo, r.us, r.t, r.comp ? 'Sí' : 'No', r.vec, Number.isFinite(r.d) ? r.d.toFixed(2) : '', r.ds, r.fon, r.nm_m, Number.isFinite(r.dm) ? r.dm.toFixed(2) : '', r.nm_b, Number.isFinite(r.db) ? r.db.toFixed(2) : '']));
function download(name, text) { try { const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob(['﻿' + text], { type: 'text/csv;charset=utf-8' })); a.download = name; document.body.appendChild(a); a.click(); a.remove(); toast('Descarga iniciada. Si no aparece, usa «Copiar».'); } catch (e) { toast('No se pudo descargar; usa «Copiar».'); } }
async function copy(text) { try { await navigator.clipboard.writeText(text); toast('Copiado al portapapeles'); } catch (e) { toast('El navegador no permitió copiar'); } }

/* ---------- panel lateral ---------- */
function renderPanel() {
  const el = $('#panel');
  if (S.focus < 0 || !R.items.has(S.focus)) {
    S.focus = -1; const top = itemsArr().sort((a, b) => b.nc - a.nc).slice(0, 12);
    el.innerHTML = `<h3>Vista nacional</h3><div class="sub">${esc(P.D.label)} · ${fmt(R.m)} SSEE ${esc(nLabel())}${S.tf ? ' · solo tipo ' + S.tf : ''}</div>
      <p class="small">Cada polígono es la Minimum Bounding Geometry de un ítem que contiene casos; su color indica cuántos tiene. Haz clic en un ítem o en un punto para ver su detalle y la propuesta de atención.</p>
      <h3 style="font-size:15px;margin-top:14px">Ítems con más casos</h3>
      <ul class="plist">${top.map(o => `<li data-it="${o.it}"><b>${esc(o.item)}</b><span class="num">${o.nc}</span><small>${esc(tcase(o.ut))} · ${fmt(o.n)} SSEE · ${pc(o.nc, o.n)} del ítem</small></li>`).join('') || '<li>Sin ítems</li>'}</ul>`;
    return;
  }
  const o = R.items.get(S.focus), ks = o.ks.slice().sort((a, b) => R.t[a] - R.t[b] || (R.d[a] || 0) - (R.d[b] || 0)), c = P.c;
  const ab = o.cnt[0] + o.cnt[1];
  let sel = '';
  if (S.sel >= 0 && R.pos[S.sel] >= 0) {
    const k = R.pos[S.sel], i = S.sel, j = R.nn[k], x = TY[R.t[k]];
    sel = `<div class="prop" style="border:2px solid ${TCOL[x]}"><p><span class="pill" style="background:${TCOL[x]}">Tipo ${x}</span> <b>${esc(c.nm[i])}</b></p>
      <p class="small">Cód. ${String(c.cm[i]).padStart(7, '0')}-${c.ax[i]} · ${esc(tcase(P.D.dict.nv[c.nv[i]]))} · ${c.us[i]} usuario(s) · ${esc(forma(i))} · ${esc(P.D.dict.pe[c.pe[i]])}<br>${esc(tcase(dist(i)))}, ${esc(tcase(prov(i)))} · ${ds149(i) ? 'En D.S. N° 149' : 'Fuera del D.S. N° 149'} · FONDES ${esc(fondes(i))}</p>
      <p class="small">${R.comp[k] ? 'Comparte local con otro servicio. ' : ''}${j >= 0 ? `Servicio más cercano del ítem: <b>${esc(c.nm[j])}</b> (${c.us[j]} usuarios, ${esc(forma(j))}) a <b>${f1(R.d[k])} km</b>.` : 'Sin coordenadas o sin otro servicio con coordenadas en el ítem.'}</p>
      ${(() => { const a = nearOf('mer', i), b = nearOf('bn', i); return a || b ? `<p class="small"><b>Entorno:</b> ${a ? `mercado más cercano <b>${esc(a.r[3])}</b> a ${f1(a.d)} km` : 'sin capa de mercados'} · ${b ? `agencia del BN <b>${esc(b.r[3])}</b> a ${f1(b.d)} km` : 'sin capa del BN'}</p>` : ''; })()}<p class="small"><b>Alternativa:</b> ${TALT[x]}</p></div>`;
  }
  el.innerHTML = `<button class="back" id="pback">← Vista nacional</button><h3>${esc(o.item)}</h3><div class="sub">Comité ${esc(o.com)} · ${esc(tcase(o.ut))}</div>
    <div class="mini"><div><small>SSEE del ítem</small><span class="num">${fmt(o.n)}</span></div><div><small>Casos ${esc(nLabel())}</small><span class="num">${fmt(o.nc)}</span> <span class="small muted">${pc(o.nc, o.n)}</span></div>
    <div><small>Área MBG del ítem</small><span class="num">${fmt(o.a)}</span> <span class="small muted">km²</span></div><div><small>Área sin los casos</small><span class="num">${fmt(o.ac)}</span> <span class="small muted">km² (−${f1(o.red)}%)</span></div></div>
    <div class="tbar" style="height:22px;margin:0">${TY.map((x, j) => o.cnt[j] ? `<i style="flex-grow:${o.cnt[j]};background:${TCOL[x]}">${o.cnt[j]}</i>` : '').join('')}</div>
    <div class="prop"><p><b>Propuesta para el ítem</b></p>
      <p class="small">Hoy en el ítem: ${esc(o.hoy)}.</p>
      ${ab ? `<p>${ab} de ${o.nc} están en la ruta del ítem (mismo local o a ${f1(S.kb)} km o menos de otro SSEE): se mantiene la entrega en su local.</p>` : ''}
      ${o.cnt[2] + o.cnt[3] ? `<p>${o.cnt[2] + o.cnt[3]} están a más de ${f1(S.kb)} km: validar con la ruta de distribución; si quedan fuera, kit con periodo ampliado.</p>` : ''}
      <p>Sin estos casos, la envolvente del ítem pasa de ${fmt(o.a)} a ${fmt(o.ac)} km² (−${f1(o.red)}%).</p></div>
    ${sel}<h3 style="font-size:15px;margin-top:6px">Casos del ítem</h3>
    <ul class="slist">${ks.map(k => { const i = R.cand[k], x = TY[R.t[k]]; return `<li data-i="${i}" class="${i === S.sel ? 'sel' : ''}"><span class="dot" style="background:${TCOL[x]}"></span><b>${esc(c.nm[i])}</b><span class="muted">${R.d[k] >= 0 ? f1(R.d[k]) + ' km' : '—'}</span><small>${esc(tcase(dist(i)))} · ${c.us[i]} us. · ${esc(forma(i))}${R.comp[k] ? ' · comparte local' : ''}</small></li>`; }).join('')}</ul>`;
}

/* ---------- motor de mapa (canvas, Web Mercator) ---------- */
const cv = $('#map'), ctx = cv.getContext('2d'), wrap = $('#mapwrap');
const V = { cx: 0, cy: 0, z: 5, W: 0, H: 0, dpr: 1, hov: null, anim: null };
const tiles = new Map(); let tileOK = 0, tileErr = 0;
const toS = (wx, wy) => { const s = 2 ** V.z; return [(wx - V.cx) * s + V.W / 2, (wy - V.cy) * s + V.H / 2]; };
const toW = (sx, sy) => { const s = 2 ** V.z; return [(sx - V.W / 2) / s + V.cx, (sy - V.H / 2) / s + V.cy]; };
let pending = false; const redraw = () => { if (!pending) { pending = true; requestAnimationFrame(() => { pending = false; draw(); }); } };
function resize() { const r = wrap.getBoundingClientRect(); V.dpr = Math.min(2, window.devicePixelRatio || 1); V.W = r.width; V.H = r.height; cv.width = r.width * V.dpr; cv.height = r.height * V.dpr; redraw(); }
new ResizeObserver(resize).observe(wrap);
function fitBB(bb, pad = 50, animate = true) {
  if (!bb) return; const dx = Math.max(bb[2] - bb[0], 1e-4), dy = Math.max(bb[3] - bb[1], 1e-4);
  const z = Math.max(4, Math.min(15, Math.log2(Math.min((V.W - 2 * pad) / dx, (V.H - 2 * pad) / dy))));
  go((bb[0] + bb[2]) / 2, (bb[1] + bb[3]) / 2, z, animate);
}
const reduced = matchMedia('(prefers-reduced-motion: reduce)').matches;
function go(cx, cy, z, animate = true) {
  if (!animate || reduced || !V.W) { V.cx = cx; V.cy = cy; V.z = z; V.anim = null; redraw(); return; }
  const a = { cx: V.cx, cy: V.cy, z: V.z }, t0 = performance.now(), dur = 900, an = V.anim = {};
  const step = now => { if (V.anim !== an) return; let t = Math.min(1, (now - t0) / dur); t = t < .5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2;
    const zm = Math.min(a.z, z) - Math.min(1.2, Math.abs(z - a.z) * .3 + 0.4) * Math.sin(Math.PI * t) * (Math.hypot(cx - a.cx, cy - a.cy) * 2 ** Math.min(a.z, z) > V.W ? 1 : 0);
    V.cx = a.cx + (cx - a.cx) * t; V.cy = a.cy + (cy - a.cy) * t; V.z = a.z + (z - a.z) * t + (zm - Math.min(a.z, z)) * (t > 0 && t < 1 ? 1 : 0); draw(); if (t < 1) requestAnimationFrame(step); else V.anim = null; };
  requestAnimationFrame(step);
}
const isDark = () => { const t = document.documentElement.dataset.theme; return t === 'dark' || (t !== 'light' && matchMedia('(prefers-color-scheme: dark)').matches); };
let COLS = {}; const readCols = () => { COLS = isDark() ? { bg: '#0F1A2E', dot: 'rgba(200,215,240,.20)', ink: '#E8EDF6', card: '#131E33', muted: '#8C97AC' } : { bg: '#E9EEF5', dot: 'rgba(20,33,61,.20)', ink: '#14213D', card: '#FFFFFF', muted: '#6B7280' }; };
matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { readCols(); redraw(); });
new MutationObserver(() => { readCols(); redraw(); }).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });

function drawTiles() {
  const B = BASES[S.base]; if (!B) return;
  const tz = Math.max(0, Math.min(18, Math.round(V.z))), sc = 2 ** (V.z - tz), ts = 256 * sc, N = 2 ** tz;
  const [w0x, w0y] = toW(0, 0), [w1x, w1y] = toW(V.W, V.H), f = N / 256;
  for (let ty = Math.max(0, Math.floor(w0y * f)); ty <= Math.min(N - 1, Math.floor(w1y * f)); ty++)
    for (let tx = Math.floor(w0x * f); tx <= Math.floor(w1x * f); tx++) {
      const x = ((tx % N) + N) % N, url = B[0].replace('{z}', tz).replace('{x}', x).replace('{y}', ty);
      let im = tiles.get(url);
      if (!im) { im = new Image(); im.crossOrigin = 'anonymous'; im.onload = () => { im.ok = 1; tileOK++; updateNote(); redraw(); }; im.onerror = () => { im.bad = 1; tileErr++; updateNote(); }; im.src = url; tiles.set(url, im); if (tiles.size > 600) tiles.delete(tiles.keys().next().value); }
      if (im.ok) { const [sx, sy] = toS(tx * 256 / N, ty * 256 / N); ctx.drawImage(im, Math.floor(sx), Math.floor(sy), Math.ceil(ts) + 1, Math.ceil(ts) + 1); }
    }
}
function updateNote() {
  const B = BASES[S.base];
  $('#mapnote').textContent = !B ? 'Fondo: red de servicios educativos del listado' : tileErr > 6 && !tileOK ? 'El mapa base no está disponible en esta vista; se muestra la red de servicios educativos como fondo.' : B[1];
}
function path(ring) { ctx.beginPath(); ring.forEach((w, k) => { const [x, y] = toS(w[0], w[1]); k ? ctx.lineTo(x, y) : ctx.moveTo(x, y); }); ctx.closePath(); }
const inView = bb => { const [a, b] = toS(bb[0], bb[1]), [c, d] = toS(bb[2], bb[3]); return c > -50 && a < V.W + 50 && d > -50 && b < V.H + 50; };
function draw() {
  if (!R || !V.W) return; const dp = V.dpr; ctx.setTransform(dp, 0, 0, dp, 0, 0);
  ctx.fillStyle = COLS.bg; ctx.fillRect(0, 0, V.W, V.H);
  drawTiles();
  const z = V.z, c = P.c, foc = S.focus >= 0 ? R.items.get(S.focus) : null;
  if (S.lyr.bg) { ctx.fillStyle = COLS.dot; const sz = Math.max(1.2, Math.min(3.5, (z - 3) * .5)), s = 2 ** z, ox = V.W / 2 - V.cx * s, oy = V.H / 2 - V.cy * s;
    for (let i = 0; i < P.n; i++) { if (!P.has[i]) continue; const x = P.WX[i] * s + ox, y = P.WY[i] * s + oy; if (x < -4 || y < -4 || x > V.W + 4 || y > V.H + 4) continue; ctx.fillRect(x - sz / 2, y - sz / 2, sz, sz); } }
  const its = itemsArr();
  if (S.lyr.items) for (const o of its) { if (!o.g || o === foc || !inView(o.g.bb)) continue; const col = rampOf(o.nc); path(o.g.ring);
    ctx.globalAlpha = foc ? .12 : .3; ctx.fillStyle = col; ctx.fill(); ctx.globalAlpha = foc ? .35 : .95; ctx.lineWidth = V.hov && V.hov.it === o.it ? 2.6 : 1; ctx.strokeStyle = V.hov && V.hov.it === o.it ? COLS.ink : RAMP[Math.min(5, RAMP.indexOf(col) + 2)]; ctx.stroke(); ctx.globalAlpha = 1; }
  if (foc && foc.g) {
    path(foc.g.ring); ctx.fillStyle = rampOf(foc.nc); ctx.globalAlpha = .16; ctx.fill(); ctx.globalAlpha = 1; ctx.setLineDash([7, 5]); ctx.lineWidth = 2.4; ctx.strokeStyle = COLS.ink; ctx.stroke(); ctx.setLineDash([]);
    if (S.lyr.core && foc.core) { path(foc.core.ring); ctx.fillStyle = '#1B64BE'; ctx.globalAlpha = .14; ctx.fill(); ctx.globalAlpha = .9; ctx.lineWidth = 2; ctx.strokeStyle = '#1B64BE'; ctx.stroke(); ctx.globalAlpha = 1; }
    for (const j of P.mem[foc.it]) { if (!P.has[j] || R.pos[j] >= 0) continue; const [x, y] = toS(P.WX[j], P.WY[j]); const r = Math.min(10, 2.5 + Math.sqrt(c.us[j]) / 3);
      ctx.beginPath(); ctx.arc(x, y, r, 0, 7); ctx.fillStyle = COLS.muted; ctx.globalAlpha = .55; ctx.fill(); ctx.globalAlpha = 1; ctx.lineWidth = 1; ctx.strokeStyle = COLS.card; ctx.stroke(); }
  }
  if (S.lyr.lines && (foc || z >= 8)) { ctx.lineWidth = 1.6; ctx.setLineDash([4, 3]);
    for (let k = 0; k < R.m; k++) { const i = R.cand[k], j = R.nn[k]; if (j < 0 || !vis(k) || (foc && c.it[i] !== foc.it)) continue; const [x, y] = toS(P.WX[i], P.WY[i]), [x2, y2] = toS(P.WX[j], P.WY[j]);
      if ((x < 0 && x2 < 0) || (x > V.W && x2 > V.W) || (y < 0 && y2 < 0) || (y > V.H && y2 > V.H)) continue; ctx.strokeStyle = TCOL[TY[R.t[k]]]; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x2, y2); ctx.stroke(); }
    ctx.setLineDash([]); }
  for (const kk of ['bn', 'mer']) { const p = PL[kk]; if (!S.lyr[kk] || !p.n) continue; const s = 2 ** z, ox = V.W / 2 - V.cx * s, oy = V.H / 2 - V.cy * s, sz = Math.max(4.5, Math.min(12, 3 + (z - 5) * 1.2));
    ctx.fillStyle = p.col; ctx.strokeStyle = '#fff'; ctx.lineWidth = z >= 7 ? 1.6 : 1; ctx.globalAlpha = foc ? .7 : 1;
    for (let i = 0; i < p.n; i++) { const x = p.WX[i] * s + ox, y = p.WY[i] * s + oy; if (x < -8 || y < -8 || x > V.W + 8 || y > V.H + 8) continue; ctx.beginPath();
      if (p.shape === 'sq') ctx.rect(x - sz / 2, y - sz / 2, sz, sz); else { const h = sz * .75; ctx.moveTo(x, y - h); ctx.lineTo(x + h, y); ctx.lineTo(x, y + h); ctx.lineTo(x - h, y); ctx.closePath(); }
      ctx.fill(); ctx.stroke(); }
    ctx.globalAlpha = 1; }
  if (S.sel >= 0 && P.has[S.sel]) { ctx.setLineDash([2, 4]); ctx.lineWidth = 2; for (const kk of ['mer', 'bn']) { const nb = S.lyr[kk] && nearOf(kk, S.sel); if (!nb) continue; const [x1, y1] = toS(P.WX[S.sel], P.WY[S.sel]), [x2, y2] = toS(PL[kk].WX[nb.i], PL[kk].WY[nb.i]); ctx.strokeStyle = PL[kk].col; ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke(); } ctx.setLineDash([]); }
  const r0 = Math.max(2.6, Math.min(foc ? 8 : 6.5, 2 + (z - 5) * .9));
  for (let pass = 0; pass < 2; pass++) for (let k = 0; k < R.m; k++) { const i = R.cand[k]; if (!P.has[i] || !vis(k)) continue; const inF = foc && c.it[i] === foc.it; if ((pass === 1) !== !!inF) continue;
    const [x, y] = toS(P.WX[i], P.WY[i]); if (x < -10 || y < -10 || x > V.W + 10 || y > V.H + 10) continue;
    ctx.beginPath(); ctx.arc(x, y, r0, 0, 7); ctx.fillStyle = TCOL[TY[R.t[k]]]; ctx.globalAlpha = foc && !inF ? .35 : 1; ctx.fill(); ctx.lineWidth = 1.4; ctx.strokeStyle = '#fff'; ctx.stroke(); ctx.globalAlpha = 1; }
  if (S.sel >= 0 && P.has[S.sel]) { const [x, y] = toS(P.WX[S.sel], P.WY[S.sel]); ctx.beginPath(); ctx.arc(x, y, r0 + 6, 0, 7); ctx.lineWidth = 3; ctx.strokeStyle = COLS.ink; ctx.stroke(); }
  if (z >= 7.5 && S.lyr.items) { ctx.font = '600 12px Inter, sans-serif'; ctx.textAlign = 'center'; let nL = 0;
    for (const o of its) { if (!o.g || !inView(o.g.bb) || nL > 40) continue; const [x, y] = toS((o.g.bb[0] + o.g.bb[2]) / 2, o.g.bb[1]); if (y < 12 || x < 30 || x > V.W - 30) continue; nL++;
      ctx.lineWidth = 3.5; ctx.strokeStyle = COLS.card; ctx.strokeText(o.item, x, y - 6); ctx.fillStyle = COLS.ink; ctx.fillText(o.item, x, y - 6); } }
}

/* ---------- interacción del mapa ---------- */
function pip(w, ring) { let ins = false; for (let a = 0, b = ring.length - 1; a < ring.length; b = a++) { const [xa, ya] = ring[a], [xb, yb] = ring[b]; if ((ya > w[1]) !== (yb > w[1]) && w[0] < (xb - xa) * (w[1] - ya) / (yb - ya) + xa) ins = !ins; } return ins; }
function hit(sx, sy) {
  let best = null, bd = 12 * 12; const foc = S.focus >= 0 ? R.items.get(S.focus) : null;
  for (let k = 0; k < R.m; k++) { const i = R.cand[k]; if (!P.has[i] || !vis(k)) continue; const [x, y] = toS(P.WX[i], P.WY[i]), d = (x - sx) ** 2 + (y - sy) ** 2; if (d < bd) { bd = d; best = { k, i, it: P.c.it[i] }; } }
  if (best) return best;
  if (foc) { bd = 9 * 9; for (const j of P.mem[foc.it]) { if (!P.has[j]) continue; const [x, y] = toS(P.WX[j], P.WY[j]), d = (x - sx) ** 2 + (y - sy) ** 2; if (d < bd) { bd = d; best = { m: j, it: foc.it }; } } if (best) return best; }
  { let pb = null, pd = 10 * 10; for (const kk of ['mer', 'bn']) { const p = PL[kk]; if (!S.lyr[kk] || !p.n || V.z < 6) continue; for (let i = 0; i < p.n; i++) { const [x, y] = toS(p.WX[i], p.WY[i]), d = (x - sx) ** 2 + (y - sy) ** 2; if (d < pd) { pd = d; pb = { poi: kk, pi: i }; } } } if (pb) return pb; }
  if (!S.lyr.items) return null; const w = toW(sx, sy); let sm = null;
  for (const o of itemsArr()) { if (!o.g) continue; const b = o.g.bb; if (w[0] < b[0] || w[0] > b[2] || w[1] < b[1] || w[1] > b[3]) continue; if (pip(w, o.g.ring) && (!sm || o.a < sm.a)) sm = o; }
  return sm ? { it: sm.it, hull: 1 } : null;
}
function showTip(h, sx, sy) {
  const tip = $('#tip'), c = P.c; if (!h) { tip.hidden = true; cv.classList.remove('hand'); return; }
  let html = '';
  if (h.poi) { const p = PL[h.poi], r = p.L.rows[h.pi]; html = `<b>${esc(r[3] || p.name)}</b><br>${esc(p.name)} · ${esc(poiCat(h.poi, r))}${r[4] ? '<br>Ubigeo ' + esc(r[4]) : ''}${r[5] ? '<br><span class="muted">Fuente: ' + esc(r[5]) + '</span>' : ''}`; }
  else if (h.k != null) { const k = h.k, i = h.i, x = TY[R.t[k]]; html = `<b>${esc(c.nm[i])}</b><br>Tipo ${x} · ${c.us[i]} usuario(s) · ${esc(forma(i))}<br>${esc(tcase(dist(i)))} · ${h.it >= 0 ? 'Ítem ' + esc(itName(h.it).item) : 'Sin ítem'}<br>${R.d[k] >= 0 ? 'Vecino a ' + f1(R.d[k]) + ' km' : 'Sin vecino con coordenadas'}${R.comp[k] ? ' · comparte local' : ''}`; }
  else if (h.m != null) { const j = h.m; html = `<b>${esc(c.nm[j])}</b><br>${c.us[j]} usuarios · ${esc(forma(j))} · ${esc(tcase(dist(j)))}`; }
  else { const o = R.items.get(h.it); html = `<b>Ítem ${esc(o.item)}</b><br>${esc(tcase(o.ut))} · ${fmt(o.n)} SSEE<br>${o.nc} casos (${pc(o.nc, o.n)}) · MBG ${fmt(o.a)} km²`; }
  tip.innerHTML = html; tip.hidden = false; const tw = tip.offsetWidth, th = tip.offsetHeight; tip.style.left = Math.min(sx, V.W - tw - 20) + 'px'; tip.style.top = Math.min(sy, V.H - th - 20) + 'px'; cv.classList.add('hand');
}
const ptrs = new Map(); let drag = null, pinch = null;
cv.addEventListener('pointerdown', e => { stopTour(); cv.setPointerCapture(e.pointerId); ptrs.set(e.pointerId, [e.offsetX, e.offsetY]); V.anim = null;
  if (ptrs.size === 1) drag = { x: e.offsetX, y: e.offsetY, cx: V.cx, cy: V.cy, moved: false };
  else if (ptrs.size === 2) { const [a, b] = [...ptrs.values()]; pinch = { d: Math.hypot(a[0] - b[0], a[1] - b[1]), z: V.z, w: toW((a[0] + b[0]) / 2, (a[1] + b[1]) / 2) }; drag = null; } });
cv.addEventListener('pointermove', e => {
  if (ptrs.has(e.pointerId)) ptrs.set(e.pointerId, [e.offsetX, e.offsetY]);
  if (pinch && ptrs.size === 2) { const [a, b] = [...ptrs.values()], d = Math.hypot(a[0] - b[0], a[1] - b[1]); V.z = Math.max(3, Math.min(17, pinch.z + Math.log2(d / pinch.d))); const s = 2 ** V.z, mx = (a[0] + b[0]) / 2, my = (a[1] + b[1]) / 2; V.cx = pinch.w[0] - (mx - V.W / 2) / s; V.cy = pinch.w[1] - (my - V.H / 2) / s; redraw(); return; }
  if (drag) { const dx = e.offsetX - drag.x, dy = e.offsetY - drag.y; if (Math.abs(dx) + Math.abs(dy) > 4) { drag.moved = true; cv.classList.add('drag'); $('#tip').hidden = true; } if (drag.moved) { const s = 2 ** V.z; V.cx = drag.cx - dx / s; V.cy = drag.cy - dy / s; redraw(); } return; }
  const h = hit(e.offsetX, e.offsetY), key = h ? (h.k ?? 'm' + h.m ?? '') + '|' + h.it : ''; if (key !== (V.hov && V.hov.key)) { V.hov = h ? { ...h, key } : null; redraw(); } showTip(h, e.offsetX, e.offsetY);
});
const endPtr = e => { ptrs.delete(e.pointerId); cv.classList.remove('drag'); if (ptrs.size < 2) pinch = null;
  if (drag && !drag.moved && e.type === 'pointerup') { const h = hit(e.offsetX, e.offsetY); if (h) { if (h.k != null) focusItem(h.it, h.i, false); else if (h.m != null) showTip(h, e.offsetX, e.offsetY); else focusItem(h.it, -1); } }
  drag = null; };
cv.addEventListener('pointerup', endPtr); cv.addEventListener('pointercancel', endPtr);
cv.addEventListener('pointerleave', () => { if (!drag) { $('#tip').hidden = true; if (V.hov) { V.hov = null; redraw(); } } });
cv.addEventListener('wheel', e => { e.preventDefault(); stopTour(); V.anim = null; const w = toW(e.offsetX, e.offsetY); V.z = Math.max(3, Math.min(17, V.z - e.deltaY * (e.deltaMode ? .05 : .0022))); const s = 2 ** V.z; V.cx = w[0] - (e.offsetX - V.W / 2) / s; V.cy = w[1] - (e.offsetY - V.H / 2) / s; redraw(); }, { passive: false });
cv.addEventListener('dblclick', e => { const w = toW(e.offsetX, e.offsetY); go(w[0], w[1], Math.min(17, V.z + 1.5)); });
$('#zin').onclick = () => go(V.cx, V.cy, Math.min(17, V.z + 1));
$('#zout').onclick = () => go(V.cx, V.cy, Math.max(3, V.z - 1));
$('#zfit').onclick = () => { S.focus = -1; S.sel = -1; renderPanel(); renderSSEE(); fitAll(); };
function fitAll(animate = true) {
  const pts = []; for (let k = 0; k < R.m; k++) { const i = R.cand[k]; if (P.has[i] && vis(k)) pts.push([P.WX[i], P.WY[i]]); }
  const a = merc(-0.03, -81.4), b = merc(-18.4, -68.6); fitBB(pts.length ? bbox(pts) : [a[0], a[1], b[0], b[1]], 40, animate);
}
function focusItem(it, i = -1, refit = true) {
  if (it == null || it < 0 || !R.items.has(it)) { if (i >= 0 && P.has[i]) { S.sel = i; go(P.WX[i], P.WY[i], Math.max(V.z, 11)); renderPanel(); } return; }
  const changed = S.focus !== it; S.focus = it; S.sel = i; renderPanel(); renderSSEE();
  const o = R.items.get(it); if (refit || changed) { if (o.g) fitBB(o.g.bb, 60); } redraw();
}

/* ---------- recorrido ---------- */
let tour = null;
function stopTour() { if (!tour) return; clearTimeout(tour.h); tour = null; $('#tour').classList.remove('on'); $('#tourbar').classList.remove('on'); }
function stepTour() { if (!tour) return; const o = tour.list[tour.k % tour.list.length]; focusItem(o.it, -1); $('#tourbar').textContent = `Recorrido ${tour.k % tour.list.length + 1} de ${tour.list.length} · ${o.item} · ${o.nc} casos`; tour.k++; tour.h = setTimeout(stepTour, 6000); }
$('#tour').onclick = () => { if (tour) { stopTour(); return; } const list = itemsArr().sort((a, b) => b.nc - a.nc).slice(0, 8); if (!list.length) return; tour = { list, k: 0 }; $('#tour').classList.add('on'); $('#tourbar').classList.add('on'); stepTour(); };

/* ---------- controles ---------- */
function fillFilters() {
  const c = P.c, deps = new Set(), fons = new Set(); P.D.dict.ub.forEach((u, j) => { const a = UBI[u]; if (a) { deps.add(a[0]); fons.add(a[4]); } });
  const opt = (sel, list, all, lab = x => x) => { const el = $(sel), cur = el.value; el.innerHTML = `<option value="">${all}</option>` + list.map(x => `<option value="${esc(x)}">${esc(lab(x))}</option>`).join(''); el.value = list.includes(cur) ? cur : ''; };
  opt('#fut', P.D.dict.ut.filter(x => x !== 'Sin dato'), 'Todas', tcase); opt('#fdep', [...deps].sort(), 'Todos', tcase);
  opt('#ffo', P.D.dict.fo, 'Todas'); const ord = ['Muy alto', 'Alto', 'Medio', 'Bajo', 'Muy bajo']; opt('#ffon', [...fons].sort((a, b) => (ord.indexOf(a) + 1 || 9) - (ord.indexOf(b) + 1 || 9)), 'Todos');
  for (const [k, s] of [['ut', '#fut'], ['dep', '#fdep'], ['fo', '#ffo'], ['fon', '#ffon']]) S.f[k] = $(s).value;
}
function syncCtl() {
  document.querySelectorAll('#yr button').forEach(b => b.classList.toggle('on', b.dataset.y === S.y));
  document.querySelectorAll('#nseg button').forEach(b => b.classList.toggle('on', +b.dataset.n === S.n));
  $('#mode').value = S.mode; $('#kb').value = S.kb; $('#kc').value = S.kc; $('#kbo').textContent = f1(S.kb) + ' km'; $('#kco').textContent = f1(S.kc) + ' km';
  $('#geo').value = S.geo; $('#base').value = S.base; for (const k of ['items', 'core', 'lines', 'bg', 'mer', 'bn']) $('#lyr' + k[0].toUpperCase() + k.slice(1)).checked = S.lyr[k];
}
function update(refit = false) {
  compute(); if (S.focus >= 0 && !R.items.has(S.focus)) { S.focus = -1; S.sel = -1; }
  renderHead(); renderCards(); renderCharts(); renderItems(); renderSSEE(); renderPanel(); syncCtl(); updateNote(); save(); redraw(); if (refit) fitAll();
}
let tmr; const later = (fn, ms = 120) => { clearTimeout(tmr); tmr = setTimeout(fn, ms); };
$('#yr').onclick = e => { const b = e.target.closest('button'); if (!b || b.dataset.y === S.y) return; stopTour(); S.y = b.dataset.y; P = prep(S.y); S.focus = -1; S.sel = -1; fillFilters(); update(true); };
$('#nseg').onclick = e => { const b = e.target.closest('button'); if (!b) return; S.n = +b.dataset.n; update(true); };
$('#mode').onchange = e => { S.mode = e.target.value; update(true); };
$('#kb').oninput = e => { S.kb = +e.target.value; if (S.kc < S.kb) S.kc = Math.ceil(S.kb); $('#kbo').textContent = f1(S.kb) + ' km'; later(() => update()); };
$('#kc').oninput = e => { S.kc = Math.max(+e.target.value, S.kb); $('#kco').textContent = f1(S.kc) + ' km'; later(() => update()); };
for (const [k, s] of [['ut', '#fut'], ['dep', '#fdep'], ['fo', '#ffo'], ['ds', '#fds'], ['fon', '#ffon']]) $(s).onchange = e => { S.f[k] = e.target.value; S.focus = -1; update(true); };
$('#reset').onclick = () => { Object.assign(S, { n: 1, mode: 'eq', kb: 2, kc: 5, tf: '', focus: -1, sel: -1, iq: '', sq: '' }); for (const k in S.f) S.f[k] = ''; ['#fut', '#fdep', '#ffo', '#fds', '#ffon'].forEach(s => $(s).value = ''); $('#iq').value = ''; $('#sq').value = ''; update(true); };
$('#geo').onchange = e => { S.geo = e.target.value; update(); };
$('#base').onchange = e => { S.base = e.target.value; tileOK = tileErr = 0; updateNote(); save(); redraw(); };
for (const k of ['items', 'core', 'lines', 'bg', 'mer', 'bn']) $('#lyr' + k[0].toUpperCase() + k.slice(1)).onchange = e => { S.lyr[k] = e.target.checked; save(); renderHead(); redraw(); };
$('#cards').onclick = e => { const b = e.target.closest('.card'); if (!b) return; S.tf = S.tf === b.dataset.t ? '' : b.dataset.t; renderCards(); renderItems(); renderSSEE(); renderPanel(); redraw(); };
$('#chN').onclick = e => { const b = e.target.closest('button'); if (!b || b.disabled) return; S.n = +b.dataset.n; update(true); };
$('#chUT').onclick = e => { const b = e.target.closest('.hb'); if (!b) return; S.f.ut = S.f.ut === b.dataset.ut ? '' : b.dataset.ut; $('#fut').value = S.f.ut; update(true); };
$('#chUT').onkeydown = e => { if (e.key === 'Enter') e.target.click(); };
$('#panel').onclick = e => { if (e.target.closest('#pback')) { S.focus = -1; S.sel = -1; renderPanel(); renderSSEE(); fitAll(); return; }
  const li = e.target.closest('li[data-it]'); if (li) { focusItem(+li.dataset.it, -1); return; }
  const si = e.target.closest('li[data-i]'); if (si) { const i = +si.dataset.i; S.sel = i; renderPanel(); if (P.has[i]) go(P.WX[i], P.WY[i], Math.max(V.z, 12.5)); } };
const sortBy = (st, k) => { st.d = st.k === k ? -st.d : (k === 'nc' || k === 'a' || k === 'red' || k === 'n' ? -1 : 1); st.k = k; };
$('#itab').onclick = e => { const th = e.target.closest('th'); if (th) { sortBy(S.isort, th.dataset.s); renderItems(); return; } const tr = e.target.closest('tr[data-it]'); if (tr) { focusItem(+tr.dataset.it, -1); $('#mapa').scrollIntoView({ behavior: reduced ? 'auto' : 'smooth' }); } };
$('#stab').onclick = e => { const th = e.target.closest('th'); if (th) { sortBy(S.ssort, th.dataset.s); renderSSEE(); return; } const tr = e.target.closest('tr[data-k]'); if (tr) { const i = R.cand[+tr.dataset.k]; $('#mapa').scrollIntoView({ behavior: reduced ? 'auto' : 'smooth' }); focusItem(P.c.it[i], i, false); if (P.has[i]) go(P.WX[i], P.WY[i], 12.5); } };
$('#iq').oninput = e => { S.iq = e.target.value; S.ilim = 25; later(renderItems, 150); };
$('#sq').oninput = e => { S.sq = e.target.value; S.slim = 50; later(renderSSEE, 150); };
$('#imore').onclick = () => { S.ilim += 50; renderItems(); };
$('#smore').onclick = () => { S.slim += 100; renderSSEE(); };
const fname = s => `${s}_${P.D.year}_${S.mode === 'eq' ? '' : 'hasta'}${S.n}usuario.csv`;
$('#icsv').onclick = () => download(fname('items'), itemCSV()); $('#icopy').onclick = () => copy(itemCSV());
$('#scsv').onclick = () => download(fname('ssee'), ssCSV()); $('#scopy').onclick = () => copy(ssCSV());
$('#present').onclick = () => { const on = document.body.classList.toggle('present'); $('#present').textContent = on ? '✕ Salir' : '▶ Presentar';
  if (on) { $('#mapa').scrollIntoView(); try { document.documentElement.requestFullscreen?.().catch(() => { }); } catch (e) { } } else { try { document.fullscreenElement && document.exitFullscreen(); } catch (e) { } } setTimeout(() => { resize(); }, 80); };
document.addEventListener('keydown', e => { if (e.key === 'Escape') { stopTour(); if (document.body.classList.contains('present')) $('#present').click(); } });
document.addEventListener('fullscreenchange', () => { if (!document.fullscreenElement && document.body.classList.contains('present')) $('#present').click(); });
new ResizeObserver(() => document.documentElement.style.setProperty('--toph', $('#top').offsetHeight + 'px')).observe($('#top'));

/* ---------- inicio ---------- */
readCols(); fillFilters(); syncCtl();
requestAnimationFrame(() => { resize(); update(); fitAll(false); $('#loading').classList.add('off'); setTimeout(() => $('#loading').remove(), 500); });
}
