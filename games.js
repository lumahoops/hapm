// HAPM site: the player page's Games tab. Loaded by player.html; uses its globals (ROOT, PID, S, $, sg, LO, MID, HI).
// Level 1: chart over any time frame (one season to a whole career): soft dots + a smooth running line
//          (HAPM time decay as of each game, or Par ± of the last 10 games), season dividers, hover card, drag = dates.
// Level 2: game log (box score + plus-minus + Par ±): time frame, months, search, filters, sortable, columns, CSV,
//          and one pooled Par ± (with SE) for whatever is selected.
// Level 3: one game opened: his stints (timeline + table), from data/stints/<season>/<gid>.json.
// Formulas (open source, same as hapm-v2/js/par.js):
//   Par ± = sum Ro / sum Wo + sum Rd / sum Wd
//   SE^2  = sum over seasons s [kappa_s Wo_s / Wo^2 + kappa_d_s Wd_s / Wd^2 + c_s sh_s^2], sh_s = season s's share of the possessions
//   HAPM  = center + B (Par - center), B = tau2 / (tau2 + SE^2); center read on the season's curve at log(poss x pace)
//   Time decay: this season's Par to date pooled with each earlier season's Par, weights td15^(seasons back) / SE^2, one shrink.
(() => {
const G = { L: null, C: null, st: {}, stP: null, open: null, prep: {} };
const NS = "http://www.w3.org/2000/svg";
const n0 = (x) => x == null ? "" : Math.round(x).toLocaleString();
const f1 = (x, d = 1) => x == null || !isFinite(x) ? "" : (x > 0 ? "+" : x < 0 ? "\u2212" : "") + Math.abs(x).toFixed(d);
const pmS = (x) => x == null ? "" : "\u00b1" + x.toFixed(1);
const esc = (s) => String(s ?? "").replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]);
const MON = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
const MORDER = [10, 11, 12, 1, 2, 3, 4, 5, 6, 7, 8, 9];            // NBA season order
const sdate = (d) => `${MON[+d.slice(5, 7) - 1]} ${+d.slice(8, 10)}`;
const ldate = (d) => `${sdate(d)}, ${d.slice(0, 4)}`;
const parBg = (x, full = 30) => { if (x == null || !isFinite(x)) return ""; const t = Math.min(1, Math.abs(x) / full), e = x >= 0 ? HI : LO; return `rgb(${MID.map((m, i) => Math.round(m + (e[i] - m) * t)).join(",")})`; };
const parFill = (x, full = 30, a0 = 0.25) => { const t = Math.min(1, Math.abs(x) / full); return x >= 0 ? `rgba(75,138,82,${a0 + (1 - a0) * t})` : `rgba(196,80,80,${a0 + (1 - a0) * t})`; };
const last = (n) => { const w = String(n).split(" "); return w.length > 2 && /^(Jr\.?|Sr\.?|II|III|IV)$/.test(w[w.length - 1]) ? w.slice(-2).join(" ") : w[w.length - 1]; };

// ---------------------------------------------------------------- Par ± over blocks (one block per season)
const Z = () => [0, 0, 0, 0, 0, 0];
function pooled(bySeason) {          // Map season -> sums [Wo, Ro, Ao, Wd, Rd, Ad]
  const t = Z(); for (const a of bySeason.values()) a.forEach((x, i) => t[i] += x);
  const [Wo, Ro, Ao, Wd, Rd, Ad] = t; if (!(Wo > 0) || !(Wd > 0)) return null;
  let v = 0;
  for (const [s, a] of bySeason) { const k = G.L.seasons[s].k; if (!(a[0] + a[3] > 0)) continue; const sh = (a[0] + a[3]) / (Wo + Wd);
    v += k[0] * a[0] / (Wo * Wo) + k[1] * a[3] / (Wd * Wd) + k[2] * sh * sh; }
  const par = Ro / Wo + Rd / Wd, act = Ao / Wo + Ad / Wd;
  return { poss: (Wo + Wd) / 2, o: Ro / Wo, d: Rd / Wd, par, act, exp: act - par, se: Math.sqrt(v) };
}
const one = (s, a) => pooled(new Map([[s, a]]));
function poolRows(rows) { const m = new Map(); for (const r of rows) if (r.sums) { const a = m.get(r.s) || Z(); r.sums.forEach((x, i) => a[i] += x); m.set(r.s, a); } return pooled(m); }

// ---------------------------------------------------------------- HAPM (time decay) as of a game
function interp(x, xs, ys) { if (x <= xs[0]) return ys[0]; const n = xs.length; if (x >= xs[n - 1]) return ys[n - 1];
  let lo = 0, hi = n - 1; while (hi - lo > 1) { const m = (lo + hi) >> 1; if (xs[m] <= x) lo = m; else hi = m; } return ys[lo] + ((ys[hi] - ys[lo]) * (x - xs[lo])) / (xs[hi] - xs[lo]); }
function hapmTD(s, cur, date) {      // cur = his Par to date this season {o, d, se, poss}
  const c = G.C.seasons[s]; if (!c || !cur) return null;
  const th = c.through; let lo = 0, hi = th.length; while (lo < hi) { const m = (lo + hi) >> 1; if (th[m][0] <= date) lo = m + 1; else hi = m; }
  const thru = lo ? th[lo - 1][1] : 1, pace = c.read_pace * c.n_games / Math.max(thru, 1);
  const lw = Math.log(Math.max(cur.poss * pace, 1)); const mu = interp(lw, c.lx, c.net);
  const iY = G.C.order.indexOf(s); let sw = 0, sv = 0, s2 = 0;
  const blocks = [{ v: cur.o + cur.d, se: cur.se, back: 0 }];
  for (const [s2l, T] of Object.entries(G.tot)) { const j = G.C.order.indexOf(s2l); if (j >= 0 && j < iY && T) blocks.push({ v: T.par, se: T.se, back: iY - j }); }
  const B1 = c.tau2 / (c.tau2 + cur.se * cur.se);
  if (B1 >= 1 - 1e-9 || blocks.length === 1) return mu + B1 * (cur.o + cur.d - mu);
  for (const b of blocks) { const w = G.C.td15 ** b.back / (b.se * b.se); sw += w; sv += w * b.v; s2 += w * w * b.se * b.se; }
  const B = c.tau2 / (c.tau2 + s2 / (sw * sw)); return mu + B * (sv / sw - mu);
}

// ---------------------------------------------------------------- columns (key, header, value, cell, default on, tip)
const ts = (r) => (r.fga + 0.44 * r.fta) > 0 ? r.pts / (2 * (r.fga + 0.44 * r.fta)) : null;
const COLS = [
  ["date", "Date", (r) => r.date, (r) => `<td class="l">${sdate(r.date)} <span class="yr">${r.date.slice(0, 4)}</span></td>`, 1, "Game date"],
  ["opp", "Opp", (r) => r.opp, (r) => `<td class="l">${r.home ? "vs" : "@"} ${esc(r.opp)}</td>`, 1, "Opponent; vs = home, @ = away"],
  ["res", "Result", (r) => r.tm_pts == null ? null : r.tm_pts - r.opp_pts, (r) => `<td class="l ${r.wl === "W" ? "w" : r.wl === "L" ? "lo" : ""}">${r.wl ?? ""} ${r.tm_pts ?? ""}${r.tm_pts != null ? "\u2013" : ""}${r.opp_pts ?? ""}</td>`, 1, "Win or loss and the final score, his team first"],
  ["team", "Team", (r) => r.team, (r) => `<td class="l">${esc(r.team)}</td>`, 0, "His team"],
  ["par", "Par \u00b1", (r) => r.x && r.x.par, (r) => `<td class="v main sep" style="background:${r.x ? parBg(r.x.par) : ""}"><span class="x">${r.x ? f1(r.x.par) : ""}</span><span class="p">${r.x ? pmS(r.x.se) : ""}</span></td>`, 1, "Actual minus expected, per 100 possessions; under it, one standard error. One game is mostly noise."],
  ["cum", "To date", (r) => r.c && r.c.par, (r) => `<td class="v main"><span class="x">${r.c ? f1(r.c.par, 2) : ""}</span><span class="p">${r.c ? pmS(r.c.se) : ""}</span></td>`, 1, "Season to date: Par \u00b1 over every game of the season up to and including this one"],
  ["td", "HAPM", (r) => r.td, (r) => `<td>${f1(r.td, 2)}</td>`, 1, "HAPM time decay as of this game: his Par to date shrunk with his earlier seasons (the line on the chart)"],
  ["poss", "Poss", (r) => r.x && r.x.poss, (r) => `<td class="ps">${r.x ? n0(r.x.poss) : ""}</td>`, 1, "Possessions on the floor (offense and defense averaged)"],
  ["min", "MIN", (r) => r.min, (r) => `<td class="sep">${r.min ?? ""}</td>`, 1, "Minutes"],
  ["pts", "PTS", (r) => r.pts, null, 1, "Points"],
  ["reb", "REB", (r) => r.reb, null, 1, "Rebounds"],
  ["oreb", "OREB", (r) => r.oreb, null, 0, "Offensive rebounds"],
  ["dreb", "DREB", (r) => r.dreb, null, 0, "Defensive rebounds"],
  ["ast", "AST", (r) => r.ast, null, 1, "Assists"],
  ["stl", "STL", (r) => r.stl, null, 1, "Steals"],
  ["blk", "BLK", (r) => r.blk, null, 1, "Blocks"],
  ["tov", "TOV", (r) => r.tov, null, 1, "Turnovers"],
  ["pf", "PF", (r) => r.pf, null, 0, "Personal fouls"],
  ["fg", "FG", (r) => r.fga ? r.fgm / r.fga : null, (r) => `<td>${r.fgm ?? ""}-${r.fga ?? ""}</td>`, 1, "Field goals made-attempted"],
  ["fg3", "3P", (r) => r.fg3a ? r.fg3m / r.fg3a : null, (r) => `<td>${r.fg3m ?? ""}-${r.fg3a ?? ""}</td>`, 1, "Threes made-attempted"],
  ["ft", "FT", (r) => r.fta ? r.ftm / r.fta : null, (r) => `<td>${r.ftm ?? ""}-${r.fta ?? ""}</td>`, 1, "Free throws made-attempted"],
  ["pac", "PAC", (r) => r.pts == null || G.L.seasons[r.s].price == null ? null : r.pts - G.L.seasons[r.s].price * (r.fga + 0.44 * r.fta), (r) => { const v = BYK.pac[2](r); return `<td>${v == null ? "" : f1(v, 1)}</td>`; }, 1, "Points above cost: his points minus what his shots cost, priced at what the possessions would return if a teammate took them (open method: github.com/aayoawoyemi/pac)"],
  ["ts", "TS%", ts, (r) => { const x = ts(r); return `<td>${x == null ? "" : (100 * x).toFixed(0)}</td>`; }, 1, "True shooting: points / (2 x (FGA + 0.44 FTA))"],
  ["pm", "+/\u2212", (r) => r.pm, (r) => `<td>${r.pm == null ? "" : f1(r.pm, 0)}</td>`, 1, "Plus-minus: his team's points minus the opponents' while he was on the floor (raw)"],
  ["act", "Actual", (r) => r.x && r.x.act, (r) => `<td>${r.x ? f1(r.x.act) : ""}</td>`, 0, "On-floor margin per 100 possessions, relative to a league-average team"],
  ["exp", "Expected", (r) => r.x && r.x.exp, (r) => `<td>${r.x ? f1(r.x.exp) : ""}</td>`, 0, "The margin per 100 the other nine on the floor would produce with a league-average player in his place"],
  ["off", "Off", (r) => r.x && r.x.o, (r) => `<td>${r.x ? f1(r.x.o) : ""}</td>`, 0, "Par \u00b1 on offense"],
  ["def", "Def", (r) => r.x && r.x.d, (r) => `<td>${r.x ? f1(r.x.d) : ""}</td>`, 0, "Par \u00b1 on defense"],
];
const CK = COLS.map((c) => c[0]);
const BYK = Object.fromEntries(COLS.map((c) => [c[0], c]));
function cols() {
  let on; try { on = JSON.parse(localStorage.getItem("hapm_gcols3") || "null"); } catch (e) { on = null; }
  return Array.isArray(on) ? CK.filter((k) => on.includes(k)) : COLS.filter((c) => c[4]).map((c) => c[0]);
}
const saveCols = (on) => { try { localStorage.setItem("hapm_gcols3", JSON.stringify(on)); } catch (e) {} };

// ---------------------------------------------------------------- search: words + conditions (pts>=30, par<0)
const ALIAS = { "3p": "fg3", "3pa": "fg3a", "3pm": "fg3m", "+/-": "pm", "plusminus": "pm", "margin": "res", "hapm": "td" };
function compileQ(q) {
  const tests = [];
  for (const raw of (q || "").toLowerCase().split(/[\s,]+/).filter(Boolean)) {
    const m = raw.match(/^([a-z0-9+/\-]+?)(>=|<=|=|>|<)(-?[\d.]+)$/);
    if (m) {
      const key = ALIAS[m[1]] || m[1], v = +m[3];
      const get = (r) => key in BYK ? BYK[key][2](r) : r[key];
      const sc = ["ts", "fg", "fg3", "ft"].includes(key) ? 0.01 : 1;
      const op = { ">=": (a) => a >= v * sc, "<=": (a) => a <= v * sc, "=": (a) => a === v * sc, ">": (a) => a > v * sc, "<": (a) => a < v * sc }[m[2]];
      tests.push((r) => { const a = get(r); return a != null && op(a); });
    } else if (raw === "@" || raw === "away") tests.push((r) => !r.home);
    else if (raw === "vs" || raw === "home") tests.push((r) => r.home);
    else if (["w", "win", "wins"].includes(raw)) tests.push((r) => r.wl === "W");
    else if (["l", "loss", "losses"].includes(raw)) tests.push((r) => r.wl === "L");
    else tests.push((r) => r.hay.includes(raw));
  }
  return (r) => tests.every((t) => t(r));
}

// ---------------------------------------------------------------- state <-> hash
const KEYS = ["s0", "s1", "q", "ha", "wl", "opp", "from", "to", "mo", "sort", "dir", "g", "view"];
function readHash() {
  const H = Object.fromEntries(new URLSearchParams(location.hash.slice(1)));
  G.st = { s0: H.s0 || H.s || "", s1: H.s1 || H.s || "", q: H.q || "", ha: H.ha || "", wl: H.wl || "", opp: H.opp || "", from: H.from || "", to: H.to || "",
    mo: H.mo || "", sort: H.sort || "date", dir: H.dir || "d", g: H.g || "", view: ["par", "total"].includes(H.view) ? H.view : "hapm" };
}
function writeHash() {
  const H = Object.fromEntries(new URLSearchParams(location.hash.slice(1))); delete H.s;
  for (const k of KEYS) delete H[k];
  const st = G.st;
  for (const k of KEYS) { const v = st[k]; if (!v) continue; if (k === "sort" && v === "date" && st.dir === "d") continue; if (k === "dir" && st.sort === "date" && v === "d") continue; if (k === "view" && v === "hapm") continue; H[k] = v; }
  history.replaceState(null, "", "#" + new URLSearchParams(H).toString());
}

// ---------------------------------------------------------------- data
async function load() {
  if (!G.L) {                // finished seasons (data/games/<pid>.json) + the season in progress (data/games/live/<pid>.json, nightly)
    const get = (u) => fetch(u).then((x) => (x.ok ? x.json() : null)).catch(() => null);
    const [H, L, C] = await Promise.all([get(`${ROOT}data/games/${PID}.json`), get(`${ROOT}data/games/live/${PID}.json`), get(`${ROOT}data/games/_ctx.json`)]);
    if (!H && !L) throw 0;
    G.L = H || { pid: PID, cols: L.cols, seasons: {} }; if (L) Object.assign(G.L.seasons, L.seasons); G.C = C;
  }
  if (!G.tot) { G.SEA = Object.keys(G.L.seasons); G.tot = {}; for (const s of G.SEA) { prepSeason(s); } for (const s of G.SEA) addTD(s); }
}
function prepSeason(s) {
  if (G.prep[s]) return G.prep[s];
  const L = G.L, { g } = L.seasons[s], ix = Object.fromEntries(L.cols.map((c, i) => [c, i]));
  const rows = g.filter((a) => a[ix.date]).map((a) => { const r = { s }; for (const c of L.cols) r[c] = a[ix[c]]; r.sums = r.Wo == null ? null : [r.Wo, r.Ro, r.Ao, r.Wd, r.Rd, r.Ad]; return r; });
  const cum = Z();
  for (const r of rows) {
    r.x = r.sums ? one(s, r.sums) : null;
    if (r.sums) r.sums.forEach((x, i) => cum[i] += x);
    r.c = one(s, cum.slice());
    r.mo = +r.date.slice(5, 7);
    r.hay = [r.date, r.opp, r.team, r.home ? "vs" : "@", MON[r.mo - 1].toLowerCase(), r.wl || "", s].join(" ").toLowerCase();
  }
  G.tot[s] = rows.length ? rows[rows.length - 1].c : null;
  return (G.prep[s] = rows);
}
function addTD(s) { for (const r of G.prep[s]) r.td = r.c ? hapmTD(s, r.c, r.date) : null; }
function spanSeasons() { const a = G.SEA.indexOf(G.st.s0), b = G.SEA.indexOf(G.st.s1); return G.SEA.slice(Math.min(a, b), Math.max(a, b) + 1); }
function spanRows() { return spanSeasons().flatMap((s) => G.prep[s]); }
function filtered(rows) {
  const st = G.st, q = compileQ(st.q), mo = st.mo ? new Set(st.mo.split(".").map(Number)) : null;
  return rows.filter((r) => (!st.ha || (st.ha === "h") === !!r.home) && (!st.wl || r.wl === st.wl) && (!st.opp || r.opp === st.opp)
    && (!st.from || r.date >= st.from) && (!st.to || r.date <= st.to) && (!mo || mo.has(r.mo)) && q(r));
}

// ---------------------------------------------------------------- shell
function shell() {
  if ($("gtools")) return;
  $("pGames").innerHTML = `
  <div class="gspan">
    <span class="seg" id="gquick"><button data-q="1">This season</button><button data-q="2">Last 2</button><button data-q="3">Last 3</button><button data-q="all">Career</button></span>
    <label>Seasons <select id="gs0"></select> to <select id="gs1"></select></label>
    <div id="gsum" class="gsum"></div>
  </div>
  <div class="gchartbox"><div class="gview"><span class="seg" id="gview"><button data-v="hapm" title="HAPM (time decay) after each game: how good he is">HAPM</button><button data-v="par" title="Par \u00b1 to date in each season, per 100 possessions, with one standard error: what he has done this season on its own">Par \u00b1</button><button data-v="total" title="Par added up game by game, in points: how much he has added">Par total</button></span><span class="gleg" id="gleg"></span></div>
    <div id="gchart" class="gchart"></div><div id="gtip" class="gtip" hidden></div></div>
  <div class="gmonths" id="gmonths"></div>
  <div class="gtools" id="gtools">
    <input id="gq" type="search" placeholder="Search: DEN, @, W, pts>=30, par>10, min>30" title="Words match opponent, team, month, date, season, W / L, vs / @. Conditions: a column key with > < >= <= =, e.g. pts>=30, ast>=10, ts>=60, par<0, pm>10, poss>60, hapm>5.">
    <span class="seg" id="gha"><button data-v="">All</button><button data-v="h">Home</button><button data-v="a">Away</button></span>
    <span class="seg" id="gwl"><button data-v="">All</button><button data-v="W">Wins</button><button data-v="L">Losses</button></span>
    <label>Opp <select id="gopp"></select></label>
    <label>From <input type="date" id="gfrom"></label><label>to <input type="date" id="gto"></label>
    <details class="gcols"><summary class="btn">Columns</summary><div id="gcolbox"></div></details>
    <button class="btn" id="gcsv">CSV</button><button class="btn" id="greset">Reset</button>
  </div>
  <div id="gsel" class="gsel"></div>
  <div id="games" class="gwrap"></div>
  <details class="note gq"><summary>? What this page shows</summary>
    <ul>
      <li>Time frame: one season, the last two or three, his career, or any seasons in between. Month buttons keep only those months, in every season shown.</li>
      <li>HAPM / Par \u00b1 / Par total: three views of the same games. HAPM is the rating after each game (time decay). Par \u00b1 is the raw season-to-date value per 100 possessions with a band of one standard error; it restarts each season. Par total adds each game's Par up in points (margin minus expected), so it climbs while he beats par, stays flat at average, and falls below it.</li>
      <li>Chart (HAPM view): the line is his HAPM (time decay) as of each game: his Par \u00b1 so far that season, combined with his earlier seasons and shrunk toward the playing-time average. The dots are his Par \u00b1 to date in that season; they swing early in a season and settle as possessions add up.</li>
      <li>The chart shows the games that pass the filters below (months, home / away, opponent, search, dates). With a filter on, the dots are his Par \u00b1 to date over those games only. Hover to see a game, click to open it, drag across it to zoom to those dates.</li>
      <li>Box score: the official box score. +/\u2212 is the raw plus-minus while he was on the floor.</li>
      <li>PAC (points above cost): his points minus what his shots cost. Each true-shot attempt is priced at what the possession would return if a teammate took it instead, which is below league average for players who carry a big share of the offense. The games add up to his season PAC. Open method: github.com/aayoawoyemi/pac.</li>
      <li>Par \u00b1: the on-floor margin per 100 possessions minus the margin the other nine players would produce with a league-average player in his place. One game is mostly noise (one standard error is about \u00b120).</li>
      <li>Selected: the strip above the table pools every game that passes the filters into one Par \u00b1 with its standard error: home games, March, games against Denver, games he scored 30+.</li>
      <li>Open a game: click a row. The opened game lists his stints, the stretches with the same ten players on the floor, with teammates, opponents, possessions and the actual and expected margin in points.</li>
      <li>Search: words match opponent, team, month, date, season, W / L and vs / @. Conditions use a column key with &gt; &lt; &gt;= &lt;= =, e.g. <code>pts&gt;=30</code>, <code>ast&gt;=10</code>, <code>ts&gt;=60</code>, <code>par&lt;0</code>, <code>pm&gt;10</code>, <code>hapm&gt;5</code>.</li>
    </ul>
    <p>In past seasons the expected margin uses the other nine players' full-season ratings, so a value inside a past season is not exactly what was known on that date.</p>
  </details>`;
  const reset = () => { G.st.from = G.st.to = G.st.g = ""; };
  $("gs0").onchange = () => { G.st.s0 = $("gs0").value; if (G.SEA.indexOf(G.st.s1) < G.SEA.indexOf(G.st.s0)) G.st.s1 = G.st.s0; reset(); draw(); };
  $("gs1").onchange = () => { G.st.s1 = $("gs1").value; if (G.SEA.indexOf(G.st.s0) > G.SEA.indexOf(G.st.s1)) G.st.s0 = G.st.s1; reset(); draw(); };
  [...$("gquick").children].forEach((b) => b.onclick = () => { const n = G.SEA.length, q = b.dataset.q; G.st.s1 = G.SEA[n - 1]; G.st.s0 = q === "all" ? G.SEA[0] : G.SEA[Math.max(0, n - +q)]; reset(); draw(); });
  let tq; $("gq").oninput = () => { clearTimeout(tq); tq = setTimeout(() => { G.st.q = $("gq").value.trim(); draw(true); }, 180); };
  for (const [id, key] of [["gha", "ha"], ["gwl", "wl"]]) [...$(id).children].forEach((b) => b.onclick = () => { G.st[key] = b.dataset.v; draw(true); });
  $("gopp").onchange = () => { G.st.opp = $("gopp").value; draw(true); };
  $("gfrom").onchange = () => { G.st.from = $("gfrom").value; draw(true); };
  $("gto").onchange = () => { G.st.to = $("gto").value; draw(true); };
  $("greset").onclick = () => { Object.assign(G.st, { q: "", ha: "", wl: "", opp: "", from: "", to: "", mo: "", sort: "date", dir: "d", g: "" }); draw(); };
  $("gcsv").onclick = csv;
  [...$("gview").children].forEach((b) => b.onclick = () => { G.st.view = b.dataset.v; chart(); writeHash(); });
}
function colBox() {
  const on = cols();
  $("gcolbox").innerHTML = COLS.map((c) => `<label title="${esc(c[5])}"><input type="checkbox" data-k="${c[0]}" ${on.includes(c[0]) ? "checked" : ""}> ${c[1]}</label>`).join("") + `<button class="btn" id="gcdef">Default</button>`;
  $("gcolbox").querySelectorAll("input").forEach((x) => x.onchange = () => { saveCols([...$("gcolbox").querySelectorAll("input:checked")].map((y) => y.dataset.k)); table(); });
  $("gcdef").onclick = () => { try { localStorage.removeItem("hapm_gcols3"); } catch (e) {} colBox(); table(); };
}

// ---------------------------------------------------------------- draw
let ROWS = [];
function draw() {
  const st = G.st, n = G.SEA.length;
  if (!G.SEA.includes(st.s1)) st.s1 = G.SEA[n - 1];
  if (!G.SEA.includes(st.s0)) st.s0 = st.s1;
  for (const id of ["gs0", "gs1"]) { const e = $(id); if (!e.options.length) for (const s of G.SEA) e.add(new Option(s, s)); }
  $("gs0").value = st.s0; $("gs1").value = st.s1; S.gs = st.s1;
  const span = spanSeasons(), quick = span.length === n && n > 3 ? "all" : span[span.length - 1] === G.SEA[n - 1] ? String(span.length) : "";
  [...$("gquick").children].forEach((b) => b.classList.toggle("on", b.dataset.q === quick || (b.dataset.q === "all" && span.length === n && n <= 3 && quick !== String(span.length))));
  ROWS = spanRows();
  const T = poolRows(ROWS), rec = ROWS.reduce((a, r) => (r.wl === "W" ? a[0]++ : r.wl === "L" ? a[1]++ : 0, a), [0, 0]), lastTD = [...ROWS].reverse().find((r) => r.td != null);
  const frame = quick === "all" ? "Career" : span.length > 1 ? `${span[0]} to ${span[span.length - 1]}` : span[0];
  $("gsum").innerHTML = (T ? `Par \u00b1 <b>${f1(T.par, 2)}</b> <span class="note">${pmS(T.se)}</span>` : "") +
    (lastTD ? ` \u00b7 HAPM (time decay) <b>${f1(lastTD.td, 2)}</b> <span class="note">after ${ldate(lastTD.date)}</span>` : "") +
    ` \u00b7 <b>${frame}</b> \u00b7 ${ROWS.length} games (${rec[0]}\u2013${rec[1]}) \u00b7 ${n0(T && T.poss)} poss`;
  // months present in the span
  const mos = MORDER.filter((m) => ROWS.some((r) => r.mo === m)), on = st.mo ? st.mo.split(".").map(Number) : [];
  $("gmonths").innerHTML = `<label>Months</label> <span class="seg">` + `<button data-m="" class="${on.length ? "" : "on"}">All</button>` +
    mos.map((m) => `<button data-m="${m}" class="${on.includes(m) ? "on" : ""}">${MON[m - 1]}</button>`).join("") + `</span>`;
  $("gmonths").querySelectorAll("button").forEach((b) => b.onclick = (e) => { const m = +b.dataset.m; let s = new Set(on);
    if (!m) s = new Set(); else if (e.shiftKey || e.ctrlKey || e.metaKey || true) { s.has(m) ? s.delete(m) : s.add(m); }
    st.mo = [...s].sort((a, b) => MORDER.indexOf(a) - MORDER.indexOf(b)).join("."); draw(true); });
  const opps = [...new Set(ROWS.map((r) => r.opp))].sort();
  $("gopp").innerHTML = `<option value="">All</option>` + opps.map((o) => `<option ${o === st.opp ? "selected" : ""}>${esc(o)}</option>`).join("");
  $("gq").value = st.q; $("gfrom").value = st.from; $("gto").value = st.to;
  const d0 = ROWS[0] && ROWS[0].date, d1 = ROWS.length && ROWS[ROWS.length - 1].date; $("gfrom").min = $("gto").min = d0 || ""; $("gfrom").max = $("gto").max = d1 || "";
  for (const [id, key] of [["gha", "ha"], ["gwl", "wl"]]) [...$(id).children].forEach((b) => b.classList.toggle("on", b.dataset.v === st[key]));
  if (!$("gcolbox").children.length) colBox();
  chart(); table(); writeHash();
}

function selection(F) {
  const X = poolRows(F), n = F.length, rec = F.reduce((a, r) => (r.wl === "W" ? a[0]++ : r.wl === "L" ? a[1]++ : 0, a), [0, 0]);
  for (const r of F) r._pac = BYK.pac[2](r);
  const avg = (k) => { const v = F.filter((r) => r[k] != null); return v.length ? v.reduce((s, r) => s + r[k], 0) / v.length : null; };
  const sum = (k) => F.reduce((s, r) => s + (r[k] || 0), 0), tsa = sum("fga") + 0.44 * sum("fta");
  const st = G.st, filt = st.q || st.ha || st.wl || st.opp || st.from || st.to || st.mo;
  const fx = (x) => x == null ? "" : x.toFixed(1);
  const tags = [];
  if (st.mo) tags.push(["mo", st.mo.split(".").map((m) => MON[+m - 1]).join(", ")]);
  if (st.ha) tags.push(["ha", st.ha === "h" ? "Home" : "Away"]);
  if (st.wl) tags.push(["wl", st.wl === "W" ? "Wins" : "Losses"]);
  if (st.opp) tags.push(["opp", "vs " + st.opp]);
  if (st.from || st.to) tags.push(["dates", `${st.from ? sdate(st.from) + " " + st.from.slice(0, 4) : "start"} to ${st.to ? sdate(st.to) + " " + st.to.slice(0, 4) : "end"}`]);
  if (st.q) tags.push(["q", `"${st.q}"`]);
  $("gsel").innerHTML = (!n ? `<span class="note">No games match.</span>` :
    `<span class="lab">${n} game${n === 1 ? "" : "s"} <span class="note">${rec[0]}\u2013${rec[1]}</span></span>` +
    (X ? `<span class="grp"><i>Par \u00b1</i> <b>${f1(X.par, 2)}</b> <span class="note">${pmS(X.se)}</span> <i>Off</i> ${f1(X.o, 2)} <i>Def</i> ${f1(X.d, 2)} <i>Poss</i> ${n0(X.poss)}</span>` : "") +
    `<span class="grp"><i>Per game</i> ${fx(avg("pts"))} pts \u00b7 ${fx(avg("reb"))} reb \u00b7 ${fx(avg("ast"))} ast \u00b7 ${fx(avg("min"))} min \u00b7 PAC ${f1(avg("_pac"), 1)} \u00b7 TS ${tsa ? (100 * sum("pts") / (2 * tsa)).toFixed(1) : ""}% \u00b7 +/\u2212 ${f1(avg("pm"), 1)}</span>`) +
    (tags.length ? `<span class="tags">${tags.map(([k, l]) => `<button class="tag" data-k="${k}" title="Remove this filter">${esc(l)} \u00d7</button>`).join("")}</span>` : "");
  $("gsel").querySelectorAll(".tag").forEach((x) => x.onclick = () => { const k = x.dataset.k; if (k === "dates") { st.from = st.to = ""; } else st[k] = ""; draw(); });
}

function table() {
  const F = filtered(ROWS), on = cols(), st = G.st, c = BYK[st.sort] || BYK.date;
  selection(F);
  const R = F.slice().sort((a, b) => { const x = c[2](a), y = c[2](b); if (x == null) return 1; if (y == null) return -1; return (x < y ? -1 : x > y ? 1 : 0) * (st.dir === "a" ? 1 : -1); });
  const th = (k) => `<th class="${["date", "opp", "res", "team"].includes(k) ? "l" : ""}${k === "par" || k === "min" ? " sep" : ""}${st.sort === k ? " srt" : ""}" data-k="${k}" title="${esc(BYK[k][5])}">${BYK[k][1]}${st.sort === k ? (st.dir === "a" ? " \u25b4" : " \u25be") : ""}</th>`;
  const cell = (k, r) => BYK[k][3] ? BYK[k][3](r) : `<td>${r[k] ?? ""}</td>`;
  const LIM = 400, more = R.length > LIM && !G.showAll;
  let prevS = null;
  $("games").innerHTML = `<table class="gl"><thead><tr>${on.map(th).join("")}</tr></thead><tbody>` +
    (more ? R.slice(0, LIM) : R).map((r) => { const div = st.sort === "date" && r.s !== prevS; prevS = r.s;
      return (div ? avgRow(r.s, F.filter((x) => x.s === r.s), on) : "") + `<tr data-g="${r.gid}" class="${r.x && r.x.poss < 15 ? "n0" : ""}${String(r.gid) === st.g ? " open" : ""}">${on.map((k) => cell(k, r)).join("")}</tr>`; }).join("") + "</tbody></table>" +
    (more ? `<button class="btn gmore" id="gmore">Show all ${R.length} games</button>` : "");
  if (more) $("gmore").onclick = () => { G.showAll = true; table(); };
  $("games").querySelectorAll("th").forEach((h) => h.onclick = () => { const k = h.dataset.k; if (st.sort === k) st.dir = st.dir === "a" ? "d" : "a"; else { st.sort = k; st.dir = ["opp", "team"].includes(k) ? "a" : "d"; } table(); writeHash(); });
  $("games").querySelectorAll("tbody tr[data-g]").forEach((tr) => tr.onclick = (e) => { if (e.target.closest("a")) return; const g = tr.dataset.g; st.g = st.g === g ? "" : g; table(); writeHash(); });
  if (st.g) { const tr = document.querySelector(`#games tr[data-g="${st.g}"]`); if (tr) openGame(+st.g, tr); }
  chartMark(F);
}

// one row per season section: totals / per-game averages of the games shown (Par ± pooled over them)
function avgRow(s, F, on) {
  const n = F.length, X = poolRows(F), avg = (k) => { const v = F.filter((r) => r[k] != null); return v.length ? v.reduce((a, r) => a + r[k], 0) / v.length : null; };
  const sum = (k) => F.reduce((a, r) => a + (r[k] || 0), 0), tsa = sum("fga") + 0.44 * sum("fta");
  const rec = F.reduce((a, r) => (r.wl === "W" ? a[0]++ : r.wl === "L" ? a[1]++ : 0, a), [0, 0]), lastTD = [...F].reverse().find((r) => r.td != null);
  const pac = F.map((r) => BYK.pac[2](r)).filter((v) => v != null), fx = (x, d = 1) => x == null ? "" : x.toFixed(d), ma = (a, b) => `${fx(avg(a))}-${fx(avg(b))}`;
  const C = {
    date: `<td class="l"><b>${s}</b></td>`, opp: `<td class="l note">${n} games</td>`, res: `<td class="l">${rec[0]}\u2013${rec[1]}</td>`, team: `<td class="l">${esc([...new Set(F.map((r) => r.team))].join("/"))}</td>`,
    par: `<td class="v main sep"><span class="x">${X ? f1(X.par, 2) : ""}</span><span class="p">${X ? pmS(X.se) : ""}</span></td>`, cum: `<td></td>`,
    td: `<td>${lastTD ? f1(lastTD.td, 2) : ""}</td>`, poss: `<td class="ps">${X ? n0(X.poss) : ""}</td>`, min: `<td class="sep">${fx(avg("min"))}</td>`,
    fg: `<td>${ma("fgm", "fga")}</td>`, fg3: `<td>${ma("fg3m", "fg3a")}</td>`, ft: `<td>${ma("ftm", "fta")}</td>`,
    pac: `<td>${pac.length ? f1(pac.reduce((a, b) => a + b, 0) / pac.length, 1) : ""}</td>`, ts: `<td>${tsa ? (100 * sum("pts") / (2 * tsa)).toFixed(0) : ""}</td>`,
    pm: `<td>${f1(avg("pm"), 1)}</td>`, act: `<td>${X ? f1(X.act) : ""}</td>`, exp: `<td>${X ? f1(X.exp) : ""}</td>`, off: `<td>${X ? f1(X.o) : ""}</td>`, def: `<td>${X ? f1(X.d) : ""}</td>` };
  return `<tr class="gsrow" title="${s}: per-game averages of the games shown; Par \u00b1 pooled over them; HAPM after the last of them">` + on.map((k) => C[k] || `<td>${fx(avg(k))}</td>`).join("") + "</tr>";
}

function csv() {
  const F = filtered(ROWS), on = cols();
  const val = (k, r) => { if (k === "res") return r.wl ? `${r.wl} ${r.tm_pts}-${r.opp_pts}` : ""; if (k === "opp") return (r.home ? "vs " : "@ ") + r.opp;
    if (k === "fg") return `${r.fgm}-${r.fga}`; if (k === "fg3") return `${r.fg3m}-${r.fg3a}`; if (k === "ft") return `${r.ftm}-${r.fta}`;
    const v = BYK[k][2](r); return v == null ? "" : typeof v === "number" ? +v.toFixed(k === "ts" ? 3 : 2) : v; };
  const lines = [["Season", ...on.map((k) => BYK[k][1]), "Par SE", "To date SE"].join(","),
    ...F.map((r) => [r.s, ...on.map((k) => `"${String(val(k, r)).replace(/"/g, '""')}"`), r.x ? r.x.se.toFixed(2) : "", r.c ? r.c.se.toFixed(2) : ""].join(","))];
  const name = ($("name").textContent || "player").trim().toLowerCase().replace(/[^a-z0-9]+/g, "-"), sp = spanSeasons();
  const a = document.createElement("a"); a.href = URL.createObjectURL(new Blob([lines.join("\n") + "\n# Par \u00b1 / HAPM: LUMA Basketball Research (hapm.github.lumahoops.org). Box scores: NBA.\n"], { type: "text/csv" }));
  a.download = `${name}_${sp[0]}${sp.length > 1 ? "_to_" + sp[sp.length - 1] : ""}_games.csv`; a.click();
}

// ---------------------------------------------------------------- chart
function el(tag, at, par) { const e = document.createElementNS(NS, tag); for (const k in at) e.setAttribute(k, at[k]); if (par) par.appendChild(e); return e; }
function smooth(pts) {               // Catmull-Rom -> cubic Bezier (a soft line through every point)
  if (pts.length < 3) return pts.length ? "M" + pts.map((p) => p.join(",")).join("L") : "";
  let d = `M${pts[0][0]},${pts[0][1]}`;
  for (let i = 0; i < pts.length - 1; i++) { const p0 = pts[i - 1] || pts[i], p1 = pts[i], p2 = pts[i + 1], p3 = pts[i + 2] || p2;
    d += `C${p1[0] + (p2[0] - p0[0]) / 6},${p1[1] + (p2[1] - p0[1]) / 6} ${p2[0] - (p3[0] - p1[0]) / 6},${p2[1] - (p3[1] - p1[1]) / 6} ${p2[0]},${p2[1]}`; }
  return d;
}
function rolling(rows, n) {          // Par ± of the last n games, possession-pooled
  const out = []; for (let i = 0; i < rows.length; i++) { if (i + 1 < n) { out.push(null); continue; } out.push(poolRows(rows.slice(i - n + 1, i + 1))); } return out;
}
const MINP = 250;          // Par ± view: a season's line starts at 250 possessions (as in the paper's Figure)
function chart() {
  const box = $("gchart"); box.innerHTML = ""; const F = filtered(ROWS), rows = F.filter((r) => r.x || r.c); if (!rows.length) { $("gleg").innerHTML = ""; return; }
  const st = G.st, filt = !!(st.q || st.ha || st.wl || st.opp || st.mo), games = false;
  const W = Math.max(320, box.clientWidth || 900), H = 280, m = { l: 44, r: 16, t: 26, b: 26 };
  const N = rows.length, X = (i) => m.l + (N === 1 ? 0.5 : i / (N - 1)) * (W - m.l - m.r);
  [...$("gview").children].forEach((b) => b.classList.toggle("on", b.dataset.v === st.view));
  const view = st.view;
  // Par ± to date within each season over the games shown (all games = his season to date); with SE
  let cum = Z(), cs = null; const toDate = rows.map((r) => { if (r.s !== cs) { cs = r.s; cum = Z(); } if (r.sums) r.sums.forEach((x, i) => cum[i] += x); return one(r.s, cum.slice()); });
  let run = 0; const total = rows.map((r) => (run += r.sums ? (r.sums[1] + r.sums[4]) / 100 : 0));     // Par in points, added up
  let dots, line, band = null, lineName, dotName, fmt = (v) => f1(v, 2);
  if (view === "par") { const ok = (p) => p && p.poss >= MINP; line = toDate.map((p) => ok(p) ? p.par : null); band = toDate.map((p) => ok(p) ? [p.par - p.se, p.par + p.se] : null); dots = rows.map(() => null);
    lineName = filt ? "Par \u00b1 so far, these games only" : "Par \u00b1 so far, each season"; dotName = ""; }
  else if (view === "total") { line = total; dots = rows.map(() => null); lineName = filt ? "Par added up, these games only (points)" : "Par added up (points)"; dotName = ""; fmt = (v) => (v > 0 ? "+" : v < 0 ? "−" : "") + Math.round(Math.abs(v)).toLocaleString(); }
  else { line = rows.map((r) => r.td); dots = toDate.map((p) => p ? p.par : null); lineName = "HAPM (time decay)"; dotName = filt ? "Par \u00b1 to date, these games only" : "Par \u00b1 to date, this season"; }
  // y range: fit the line; dots outside are pinned to the edge
  const lv = line.filter((v) => v != null), dv = dots.filter((v) => v != null).sort((a, b) => a - b);
  let lo, hi;
  { const q = (p) => dv.length ? dv[Math.floor(p * (dv.length - 1))] : 0;
    if (view === "par") { const bv = band.filter(Boolean).slice(Math.floor(band.length * 0.04)); lo = Math.min(...lv.slice(Math.floor(lv.length * 0.04)), ...bv.map((x) => x[0]).sort((a, b) => a - b).slice(Math.floor(bv.length * 0.02)), 0) - 1; hi = Math.max(...lv.slice(Math.floor(lv.length * 0.04)), ...bv.map((x) => x[1]).sort((a, b) => b - a).slice(Math.floor(bv.length * 0.02)), 0) + 1; }
    else if (view === "total") { lo = Math.min(...lv, 0); hi = Math.max(...lv, 0); const pad = (hi - lo) * 0.06 || 10; if (lo < 0) lo -= pad; if (hi > 0) hi += pad; }
    else { lo = Math.min(...lv, q(0.01), 0) - 1; hi = Math.max(...lv, q(0.99), 0) + 1; } }
  const span0 = hi - lo, step = view === "total" ? [10, 20, 50, 100, 200, 500, 1000, 2000, 5000].find((s) => span0 / s <= 6) || 10000 : span0 > 24 ? 10 : span0 > 10 ? 4 : 2; lo = Math.floor(lo / step) * step; hi = Math.ceil(hi / step) * step;
  const Y = (v) => m.t + (hi - Math.max(lo, Math.min(hi, v))) / (hi - lo) * (H - m.t - m.b);
  const svg = el("svg", { width: W, height: H, viewBox: `0 0 ${W} ${H}`, class: "gsvg" }, box);
  for (let v = lo; v <= hi + 1e-9; v += step) { el("line", { x1: m.l, x2: W - m.r, y1: Y(v), y2: Y(v), class: v === 0 ? "gz" : "gl0" }, svg); el("text", { x: m.l - 8, y: Y(v) + 4, "text-anchor": "end", class: "gt" }, svg).textContent = v > 0 ? "+" + v.toLocaleString() : v === 0 ? "0" : "\u2212" + Math.abs(v).toLocaleString(); }
  // season dividers + labels; month ticks inside a single season
  const span = spanSeasons();
  if (span.length > 1) {
    let i0 = 0; for (let i = 1; i <= N; i++) if (i === N || rows[i].s !== rows[i - 1].s) {
      if (i < N) el("line", { x1: (X(i - 1) + X(i)) / 2, x2: (X(i - 1) + X(i)) / 2, y1: m.t - 6, y2: H - m.b, class: "gdiv" }, svg);
      const w = X(i - 1) - X(i0); if (w > 34 || span.length <= 8) el("text", { x: (X(i0) + X(i - 1)) / 2, y: H - 8, "text-anchor": "middle", class: "gt" }, svg).textContent = w > 60 ? rows[i0].s : "'" + rows[i0].s.slice(5);
      i0 = i; }
  } else { let lm = -1; rows.forEach((r, i) => { if (r.mo !== lm) { lm = r.mo; el("line", { x1: X(i), x2: X(i), y1: H - m.b, y2: H - m.b + 4, class: "gz" }, svg); el("text", { x: X(i) + 3, y: H - 8, class: "gt" }, svg).textContent = MON[r.mo - 1]; } }); }
  // dots (soft) then the line
  const dg = el("g", {}, svg); G.dots = new Map();
  rows.forEach((r, i) => { const v = dots[i]; if (v == null) return;   // every game has a dot; the rare one beyond the range sits on the edge
    const rad = N > 600 ? 1.2 : N > 200 ? 1.5 : 1.9;
    const c = el("circle", { cx: X(i), cy: Y(v), r: rad, class: "gdot" }, dg); G.dots.set(r.gid, c); });
  if (band) { let s0 = 0; for (let i = 1; i <= N; i++) if (i === N || rows[i].s !== rows[i - 1].s) { const idx = []; for (let j = s0; j < i; j++) if (band[j]) idx.push(j);
      if (idx.length > 1) el("polygon", { points: idx.map((j) => `${X(j)},${Y(band[j][1])}`).concat(idx.slice().reverse().map((j) => `${X(j)},${Y(band[j][0])}`)).join(" "), class: "gband" }, svg); s0 = i; } }
  const brk = view === "par";          // the Par ± line restarts each season
  const segs = []; let cur = [];
  rows.forEach((r, i) => { const v = line[i]; if (v == null) { if (cur.length) segs.push(cur); cur = []; return; } if (brk && i && rows[i - 1].s !== r.s && cur.length) { segs.push(cur); cur = []; } cur.push([+X(i).toFixed(1), +Y(v).toFixed(1)]); });
  if (cur.length) segs.push(cur);
  for (const sgm of segs) el("path", { d: smooth(sgm), class: "gline" }, svg);
  if (view === "par") {                 // every season: a square at its final value, labelled (his season Par \u00b1 over the games shown)
    let s0 = 0; for (let i = 1; i <= N; i++) if (i === N || rows[i].s !== rows[i - 1].s) { let j = i - 1; while (j >= s0 && line[j] == null) j--;
      if (j >= s0) { el("rect", { x: X(j) - 3.5, y: Y(line[j]) - 3.5, width: 7, height: 7, class: "gsq" }, svg);
        if (i - s0 > 6 || N < 200) el("text", { x: X(j) - 4, y: Y(line[j]) - 7, "text-anchor": "end", class: "gendt" }, svg).textContent = f1(line[j], 1); }
      s0 = i; }
  }
  const lastI = view === "par" ? -1 : line.length - 1 - [...line].reverse().findIndex((v) => v != null);
  if (lastI >= 0 && lastI < N && line[lastI] != null) { el("circle", { cx: X(lastI), cy: Y(line[lastI]), r: 4.5, class: "gend" }, svg); el("text", { x: Math.min(X(lastI) + 7, W - m.r - 30), y: Y(line[lastI]) - 8, class: "gendt" }, svg).textContent = fmt(line[lastI]); }
  $("gleg").innerHTML = `<span class="lg-line"></span> ${lineName}` + (dotName ? ` <span class="lg-dot"></span> ${dotName}` : "") +
    `<span class="ghow">${{ hapm: "The line is his rating after each game: this season so far, combined with his past seasons. Higher = better; 0 = average.",
      par: "One line per season: his Par \u00b1 so far that season, per 100 possessions, starting at 250 possessions. The band is the uncertainty (\u00b1 1 SE); it narrows as games add up. The square is where the season ended.",
      total: "Every game's Par added up, in points. Climbing = beating par; flat = average; falling = below par. Steeper = better per game." }[view]}</span>`;
  // hover: guide + card; click = open the game; drag = dates
  const guide = el("line", { x1: 0, x2: 0, y1: m.t - 6, y2: H - m.b, class: "gguide", visibility: "hidden" }, svg);
  const hl = el("circle", { r: 5, class: "ghl", visibility: "hidden" }, svg), hd = el("circle", { r: 4, class: "ghd", visibility: "hidden" }, svg);
  const rect = el("rect", { x: m.l, y: 0, width: W - m.l - m.r, height: H, fill: "transparent" }, svg);
  const tip = $("gtip"), idxAt = (px) => Math.max(0, Math.min(N - 1, Math.round((px - m.l) / (W - m.l - m.r) * (N - 1))));
  const card = (r) => `<div class="tt-h">${ldate(r.date)} \u00b7 ${r.home ? "vs" : "@"} ${esc(r.opp)} \u00b7 <span class="${r.wl === "W" ? "w" : "lo"}">${r.wl ?? ""} ${r.tm_pts ?? ""}\u2013${r.opp_pts ?? ""}</span></div>` +
    (r.min != null ? `<div>${r.pts} pts \u00b7 ${r.reb} reb \u00b7 ${r.ast} ast \u00b7 PAC ${f1(BYK.pac[2](r), 1)} \u00b7 ${r.min} min \u00b7 +/\u2212 ${f1(r.pm, 0)}</div>` : "") +
    `<div class="tt-g"><span>Game Par \u00b1</span><b>${r.x ? f1(r.x.par) : ""}</b><span>To date</span><b>${r.c ? f1(r.c.par, 2) : ""}</b><span>HAPM</span><b>${f1(r.td, 2)}</b>${view === "total" ? `<span>Par total</span><b>${fmt(total[rows.indexOf(r)])} pts</b>` : ""}</div><div class="note">Click to open the game</div>`;
  let b0 = null, brush = null, moved = false;
  const pos = (e) => { const R = svg.getBoundingClientRect(); return e.clientX - R.left; };
  rect.addEventListener("mousemove", (e) => {
    const px = pos(e);
    if (b0 != null) { moved = moved || Math.abs(px - b0) > 5; const a = Math.min(b0, px), b = Math.max(b0, px); brush.setAttribute("x", a); brush.setAttribute("width", b - a); return; }
    const i = idxAt(px), r = rows[i], v = dots[i] ?? line[i]; guide.setAttribute("x1", X(i)); guide.setAttribute("x2", X(i)); guide.setAttribute("visibility", "visible");
    hl.setAttribute("cx", X(i)); hl.setAttribute("visibility", line[i] != null ? "visible" : "hidden"); if (line[i] != null) hl.setAttribute("cy", Y(line[i]));
    const dv0 = dots[i], inR = dv0 != null; hd.setAttribute("cx", X(i)); hd.setAttribute("visibility", inR ? "visible" : "hidden"); if (inR) hd.setAttribute("cy", Y(dv0));
    tip.innerHTML = card(r); tip.hidden = false; const bw = box.clientWidth, tw = tip.offsetWidth; tip.style.left = Math.min(Math.max(0, X(i) + 14), bw - tw - 4) + "px"; tip.style.top = (m.t + 30) + "px"; });
  rect.addEventListener("mouseleave", () => { if (b0 == null) { for (const x of [guide, hl, hd]) x.setAttribute("visibility", "hidden"); tip.hidden = true; } });
  rect.addEventListener("mousedown", (e) => { b0 = pos(e); moved = false; brush = el("rect", { x: b0, y: m.t - 6, width: 0, height: H - m.t - m.b + 6, class: "gbrush" }, svg); e.preventDefault(); });
  window.addEventListener("mouseup", (e) => { if (b0 == null) return; const px = pos(e), a = Math.min(b0, px), b = Math.max(b0, px); b0 = null; brush && brush.remove();
    if (moved) { G.st.from = rows[idxAt(a)].date; G.st.to = rows[idxAt(b)].date; draw(); }
    else { const r = rows[idxAt(px)]; G.st.g = String(r.gid); tip.hidden = true; table(); writeHash(); const tr = document.querySelector(`#games tr[data-g="${r.gid}"]`); if (tr) tr.scrollIntoView({ block: "center", behavior: "smooth" }); } });
}
function chartMark() { if (!G.dots) return; for (const [g, c] of G.dots) c.classList.toggle("sel", String(g) === G.st.g); }

// ---------------------------------------------------------------- level 3: one game opened (stints)
// stints: one binary per season (data/stints/<season>.bin, layout in data/stints/meta.json; see _export_hapm_stints.py)
const TYPES = { u1: Uint8Array, u2: Uint16Array, i2: Int16Array, f4: Float32Array };
async function stintPlayers() { if (!G.stP) G.stP = await (await fetch(`${ROOT}data/stints/players.json`)).json(); return G.stP; }
async function stintMeta() { if (!G.stM) G.stM = await (await fetch(`${ROOT}data/stints/meta.json`)).json(); return G.stM; }
G.stS = {};
function stintSeason(s) {
  if (!G.stS[s]) G.stS[s] = (async () => {
    const [M, buf, info] = await Promise.all([stintMeta(), fetch(`${ROOT}data/stints/${s}.bin`).then((x) => { if (!x.ok) throw 0; return x.arrayBuffer(); }),
      fetch(`${ROOT}data/stints/${s}.json`).then((x) => x.json())]);
    const n = new DataView(buf).getUint32(0, true), S = { n, info }; let pos = 4;
    for (const [name, dt, k] of M.row_layout) { pos += (4 - (pos % 4)) % 4; const T = TYPES[dt]; S[name] = new T(buf, pos, n * k); pos += n * k * T.BYTES_PER_ELEMENT; }
    S.gidIx = new Map(info.games.map((g, i) => [g[0], i]));
    S.byGi = new Map(); for (let r = 0; r < n; r++) { const g = S.gi[r]; let a = S.byGi.get(g); if (!a) S.byGi.set(g, (a = [])); a.push(r); }
    return S;
  })();
  return G.stS[s];
}
const clock = (el) => { const per = el >= 2880 ? 5 + Math.floor((el - 2880) / 300) : 1 + Math.floor(el / 720), end = el >= 2880 ? 2880 + (per - 4) * 300 : per * 720, left = end - el;
  return { per, lab: per <= 4 ? `Q${per}` : `OT${per - 4}`, clk: `${Math.floor(left / 60)}:${String(left % 60).padStart(2, "0")}` }; };
const mmss = (s) => `${Math.floor(s / 60)}:${String(Math.round(s % 60)).padStart(2, "0")}`;
async function openGame(gid, tr) {
  const r = ROWS.find((x) => x.gid === gid); if (!r) return;
  const ncol = tr.children.length, det = document.createElement("tr"); det.className = "gdet"; det.innerHTML = `<td colspan="${ncol}"><div class="gbox">Loading the game (first game of a season loads its stint file)\u2026</div></td>`;
  tr.after(det);
  let SS, P; try { [SS, P] = await Promise.all([stintSeason(r.s), stintPlayers()]); if (!SS.gidIx.has(gid)) throw 0; }
  catch (e) { det.querySelector(".gbox").innerHTML = "No stint data for this game."; return; }
  const me = P.indexOf(PID), name = (pid) => (S.slugs[pid] ? S.slugs[pid][0] : String(pid)), link = (pid) => S.slugs[pid] ? `<a href="${ROOT}player/${S.slugs[pid][1]}/">${esc(last(name(pid)))}</a>` : esc(pid);
  const myHome = r.home ? 1 : 0;
  const st = new Map(); let gameEnd = 2880;
  const R = (SS.byGi.get(SS.gidIx.get(gid)) || []).slice().sort((a, b) => SS.el[a] - SS.el[b] || SS.flags[a] - SS.flags[b]);
  for (const q of R) {
    const el0 = SS.el[q], secs = SS.secs[q], m0 = SS.m0[q], Pp = SS.P[q], y = SS.y[q], pl = SS.pl.subarray(q * 10, q * 10 + 10), ex = SS.ex.subarray(q * 10, q * 10 + 10);
    gameEnd = Math.max(gameEnd, el0 + secs);
    const k = pl.indexOf(me); if (k < 0 || Number.isNaN(ex[k])) continue;   // rows without an expected value are not in Par ±
    const sgn = k < 5 ? 1 : -1, b = k < 5 ? 0 : 5, ob = k < 5 ? 5 : 0;
    const s = st.get(el0) || { el: el0, secs, m0: myHome ? m0 : -m0, poss: 0, act: 0, exp: 0, mates: null, opps: null };
    s.secs = Math.max(s.secs, secs);
    s.act += sgn * y * Pp / 100; s.exp += sgn * ex[k] * Pp / 100; s.poss += Pp / 2;
    if (!s.mates) { s.mates = [...pl.slice(b, b + 5)].filter((_, i) => b + i !== k).map((i) => P[i]); s.opps = [...pl.slice(ob, ob + 5)].map((i) => P[i]); }
    st.set(el0, s);
  }
  const L = [...st.values()].sort((a, b) => a.el - b.el);
  const flow = R.map((q) => [SS.el[q], myHome ? SS.m0[q] : -SS.m0[q]]);
  const T = L.reduce((t, s) => ({ poss: t.poss + s.poss, act: t.act + s.act, exp: t.exp + s.exp, secs: t.secs + s.secs }), { poss: 0, act: 0, exp: 0, secs: 0 });
  const box = r.min != null ? `${r.min} min \u00b7 ${r.pts} pts \u00b7 ${r.reb} reb \u00b7 ${r.ast} ast \u00b7 ${r.stl} stl \u00b7 ${r.blk} blk \u00b7 ${r.tov} tov \u00b7 ${r.fgm}-${r.fga} FG \u00b7 ${r.fg3m}-${r.fg3a} 3P \u00b7 ${r.ftm}-${r.fta} FT \u00b7 +/\u2212 ${f1(r.pm, 0)}` : "";
  const g = det.querySelector(".gbox");
  g.innerHTML = `<div class="ghd"><b>${ldate(r.date)}: ${esc(r.team)} ${r.home ? "vs" : "@"} ${esc(r.opp)}, ${r.wl ?? ""} ${r.tm_pts ?? ""}\u2013${r.opp_pts ?? ""}</b> <span class="note">${box}</span></div>` +
    `<div class="gsum2">${L.length} stints \u00b7 ${mmss(T.secs)} on the floor \u00b7 ${n0(T.poss)} possessions \u00b7 margin <b>${f1(T.act, 1)}</b> pts vs expected ${f1(T.exp, 1)} \u00b7 Par <b style="background:${parBg((T.act - T.exp) * 100 / Math.max(T.poss, 1))}">${f1(T.act - T.exp, 1)} pts</b>` +
    (r.x ? ` = ${f1(r.x.par)} per 100 (Off ${f1(r.x.o)}, Def ${f1(r.x.d)}, \u00b1${r.x.se.toFixed(0)})` : "") + (r.td != null ? ` \u00b7 HAPM after this game ${f1(r.td, 2)}` : "") + `</div>` +
    `<div class="gtl"></div>` +
    `<table class="gst"><thead><tr><th class="l">Start</th><th>Length</th><th>Lead</th><th class="l">With him</th><th class="l">Against</th><th class="ps">Poss</th><th>Margin</th><th>Expected</th><th>Par</th></tr></thead><tbody>` +
    L.map((s) => { const c = clock(s.el), p = s.act - s.exp;
      return `<tr><td class="l">${c.lab} ${c.clk}</td><td>${mmss(s.secs)}</td><td>${f1(s.m0, 0) || "0"}</td><td class="l">${s.mates.map(link).join(", ")}</td><td class="l">${s.opps.map(link).join(", ")}</td>` +
        `<td class="ps">${s.poss.toFixed(1)}</td><td>${f1(s.act, 1)}</td><td>${f1(s.exp, 1)}</td><td class="v" style="background:${parBg(p, 6)}">${f1(p, 1)}</td></tr>`; }).join("") +
    `</tbody></table><p class="note">Margin and expected are in points, relative to a league-average team. Lead = his team's score margin when the stint started. Par = margin minus expected; over the game it adds up to his Par \u00b1 for the game. Click a column head to sort.</p>`;
  timeline(g.querySelector(".gtl"), L, flow, gameEnd);
  sortable(g.querySelector(".gst"));
}
function timeline(box, L, flow, end) {
  const W = Math.max(320, box.clientWidth || 900), H = 140, m = { l: 44, r: 16, t: 8, b: 18 };
  const X = (s) => m.l + s / end * (W - m.l - m.r), mx = Math.max(10, ...flow.map((f) => Math.abs(f[1]))), Y = (v) => m.t + 30 + (mx - v) / (2 * mx) * (H - m.t - m.b - 30);
  const svg = el("svg", { width: W, height: H, class: "gsvg" }, box);
  for (let q = 0; q <= end; q += q < 2880 ? 720 : 300) { el("line", { x1: X(q), x2: X(q), y1: m.t, y2: H - m.b, class: "gl0" }, svg); if (q < end) el("text", { x: X(q) + 3, y: H - 5, class: "gt" }, svg).textContent = q < 2880 ? `Q${q / 720 + 1}` : `OT${(q - 2880) / 300 + 1}`; }
  el("text", { x: m.l - 8, y: m.t + 16, "text-anchor": "end", class: "gt" }, svg).textContent = "on floor";
  for (const s of L) { const p = s.act - s.exp; const rc = el("rect", { x: X(s.el), y: m.t + 4, width: Math.max(1.5, X(s.el + s.secs) - X(s.el)), height: 18, rx: 2, fill: parFill(p, 6), class: "gbar" }, svg);
    el("title", {}, rc).textContent = `${clock(s.el).lab} ${clock(s.el).clk}, ${mmss(s.secs)}: margin ${f1(s.act, 1)} vs expected ${f1(s.exp, 1)} = Par ${f1(p, 1)} pts`; }
  el("line", { x1: m.l, x2: W - m.r, y1: Y(0), y2: Y(0), class: "gz" }, svg);
  el("text", { x: m.l - 8, y: Y(0) + 4, "text-anchor": "end", class: "gt" }, svg).textContent = "lead";
  el("path", { d: smooth(flow.map((f) => [X(f[0]), Y(f[1])])), class: "gflow" }, svg);
}
function sortable(t) {
  t.querySelectorAll("th").forEach((h, i) => h.onclick = () => {
    const body = t.tBodies[0], rows = [...body.rows], dir = h.dataset.d === "d" ? 1 : -1; h.dataset.d = dir > 0 ? "a" : "d";
    const v = (r) => { if (r.cells[i].dataset.v) return r.cells[i].dataset.v; const s = r.cells[i].textContent.replace("\u2212", "-").replace(/^(Q|OT)(\d) (\d+):(\d+)/, (_, a, b, c, d) => String((a === "Q" ? +b : 4 + +b) * 1e4 - (+c * 60 + +d))); const n = parseFloat(s); return isNaN(n) ? s : n; };
    rows.sort((a, b) => (v(a) > v(b) ? 1 : v(a) < v(b) ? -1 : 0) * dir).forEach((r) => body.appendChild(r)); });
}

// ================================================================ STINTS TAB (v2, 2026-11-26)
// How does he do when ___ ? Teammates and opponents each get Combo / On / Off (databallr style): Combo players split the
// result into every on / off combination (one clean row each), On / Off hold for every row. Each row: held-out Par ± (SE) next
// to the raw on-floor margin, so the gap between them is what his teammates and opponents explain. Built from
// data/stints/<season>.bin; Par ± pooled exactly like the Games tab (per-season SE blocks).
const Q = { cm: [], co: [], tw: [], tx: [], on: [], off: [], f: [], ag: "", pk: [], md: "rows", x: "date", so: "", sd: "d", hr: [], hc: [], sub: "wowy", fr: "", me: "", cb: "par.o.d", dm: "chg", cl: "0", ow: "", vw: "", mp: "", bs: "" };
const CB = () => new Set(Q.cb.split(".").filter(Boolean));
const pids = (s) => (s ? s.split(".").map(Number).filter(Boolean) : []);
const QK = { cm: 1, co: 1, tw: 1, tx: 1, on: 1, off: 1 };
// filters (the "+ Add filter" rows) <-> hash: rows joined by ";", fields by ","
const FENC = (f) => [f.t, ...(f.t === "tm" || f.t === "op" ? [f.m, f.n, f.p.join(".")] : f.t === "ot" ? [f.dir, f.n, f.st] : f.t === "q" ? [f.v.join(".")] : f.t === "sm" || f.t === "dt" ? [f.a, f.b] : f.t === "tr" ? [f.who, f.agg, f.st, f.op, f.v, f.m, f.n] : [f.a])].join(",");
function FDEC(s) { const [t, a = "", b = "", c = "", ...z] = s.split(",");
  if (t === "tr") return { t, who: a === "o" ? "o" : "m", agg: b === "cnt" ? "cnt" : "avg", st: c || "p3", op: z[0] === "le" ? "le" : "ge", v: z[1] || "", m: z[2] || "al", n: z[3] || "2" };
  switch (t) { case "tm": case "op": return { t, m: a || "al", n: b || "1", p: pids(c) }; case "ot": return { t, dir: a || "top", n: b || "5", st: c || "net" };
    case "q": return { t, v: a ? a.split(".") : [] }; case "sm": case "dt": return { t, a, b }; case "ck": case "ln": return { t, a }; } return null; }
function readQ() { const H = Object.fromEntries(new URLSearchParams(location.hash.slice(1)));
  for (const k in QK) Q[k] = pids(H[k]); for (const k of ["ag", "so", "fr"]) Q[k] = H[k] || ""; Q.sd = H.sd === "a" ? "a" : "d";
  for (const k of ["pk", "hr", "hc"]) Q[k] = H[k] ? H[k].split(".") : []; Q.md = H.md === "overlap" ? "overlap" : "rows";
  Q.x = H.x === "poss" ? "poss" : "date"; Q.me = H.me === "1" ? "1" : ""; Q.cb = H.cb != null ? H.cb : "par.o.d"; Q.dm = ["only", "pct"].includes(H.dm) ? H.dm : "chg"; Q.cl = H.cl === "1" ? "1" : "0"; Q.ow = H.ow === "1" ? "1" : ""; Q.mp = H.mp || ""; Q.bs = H.bs || ""; Q.vw = H.vw === "card" ? "card" : ""; Q.sub = H.sub === "find" ? "find" : "wowy"; Q.f = H.f ? H.f.split(";").map(FDEC).filter(Boolean) : []; }
function writeQ() { const H = Object.fromEntries(new URLSearchParams(location.hash.slice(1)));
  for (const k of [...Object.keys(QK), "ag", "pk", "md", "so", "sd", "hr", "hc", "x", "sub", "f", "fr", "bx", "me", "cb", "dm", "cl", "ow", "vw", "mp", "bs"]) delete H[k];
  for (const k in QK) if (Q[k].length) H[k] = Q[k].join("."); for (const k of ["ag", "so", "fr"]) if (Q[k]) H[k] = Q[k];
  for (const k of ["pk", "hr", "hc"]) if (Q[k].length) H[k] = Q[k].join("."); if (Q.md !== "rows") H.md = Q.md; if (Q.so && Q.sd === "a") H.sd = "a";
  if (Q.x !== "date") H.x = Q.x; if (Q.me) H.me = "1"; if (Q.cb !== "par.o.d") H.cb = Q.cb; if (Q.dm !== "chg") H.dm = Q.dm; if (Q.cl === "1") H.cl = "1"; if (Q.ow) H.ow = "1"; if (Q.mp) H.mp = Q.mp; if (Q.bs) H.bs = Q.bs; if (Q.vw) H.vw = Q.vw; if (Q.sub !== "wowy") H.sub = Q.sub; if (Q.f.length) H.f = Q.f.map(FENC).join(";");
  history.replaceState(null, "", "#" + new URLSearchParams(H).toString()); writeHash(); }
const nm = (pid) => (S.slugs[pid] ? S.slugs[pid][0] : String(pid)), lnm = (pid) => last(nm(pid));
const plink = (pid) => S.slugs[pid] ? `<a href="${ROOT}player/${S.slugs[pid][1]}/">${esc(lnm(pid))}</a>` : esc(pid);
const COL = ["#B5577A", "#8a8d94", "#2f6f9f", "#c08a1e", "#4b8a52", "#7b5ea7", "#c45050", "#3a9a9a"];

// stint sides of one player in a season (one per stint x end of the floor), cached per season + player
G.sides = {};
async function sidesFor(s, pid = PID) {
  const key = s + ":" + pid; if (G.sides[key]) return G.sides[key];
  const [SS, P] = await Promise.all([stintSeason(s), stintPlayers()]); const me = P.indexOf(pid), out = [];
  if (me < 0) return (G.sides[key] = out);
  const games = SS.info.games, teams = SS.info.teams;
  for (let q = 0, N = SS.n; q < N; q++) {
    const b = q * 10; let k = -1; for (let j = 0; j < 10; j++) if (SS.pl[b + j] === me) { k = j; break; }
    if (k < 0) continue; const e = SS.ex[b + k]; if (Number.isNaN(e)) continue;
    const off = k < 5, g = games[SS.gi[q]], my = teams[off ? SS.to[q] : SS.td[q]], home = g[2] === my, lead = home ? SS.m0[q] : -SS.m0[q];
    const mb = off ? 0 : 5, ob = off ? 5 : 0, mates = [], opps = [];
    for (let j = mb; j < mb + 5; j++) if (j !== k) mates.push(P[SS.pl[b + j]]);
    for (let j = ob; j < ob + 5; j++) opps.push(P[SS.pl[b + j]]);
    const el0 = SS.el[q], per = el0 >= 2880 ? 5 + Math.floor((el0 - 2880) / 300) : 1 + Math.floor(el0 / 720), pend = el0 >= 2880 ? 2880 + (per - 4) * 300 : per * 720;
    out.push({ s, q, k, gid: g[0], date: g[1], el: el0, left: pend - el0, secs: SS.secs[q], per, lead, off, P: SS.P[q], y: SS.y[q], e, mates, opps, team: my, opp: teams[off ? SS.td[q] : SS.to[q]], home });
  }
  out.sort((a, b) => (a.date < b.date ? -1 : a.date > b.date ? 1 : a.gid - b.gid || a.el - b.el || (a.off ? -1 : 1)));
  return (G.sides[key] = out);
}
G.offs = {};
async function offSidesFor(s, mine) {        // mine = his on-floor sides that season (games + his team in each game)
  const key = s + ":" + PID; if (G.offs[key]) return G.offs[key];
  const [SS, P] = await Promise.all([stintSeason(s), stintPlayers()]), me = P.indexOf(PID), out = [], games = SS.info.games, teams = SS.info.teams, tm = new Map();
  for (const d of mine) tm.set(d.gid, d.team);
  for (const [gid, team] of tm) { const gi = SS.gidIx.get(gid); if (gi == null) continue;
    for (const q of SS.byGi.get(gi) || []) { const b = q * 10; let here = false; for (let j = 0; j < 10; j++) if (SS.pl[b + j] === me) { here = true; break; } if (here) continue;
      const to = teams[SS.to[q]], td = teams[SS.td[q]]; if (to !== team && td !== team) continue;
      const off = to === team, g = games[gi], home = g[2] === team, lead = home ? SS.m0[q] : -SS.m0[q], mb = off ? 0 : 5, ob = off ? 5 : 0, mates = [], opps = [];
      for (let j = mb; j < mb + 5; j++) mates.push(P[SS.pl[b + j]]); for (let j = ob; j < ob + 5; j++) opps.push(P[SS.pl[b + j]]);
      const el0 = SS.el[q], per = el0 >= 2880 ? 5 + Math.floor((el0 - 2880) / 300) : 1 + Math.floor(el0 / 720), pend = el0 >= 2880 ? 2880 + (per - 4) * 300 : per * 720;
      out.push({ s, q, gid, date: g[1], el: el0, left: pend - el0, secs: SS.secs[q], per, lead, off, P: SS.P[q], y: SS.y[q], e: NaN, mates, opps, team, opp: off ? td : to, home, self0: true }); } }
  out.sort((a, b) => (a.date < b.date ? -1 : a.date > b.date ? 1 : a.gid - b.gid || a.el - b.el || (a.off ? -1 : 1)));
  return (G.offs[key] = out);
}
// his own counts per stint (data/stints/<season>.own.bin): offense five x [rim, mid, 3PA, FTA, TOV, OREB], 4 bits each
G.own = {};
function ownSeason(s) {
  if (!G.ownP) G.ownP = {};
  if (!G.ownP[s]) G.ownP[s] = fetch(`${ROOT}data/stints/${s}.own.bin`).then((x) => { if (!x.ok) throw 0; return x.arrayBuffer(); })
    .then((buf) => { const n = new DataView(buf).getUint32(0, true); G.own[s] = new Uint8Array(buf, 4, n * 15); }).catch(() => {});
  return G.ownP[s];
}
const ownGet = (O, q, k, c) => { const i = k * 6 + c, b = O[q * 15 + (i >> 1)]; return i & 1 ? b >> 4 : b & 15; };
// his own rates: attempts / TOV per 100 possessions on the floor, OREB per team miss; league = a fifth of the team rate that season
function ownStats(w, e, P, ms, ems) {
  const o = {}; [["rim", 0], ["mid", 1], ["r3", 2], ["fta", 3], ["tov", 4]].forEach(([n, j]) => { o["o_" + n] = P > 0 ? 100 * w[j] / P : null; o["o_" + n + "_lg"] = P > 0 ? 100 * (w[j] - e[j]) / P : null; });
  o.o_orb = ms > 0 ? 100 * w[5] / ms : null; o.o_orb_lg = ms > 0 ? 100 * (w[5] - ems) / ms : null; return o;
}
function poolSides(list) {
  if (list.length && list[0].self0) return poolOff(list);
  const ow = new Float64Array(6), ew = new Float64Array(6); let oms = 0, oems = 0, hasO = false;
  const m = new Map(), bo = new Float64Array(10), bd = new Float64Array(10), eo = new Float64Array(10), ed = new Float64Array(10); let po = 0, pd = 0, hasB = false;
  for (const d of list) { let a = m.get(d.s); if (!a) m.set(d.s, (a = Z()));
    if (d.off) { a[0] += d.P; a[1] += d.P * (d.y - d.e); a[2] += d.P * d.y; } else { a[3] += d.P; a[4] += d.P * (d.e - d.y); a[5] -= d.P * d.y; }
    const B = G.box[d.s], L = G.lgb[d.s]; if (B && L) { hasB = true; const b = d.q * 10, t = d.off ? bo : bd, e = d.off ? eo : ed;
      for (let j = 0; j < 10; j++) t[j] += B[b + j]; for (const j of [0, 2, 4, 6, 8]) e[j] += L.r[j] * d.P; e[9] += L.orb * miss(B, b); if (d.off) po += d.P; else pd += d.P;
      const O = Q.ow && d.off && G.own[d.s]; if (O) { hasO = true; for (let c = 0; c < 6; c++) ow[c] += ownGet(O, d.q, d.k, c); [0, 2, 4, 6, 8].forEach((j, c) => ew[c] += L.r[j] * d.P / 5); const ms = miss(B, b); oms += ms; oems += L.orb * ms / 5; } } }
  const p = pooled(m); if (p) { p.games = new Set(list.map((d) => d.gid)).size; if (hasB) Object.assign(p, boxStats(bo, eo, po, "o_"), boxStats(bd, ed, pd, "d_")); if (hasB && Q.ow) Object.assign(p, hasO ? ownStats(ow, ew, po, oms, oems) : { o_rim: null, o_mid: null, o_r3: null, o_fta: null, o_tov: null, o_orb: null }); } return p;
}
// his team with him on the bench: no Par ± (he is not on the floor), raw net + shot types only
function poolOff(list) {
  let Wo = 0, Ao = 0, Wd = 0, Ad = 0; const bo = new Float64Array(10), bd = new Float64Array(10), eo = new Float64Array(10), ed = new Float64Array(10); let po = 0, pd = 0, hasB = false;
  for (const d of list) { if (d.off) { Wo += d.P; Ao += d.P * d.y; } else { Wd += d.P; Ad -= d.P * d.y; }
    const B = G.box[d.s], L = G.lgb[d.s]; if (B && L) { hasB = true; const b = d.q * 10, t = d.off ? bo : bd, e = d.off ? eo : ed;
      for (let j = 0; j < 10; j++) t[j] += B[b + j]; for (const j of [0, 2, 4, 6, 8]) e[j] += L.r[j] * d.P; e[9] += L.orb * miss(B, b); if (d.off) po += d.P; else pd += d.P; } }
  if (!(Wo > 0) || !(Wd > 0)) return null;
  const p = { poss: (Wo + Wd) / 2, act: Ao / Wo + Ad / Wd, par: null, o: null, d: null, exp: null, se: null, games: new Set(list.map((d) => d.gid)).size, bench: true };
  if (hasB) Object.assign(p, boxStats(bo, eo, po, "o_"), boxStats(bd, ed, pd, "d_"));
  if (Q.ow) for (const k of ["o_rim", "o_mid", "o_r3", "o_fta", "o_tov", "o_orb"]) { p[k] = null; p[k + "_lg"] = null; }      // his own shots: none on the bench
  return p;
}
// percentiles: every player-season with 800+ possessions on that end, his on-floor shot types minus league (that season)
G.pctS = {}; G.pctSpan = {};
const BXK = ["o_rim", "o_mid", "o_r3", "o_fta", "o_tov", "o_orb", "d_rim", "d_mid", "d_r3", "d_fta", "d_tov", "d_drb"];
async function pctSeason(s) {
  const key = s + (Q.ow ? ":own" : ""); if (G.pctS[key]) return G.pctS[key];
  await boxSeason(s); if (Q.ow) await ownSeason(s); const OW = Q.ow ? G.own[s] : null; const [SS, P] = await Promise.all([stintSeason(s), stintPlayers()]), B = G.box[s], L = G.lgb[s]; if (!B || !L) return (G.pctS[key] = {});
  const NP = P.length, C = [new Float64Array(NP * 10), new Float64Array(NP * 10)], W = [new Float64Array(NP), new Float64Array(NP)], OC = OW ? new Float64Array(NP * 6) : null, OM = OW ? new Float64Array(NP) : null;
  for (let q = 0; q < SS.n; q++) { const b = q * 10, w = SS.P[q], ms = OW ? miss(B, b) : 0;
    for (let j = 0; j < 10; j++) { const side = j < 5 ? 0 : 1, pi = SS.pl[b + j], c = C[side], o = pi * 10; W[side][pi] += w; for (let k = 0; k < 10; k++) c[o + k] += B[b + k];
      if (OW && j < 5) { for (let c6 = 0; c6 < 6; c6++) OC[pi * 6 + c6] += ownGet(OW, q, j, c6); OM[pi] += ms; } } }
  const out = {}; for (const k of BXK) out[k] = [];
  for (let pi = 0; pi < NP; pi++) for (const side of [0, 1]) { const w = W[side][pi]; if (w < 800) continue;
    const c = C[side].subarray(pi * 10, pi * 10 + 10), e = new Float64Array(10); for (const j of [0, 2, 4, 6, 8]) e[j] = L.r[j] * w;
    e[9] = L.orb * (c[0] + c[2] + c[4] - c[1] / 2 - c[3] / 2 - c[5] / 3); let S = boxStats(c, e, w, side ? "d_" : "o_");
    if (OW && !side) S = ownStats(OC.subarray(pi * 6, pi * 6 + 6), [0, 2, 4, 6, 8].map((j) => L.r[j] * w / 5), w, OM[pi], L.orb * OM[pi] / 5);
    for (const k of BXK) if (k[0] === (side ? "d" : "o") && S[k + "_lg"] != null) out[k].push(S[k + "_lg"]); }
  return (G.pctS[key] = out);
}
async function pctFor(span) {
  const key = span.join(",") + (Q.ow ? ":own" : ""); if (G.pctSpan[key]) return G.pctSpan[key];
  const L = await Promise.all(span.map(pctSeason)), out = {}; for (const k of BXK) out[k] = Float64Array.from(L.flatMap((x) => x[k] || [])).sort();
  return (G.pctSpan[key] = out);
}
function pctOf(k, v) { const A = G.pctNow && G.pctNow[k]; if (!A || !A.length || v == null) return null; let lo = 0, hi = A.length; while (lo < hi) { const m = (lo + hi) >> 1; if (A[m] < v) lo = m + 1; else hi = m; } return Math.min(99, Math.max(1, Math.round(100 * lo / A.length))); }
// shooting and ball control from the per-stint counts (data/stints/<season>.box.bin, same row order as <season>.bin)
G.box = {};
G.lgb = {};
function boxSeason(s) {
  if (!G.boxP) G.boxP = {};
  if (!G.boxP[s]) G.boxP[s] = Promise.all([fetch(`${ROOT}data/stints/${s}.box.bin`).then((x) => { if (!x.ok) throw 0; return x.arrayBuffer(); }), stintSeason(s)])
    .then(([buf, SS]) => { const n = new DataView(buf).getUint32(0, true), B = new Uint8Array(buf, 4, n * 10), c = new Float64Array(10); let P = 0, ms = 0;
      for (let q = 0; q < n; q++) { for (let j = 0; j < 10; j++) c[j] += B[q * 10 + j]; P += SS.P[q]; ms += miss(B, q * 10); }
      G.lgb[s] = { r: [...c].map((x) => x / P), orb: c[9] / ms }; G.box[s] = B; }).catch(() => {});      // league rates: every stint that season
  return G.boxP[s];
}
const miss = (B, b) => B[b] + B[b + 2] + B[b + 4] - B[b + 1] / 2 - B[b + 3] / 2 - B[b + 5] / 3;   // missed field goals
// per 100 possessions (shots, FTA, turnovers) or per missed field goal (offensive rebounds); _lg = minus the league-expected value
function boxStats(c, e, P, k) {
  const o = {}, ms = c[0] + c[2] + c[4] - c[1] / 2 - c[3] / 2 - c[5] / 3;
  [["rim", 0], ["mid", 2], ["r3", 4], ["fta", 6], ["tov", 8]].forEach(([n, j]) => { o[k + n] = P > 0 ? 100 * c[j] / P : null; o[k + n + "_lg"] = P > 0 ? 100 * (c[j] - e[j]) / P : null; });
  const orb = ms > 0 ? 100 * c[9] / ms : null, d = ms > 0 ? 100 * (c[9] - e[9]) / ms : null;
  if (k === "o_") { o.o_orb = orb; o.o_orb_lg = d; } else { o.d_drb = orb == null ? null : 100 - orb; o.d_drb_lg = d == null ? null : -d; }
  return o;
}
const BXO_T = [["o_rim", "Rim", "His team's rim attempts (4 ft or closer) per 100 possessions while he is on the floor"], ["o_mid", "Mid", "His team's other two-point attempts per 100 possessions while he is on the floor"],
  ["o_r3", "3PA", "His team's three-point attempts per 100 possessions while he is on the floor"], ["o_fta", "FTA", "His team's free-throw attempts per 100 possessions while he is on the floor"],
  ["o_tov", "TOV", "His team's turnovers per 100 possessions while he is on the floor"], ["o_orb", "OREB%", "His team's offensive rebounds per missed field goal while he is on the floor"]];
const BXO_O = [["o_rim", "His rim", "His own rim attempts (4 ft or closer) per 100 possessions on the floor; league = a fifth of the league team rate"], ["o_mid", "His mid", "His own other two-point attempts per 100 possessions on the floor"],
  ["o_r3", "His 3PA", "His own three-point attempts per 100 possessions on the floor"], ["o_fta", "His FTA", "His own free-throw attempts per 100 possessions on the floor"],
  ["o_tov", "His TOV", "His own turnovers per 100 possessions on the floor"], ["o_orb", "His OREB%", "His own offensive rebounds per team missed field goal; league = a fifth of the league rate"]];
let BXO = BXO_T;
const BXD = [["d_rim", "Opp rim", "Opponents' rim attempts per 100 possessions while he is on the floor"], ["d_mid", "Opp mid", "Opponents' other two-point attempts per 100 possessions while he is on the floor"],
  ["d_r3", "Opp 3PA", "Opponents' three-point attempts per 100 possessions while he is on the floor"], ["d_fta", "Opp FTA", "Opponents' free-throw attempts per 100 possessions while he is on the floor"],
  ["d_tov", "Forced TOV", "Opponents' turnovers per 100 possessions while he is on the floor"], ["d_drb", "DREB%", "His team's defensive rebounds per opponent missed field goal while he is on the floor"]];
// ---- filters: every situation is a "+ Add filter" row (no preset menus)
const num = (v) => (v === "" || v == null || isNaN(+v) ? null : +v);
const FT = { tm: "Teammates on the floor", op: "Opponents on the floor", ot: "Opponent team strength", q: "Quarter", sm: "Score margin at the start", ck: "Time left in the period", dt: "Dates", ln: "Stint length", tr: "Player traits on the floor" };
const FNEW = { tm: () => ({ t: "tm", m: "al", n: "1", p: [] }), op: () => ({ t: "op", m: "al", n: "1", p: [] }), ot: () => ({ t: "ot", dir: "top", n: "5", st: "net" }),
  q: () => ({ t: "q", v: [] }), sm: () => ({ t: "sm", a: "", b: "" }), ck: () => ({ t: "ck", a: "" }), dt: () => ({ t: "dt", a: "", b: "" }), ln: () => ({ t: "ln", a: "" }), tr: () => ({ t: "tr", who: "m", agg: "avg", st: "p3", op: "ge", v: "", m: "al", n: "2" }) };
// player traits (data/stints/traits.json): that season's box-score facts, height and HAPM
const TRS = { p3: "3P%", a3: "3PA per 36", r3: "3PA share of FGA %", ts: "TS%", usg: "usage %", ht: "height", hapm: "HAPM" };
const htIn = (v) => { const s = String(v).trim(), m = s.match(/^(\d)\s*['\-\s]\s*(\d{1,2})/); return m ? +m[1] * 12 + +m[2] : num(s); };
const htTxt = (n) => `${Math.floor(n / 12)}'${n % 12}"`;
async function traits() {
  if (G.trt) return G.trt;
  const J = await fetch(`${ROOT}data/stints/traits.json`).then((x) => x.json()), T = {};
  for (const [s, D] of Object.entries(J.seasons)) { const m = new Map(); for (const k in D) m.set(+k, D[k]); T[s] = m; }
  G.trtc = Object.fromEntries(J.cols.map((c, i) => [c, i])); return (G.trt = T);
}
G.tr = {};
async function teamRanks(s) {               // full-season team ratings from the stints (per 100 vs league): offense, defense, net + ranks
  if (G.tr[s]) return G.tr[s];
  const SS = await stintSeason(s), T = SS.info.teams, a = T.map(() => [0, 0, 0, 0]);
  for (let q = 0; q < SS.n; q++) { const P = SS.P[q], y = SS.y[q]; a[SS.to[q]][0] += P * y; a[SS.to[q]][1] += P; a[SS.td[q]][2] -= P * y; a[SS.td[q]][3] += P; }
  const R = {}; T.forEach((t, i) => { if (a[i][1] > 0 && a[i][3] > 0) { const off = a[i][0] / a[i][1], def = a[i][2] / a[i][3]; R[t] = { off, def, net: off + def, rk: {} }; } });
  const n = Object.keys(R).length; for (const st of ["off", "def", "net"]) Object.keys(R).sort((x, y) => R[y][st] - R[x][st]).forEach((t, i) => R[t].rk[st] = i + 1);
  return (G.tr[s] = { R, n });
}
function fpass(d) {
  for (const f of Q.f) {
    if (f.t === "tm" || f.t === "op") { if (!f.p.length) continue; const arr = f.t === "tm" ? d.mates : d.opps, c = f.p.filter((p) => arr.includes(p)).length, n = +f.n || 0;
      if (f.m === "ex" ? c !== n : f.m === "am" ? c > n : c < n) return false; }
    else if (f.t === "ot") { const T = G.tr[d.s], r = T && T.R[d.opp]; if (!r) return false; const k = r.rk[f.st], n = +f.n || 0; if (f.dir === "top" ? k > n : k <= T.n - n) return false; }
    else if (f.t === "q") { if (f.v.length && !f.v.includes(d.per > 4 ? "OT" : String(d.per))) return false; }
    else if (f.t === "sm") { const a = num(f.a), b = num(f.b); if ((a != null && d.lead < a) || (b != null && d.lead > b)) return false; }
    else if (f.t === "ck") { const a = num(f.a); if (a != null && d.left > a * 60) return false; }
    else if (f.t === "dt") { if ((f.a && d.date < f.a) || (f.b && d.date > f.b)) return false; }
    else if (f.t === "ln") { const a = num(f.a); if (a != null && d.secs < a) return false; }
    else if (f.t === "tr") { const v = f.st === "ht" ? htIn(f.v) : num(f.v); if (v == null || !G.trt) continue;
      const T = G.trt[d.s], ci = G.trtc[f.st], arr = f.who === "m" ? d.mates : d.opps, xs = arr.map((p) => { const r = T && T.get(p); return r ? r[ci] : null; });
      const ok = (x) => x != null && (f.op === "ge" ? x >= v : x <= v);
      if (f.agg === "avg") { const g = xs.filter((x) => x != null); if (!g.length || !ok(g.reduce((a, b) => a + b, 0) / g.length)) return false; }
      else { const c = xs.filter(ok).length, n = +f.n || 0; if (f.m === "ex" ? c !== n : f.m === "am" ? c > n : c < n) return false; } }
  }
  return true;
}
const MODE = { al: "at least", ex: "exactly", am: "at most" }, STN = { net: "net rating", off: "offense", def: "defense" };
function fdesc(f) {
  const L = (a) => a.map(lnm).join(", ");
  switch (f.t) {
    case "tm": case "op": if (!f.p.length) return ""; return f.p.length === 1 ? (+f.n > 0 && f.m !== "am" ? `${f.t === "tm" ? "with" : "against"} ${L(f.p)}` : `${L(f.p)} off the floor`) : `${MODE[f.m]} ${f.n} of ${L(f.p)} ${f.t === "tm" ? "with him" : "against him"}`;
    case "ot": return `vs ${f.dir === "top" ? "top" : "bottom"} ${f.n} ${STN[f.st]} teams`;
    case "q": return f.v.length ? f.v.map((v) => (v === "OT" ? "OT" : "Q" + v)).join(" / ") : "";
    case "sm": return f.a || f.b ? `margin ${f.a || "any"} to ${f.b || "any"}` : "";
    case "ck": return f.a ? `${f.a} min or less left in the period` : "";
    case "dt": return f.a || f.b ? `${f.a || "start"} to ${f.b || "end"}` : "";
    case "ln": return f.a ? `stints of ${f.a}+ seconds` : "";
    case "tr": { if (f.v === "") return ""; const v = f.st === "ht" ? htTxt(htIn(f.v) || 0) : f.v, op = f.op === "ge" ? "at least" : "at most", who = f.who === "m" ? "teammates" : "opponents";
      return f.agg === "avg" ? `${who}' average ${TRS[f.st]} ${op} ${v}` : `${MODE[f.m]} ${f.n} ${+f.n === 1 ? who.slice(0, -1) : who} with ${TRS[f.st]} ${op} ${v}`; } }
  return "";
}
function fbar() {
  const opt = (o, v) => Object.entries(o).map(([k, l]) => `<option value="${k}" ${k === v ? "selected" : ""}>${l}</option>`).join("");
  const ppl = (f, i) => f.p.map((p) => `<span class="fp">${esc(nm(p))}<button class="hx" data-i="${i}" data-rm="${p}" title="Remove">\u00d7</button></span>`).join("") + `<input class="fadd" data-i="${i}" list="sfl-${f.t}" placeholder="+ ${f.t === "tm" ? "teammate" : "opponent"}">`;
  const row = (f, i) => { let c = "";
    if (f.t === "tm" || f.t === "op") c = `<select data-i="${i}" data-k="m">${opt(MODE, f.m)}</select> <input type="number" min="0" max="5" data-i="${i}" data-k="n" value="${f.n}"> of ${ppl(f, i)}`;
    else if (f.t === "ot") c = `vs <select data-i="${i}" data-k="dir">${opt({ top: "top", bottom: "bottom" }, f.dir)}</select> <input type="number" min="1" max="29" data-i="${i}" data-k="n" value="${f.n}"> teams by <select data-i="${i}" data-k="st">${opt(STN, f.st)}</select> <span class="note">(that season's full-season rating)</span>`;
    else if (f.t === "q") c = `<span class="seg">${["1", "2", "3", "4", "OT"].map((v) => `<button data-i="${i}" data-qv="${v}" class="${f.v.includes(v) ? "on" : ""}">${v === "OT" ? "OT" : "Q" + v}</button>`).join("")}</span>`;
    else if (f.t === "sm") c = `his team from <input type="number" data-i="${i}" data-k="a" value="${f.a}"> to <input type="number" data-i="${i}" data-k="b" value="${f.b}"> points`;
    else if (f.t === "ck") c = `<input type="number" min="0" max="12" data-i="${i}" data-k="a" value="${f.a}"> min or less left when the stint starts`;
    else if (f.t === "dt") c = `from <input type="date" data-i="${i}" data-k="a" value="${f.a}"> to <input type="date" data-i="${i}" data-k="b" value="${f.b}">`;
    else if (f.t === "ln") c = `at least <input type="number" min="0" data-i="${i}" data-k="a" value="${f.a}"> seconds`;
    else if (f.t === "tr") c = (f.agg === "cnt" ? `<select data-i="${i}" data-k="m">${opt(MODE, f.m)}</select> <input type="number" min="0" max="5" data-i="${i}" data-k="n" value="${f.n}"> ` : "") +
      `<select data-i="${i}" data-k="who">${opt({ m: "of his teammates", o: "of the opponents" }, f.who)}</select> <select data-i="${i}" data-k="agg">${opt({ avg: "average", cnt: "count players" }, f.agg)}</select>
      <select data-i="${i}" data-k="st">${opt(TRS, f.st)}</select> <select data-i="${i}" data-k="op">${opt({ ge: "at least", le: "at most" }, f.op)}</select>
      <input class="tv" data-i="${i}" data-k="v" value="${esc(f.v)}" placeholder="${f.st === "ht" ? "6'8" : f.st === "hapm" ? "2" : f.st === "a3" ? "5" : "36"}"> <span class="note">(that season)</span>`;
    return `<div class="sfr"><span class="fl">${FT[f.t]}</span> ${c} <button class="hx fx" data-del="${i}" title="Remove this filter">\u00d7</button></div>`; };
  $("sfb").innerHTML = Q.f.map(row).join("") + `<div class="sfr"><select id="sfadd"><option value="">+ Add filter</option>${opt(FT, "")}</select>
    <button class="btn" id="sclutch" title="Adds three filters you can edit: Q4 and OT, 5 min or less left, margin -5 to +5">+ Clutch</button>
    <label title="Leave out games in which a Combo teammate was not on his team"><input type="checkbox" id="sag" ${Q.ag !== "no" ? "checked" : ""}> Only games where every Combo teammate played</label>
    ${Q.f.length ? '<a href="#" id="sfclear">Clear filters</a>' : ""} <button class="btn" id="sreset" title="Clears filters, Combo / On / Off, sorting and hidden rows">Reset all</button></div>`;
  const go = () => { Q.pk = []; sdraw(); };
  $("sfadd").onchange = () => { const t = $("sfadd").value; if (t) { Q.f.push(FNEW[t]()); if (t === "tm" || t === "op") { fbar(); const x = $("sfb").querySelectorAll(".fadd"); x[x.length - 1].focus(); writeQ(); return; } go(); } };
  $("sclutch").onclick = () => { Q.f = Q.f.filter((f) => !["q", "ck", "sm"].includes(f.t)); Q.f.push({ t: "q", v: ["4", "OT"] }, { t: "ck", a: "5" }, { t: "sm", a: "-5", b: "5" }); go(); };
  $("sag").onchange = () => { Q.ag = $("sag").checked ? "" : "no"; go(); };
  if ($("sfclear")) $("sfclear").onclick = (e) => { e.preventDefault(); Q.f = []; go(); };
  $("sreset").onclick = () => { Object.assign(Q, { cm: [], co: [], tw: [], tx: [], on: [], off: [], f: [], ag: "", pk: [], so: "", sd: "d", hr: [], hc: [], fr: "", me: "" }); sdraw(); };
  $("sfb").querySelectorAll("[data-k]").forEach((x) => x.onchange = () => { Q.f[+x.dataset.i][x.dataset.k] = x.value; go(); });
  $("sfb").querySelectorAll("[data-qv]").forEach((b) => b.onclick = () => { const f = Q.f[+b.dataset.i], v = b.dataset.qv; f.v = f.v.includes(v) ? f.v.filter((x) => x !== v) : [...f.v, v]; go(); });
  $("sfb").querySelectorAll("[data-del]").forEach((b) => b.onclick = () => { Q.f.splice(+b.dataset.del, 1); go(); });
  $("sfb").querySelectorAll("[data-rm]").forEach((b) => b.onclick = () => { const f = Q.f[+b.dataset.i]; f.p = f.p.filter((p) => p !== +b.dataset.rm); go(); });
  $("sfb").querySelectorAll(".fadd").forEach((x) => x.onchange = () => { const f = Q.f[+x.dataset.i], o = [...$("sfl-" + f.t).options].find((y) => y.value === x.value); if (o && !f.p.includes(+o.dataset.pid)) { f.p.push(+o.dataset.pid); go(); } else x.value = ""; });
}

const fixed = (d) => Q.tw.every((p) => d.mates.includes(p)) && !Q.tx.some((p) => d.mates.includes(p)) && Q.on.every((p) => d.opps.includes(p)) && !Q.off.some((p) => d.opps.includes(p));
const combo = () => [...(Q.me ? [{ p: PID, t: "me" }] : []), ...Q.cm.map((p) => ({ p, t: "m" })), ...Q.co.map((p) => ({ p, t: "o" }))];
const keyOf = (d, C) => C.map((c) => (c.t === "me" ? (d.self0 ? "0" : "1") : (c.t === "m" ? d.mates : d.opps).includes(c.p) ? "1" : "0")).join("");
const rowLab = (k, C) => (C.length ? C.map((c, j) => `${k[j] === "1" ? "" : "no "}${lnm(c.p)}`).join(", ") : "All his stints");

function sshell() {
  if ($("srail")) return;
  $("pStints").innerHTML = `
  <div class="gspan">
    <span class="seg" id="squick"><button data-q="1">This season</button><button data-q="2">Last 2</button><button data-q="3">Last 3</button><button data-q="all">Career</button></span>
    <label>Seasons <select id="ss0"></select> to <select id="ss1"></select></label>
  </div>
  <div id="sfb" class="sfb"></div>
  <datalist id="sfl-tm"></datalist><datalist id="sfl-op"></datalist>
  <div class="sgrid">
    <div class="srail spanel" id="srail"><button class="fsb">Full screen</button>
      <div class="srh">Teammates</div>
      <div class="skey"><b>Combo</b>: split the table into with and without rows.<br><b>On</b>: keep only stints with him. <b>Off</b>: keep only stints without him.</div>
      <input id="smsearch" type="search" placeholder="Search teammates">
      <div id="smates" class="slistp"></div>
      <div class="srh">Opponents</div>
      <input id="soadd" list="solist" placeholder="+ opposing player"><datalist id="solist"></datalist>
      <div id="sopps" class="slistp"></div>
    </div>
    <div class="smain">
      <div class="ssubbar"><span class="seg" id="ssub"><button data-v="wowy">With / without</button><button data-v="find">Stint finder</button></span><div id="ssent" class="ssent"></div></div>
      <div class="spanel" id="stabp"><button class="fsb">Full screen</button><div id="scap" class="fscap"></div><div class="sbxbar"><span class="cbx">Columns ${[["par", "Par \u00b1"], ["raw", "Raw net and expected"], ["o", "Offense shot types"], ["d", "Defense shot types"]].map(([k, l]) => `<label><input type="checkbox" data-cb="${k}"> ${l}</label>`).join("")}</span>
        <label>Show <select id="sdm"><option value="chg">Value + change vs league</option><option value="only">Change vs league</option><option value="pct">Value + percentile</option></select></label>
        <label>Shots <select id="sown"><option value="">His team</option><option value="1">His own</option></select></label>
        <span class="seg" id="svw"><button data-v="">Table</button><button data-v="card">Card</button></span>
        <label><input type="checkbox" id="scl"> Color</label>
        <label title="What the small number compares each row with">Compare to <select id="sbs"></select></label>
        <label title="Hide combination rows with fewer possessions">Rows with at least <input type="number" id="smp" min="0" step="50" placeholder="0" style="width:64px"> poss</label></div><div id="stab" class="gwrap"></div></div>
      <div class="gchartbox spanel" id="schartp"><button class="fsb">Full screen</button><div class="gview"><span class="seg" id="smd"><button data-v="rows" title="His Par \u00b1 in each ticked row of the table">By combination</button><button data-v="overlap" title="His own Par \u00b1 and each Combo teammate's own Par \u00b1, in the same games">By player</button></span>
        <span class="seg" id="sx"><button data-v="date" title="His games in date order; offseasons left out">By date</button><button data-v="poss" title="Possessions played so far">By possessions</button></span><span class="gleg" id="sleg"></span></div><div id="schart" class="gchart"></div></div>
      <div class="spanel" id="slistp"><button class="fsb">Full screen</button>
        <div class="gtools"><span id="sfrom"></span><span class="note" id="scount"></span><button class="btn" id="scsv">CSV</button></div>
        <div id="slist" class="gwrap"></div></div>
    </div>
  </div>
  <details class="note gq"><summary>? What this page shows</summary><ul>
    <li>Stint: a stretch with the same ten players on the floor. His Par \u00b1 is the sum of his stints.</li>
    <li>Filters: "+ Add filter" adds a condition every stint must meet: teammates or opponents on the floor (at least, exactly or at most N of the players listed), opponent team strength (top or bottom N teams by that season's net rating, offense or defense, computed from the season's stints), quarter, score margin at the start, time left in the period, dates, stint length, and player traits on the floor: the average of his four teammates (or the five opponents), or how many of them meet a mark, on that season's 3P% (50+ attempts), 3PA per 36, 3PA share of FGA, TS%, usage %, height or HAPM. Players without enough attempts for a trait are left out of the average and do not count toward a mark. "+ Clutch" adds three editable filters (Q4 and OT, 5 min or less left, margin \u22125 to +5).</li>
    <li>Combo / On / Off: a Combo player splits the table into every on / off combination (up to 5 Combo players). On and Off apply to every row: On keeps only stints with that player on the floor, Off only stints without him.</li>
    <li>Raw net: the plain margin per 100 possessions while he was on the floor, relative to a league-average team.</li>
    <li>Expected: the margin per 100 the other nine players on the floor (his four teammates against the five opponents) would produce with a league-average player in his place, from their held-out ratings.</li>
    <li>Par \u00b1: Raw net minus Expected, with one standard error. It is what he added beyond what his teammates and opponents explain.</li>
    <li>Shot types and possessions: plain counts from the play-by-play of the same stints. Offense = his team while he is on the floor: rim attempts (4 ft or closer), other two-point attempts, three-point attempts, free-throw attempts and turnovers per 100 possessions, and OREB% (offensive rebounds per missed field goal). Defense = the same for the opponents, plus DREB% (his team's defensive rebounds per opponent miss). The small number under each value is the difference from the league average, each stint compared with its own season's league rates (so eras do not drive it). Shots: His own switches the offense columns to his own rim, mid-range, three-point and free-throw attempts and turnovers per 100 possessions on the floor, and his own offensive rebounds per team miss (league = a fifth of the league team rate). Compare to: the small number is the change from league average (default), or from the All row or one combination row you pick (for example his stints with none of the Combo players), in the same units. Show: Value + percentile gives where the change from league average ranks among all player-seasons with 800+ possessions on that end in the seasons shown. Color marks the 85th percentile or better toward the side usually linked to winning in green and the 15th or worse in red. Card view puts the statistics down the side and one column per combination. These are not adjusted for teammates or opponents; Par \u00b1 is.</li>
    <li>On \u2212 Off: with one Combo player, the difference between the "on" and "off" rows, with the standard error of the difference (the two rows treated as independent).</li>
    <li>With / without: Par \u00b1 already accounts for how good a teammate is, so a gap between "on" and "off" rows shows how the two fit together, not the teammate's own quality. Gaps smaller than about twice their standard error are within the noise.</li>
    <li>Only games where every Combo teammate played: on by default, so a row does not mix in seasons or games when a teammate was not on his team.</li>
    <li>Sorting and hiding: click a column header to sort the rows (again to reverse, a third time to restore the order); \u00d7 hides a row or a column; the "Hidden" line under the table brings each one back. Full screen enlarges a panel; Esc closes it.</li>
    <li>Chart, By combination: his Par \u00b1 so far, adding stints in order, one line per ticked row (from 250 possessions); the square is the final value with one standard error. By player: each Combo teammate's own Par \u00b1 so far next to his, in the same games (as in the paper's Jokic and Caldwell-Pope figure). By date: x is his games in date order, offseasons left out; By possessions: x is possessions played so far in that row.</li>
    <li>Stint finder: every stint that meets the filters and Combo / On / Off choices, with the ten players, the margin and the expected margin. Click a date to open the game.</li></ul></details>`;
  const re = () => { G.st.from = G.st.to = ""; Q.pk = []; sdraw(); };
  $("ss0").onchange = () => { G.st.s0 = $("ss0").value; if (G.SEA.indexOf(G.st.s1) < G.SEA.indexOf(G.st.s0)) G.st.s1 = G.st.s0; re(); };
  $("ss1").onchange = () => { G.st.s1 = $("ss1").value; if (G.SEA.indexOf(G.st.s0) > G.SEA.indexOf(G.st.s1)) G.st.s0 = G.st.s1; re(); };
  [...$("squick").children].forEach((b) => b.onclick = () => { const n = G.SEA.length, q = b.dataset.q; G.st.s1 = G.SEA[n - 1]; G.st.s0 = q === "all" ? G.SEA[0] : G.SEA[Math.max(0, n - +q)]; re(); });
  [...$("smd").children].forEach((b) => b.onclick = () => { Q.md = b.dataset.v; sdraw(); });
  $("stabp").querySelectorAll("[data-cb]").forEach((x) => x.onchange = () => { const c = CB(); x.checked ? c.add(x.dataset.cb) : c.delete(x.dataset.cb); Q.cb = [...c].join("."); sdraw(); });
  $("sdm").onchange = () => { Q.dm = $("sdm").value; sdraw(); };
  $("sown").onchange = () => { Q.ow = $("sown").value; sdraw(); };
  [...$("svw").children].forEach((b) => b.onclick = () => { Q.vw = b.dataset.v; marks(); ctable(SB.rows, SB.use, SB.C); writeQ(); });
  $("sbs").onchange = () => { Q.bs = $("sbs").value; ctable(SB.rows, SB.use, SB.C); writeQ(); };
  $("smp").onchange = () => { Q.mp = $("smp").value; ctable(SB.rows, SB.use, SB.C); writeQ(); };
  $("scl").onchange = () => { Q.cl = $("scl").checked ? "1" : "0"; sdraw(); };
  [...$("sx").children].forEach((b) => b.onclick = () => { Q.x = b.dataset.v; marks(); schart(SB.rows, SB.C); writeQ(); });
  [...$("ssub").children].forEach((b) => b.onclick = () => { Q.sub = b.dataset.v; marks(); if (Q.sub === "find") slist(); else schart(SB.rows, SB.C); writeQ(); });
  $("smsearch").oninput = () => rail(SB && SB.pool);
  $("soadd").onchange = () => { const o = [...$("solist").options].find((x) => x.value === $("soadd").value); if (o) { const p = +o.dataset.pid; if (!Q.on.includes(p) && !Q.off.includes(p) && !Q.co.includes(p)) Q.on.push(p); } $("soadd").value = ""; sdraw(); };
  $("scsv").onclick = scsv;
  $("pStints").querySelectorAll(".fsb").forEach((b) => b.onclick = () => fsToggle(b.closest(".spanel")));
  document.addEventListener("keydown", (e) => { if (e.key === "Escape") { const f = document.querySelector(".spanel.fs"); if (f) fsToggle(f); } });
}
function marks() {
  [...$("smd").children].forEach((b) => b.classList.toggle("on", b.dataset.v === Q.md));
  [...$("sx").children].forEach((b) => b.classList.toggle("on", b.dataset.v === Q.x));
  [...$("ssub").children].forEach((b) => b.classList.toggle("on", b.dataset.v === Q.sub));
  const cbs = CB(); $("stabp").querySelectorAll("[data-cb]").forEach((x) => x.checked = cbs.has(x.dataset.cb));
  $("sdm").value = Q.dm; $("sown").value = Q.ow; [...$("svw").children].forEach((b) => b.classList.toggle("on", b.dataset.v === Q.vw)); $("scl").checked = Q.cl === "1"; $("smp").value = Q.mp;
  const f = Q.sub === "find"; $("stabp").hidden = f; $("schartp").hidden = f; $("slistp").hidden = !f;
}
function fsToggle(pn) {
  const on = !pn.classList.contains("fs");
  document.querySelectorAll(".spanel.fs").forEach((x) => x.classList.remove("fs")); if (on) pn.classList.add("fs");
  document.body.classList.toggle("sfsopen", on);
  document.querySelectorAll(".spanel .fsb").forEach((b) => b.textContent = b.closest(".spanel").classList.contains("fs") ? "Close (Esc)" : "Full screen");
  if (SB) { if (pn.id === "srail") rail(SB.pool); if (pn.id === "schartp") schart(SB.rows, SB.C); }
}

let SB = null;
async function sdraw() {
  const st = G.st, n = G.SEA.length;
  if (!G.SEA.includes(st.s1)) st.s1 = G.SEA[n - 1]; if (!G.SEA.includes(st.s0)) st.s0 = st.s1;
  for (const id of ["ss0", "ss1"]) { const e = $(id); if (!e.options.length) for (const s of G.SEA) e.add(new Option(s, s)); }
  $("ss0").value = st.s0; $("ss1").value = st.s1;
  const span = spanSeasons(), quick = span.length === n && n > 3 ? "all" : span[span.length - 1] === G.SEA[n - 1] ? String(span.length) : "";
  [...$("squick").children].forEach((b) => b.classList.toggle("on", b.dataset.q === quick));
  marks(); fbar();
  ROWS = spanRows();
  const busy = Q.sub === "find" ? "slist" : "stab";
  $(busy).innerHTML = `<p class="note">Loading his stints for ${span.length > 1 ? span[0] + " to " + span[span.length - 1] : span[0]}\u2026</p>`;
  let all; try { all = (await Promise.all(span.map((s) => sidesFor(s)))).flat(); if (Q.f.some((f) => f.t === "ot")) await Promise.all(span.map(teamRanks)); if (Q.f.some((f) => f.t === "tr")) await traits(); const cb = CB(); BXO = Q.ow ? BXO_O : BXO_T;
    if (cb.has("o") || cb.has("d")) { await Promise.all(span.map(boxSeason)); if (Q.ow) await Promise.all(span.map(ownSeason)); G.pctNow = Q.dm === "pct" || Q.cl === "1" ? await pctFor(span) : null; } }
  catch (e) { $(busy).innerHTML = '<p class="note">No stint data for these seasons.</p>'; return; }
  const ord = [...ROWS].sort((a, b) => (a.date < b.date ? -1 : a.date > b.date ? 1 : a.gid - b.gid)); G.gix = new Map(ord.map((r, i) => [r.gid, i])); G.gord = ord;
  const okG = new Set(ROWS.map((r) => r.gid));
  const pool = all.filter((d) => okG.has(d.gid) && fpass(d));               // time frame + filters
  const C = combo();
  let use = pool.filter(fixed);
  if (Q.me) { const offs = (await Promise.all(span.map((s) => offSidesFor(s, all.filter((d) => d.s === s))))).flat(); use = use.concat(offs.filter((d) => okG.has(d.gid) && fpass(d) && fixed(d))); }
  if (Q.ag !== "no" && Q.cm.length) {                                         // only games where every Combo teammate was on his team
    const seen = new Map(); for (const d of all) { let s = seen.get(d.gid); if (!s) seen.set(d.gid, (s = new Set())); for (const p of d.mates) s.add(p); }
    use = use.filter((d) => { const s = seen.get(d.gid); return Q.cm.every((p) => s && s.has(p)); });
  }
  const groups = new Map(); for (const d of use) { const k = keyOf(d, C); let a = groups.get(k); if (!a) groups.set(k, (a = [])); a.push(d); }
  const rows = [...Array(1 << C.length).keys()].map((i) => { const k = C.map((_, j) => ((i >> (C.length - 1 - j)) & 1 ? "1" : "0")).join(""); const l = groups.get(k) || []; return { k, l, X: poolSides(l) }; })
    .sort((a, b) => (b.k > a.k ? 1 : b.k < a.k ? -1 : 0));
  Q.pk = Q.pk.filter((k) => rows.some((r) => r.k === k && r.X && r.X.par != null));
  if (!Q.pk.length) Q.pk = rows.filter((r) => r.X && r.X.par != null && r.X.poss >= 250 && !Q.hr.includes(r.k)).slice(0, 4).map((r) => r.k);
  SB = { all, pool, use, C, rows, okG };
  rail(pool); sentence(span, C); ctable(rows, use, C);
  if (Q.sub === "find") slist(); else await schart(rows, C);
  writeQ();
}

function rail(pool) {
  if (!pool) return;
  const sh = new Map(), so = new Map();
  for (const d of pool) { for (const p of d.mates) sh.set(p, (sh.get(p) || 0) + d.P / 2); for (const p of d.opps) so.set(p, (so.get(p) || 0) + d.P / 2); }
  const f = ($("smsearch").value || "").toLowerCase(), state = (p) => (Q.cm.includes(p) ? "c" : Q.tw.includes(p) ? "on" : Q.tx.includes(p) ? "off" : "");
  const ms = [...sh.entries()].sort((a, b) => b[1] - a[1]), mates = ms.filter(([p]) => !f || nm(p).toLowerCase().includes(f) || state(p));
  const btns = (p, s, kind) => `<span class="cbtns">${[["c", "Combo"], ["on", "On"], ["off", "Off"]].map(([v, l]) => `<button class="${s === v ? "on" : v === "c" ? "cmb" : ""}" data-p="${p}" data-v="${v}" data-kind="${kind}">${l}</button>`).join("")}</span>`;
  $("smates").innerHTML = `<div class="srow ${Q.me ? "act" : ""}"><span class="sn" title="Adds rows with ${esc(lnm(PID))} off the floor: his team's stints in the games he played">${esc(nm(PID))} <i>himself</i></span><span class="cbtns"><button class="${Q.me ? "on" : "cmb"}" id="smebtn">Combo</button></span></div>` + mates.slice(0, f || $("srail").classList.contains("fs") ? 400 : 18).map(([p, v]) => `<div class="srow ${state(p) ? "act" : ""}"><span class="sn" title="${n0(v)} possessions together">${esc(nm(p))}<i>${n0(v)}</i></span>${btns(p, state(p), "m")}</div>`).join("") || '<p class="note">No teammates.</p>';
  const ost = (p) => (Q.co.includes(p) ? "c" : Q.on.includes(p) ? "on" : Q.off.includes(p) ? "off" : "");
  const ol = [...new Set([...Q.co, ...Q.on, ...Q.off])];
  $("sopps").innerHTML = ol.map((p) => `<div class="srow act"><span class="sn">${esc(nm(p))}<i>${n0(so.get(p) || 0)}</i></span>${btns(p, ost(p), "o")}</div>`).join("");
  const os = [...so.entries()].sort((a, b) => b[1] - a[1]).slice(0, 400);
  $("solist").innerHTML = $("sfl-op").innerHTML = os.map(([p, v]) => `<option data-pid="${p}" value="${esc(nm(p))}">${n0(v)} poss faced</option>`).join("");
  $("sfl-tm").innerHTML = ms.map(([p, v]) => `<option data-pid="${p}" value="${esc(nm(p))}">${n0(v)} poss together</option>`).join("");
  $("smebtn").onclick = () => { Q.me = Q.me ? "" : "1"; if (Q.me) { const c = CB(); c.add("raw"); Q.cb = [...c].join("."); } Q.pk = []; Q.hr = []; if (/^c/.test(Q.so)) Q.so = ""; sdraw(); };
  $("srail").querySelectorAll(".cbtns button[data-p]").forEach((b) => b.onclick = () => {
    const p = +b.dataset.p, v = b.dataset.v, m = b.dataset.kind === "m", L = m ? ["cm", "tw", "tx"] : ["co", "on", "off"], cur = L.find((k) => Q[k].includes(p)), want = { c: L[0], on: L[1], off: L[2] }[v];
    for (const k of L) Q[k] = Q[k].filter((x) => x !== p);
    if (cur !== want) { if (want === L[0] && Q.cm.length + Q.co.length >= 5) { alert("Up to 5 Combo players."); } else Q[want].push(p); }
    Q.pk = []; Q.hr = []; if (/^c/.test(Q.so)) Q.so = ""; sdraw(); });
}
function sentence(span, C) {
  const L = (a) => a.map(lnm).join(", "), parts = [];
  if (Q.tw.length) parts.push(`with ${L(Q.tw)}`); const Lc = (a) => a.map((c) => (c.t === "me" ? lnm(c.p) + " on / off" : lnm(c.p))).join(", "); if (Q.tx.length) parts.push(`without ${L(Q.tx)}`);
  if (Q.on.length) parts.push(`against ${L(Q.on)}`); if (Q.off.length) parts.push(`${L(Q.off)} off the floor`);
  for (const f of Q.f) { const t = fdesc(f); if (t) parts.push(t); }
  $("ssent").innerHTML = `<b>${esc(lnm(PID))}</b> ${parts.length ? esc(parts.join(", ")) : "in all his stints"}${C.length ? `, split by ${esc(Lc(C))}` : ""} <span class="note">\u00b7 ${span.length > 1 ? span[0] + " to " + span[span.length - 1] : span[0]}</span>`;
  $("scap").innerHTML = $("ssent").innerHTML + ' <span class="note">· HAPM by LUMA Basketball Research</span>';
}
const SCOLS = [["poss", "Poss", "ps sep"], ["par", "Par \u00b1", "", "Raw net minus Expected, per 100 possessions"], ["o", "Off", "", "Par \u00b1 on offense"], ["d", "Def", "", "Par \u00b1 on defense"],
  ["act", "Raw net", "sep", "Plain on-floor margin per 100, relative to a league-average team"],
  ["exp", "Expected", "", "The margin per 100 the other nine on the floor would produce with a league-average player in his place"], ["games", "Games", "ps"]];
const GOOD = { o_rim: 1, o_mid: -1, o_r3: 1, o_fta: 1, o_tov: -1, o_orb: 1, d_rim: -1, d_mid: 1, d_r3: -1, d_fta: -1, d_tov: 1, d_drb: 1 };
const SCL = { rim: 5, mid: 5, r3: 6, fta: 4, tov: 2.5, orb: 6, drb: 5 };
const ordn = (n) => n + (n % 100 >= 11 && n % 100 <= 13 ? "th" : ["th", "st", "nd", "rd"][n % 10] || "th");
const goodPct = (k, l) => { const q = pctOf(k, l); return q == null ? null : GOOD[k] > 0 ? q : 100 - q; };
const tone = (k, l) => { if (Q.cl !== "1") return ""; const g = goodPct(k, l); return g == null ? "" : g >= 85 ? "pg" : g <= 15 ? "pb" : ""; };
function ctable(rows, use, C) {
  const cb = CB(), bx = (L) => L.map((c, i) => [c[0], c[1], i ? "bx" : "bx sep", c[2] + (Q.dm === "pct" ? "; small number = percentile among player-seasons (800+ possessions on that end), vs league" : Q.dm === "only" ? "; shown as the difference from the league average that season" : "; small number = minus the league average that season")]);
  const bxc = [...(cb.has("o") ? bx(BXO) : []), ...(cb.has("d") ? bx(BXD) : [])];
  const base = SCOLS.filter((c) => c[0] === "poss" || c[0] === "games" || (cb.has("par") && ["par", "o", "d"].includes(c[0])) || (cb.has("raw") && ["act", "exp"].includes(c[0])));
  const T = poolSides(use.filter((d) => !d.self0)), hc = new Set(Q.hc), cols = [...base.filter((c) => c[0] !== "games"), ...bxc, ...base.filter((c) => c[0] === "games")].filter((c) => !hc.has(c[0])), ci = (i) => COL[i % COL.length];
  if (Q.bs && Q.bs !== "all" && !rows.some((r) => r.k === Q.bs && r.X)) Q.bs = "";
  const BX = Q.bs === "all" ? T : Q.bs ? rows.find((r) => r.k === Q.bs).X : null, bname = Q.bs === "all" ? "All" : Q.bs ? rowLab(Q.bs, C) : "";
  const vsB = (X, k, v) => (BX && X !== BX && !X.diff && BX[k] != null && v != null ? v - BX[k] : null);
  const cell = (X, c) => { const v = X ? X[c[0]] : null; if (v == null) return `<td class="${c[2]}"></td>`;
    const isB = BX && X === BX, bd = vsB(X, c[0], v), bl = bd == null ? (isB && c[0] !== "poss" && c[0] !== "games" ? '<span class="p sb">base</span>' : "") : `<span class="p" title="Change from the base row (${esc(bname)})">${f1(bd, 1)}</span>`;
    if (c[0] === "par") return `<td class="v main ${c[2]}" style="background:${parBg(v, 15)}"><span class="x">${f1(v, 1)}</span>${X.se != null && isFinite(X.se) ? `<span class="p">\u00b1${X.se.toFixed(1)}</span>` : ""}${BX ? bl.replace('class="p', 'class="p pv') : ""}</td>`;
    if (BX && ["o", "d", "act", "exp"].includes(c[0]) && !X.diff) return `<td class="${c[2]} bx2"><span class="x">${f1(v, 1)}</span>${bl}</td>`;
    if (/^[od]_/.test(c[0]) && BX && !X.diff) { const q = pctOf(c[0], X[c[0] + "_lg"]), tip = `${c[1]}: ${v.toFixed(1)}${/orb|drb/.test(c[0]) ? "%" : " per 100"} · base (${bname}) ${BX[c[0]] == null ? "-" : BX[c[0]].toFixed(1)}${bd == null ? "" : " · change " + f1(bd, 1)} · ${n0(X.poss)} poss`;
      if (Q.dm === "only") return `<td class="${c[2]}" title="${esc(tip)}">${bd == null ? (isB ? '<span class="sb">base</span>' : "") : f1(bd, 1)}</td>`;
      const small = Q.dm === "pct" ? (q == null ? "" : `<span class="p">${ordn(q)}</span>`) : bl;
      return `<td class="${c[2]}" title="${esc(tip)}"><span class="x">${v.toFixed(1)}</span>${small}</td>`; }
    if (/^[od]_/.test(c[0])) { const l = X[c[0] + "_lg"];
      if (X.diff) return `<td class="${c[2]}" title="${esc(c[1])}: on minus off">${f1(v, 1)}</td>`;
      const q = pctOf(c[0], l), u = /orb|drb/.test(c[0]) ? "%" : " per 100", tip = `${c[1]}: ${v.toFixed(1)}${u} \u00b7 league ${(v - l).toFixed(1)} \u00b7 change ${f1(l, 1)}${q == null ? "" : ` \u00b7 ${ordn(q)} percentile among player-seasons`} \u00b7 ${n0(X.poss)} poss`, tn = tone(c[0], l);
      if (Q.dm === "only") return `<td class="${c[2]}" title="${esc(tip)}"><span class="${tn}">${l == null ? "" : f1(l, 1)}</span></td>`;
      const small = Q.dm === "pct" ? (q == null ? "" : ordn(q)) : l == null ? "" : f1(l, 1);
      return `<td class="${c[2]}" title="${esc(tip)}"><span class="x">${v.toFixed(1)}</span>${small ? `<span class="p ${tn}">${small}</span>` : ""}</td>`; }
    return `<td class="${c[2]}">${c[0] === "poss" ? n0(v) : c[0] === "games" ? v : f1(v, 1)}</td>`; };
  const arrow = (k) => (Q.so === k ? (Q.sd === "a" ? " \u25b4" : " \u25be") : "");
  const head = `<tr><th></th>${C.map((c, j) => `<th class="cp sth" data-so="c${j}" title="${esc(nm(c.p))}${c.t === "o" ? " (opponent)" : c.t === "me" ? " himself" : ""}: click to sort">${esc(lnm(c.p))}${c.t === "o" ? ' <span class="note">opp</span>' : c.t === "me" ? ' <span class="note">himself</span>' : ""}${arrow("c" + j)}</th>`).join("")}` +
    cols.map((c) => `<th class="${c[2]} sth" data-so="${c[0]}" title="${c[3] ? esc(c[3]) + ". " : ""}Click to sort">${c[1]}${arrow(c[0])}<button class="hx" data-hc="${c[0]}" title="Hide this column">\u00d7</button></th>`).join("") + `</tr>`;
  $("sbs").innerHTML = `<option value="">League average</option><option value="all" ${Q.bs === "all" ? "selected" : ""}>All row</option>` + (C.length ? rows.filter((r) => r.X).map((r) => `<option value="${r.k}" ${r.k === Q.bs ? "selected" : ""}>${esc(rowLab(r.k, C))}</option>`).join("") : "");
  const mpv = +Q.mp || 0, keep = (r) => !Q.hr.includes(r.k) && (!mpv || (r.X && r.X.poss >= mpv));
  let body = C.length ? rows.filter(keep) : [];
  if (Q.so) { const j = Q.so[0] === "c" ? +Q.so.slice(1) : -1, dir = Q.sd === "a" ? 1 : -1;
    const v = (r) => (j >= 0 ? +r.k[j] : r.X ? r.X[Q.so] : null);
    body = [...body].sort((a, b) => { const x = v(a), y = v(b); if (x == null) return 1; if (y == null) return -1; return (x - y) * dir; }); }
  const tr = (r) => { const pk = Q.pk.indexOf(r.k);
    return `<tr class="${r.X && r.X.poss < 250 ? "n0" : ""}"><td class="nw"><input type="checkbox" class="spk" data-k="${r.k}" ${pk >= 0 ? "checked" : ""} ${r.X && r.X.par != null ? "" : 'disabled title="No Par \u00b1 with him off the floor"'}>${pk >= 0 ? `<span class="sw" style="background:${ci(pk)}"></span>` : ""}<button class="hx" data-hr="${r.k}" title="Hide this row">\u00d7</button></td>` +
      C.map((c, j) => `<td class="oo">${r.k[j] === "1" ? '<span class="d1">\u25cf on</span>' : '<span class="d0">\u25cb off</span>'}</td>`).join("") + cols.map((c) => cell(r.X, c)).join("") + `</tr>`; };
  let diff = "";
  if (C.length === 1) { const a = rows.find((r) => r.k === "1"), b = rows.find((r) => r.k === "0");
    if (a && b && a.X && b.X) { const D = { se: a.X.se != null && b.X.se != null ? Math.hypot(a.X.se, b.X.se) : null, diff: true }; for (const k of ["par", "o", "d", "act", "exp", ...bxc.map((c) => c[0])]) D[k] = a.X[k] != null && b.X[k] != null ? a.X[k] - b.X[k] : null;
      diff = `<tr class="sdiff"><td></td><td class="oo"><b>On \u2212 Off</b></td>${cols.map((c) => cell(D, c)).join("")}</tr>`; } }
  const hr = Q.hr.filter((k) => rows.some((r) => r.k === k)), hl = [...hr.map((k) => `<a href="#" data-uh="r${k}" title="Show this row again">${esc(rowLab(k, C))}</a>`), ...Q.hc.map((k) => `<a href="#" data-uh="c${k}" title="Show this column again">${esc(([...SCOLS, ...BXO, ...BXD].find((c) => c[0] === k) || [k, k])[1])} column</a>`)];
  if (Q.vw === "card") {
    const D = diff ? (() => { const a = rows.find((r) => r.k === "1"), b = rows.find((r) => r.k === "0"), o = { se: a.X.se != null && b.X.se != null ? Math.hypot(a.X.se, b.X.se) : null, diff: true };
      for (const k of ["par", "o", "d", "act", "exp", ...bxc.map((c) => c[0])]) o[k] = a.X[k] != null && b.X[k] != null ? a.X[k] - b.X[k] : null; return o; })() : null;
    const shown = C.length ? rows.filter(keep) : [], hd = (k) => C.map((c, j) => `${k[j] === "1" ? "" : "no "}${esc(lnm(c.p))}`).join("<br>");
    const colsC = [{ X: T, h: `<b>All</b>${Q.me ? '<br><span class="note">him on</span>' : ""}` }, ...shown.map((r) => ({ X: r.X, h: hd(r.k) })), ...(D ? [{ X: D, h: "<b>On \u2212 Off</b>" }] : [])];
    $("stab").innerHTML = `<table class="gl scomb scard"><thead><tr><th></th>${colsC.map((c) => `<th>${c.h}</th>`).join("")}</tr></thead><tbody>` +
      cols.map((c) => `<tr><th class="l" title="${esc(c[3] || "")}">${c[1]}</th>${colsC.map((x) => cell(x.X, c).replace(/class="([^"]*)\bsep\b/, 'class="$1')).join("")}</tr>`).join("") + `</tbody></table>` +
      `<p class="note">Card view: one column per combination. Switch to Table to tick rows for the chart, sort or hide.</p>`;
    return;
  }
  $("stab").innerHTML = `<table class="gl scomb"><thead>${head}</thead><tbody><tr class="gsrow"><td class="nw"><b>All</b>${Q.me ? ' <span class="note">him on</span>' : ""}</td>${C.map(() => "<td></td>").join("")}${cols.map((c) => cell(T, c)).join("")}</tr>${body.map(tr).join("")}${diff}</tbody></table>` +
    `<p class="note">${C.length ? "Tick rows to draw them below. Gray rows: under 250 possessions." + (Q.me ? ` Rows with ${esc(lnm(PID))} off: his team in the games he played; no Par \u00b1 (he is not on the floor).` : "") : "Click Combo next to a teammate (or next to his own name) to split this into on and off rows."}${bxc.length && Q.cl === "1" ? " Color: green = 85th percentile or better toward the side usually linked to winning (more rim attempts, threes, free throws and rebounds, fewer mid-range shots and turnovers; the reverse for opponents); red = 15th or worse." : ""}</p>` +
    (hl.length ? `<p class="note shid">Hidden (click to show): ${hl.join(" \u00b7 ")}${hl.length > 1 ? ' \u00b7 <a href="#" data-uh="all">show all</a>' : ""}</p>` : "");
  const redo = () => { ctable(rows, use, C); writeQ(); }, full = () => { ctable(rows, use, C); if (Q.sub === "find") slist(); else schart(rows, C); writeQ(); };
  $("stab").querySelectorAll(".spk").forEach((x) => x.onchange = () => { const k = x.dataset.k; Q.pk = x.checked ? [...Q.pk, k] : Q.pk.filter((y) => y !== k); full(); });
  $("stab").querySelectorAll("th.sth").forEach((h) => h.onclick = (e) => { if (e.target.closest(".hx")) return; const k = h.dataset.so;
    if (Q.so !== k) { Q.so = k; Q.sd = "d"; } else if (Q.sd === "d") Q.sd = "a"; else { Q.so = ""; Q.sd = "d"; } redo(); });
  $("stab").querySelectorAll(".hx").forEach((x) => x.onclick = (e) => { e.stopPropagation();
    if (x.dataset.hc) { Q.hc = [...Q.hc, x.dataset.hc]; if (Q.so === x.dataset.hc) Q.so = ""; redo(); }
    else { const k = x.dataset.hr; Q.hr = [...Q.hr, k]; if (Q.pk.includes(k)) { Q.pk = Q.pk.filter((y) => y !== k); full(); } else redo(); } });
  $("stab").querySelectorAll("[data-uh]").forEach((a) => a.onclick = (e) => { e.preventDefault(); const u = a.dataset.uh;
    if (u === "all") { Q.hr = []; Q.hc = []; } else if (u[0] === "r") Q.hr = Q.hr.filter((k) => k !== u.slice(1)); else Q.hc = Q.hc.filter((k) => k !== u.slice(1)); redo(); });
}
// running Par ±: by possessions (a point every few stints) or by date (a point after each of his games, x = game number in the frame)
function runLine(list) {
  const out = [], byDate = Q.x === "date"; let Wo = 0, Ro = 0, Wd = 0, Rd = 0; const step = Math.max(1, Math.floor(list.length / 500));
  list.forEach((d, i) => { if (d.off) { Wo += d.P; Ro += d.P * (d.y - d.e); } else { Wd += d.P; Rd += d.P * (d.e - d.y); }
    const poss = (Wo + Wd) / 2; if (poss < MINP || !(Wo > 0) || !(Wd > 0)) return; const endG = i === list.length - 1 || list[i + 1].gid !== d.gid;
    if (byDate ? endG : i % step === 0 || i === list.length - 1) out.push({ x: byDate ? G.gix.get(d.gid) + 1 : poss, y: Ro / Wo + Rd / Wd }); });
  return out;
}
async function schart(rows, C) {
  const box = $("schart"); box.innerHTML = ""; let lines = [];
  if (Q.md === "overlap") {
    const span = spanSeasons(), ok = SB.okG, who = [PID, ...Q.cm];
    const L = await Promise.all(who.map(async (p) => (await Promise.all(span.map((s) => sidesFor(s, p)))).flat().filter((d) => ok.has(d.gid) && fpass(d))));
    lines = who.map((p, i) => ({ n: nm(p), c: COL[i % COL.length], pts: runLine(L[i]), fin: poolSides(L[i]) }));
    $("sleg").innerHTML = lines.map((s) => `<span class="lg-line" style="background:${s.c}"></span> ${esc(s.n)}`).join(" &nbsp; ") + `<span class="ghow">Each player's own Par \u00b1 so far, in the games shown${Q.cm.length ? "" : " (pick Combo teammates to add their lines)"}; from 250 possessions; square = final value \u00b1 1 SE.</span>`;
  } else {
    const pick = Q.pk.map((k) => rows.find((r) => r.k === k)).filter((r) => r && r.X && r.X.par != null);
    lines = (C.length ? pick : [{ k: "", l: SB.use }]).map((r, i) => ({ n: rowLab(r.k, C), c: COL[i % COL.length], pts: runLine(r.l), fin: poolSides(r.l) }));
    $("sleg").innerHTML = lines.map((s) => `<span class="lg-line" style="background:${s.c}"></span> ${esc(s.n)}`).join(" &nbsp; ") + `<span class="ghow">His Par \u00b1 so far in each ticked row, adding stints in order (from 250 possessions); square = final value \u00b1 1 SE.</span>`;
  }
  const small = lines.filter((s) => !s.pts.length); lines = lines.filter((s) => s.pts.length);
  if (small.length) $("sleg").innerHTML += `<span class="ghow">Not drawn (under 250 possessions): ${small.map((s) => esc(s.n)).join("; ")}.</span>`;
  if (!lines.length) { box.innerHTML = '<p class="note">Not enough possessions to draw (250 needed).</p>'; return; }
  const byDate = Q.x === "date", W = Math.max(320, box.clientWidth || 900), H = box.closest(".fs") ? Math.max(320, innerHeight - 150) : 270, m = { l: 44, r: 120, t: 14, b: 34 };
  const xmax = byDate ? G.gord.length : Math.max(...lines.map((s) => s.pts[s.pts.length - 1].x)), ys = lines.flatMap((s) => [...s.pts.slice(Math.floor(s.pts.length * 0.03)).map((p) => p.y), s.fin ? s.fin.par - s.fin.se : 0, s.fin ? s.fin.par + s.fin.se : 0]);
  let lo = Math.min(0, ...ys), hi = Math.max(0, ...ys); const sp = hi - lo, stp = sp > 40 ? 10 : sp > 16 ? 5 : 2; lo = Math.floor(lo / stp) * stp; hi = Math.ceil(hi / stp) * stp;
  const X = (x) => m.l + x / xmax * (W - m.l - m.r), Y = (v) => m.t + (hi - Math.max(lo, Math.min(hi, v))) / (hi - lo) * (H - m.t - m.b);
  const svg = el("svg", { width: W, height: H, class: "gsvg" }, box);
  for (let v = lo; v <= hi + 1e-9; v += stp) { el("line", { x1: m.l, x2: W - m.r, y1: Y(v), y2: Y(v), class: v === 0 ? "gz" : "gl0" }, svg); el("text", { x: m.l - 8, y: Y(v) + 4, "text-anchor": "end", class: "gt" }, svg).textContent = v > 0 ? "+" + v : v === 0 ? "0" : "\u2212" + Math.abs(v); }
  if (byDate) {
    const O = G.gord, multi = new Set(O.map((r) => r.s)).size > 1; let ls = null, lm = null, lastX = -1e9;
    O.forEach((r, i) => { const mo = r.date.slice(0, 7), x = X(i);
      if (r.s !== ls) { if (ls) el("line", { x1: x, x2: x, y1: m.t, y2: H - m.b, class: "gl0" }, svg); if (multi && x - lastX > 44) { el("text", { x: x + 2, y: H - 18, class: "gt" }, svg).textContent = r.s; lastX = x; } ls = r.s; }
      if (!multi && mo !== lm && x - lastX > 30) { el("text", { x, y: H - 18, "text-anchor": "start", class: "gt" }, svg).textContent = MON[+mo.slice(5) - 1]; lastX = x; }
      lm = mo; });
    el("text", { x: (m.l + W - m.r) / 2, y: H - 4, "text-anchor": "middle", class: "gt" }, svg).textContent = "his games in date order (offseasons left out)";
  } else {
    const xt = [250, 500, 1000, 2000, 5000, 10000, 20000].find((s) => xmax / s <= 6) || 50000;
    for (let x = 0; x <= xmax; x += xt) el("text", { x: X(x), y: H - 18, "text-anchor": "middle", class: "gt" }, svg).textContent = x.toLocaleString();
    el("text", { x: (m.l + W - m.r) / 2, y: H - 4, "text-anchor": "middle", class: "gt" }, svg).textContent = "possessions played so far";
  }
  const ends = [];
  for (const s of lines) {
    const xy = s.pts.map((p) => [X(p.x), Y(p.y)]);
    el("path", { d: byDate ? "M" + xy.map((p) => p[0].toFixed(1) + "," + p[1].toFixed(1)).join("L") : smooth(xy), class: "sline", stroke: s.c }, svg);
    if (s.fin) { const xe = X(s.pts[s.pts.length - 1].x) + 10; el("line", { x1: xe, x2: xe, y1: Y(s.fin.par - s.fin.se), y2: Y(s.fin.par + s.fin.se), stroke: s.c, "stroke-width": 1.4 }, svg);
      el("rect", { x: xe - 4, y: Y(s.fin.par) - 4, width: 8, height: 8, class: "ssq", stroke: s.c }, svg); ends.push({ x: xe, y: Y(s.fin.par), t: `${f1(s.fin.par, 1)} \u00b1${s.fin.se.toFixed(1)}`, c: s.c }); }
  }
  ends.sort((a, b) => a.y - b.y); for (let i = 1; i < ends.length; i++) if (ends[i].y - ends[i - 1].y < 13 && Math.abs(ends[i].x - ends[i - 1].x) < 90) ends[i].y = ends[i - 1].y + 13;
  for (const e of ends) el("text", { x: e.x + 8, y: e.y + 4, class: "stx", fill: e.c }, svg).textContent = e.t;
}
// Stint finder: the stints behind the table (all rows, or one row), same filters; no free-text search
function stintRows(list) {
  const m = new Map();
  for (const d of list) { const k = d.gid + ":" + d.el; let r = m.get(k);
    if (!r) m.set(k, (r = { d, poss: 0, act: 0, exp: d.self0 ? NaN : 0 })); r.poss += d.P / 2; const sg = d.off ? 1 : -1; r.act += sg * d.y * d.P / 100; r.exp += sg * d.e * d.P / 100; }
  return [...m.values()].sort((a, b) => (a.d.date < b.d.date ? 1 : a.d.date > b.d.date ? -1 : b.d.el - a.d.el));
}
function shownStints() {
  if (!SB) return []; const r = SB.C.length && Q.fr ? SB.rows.find((x) => x.k === Q.fr) : null;
  return stintRows(r ? r.l : SB.use.filter((d) => !d.self0));
}
function slist() {
  if (!SB) return;
  const C = SB.C; if (Q.fr && !SB.rows.some((r) => r.k === Q.fr)) Q.fr = "";
  $("sfrom").innerHTML = C.length ? `<label>Rows <select id="sfr"><option value="">All rows</option>${SB.rows.filter((r) => r.X).map((r) => `<option value="${r.k}" ${r.k === Q.fr ? "selected" : ""}>${esc(rowLab(r.k, C))}</option>`).join("")}</select></label>` : "";
  if ($("sfr")) $("sfr").onchange = () => { Q.fr = $("sfr").value; slist(); writeQ(); };
  const R = shownStints(), LIM = 300, more = R.length > LIM && !G.sAll;
  const tot = R.reduce((a, r) => ({ p: a.p + r.poss, act: a.act + r.act, exp: a.exp + r.exp }), { p: 0, act: 0, exp: 0 });
  $("scount").textContent = `${R.length.toLocaleString()} stints \u00b7 ${n0(tot.p)} poss \u00b7 margin ${f1(tot.act, 1)} vs expected ${f1(tot.exp, 1)} = Par ${f1(tot.act - tot.exp, 1)} pts`;
  $("slist").innerHTML = `<table class="gl gst"><thead><tr><th class="l">Date</th><th class="l">Opp</th><th class="l">Start</th><th>Length</th><th>Lead</th><th class="l">With him</th><th class="l">Against</th><th class="ps">Poss</th><th>Margin</th><th>Expected</th><th>Par</th></tr></thead><tbody>` +
    (more ? R.slice(0, LIM) : R).map((r) => { const d = r.d, c = clock(d.el), p = r.act - r.exp;
      return `<tr><td class="l" data-v="${d.date}"><a href="#" class="sgo" data-g="${d.gid}">${sdate(d.date)} <span class="yr">${d.date.slice(0, 4)}</span></a></td><td class="l">${d.home ? "vs" : "@"} ${esc(d.opp)}</td><td class="l">${c.lab} ${c.clk}</td><td>${mmss(d.secs)}</td><td>${f1(d.lead, 0) || "0"}</td>` +
        `<td class="l">${d.mates.map(plink).join(", ")}</td><td class="l">${d.opps.map(plink).join(", ")}</td><td class="ps">${r.poss.toFixed(1)}</td><td>${f1(r.act, 1)}</td><td>${f1(r.exp, 1)}</td><td class="v" style="background:${parBg(p, 6)}">${f1(p, 1)}</td></tr>`; }).join("") +
    "</tbody></table>" + (more ? `<button class="btn gmore" id="smore">Show all ${R.length.toLocaleString()} stints</button>` : "") +
    `<p class="note">Margin and expected are in points, relative to a league-average team; Par = margin minus expected. Lead = his team's margin when the stint started. Click a header to sort, a date to open that game in the Games tab.</p>`;
  if (more) $("smore").onclick = () => { G.sAll = true; slist(); };
  sortable($("slist").querySelector("table"));
  $("slist").querySelectorAll(".sgo").forEach((a) => a.onclick = (e) => { e.preventDefault(); G.st.g = a.dataset.g; S.tab = "games"; history.replaceState(null, "", "#" + new URLSearchParams({ t: "games", s0: G.st.s0, s1: G.st.s1, g: a.dataset.g }).toString()); render(); });
}
function scsv() {
  const R = shownStints();
  const lines = [["Season", "Date", "Game ID", "Opp", "Home", "Period", "Start (s into game)", "Length (s)", "Lead", "With him", "Against", "Poss", "Margin (pts)", "Expected (pts)", "Par (pts)"].join(","),
    ...R.map((r) => { const d = r.d; return [d.s, d.date, d.gid, d.opp, d.home ? 1 : 0, d.per, d.el, d.secs, d.lead, `"${d.mates.map(nm).join("; ")}"`, `"${d.opps.map(nm).join("; ")}"`, r.poss.toFixed(2), r.act.toFixed(2), r.exp.toFixed(2), (r.act - r.exp).toFixed(2)].join(","); })];
  const a = document.createElement("a"); a.href = URL.createObjectURL(new Blob([lines.join("\n") + "\n# Par \u00b1 / HAPM stints: LUMA Basketball Research (hapm.github.lumahoops.org).\n"], { type: "text/csv" }));
  a.download = `${($("name").textContent || "player").trim().toLowerCase().replace(/[^a-z0-9]+/g, "-")}_stints.csv`; a.click();
}
window.stintsTab = async function () {
  sshell();
  if (!G.ready) { readHash(); G.ready = true; }
  if (!G.qready) { readQ(); G.qready = true; }
  try { await load(); } catch (e) { $("stab").innerHTML = '<p class="note">No data for this player yet.</p>'; return; }
  sdraw();
};

// ---------------------------------------------------------------- entry (called by player.html render())
window.gamesTab = async function () {
  shell();
  if (!G.ready) { readHash(); G.ready = true; }
  try { await load(); } catch (e) { $("games").innerHTML = '<p class="note">No game log for this player yet.</p>'; return; }
  draw();
};
window.addEventListener("resize", () => { if (G.L && S.tab === "games") { clearTimeout(G.rz); G.rz = setTimeout(() => { chart(); chartMark(filtered(ROWS)); }, 150); } });
})();
