/* Usage counts for this site (page views, time on page, scroll depth, clicks, controls), sent to LUMA Basketball
   Research. No cookies; two random ids in localStorage. Nothing typed is sent except player names added in Compare. */
(function () {
  var URL_ = 'https://lumahoops.org/api/luma/hapm-track';
  var IDLE = 30 * 60 * 1000;
  var ls = (function () { try { localStorage.setItem('hapm_t', '1'); localStorage.removeItem('hapm_t'); return localStorage; } catch (e) { return null; } })();
  function rid() { return 'hapm-' + ((window.crypto && crypto.randomUUID) ? crypto.randomUUID() : (Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 12))); }
  function get(k) { return ls ? ls.getItem(k) : null; } function set(k, v) { if (ls) ls.setItem(k, v); }
  var vid = get('hapm_vid'); if (!vid) { vid = rid(); set('hapm_vid', vid); }
  var mem = null;
  function sid() {
    var now = Date.now(), s = get('hapm_sid') || mem, t = +(get('hapm_sid_ts') || 0);
    if (!s || !t || now - t > IDLE) { s = rid(); set('hapm_sid', s); }
    mem = s; set('hapm_sid_ts', String(now)); return s;
  }
  var refExt = (function () { try { var r = document.referrer; return r && new URL(r).host !== location.host ? r : ''; } catch (e) { return ''; } })();
  function send(e, p) {
    var b = JSON.stringify({ sid: sid(), vid: vid, e: e, path: location.pathname, ref: refExt || null, p: p || {} });
    try {
      if (navigator.sendBeacon && navigator.sendBeacon(URL_, new Blob([b], { type: 'text/plain' }))) return;
    } catch (x) { /* fall through */ }
    try { fetch(URL_, { method: 'POST', body: b, keepalive: true, mode: 'no-cors', headers: { 'content-type': 'text/plain' } }); } catch (x) { /* best-effort */ }
  }
  function txt(el) { return ((el && (el.getAttribute('aria-label') || el.textContent)) || '').replace(/\s+/g, ' ').trim().slice(0, 60); }
  var theme = function () { return document.documentElement.dataset.theme === 'graphite' ? 'graphite' : 'light'; };

  // page view
  var qs = location.search.slice(0, 120);
  // tab and subtab when the page opens from a link (#t=stints&sub=find); tab clicks after that are counted as buttons
  var hq = (function () { try { return new URLSearchParams(location.hash.slice(1)); } catch (e) { return new URLSearchParams(''); } })();
  send('hapm_page_view', { title: document.title.slice(0, 120), qs: qs || undefined, theme: theme(),
    tab: (hq.get('t') || '').slice(0, 20) || undefined, sub: (hq.get('sub') || '').slice(0, 20) || undefined,
    entry: refExt ? 'external' : (document.referrer ? 'internal' : 'direct'), vw: window.innerWidth || 0 });

  // active time: counts only while the tab is visible; sent when the page is hidden or left (and every 60 s of activity)
  var active = 0, since = document.visibilityState === 'visible' ? Date.now() : 0, t0 = Date.now(), maxDepth = 0, lastSent = 0;
  function tick() { if (since) { active += Date.now() - since; since = document.visibilityState === 'visible' ? Date.now() : 0; } }
  function dwell(reason) {
    tick(); var s = Math.round(active / 1000);
    if (s === lastSent && reason !== 'leave') return; lastSent = s;
    send('hapm_dwell', { active_s: s, total_s: Math.round((Date.now() - t0) / 1000), depth: maxDepth, reason: reason });
  }
  document.addEventListener('visibilitychange', function () {
    if (document.visibilityState === 'hidden') dwell('hide'); else since = Date.now();
  });
  window.addEventListener('pagehide', function () { dwell('leave'); });
  setInterval(function () { if (document.visibilityState === 'visible') dwell('beat'); }, 60000);

  // scroll depth: 25 / 50 / 75 / 100 %, once each
  var marks = [25, 50, 75, 100];
  window.addEventListener('scroll', function () {
    var h = document.documentElement, max = h.scrollHeight - h.clientHeight; if (max <= 0) return;
    var d = Math.round((h.scrollTop || document.body.scrollTop) / max * 100); if (d > maxDepth) maxDepth = d;
    while (marks.length && d >= marks[0]) send('hapm_scroll_depth', { depth: marks.shift() });
  }, { passive: true });

  // clicks: links (where to), table headers (sorting), buttons
  document.addEventListener('click', function (ev) {
    var a = ev.target.closest && ev.target.closest('a[href]');
    if (a) {
      var u; try { u = new URL(a.href, location.href); } catch (x) { return; }
      var kind = u.host === location.host ? (u.pathname === location.pathname && u.hash ? 'anchor' : 'internal') : (/(^|\.)lumahoops\.org$/.test(u.hostname) ? 'luma' : 'outbound');
      send('hapm_click', { kind: kind, to: (u.host === location.host ? '' : u.host) + u.pathname.slice(0, 100), text: txt(a), cls: (a.className || '').toString().slice(0, 30) || undefined });
      return;
    }
    var th = ev.target.closest && ev.target.closest('th');
    if (th) { send('hapm_action', { kind: 'sort', col: th.getAttribute('data-k') || txt(th) }); return; }
    var b = ev.target.closest && ev.target.closest('button');
    if (b) send('hapm_action', { kind: 'button', what: txt(b), id: b.id || (b.parentNode && b.parentNode.id) || undefined });
  }, true);

  // controls: selects / checkboxes (season, team, position, variant, compare options); the Compare "add a player" box
  document.addEventListener('change', function (ev) {
    var el = ev.target; if (!el || !el.tagName) return;
    var name = el.id || el.getAttribute('data-col') || el.getAttribute('data-k') || el.name || el.tagName.toLowerCase();
    var v = el.type === 'checkbox' ? (el.checked ? 'on' : 'off') : String(el.value || '').slice(0, 60);
    send('hapm_action', { kind: el.type === 'checkbox' ? 'toggle' : el.tagName === 'SELECT' ? 'select' : 'input', what: name.slice(0, 30), value: v });
  }, true);

  // explainer drawers ("What is HAPM?", "How HAPM works", ...) and the "?" tooltip
  document.addEventListener('toggle', function (ev) {
    var d = ev.target; if (!d || d.tagName !== 'DETAILS') return;
    send('hapm_action', { kind: d.open ? 'open' : 'close', what: txt(d.querySelector('summary')) });
  }, true);
  var tipSeen = false;
  function tip(ev) { if (!tipSeen && ev.target.closest && ev.target.closest('.tip')) { tipSeen = true; send('hapm_action', { kind: 'tip' }); } }
  document.addEventListener('mouseover', tip, true); document.addEventListener('focusin', tip, true);
})();
