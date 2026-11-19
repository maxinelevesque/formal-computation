/* The reducer of "Atoms and Probes" as it was before the essay used ski.js (essay blob 1356f7b,
   lines 875-950), kept verbatim so that test.js can compare ski.js with it. Not used by the essay. */
'use strict';
  /* ---------- reducer ---------- */
  var A = function (n) { return { k: 'a', n: n }; };
  var App = function (f, x) { return { k: 'p', f: f, x: x }; };
  function parse(s) {
    var toks = s.match(/[()]|[^\s()]+/g) || [], i = 0;
    function seq() {
      var cur = null, t;
      while (i < toks.length && toks[i] !== ')') {
        if (toks[i] === '(') { i++; t = seq(); i++; } else { t = A(toks[i]); i++; }
        cur = cur ? App(cur, t) : t;
      }
      return cur;
    }
    return seq();
  }
  function plain(t) {
    if (t.k === 'a') return t.n;
    return plain(t.f) + ' ' + (t.x.k === 'p' ? '(' + plain(t.x) + ')' : plain(t.x));
  }
  function isOmegaHalf(t) { return t.k === 'p' && plain(t) === 'S I I'; }
  // printed form with ω for S I I; marks the redex node r when given
  function pretty(t, r, html) {
    function go(u) {
      var s;
      if (isOmegaHalf(u)) s = 'ω';
      else if (u.k === 'a') s = u.n;
      else {
        var xs = go(u.x);
        s = go(u.f) + ' ' + ((u.x.k === 'p' && !isOmegaHalf(u.x)) ? '(' + xs + ')' : xs);
      }
      return (html && u === r) ? '<mark>' + s + '</mark>' : s;
    }
    return go(t);
  }
  function spine(t) {
    var args = [], apps = [];
    while (t.k === 'p') { args.unshift(t.x); apps.unshift(t); t = t.f; }
    return { head: t, args: args, apps: apps };
  }
  function need(h) { return h.n === 'I' ? 1 : h.n === 'K' ? 2 : h.n === 'S' ? 3 : 0; }
  // every redex of t, the head redex first and then those inside the arguments, left to right
  function redexes(t) {
    var out = [];
    (function go(u) {
      if (u.k === 'a') return;
      var sp = spine(u), n = need(sp.head);
      if (n && sp.args.length >= n) out.push(sp.apps[n - 1]);
      sp.args.forEach(go);
    })(t);
    return out;
  }
  function redexOuter(t) { return redexes(t)[0] || null; }
  function redexInner(t) {
    if (t.k === 'a') return null;
    var sp = spine(t), n = need(sp.head);
    for (var i = 0; i < sp.args.length; i++) { var r = redexInner(sp.args[i]); if (r) return r; }
    if (n && sp.args.length >= n) return sp.apps[n - 1];
    return null;
  }
  function contractAt(t, r) {
    if (t === r) {
      var sp = spine(t), a = sp.args;
      if (sp.head.n === 'S') return App(App(a[0], a[2]), App(a[1], a[2]));
      return a[0];
    }
    if (t.k === 'a') return t;
    var f = contractAt(t.f, r), x = contractAt(t.x, r);
    return (f === t.f && x === t.x) ? t : App(f, x);
  }
  function ruleOf(r) { return 'the ' + spine(r).head.n + '-rule'; }
  function runOuter(t) {
    var seq = [t];
    for (var i = 0; i < 40; i++) { var r = redexOuter(t); if (!r) break; t = contractAt(t, r); seq.push(t); }
    return seq;
  }
  function nfOuter(t) { var seq = runOuter(t), last = seq[seq.length - 1]; return redexOuter(last) ? null : plain(last); }

module.exports = { parse: parse, plain: plain, pretty: pretty, redexes: redexes, redexOuter: redexOuter, redexInner: redexInner, contractAt: contractAt, runOuter: runOuter, ruleOf: ruleOf };
