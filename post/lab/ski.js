/* Combinatory logic (S, K, I), extracted from the reducer of "Atoms and Probes".
   Interface shared with tree.js and net.js (see README.md):
     id, name, parse, print, key, redexes, contract, step, isNormal, isOutcome, plug, run.
   Terms: { k: 'a', n: name } for an atom, { k: 'p', f: f, x: x } for an application.
   A redex position `at` is a path from the root: a string of 'f' (go to the function)
   and 'x' (go to the argument). Positions are paths rather than node identities because
   the S-rule shares its third argument between two places. */
(function (root) {
  var CALC = root.CALC || (root.CALC = {});

  var A = function (n) { return { k: 'a', n: n }; };
  var App = function (f, x) { return { k: 'p', f: f, x: x }; };
  var HOLE = '[ ]';

  function parse(s) {
    s = String(s).replace(/ω/g, '(S I I)');
    var toks = s.match(/\[\s*\]|[()]|[^\s()\[\]]+/g) || [], i = 0;
    function seq() {
      var cur = null, t;
      while (i < toks.length && toks[i] !== ')') {
        if (toks[i] === '(') { i++; t = seq(); if (toks[i] !== ')') throw new Error('missing )'); i++; }
        else { t = A(/^\[\s*\]$/.test(toks[i]) ? HOLE : toks[i]); i++; }
        cur = cur ? App(cur, t) : t;
      }
      return cur;
    }
    var t = seq();
    if (i < toks.length) throw new Error('unexpected )');
    if (!t) throw new Error('empty term');
    return t;
  }
  function plain(t) {
    if (t.k === 'a') return t.n;
    return plain(t.f) + ' ' + (t.x.k === 'p' ? '(' + plain(t.x) + ')' : plain(t.x));
  }
  function isOmegaHalf(t) { return t.k === 'p' && plain(t) === 'S I I'; }
  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;'); }
  // printed form with ω for S I I. opts.html marks the redex at path opts.mark (or the node opts.mark)
  function print(t, opts) {
    opts = opts || {};
    var html = !!opts.html, mark = opts.mark;
    var markPath = typeof mark === 'string' ? mark : (mark && mark.at !== undefined ? mark.at : null);
    var markNode = (mark && typeof mark === 'object' && mark.k) ? mark : null;
    function go(u, path) {
      var s;
      if (!opts.raw && isOmegaHalf(u)) s = 'ω';
      else if (u.k === 'a') s = html ? esc(u.n) : u.n;
      else {
        var xs = go(u.x, path + 'x');
        s = go(u.f, path + 'f') + ' ' + ((u.x.k === 'p' && (opts.raw || !isOmegaHalf(u.x))) ? '(' + xs + ')' : xs);
      }
      return (html && (path === markPath || u === markNode)) ? '<mark>' + s + '</mark>' : s;
    }
    return go(t, '');
  }
  function spine(t, path) {
    path = path || '';
    var args = [], apps = [], paths = [];
    while (t.k === 'p') { args.unshift(t.x); apps.unshift(t); paths.unshift(path); t = t.f; path += 'f'; }
    return { head: t, args: args, apps: apps, paths: paths };
  }
  function need(h) { return h.n === 'I' ? 1 : h.n === 'K' ? 2 : h.n === 'S' ? 3 : 0; }
  function ruleName(h) { return 'the ' + h.n + '-rule'; }
  // every redex of t, the head redex first and then those inside the arguments, left to right
  function redexes(t) {
    var out = [];
    (function go(u, path) {
      if (u.k === 'a') return;
      var sp = spine(u, path), n = need(sp.head);
      if (n && sp.args.length >= n) out.push({ at: sp.paths[n - 1], node: sp.apps[n - 1], rule: ruleName(sp.head) });
      sp.args.forEach(function (a, i) { go(a, sp.paths[i] + 'x'); });
    })(t, '');
    return out;
  }
  // arguments first: the leftmost innermost redex (the essay's redexInner)
  function redexInner(t) {
    return (function go(u, path) {
      if (u.k === 'a') return null;
      var sp = spine(u, path), n = need(sp.head);
      for (var i = 0; i < sp.args.length; i++) { var r = go(sp.args[i], sp.paths[i] + 'x'); if (r) return r; }
      if (n && sp.args.length >= n) return { at: sp.paths[n - 1], node: sp.apps[n - 1], rule: ruleName(sp.head) };
      return null;
    })(t, '');
  }
  function subterm(t, path) {
    for (var i = 0; i < path.length; i++) t = path.charAt(i) === 'f' ? t.f : t.x;
    return t;
  }
  function contractHere(r) {
    var sp = spine(r), a = sp.args;
    if (sp.head.n === 'S') return App(App(a[0], a[2]), App(a[1], a[2]));
    return a[0];
  }
  function replaceAt(t, path, f) {
    if (path === '') return f(t);
    return path.charAt(0) === 'f' ? App(replaceAt(t.f, path.slice(1), f), t.x) : App(t.f, replaceAt(t.x, path.slice(1), f));
  }
  function contract(t, r) {
    var at = typeof r === 'string' ? r : r.at;
    return replaceAt(t, at, contractHere);
  }
  function pick(t, strategy) {
    if (typeof strategy === 'function') return strategy(redexes(t), t);
    if (strategy === 'inner') return redexInner(t);
    return redexes(t)[0] || null;
  }
  function step(t, strategy) {
    var r = pick(t, strategy || 'outer');
    if (!r) return null;
    return { t: contract(t, r), rule: r.rule, at: r.at };
  }
  function isNormal(t) { return redexes(t).length === 0; }
  var CONST = { S: 1, K: 1, I: 1 };
  // written in variables alone (the essay's `own`: no S, K or I in the result)
  function isOutcome(t) {
    if (t.k === 'a') return !CONST[t.n] && t.n !== HOLE;
    return isOutcome(t.f) && isOutcome(t.x);
  }
  function fill(c, t) {
    if (c.k === 'a') return c.n === HOLE ? t : c;
    return App(fill(c.f, t), fill(c.x, t));
  }
  // probe: a list of variable names to supply, or a context (string or term) with a hole [ ]
  function plug(probe, t) {
    if (typeof t === 'string') t = parse(t);
    if (Array.isArray(probe)) { var e = t; probe.forEach(function (a) { e = App(e, A(a)); }); return e; }
    return fill(typeof probe === 'string' ? parse(probe) : probe, t);
  }
  // the states of a run, from t, by the strategy, for at most max steps (the essay's runOuter caps at 40)
  function run(t, strategy, max) {
    if (typeof t === 'string') t = parse(t);
    max = max === undefined ? 40 : max;
    var seq = [t];
    for (var i = 0; i < max; i++) { var s = step(t, strategy); if (!s) break; t = s.t; seq.push(t); }
    return seq;
  }

  var ski = {
    id: 'ski', name: 'Combinatory logic',
    atom: A, app: App, hole: HOLE,
    parse: parse, print: print, key: plain, plain: plain,
    spine: spine, subterm: subterm,
    redexes: redexes, redexInner: redexInner, contract: contract, step: step,
    isNormal: isNormal, isOutcome: isOutcome, plug: plug, run: run,
    strategies: ['outer', 'inner']
  };
  CALC.ski = ski;
  if (typeof module !== 'undefined' && module.exports) module.exports = ski;
})(typeof window !== 'undefined' ? window : (typeof globalThis !== 'undefined' ? globalThis : this));
