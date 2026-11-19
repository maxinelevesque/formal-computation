/* Tree calculus, the triage presentation (as FormalComputation/Tree/Calculus.lean):
     △ △ y z            → y          the K-rule
     △ (△ x) y z        → x z (y z)  the S-rule
     △ (△ w x) y △      → w          triage on a leaf
     △ (△ w x) y (△ u)  → x u        triage on a stem
     △ (△ w x) y (△ u v) → y u v     triage on a fork
   Terms are those of ski.js: { k: 'a', n: '△' } is the leaf, any other atom is a variable,
   { k: 'p', f, x } is an application. Abbreviations, expanded by parse and recovered by print:
     K = △△,  I = △(△K)△,  S x y = △(△x)y,  ω = S I I,  triage(a, b, c) = △(△ a b) c.
   Redex positions are paths ('f'/'x' strings), as in ski.js. "outer" is the stepper of
   Calculus.lean (root, then the function part, then the argument), which is the head redex
   first and then the arguments left to right; "inner" is arguments first. */
(function (root) {
  var CALC = root.CALC || (root.CALC = {});

  var LEAF = '△';
  var HOLE = '[ ]';
  var A = function (n) { return { k: 'a', n: n }; };
  var App = function (f, x) { return { k: 'p', f: f, x: x }; };
  var L = A(LEAF);
  function isL(t) { return t.k === 'a' && t.n === LEAF; }
  var K = App(L, L);
  var I = App(App(L, App(L, K)), L);
  function Sxy(x, y) { return App(App(L, App(L, x)), y); }
  var OMEGA = Sxy(I, I);
  function triage(a, b, c) { return App(App(L, App(App(L, a), b)), c); }

  /* ---------- parsing ---------- */
  function parse(s) {
    var toks = String(s).match(/\[\s*\]|[()△Δω,]|[^\s()\[\],△Δω]+/g) || [], i = 0;
    function operand() {
      var t = toks[i];
      if (t === '(') { i++; var u = seq(); if (toks[i] !== ')') throw new Error('missing )'); i++; return u; }
      if (t === 'triage' && toks[i + 1] === '(') {
        i += 2;
        var as = [seq()];
        while (toks[i] === ',') { i++; as.push(seq()); }
        if (toks[i] !== ')' || as.length !== 3) throw new Error('triage takes three arguments');
        i++;
        return triage(as[0], as[1], as[2]);
      }
      i++;
      if (t === '△' || t === 'Δ') return L;
      if (t === 'K') return K;
      if (t === 'I') return I;
      if (t === 'ω') return OMEGA;
      if (t === 'S') {
        if (i >= toks.length || toks[i] === ')' || toks[i] === ',') throw new Error('S needs two arguments (S x y = △(△x)y)');
        var x = operand();
        if (i >= toks.length || toks[i] === ')' || toks[i] === ',') throw new Error('S needs two arguments (S x y = △(△x)y)');
        var y = operand();
        return Sxy(x, y);
      }
      if (/^\[\s*\]$/.test(t)) return A(HOLE);
      return A(t);
    }
    function seq() {
      var cur = null;
      while (i < toks.length && toks[i] !== ')' && toks[i] !== ',') {
        var t = operand();
        cur = cur ? App(cur, t) : t;
      }
      if (!cur) throw new Error('empty term');
      return cur;
    }
    var t = seq();
    if (i < toks.length) throw new Error('unexpected ' + toks[i]);
    return t;
  }

  /* ---------- printing ---------- */
  function same(a, b) {
    if (a === b) return true;
    if (a.k !== b.k) return false;
    if (a.k === 'a') return a.n === b.n;
    return same(a.f, b.f) && same(a.x, b.x);
  }
  function isK(t) { return t.k === 'p' && isL(t.f) && isL(t.x); }
  function sArgs(t) {   // △ (△ x) y  ->  [x, y]
    if (t.k === 'p' && t.f.k === 'p' && isL(t.f.f) && t.f.x.k === 'p' && isL(t.f.x.f)) return [t.f.x.x, t.x];
    return null;
  }
  function isI(t) { var s = sArgs(t); return !!s && isK(s[0]) && isL(s[1]); }
  function isOmega(t) { var s = sArgs(t); return !!s && isI(s[0]) && isI(s[1]); }
  function abbrev(t) { return isOmega(t) ? 'ω' : isI(t) ? 'I' : isK(t) ? 'K' : null; }
  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;'); }
  // opts: raw (print △ only), html (escape, and <mark> the redex at path opts.mark),
  // cls(node) -> class name or null (wraps the node in a span; used for net read-backs)
  function print(t, opts) {
    opts = opts || {};
    var raw = !!opts.raw, html = !!opts.html, mark = opts.mark;
    var markPath = typeof mark === 'string' ? mark : (mark && mark.at !== undefined ? mark.at : null);
    function wrap(u, path, s) {
      if (html && opts.cls) { var c = opts.cls(u); if (c) s = '<span class="' + c + '">' + s + '</span>'; }
      if (html && path === markPath) s = '<mark>' + s + '</mark>';
      return s;
    }
    // returns { s, atomic }
    function go(u, path) {
      var ab = raw ? null : abbrev(u);
      if (ab) return { s: wrap(u, path, ab), atomic: true };
      if (u.k === 'a') return { s: wrap(u, path, html ? esc(u.n) : u.n), atomic: true };
      var sa = raw ? null : sArgs(u);
      if (sa && !isL(sa[0])) {   // △(△△) y prints as △K y, not S △ y
        // S x y: the paths of x and y are 'fxx' and 'x' below this node
        var x = go(sa[0], path + 'fxx'), y = go(sa[1], path + 'x');
        return { s: wrap(u, path, 'S ' + par(x) + ' ' + par(y)), atomic: false };
      }
      var f = go(u.f, path + 'f'), a = go(u.x, path + 'x');
      // no space directly after the leaf: △K, △(△K), △△ y
      return { s: wrap(u, path, f.s + (isL(u.f) ? '' : ' ') + par(a)), atomic: false };
    }
    function par(r) { return r.atomic ? r.s : '(' + r.s + ')'; }
    return go(t, '').s;
  }
  // the key: raw △ form, fully parenthesised by application (unique for each term)
  function key(t) {
    if (t.k === 'a') return t.n;
    return key(t.f) + ' ' + (t.x.k === 'p' ? '(' + key(t.x) + ')' : key(t.x));
  }

  /* ---------- redexes ---------- */
  function spine(t, path) {
    path = path || '';
    var args = [], apps = [], paths = [];
    while (t.k === 'p') { args.unshift(t.x); apps.unshift(t); paths.unshift(path); t = t.f; path += 'f'; }
    return { head: t, args: args, apps: apps, paths: paths };
  }
  // the rule for △ a1 a2 a3, or null
  function ruleFor(a1, a3) {
    if (isL(a1)) return 'K';
    var s1 = spine(a1);
    if (!isL(s1.head)) return null;
    if (s1.args.length === 1) return 'S';
    if (s1.args.length !== 2) return null;
    var s3 = spine(a3);
    if (!isL(s3.head)) return null;
    return s3.args.length === 0 ? 'TL' : s3.args.length === 1 ? 'TS' : s3.args.length === 2 ? 'TF' : null;
  }
  var RULES = { K: 'the K-rule', S: 'the S-rule', TL: 'triage on a leaf', TS: 'triage on a stem', TF: 'triage on a fork' };
  function headRedex(sp) {
    if (!isL(sp.head) || sp.args.length < 3) return null;
    var r = ruleFor(sp.args[0], sp.args[2]);
    return r ? { at: sp.paths[2], node: sp.apps[2], rule: RULES[r], kind: r } : null;
  }
  function redexes(t) {
    var out = [];
    (function go(u, path) {
      if (u.k === 'a') return;
      var sp = spine(u, path), h = headRedex(sp);
      if (h) out.push(h);
      sp.args.forEach(function (a, i) { go(a, sp.paths[i] + 'x'); });
    })(t, '');
    return out;
  }
  function redexInner(t) {
    return (function go(u, path) {
      if (u.k === 'a') return null;
      var sp = spine(u, path);
      for (var i = 0; i < sp.args.length; i++) { var r = go(sp.args[i], sp.paths[i] + 'x'); if (r) return r; }
      return headRedex(sp);
    })(t, '');
  }
  function contractHere(r) {
    var sp = spine(r), a = sp.args, k = ruleFor(a[0], a[2]);
    var s1 = spine(a[0]), s3 = spine(a[2]);
    switch (k) {
      case 'K': return a[1];
      case 'S': return App(App(s1.args[0], a[2]), App(a[1], a[2]));
      case 'TL': return s1.args[0];
      case 'TS': return App(s1.args[1], s3.args[0]);
      case 'TF': return App(App(a[1], s3.args[0]), s3.args[1]);
    }
    throw new Error('not a redex');
  }
  function replaceAt(t, path, f) {
    if (path === '') return f(t);
    return path.charAt(0) === 'f' ? App(replaceAt(t.f, path.slice(1), f), t.x) : App(t.f, replaceAt(t.x, path.slice(1), f));
  }
  function subterm(t, path) {
    for (var i = 0; i < path.length; i++) t = path.charAt(i) === 'f' ? t.f : t.x;
    return t;
  }
  function contract(t, r) { return replaceAt(t, typeof r === 'string' ? r : r.at, contractHere); }
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
  function isVar(t) { return t.k === 'a' && t.n !== LEAF && t.n !== HOLE && t.n !== '?' && t.n !== '…'; }
  function isOutcome(t) { return t.k === 'a' ? isVar(t) : isOutcome(t.f) && isOutcome(t.x); }
  function fill(c, t) {
    if (c.k === 'a') return c.n === HOLE ? t : c;
    return App(fill(c.f, t), fill(c.x, t));
  }
  function plug(probe, t) {
    if (typeof t === 'string') t = parse(t);
    if (Array.isArray(probe)) { var e = t; probe.forEach(function (a) { e = App(e, A(a)); }); return e; }
    return fill(typeof probe === 'string' ? parse(probe) : probe, t);
  }
  function run(t, strategy, max) {
    if (typeof t === 'string') t = parse(t);
    max = max === undefined ? 40 : max;
    var seq = [t];
    for (var i = 0; i < max; i++) { var s = step(t, strategy); if (!s) break; t = s.t; seq.push(t); }
    return seq;
  }
  // a closed normal form is a tree: leaf, stem or fork
  function shape(t) {
    var sp = spine(t);
    if (!isL(sp.head) || sp.args.length > 2) return null;
    return ['leaf', 'stem', 'fork'][sp.args.length];
  }

  var tree = {
    id: 'tree', name: 'Tree calculus',
    LEAF: LEAF, hole: HOLE, atom: A, app: App,
    leaf: L, K: K, I: I, S: Sxy, omega: OMEGA, triage: triage,
    isLeaf: isL, isVar: isVar, same: same, shape: shape, abbrev: abbrev,
    parse: parse, print: print, key: key, plain: key,
    spine: spine, subterm: subterm,
    redexes: redexes, redexInner: redexInner, contract: contract, step: step,
    isNormal: isNormal, isOutcome: isOutcome, plug: plug, run: run,
    rules: RULES, strategies: ['outer', 'inner']
  };
  CALC.tree = tree;
  if (typeof module !== 'undefined' && module.exports) module.exports = tree;
})(typeof window !== 'undefined' ? window : (typeof globalThis !== 'undefined' ? globalThis : this));
