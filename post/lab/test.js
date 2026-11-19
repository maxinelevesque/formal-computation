/* Tests for the calculus layer. Run: node post/lab/test.js
   Plain Node, no packages. Exits with status 1 if any check fails. */
'use strict';
var fs = require('fs');
var path = require('path');
var ski = require('./ski.js');
var tree = require('./tree.js');
var net = require('./net.js');
var graph = require('./graph.js');

var failures = 0, passes = 0;
function check(cond, what) {
  if (cond) { passes++; return; }
  failures++;
  console.log('  FAIL: ' + what);
}
function eq(a, b, what) { check(a === b, what + ' (got ' + JSON.stringify(a) + ', expected ' + JSON.stringify(b) + ')'); }
function section(s) { console.log('\n== ' + s); }
function pad(s, n) { s = String(s); while (s.length < n) s += ' '; return s; }
function table(rows) {
  var w = rows[0].map(function (_, c) { return Math.max.apply(null, rows.map(function (r) { return String(r[c]).length; })); });
  rows.forEach(function (r, i) {
    console.log('  ' + r.map(function (x, c) { return pad(x, w[c]); }).join('  '));
    if (i === 0) console.log('  ' + w.map(function (n) { return new Array(n + 1).join('-'); }).join('  '));
  });
}

/* ---------- SKI ---------- */
section('Combinatory logic (ski.js)');

// the essay's own reducer, as it was before the essay used ski.js (kept in essay-reducer.js), to compare behaviour
var essay = require('./essay-reducer.js');
var html = fs.readFileSync(path.join(__dirname, '..', 'atoms-and-probes.html'), 'utf8');
check(html.indexOf('SKI = CALC.ski') > 0 && html.indexOf('/* ---- post/lab/ski.js ---- */') > 0, 'the essay now runs on the inlined ski.js');

// the six terms and three probes of the bench, and the readings the essay's figure shows
var TERMS = ['I', 'S K K', 'S K S', 'K I', 'K (S K K)', 'K'];
var PROBES = [[], ['x'], ['x', 'y']];
var EXPECT = [
  ['I', 'x', 'x y'],
  ['S K K', 'x', 'x y'],
  ['S K S', 'x', 'x y'],
  ['K I', 'I', 'y'],
  ['K (S K K)', 'S K K', 'y'],
  ['K', 'K x', 'x']
];
var skiRows = [['term', '[ ]', '[ ] x', '[ ] x y', 'point']], keys = [], seen = {}, points = 0;
TERMS.forEach(function (s, r) {
  var row = [s], key = [];
  PROBES.forEach(function (p, c) {
    var e = ski.plug(p, s), seq = ski.run(e, 'outer', 40), last = seq[seq.length - 1];
    var out = ski.print(last), own = ski.isOutcome(last);
    // the essay's own computation of the same cell
    var ee = essay.parse(s);
    p.forEach(function (a) { ee = { k: 'p', f: ee, x: { k: 'a', n: a } }; });
    var es = essay.runOuter(ee), el = es[es.length - 1];
    eq(out, essay.pretty(el), 'SKI ' + s + ' under ' + JSON.stringify(p) + ' agrees with the essay');
    eq(seq.length, es.length, 'SKI ' + s + ' under ' + JSON.stringify(p) + ': same number of steps as the essay');
    eq(out, EXPECT[r][c], 'SKI ' + s + ' under ' + JSON.stringify(p));
    row.push(out + ' (' + (seq.length - 1) + ')' + (own ? '' : ' *'));
    key.push(own ? out : '');
  });
  key = key.join('|');
  if (!seen[key]) seen[key] = ++points;
  row.push(seen[key]);
  keys.push(seen[key]);
  skiRows.push(row);
});
table(skiRows);
console.log('  (n) = steps, outermost; * = not read: the outcome contains S, K or I');
eq(keys.join(','), '1,1,1,2,2,3', 'the six SKI terms make three points under these probes');

var skk = ski.run('S K K a', 'outer');
eq(skk.length - 1, 2, 'S K K a reaches a in 2 steps');
eq(ski.print(skk[2]), 'a', 'S K K a reaches a');
var loop = graph.runPath(ski, 'S I I (S I I)', 'inner');
check(loop.cyc && loop.cycleStart === 0 && loop.states.length === 3, 'S I I (S I I) cycles, arguments first, with period 3');
eq(loop.rules.join(', '), 'the S-rule, the I-rule, the I-rule', 'the rules around the SKI loop');
var g0 = graph.reductionGraph(ski, 'S I I (S I I)', { max: 30 });
check(g0.states[0].onCycle, 'the reduction graph of S I I (S I I) has a cycle through it');

// identical behaviour to the essay's reducer, on the essay's terms and on random terms
var NODES = ['S K K a', 'K a (I b)', 'K a (K a)', 'I a', 'K a b', 'a', 'I I', 'K I a', 'I', 'S K K', 'S K S',
  'S I I (S I I)', 'I (S I I) (I (S I I))', 'I (S I I) (S I I)'];
var rnd = net.rng(7);
function randomSki(n) {
  if (n <= 1) return ['S', 'K', 'I', 'a', 'b'][Math.floor(rnd() * 5)];
  var k = 1 + Math.floor(rnd() * (n - 1));
  var f = randomSki(k), x = randomSki(n - k);
  return f + ' ' + (x.indexOf(' ') >= 0 ? '(' + x + ')' : x);
}
var samples = NODES.slice();
for (var i = 0; i < 400; i++) samples.push(randomSki(2 + Math.floor(rnd() * 9)));
// The essay contracts a redex by node identity, and the S-rule shares its third argument, so a
// redex inside a shared argument is contracted in both places in one step. ski.js uses paths.
// On the terms the essay shows the two agree; with sharing removed after each step they agree always.
function unshare(t) { return t.k === 'a' ? { k: 'a', n: t.n } : { k: 'p', f: unshare(t.f), x: unshare(t.x) }; }
var sameOuter = 0, sameInner = 0, sameRedexes = 0, sameUnshared = 0, sharedDiff = [];
samples.forEach(function (s) {
  var t = ski.parse(s), et = essay.parse(s);
  // redexes in the same order, with the same rule names
  var mine = ski.redexes(t).map(function (r) { return ski.plain(ski.subterm(t, r.at)) + '/' + r.rule; }).join(';');
  var theirs = essay.redexes(et).map(function (r) { return essay.plain(r) + '/' + essay.ruleOf(r); }).join(';');
  if (mine === theirs) sameRedexes++;
  var a = ski.run(t, 'outer', 40).map(ski.plain).join(' > ');
  var b = essay.runOuter(et).map(essay.plain).join(' > ');
  if (a === b) sameOuter++; else sharedDiff.push(s);
  var u = et, ub = [essay.plain(u)];
  for (var k = 0; k < 40; k++) { var r0 = essay.redexOuter(u); if (!r0) break; u = unshare(essay.contractAt(u, r0)); ub.push(essay.plain(u)); }
  if (a === ub.join(' > ')) sameUnshared++;
  var ia = ski.run(t, 'inner', 40).map(ski.plain).join(' > ');
  u = et; var ib = [essay.plain(u)];
  for (k = 0; k < 40; k++) { var r = essay.redexInner(u); if (!r) break; u = essay.contractAt(u, r); ib.push(essay.plain(u)); }
  if (ia === ib.join(' > ')) sameInner++;
});
eq(sameRedexes, samples.length, 'redexes and rule names agree with the essay on ' + samples.length + ' terms');
eq(sameInner, samples.length, 'arguments-first runs agree with the essay on ' + samples.length + ' terms');
eq(sameUnshared, samples.length, 'outermost runs agree with the essay\'s reducer once shared subterms are copied');
NODES.forEach(function (s, i) {
  var t = ski.parse(s), et = essay.parse(s);
  // as the essay's hero figure: the loop terms (the last three) are run arguments first
  if (i < 11) eq(ski.run(t, 'outer', 40).map(ski.plain).join(' > '), essay.runOuter(et).map(essay.plain).join(' > '), 'outermost run of ' + s + ' as in the essay');
  eq(ski.print(t), essay.pretty(et), 'printed form of ' + s + ' as in the essay');
});
console.log('  runs agree with the essay\'s reducer: outermost ' + sameOuter + '/' + samples.length + ', arguments first ' + sameInner + '/' + samples.length +
  ', outermost with sharing removed ' + sameUnshared + '/' + samples.length);
if (sharedDiff.length) console.log('  the ' + sharedDiff.length + ' outermost differences are the essay contracting a shared redex twice in one step, e.g. from ' + sharedDiff[0]);

/* ---------- tree calculus ---------- */
section('Tree calculus (tree.js)');
var ia = tree.run('I a', 'outer');
eq(ia.length - 1, 2, 'I a reaches a in 2 steps');
eq(tree.print(ia[2]), 'a', 'I a reaches a');
var iaRules = graph.runPath(tree, 'I a', 'outer').rules.join(', ');
eq(iaRules, 'the S-rule, the K-rule', 'I a: the S-rule, then the K-rule');
eq(tree.print(tree.parse('△(△K)△')), 'I', 'I = △(△K)△ is re-abbreviated');
eq(tree.print(tree.parse('S K K'), { raw: true }), '△(△(△△)) (△△)', 'raw printing');
eq(tree.print(tree.parse('S I I')), 'ω', 'ω = S I I is re-abbreviated');
eq(tree.key(tree.parse('S K △')), tree.key(tree.parse('I')), 'S K △ is I');

var SEP = 'triage(x, K y, △) (triage(△, △, K I) [ ])';
var s1 = tree.run(tree.plug(SEP, '△(△K)△'), 'outer'), s2 = tree.run(tree.plug(SEP, '△(△K)K'), 'outer');
eq(tree.print(s1[s1.length - 1]), 'x', 'the separating probe reads x from △(△K)△');
eq(s1.length - 1, 5, 'the separating probe on △(△K)△: 5 steps (Lean: sep_idT)');
eq(tree.print(s2[s2.length - 1]), 'y', 'the separating probe reads y from △(△K)K');
eq(s2.length - 1, 6, 'the separating probe on △(△K)K: 6 steps (Lean: sep_idT\')');
console.log('  separating probe on I:     ' + s1.map(function (t) { return tree.print(t); }).join(' → '));
console.log('  separating probe on S K K: ' + s2.map(function (t) { return tree.print(t); }).join(' → '));

var tl = graph.runPath(tree, 'ω ω', 'inner');
check(tl.cyc && tl.cycleStart === 0, 'tree ω ω cycles, arguments first');
eq(tl.states.length, 5, 'tree ω ω: a lap of 5 steps');
console.log('  tree ω ω: ' + tl.states.map(function (t) { return tree.print(t); }).join(' → ') + ' → ω ω');
var g1 = graph.reductionGraph(tree, 'ω ω', { max: 40 });
check(g1.states[0].onCycle, 'the reduction graph of tree ω ω has a cycle through it');
var ka = tree.run('K a (ω ω)', 'outer');
eq(tree.print(ka[ka.length - 1]), 'a', 'K a (ω ω) reaches a, outermost');
eq(ka.length - 1, 1, 'K a (ω ω): one step (the K-rule)');
var kaIn = graph.runPath(tree, 'K a (ω ω)', 'inner');
check(kaIn.cyc, 'K a (ω ω), arguments first: loops');

var TTERMS = ['I', 'S K K', 'S K (△K)', 'K I', 'K (S K K)', 'K'];
var TPROBES = [[], ['x'], ['x', 'y'], SEP];
var TPNAMES = ['[ ]', '[ ] x', '[ ] x y', 'triage'];
var TEXPECT = [
  ['I', 'x', 'x y', 'x'],
  ['S K K', 'x', 'x y', 'y'],
  ['S K (△K)', 'x', 'x y', 'y'],
  ['K I', 'I', 'y', 'I'],
  ['K (S K K)', 'S K K', 'y', 'S K K'],
  ['K', 'K x', 'x', 'y']
];
var treeRows = [['term'].concat(TPNAMES)], treeNF = {};
TTERMS.forEach(function (s, r) {
  var row = [s];
  TPROBES.forEach(function (p, c) {
    var seq = tree.run(tree.plug(p, s), 'outer', 200), last = seq[seq.length - 1];
    check(tree.isNormal(last), 'tree ' + s + ' under ' + TPNAMES[c] + ' finishes');
    eq(tree.print(last), TEXPECT[r][c], 'tree ' + s + ' under ' + TPNAMES[c]);
    treeNF[r + ',' + c] = { term: last, steps: seq.length - 1 };
    row.push(tree.print(last) + ' (' + (seq.length - 1) + ')' + (tree.isOutcome(last) ? '' : ' *'));
  });
  treeRows.push(row);
});
table(treeRows);
console.log('  (n) = steps, outermost; * = not read: the outcome contains △');

/* ---------- interaction nets ---------- */
section('Interaction nets (net.js, eager table of tree-semantics)');
eq(net.TABLE.length, 15, 'fifteen rules');
// the table is well formed: every right-hand-side port occurs exactly once (eagerTable_wellFormed)
net.TABLE.forEach(function (r) {
  var ports = [], n = net.ARITY[r.left] + net.ARITY[r.right], ends = [];
  for (var i = 0; i < n; i++) ports.push('b' + i);
  r.kinds.forEach(function (k, c) { for (var j = 0; j <= net.ARITY[k]; j++) ports.push('c' + c + '.' + j); });
  r.links.forEach(function (l) { ends.push(l[0], l[1]); });
  eq(ends.slice().sort().join(' '), ports.slice().sort().join(' '), 'rule ' + r.code + ' covers each port once');
});

// all orders: every maximal run from the start, over the graph of states up to renaming
function allOrders(start, cap) {
  var memo = {}, count = 0, tooBig = false, diamonds = 0, diamondFails = 0, maxPairs = 0;
  function lengths(n) {
    var k = net.key(n);
    if (memo[k]) return memo[k];
    if (++count > cap) { tooBig = true; return [0]; }
    var ps = net.activePairs(n), out = {};
    if (ps.length > maxPairs) maxPairs = ps.length;
    if (!ps.length) { memo[k] = [0]; return memo[k]; }
    var next = ps.map(function (p) { return net.fire(n, p); });
    // the one-step diamond: two different pairs fired in either order give the same net
    for (var i = 0; i < ps.length; i++) for (var j = i + 1; j < ps.length; j++) {
      diamonds++;
      var ab = net.key(net.fire(next[i], ps[j])), ba = net.key(net.fire(next[j], ps[i]));
      if (ab !== ba) diamondFails++;
    }
    next.forEach(function (m) { lengths(m).forEach(function (l) { out[l + 1] = true; }); });
    memo[k] = Object.keys(out).map(Number).sort(function (a, b) { return a - b; });
    return memo[k];
  }
  var ls = lengths(start);
  return { lengths: ls, states: count, exhaustive: !tooBig, diamonds: diamonds, diamondFails: diamondFails, maxPairs: maxPairs };
}
function randomOrders(start, n, cap) {
  var lens = {}, finals = {};
  for (var s = 0; s < n; s++) {
    var rr = net.rng(1000 + s), m = start, k = 0;
    while (k < cap) { var st = net.step(m, 'random', rr); if (!st) break; m = st.t; k++; }
    lens[k] = true; finals[net.key(m)] = true;
  }
  return { lengths: Object.keys(lens).map(Number), finals: Object.keys(finals).length };
}

var netRows = [['term', 'probe', 'tree NF (steps)', 'net read-back', 'interactions', 'states', 'orders', 'diamonds']];
var counts = {};
TTERMS.forEach(function (s, r) {
  TPROBES.forEach(function (p, c) {
    var start = net.plug(p, s);
    var outer = net.run(start, 'outer', 2000), last = outer[outer.length - 1], n = outer.length - 1;
    check(net.isNormal(last), 'net ' + s + ' under ' + TPNAMES[c] + ' finishes');
    var rb = net.readback(last), nf = treeNF[r + ',' + c];
    eq(tree.key(rb.term), tree.key(nf.term), 'net ' + s + ' under ' + TPNAMES[c] + ' reads back the tree normal form');
    check(rb.ok, 'net ' + s + ' under ' + TPNAMES[c] + ': the read-back has no unread part');
    var inner = net.run(start, 'inner', 2000), oldest = net.run(start, 'oldest', 2000);
    eq(inner.length - 1, n, 'net ' + s + ' under ' + TPNAMES[c] + ': inner order, same length');
    eq(oldest.length - 1, n, 'net ' + s + ' under ' + TPNAMES[c] + ': fixed pair order, same length');
    var all = allOrders(start, 20000), orders;
    if (all.exhaustive) {
      eq(all.lengths.join(','), String(n), 'net ' + s + ' under ' + TPNAMES[c] + ': every order has ' + n + ' interactions');
      eq(all.diamondFails, 0, 'net ' + s + ' under ' + TPNAMES[c] + ': one-step diamond on ' + all.diamonds + ' pairs of pairs');
      orders = 'all';
    } else {
      orders = '200 random';
    }
    var ro = randomOrders(start, all.exhaustive ? 40 : 200, 5000);
    eq(ro.lengths.join(','), String(n), 'net ' + s + ' under ' + TPNAMES[c] + ': random orders, same length');
    eq(ro.finals, 1, 'net ' + s + ' under ' + TPNAMES[c] + ': random orders, same final net');
    counts[s + ' | ' + TPNAMES[c]] = n;
    netRows.push([s, TPNAMES[c], tree.print(nf.term) + ' (' + nf.steps + ')', net.print(last), n,
      all.exhaustive ? all.states : '>20000', orders, all.exhaustive ? all.diamonds : '-']);
  });
});
table(netRows);
console.log('  states = nets reachable up to renaming; diamonds = pairs of active pairs checked to commute');

// compact table: interactions per bench cell
var cRows = [['term'].concat(TPNAMES)];
TTERMS.forEach(function (s) { cRows.push([s].concat(TPNAMES.map(function (p) { return counts[s + ' | ' + p]; }))); });
console.log('\n  Interactions per bench cell (the same for every order):');
table(cRows);

// eager K a (ω ω): the answer is at the result port early, but the run never ends
var kn = net.parse('K a (ω ω)'), first = -1, steady = true, alwaysActive = true, m = kn;
for (var t = 0; t <= 400; t++) {
  var rbk = net.readback(m);
  var reads = tree.print(rbk.term) === 'a';
  if (reads && first < 0) first = t;
  if (first >= 0 && !reads) steady = false;
  if (net.isNormal(m)) { alwaysActive = false; break; }
  if (t < 400) m = net.step(m, 'outer').t;
}
check(first >= 0 && first <= 3, 'eager K a (ω ω): the result port reads a after ' + first + ' interactions');
check(steady, 'eager K a (ω ω): the reading stays a');
check(alwaysActive, 'eager K a (ω ω): active pairs never run out (400 interactions)');
console.log('  eager K a (ω ω): reads a after ' + first + ' interactions; after 400 interactions ' + net.size(m) +
  ' agents and ' + net.activePairs(m).length + ' active pairs remain');
var mr = kn, rr = net.rng(3), readA = -1;
for (var t2 = 0; t2 < 400; t2++) { mr = net.step(mr, 'random', rr).t; if (readA < 0 && tree.print(net.readback(mr).term) === 'a') readA = t2 + 1; }
check(readA > 0 && !net.isNormal(mr), 'eager K a (ω ω), a random order: reads a (after ' + readA + '), never finishes');

// compile and read back agree on values; key is invariant under renaming
['I', 'K (S K K)', 'S K (△K)', 'ω', '△ (x y) z'].forEach(function (s) {
  eq(tree.key(net.readback(net.parse(s)).term), tree.key(tree.parse(s)), 'read-back of the compiled ' + s);
});
var shifted = net.compile('S K K x y');
var ren = net.clone(shifted), map = {}, off = 17;
ren.kind = {}; ren.link = {};
Object.keys(shifted.kind).forEach(function (id) { ren.kind[Number(id) * 3 + off] = shifted.kind[id]; });
Object.keys(shifted.link).forEach(function (p) {
  function mv(q) { return /^[@$]/.test(q) ? q : (Number(q.split('.')[0]) * 3 + off) + '.' + q.split('.')[1]; }
  ren.link[mv(p)] = mv(shifted.link[p]);
});
eq(net.key(ren), net.key(shifted), 'key is invariant under renaming agents');
// plugging a net into a probe is the same as plugging the term
eq(net.key(net.plug(SEP, net.parse('I'))), net.key(net.plug(SEP, 'I')), 'plugging a net into a context');
function finalKey(n) { var r = net.run(n, 'outer'); return net.key(r[r.length - 1]); }
eq(finalKey(net.plug(['x', 'y'], net.parse('K'))), finalKey(net.plug(['x', 'y'], 'K')), 'plugging a net with variables: same final net');

// interaction counts against the cost recursion of tree-semantics (IxTreeCost.lean: EvalNet),
// on closed applications f x of trees: compile f x is IxTreeCompile.compile
function shapeOf(t) { var sp = tree.spine(t); return sp.args; }
function tsize(t) { return shapeOf(t).reduce(function (a, c) { return a + tsize(c); }, 1); }
function evalNet(f, z, fuel) {
  if (fuel.n-- <= 0) throw new Error('fuel');
  var a = shapeOf(f), L = tree.leaf, App = tree.app;
  if (a.length === 0) return { v: App(L, z), n: 1 };
  if (a.length === 1) return { v: App(App(L, a[0]), z), n: 1 };
  var u = a[0], y = a[1], ua = shapeOf(u);
  if (ua.length === 0) return { v: y, n: 2 + tsize(z) };
  if (ua.length === 1) {
    var r1 = evalNet(ua[0], z, fuel), r2 = evalNet(y, z, fuel), r3 = evalNet(r1.v, r2.v, fuel);
    return { v: r3.v, n: 2 + tsize(z) + r1.n + r2.n + r3.n };
  }
  var w = ua[0], x = ua[1], za = shapeOf(z);
  if (za.length === 0) return { v: w, n: 3 + tsize(x) + tsize(y) };
  if (za.length === 1) { var q = evalNet(x, za[0], fuel); return { v: q.v, n: 3 + tsize(w) + tsize(y) + q.n }; }
  var p1 = evalNet(y, za[0], fuel), p2 = evalNet(p1.v, za[1], fuel);
  return { v: p2.v, n: 3 + tsize(w) + tsize(x) + p1.n + p2.n };
}
function randomTree(n) {
  if (n <= 1) return tree.leaf;
  var r = rnd();
  if (r < 0.4) return tree.app(tree.leaf, randomTree(n - 1));
  var k = 1 + Math.floor(rnd() * (n - 2));
  return tree.app(tree.app(tree.leaf, randomTree(k)), randomTree(n - 1 - k));
}
var costChecked = 0, costAgree = 0;
for (var ci = 0; ci < 300; ci++) {
  var cf = randomTree(1 + Math.floor(rnd() * 7)), cx = randomTree(1 + Math.floor(rnd() * 5)), ev;
  try { ev = evalNet(cf, cx, { n: 300 }); } catch (e) { continue; }
  var cr = net.run(net.compileApp(cf, cx), 'outer', 5000), cl = cr[cr.length - 1];
  costChecked++;
  if (net.isNormal(cl) && cr.length - 1 === ev.n && tree.key(net.readback(cl).term) === tree.key(ev.v) && net.readback(cl).garbage === 0) costAgree++;
}
check(costChecked >= 200, 'cost recursion: enough finishing samples (' + costChecked + ')');
eq(costAgree, costChecked, 'interactions, value and no garbage agree with EvalNet (IxTreeCost.lean) on ' + costChecked + ' closed applications');
console.log('  interaction counts equal the EvalNet cost recursion on ' + costAgree + '/' + costChecked + ' random closed applications f x');
// a variable used twice gets a duplicator
var xx = net.run(net.parse('S K K (x x)'), 'outer');
eq(net.print(xx[xx.length - 1]), 'x x', 'S K K (x x) reads x x');
// the reduction graph of a net, and its layout
var gn = graph.reductionGraph(net, 'K a (I b)', { max: 400 });
check(!gn.truncated && gn.fibres.length === 1 && gn.fibres[0].label === 'a', 'net K a (I b): one fibre, over a');
var L = graph.layoutBundle(gn, {});
check(L.nodes.every(function (n) { return isFinite(n.x) && isFinite(n.y); }), 'layoutBundle places every state');
var ln = net.layoutNet(net.parse('S K K x'));
check(ln.agents.length === net.size(net.parse('S K K x')) && ln.wires.every(function (w) { return /^M [-\d.]+ [-\d.]+ C/.test(w.d); }), 'layoutNet draws every agent and wire');
var lnK = net.layoutNet(m);
check(lnK.agents.length === net.size(m), 'layoutNet handles detached parts (' + net.size(m) + ' agents)');

/* ---------- graph layer on the essay's bundle ---------- */
section('Reduction graphs (graph.js)');
var gb = graph.reductionGraph(ski, NODES, { closed: true });
eq(gb.edges.length, 11, 'the essay bundle: eleven steps among the fourteen terms');
eq(gb.fibres.map(function (f) { return f.label; }).join(' | '), 'a | I | S K K | S K S | no value', 'the essay bundle: five fibres');
var lb = graph.layoutBundle(gb, { orientation: 'wide' }), lt = graph.layoutBundle(gb, { orientation: 'tall' });
check(lb.nodes.length === 14 && lt.nodes.length === 14, 'both layouts place the fourteen terms');
function overlaps(Lo) {
  var bad = 0, tall = Lo.orientation === 'tall';
  Lo.nodes.forEach(function (a, i) { Lo.nodes.forEach(function (b, j) {
    if (j <= i) return;
    var wa = tall ? 22 : a.w, wb = tall ? 22 : b.w;
    if (Math.abs(a.x - b.x) < (wa + wb) / 2 && Math.abs(a.y - b.y) < 22) bad++;
  }); });
  return bad;
}
eq(overlaps(lb) + overlaps(lt), 0, 'no two states overlap in either layout');
var fx = Object.keys(lb.fibres).map(function (k) { return lb.fibres[k].x; });
check(fx.every(function (x, i) { return i === 0 || x > fx[i - 1]; }), 'fibre points in order along the line');
var lnet = net.layoutNet(net.run(net.parse('K a (ω ω)'), 'outer', 60).pop()), coin = 0;
lnet.agents.forEach(function (a, i) { lnet.agents.forEach(function (b, j) { if (j > i && Math.abs(a.x - b.x) < 20 && Math.abs(a.y - b.y) < 20) coin++; }); });
eq(coin, 0, 'layoutNet: no two agents coincide');
var TNODES = ['S K K a', 'K a (I b)', 'K a (K a)', 'I a', 'K a b', 'a', 'I I', 'K I a', 'I', 'S K K', 'S K (△K)', 'ω ω'];
var gt = graph.reductionGraph(tree, TNODES, { max: 80, maxDepth: 6 });
console.log('  tree bundle from ' + TNODES.length + ' terms: ' + gt.states.length + ' states, ' + gt.edges.length + ' steps, fibres: ' +
  gt.fibres.map(function (f) { return f.label; }).join(' | '));

console.log('\n' + passes + ' checks passed, ' + failures + ' failed.');
if (failures) process.exit(1);
