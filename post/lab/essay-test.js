/* The essay under a stub DOM: node post/lab/essay-test.js
   1. Combinatory logic: a fixed scenario of clicks and fake time over every figure, at a wide and
      a narrow width. The serialised figures are hashed and compared with essay-ski-snapshot.json,
      which was taken from the essay before the calculus switch was added (blob 1356f7b).
      Regenerate (only from that version!) with
        node post/lab/essay-test.js --write-snapshot OLD.html
      and show the differences against an old copy with
        node post/lab/essay-test.js --diff OLD.html
      Review R1 (pass G) changed 14 snapshots on purpose; the fixture's "source" field lists them.
   2. The switch: every mode, every figure rendered and driven without exceptions; no duplicate ids;
      the hash round-trips; the calculus notes show only in their mode.
   3-6. What the figures show in tree calculus and in nets.
   7. Keyboard (no hidden box in the tab order), captions and labels by mode, reduced motion (nothing moves
      by itself), Pause, and the width of the net bench at 390 px.
   Plain Node, no packages. */
'use strict';
var fs = require('fs');
var path = require('path');
var crypto = require('crypto');
var stub = require('./stubdom.js');

var ESSAY = path.join(__dirname, '..', 'atoms-and-probes.html');
var SNAP = path.join(__dirname, 'essay-ski-snapshot.json');
var failures = 0, passes = 0;
function check(cond, what) { if (cond) { passes++; return; } failures++; console.log('  FAIL: ' + what); }
function section(s) { console.log('\n== ' + s); }

// the elements whose contents the figures write
var IDS = ['svg-tree', 'grid', 'benchsay', 'benchrun', 'benchverdict', 'benchread', 'benchcode',
  'svg-hero', 'now', 'stepinfo', 'heroread', 'focus', 'order', 'time', 'play',
  'svg-base', 'baseread', 'addrule', 'svg-paint', 'verdict', 'paintread', 'pred', 'closeit',
  'svg-lemma', 'lemmaread', 'svg-pent', 'pentread', 'svg-exit', 'svg-code', 'coderead', 'readcode',
  'fib-a', 'fib-w', 'fread', 'svg-loop', 'svg-kloop', 'loopread', 'kloopread', 'evid',
  'svg-grid', 'gridread', 'gridab', 'gridba', 'svg-proc', 'svg-outside', 'z0', 'z1', 'z2', 'z3', 'z4', 'z5', 'z6', 'z7'];
function tabsHtml(env) {
  return env.document.querySelectorAll('.tab').map(function (b) { return b.outerHTML; }).join('');
}

/* The scenario. snap(name, ids) records the serialised elements. */
function scenario(env, snap) {
  var $ = env.$, adv = env.advance;
  function all(name) { snap(name, IDS); }
  adv(3000); all('load');
  // the bench: every cell, both readings, and reading code
  for (var r = 0; r < 6; r++) for (var c = 0; c < 3; c++) {
    env.click(env.document.querySelector('#grid [data-r="' + r + '"][data-c="' + c + '"]'));
    adv(r === 0 && c === 0 ? 300 : 9000);
    snap('bench ' + r + ',' + c, ['svg-tree', 'grid', 'benchsay', 'benchrun', 'benchverdict', 'benchread']);
  }
  env.click(env.document.querySelector('.tab[data-r="text"]')); adv(100); snap('bench text', ['svg-tree', 'benchsay', 'grid']);
  env.click($('benchcode')); adv(2000); snap('bench code', ['grid', 'benchverdict', 'benchread']);
  env.click(env.document.querySelector('.tab[data-r="probe"]')); env.click($('benchcode')); adv(2000); snap('bench back', ['grid', 'svg-tree']);
  // running: four views, every term, both orders
  [1, 2, 4, 3].forEach(function (l) { env.click(env.document.querySelector('[data-l="' + l + '"]')); adv(700); snap('hero level ' + l, ['svg-hero', 'now', 'stepinfo', 'heroread']); });
  var nf = $('focus').options.length;
  ['outer', 'inner'].forEach(function (o) {
    env.change($('order'), o); adv(200);
    for (var i = 0; i < nf; i++) {
      env.change($('focus'), String(i)); adv(1300); snap('hero ' + o + ' ' + i + ' mid', ['svg-hero', 'now', 'stepinfo']);
      adv(20000); snap('hero ' + o + ' ' + i, ['svg-hero', 'now', 'stepinfo', 'heroread', 'play', 'time']);
    }
  });
  env.change($('time'), '0.5'); adv(100); snap('hero time', ['svg-hero', 'now', 'stepinfo']);
  env.click(env.document.querySelector('[data-l="1"]')); adv(100); snap('hero step', ['svg-hero', 'heroread']);
  env.click(env.document.querySelector('[data-l="3"]'));
  // the three equalities and the rule
  ['syntax', 'test', 'run'].forEach(function (m) { env.click(env.document.querySelector('[data-m="' + m + '"]')); adv(1000); snap('base ' + m, ['svg-base', 'baseread']); });
  env.click($('addrule')); adv(1500); snap('base rule', ['svg-base', 'baseread']);
  env.click(env.document.querySelector('[data-m="test"]')); adv(1000); snap('base rule test', ['svg-base', 'baseread']);
  env.click($('addrule')); env.click(env.document.querySelector('[data-m="run"]')); adv(1000); snap('base back', ['svg-base', 'baseread']);
  // a predicate and its leaks
  $('pred').options.forEach(function (o) {
    env.change($('pred'), o.value); adv(100); snap('paint ' + o.value, ['svg-paint', 'verdict', 'paintread', 'closeit']);
    if (!$('closeit').disabled) { env.click($('closeit')); adv(3000); snap('paint closed ' + o.value, ['svg-paint', 'verdict', 'paintread']); env.click($('closeit')); }
  });
  env.change($('pred'), 'hasK');
  var picks = $('svg-paint').querySelectorAll('g.pick');
  env.click(picks[2]); adv(100); env.key(picks[5], 'Enter'); adv(100); snap('paint by hand', ['svg-paint', 'verdict', 'paintread', 'pred']);
  // the fundamental lemma
  [1, 2, 0].forEach(function (k) { env.click(env.document.querySelector('[data-k="' + k + '"]')); adv(1000); snap('lemma ' + k, ['svg-lemma', 'lemmaread']); });
  env.click($('lemmaplay')); adv(1500); snap('lemma play mid', ['svg-lemma', 'lemmaread']); adv(4000); snap('lemma play', ['svg-lemma', 'lemmaread']);
  // two fibres from the inside
  env.click($('fill')); adv(500); snap('pent fill', ['svg-pent', 'pentread']);
  snap('exit', ['svg-exit']);
  // reading code
  env.click($('readcode')); adv(1500); snap('code on', ['svg-code', 'coderead']);
  env.click($('readcode')); adv(1500); snap('code off', ['svg-code', 'coderead']);
  // what is kept of a fibre
  [1, 2, 3, 0].forEach(function (k) { env.click(env.document.querySelector('[data-f="' + k + '"]')); adv(2500); snap('fib ' + k, ['fib-a', 'fib-w', 'fread']); });
  env.click($('fplay')); adv(16000); snap('fib play', ['fib-a', 'fib-w', 'fread']);
  // the counter
  env.click($('lapfwd')); adv(1000); snap('lap mid', ['svg-loop', 'loopread']); adv(3000); snap('lap fwd', ['svg-loop', 'loopread']);
  env.click($('lapback')); adv(4000); snap('lap back', ['svg-loop', 'loopread']);
  env.click($('ksend')); adv(2000); snap('k mid', ['svg-kloop', 'kloopread']); adv(3000); snap('k send', ['svg-kloop', 'kloopread']);
  env.change($('evid'), 'yes'); adv(100); env.click($('lapfwd')); adv(4000); env.click($('ksend')); adv(5000); snap('yes', ['svg-loop', 'svg-kloop', 'loopread', 'kloopread']);
  env.click($('lapreset')); adv(100); snap('lap reset', ['svg-loop', 'svg-kloop', 'loopread', 'kloopread']);
  // words as paths
  env.click($('gridab')); adv(1500); env.click($('gridab')); adv(1500); env.click($('gridba')); adv(1500); snap('grid', ['svg-grid', 'gridread']);
  snap('tabs', []);
}

function runScenario(html, width, before) {
  var env = stub.load(html, { width: width }), out = [], seen = {};
  if (before) before(env);
  scenario(env, function (name, ids) {
    if (seen[name]) throw new Error('scenario: step name used twice: ' + name);
    seen[name] = true;
    ids.forEach(function (id) { var el = env.$(id); out.push({ k: width + ' ' + name + ' #' + id, html: el ? el.outerHTML : '(missing)' }); });
    if (!ids.length) out.push({ k: width + ' ' + name + ' tabs', html: tabsHtml(env) });
  });
  return out;
}
function hash(s) { return crypto.createHash('sha1').update(s).digest('hex').slice(0, 16); }
function skiRuns(html, before) { return runScenario(html, 1200, before).concat(runScenario(html, 400, before)); }

var args = process.argv.slice(2);
if (args[0] === '--write-snapshot') {
  var old = fs.readFileSync(args[1], 'utf8'), snaps = skiRuns(old), o = {};
  snaps.forEach(function (s) { o[s.k] = hash(s.html); });
  fs.writeFileSync(SNAP, JSON.stringify({ source: 'post/atoms-and-probes.html, blob 1356f7b (before the calculus switch)', snapshots: o }, null, 1) + '\n');
  console.log('wrote ' + Object.keys(o).length + ' snapshots to ' + SNAP);
  process.exit(0);
}
var html = fs.readFileSync(ESSAY, 'utf8');
if (args[0] === '--diff') {
  var a = skiRuns(fs.readFileSync(args[1], 'utf8')), b = skiRuns(html), shown = 0;
  a.forEach(function (s, i) {
    if (!b[i] || b[i].html === s.html || shown > 4) return;
    shown++;
    var x = s.html, y = b[i].html, k = 0;
    while (k < x.length && x[k] === y[k]) k++;
    console.log(s.k + '\n  old: …' + x.slice(Math.max(0, k - 120), k + 200) + '\n  new: …' + y.slice(Math.max(0, k - 120), k + 200));
  });
  console.log(shown ? 'differences shown' : 'no differences');
  process.exit(0);
}

module.exports = { scenario: scenario, IDS: IDS };
if (require.main !== module) return;

/* ---------- 1. combinatory logic: the same output as before the switch ---------- */
section('Combinatory logic: every figure as before the switch');
var fixture = JSON.parse(fs.readFileSync(SNAP, 'utf8')).snapshots;
function compareSki(snaps, what) {
  var bad = [];
  snaps.forEach(function (s) { if (fixture[s.k] !== hash(s.html)) bad.push(s.k); });
  check(snaps.length === Object.keys(fixture).length, what + ': ' + snaps.length + ' snapshots, fixture has ' + Object.keys(fixture).length);
  check(bad.length === 0, what + ': ' + bad.length + ' snapshots differ, first: ' + bad.slice(0, 3).join('; '));
  console.log('  ' + what + ': ' + (snaps.length - bad.length) + '/' + snaps.length + ' snapshots identical');
}
compareSki(skiRuns(html), 'on load');
if (typeof module.exports.afterSki === 'function') module.exports.afterSki();

/* ---------- 2. the switch ---------- */
section('The calculus switch');
function attempt(what, f) {
  try { f(); check(true, what); } catch (e) { check(false, what + ': ' + (e && e.stack ? e.stack.split('\n').slice(0, 4).join(' | ') : e)); }
}
function radios(env, value) { return env.document.querySelectorAll('.calc-switch input').filter(function (i) { return i.value === value; }); }
function pick(env, value, k) { env.click(radios(env, value)[k || 0]); }
function dupIds(env) {
  var seen = {}, dup = [];
  env.document.walk(function (el) { var id = el.getAttribute('id'); if (id) { if (seen[id]) dup.push(id); seen[id] = true; } });
  return dup;
}
var nSwitch = 0;
[1200, 400].forEach(function (width) {
  var env = stub.load(html, { width: width });
  var boxes = env.document.querySelectorAll('.calc-switch');
  nSwitch = boxes.length;
  check(boxes.length === 10, width + ': ten switches, the main one and nine in figures (' + boxes.length + ')');
  check(boxes.every(function (b) { return b.getAttribute('role') === 'radiogroup' && !b.hasAttribute('hidden') && b.querySelectorAll('input[type="radio"]').length === 3; }), width + ': each switch is a radio group of three, shown');
  check(boxes.every(function (b) { return b.querySelectorAll('label').length === 3; }), width + ': every radio has a label');
  var names = boxes.map(function (b) { return b.querySelector('input').getAttribute('name'); });
  check(names.filter(function (n, i) { return names.indexOf(n) === i; }).length === names.length, width + ': each switch is its own radio group');
  check(radios(env, 'ski').every(function (i) { return i.checked; }), width + ': combinatory logic is the default');
  check(env.document.documentElement.getAttribute('data-calc') === 'ski', width + ': the page says ski');
  check(dupIds(env).length === 0, width + ': no duplicate ids on load (' + dupIds(env).join(', ') + ')');
  ['tree', 'net', 'ski', 'net', 'tree', 'ski'].forEach(function (c, k) {
    attempt(width + ': switch to ' + c + ' from the switch in figure ' + (k % boxes.length), function () {
      pick(env, c, (k * 3) % boxes.length); env.advance(3000);
    });
    check(env.window.location.hash === (c === 'ski' ? '' : '#calc=' + c), width + ': the hash after choosing ' + c + ' is ' + JSON.stringify(env.window.location.hash));
    check(env.document.documentElement.getAttribute('data-calc') === c, width + ': the page says ' + c);
    check(radios(env, c).every(function (i) { return i.checked; }) && env.document.querySelectorAll('.calc-switch input').filter(function (i) { return i.checked; }).length === boxes.length,
      width + ': every switch shows ' + c);
    check(dupIds(env).length === 0, width + ': no duplicate ids in ' + c + ' (' + dupIds(env).join(', ') + ')');
  });
  // the hash, the other way: from the address to the page
  ['#calc=net', '#calc=tree', '#mechanized', '#calc=ski'].forEach(function (h) {
    attempt(width + ': hash ' + h, function () { env.setHash(h); env.advance(2000); });
    var want = /tree|net/.exec(h) ? /tree|net/.exec(h)[0] : 'ski';
    check(env.document.documentElement.getAttribute('data-calc') === want && radios(env, want).every(function (i) { return i.checked; }), width + ': hash ' + h + ' gives ' + want);
  });
  // loading with the hash
  ['tree', 'net'].forEach(function (c) {
    var e2;
    attempt(width + ': load with #calc=' + c, function () { e2 = stub.load(html, { width: width, hash: '#calc=' + c }); e2.advance(3000); });
    if (!e2) return;
    check(e2.document.documentElement.getAttribute('data-calc') === c && radios(e2, c).every(function (i) { return i.checked; }), width + ': loaded with #calc=' + c);
    check(dupIds(e2).length === 0, width + ': no duplicate ids, loaded in ' + c);
    // every figure driven, in this calculus
    attempt(width + ': the whole scenario in ' + c, function () { scenario(e2, function () {}); });
  });
});

// combinatory logic again after a tour of the other two: still as before the switch
// (14 s for each: 42 s in all is a whole number of frames and of the periods of the looping animations, 3 and 4.2 s)
compareSki(skiRuns(html, function (env) { ['tree', 'net', 'ski'].forEach(function (c) { pick(env, c); env.advance(14000); }); }), 'after tree and nets and back');

/* ---------- 3. what each figure shows in the other calculi ---------- */
section('Figures in tree calculus and in nets');
function load(c, width) { var e = stub.load(html, { width: width || 1200, hash: c === 'ski' ? '' : '#calc=' + c }); e.advance(3000); return e; }
function cell(env, r, c) { return env.document.querySelector('#grid [data-r="' + r + '"][data-c="' + c + '"]'); }
function cellText(env, r, c) { var b = cell(env, r, c); return b.childNodes.filter(function (n) { return n.nodeType === 3; }).map(function (n) { return n.data; }).join(''); }
var T = load('tree'), N = load('net');
// the bench
var TEXP = [['not read', 'x', 'x y', 'x'], ['not read', 'x', 'x y', 'y'], ['not read', 'x', 'x y', 'z'], ['not read', 'not read', 'y', 'not read'], ['not read', 'not read', 'y', 'not read'], ['not read', 'not read', 'x', 'not read']];
var bad = [];
TEXP.forEach(function (row, r) { row.forEach(function (w, c) { if (cellText(T, r, c) !== w) bad.push(r + ',' + c + ': ' + cellText(T, r, c)); if (cellText(N, r, c) !== w) bad.push('net ' + r + ',' + c + ': ' + cellText(N, r, c)); }); });
check(bad.length === 0, 'tree bench: the readings of Tree.tree_six_terms, in both modes (' + bad.join('; ') + ')');
var pts = [0, 1, 2, 3, 4, 5].map(function (r) { return T.$('pt' + r).textContent; }).join(',');
check(pts === '1,2,3,4,4,5', 'tree bench: points 1,2,3,4,4,5 (' + pts + ')');
check(T.$('grid').querySelectorAll('thead th').length === 6, 'tree bench: four probe columns');
check(/triage/.test(T.$('grid').querySelector('thead').textContent), 'tree bench: a column headed triage');
var counts = [];
for (var r = 0; r < 6; r++) for (var c = 0; c < 4; c++) { var sp = cell(N, r, c).querySelector('.ncount'); counts.push(sp ? sp.textContent : '?'); }
check(counts.join(' ') === '0 7 7 43 0 8 8 46 0 9 9 49 0 2 9 50 0 2 10 52 0 1 3 35', 'net bench: interaction counts (' + counts.join(' ') + ')');
check(T.$('grid').querySelectorAll('.ncount').length === 0, 'tree bench: no interaction counts');
T.click(cell(T, 2, 3)); T.advance(20000);
check(/z/.test(T.$('benchverdict').textContent) && /triage/.test(T.$('benchsay').textContent), 'tree bench: the triage cell of S K (△K) runs and reads z');
N.click(cell(N, 1, 3)); N.advance(20000);
check(/46 interactions in all/.test(N.$('benchrun').textContent), 'net bench: the run line counts the interactions (' + N.$('benchrun').textContent.slice(-60) + ')');
check(/run data/.test(N.$('benchread').textContent) && /same number in every order/.test(N.$('benchread').textContent), 'net bench: the readout calls the counts run data, the same number in every order');
// running
check(T.$('focus').options.length === 19, 'tree hero: nineteen terms (' + T.$('focus').options.length + ')');
check(/^Nineteen terms/.test(T.$('heroread').textContent), 'tree hero: the readout counts nineteen terms');
check(T.$('svg-hero').querySelectorAll('rect.n-rect').length === 19, 'tree hero: nineteen boxes');
check(N.$('focus').options.length === 14, 'net hero: fourteen terms, the loop left out (' + N.$('focus').options.length + ')');
N.change(N.$('focus'), '1'); N.advance(200);
check(/44 nets|forty-four nets/.test(N.$('heroread').textContent) || / nets, placed/.test(N.$('heroread').textContent), 'net hero: the lattice of K a (I b) (' + N.$('heroread').textContent.slice(0, 80) + ')');
check(N.$('svg-hero').querySelectorAll('circle.n-dot').length === 44, 'net hero: 44 nets drawn for K a (I b)');
var lens = {};
['outer', 'inner', 'random', 'random', 'random'].forEach(function (o) {
  N.change(N.$('order'), o); N.advance(30000);
  var m = /Finished in (\w+) interactions/.exec(N.$('stepinfo').textContent);
  lens[m ? m[1] : N.$('stepinfo').textContent] = true;
});
check(Object.keys(lens).join() === 'ten', 'net hero: every order finishes in ten interactions (' + Object.keys(lens).join(' / ') + ')');
check(/same length/.test(N.$('heroread').textContent), 'net hero: the readout says the length is the same whichever order');
N.click(N.document.querySelector('[data-l="1"]')); N.change(N.$('time'), '0'); N.advance(100);
check(N.$('svg-hero').querySelectorAll('polygon.agent').length > 0 && N.$('svg-hero').querySelectorAll('path.wire.next').length === 1, 'net hero: one step draws the net, with the next pair marked');
N.click(N.document.querySelector('[data-l="3"]'));
check(N.document.querySelector('[data-l="3"]').textContent === 'All the states' && T.document.querySelector('[data-l="3"]').textContent === 'All the terms', 'the third view is called All the states for nets');
// equalities
T.click(T.$('addrule')); T.advance(2000);
check(/unsound/.test(T.$('baseread').textContent), 'tree equalities: with the rule, the readout says it is unsound');
check(T.$('svg-base').querySelectorAll('path.edge.leak').length === 2, 'tree equalities: the two steps of the rule are drawn red');
T.click(T.document.querySelector('[data-m="test"]')); T.advance(1500);
check(/^Nineteen descriptions, five points/.test(T.$('baseread').textContent), 'tree equalities: under probes, five points (' + T.$('baseread').textContent.slice(0, 40) + ')');
// reading code
check(T.$('readcode').checked && T.$('readcode').disabled && N.$('readcode').checked && N.$('readcode').disabled, 'reading code: the box is ticked and fixed in tree calculus and nets');
pick(T, 'ski'); T.advance(2000);
check(!T.$('readcode').checked && !T.$('readcode').disabled, 'reading code: back in combinatory logic the box is free again');
pick(T, 'tree'); T.advance(2000);
// types
T.change(T.$('pred'), 'evalI'); T.advance(100);
check(/a probe defines it/.test(T.$('paintread').textContent), 'tree types: runs to I is defined by a probe');
T.change(T.$('pred'), 'probeA'); T.advance(100);
check(T.$('svg-paint').querySelectorAll('rect.paint.pb').length === 6, 'tree types: six terms return a when applied to a');
T.change(T.$('pred'), 'hasK'); T.advance(100);
check(/leak/.test(T.$('verdict').textContent), 'tree types: mentions K leaks');
// the lemma
check(/△△ ∈ ⟦A → B → A⟧/.test(T.$('svg-lemma').textContent) || (T.click(T.document.querySelector('[data-k="2"]')), T.advance(1500), /△△ ∈/.test(T.$('svg-lemma').textContent)), 'tree lemma: K is written △△');
// the loop with exits
check(T.$('svg-exit').querySelectorAll('rect.n-rect').length === 6, 'tree exits: five terms of the loop and a');
N.advance(1000);
var c0 = Number(N.$('svg-exit').querySelector('text.ev').textContent.replace('…', ''));
N.advance(3000);
var c1 = Number(N.$('svg-exit').querySelector('text.ev').textContent.replace('…', ''));
check(c1 > c0 && c0 >= 0, 'net exits: the count of interactions rises (' + c0 + ' then ' + c1 + ')');
check(N.$('svg-exit').querySelectorAll('rect.n-rect.cur').length === 1, 'net exits: the result port reads a');
check(/lazy table/.test(N.document.querySelectorAll('.calc-note[data-calc="net"]').map(function (p) { return p.textContent; }).join(' ')), 'net exits: the note mentions the lazy table');
// fibres
check(T.$('fib-a').querySelectorAll('rect.n-rect').length === 4 && T.$('fib-w').querySelectorAll('rect.n-rect').length === 5, 'tree fibres: four terms over a, five in the loop');
check(N.$('fib-a').querySelectorAll('circle.n-dot').length === 44, 'net fibres: the lattice of K a (I b)');
[1, 2, 3].forEach(function (k) { N.click(N.document.querySelector('[data-f="' + k + '"]')); N.advance(4000); });
check(/ten interactions/.test(N.$('fread').textContent), 'net fibres: every run ten interactions');
// the counter
T.click(T.$('lapfwd')); T.advance(6000);
check(/evidence is 1\./.test(T.$('loopread').textContent), 'tree counter: a lap adds one (' + T.$('loopread').textContent + ')');
T.click(T.$('ksend')); T.advance(7000);
check(/as 0 by one route and as 1 by the other/.test(T.$('kloopread').textContent), 'tree counter: absorbed inside K a (ω ω)');
check(N.$('svg-loop').querySelectorAll('rect.n-rect').length === 5, 'net counter: the tree loop is shown');

/* ---------- 4. the notes ---------- */
section('Calculus notes and marks');
var notes = T.document.querySelectorAll('.calc-note');
check(notes.every(function (p) { return /^(tree|net)( (tree|net))?$/.test(p.getAttribute('data-calc')); }), 'every calc-note names its calculus');
var figs = T.document.querySelectorAll('figure').filter(function (f) { return f.querySelector('.calc-switch'); });
check(figs.length === 9, 'nine figures carry a switch (' + figs.length + ')');
figs.forEach(function (f) {
  var title = f.querySelector('.fig-title').textContent;
  ['tree', 'net'].forEach(function (c) {
    check(f.querySelectorAll('.calc-note').some(function (p) { return p.getAttribute('data-calc').split(' ').indexOf(c) >= 0; }), 'figure "' + title + '" has a note for ' + c);
  });
});
var LEAN = ['Tree.probes_read_code', 'Tree.calculus_confluent', 'Calculus.probeEq_of_conv', 'Calculus.codeEq_iff_conv', 'Calculus.probeEq_plug',
  'Tree.tree_six_terms', 'Tree.tree_six_distinct', 'Tree.sk_unsound', 'Tree.fundamental_K', 'Tree.fundamental_S', 'Tree.fundamental_triage', 'Tree.omega_cycle', 'Diamond.equal_lengths', 'Diamond.length_le', 'SKI.six_terms'];
var marks = T.document.querySelectorAll('.calc-note a.lean, .calc-bar a.lean');
check(marks.length > 0 && marks.every(function (a) { var n = a.getAttribute('data-lean'); return LEAN.indexOf(n) >= 0 && a.getAttribute('title') === 'Mechanized: ' + n && a.getAttribute('aria-label') === 'Mechanized: ' + n; }), 'lean marks in the notes use known names, in the essay\'s format (' + marks.length + ')');
var tsl = T.document.querySelectorAll('a.ts');
check(tsl.length > 0 && tsl.every(function (a) {
  return /^https:\/\/github\.com\/maxinelevesque\/tree-semantics\/blob\/5147cfad47f152f30dac95f8344105c867561b5c\/TreeCalculus\/\w+\.lean#L\d+$/.test(a.getAttribute('href')) && /^Mechanized in tree-semantics: /.test(a.getAttribute('title'));
}), 'tree-semantics links are pinned and titled (' + tsl.length + ')');
check(!/disp-ic/.test(html), 'nothing from docs/interaction-nets/disp-ic.md');
check(/html\[data-calc="tree"\] \.calc-note\[data-calc~="tree"\]/.test(html), 'the stylesheet shows a note only in its calculus');

/* ---------- 5. the tree bundle's layout ---------- */
section('The tree bundle, laid out');
// the width of a box, as the essay estimates it where nothing can be measured: 7.6 a character, 1.15 em (14.4) a △
function estW(s) { var d = s.split('△').length - 1; return (s.length - d) * 7.6 + d * 14.4 + 14; }
// sample points along a drawn arrow: a line, one quadratic or cubic Bézier, or a polyline
function arrowPoints(l) {
  var pts = [], s, u;
  if (l.localName === 'line') { for (s = 0; s <= 40; s++) { u = s / 40; pts.push([+l.getAttribute('x1') + (l.getAttribute('x2') - l.getAttribute('x1')) * u, +l.getAttribute('y1') + (l.getAttribute('y2') - l.getAttribute('y1')) * u]); } return pts; }
  var d = l.getAttribute('d'), m = d.match(/-?[\d.]+/g).map(Number);
  if (/C/.test(d)) { for (s = 0; s <= 60; s++) { u = s / 60; var v = 1 - u, w = [v * v * v, 3 * u * v * v, 3 * u * u * v, u * u * u]; pts.push([w[0] * m[0] + w[1] * m[2] + w[2] * m[4] + w[3] * m[6], w[0] * m[1] + w[1] * m[3] + w[2] * m[5] + w[3] * m[7]]); } return pts; }
  if (/Q/.test(d)) { for (s = 0; s <= 40; s++) { u = s / 40; var a = (1 - u) * (1 - u), b = 2 * u * (1 - u), c = u * u; pts.push([a * m[0] + b * m[2] + c * m[4], a * m[1] + b * m[3] + c * m[5]]); } return pts; }
  for (var i = 0; i + 3 < m.length; i += 2) for (s = 0; s < 20; s++) { u = s / 20; pts.push([m[i] + (m[i + 2] - m[i]) * u, m[i + 1] + (m[i + 3] - m[i + 1]) * u]); }
  pts.push([m[m.length - 2], m[m.length - 1]]);
  return pts;
}
function bundleChecks(e, width, what) {
  var svg = e.$('svg-hero'), vb = svg.getAttribute('viewBox').split(' ').map(Number);
  var rects = svg.querySelectorAll('rect.n-rect').map(function (r) { return { x: +r.getAttribute('x'), y: +r.getAttribute('y'), w: +r.getAttribute('width'), h: +r.getAttribute('height'), t: r.parentNode.querySelector('text').textContent }; });
  var over = 0, outside = 0;
  rects.forEach(function (a, i) {
    if (a.x < vb[0] || a.y < vb[1] || a.x + a.w > vb[0] + vb[2] || a.y + a.h > vb[1] + vb[3]) outside++;
    rects.forEach(function (b, j) { if (j > i && a.x < b.x + b.w + 4 && b.x < a.x + a.w + 4 && a.y < b.y + b.h + 4 && b.y < a.y + a.h + 4) over++; });
  });
  check(over === 0, what + ': no two boxes of the tree bundle touch');
  check(outside === 0, what + ': every box inside the view box ' + vb.join(' '));
  // no arrow crosses a box it does not join; a curve also keeps 3 clear of every box
  var crossings = 0, notOne = [], short = [];
  svg.querySelectorAll('.edge').forEach(function (l) {
    var pts = arrowPoints(l), curve = l.localName === 'path' && /C/.test(l.getAttribute('d')), m = curve ? -3 : 2;
    if (l.localName === 'path' && !/^M -?[\d.]+ -?[\d.]+ [QC]( -?[\d.]+)+$/.test(l.getAttribute('d'))) notOne.push(l.getAttribute('d'));
    var len = 0;
    for (var k = 1; k < pts.length; k++) len += Math.sqrt(Math.pow(pts[k][0] - pts[k - 1][0], 2) + Math.pow(pts[k][1] - pts[k - 1][1], 2));
    if (len < 12) short.push(r1(len));
    rects.forEach(function (r) { if (pts.slice(2, -2).some(function (p) { return p[0] > r.x + m && p[0] < r.x + r.w - m && p[1] > r.y + m && p[1] < r.y + r.h - m; })) crossings++; });
  });
  check(crossings === 0, what + ': no arrow crosses a box, and every curve clears the boxes by 3 (' + crossings + ')');
  check(notOne.length === 0, what + ': every arrow that is not straight is one smooth Bézier curve, with no corners (' + notOne.join(' | ') + ')');
  check(short.length === 0, what + ': every arrow is at least 12 long (' + short.join(', ') + ')');
  return { svg: svg, vb: vb, rects: rects };
}
function r1(x) { return Math.round(x * 10) / 10; }
[1200, 400].forEach(function (width) {
  var e = load('tree', width), b = bundleChecks(e, width, String(width)), vb = b.vb, rects = b.rects;
  var top = Math.min.apply(null, rects.map(function (r) { return r.y; }));
  check(top - vb[1] <= 40, width + ': no empty band above the bundle: the highest box is ' + r1(top - vb[1]) + ' below the top of the view box (at most 40)');
  if (width <= 820) check(vb[2] <= 440, width + ': the narrow bundle fits its 440 px frame unscaled (' + vb[2] + ' wide)');
  var bad = rects.filter(function (r) { return Math.abs(r.w - estW(r.t)) > 0.15; });
  check(bad.length === 0, width + ': box widths allow 1.15 em for each △ (' + bad.map(function (r) { return r.t + ' ' + r.w; }).join('; ') + ')');
  console.log('  ' + width + ': view box ' + vb.join(' ') + ', ' + rects.length + ' boxes, ' + b.svg.querySelectorAll('path.edge').length + ' arrows not straight');
});
// in a browser the labels with △ are measured (getComputedTextLength); the stand-in makes each △ 2 em wide
[1200, 400].forEach(function (width) {
  var wide = function (s) { var d = s.split('△').length - 1; return (s.length - d) * 7.6 + d * 25; };
  var e = stub.load(html, { width: width, hash: '#calc=tree', textLength: wide });
  e.advance(3000);
  var b = bundleChecks(e, width, width + ', measured'), bad = b.rects.filter(function (r) { return Math.abs(r.w - (/△/.test(r.t) ? r1(wide(r.t) + 14) : estW(r.t))) > 0.15; });
  check(bad.length === 0, width + ', measured: a box with △ is as wide as its measured label, and 14 (' + bad.map(function (r) { return r.t + ' ' + r.w; }).join('; ') + ')');
  check(dupIds(e).length === 0, width + ', measured: no duplicate ids');
});

/* ---------- 6. the net of one step: labels ---------- */
section('Nets, one step: the labels of free ports');
[1200, 400].forEach(function (width) {
  var e = load('net', width), nets = 0, clash = [], hit = [];
  e.click(e.document.querySelector('[data-l="1"]'));
  e.$('focus').options.forEach(function (o) {
    e.change(e.$('focus'), o.value); e.advance(100);
    ['outer', 'inner', 'random'].forEach(function (ord) {
      e.change(e.$('order'), ord); e.advance(100);
      for (var k = 0; k <= Number(e.$('time').max); k++) {
        e.change(e.$('time'), String(k)); e.advance(20);
        var svg = e.$('svg-hero'), labs = [], tris = [];
        svg.querySelectorAll('text.freep, text.lab').forEach(function (t) {
          var s = t.textContent, w = s.length * (/freep/.test(t.getAttribute('class')) ? 7.6 : 6.4), x = +t.getAttribute('x'), y = +t.getAttribute('y');
          labs.push({ s: s, x0: x - w / 2, x1: x + w / 2, y0: y - 10, y1: y + 3 });
        });
        svg.querySelectorAll('polygon.agent').forEach(function (p) {
          var q = p.getAttribute('points').split(' ').map(function (xy) { return xy.split(',').map(Number); });
          tris.push({ x0: Math.min(q[0][0], q[1][0], q[2][0]), x1: Math.max(q[0][0], q[1][0], q[2][0]), y0: Math.min(q[0][1], q[1][1], q[2][1]), y1: Math.max(q[0][1], q[1][1], q[2][1]) });
        });
        function meet(a, b) { return a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1; }
        labs.forEach(function (a, i) {
          labs.forEach(function (b, j) { if (j > i && meet(a, b)) clash.push(o.textContent + ' ' + ord + ' ' + k + ': ' + a.s + '/' + b.s); });
          tris.forEach(function (t) { if (meet(a, t)) hit.push(o.textContent + ' ' + ord + ' ' + k + ': ' + a.s); });
        });
        nets++;
      }
    });
  });
  check(nets > 250, width + ': the one-step view drawn for every net of every term, in three orders (' + nets + ')');
  check(clash.length === 0, width + ': no two labels of free ports overlap (' + clash.slice(0, 3).join('; ') + ')');
  check(hit.length === 0, width + ': no label overlaps an agent (' + hit.slice(0, 3).join('; ') + ')');
  console.log('  ' + width + ': ' + nets + ' nets drawn, labels apart');
});

/* ---------- 7. figures: keyboard, captions and labels by mode, reduced motion, a phone's width ---------- */
section('Keyboard, captions by mode, reduced motion, phone width');
// the text a reader sees of an element in a calculus: words marked data-only for other calculi are left out
function shownText(el, mode) {
  return (function walk(n) {
    if (n.nodeType === 3) return n.data;
    var only = n.getAttribute && n.getAttribute('data-only');
    if (only && only.split(' ').indexOf(mode) < 0) return '';
    return n.childNodes.map(walk).join('');
  })(el).replace(/\s+/g, ' ').trim();
}
function figOf(env, id) { return env.$(id).closest('figure'); }
// hidden boxes leave the tab order, the pointer and the accessibility tree
['ski', 'tree'].forEach(function (c) {
  var e = load(c), bad = [];
  function audit(what) {
    e.$('svg-hero').querySelectorAll('g.pick').forEach(function (g) {
      var gone = String(g.style.opacity) === '0', ok = gone
        ? g.getAttribute('tabindex') === '-1' && g.getAttribute('aria-hidden') === 'true' && g.style.pointerEvents === 'none'
        : g.getAttribute('tabindex') === '0' && !g.hasAttribute('aria-hidden') && !g.style.pointerEvents;
      if (!ok) bad.push(what + ': ' + g.getAttribute('aria-label'));
    });
  }
  [1, 2, 3, 4, 1].forEach(function (l) {
    e.click(e.document.querySelector('[data-l="' + l + '"]')); e.advance(200); audit('view ' + l);
    e.click(e.$('play')); e.advance(1500); audit('view ' + l + ', playing');
  });
  check(bad.length === 0, c + ': every box out of sight is out of the tab order and every box in sight is in it (' + bad.slice(0, 3).join('; ') + ')');
  // a focused box that disappears hands the focus to the Term selector
  e.change(e.$('focus'), '1'); e.advance(200); e.change(e.$('time'), '0'); e.advance(50);
  var start = e.$('svg-hero').querySelectorAll('g.pick')[1];
  start.focus(); e.click(e.$('play')); e.advance(3000);
  check(e.document.activeElement === e.$('focus'), c + ': the focus moves to Term when its box leaves the view');
  e.click(e.document.querySelector('[data-l="3"]')); e.advance(100);
  check(e.$('svg-hero').querySelectorAll('g.pick').every(function (g) { return g.getAttribute('tabindex') === '0'; }), c + ': in All the terms every box can be reached');
  // a term of the loop: Order gives way to the label of the cycle shown
  var loopAt = e.$('focus').options.filter(function (o) { return /ω|S I I/.test(o.textContent); })[0].value;
  e.change(e.$('focus'), loopAt); e.advance(200);
  check(e.$('order').parentNode.hidden && !e.$('ordercyc').hidden && /shown cycle/.test(e.$('ordercyc').textContent), c + ': for a term of the loop, Order says it shows the cycle');
  e.change(e.$('focus'), '0'); e.advance(200);
  check(!e.$('order').parentNode.hidden && e.$('ordercyc').hidden, c + ': for another term, Order is back');
});
// captions, titles and labels, by mode
var S0 = load('ski'), modes = { ski: S0, tree: T, net: N };
var cap = {};
Object.keys(modes).forEach(function (m) {
  cap[m] = {
    hero: shownText(figOf(modes[m], 'svg-hero').querySelector('figcaption'), m),
    bench: shownText(figOf(modes[m], 'grid').querySelector('figcaption'), m),
    benchTitle: shownText(figOf(modes[m], 'grid').querySelector('.fig-title'), m),
    exitH: shownText(modes[m].$('svg-exit').parentNode.querySelector('h3'), m),
    counter: shownText(figOf(modes[m], 'svg-loop').querySelector('figcaption'), m),
    counterTitle: shownText(figOf(modes[m], 'svg-loop').querySelector('.fig-title'), m),
    fib: shownText(figOf(modes[m], 'fib-a').querySelector('figcaption'), m)
  };
});
check(/^Each box is a term/.test(cap.ski.hero) && /^Each box is a term/.test(cap.tree.hero) && /^Each dot is a net/.test(cap.net.hero) && !/box/.test(cap.net.hero), 'running: the caption speaks of boxes for terms and of dots for nets');
check(/left to right/.test(cap.net.hero), 'running: in nets the caption says which way time runs');
check(cap.ski.benchTitle === 'Six terms under three probes' && cap.tree.benchTitle === 'Six terms under four probes' && cap.net.benchTitle === 'Six terms under four probes', 'bench: three probes, or four with triage (' + cap.tree.benchTitle + ')');
check(/run data/.test(cap.net.bench) && !/run data/.test(cap.tree.bench) && !/run data/.test(cap.ski.bench), 'bench: only in nets does the caption call the counts run data');
check(cap.net.exitH === 'An answer before the run ends' && cap.ski.exitH === 'A loop with exits' && cap.tree.exitH === 'A loop with exits', 'exits: the net panel is an answer before the run ends');
check(/S-step at the root/.test(cap.tree.counter) && /S-step at the root/.test(cap.net.counter) && /each use of the S-rule/.test(cap.ski.counter), 'counter: in trees and nets the caption names the S-step at the root');
check(/tree-calculus example/.test(cap.net.counterTitle) && !/tree-calculus/.test(cap.tree.counterTitle), 'counter: in nets the title says the panels are a tree example');
check(/two runs/.test(cap.ski.fib) && /three runs/.test(cap.tree.fib) && /every net/.test(cap.net.fib), 'fibres: the caption describes the panels of each mode');
var ARIA_IDS = ['svg-hero', 'svg-base', 'svg-paint', 'svg-code', 'svg-lemma', 'svg-exit', 'fib-a', 'fib-w', 'svg-loop', 'svg-kloop'];
var page = stub.load(html, { width: 1200 });     // the labels as written in the page
check(ARIA_IDS.every(function (id) { return S0.$(id).getAttribute('aria-label') === page.$(id).getAttribute('aria-label'); }), 'labels: combinatory logic keeps the accessible descriptions written in the page');
check(ARIA_IDS.every(function (id) { return !/[Ff]ourteen|three terms in a cycle/.test(T.$(id).getAttribute('aria-label')) && !/[Ff]ourteen|three terms in a cycle/.test(N.$(id).getAttribute('aria-label')); }), 'labels: no tree or net description speaks of fourteen terms or a cycle of three');
check(/nets/.test(N.$('svg-hero').getAttribute('aria-label')) && /[Nn]ineteen/.test(T.$('svg-hero').getAttribute('aria-label')), 'labels: running is described as nets in nets and as nineteen terms in trees');
// the three equalities: a caption that holds when the rule is added in trees
var T2 = load('tree');
check(/coarser than the one before/.test(T2.$('basecap').textContent), 'equalities: without the rule the caption orders the three equalities');
T2.click(T2.$('addrule')); T2.advance(1500);
check(/probes still distinguish/.test(T2.$('basecap').textContent), 'equalities: with the rule in trees the caption says it merges what probes distinguish');
S0.click(S0.$('addrule')); S0.advance(1500);
check(/coarser than the one before/.test(S0.$('basecap').textContent), 'equalities: with the rule in combinatory logic the caption is unchanged');
S0.click(S0.$('addrule')); S0.advance(1500);
// a predicate closed: what is shown shaded is pressed, and a hand edit starts from it
var P = load('ski');
P.change(P.$('pred'), 'hasK'); P.advance(100); P.click(P.$('closeit')); P.advance(3000);
var gs = P.$('svg-paint').querySelectorAll('g.pick'), shaded = gs.map(function (g) { return /paint|spread/.test(g.querySelector('rect.n-rect').getAttribute('class')); });
check(gs.every(function (g, i) { return g.getAttribute('aria-pressed') === String(shaded[i]); }), 'types: after closing, aria-pressed follows the shading shown');
var k = shaded.indexOf(true, shaded.indexOf(true) + 1);
P.click(gs[k]); P.advance(100);
var gs2 = P.$('svg-paint').querySelectorAll('g.pick'), now = gs2.map(function (g) { return /paint/.test(g.querySelector('rect.n-rect').getAttribute('class')); });
check(P.$('pred').value === 'custom' && now.every(function (x, i) { return x === (i === k ? false : shaded[i]); }), 'types: a box selected after closing starts from the closed shading');
// reduced motion: nothing moves until the reader asks
var STILL = ['svg-pent', 'svg-exit', 'fib-a', 'fib-w', 'svg-hero', 'grid', 'svg-loop', 'svg-kloop', 'svg-lemma'];
['ski', 'tree', 'net'].forEach(function (c) {
  var e = stub.load(html, { width: 1200, reducedMotion: true, hash: c === 'ski' ? '' : '#calc=' + c });
  e.advance(3000);
  var a = STILL.map(function (id) { return e.$(id).outerHTML; });
  e.advance(15000);
  var moved = STILL.filter(function (id, i) { return e.$(id).outerHTML !== a[i]; });
  check(moved.length === 0, c + ', reduced motion: no figure changes by itself (' + moved.join(', ') + ')');
  [1, 2, 3].forEach(function (l) { e.click(e.document.querySelector('[data-f="' + l + '"]')); e.advance(300); });
  var f = e.$('fib-w').outerHTML + e.$('fib-a').outerHTML; e.advance(10000);
  check(f === e.$('fib-w').outerHTML + e.$('fib-a').outerHTML, c + ', reduced motion: a view of the fibres chosen by hand stands still');
  check(e.$('exitpause').textContent === 'Play' && e.$('fpause').textContent === 'Play', c + ', reduced motion: the moving figures start paused');
  e.click(e.$('exitpause')); e.advance(100);
  var p0 = e.$('svg-pent').outerHTML + e.$('svg-exit').outerHTML; e.advance(2500);
  check(p0 !== e.$('svg-pent').outerHTML + e.$('svg-exit').outerHTML, c + ', reduced motion: Play sets the two fibres moving');
  e.click(e.$('exitpause')); e.advance(100);
  var p1 = e.$('svg-pent').outerHTML + e.$('svg-exit').outerHTML; e.advance(5000);
  check(p1 === e.$('svg-pent').outerHTML + e.$('svg-exit').outerHTML, c + ', reduced motion: Pause stops them');
});
// normal motion: Pause stops the repeating figures, Play starts them again
(function () {
  var e = stub.load(html, { width: 1200 });
  e.advance(1000);
  check(e.$('exitpause').textContent === 'Pause' && e.$('fpause').textContent === 'Pause', 'pause: the moving figures start playing');
  e.click(e.$('exitpause')); e.click(e.document.querySelector('[data-f="2"]')); e.click(e.$('fpause')); e.advance(100);
  var a = e.$('svg-exit').outerHTML + e.$('fib-w').outerHTML; e.advance(4000);
  check(a === e.$('svg-exit').outerHTML + e.$('fib-w').outerHTML, 'pause: Pause holds both repeating figures still');
  e.click(e.$('exitpause')); e.click(e.$('fpause')); e.advance(1500);
  check(a !== e.$('svg-exit').outerHTML + e.$('fib-w').outerHTML, 'pause: Play starts them again');
})();
check(/\.grid-wrap \{ overflow-x: auto;/.test(html) && !/animation: pulse/.test(html) && /prefers-reduced-motion: reduce\) \{\n  [^}]*\.n-dot, \.lattice \{ transition: none; \}/.test(html), 'stylesheet: the table scrolls in its frame if need be, the leak is steady, and net dots do not fade under reduced motion');
/* The net bench at 390 px. There is no layout engine here, so the width is estimated from the stylesheet's
   narrow rules (under 640 px): type 0.8rem, cells 5 px padding and a 1 px border, 4 px between columns, the
   count under its reading, a reading wrapping at spaces. A character of IBM Plex Mono is 0.6 em, of Plex Sans at
   most 0.56 em; a △ 1.15 em. Headers and row labels do not wrap. The column is 390 − 2 × 18 = 354 px. */
function textW(s, em, mono) { var d = s.split('△').length - 1; return (s.length - d) * em * (mono ? 0.6 : 0.56) + d * em * 1.15; }
[['tree', T], ['net', N]].forEach(function (pair) {
  var e = stub.load(html, { width: 390, hash: '#calc=' + pair[0] }); e.advance(3000);
  var grid = e.$('grid'), rows = grid.querySelectorAll('tr'), cols = [];
  var G = 12.8, HEAD = 0.82 * 16, CELL = 0.94 * G;
  rows.forEach(function (tr) {
    tr.children.forEach(function (td, c) {
      var w;
      if (td.localName === 'th' && td.parentNode.parentNode.localName === 'thead') {
        var code = td.querySelector('code');
        w = code ? textW(code.textContent, HEAD, true) : textW(td.textContent, HEAD, false);
      } else if (td.getAttribute('scope') === 'row') w = textW(td.textContent, CELL, true);
      else if (td.querySelector('.cell')) {
        var b = td.querySelector('.cell'), mono = !/sealed/.test(b.getAttribute('class'));
        var read = b.childNodes.filter(function (n) { return n.nodeType === 3; }).map(function (n) { return n.data; }).join('');
        var cnt = b.querySelector('.ncount'), words = read.split(' ').map(function (x) { return textW(x, CELL, mono); });
        w = Math.max(Math.max.apply(null, words), cnt ? textW(cnt.textContent, 0.8 * CELL, false) : 0) + 12;
      } else w = textW(td.textContent, G, false);
      cols[c] = Math.max(cols[c] || 0, w + 4);
    });
  });
  var total = Math.round(cols.reduce(function (a, x) { return a + x; }, 0));
  check(total <= 354, pair[0] + ' bench at 390 px: the table fits the 354 px column (estimated ' + total + ' px)');
  console.log('  ' + pair[0] + ' bench at 390 px: about ' + total + ' px wide');
  // and nothing in the notes is wider than the column: unbreakable code is short
  var wide = e.document.querySelectorAll('.calc-note code').filter(function (c) { return !/long/.test(c.getAttribute('class') || '') && textW(c.textContent, 0.86 * 0.82 * 16, true) > 342; });
  check(wide.length === 0, pair[0] + ' at 390 px: no unbreakable code in a note is wider than the column (' + wide.map(function (c) { return c.textContent; }).join('; ') + ')');
});

console.log('\n' + passes + ' checks passed, ' + failures + ' failed.');
if (failures) process.exit(1);
