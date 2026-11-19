/* The essay under a stub DOM: node post/lab/essay-test.js
   1. Combinatory logic: a fixed scenario of clicks and fake time over every figure, at a wide and
      a narrow width. The serialised figures are hashed and compared with essay-ski-snapshot.json,
      which was taken from the essay before the calculus switch was added (blob 1356f7b).
      Regenerate (only from that version!) with
        node post/lab/essay-test.js --write-snapshot OLD.html
      and show the differences against an old copy with
        node post/lab/essay-test.js --diff OLD.html
   2. The switch: every mode, every figure rendered and driven without exceptions; no duplicate ids;
      the hash round-trips; the calculus notes show only in their mode.
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
check(/same for every order/.test(N.$('benchread').textContent), 'net bench: the readout says the count is the same for every order');
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
  'Tree.tree_six_terms', 'Tree.tree_six_distinct', 'Tree.sk_unsound', 'Tree.fundamental_K', 'Tree.fundamental_S', 'Tree.fundamental_triage', 'Tree.omega_cycle', 'Diamond.equal_lengths', 'Diamond.length_le'];
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
[1200, 400].forEach(function (width) {
  var e = load('tree', width), svg = e.$('svg-hero'), vb = svg.getAttribute('viewBox').split(' ').map(Number);
  var rects = svg.querySelectorAll('rect.n-rect').map(function (r) { return { x: +r.getAttribute('x'), y: +r.getAttribute('y'), w: +r.getAttribute('width'), h: +r.getAttribute('height'), t: r.parentNode.querySelector('text').textContent }; });
  var over = 0, outside = 0;
  rects.forEach(function (a, i) {
    if (a.x < vb[0] || a.y < vb[1] || a.x + a.w > vb[0] + vb[2] || a.y + a.h > vb[1] + vb[3]) outside++;
    rects.forEach(function (b, j) { if (j > i && a.x < b.x + b.w + 4 && b.x < a.x + a.w + 4 && a.y < b.y + b.h + 4 && b.y < a.y + a.h + 4) over++; });
  });
  check(over === 0, width + ': no two boxes of the tree bundle touch');
  check(outside === 0, width + ': every box inside the view box ' + vb.join(' '));
  // no arrow crosses a box it does not join
  var crossings = 0;
  svg.querySelectorAll('.edge').forEach(function (l) {
    var pts = [];
    if (l.localName === 'line') { for (var s = 0; s <= 40; s++) { var u = s / 40; pts.push([+l.getAttribute('x1') + (l.getAttribute('x2') - l.getAttribute('x1')) * u, +l.getAttribute('y1') + (l.getAttribute('y2') - l.getAttribute('y1')) * u]); } }
    else if (/Q/.test(l.getAttribute('d'))) { var m = l.getAttribute('d').match(/-?[\d.]+/g).map(Number); for (var s2 = 0; s2 <= 40; s2++) { var v = s2 / 40, a = (1 - v) * (1 - v), b = 2 * v * (1 - v), c = v * v; pts.push([a * m[0] + b * m[2] + c * m[4], a * m[1] + b * m[3] + c * m[5]]); } }
    else { var q = l.getAttribute('d').match(/-?[\d.]+/g).map(Number); for (var i = 0; i + 3 < q.length; i += 2) for (var s3 = 0; s3 < 20; s3++) { var w = s3 / 20; pts.push([q[i] + (q[i + 2] - q[i]) * w, q[i + 1] + (q[i + 3] - q[i + 1]) * w]); } pts.push([q[q.length - 2], q[q.length - 1]]); }
    rects.forEach(function (r) { if (pts.slice(2, -2).some(function (p) { return p[0] > r.x + 2 && p[0] < r.x + r.w - 2 && p[1] > r.y + 2 && p[1] < r.y + r.h - 2; })) crossings++; });
  });
  check(crossings === 0, width + ': no arrow crosses a box (' + crossings + ')');
  console.log('  ' + width + ': view box ' + vb.join(' ') + ', ' + rects.length + ' boxes, ' + svg.querySelectorAll('path.edge').length + ' arrows not straight');
});

console.log('\n' + passes + ' checks passed, ' + failures + ' failed.');
if (failures) process.exit(1);
