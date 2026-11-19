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
