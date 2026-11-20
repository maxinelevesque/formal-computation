/* Interaction nets for tree calculus: the eager table of tree-semantics
   (TreeCalculus/IxTree.lean: treeSig, ruleAL … ruleEF, eagerTable), on the port-graph
   substrate of TreeCalculus/IxCore.lean (fire), with compilation as in IxTreeCompile.lean
   and the structural read-back of IxTreeRegion.lean, extended to read unfinished parts.

   Agents and ports. Port 0 is principal; port i+1 is auxiliary port i. Auxiliary order:
     L ()  S (child)  F (left, right)  A (arg, res)  T (y, z, res)  Sel (w, x, y, res)
     D (out0, out1)  E ()
   L, S, F are constructors (producers); A, T, Sel, D, E are consumers. A rule's boundary
   lists the left (consumer) agent's auxiliary ports, then the right (constructor) agent's.

   A net: { kind: {id: Kind}, link: {port: port}, next: fresh id, loops: closed loops,
            steps: interactions fired so far (bookkeeping, not part of the key) }.
   Port names: 'id.i' for agent ports, '@' for the result (free port 0), '$x' for the free
   wire of the variable x. The net is never mutated: fire returns a new net. */
(function (root) {
  var CALC = root.CALC || (root.CALC = {});
  var tree = CALC.tree || (typeof require === 'function' ? require('./tree.js') : null);

  var ARITY = { L: 0, S: 1, F: 2, A: 2, T: 3, Sel: 4, D: 2, E: 0 };
  var PRODUCER = { L: true, S: true, F: true };
  var AUX = { L: [], S: ['child'], F: ['left', 'right'], A: ['arg', 'res'], T: ['y', 'z', 'res'],
              Sel: ['w', 'x', 'y', 'res'], D: ['out0', 'out1'], E: [] };

  /* ---------- the fifteen rules (IxTree.lean), transcribed: 'cK.J' = cell K slot J, 'bI' = boundary I ---------- */
  function R(left, right, kinds, links, name) {
    return { left: left, right: right, code: left + right, kinds: kinds, name: name,
             links: links.map(function (l) { return l.split(' '); }) };
  }
  var TABLE = [
    R('A', 'L', ['S'], ['b0 c0.1', 'b1 c0.0'], 'apply a leaf'),
    R('A', 'S', ['F'], ['b0 c0.2', 'b1 c0.0', 'b2 c0.1'], 'apply a stem'),
    R('A', 'F', ['T'], ['b0 c0.2', 'b1 c0.3', 'b2 c0.0', 'b3 c0.1'], 'apply a fork'),
    R('T', 'L', ['E'], ['b0 b2', 'b1 c0.0'], 'the K-rule'),
    R('T', 'S', ['D', 'A', 'A', 'A'], ['b0 c2.0', 'b1 c0.0', 'b2 c3.2', 'b3 c1.0',
      'c0.1 c1.1', 'c0.2 c2.1', 'c1.2 c3.0', 'c2.2 c3.1'], 'the S-rule'),
    R('T', 'F', ['Sel'], ['b0 c0.3', 'b1 c0.0', 'b2 c0.4', 'b3 c0.1', 'b4 c0.2'], 'triage: wait for z'),
    R('Sel', 'L', ['E', 'E'], ['b0 b3', 'b1 c0.0', 'b2 c1.0'], 'triage on a leaf'),
    R('Sel', 'S', ['A', 'E', 'E'], ['b0 c1.0', 'b1 c0.0', 'b2 c2.0', 'b3 c0.2', 'b4 c0.1'], 'triage on a stem'),
    R('Sel', 'F', ['A', 'A', 'E', 'E'], ['b0 c2.0', 'b1 c3.0', 'b2 c0.0', 'b3 c1.2', 'b4 c0.1',
      'b5 c1.1', 'c0.2 c1.0'], 'triage on a fork'),
    R('D', 'L', ['L', 'L'], ['b0 c0.0', 'b1 c1.0'], 'copy a leaf'),
    R('D', 'S', ['S', 'S', 'D'], ['b0 c0.0', 'b1 c1.0', 'b2 c2.0', 'c0.1 c2.1', 'c1.1 c2.2'], 'copy a stem'),
    R('D', 'F', ['F', 'F', 'D', 'D'], ['b0 c0.0', 'b1 c1.0', 'b2 c2.0', 'b3 c3.0', 'c0.1 c2.1',
      'c1.1 c2.2', 'c0.2 c3.1', 'c1.2 c3.2'], 'copy a fork'),
    R('E', 'L', [], [], 'erase a leaf'),
    R('E', 'S', ['E'], ['b0 c0.0'], 'erase a stem'),
    R('E', 'F', ['E', 'E'], ['b0 c0.0', 'b1 c1.0'], 'erase a fork')
  ];
  var RULE = {};
  TABLE.forEach(function (r) { RULE[r.left + '|' + r.right] = r; });

  /* ---------- ports ---------- */
  function P(id, i) { return id + '.' + i; }
  function isFree(p) { return p.charAt(0) === '@' || p.charAt(0) === '$'; }
  function owner(p) { return isFree(p) ? null : Number(p.slice(0, p.indexOf('.'))); }
  function slot(p) { return Number(p.slice(p.indexOf('.') + 1)); }
  function varPort(x) { return '$' + x; }
  function copyObj(o) { var c = {}; for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) c[k] = o[k]; return c; }
  function connect(net, p, q) { net.link[p] = q; net.link[q] = p; }
  function newAgent(net, k) { var id = net.next++; net.kind[id] = k; return id; }
  function ids(net) { return Object.keys(net.kind).map(Number).sort(function (a, b) { return a - b; }); }
  function size(net) { return Object.keys(net.kind).length; }
  function empty() { return { kind: {}, link: {}, next: 0, loops: 0, steps: 0 }; }
  function clone(net) { return { kind: copyObj(net.kind), link: copyObj(net.link), next: net.next, loops: net.loops, steps: net.steps }; }

  /* ---------- compilation (IxTreeCompile.lean, extended to variables) ----------
     As compileTm: a closed tree (△ with at most two arguments, each a closed tree) is a
     constructor region (L, S, F), as ofTree; every other application is an A agent with the
     function at its principal port, the argument at aux 0 and its result at aux 1, as Code.app.
     So compile(f x), for trees f and x, is exactly IxTreeCompile.compile f x (the A agent
     first, then f and x in preorder). A variable is a free wire; a variable used k > 1 times
     gets a chain of k-1 duplicators facing its free wire. With opts.direct, any △ with at
     most two arguments becomes a constructor (△ x is then a stem over x's wire, saving the
     A·L interaction). */
  function addVarUse(net, x, port) {
    var v = varPort(x), q = net.link[v];
    if (q === undefined) { connect(net, v, port); return; }
    var d = newAgent(net, 'D');
    connect(net, v, P(d, 0)); connect(net, P(d, 1), q); connect(net, P(d, 2), port);
  }
  function isTree(u) {
    var sp = tree.spine(u);
    return tree.isLeaf(sp.head) && sp.args.length <= 2 && sp.args.every(isTree);
  }
  function compileInto(net, t, out, opts) {
    var direct = !!(opts && opts.direct);
    (function c(u, consumer) {
      if (u.k === 'a') {
        if (tree.isLeaf(u)) { connect(net, P(newAgent(net, 'L'), 0), consumer); return; }
        addVarUse(net, u.n, consumer); return;
      }
      var sp = tree.spine(u);
      if (tree.isLeaf(sp.head) && sp.args.length <= 2 && (direct || isTree(u))) {
        var id = newAgent(net, sp.args.length === 1 ? 'S' : 'F');
        connect(net, P(id, 0), consumer);
        sp.args.forEach(function (a, i) { c(a, P(id, i + 1)); });
        return;
      }
      var ap = newAgent(net, 'A');
      connect(net, P(ap, 2), consumer);
      c(u.f, P(ap, 0));
      c(u.x, P(ap, 1));
    })(t, out);
    return net;
  }
  // IxTreeCompile.compile f x: an A agent at the root even when f x is itself a tree
  function compileApp(f, x, opts) {
    if (typeof f === 'string') f = tree.parse(f);
    if (typeof x === 'string') x = tree.parse(x);
    var net = empty(), ap = newAgent(net, 'A');
    connect(net, P(ap, 2), '@');
    compileInto(net, f, P(ap, 0), opts);
    compileInto(net, x, P(ap, 1), opts);
    return net;
  }
  function compile(t, opts) {
    if (typeof t === 'string') t = tree.parse(t);
    return compileInto(empty(), t, '@', opts);
  }

  /* ---------- active pairs and firing (IxCore.lean: fire) ---------- */
  function ruleOf(net, a, b) { return RULE[net.kind[a] + '|' + net.kind[b]] || null; }
  function rawPairs(net) {
    var out = [];
    ids(net).forEach(function (a) {
      if (PRODUCER[net.kind[a]]) return;
      var q = net.link[P(a, 0)];
      if (q === undefined || isFree(q) || slot(q) !== 0) return;
      var b = owner(q), r = ruleOf(net, a, b);
      if (r) out.push({ a: a, b: b, at: a + '~' + b, code: r.code, rule: r.name });
    });
    return out;
  }
  function fire(net, pair) {
    var a = pair.a, b = pair.b;
    if (!PRODUCER[net.kind[b]]) { var t0 = a; a = b; b = t0; }
    var r = ruleOf(net, a, b);
    if (!r || net.link[P(a, 0)] !== P(b, 0)) throw new Error('not an active pair: ' + a + ', ' + b);
    var na = ARITY[net.kind[a]], nb = ARITY[net.kind[b]], nB = na + nb;
    var bp = [], i;
    for (i = 0; i < nB; i++) bp.push(i < na ? P(a, i + 1) : P(b, i - na + 1));
    var M = clone(net);
    M.steps = net.steps + 1;
    // outer partner of each boundary slot: another slot, or a port outside the pair
    var O = {};
    for (i = 0; i < nB; i++) {
      var e = net.link[bp[i]], j = bp.indexOf(e);
      O['B' + i] = j >= 0 ? 'B' + j : e;
    }
    // remove the pair
    [a, b].forEach(function (x) {
      for (var s = 0; s <= ARITY[net.kind[x]]; s++) delete M.link[P(x, s)];
      delete M.kind[x];
    });
    // create the cells, in order, with fresh names
    var made = r.kinds.map(function (k) { return newAgent(M, k); });
    function sock(s) {
      if (s.charAt(0) === 'b') return 'B' + s.slice(1);
      var dot = s.indexOf('.');
      return P(made[Number(s.slice(1, dot))], Number(s.slice(dot + 1)));
    }
    var Rw = {};
    r.links.forEach(function (l) { var x = sock(l[0]), y = sock(l[1]); Rw[x] = y; Rw[y] = x; });
    function isB(s) { return s !== undefined && s.charAt(0) === 'B'; }
    var seenB = {};
    // walk alternately along rule wires and outer wires until an end that is not a slot
    function walk(s, viaRule) {
      var cur = viaRule ? Rw[s] : O[s];
      var lastRule = viaRule;
      while (isB(cur)) {
        seenB[cur] = true;
        cur = lastRule ? O[cur] : Rw[cur];
        lastRule = !lastRule;
      }
      return cur;
    }
    var done = {};
    made.forEach(function (id) {
      for (var s = 0; s <= ARITY[M.kind[id]]; s++) {
        var p = P(id, s);
        if (done[p]) continue;
        var e = walk(p, true);
        connect(M, p, e); done[p] = true; done[e] = true;
      }
    });
    for (i = 0; i < nB; i++) {
      var o = O['B' + i];
      if (isB(o) || done[o]) continue;
      // start from the outside port o, entering slot i along the outer wire
      seenB['B' + i] = true;
      var end = walk('B' + i, true);
      connect(M, o, end); done[o] = true; done[end] = true;
    }
    // slots joined only to each other form closed loops
    for (i = 0; i < nB; i++) {
      var bi = 'B' + i;
      if (seenB[bi]) continue;
      M.loops++;
      var cur = bi, viaRule = true;
      do { seenB[cur] = true; cur = viaRule ? Rw[cur] : O[cur]; viaRule = !viaRule; } while (cur !== bi && !seenB[cur]);
    }
    return M;
  }

  /* ---------- canonical traversal and key ---------- */
  function freePorts(net) {
    var vs = [];
    for (var p in net.link) if (p.charAt(0) === '$') vs.push(p);
    vs.sort();
    return (net.link['@'] !== undefined ? ['@'] : []).concat(vs);
  }
  // breadth-first labelling: continue from the agents already in `order` (from position `from`),
  // visiting ports in order, labelling agents as they are first seen
  function traverse(net, label, order, from) {
    var head = from || 0;
    while (head < order.length) {
      var id = order[head++];
      for (var s = 0; s <= ARITY[net.kind[id]]; s++) {
        var p = net.link[P(id, s)];
        if (p === undefined || isFree(p)) continue;
        var o = owner(p);
        if (label[o] === undefined) { label[o] = order.length; order.push(o); }
      }
    }
  }
  function describe(net, order, label, prefix) {
    return order.map(function (id) {
      var ps = [];
      for (var s = 0; s <= ARITY[net.kind[id]]; s++) {
        var p = net.link[P(id, s)];
        ps.push(p === undefined ? '-' : isFree(p) ? p : prefix + label[owner(p)] + '.' + slot(p));
      }
      return net.kind[id] + '(' + ps.join(',') + ')';
    }).join(' ');
  }
  // the agents reachable from the free ports, in canonical order, and the remaining components
  function canonical(net) {
    var label = {}, order = [];
    var frees = freePorts(net);
    frees.forEach(function (f) {
      var p = net.link[f];
      if (isFree(p)) return;
      var o = owner(p);
      if (label[o] !== undefined) return;
      var from = order.length;
      label[o] = from; order.push(o);
      traverse(net, label, order, from);
    });
    var comps = [], seen = copyObj(label);
    ids(net).forEach(function (id) {
      if (seen[id] !== undefined) return;
      var l = {}, ord = [];
      l[id] = 0; ord.push(id);
      traverse(net, l, ord, 0);
      ord.forEach(function (x) { seen[x] = true; });
      comps.push(ord);
    });
    return { label: label, order: order, frees: frees, comps: comps };
  }
  // a string identifying the net up to renaming of agents and wires, detached parts included
  function key(net) {
    var c = canonical(net);
    var main = c.frees.map(function (f) {
      var p = net.link[f];
      return f + '=' + (isFree(p) ? p : c.label[owner(p)] + '.' + slot(p));
    }).join(' ') + ' | ' + describe(net, c.order, c.label, '');
    var garbage = c.comps.map(function (comp) {
      var best = null;
      comp.forEach(function (start) {
        var l = {}, ord = [];
        l[start] = 0; ord.push(start);
        traverse(net, l, ord, 0);
        var s = describe(net, ord, l, 'g');
        if (best === null || s < best) best = s;
      });
      return best;
    }).sort();
    return main + (garbage.length ? ' || ' + garbage.join(' || ') : '') + (net.loops ? ' ○' + net.loops : '');
  }

  /* ---------- read-back (IxTreeRegion.lean: readback, extended) ----------
     From the result port: a constructor reads as △ applied to its children; an A agent's result
     reads as an application; T's result as △ u y z and Sel's as △ (△ w x) y z (a triage under
     way); a duplicator's output reads as what it copies; a free wire as its variable. Term nodes
     read through a consumer carry `agent` (its id) and `pending: true`. Anything else reads '?'.
     Agents the read-back does not visit are garbage. */
  function readback(net, opts) {
    opts = opts || {};
    var A = tree.atom, App = tree.app, visited = {}, pending = 0, ok = true, depthMax = opts.depth || 400;
    function tag(t, id) { var c = { k: t.k }; if (t.k === 'a') c.n = t.n; else { c.f = t.f; c.x = t.x; } c.agent = id; c.pending = true; return c; }
    function from(port, depth) {
      var p = net.link[port];
      if (p === undefined) { ok = false; return A('?'); }
      if (depth > depthMax) { ok = false; return A('…'); }
      if (p === '@') { ok = false; return A('?'); }
      if (p.charAt(0) === '$') return A(p.slice(1));
      var id = owner(p), s = slot(p), k = net.kind[id];
      visited[id] = true;
      if (PRODUCER[k] && s === 0) {
        if (k === 'L') { var l = A(tree.LEAF); l.agent = id; return l; }
        if (k === 'S') { var st = App(A(tree.LEAF), from(P(id, 1), depth + 1)); st.agent = id; return st; }
        var fk = App(App(A(tree.LEAF), from(P(id, 1), depth + 1)), from(P(id, 2), depth + 1)); fk.agent = id; return fk;
      }
      if (k === 'A' && s === 2) { pending++; return tag(App(from(P(id, 0), depth + 1), from(P(id, 1), depth + 1)), id); }
      if (k === 'T' && s === 3) {
        pending++;
        return tag(App(App(App(A(tree.LEAF), from(P(id, 0), depth + 1)), from(P(id, 1), depth + 1)), from(P(id, 2), depth + 1)), id);
      }
      if (k === 'Sel' && s === 4) {
        pending++;
        var wx = App(App(A(tree.LEAF), from(P(id, 1), depth + 1)), from(P(id, 2), depth + 1));
        return tag(App(App(App(A(tree.LEAF), wx), from(P(id, 3), depth + 1)), from(P(id, 0), depth + 1)), id);
      }
      if (k === 'D' && (s === 1 || s === 2)) return from(P(id, 0), depth + 1);
      ok = false;
      return A('?');
    }
    var term = net.link['@'] === undefined ? A('?') : from('@', 0);
    var garbage = 0;
    for (var id in net.kind) if (!visited[id]) garbage++;
    return { term: term, pending: pending, garbage: garbage, ok: ok, value: ok && pending === 0 };
  }

  /* ---------- the calculus interface ---------- */
  function parse(s) { return compile(tree.parse(s)); }
  function print(net, opts) {
    opts = opts || {};
    var rb = readback(net), mark = opts.mark;
    var o = { raw: opts.raw, html: opts.html };
    if (opts.html) {
      o.cls = function (u) {
        if (mark && u.agent !== undefined && (u.agent === mark.a || u.agent === mark.b)) return 'redex';
        return u.pending ? 'pending' : null;
      };
    }
    var s = tree.print(rb.term, o);
    if (opts.size) s += ' · ' + size(net) + (size(net) === 1 ? ' agent' : ' agents');
    if (opts.garbage && rb.garbage) s += ' + ' + rb.garbage + ' detached';
    return s;
  }
  // active pairs, nearest the result port first ("outermost"); detached pairs last
  function redexes(net) {
    var ps = rawPairs(net);
    if (ps.length < 2) return ps;
    var c = canonical(net), rank = copyObj(c.label), n = c.order.length;
    c.comps.forEach(function (comp) { comp.forEach(function (id) { rank[id] = n++; }); });
    return ps.sort(function (p, q) { return Math.min(rank[p.a], rank[p.b]) - Math.min(rank[q.a], rank[q.b]); });
  }
  var activePairs = redexes;
  function contract(net, pair) { return fire(net, pair); }
  // seeded random numbers (mulberry32), for reproducible random orders
  function rng(seed) {
    var s = seed >>> 0;
    return function () {
      s = (s + 0x6D2B79F5) >>> 0;
      var t = s;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  // strategies: 'outer' (nearest the result first), 'inner' (farthest first), 'oldest' (a fixed
  // pair order: the pair whose older agent was created first), 'random' (Math.random, or opts.random),
  // or a function (pairs, net) -> pair
  function pick(net, strategy, random) {
    if (typeof strategy === 'function') return strategy(redexes(net), net);
    var ps;
    if (strategy === 'oldest') {
      ps = rawPairs(net);
      ps.sort(function (p, q) { return Math.min(p.a, p.b) - Math.min(q.a, q.b); });
      return ps[0] || null;
    }
    if (strategy === 'random') { ps = rawPairs(net); return ps.length ? ps[Math.floor((random || Math.random)() * ps.length)] : null; }
    ps = redexes(net);
    if (strategy === 'inner') return ps[ps.length - 1] || null;
    return ps[0] || null;
  }
  function step(net, strategy, random) {
    var r = pick(net, strategy || 'outer', random);
    if (!r) return null;
    return { t: fire(net, r), rule: r.rule, at: r.at, code: r.code, pair: r };
  }
  function isNormal(net) { return rawPairs(net).length === 0; }
  function isOutcome(net) { return isNormal(net) && tree.isOutcome(readback(net).term); }
  // probe: list of variable names, or a context (string or tree term) with a hole [ ];
  // t: a tree term, a string, or a net (then the net is spliced into the probe's hole)
  function plug(probe, t) {
    if (typeof t === 'string' || (t && t.k)) return compile(tree.plug(probe, typeof t === 'string' ? tree.parse(t) : t));
    var net = clone(t);
    if (Array.isArray(probe)) {
      probe.forEach(function (x) {
        var f = net.link['@'], ap = newAgent(net, 'A');
        delete net.link['@'];
        connect(net, P(ap, 0), f); connect(net, P(ap, 2), '@');
        addVarUse(net, x, P(ap, 1));
      });
      return net;
    }
    var ctx = compile(typeof probe === 'string' ? tree.parse(probe) : probe), off = ctx.next;
    var hole = varPort(tree.hole), h = ctx.link[hole];
    if (h === undefined) return ctx;
    delete ctx.link[hole]; delete ctx.link[h];
    function sh(p) { return isFree(p) ? p : P(owner(p) + off, slot(p)); }
    for (var id in net.kind) ctx.kind[Number(id) + off] = net.kind[id];
    ctx.next = off + net.next;
    var vars = [];
    for (var p in net.link) {
      if (p === '@') continue;
      if (p.charAt(0) === '$') { vars.push(p); continue; }
      var q = net.link[p];
      if (isFree(q)) continue;
      ctx.link[sh(p)] = sh(q);
    }
    var r = net.link['@'];
    if (r.charAt(0) === '$') addVarUse(ctx, r.slice(1), h);
    else {
      connect(ctx, h, sh(r));
    }
    vars.forEach(function (v) { var q = net.link[v]; if (q !== '@') addVarUse(ctx, v.slice(1), sh(q)); });
    ctx.loops += net.loops;
    return ctx;
  }
  function run(net, strategy, max, random) {
    if (typeof net === 'string') net = parse(net);
    max = max === undefined ? 400 : max;
    var seq = [net];
    for (var i = 0; i < max; i++) { var s = step(net, strategy, random); if (!s) break; net = s.t; seq.push(net); }
    return seq;
  }

  /* ---------- layout for drawing ----------
     Agents are Lafont triangles with the principal port at the apex, pointing toward the
     agent its principal port is wired to. Layered from the result port: a spanning tree by
     breadth-first search, leaves side by side, parents centred over their children.
     Detached components are laid out to the right of the main one. */
  function layoutNet(net, opts) {
    opts = opts || {};
    var gx = opts.gapX || 34, gy = opts.gapY || 46, h = opts.half || 11, margin = opts.margin || 24;
    var c = canonical(net), depth = {}, kids = {}, parent = {};
    function span(roots) {
      var q = roots.slice(), head = 0;
      roots.forEach(function (r) { depth[r] = 0; kids[r] = []; });
      while (head < q.length) {
        var id = q[head++];
        for (var s = 0; s <= ARITY[net.kind[id]]; s++) {
          var p = net.link[P(id, s)];
          if (p === undefined || isFree(p)) continue;
          var o = owner(p);
          if (depth[o] === undefined) { depth[o] = depth[id] + 1; parent[o] = id; kids[o] = []; kids[id].push(o); q.push(o); }
        }
      }
    }
    var blocks = [];
    var mainRoots = [];
    c.frees.forEach(function (f) { var p = net.link[f]; if (!isFree(p) && mainRoots.indexOf(owner(p)) < 0 && depth[owner(p)] === undefined) { mainRoots.push(owner(p)); span([owner(p)]); } });
    if (mainRoots.length) blocks.push({ roots: mainRoots, main: true });
    c.comps.forEach(function (comp) { span([comp[0]]); blocks.push({ roots: [comp[0]], main: false }); });
    var X = {}, slotX = 0, maxDepth = 0;
    blocks.forEach(function (bk, bi) {
      if (bi > 0) slotX += 1;   // a gap between blocks
      bk.x0 = slotX;
      bk.roots.forEach(function place(id) {
        if (depth[id] > maxDepth) maxDepth = depth[id];
        if (!kids[id].length) { X[id] = slotX++; return; }
        kids[id].forEach(place);
        X[id] = (X[kids[id][0]] + X[kids[id][kids[id].length - 1]]) / 2;
      });
      bk.x1 = slotX - 1;
    });
    var top = margin + gy * 0.9;
    function pos(id) { return { x: margin + 20 + X[id] * gx, y: top + depth[id] * gy }; }
    var agents = [], at = {};
    ids(net).forEach(function (id) {
      var p = pos(id), k = net.kind[id], pp = net.link[P(id, 0)], dir;
      if (pp === undefined) dir = 'up';
      else if (isFree(pp)) dir = pp === '@' ? 'up' : 'down';
      else dir = depth[owner(pp)] < depth[id] || (depth[owner(pp)] === depth[id] && X[owner(pp)] < X[id]) ? 'up' : 'down';
      var sgn = dir === 'up' ? -1 : 1, n = ARITY[k], ports = [{ x: p.x, y: p.y + sgn * h, nx: 0, ny: sgn }];
      for (var i = 0; i < n; i++) {
        var off = n === 1 ? 0 : (i - (n - 1) / 2) * (2 * h * 0.85 / Math.max(1, n - 1));
        ports.push({ x: p.x + off, y: p.y - sgn * h * 0.75, nx: 0, ny: -sgn, name: AUX[k][i] });
      }
      var tri = dir === 'up'
        ? [[p.x, p.y - h], [p.x - h * 1.05, p.y + h * 0.75], [p.x + h * 1.05, p.y + h * 0.75]]
        : [[p.x, p.y + h], [p.x - h * 1.05, p.y - h * 0.75], [p.x + h * 1.05, p.y - h * 0.75]];
      var ag = { id: id, kind: k, x: p.x, y: p.y, dir: dir, ports: ports, triangle: tri, main: c.label[id] !== undefined,
                 producer: !!PRODUCER[k] };
      agents.push(ag); at[id] = ag;
    });
    var free = [], fpos = {};
    c.frees.forEach(function (f) {
      var p = net.link[f], x, y;
      if (f === '@') {
        if (isFree(p)) { x = margin + 20; y = margin; }
        else { x = at[owner(p)].x; y = margin; }
      } else {
        if (isFree(p)) { x = margin + 20 + gx * (free.length); y = top + (maxDepth + 1) * gy; }
        else { x = at[owner(p)].x + 6; y = top + (maxDepth + 1) * gy; }
      }
      free.push({ name: f === '@' ? 'result' : f.slice(1), port: f, x: x, y: y });
    });
    /* Labels of free ports: the name is drawn centred under its port (12 below; 'result' 4 above). No two
       labels may overlap, and none may overlap an agent: the ports of a row are spread apart, as little as
       will do (clusters of touching labels are centred on the mean of their ports), and a label that still
       meets an agent moves down a row. Each free port gets its label's box: label { x, y, w, h }. */
    var cw = opts.charWidth || 7.6, pad = opts.labelGap || 8;
    function labelBox(fp) {
      var w = fp.name.length * (fp.port === '@' ? 6.4 : cw) + 2;
      fp.label = { x: fp.x - w / 2, y: fp.port === '@' ? fp.y - 14 : fp.y + 2, w: w, h: 13 };
    }
    var rowsOf = {};
    free.forEach(function (fp) { if (fp.port !== '@') (rowsOf[fp.y] = rowsOf[fp.y] || []).push(fp); });
    Object.keys(rowsOf).forEach(function (y) {
      var row = rowsOf[y].slice().sort(function (a, b) { return a.x - b.x || (a.port < b.port ? -1 : 1); });
      var want = row.map(function (fp) { return fp.x; }), half = row.map(function (fp) { return (fp.name.length * cw + 2) / 2; });
      // clusters of touching labels, packed pad apart, each placed so that its ports are nearest (on mean) to
      // where they would be alone; a cluster that then meets the one before is merged with it
      var cl = [];
      row.forEach(function (fp, k) {
        cl.push({ members: [k], offs: [half[k]], width: 2 * half[k], left: want[k] - half[k] });
        for (;;) {
          var c = cl[cl.length - 1], p = cl[cl.length - 2];
          if (!p || c.left >= p.left + p.width + pad) break;
          var members = p.members.concat(c.members), offs = [], x = 0;
          members.forEach(function (m, q) { x += q ? half[members[q - 1]] + pad + half[m] : half[m]; offs.push(x); });
          var left = members.reduce(function (a, m, q) { return a + want[m] - offs[q]; }, 0) / members.length;
          cl.pop(); cl.pop();
          cl.push({ members: members, offs: offs, width: x + half[members[members.length - 1]], left: left });
        }
      });
      var shift = Math.max(0, 2 - cl[0].left);
      cl.forEach(function (c) { c.members.forEach(function (m, q) { row[m].x = c.left + shift + c.offs[q]; }); });
    });
    free.forEach(labelBox);
    function hitsAgent(b) {
      return agents.some(function (ag) {
        var xs = ag.triangle.map(function (p) { return p[0]; }), ys = ag.triangle.map(function (p) { return p[1]; });
        return b.x < Math.max.apply(null, xs) + 2 && Math.min.apply(null, xs) - 2 < b.x + b.w && b.y < Math.max.apply(null, ys) + 2 && Math.min.apply(null, ys) - 2 < b.y + b.h;
      });
    }
    function hitsLabel(fp) {
      return free.some(function (o) { return o !== fp && fp.label.x < o.label.x + o.label.w && o.label.x < fp.label.x + fp.label.w && fp.label.y < o.label.y + o.label.h && o.label.y < fp.label.y + fp.label.h; });
    }
    free.forEach(function (fp) {
      for (var tries = 0; tries < 6 && (hitsAgent(fp.label) || hitsLabel(fp)); tries++) { fp.y += fp.port === '@' ? -gy / 2 : gy / 2; labelBox(fp); }
    });
    free.forEach(function (fp) { fpos[fp.port] = { x: fp.x, y: fp.y, nx: 0, ny: fp.port === '@' ? 1 : -1 }; });
    function portPos(p) {
      if (isFree(p)) return fpos[p];
      return at[owner(p)].ports[slot(p)];
    }
    var wires = [], done = {};
    Object.keys(net.link).forEach(function (p) {
      var q = net.link[p];
      if (done[p] || done[q]) return;
      done[p] = done[q] = true;
      var A = portPos(p), B = portPos(q);
      if (!A || !B) return;
      var d = Math.sqrt((A.x - B.x) * (A.x - B.x) + (A.y - B.y) * (A.y - B.y)), k = Math.max(16, d / 2.5);
      var active = !isFree(p) && !isFree(q) && slot(p) === 0 && slot(q) === 0;
      wires.push({ from: p, to: q, active: active, x1: A.x, y1: A.y, x2: B.x, y2: B.y,
        d: 'M ' + r1(A.x) + ' ' + r1(A.y) + ' C ' + r1(A.x + A.nx * k) + ' ' + r1(A.y + A.ny * k) + ' ' +
           r1(B.x + B.nx * k) + ' ' + r1(B.y + B.ny * k) + ' ' + r1(B.x) + ' ' + r1(B.y) });
    });
    var width = margin * 2 + 40 + Math.max(0, slotX - 1) * gx, height = top + (maxDepth + 1) * gy + margin;
    free.forEach(function (fp) { width = Math.max(width, fp.label.x + fp.label.w + margin); height = Math.max(height, fp.label.y + fp.label.h + margin / 2); });
    var mainEnd = blocks.length && blocks[0].main ? margin + 20 + blocks[0].x1 * gx + gx / 2 : null;
    return { agents: agents, wires: wires, free: free, width: width, height: height, loops: net.loops,
             viewBox: '0 0 ' + r1(width) + ' ' + r1(height), detachedFrom: blocks.length > 1 ? mainEnd : null };
  }
  function r1(x) { return Math.round(x * 10) / 10; }

  var netCalc = {
    id: 'net', name: 'Interaction nets',
    ARITY: ARITY, AUX: AUX, PRODUCER: PRODUCER, TABLE: TABLE,
    compile: compile, compileApp: compileApp, compileInto: compileInto, start: parse, fromTree: compile,
    activePairs: activePairs, fire: fire, readback: readback, key: key, size: size, layoutNet: layoutNet,
    parse: parse, print: print, redexes: redexes, contract: contract, step: step,
    isNormal: isNormal, isOutcome: isOutcome, plug: plug, run: run,
    rng: rng, ids: ids, clone: clone,
    strategies: ['outer', 'inner', 'oldest', 'random']
  };
  CALC.net = netCalc;
  if (typeof module !== 'undefined' && module.exports) module.exports = netCalc;
})(typeof window !== 'undefined' ? window : (typeof globalThis !== 'undefined' ? globalThis : this));
