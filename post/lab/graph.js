/* Calculus-generic reduction graphs, runs, and an automatic layout of a bundle of fibres.
   Works with any module of the shared interface (CALC.ski, CALC.tree, CALC.net). */
(function (root) {
  var CALC = root.CALC || (root.CALC = {});

  function asState(calc, t) { return typeof t === 'string' ? calc.parse(t) : t; }

  /* Breadth-first search over the states reachable from `terms` (one term or a list), up to
     opts.max states (default 200). Each state: { key, t, label, depth, normal, outcome, onCycle,
     fibre, out: [edge indices], in: [...] }. Each edge: { from, to, rule, at }. Edges between
     the same two states by different redexes are kept (a multigraph) unless opts.simple.
     fibre: the key of the normal form the state reaches, or 'none' if it reaches none in the
     explored graph, or 'open' if the search stopped at opts.max before deciding.
     opts.closed: keep only the given terms, and the steps between them (as the essay's
     hand-laid bundle of fourteen terms). opts.maxDepth: do not expand beyond this depth.
     Fibres are listed in the order of the first given term over each, 'no value' last. */
  function reductionGraph(calc, terms, opts) {
    opts = opts || {};
    var max = opts.max || 200;
    var label = opts.label || function (t) { return calc.print(t); };
    if (!Array.isArray(terms)) terms = [terms];
    var states = [], edges = [], index = {}, queue = [], truncated = false;
    var closed = !!opts.closed, maxDepth = opts.maxDepth === undefined ? Infinity : opts.maxDepth, adding = true;
    function add(t, depth) {
      var k = calc.key(t);
      if (index[k] !== undefined) return index[k];
      if (closed && !adding) return -2;
      if (states.length >= max) { truncated = true; return -1; }
      index[k] = states.length;
      states.push({ key: k, t: t, label: label(t), depth: depth, out: [], in: [], root: false });
      queue.push(index[k]);
      return index[k];
    }
    terms.forEach(function (t) { var i = add(asState(calc, t), 0); if (i >= 0) states[i].root = true; });
    adding = false;
    var seenEdge = {};
    for (var h = 0; h < queue.length; h++) {
      var i = queue[h], s = states[i], rs = calc.redexes(s.t);
      s.normal = rs.length === 0;
      s.expanded = true;
      if (s.depth >= maxDepth && !closed) { s.expanded = rs.length === 0; if (rs.length) truncated = true; continue; }
      rs.forEach(function (r) {
        var u = calc.contract(s.t, r), j = add(u, s.depth + 1);
        if (j === -2) return;   // a step leaving the given terms
        if (j < 0) { s.expanded = false; return; }
        var ek = i + '>' + j;
        if (opts.simple && seenEdge[ek] !== undefined) return;
        seenEdge[ek] = edges.length;
        s.out.push(edges.length); states[j].in.push(edges.length);
        edges.push({ from: i, to: j, rule: r.rule, at: r.at });
      });
    }
    states.forEach(function (s) {
      if (s.normal === undefined) { s.normal = calc.isNormal(s.t); s.expanded = s.normal; }
      s.outcome = s.normal && calc.isOutcome(s.t);
    });
    // fibres: the normal forms reachable backwards
    var fibreOf = states.map(function () { return []; });
    states.forEach(function (s, i) {
      if (!s.normal) return;
      var stack = [i], seen = {};
      seen[i] = true;
      while (stack.length) {
        var j = stack.pop();
        fibreOf[j].push(s.key);
        states[j].in.forEach(function (e) { var f = edges[e].from; if (!seen[f]) { seen[f] = true; stack.push(f); } });
      }
    });
    states.forEach(function (s, i) {
      s.fibre = fibreOf[i].length === 1 ? fibreOf[i][0] : fibreOf[i].length ? 'many' : truncated ? 'open' : 'none';
    });
    // cycles: strongly connected components (Tarjan, iterative) with more than one state or a self-loop
    var idx = 0, stk = [], onStk = {}, num = {}, low = {};
    states.forEach(function (s, v0) {
      if (num[v0] !== undefined) return;
      var work = [[v0, 0]];
      num[v0] = low[v0] = idx++; stk.push(v0); onStk[v0] = true;
      while (work.length) {
        var top = work[work.length - 1], v = top[0];
        if (top[1] < states[v].out.length) {
          var w = edges[states[v].out[top[1]++]].to;
          if (num[w] === undefined) { num[w] = low[w] = idx++; stk.push(w); onStk[w] = true; work.push([w, 0]); }
          else if (onStk[w]) low[v] = Math.min(low[v], num[w]);
        } else {
          work.pop();
          if (work.length) { var p = work[work.length - 1][0]; low[p] = Math.min(low[p], low[v]); }
          if (low[v] === num[v]) {
            var comp = [], x;
            do { x = stk.pop(); onStk[x] = false; comp.push(x); } while (x !== v);
            var cyc = comp.length > 1 || states[v].out.some(function (e) { return edges[e].to === v; });
            comp.forEach(function (c) { states[c].onCycle = cyc; });
          }
        }
      }
    });
    var fibres = [], fseen = {};
    var byRoot = states.filter(function (s) { return s.root; }).concat(states.filter(function (s) { return !s.root; }));
    byRoot.forEach(function (s) {
      if (fseen[s.fibre]) return;
      fseen[s.fibre] = true;
      var nf = s.fibre === 'none' || s.fibre === 'many' || s.fibre === 'open' ? null : index[s.fibre];
      fibres.push({ id: s.fibre, nf: nf, label: nf === null ? ({ none: 'no value', open: 'not reached yet', many: 'several' })[s.fibre] : states[nf].label });
    });
    fibres.forEach(function (f, i) { f.order = i; });
    function last(f) { return f.id === 'none' || f.id === 'open' ? 1 : 0; }
    fibres.sort(function (a, b) { return last(a) - last(b) || a.order - b.order; });
    return { calc: calc.id, states: states, edges: edges, index: index, fibres: fibres, truncated: truncated };
  }

  /* Follow one strategy from t: { states, keys, rules, ats, normal, cyc, cycleStart, capped }.
     A run stops at a normal form, at the first repeated state (cyc: the run is a lap of a loop,
     cycleStart: the index of the repeated state), or after opts.max steps (default 60). */
  function runPath(calc, t, strategy, opts) {
    opts = opts || {};
    var max = opts.max === undefined ? 60 : opts.max;
    t = asState(calc, t);
    var states = [t], keys = [calc.key(t)], rules = [], ats = [], seen = {};
    seen[keys[0]] = 0;
    for (var i = 0; i < max; i++) {
      var s = calc.step(t, strategy, opts.random);
      if (!s) return { states: states, keys: keys, rules: rules, ats: ats, normal: true, cyc: false, capped: false };
      t = s.t;
      var k = calc.key(t);
      rules.push(s.rule); ats.push(s.at);
      if (seen[k] !== undefined) return { states: states, keys: keys, rules: rules, ats: ats, normal: false, cyc: true, cycleStart: seen[k], capped: false };
      seen[k] = states.length; states.push(t); keys.push(k);
    }
    return { states: states, keys: keys, rules: rules, ats: ats, normal: false, cyc: false, capped: true };
  }

  /* Automatic layered layout of a reduction graph as a bundle over a line, after the essay's
     hero figure: each fibre sits over its own point of the line, the normal form nearest
     the line, the other states in layers by their distance to it (for the fibre with no
     value: by distance from its first states). opts: width, height, orientation ('wide': line
     along the bottom; 'tall': line down the right side), measure(label) -> box width (default: 7.6
     a character, 1.15 em for a △, which may come from a wider fallback font, and 14 of padding).
     opts.layering: 'nearest' (default: the shortest distance to the normal form) or 'longest'
     (the longest run to it, so that every step goes down at least one layer).
     opts.slots: a step over more than one layer gets a slot in each layer it crosses; its edge has
     via: the points of those slots, from source to target.
     opts.curves (with slots): such an edge also gets curve: the two control points of one cubic
     Bézier from the source's centre to the target's, the least bent that clears every other box
     (null if none does; then draw it through via).
     opts.rings: a fibre with no value whose states lie on one loop is drawn as a ring, in the
     order its states were given, clockwise from the top, rather than as a column.
     Steps between two states of one row (only with layering 'nearest') keep the two side by side,
     opts.linkGap (default 12) further apart than the other neighbours.
     The view box is fitted to the content: the boxes (with room above for a marker), the curves,
     and the line.
     Returns { nodes: [{ i, x, y, w, label, fibre, nf, layer }], edges: [{ from, to, rule }],
               fibres: { id: { x, y, label } }, line: [x1, y1, x2, y2], vb, width, height }. */
  function layoutBundle(graph, opts) {
    opts = opts || {};
    var tall = opts.orientation === 'tall';
    var measure = opts.measure || function (s) { var d = (s.match(/△/g) || []).length; return (s.length - d) * 7.6 + d * 14.4 + 14; };
    var st = graph.states;
    var layer = st.map(function () { return -1; });
    var byFibre = {};
    graph.fibres.forEach(function (f) { byFibre[f.id] = []; });
    st.forEach(function (s, i) { byFibre[s.fibre].push(i); });
    // layers: distance to the normal form (backward BFS), else distance from the fibre's roots
    graph.fibres.forEach(function (f) {
      var mem = byFibre[f.id], q = [], h;
      if (f.nf !== null) {
        layer[f.nf] = 0; q.push(f.nf);
        for (h = 0; h < q.length; h++) st[q[h]].in.forEach(function (e) {
          var j = graph.edges[e].from;
          if (layer[j] < 0 && st[j].fibre === f.id) { layer[j] = layer[q[h]] + 1; q.push(j); }
        });
        if (opts.layering === 'longest') {
          // the longest run to the normal form (the fibre has a value, so no loop is expected; if one is met, keep the shortest)
          var memo = {}, onPath = {}, loop = false;
          var longest = function (i) {
            if (memo[i] !== undefined) return memo[i];
            if (onPath[i]) { loop = true; return 0; }
            onPath[i] = true;
            var best = 0;
            st[i].out.forEach(function (e) { var j = graph.edges[e].to; if (st[j].fibre === f.id && j !== i) best = Math.max(best, 1 + longest(j)); });
            onPath[i] = false;
            memo[i] = best;
            return best;
          };
          var lay = {};
          mem.forEach(function (i) { lay[i] = longest(i); });
          if (!loop) mem.forEach(function (i) { layer[i] = lay[i]; });
        }
      } else {
        // first states: those no step of the fibre enters; on a bare loop, the first given term
        var roots = mem.filter(function (i) { return !st[i].in.some(function (e) { return st[graph.edges[e].from].fibre === f.id; }); });
        if (!roots.length) roots = [mem[0]];
        roots.forEach(function (r) { layer[r] = 0; q.push(r); });
        for (h = 0; h < q.length; h++) st[q[h]].out.forEach(function (e) {
          var j = graph.edges[e].to;
          if (layer[j] < 0 && st[j].fibre === f.id) { layer[j] = layer[q[h]] + 1; q.push(j); }
        });
        // with no value, the first states sit farthest from the line
        var top = 0;
        mem.forEach(function (i) { if (layer[i] > top) top = layer[i]; });
        mem.forEach(function (i) { layer[i] = layer[i] < 0 ? 0 : top - layer[i]; });
      }
      mem.forEach(function (i) { if (layer[i] < 0) layer[i] = 0; });
    });
    var nLayers = 1;
    st.forEach(function (s, i) { if (layer[i] + 1 > nLayers) nLayers = layer[i] + 1; });
    // rows within each fibre, ordered by discovery, then by the mean position of their successors
    var gap = opts.gap || 14, fgap = opts.fibreGap || 28;
    var nodes = st.map(function (s, i) { return { i: i, label: s.label, w: measure(s.label), fibre: s.fibre, nf: s.normal, layer: layer[i], cycle: !!s.onCycle }; });
    var bands = [], cursor = 0;
    var ringOf = {}, slotsOf = {}, slotLayer = {}, slotAlong = {};
    graph.fibres.forEach(function (f) {
      var mem = byFibre[f.id];
      if (!opts.rings || f.nf !== null || mem.length < 3 || !mem.every(function (i) { return st[i].onCycle; })) return;
      // a ring: offsets from its centre, wide enough that no two boxes meet
      var n = mem.length, ry = opts.ringRy || Math.max(44, 12.5 * n), rx = 30, off;
      for (var tries = 0; tries < 200; tries++, rx += 4) {
        off = mem.map(function (i, k) { var a = -Math.PI / 2 + 2 * Math.PI * k / n; return { i: i, dx: rx * Math.cos(a), dy: ry * Math.sin(a) }; });
        var clash = off.some(function (a, p) { return off.some(function (b, q) {
          // side by side: room for an arrow between them
          return q > p && Math.abs(a.dx - b.dx) < (nodes[a.i].w + nodes[b.i].w) / 2 + 30 && Math.abs(a.dy - b.dy) < 30;
        }); });
        if (!clash) break;
      }
      var box = { x0: Infinity, x1: -Infinity, y0: Infinity, y1: -Infinity };
      off.forEach(function (o) {
        box.x0 = Math.min(box.x0, o.dx - nodes[o.i].w / 2); box.x1 = Math.max(box.x1, o.dx + nodes[o.i].w / 2);
        box.y0 = Math.min(box.y0, o.dy - 11); box.y1 = Math.max(box.y1, o.dy + 11);
      });
      ringOf[f.id] = { off: off, box: box };
    });
    graph.fibres.forEach(function (f) {
      var rows = [];
      if (ringOf[f.id]) {
        var rg = ringOf[f.id], size = tall ? rg.box.y1 - rg.box.y0 : rg.box.x1 - rg.box.x0;
        rg.off.forEach(function (o) {
          nodes[o.i].along = cursor + (tall ? o.dy - rg.box.y0 : o.dx - rg.box.x0);
          nodes[o.i].ring = o; nodes[o.i].layer = 0;
        });
        bands.push({ id: f.id, label: f.label, start: cursor, end: cursor + size, anchor: cursor + (tall ? -rg.box.y0 : -rg.box.x0), ring: rg });
        cursor += size + fgap;
        return;
      }
      byFibre[f.id].forEach(function (i) { (rows[layer[i]] = rows[layer[i]] || []).push(i); });
      // with opts.slots, a step over more than one layer gets a slot (a dummy, named 'd<edge>_<layer>') in each
      // layer it crosses, so that the rows leave a way through for it
      var succOf = {};
      byFibre[f.id].forEach(function (i) { succOf[i] = st[i].out.map(function (e) { return graph.edges[e].to; }); });
      if (opts.slots) {
        byFibre[f.id].forEach(function (i) { succOf[i] = []; });
        graph.edges.forEach(function (e, k) {
          if (st[e.from].fibre !== f.id || st[e.to].fibre !== f.id) return;
          var hi = layer[e.from], lo = layer[e.to], prev = e.from;
          for (var Ly = hi - 1; Ly > lo; Ly--) {
            var id = 'd' + k + '_' + Ly;
            (rows[Ly] = rows[Ly] || []).push(id); succOf[prev].push(id); succOf[id] = []; prev = id;
            (slotsOf[k] = slotsOf[k] || []).push(id); slotLayer[id] = Ly;
          }
          succOf[prev].push(e.to);
        });
      }
      function size(i) { return typeof i === 'string' ? 10 : tall ? 22 : nodes[i].w; }
      var along = {}, bary = {}, rank = {};
      // steps within a row (the two states are then kept side by side, a little further apart)
      var same = {}, linkGap = opts.linkGap === undefined ? 12 : opts.linkGap;
      graph.edges.forEach(function (e) {
        if (e.from === e.to || st[e.from].fibre !== f.id || st[e.to].fibre !== f.id || layer[e.from] !== layer[e.to]) return;
        (same[e.from] = same[e.from] || []).push(e.to);
      });
      function linked(i, j) { return (same[i] || []).indexOf(j) >= 0 || (same[j] || []).indexOf(i) >= 0; }
      function gapAfter(row, k) { return gap + (k + 1 < row.length && linked(row[k], row[k + 1]) ? linkGap : 0); }
      function rowW(row) { return row.reduce(function (a, i, k) { return a + size(i) + (k + 1 < row.length ? gapAfter(row, k) : 0); }, 0); }
      // place rows from the line outward; each row ordered by the mean place of its successors
      var bandW = 0;
      rows.forEach(function (row) {
        if (!row) return;
        var nl = row.reduce(function (a, i) { return a + (same[i] || []).filter(function (j) { return row.indexOf(j) >= 0; }).length; }, 0);
        var w = rowW(row) + linkGap * Math.min(nl, row.length - 1);
        if (w > bandW) bandW = w;
      });
      function placeRow(row) {
        var w = rowW(row), x = cursor + (bandW - w) / 2;
        row.forEach(function (i, k) { along[i] = x + size(i) / 2; x += size(i) + gapAfter(row, k); });
      }
      // states joined by a step within the row are kept together, sources first; the groups in the order they had
      function groupRow(row) {
        var pos = {}, grp = {}, any = false;
        row.forEach(function (i, k) { pos[i] = k; grp[i] = i; });
        function find(i) { while (grp[i] !== i) i = grp[i]; return i; }
        row.forEach(function (i) { (same[i] || []).forEach(function (j) {
          if (pos[j] === undefined) return;
          any = true;
          var a = find(i), b = find(j);
          if (a !== b) grp[b] = a;
        }); });
        if (!any) return;
        var groups = {}, keys = [];
        row.forEach(function (i) { var g = find(i); if (!groups[g]) { groups[g] = []; keys.push(g); } groups[g].push(i); });
        var mid = {};
        keys.forEach(function (g) { mid[g] = groups[g].reduce(function (a, i) { return a + pos[i]; }, 0) / groups[g].length; });
        keys.sort(function (a, b) { return mid[a] - mid[b]; });
        var out = [];
        keys.forEach(function (g) {
          var mem = groups[g].slice(), indeg = {};
          mem.forEach(function (i) { indeg[i] = 0; });
          mem.forEach(function (i) { (same[i] || []).forEach(function (j) { if (indeg[j] !== undefined && j !== i) indeg[j]++; }); });
          while (mem.length) {
            var free = mem.filter(function (i) { return indeg[i] === 0; }), pick = (free.length ? free : mem)[0];
            out.push(pick); mem.splice(mem.indexOf(pick), 1);
            (same[pick] || []).forEach(function (j) { if (indeg[j] !== undefined) indeg[j]--; });
          }
        });
        out.forEach(function (i, k) { row[k] = i; });
      }
      // order a row by the mean place of its neighbours (ties: the order it had)
      function orderRow(row, nb) {
        row.forEach(function (i, k) { rank[i] = k; });
        row.forEach(function (i) {
          var ns = nb[i].filter(function (j) { return along[j] !== undefined; });
          bary[i] = ns.length ? ns.reduce(function (a, j) { return a + along[j]; }, 0) / ns.length : (along[i] !== undefined ? along[i] : Infinity);
          if (typeof i !== 'string') nodes[i].bary = bary[i];
        });
        row.sort(function (a, b) { return bary[a] - bary[b] || rank[a] - rank[b]; });
        groupRow(row);
      }
      rows.forEach(function (row, r) {
        if (!row) return;
        if (r > 0) orderRow(row, succOf); else groupRow(row);
        placeRow(row);
      });
      if (opts.slots) {
        // sweep back from the outside in (by the rows above), then out again (by the rows below)
        var predOf = {};
        rows.forEach(function (row) { (row || []).forEach(function (i) { predOf[i] = []; }); });
        Object.keys(succOf).forEach(function (i) { succOf[i].forEach(function (j) { if (predOf[j]) predOf[j].push(isNaN(i) ? i : Number(i)); }); });
        for (var r2 = rows.length - 2; r2 >= 0; r2--) if (rows[r2]) { orderRow(rows[r2], predOf); placeRow(rows[r2]); }
        for (r2 = 1; r2 < rows.length; r2++) if (rows[r2]) { orderRow(rows[r2], succOf); placeRow(rows[r2]); }
      }
      Object.keys(slotLayer).forEach(function (id) { if (along[id] !== undefined && slotAlong[id] === undefined) slotAlong[id] = along[id]; });
      byFibre[f.id].forEach(function (i) { nodes[i].along = along[i]; });
      var anchor = f.nf !== null ? along[f.nf] : cursor + bandW / 2;
      bands.push({ id: f.id, label: f.label, start: cursor, end: cursor + bandW, anchor: anchor });
      cursor += bandW + fgap;
    });
    var total = Math.max(1, cursor - fgap);
    function ringBox(n) { return ringOf[n.fibre].box; }
    function ringBottom(n) { return ringOf[n.fibre].box.y1 - 11; }
    var slotXY = null;
    var out = { nodes: nodes, edges: graph.edges.map(function (e) { return { from: e.from, to: e.to, rule: e.rule }; }), fibres: {} };
    if (!tall) {
      var W = Math.max(opts.width || 720, total + 40), rowH = opts.rowGap || 70;
      var H = opts.height || (nLayers * rowH + 80);
      rowH = Math.min(rowH, (H - 80) / Math.max(1, nLayers));
      var lineY = H - 14, x0 = (W - total) / 2, nfY = lineY - 60;
      nodes.forEach(function (n) { n.x = x0 + n.along; n.y = n.ring ? nfY + n.ring.dy - ringBottom(n) : nfY - n.layer * rowH; });
      slotXY = function (id) { return [x0 + slotAlong[id], nfY - slotLayer[id] * rowH]; };
      bands.forEach(function (b) { out.fibres[b.id] = { x: x0 + b.anchor, y: lineY, label: b.label, from: x0 + b.start, to: x0 + b.end }; });
      out.line = [20, lineY, W - 20, lineY];
      out.width = W; out.height = H;
      // from the line down; the boxes are added below, so the view box starts at the highest of them
      out.vb = '0 ' + Math.round(lineY - 10) + ' ' + W + ' ' + Math.round(H - lineY + 10);
    } else {
      // tall: the line down the right; layers become columns, the normal form nearest the line
      var colW = [];
      // a ring sits below the columns, so it does not widen them
      nodes.forEach(function (n) { if (!n.ring) colW[n.layer] = Math.max(colW[n.layer] || 0, n.w); });
      var Wt = opts.width || 380, lineX = Wt - 60, Ht = Math.max(opts.height || 424, total + 40), y0 = (Ht - total) / 2;
      // columns only for the layers that hold a state outside a ring
      var colX = [], x = lineX - 32;
      for (var c = 0; c < colW.length; c++) { colX[c] = x - (colW[c] || 0) / 2; x -= (colW[c] || 0) + 16; }
      x += 16;
      nodes.forEach(function (n) { n.x = n.ring ? lineX - 32 - (ringBox(n).x1 - n.ring.dx) : colX[n.layer]; n.y = y0 + n.along; });
      slotXY = function (id) { return [colX[slotLayer[id]], y0 + slotAlong[id]]; };
      bands.forEach(function (b) { out.fibres[b.id] = { x: lineX, y: y0 + b.anchor, label: b.label, from: y0 + b.start, to: y0 + b.end }; });
      out.line = [lineX, 16, lineX, Ht - 12];
      var left = Math.min(0, Math.round(x));
      out.width = Wt - left; out.height = Ht;
      out.vb = left + ' 0 ' + (Wt - left) + ' ' + Ht;
    }
    out.orientation = tall ? 'tall' : 'wide';
    // the slots of a long step, from its source to its target
    out.edges.forEach(function (e, k) { if (slotsOf[k]) e.via = slotsOf[k].map(function (id) { return slotXY(id); }); });
    if (opts.curves) out.edges.forEach(function (e) { if (e.via) e.curve = smoothCurve(nodes[e.from], nodes[e.to], e.via, nodes); });
    // the view box covers every box (a ring may reach past the layers) and every curve
    var vb = out.vb.split(' ').map(Number), bx0 = vb[0], by0 = vb[1], bx1 = vb[0] + vb[2], by1 = vb[1] + vb[3];
    nodes.forEach(function (n) {
      bx0 = Math.min(bx0, Math.floor(n.x - n.w / 2 - 8)); bx1 = Math.max(bx1, Math.ceil(n.x + n.w / 2 + 8));
      by0 = Math.min(by0, Math.floor(n.y - 30)); by1 = Math.max(by1, Math.ceil(n.y + 20));
    });
    out.edges.forEach(function (e) {
      if (e.curve) cubicPoints(nodes[e.from], e.curve[0], e.curve[1], nodes[e.to], 24).forEach(function (p) {
        bx0 = Math.min(bx0, Math.floor(p[0] - 8)); bx1 = Math.max(bx1, Math.ceil(p[0] + 8));
        by0 = Math.min(by0, Math.floor(p[1] - 8)); by1 = Math.max(by1, Math.ceil(p[1] + 8));
      });
    });
    out.vb = bx0 + ' ' + by0 + ' ' + (bx1 - bx0) + ' ' + (by1 - by0);
    return out;
  }

  function cubicPoints(a, c1, c2, b, n) {
    var pts = [];
    for (var s = 0; s <= n; s++) {
      var u = s / n, v = 1 - u, w0 = v * v * v, w1 = 3 * u * v * v, w2 = 3 * u * u * v, w3 = u * u * u;
      pts.push([w0 * a.x + w1 * c1[0] + w2 * c2[0] + w3 * b.x, w0 * a.y + w1 * c1[1] + w2 * c2[1] + w3 * b.y]);
    }
    return pts;
  }
  /* One cubic Bézier from a to b (box centres) that clears every other box by 6 across and 5 up and down:
     its control points sit at a third and two thirds of the chord, moved off it by k1 and k2. The least bent
     such curve, bent to the side of the slots first; null if none within 240. */
  function smoothCurve(a, b, via, others) {
    var dx = b.x - a.x, dy = b.y - a.y, len = Math.sqrt(dx * dx + dy * dy) || 1, nx = -dy / len, ny = dx / len;
    var side = (via || []).reduce(function (s, p) { return s + (p[0] - a.x) * nx + (p[1] - a.y) * ny; }, 0) < 0 ? -1 : 1;
    var ks = [0];
    for (var k = 6; k <= 240; k += 6) ks.push(side * k, -side * k);
    var cands = [];
    ks.forEach(function (k1) { ks.forEach(function (k2) {
      if (k1 * k2 < 0) return;   // one side only: no S-bends
      cands.push({ k1: k1, k2: k2, cost: Math.max(Math.abs(k1), Math.abs(k2)) + 0.35 * Math.abs(k1 - k2) + ((k1 + k2) * side < 0 ? 0.5 : 0) });
    }); });
    cands.sort(function (p, q) { return p.cost - q.cost; });
    var boxes = (others || []).filter(function (n) { return n !== a && n !== b; });
    for (var i = 0; i < cands.length; i++) {
      var c1 = [a.x + dx / 3 + nx * cands[i].k1, a.y + dy / 3 + ny * cands[i].k1], c2 = [a.x + 2 * dx / 3 + nx * cands[i].k2, a.y + 2 * dy / 3 + ny * cands[i].k2];
      var pts = cubicPoints(a, c1, c2, b, 60);
      var clear = boxes.every(function (n) { return pts.every(function (p) { return Math.abs(p[0] - n.x) >= n.w / 2 + 6 || Math.abs(p[1] - n.y) >= 16; }); });
      if (clear) return [[Math.round(c1[0] * 10) / 10, Math.round(c1[1] * 10) / 10], [Math.round(c2[0] * 10) / 10, Math.round(c2[1] * 10) / 10]];
    }
    return null;
  }

  var graph = { reductionGraph: reductionGraph, runPath: runPath, layoutBundle: layoutBundle };
  CALC.graph = graph;
  if (typeof module !== 'undefined' && module.exports) module.exports = graph;
})(typeof window !== 'undefined' ? window : (typeof globalThis !== 'undefined' ? globalThis : this));
