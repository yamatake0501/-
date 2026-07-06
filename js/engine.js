/* =========================================================
 * 立体四目並べ 思考エンジン
 *
 * - 反復深化 + αβ探索（ネガマックス）
 * - 置換表（Zobrist ハッシュ）
 * - キラームーブ / 履歴ヒューリスティックによる手順前後の最適化
 * - ラインごとの玉数を差分更新する軽量評価関数
 * - 即勝ち / 相手の即勝ち（受け強制）をノードごとに静的検出し、
 *   受けが 1 通りしかない局面は深さを消費せずに読み進める
 *
 * この関数全体を Worker のソースとして toString() で埋め込めるよう、
 * 外部依存を一切持たない即時実行可能な形で書いてある。
 * ========================================================= */
function SCORE4_ENGINE() {
  'use strict';

  var N = 4, COLS = 16, CELLS = 64;
  var WIN_SCORE = 1000000, WIN_THRESH = 999000;
  var NOW = (typeof performance !== 'undefined' && performance.now)
    ? function () { return performance.now(); }
    : function () { return Date.now(); };

  // ---------- 勝利ライン列挙（main.js と同じ idx = x + z*4 + y*16） ----------
  var LINE_COUNT = 0;
  var CELL_LINES_OFF = new Int32Array(CELLS + 1);
  var CELL_LINES;
  (function buildLines() {
    var dirs = [];
    for (var dx = -1; dx <= 1; dx++)
      for (var dy = -1; dy <= 1; dy++)
        for (var dz = -1; dz <= 1; dz++) {
          if (dx === 0 && dy === 0 && dz === 0) continue;
          if (dx < 0) continue;
          if (dx === 0 && dz < 0) continue;
          if (dx === 0 && dz === 0 && dy < 0) continue;
          dirs.push([dx, dy, dz]);
        }
    var per = [];
    for (var i = 0; i < CELLS; i++) per.push([]);
    for (var x = 0; x < N; x++)
      for (var z = 0; z < N; z++)
        for (var y = 0; y < N; y++)
          for (var k = 0; k < dirs.length; k++) {
            var d = dirs[k];
            if (x + d[0] * 3 < 0 || x + d[0] * 3 >= N) continue;
            if (y + d[1] * 3 < 0 || y + d[1] * 3 >= N) continue;
            if (z + d[2] * 3 < 0 || z + d[2] * 3 >= N) continue;
            var id = LINE_COUNT++;
            for (var s = 0; s < 4; s++)
              per[(x + d[0] * s) + (z + d[2] * s) * N + (y + d[1] * s) * N * N].push(id);
          }
    var off = 0;
    for (i = 0; i < CELLS; i++) { CELL_LINES_OFF[i] = off; off += per[i].length; }
    CELL_LINES_OFF[CELLS] = off;
    CELL_LINES = new Int16Array(off);
    var pos = 0;
    for (i = 0; i < CELLS; i++)
      for (k = 0; k < per[i].length; k++) CELL_LINES[pos++] = per[i][k];
  })();

  // ---------- Zobrist ハッシュ ----------
  var ZA = new Uint32Array(CELLS * 2), ZB = new Uint32Array(CELLS * 2);
  (function initZobrist() {
    var seed = 0x9e3779b9 | 0;
    function rnd() {  // mulberry32
      seed = (seed + 0x6D2B79F5) | 0;
      var t = seed;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return (t ^ (t >>> 14)) >>> 0;
    }
    for (var i = 0; i < CELLS * 2; i++) { ZA[i] = rnd(); ZB[i] = rnd(); }
  })();

  // ---------- 置換表 ----------
  // info: move(4bit) | depth<<4 (6bit) | flag<<10 (1=exact, 2=lower, 3=upper)
  var TT_BITS = 21, TT_SIZE = 1 << TT_BITS, TT_MASK = TT_SIZE - 1;
  var ttKey = new Uint32Array(TT_SIZE);
  var ttInfo = new Uint32Array(TT_SIZE);
  var ttScore = new Int32Array(TT_SIZE);

  // ---------- 局面状態 ----------
  var heights = new Int8Array(COLS);
  var cntW = new Int8Array(LINE_COUNT), cntB = new Int8Array(LINE_COUNT);
  var S = 0;                       // 白から見た評価値（差分更新）
  var hashA = 0, hashB = 0;
  var moveCnt = 0;

  // ライン中の玉数 → 評価値。両者の玉が混在するラインは 0
  var WT = [0, 2, 12, 96, 0];
  var CONTRIB = new Int32Array(40);   // (w<<3)|b
  for (var w0 = 0; w0 <= 4; w0++)
    for (var b0 = 0; b0 <= 4; b0++)
      CONTRIB[(w0 << 3) | b0] = (w0 > 0 && b0 > 0) ? 0 : (w0 > 0 ? WT[w0] : -WT[b0]);

  function resetPosition() {
    heights.fill(0); cntW.fill(0); cntB.fill(0);
    S = 0; hashA = 0; hashB = 0; moveCnt = 0;
  }

  function make(col, player) {          // player: 0=白, 1=黒
    var h = heights[col], idx = col + (h << 4);
    heights[col] = h + 1; moveCnt++;
    hashA = (hashA ^ ZA[(idx << 1) | player]) >>> 0;
    hashB = (hashB ^ ZB[(idx << 1) | player]) >>> 0;
    var e = CELL_LINES_OFF[idx + 1];
    for (var i = CELL_LINES_OFF[idx]; i < e; i++) {
      var l = CELL_LINES[i], w = cntW[l], b = cntB[l];
      S -= CONTRIB[(w << 3) | b];
      if (player === 0) w = ++cntW[l]; else b = ++cntB[l];
      S += CONTRIB[(w << 3) | b];
    }
  }

  function unmake(col, player) {
    var h = heights[col] - 1, idx = col + (h << 4);
    heights[col] = h; moveCnt--;
    hashA = (hashA ^ ZA[(idx << 1) | player]) >>> 0;
    hashB = (hashB ^ ZB[(idx << 1) | player]) >>> 0;
    var e = CELL_LINES_OFF[idx + 1];
    for (var i = CELL_LINES_OFF[idx]; i < e; i++) {
      var l = CELL_LINES[i], w = cntW[l], b = cntB[l];
      S -= CONTRIB[(w << 3) | b];
      if (player === 0) w = --cntW[l]; else b = --cntB[l];
      S += CONTRIB[(w << 3) | b];
    }
  }

  // ---------- 即勝ち / 相手の即勝ちの静的検出 ----------
  // 各列の着地セルについて、そこを埋めると 4 連が完成するラインがあるか調べる。
  // （3 個 + 相手 0 個のラインの空きセルは一意で、着地セルがライン上なら必ずそのセル）
  var g_myWin = -1, g_oppN = 0, g_oppCol = -1, g_nValid = 0;
  function scanNode(player) {
    var myCnt = player === 0 ? cntW : cntB;
    var opCnt = player === 0 ? cntB : cntW;
    g_myWin = -1; g_oppN = 0; g_oppCol = -1; g_nValid = 0;
    for (var col = 0; col < COLS; col++) {
      var h = heights[col];
      if (h >= N) continue;
      g_nValid++;
      var idx = col + (h << 4), e = CELL_LINES_OFF[idx + 1];
      var oppHere = false;
      for (var i = CELL_LINES_OFF[idx]; i < e; i++) {
        var l = CELL_LINES[i];
        if (opCnt[l] === 0 && myCnt[l] === 3) { g_myWin = col; return; }
        if (myCnt[l] === 0 && opCnt[l] === 3) oppHere = true;
      }
      if (oppHere) { g_oppN++; if (g_oppCol < 0) g_oppCol = col; }
    }
  }

  // ---------- 探索 ----------
  var ABORT = { aborted: true };
  var nodes = 0, deadline = 0;
  var MAX_PLY = 64;
  var KILL1 = new Int8Array(MAX_PLY), KILL2 = new Int8Array(MAX_PLY);
  var HIST = new Int32Array(2 * COLS);
  var MBUF = new Int8Array(MAX_PLY * COLS);
  var SBUF = new Int32Array(MAX_PLY * COLS);
  var CENTER = new Int32Array(COLS);
  for (var c0 = 0; c0 < COLS; c0++) {
    var cx = c0 & 3, cz = c0 >> 2;
    CENTER[c0] = ((4 - (Math.abs(cx - 1.5) + Math.abs(cz - 1.5))) * 2) | 0;
  }

  function negamax(depth, ply, alpha, beta, player) {
    if ((++nodes & 2047) === 0 && NOW() > deadline) throw ABORT;
    var alphaOrig = alpha;

    // 置換表
    var hIdx = (hashA & TT_MASK) >>> 0, ttMove = -1;
    if (ttKey[hIdx] === hashB && ttInfo[hIdx] !== 0) {
      var info = ttInfo[hIdx];
      ttMove = info & 15;
      var tDepth = (info >>> 4) & 63, flag = (info >>> 10) & 3;
      var ts = ttScore[hIdx];
      if (ts > WIN_THRESH) ts -= ply; else if (ts < -WIN_THRESH) ts += ply;
      if (tDepth >= depth) {
        if (flag === 1) return ts;
        if (flag === 2) { if (ts >= beta) return ts; if (ts > alpha) alpha = ts; }
        else if (flag === 3) { if (ts <= alpha) return ts; if (ts < beta) beta = ts; }
        if (alpha >= beta) return ts;
      }
    }

    // 即勝ち・相手の即勝ちの検出（葉でも行うので静的評価が「静か」になる）
    scanNode(player);
    if (g_myWin >= 0) return WIN_SCORE - ply;             // 今すぐ勝てる
    if (g_nValid === 0) return 0;                          // 満杯 → 引き分け
    if (g_oppN >= 2) return -(WIN_SCORE - ply - 1);        // 両狙いは受からない
    if (depth <= 0 || ply >= MAX_PLY - 2) return player === 0 ? S : -S;

    // 候補手の生成と並べ替え
    var base = ply << 4, mn = 0, col, i;
    if (g_oppN === 1) {
      MBUF[base] = g_oppCol; mn = 1;                       // 受けが強制
    } else {
      for (col = 0; col < COLS; col++) {
        if (heights[col] >= N) continue;
        var sc = HIST[(player << 4) | col] + CENTER[col];
        if (col === ttMove) sc += 1 << 28;
        else if (col === KILL1[ply]) sc += 1 << 20;
        else if (col === KILL2[ply]) sc += 1 << 19;
        // 挿入ソート（降順）
        var j = mn;
        while (j > 0 && SBUF[base + j - 1] < sc) {
          SBUF[base + j] = SBUF[base + j - 1];
          MBUF[base + j] = MBUF[base + j - 1];
          j--;
        }
        SBUF[base + j] = sc; MBUF[base + j] = col; mn++;
      }
    }

    // 受けが 1 通りしかない場合は深さを消費しない（強制手延長）
    var childDepth = (mn === 1) ? depth : depth - 1;
    var best = -Infinity, bestMv = MBUF[base];
    var opp = player ^ 1;
    for (i = 0; i < mn; i++) {
      var mv = MBUF[base + i];
      make(mv, player);
      var v = -negamax(childDepth, ply + 1, -beta, -alpha, opp);
      unmake(mv, player);
      if (v > best) { best = v; bestMv = mv; }
      if (best > alpha) {
        alpha = best;
        if (alpha >= beta) {
          if (mv !== KILL1[ply]) { KILL2[ply] = KILL1[ply]; KILL1[ply] = mv; }
          HIST[(player << 4) | mv] += depth * depth;
          break;
        }
      }
    }

    // 置換表へ保存（詰みスコアはノード相対に変換）
    var storeScore = best;
    if (storeScore > WIN_THRESH) storeScore += ply;
    else if (storeScore < -WIN_THRESH) storeScore -= ply;
    var storeFlag = best <= alphaOrig ? 3 : (best >= beta ? 2 : 1);
    ttKey[hIdx] = hashB;
    ttScore[hIdx] = storeScore;
    ttInfo[hIdx] = bestMv | (Math.min(depth, 63) << 4) | (storeFlag << 10);
    return best;
  }

  // ---------- ルート探索（反復深化の 1 段） ----------
  var rootMoves = [], rootScores = [];
  var liveBestCol = -1;   // 打ち切り時に使う、探索中の暫定最善手

  function searchRoot(depth, player) {
    var alpha = -Infinity, best = -Infinity, bestMv = -1;
    var opp = player ^ 1;
    for (var i = 0; i < rootMoves.length; i++) {
      var mv = rootMoves[i];
      make(mv, player);
      var v = -negamax(depth - 1, 1, -Infinity, -alpha, opp);
      unmake(mv, player);
      rootScores[i] = v;
      if (v > best) { best = v; bestMv = mv; liveBestCol = mv; }
      if (v > alpha) alpha = v;
    }
    // 次の反復のために評価値の高い順へ並べ替え（安定ソート）
    var order = rootMoves.map(function (m, k) { return [m, rootScores[k], k]; });
    order.sort(function (a, b) { return (b[1] - a[1]) || (a[2] - b[2]); });
    for (i = 0; i < order.length; i++) { rootMoves[i] = order[i][0]; rootScores[i] = order[i][1]; }
    return { best: best, bestMv: bestMv };
  }

  // ---------- 公開 API ----------
  // history: これまでの着手（列番号 0..15 の配列、白から交互）
  // opts: { timeMs, maxDepth }
  // onProgress: 深さを 1 つ読み終えるたびに呼ばれる
  function search(history, opts, onProgress) {
    resetPosition();
    for (var i = 0; i < history.length; i++) make(history[i], i & 1);
    var player = history.length & 1;
    var budget = (opts && opts.timeMs) || 5000;
    var maxDepth = (opts && opts.maxDepth) || 30;
    var start = NOW();
    deadline = start + budget;
    nodes = 0;
    KILL1.fill(-1); KILL2.fill(-1); HIST.fill(0);

    function result(col, depth, score, extra) {
      var r = { col: col, depth: depth, score: score, nodes: nodes, elapsedMs: NOW() - start };
      if (extra) for (var k in extra) r[k] = extra[k];
      return r;
    }

    // 序盤定石: 最初の 2 手は中央 4 本のどれか（探索不要）
    if (history.length <= 1) {
      var centers = [5, 6, 9, 10].filter(function (c) { return heights[c] < N; });
      return result(centers[(Math.random() * centers.length) | 0], 0, 0, { book: true });
    }

    // 静的ショートカット: 即勝ち / 受けの強制
    scanNode(player);
    if (g_myWin >= 0) return result(g_myWin, 0, WIN_SCORE, { forced: true });
    if (g_nValid === 0) return result(-1, 0, 0);
    if (g_oppN >= 1) {
      // 受けは 1 通り（2 つ以上狙われていたら受からないが最善の抵抗として塞ぐ）
      return result(g_oppCol, 0, 0, { forced: true });
    }

    rootMoves.length = 0; rootScores.length = 0;
    var order = [];
    for (var col = 0; col < COLS; col++)
      if (heights[col] < N) order.push(col);
    order.sort(function (a, b) { return CENTER[b] - CENTER[a]; });
    for (i = 0; i < order.length; i++) { rootMoves.push(order[i]); rootScores.push(0); }

    var effMaxDepth = Math.min(maxDepth, CELLS - moveCnt);
    var bestCol = rootMoves[0], bestScore = 0, reached = 0;
    liveBestCol = -1;

    for (var d = 2; d <= effMaxDepth; d++) {
      if (NOW() - start > budget * 0.45) break;   // 次の反復が収まりそうにない
      liveBestCol = -1;
      var r;
      try {
        r = searchRoot(d, player);
      } catch (e) {
        if (e !== ABORT) throw e;
        // 時間切れ: 打ち切った反復で暫定最善が出ていればそれを採用
        if (liveBestCol >= 0) bestCol = liveBestCol;
        break;
      }
      bestCol = r.bestMv; bestScore = r.best; reached = d;
      if (onProgress) onProgress({ depth: d, score: bestScore, col: bestCol, nodes: nodes, elapsedMs: NOW() - start });
      // 勝ち / 負けが確定したらこれ以上深く読む意味がない
      if (bestScore > WIN_THRESH || bestScore < -WIN_THRESH) break;
      // 履歴ヒューリスティックを減衰
      for (i = 0; i < HIST.length; i++) HIST[i] >>= 1;
    }

    return result(bestCol, reached, bestScore);
  }

  return { search: search, lineCount: LINE_COUNT };
}

// ブラウザのメインスレッドから参照できるように公開（Worker 内では未定義）
if (typeof window !== 'undefined') window.SCORE4_ENGINE = SCORE4_ENGINE;
