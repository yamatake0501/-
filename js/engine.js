/* =========================================================
 * 立体四目並べ 思考エンジン（ビットボード版）
 *
 * - 反復深化 + αβ探索（ネガマックス）
 * - ビットボード（32bit × 2 ワードで 64 マスを表現）
 *     occ  : 両者の石の占有マス
 *     P    : 各列の着地マス（次に玉が落ちるマス）
 *     thrW / thrB : リーチマス（そこを埋めると 4 連が完成するマス）を
 *                   着手のたびに差分更新。即勝ち・受け強制・両狙いの
 *                   判定が「リーチマス AND 着地マス」の数命令で終わる
 * - 置換表（Zobrist ハッシュ）
 * - キラームーブ / 履歴ヒューリスティック
 * - ラインごとの玉数を差分更新する軽量評価関数
 * - 序盤定石: 初手〜4手目は隅が最善
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
  var CELL_LINES;                 // セル → そのセルを通るライン ID（平坦化）
  var LINE_CELLS;                 // ライン ID → 4 セル（平坦化）
  var LPC = new Int32Array(CELLS); // セルを通るライン数（手の並べ替えに使用）
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
    var per = [], cellsOf = [];
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
            for (var s = 0; s < 4; s++) {
              var cc = (x + d[0] * s) + (z + d[2] * s) * N + (y + d[1] * s) * N * N;
              per[cc].push(id);
              cellsOf.push(cc);
            }
          }
    var off = 0;
    for (i = 0; i < CELLS; i++) { CELL_LINES_OFF[i] = off; off += per[i].length; LPC[i] = per[i].length; }
    CELL_LINES_OFF[CELLS] = off;
    CELL_LINES = new Int16Array(off);
    LINE_CELLS = new Int8Array(LINE_COUNT * 4);
    var pos = 0;
    for (i = 0; i < CELLS; i++)
      for (k = 0; k < per[i].length; k++) CELL_LINES[pos++] = per[i][k];
    for (i = 0; i < cellsOf.length; i++) LINE_CELLS[i] = cellsOf[i];
  })();

  // ---------- ビット演算ユーティリティ ----------
  function pop32(x) {
    x = x - ((x >>> 1) & 0x55555555);
    x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
    x = (x + (x >>> 4)) & 0x0f0f0f0f;
    return Math.imul(x, 0x01010101) >>> 24;
  }
  function ctz32(x) { return 31 - Math.clz32(x & -x); }

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

  // ---------- 序盤定跡 ----------
  // 定跡書「重力付き3次元4目並べは後手不敗である」（山本, 2026）に基づく。
  // 論文の座標 (x, y) は列番号 col = x + 4y に対応する。
  // 局面（各列の石の積み方）をキーに、盤面の 8 対称すべてへ展開して登録する。
  var TCOL = [];    // TCOL[t][col] = 対称変換 t を施した列番号
  (function buildTransforms() {
    var fns = [
      function (x, y) { return [x, y]; },
      function (x, y) { return [y, x]; },
      function (x, y) { return [3 - x, y]; },
      function (x, y) { return [x, 3 - y]; },
      function (x, y) { return [3 - x, 3 - y]; },
      function (x, y) { return [y, 3 - x]; },
      function (x, y) { return [3 - y, x]; },
      function (x, y) { return [3 - y, 3 - x]; },
    ];
    for (var t = 0; t < 8; t++) {
      var map = new Int8Array(COLS);
      for (var col = 0; col < COLS; col++) {
        var p = fns[t](col & 3, col >> 2);
        map[col] = p[0] + 4 * p[1];
      }
      TCOL.push(map);
    }
  })();

  var BOOK = {};
  // side: 0 = 白の応手のみ登録, 1 = 黒のみ, 2 = 両方
  // from: 登録を始める手数（それ以前の手は「文脈」であり推奨手として教えない）
  function addBookLine(mvs, side, from) {
    for (var t = 0; t < 8; t++) {
      var hh = new Int8Array(COLS);
      var chars = [];
      for (var i = 0; i < CELLS; i++) chars.push('.');
      for (var k = 0; k < mvs.length; k++) {
        var tc = TCOL[t][mvs[k]];
        if (k >= from && (side === 2 || (k & 1) === side)) {
          var key = chars.join('');
          var arr = BOOK[key] || (BOOK[key] = []);
          if (arr.indexOf(tc) < 0) arr.push(tc);
        }
        chars[tc * 4 + hh[tc]] = (k & 1) === 0 ? 'w' : 'b';
        hh[tc]++;
      }
    }
  }
  (function buildBook() {
    // 本線（並行オープニング）: W(0,0) B(3,3) W(3,0) B(0,3) W(1,0) B(2,0) W(1,3)
    // 8手目の黒は (1,0) が唯一の正着（定跡書 Table 3）。
    // 以降は §4.4 の応酬 W(1,1) B(1,2) W(1,1) B(1,1) W(0,1) B(1,0)
    addBookLine([0, 15, 3, 12, 1, 2, 13, 1, 5, 9, 5, 5, 4, 1], 2, 0);
    // 8手目 B(2,0,1)（黒の最速の攻め）には白は即 (2,0,2) と受ける（§4.5 注記）
    addBookLine([0, 15, 3, 12, 1, 2, 13, 2, 2], 0, 8);
    // 8手目 B(1,1) への白の攻め（§4.1）: W(1,1,1) 以下、白有利の変化
    addBookLine([0, 15, 3, 12, 1, 2, 13, 5, 5, 5, 1, 1, 4, 4], 0, 8);
    // 8手目 B(1,2) への白の理想形（§4.2）: W(1,0) B(3,0) W(1,0) B(1,0) W(2,3)
    addBookLine([0, 15, 3, 12, 1, 2, 13, 9, 1, 3, 1, 1, 14], 0, 8);
    // 同変化で黒側は B(3,0) でなく B(0,0) と受けるのが改良手（§4.2 図17）
    addBookLine([0, 15, 3, 12, 1, 2, 13, 9, 1, 0, 1, 1], 1, 9);
    // 8手目 B(2,3) への白の攻め（§4.3）: W(1,2) から縦に圧力をかける白有利の変化
    addBookLine([0, 15, 3, 12, 1, 2, 13, 14, 9, 5, 9, 9, 5, 5, 1, 13, 1, 1], 0, 8);
    // 白が5手目で本線 (1,0)/(2,0) を外した場合、黒は (1,3) 型で受ける（§3.2）
    for (var x5 = 0; x5 < COLS; x5++) {
      if (x5 === 1 || x5 === 2 || x5 === 13 || x5 === 14) continue;
      addBookLine([0, 15, 3, 12, x5, 13], 1, 5);
      addBookLine([0, 15, 3, 12, x5, 13, 14, 2], 1, 7);
    }
    addBookLine([0, 15, 3, 12, 13, 14], 1, 5);
    addBookLine([0, 15, 3, 12, 14, 13], 1, 5);
  })();

  // 現局面（列ごとの石の積み方）のキー文字列
  function posKey(history) {
    var hh = new Int8Array(COLS);
    var chars = [];
    for (var i = 0; i < CELLS; i++) chars.push('.');
    for (var k = 0; k < history.length; k++) {
      var c = history[k];
      chars[c * 4 + hh[c]] = (k & 1) === 0 ? 'w' : 'b';
      hh[c]++;
    }
    return chars.join('');
  }

  // ---------- 置換表 ----------
  // info: move(4bit) | depth<<4 (6bit) | flag<<10 (1=exact, 2=lower, 3=upper)
  var TT_BITS = 21, TT_SIZE = 1 << TT_BITS, TT_MASK = TT_SIZE - 1;
  var ttKey = new Uint32Array(TT_SIZE);
  var ttInfo = new Uint32Array(TT_SIZE);
  var ttScore = new Int32Array(TT_SIZE);

  // ---------- 局面状態 ----------
  var heights = new Int8Array(COLS);
  // ラインごとの玉数を 1 バイトにパック: CNT[l] = (白の数 << 3) | 黒の数
  // 白 +1 は +8、黒 +1 は +1。CONTRIB の添字にそのまま使える
  var CNT = new Int8Array(LINE_COUNT);
  var S = 0;                        // 白から見た評価値（差分更新）
  var hashA = 0, hashB = 0;
  var moveCnt = 0;
  // ビットボード（lo: セル 0..31, hi: セル 32..63）
  var occLo = 0, occHi = 0;         // 占有マス（両者）
  var PLo = 0, PHi = 0;             // 着地マス（各列の次の空きマス）
  var thrLo = [0, 0], thrHi = [0, 0];          // [白, 黒] のリーチマス
  var thrCnt = [new Int8Array(CELLS), new Int8Array(CELLS)];  // 同一マスの多重リーチ数

  // ライン中の玉数 → 評価値。両者の玉が混在するラインは 0
  var WT = [0, 2, 12, 96, 0];
  var CONTRIB = new Int32Array(40);   // (w<<3)|b
  for (var w0 = 0; w0 <= 4; w0++)
    for (var b0 = 0; b0 <= 4; b0++)
      CONTRIB[(w0 << 3) | b0] = (w0 > 0 && b0 > 0) ? 0 : (w0 > 0 ? WT[w0] : -WT[b0]);

  function resetPosition() {
    heights.fill(0); CNT.fill(0);
    S = 0; hashA = 0; hashB = 0; moveCnt = 0;
    occLo = 0; occHi = 0;
    PLo = 0x0000FFFF; PHi = 0;       // 初期の着地マスは各列の最下段（セル 0..15）
    thrLo[0] = thrLo[1] = 0; thrHi[0] = thrHi[1] = 0;
    thrCnt[0].fill(0); thrCnt[1].fill(0);
  }

  function thrInc(p, cell) {
    if (thrCnt[p][cell]++ === 0) {
      if (cell < 32) thrLo[p] |= (1 << cell); else thrHi[p] |= (1 << (cell - 32));
    }
  }
  function thrDec(p, cell) {
    if (--thrCnt[p][cell] === 0) {
      if (cell < 32) thrLo[p] &= ~(1 << cell); else thrHi[p] &= ~(1 << (cell - 32));
    }
  }
  // ライン l の唯一の空きセルを返す（呼び出し側が空き 1 の状態を保証）
  function emptyCellOf(l) {
    var b4 = l << 2;
    for (var k = 0; k < 4; k++) {
      var cc = LINE_CELLS[b4 + k];
      if (cc < 32) { if ((occLo & (1 << cc)) === 0) return cc; }
      else { if ((occHi & (1 << (cc - 32))) === 0) return cc; }
    }
    return -1;  // 到達しない
  }

  function make(col, player) {          // player: 0=白, 1=黒
    var h = heights[col], idx = col + (h << 4);
    heights[col] = h + 1; moveCnt++;
    hashA = (hashA ^ ZA[(idx << 1) | player]) >>> 0;
    hashB = (hashB ^ ZB[(idx << 1) | player]) >>> 0;
    // 占有と着地マスの更新
    if (idx < 32) { occLo |= (1 << idx); PLo &= ~(1 << idx); }
    else { occHi |= (1 << (idx - 32)); PHi &= ~(1 << (idx - 32)); }
    if (h + 1 < N) {
      var up = idx + 16;
      if (up < 32) PLo |= (1 << up); else PHi |= (1 << (up - 32));
    }
    // ライン玉数・評価値・リーチマスの差分更新
    // CNT の特定値がリーチの遷移点になる:
    //   白16=(w2,b0)/黒2=(w0,b2) → 自分のリーチ完成
    //   白 3=(w0,b3)/黒24=(w3,b0) → 相手のリーチマスを埋めた
    var e = CELL_LINES_OFF[idx + 1], i, l, c;
    if (player === 0) {
      for (i = CELL_LINES_OFF[idx]; i < e; i++) {
        l = CELL_LINES[i]; c = CNT[l];
        S -= CONTRIB[c];
        if (c === 16) thrInc(0, emptyCellOf(l));
        else if (c === 3) thrDec(1, idx);
        CNT[l] = c + 8;
        S += CONTRIB[c + 8];
      }
    } else {
      for (i = CELL_LINES_OFF[idx]; i < e; i++) {
        l = CELL_LINES[i]; c = CNT[l];
        S -= CONTRIB[c];
        if (c === 2) thrInc(1, emptyCellOf(l));
        else if (c === 24) thrDec(0, idx);
        CNT[l] = c + 1;
        S += CONTRIB[c + 1];
      }
    }
  }

  function unmake(col, player) {
    var h = heights[col] - 1, idx = col + (h << 4);
    heights[col] = h; moveCnt--;
    hashA = (hashA ^ ZA[(idx << 1) | player]) >>> 0;
    hashB = (hashB ^ ZB[(idx << 1) | player]) >>> 0;
    // リーチマスの巻き戻し（占有はまだ元のまま = emptyCellOf が make 時と一致）
    //   白24=(w3,b0)/黒3=(w0,b3) → make で追加した自分のリーチを取り消す
    //   白11=(w1,b3)/黒25=(w3,b1) → make で消した相手リーチを復活させる
    var e = CELL_LINES_OFF[idx + 1], i, l, c;
    if (player === 0) {
      for (i = CELL_LINES_OFF[idx]; i < e; i++) {
        l = CELL_LINES[i]; c = CNT[l];
        S -= CONTRIB[c];
        if (c === 24) thrDec(0, emptyCellOf(l));
        else if (c === 11) thrInc(1, idx);
        CNT[l] = c - 8;
        S += CONTRIB[c - 8];
      }
    } else {
      for (i = CELL_LINES_OFF[idx]; i < e; i++) {
        l = CELL_LINES[i]; c = CNT[l];
        S -= CONTRIB[c];
        if (c === 3) thrDec(1, emptyCellOf(l));
        else if (c === 25) thrInc(0, idx);
        CNT[l] = c - 1;
        S += CONTRIB[c - 1];
      }
    }
    // 占有と着地マスの復元
    if (idx < 32) { occLo &= ~(1 << idx); PLo |= (1 << idx); }
    else { occHi &= ~(1 << (idx - 32)); PHi |= (1 << (idx - 32)); }
    if (h + 1 < N) {
      var up = idx + 16;
      if (up < 32) PLo &= ~(1 << up); else PHi &= ~(1 << (up - 32));
    }
  }

  // ---------- Tポイント評価（定跡書 §2 の形勢判断） ----------
  // Tポイント = 3段目（z=2）にあり直下（z=1）が空の決勝点（リーチマス）。
  //   白の T ポイント → 白勝ち含み / 黒の T ポイント → 白の有無に関わらず黒勝ち含み
  //   重複 T ポイント（同じマスが両者の決勝点）は 1 つ目が白、2 つ目以降は黒に味方する
  // さらに黒は偶数段（z=1, z=3）の浮き決勝点を持つと終盤の埋め合いで有利になる。
  // リーチマスをビットボードで持っているため、いずれも数命令で判定できる。
  function tpointEval() {
    var eb2 = (~occLo >>> 16) & 0xFFFF;            // z=1 が空の列
    var t0 = thrHi[0] & eb2;                       // 白の T ポイント（z=2 & 直下空）
    var t1 = thrHi[1] & eb2;                       // 黒の T ポイント
    var bonus = 0;
    if ((t0 | t1) !== 0) {
      var dup = t0 & t1;
      var w = pop32(t0 ^ dup), b = pop32(t1 ^ dup), d = pop32(dup);
      if (b > 0) bonus -= 450 + 120 * (b - 1);     // 黒 T は白 T に優先する
      else if (w > 0) bonus += 380 + 100 * (w - 1);
      if (d === 1) bonus += 260;
      else if (d >= 2) bonus -= 480;
    }
    // 黒の偶数段の浮き決勝点（z=1 で直下 z=0 が空 / z=3 で直下 z=2 が空）
    var be1 = (thrLo[1] >>> 16) & (~occLo & 0xFFFF);
    var be3 = (thrHi[1] >>> 16) & (~occHi & 0xFFFF);
    if ((be1 | be3) !== 0) bonus -= 45 * (pop32(be1) + pop32(be3));
    return bonus;
  }

  // ---------- 探索 ----------
  var ABORT = { aborted: true };
  var nodes = 0, deadline = 0;
  var MAX_PLY = 64;
  var KILL1 = new Int8Array(MAX_PLY), KILL2 = new Int8Array(MAX_PLY);
  var HIST = new Int32Array(2 * COLS);
  var MBUF = new Int8Array(MAX_PLY * COLS);
  var SBUF = new Int32Array(MAX_PLY * COLS);

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

    // ビットボードによる即勝ち / 受け強制 / 両狙いの検出
    var opp = player ^ 1;
    if (((thrLo[player] & PLo) | (thrHi[player] & PHi)) !== 0)
      return WIN_SCORE - ply;                              // 今すぐ勝てる
    if (moveCnt >= CELLS) return 0;                        // 満杯 → 引き分け
    var oLo = thrLo[opp] & PLo, oHi = thrHi[opp] & PHi;
    var oppN = (oLo === 0 && oHi === 0) ? 0 : pop32(oLo) + pop32(oHi);
    if (oppN >= 2) return -(WIN_SCORE - ply - 1);          // 両狙いは受からない
    if (depth <= 0 || ply >= MAX_PLY - 2) {
      var ev = S + tpointEval();
      return player === 0 ? ev : -ev;
    }

    // 候補手の生成と並べ替え
    var base = ply << 4, mn = 0, col, i;
    if (oppN === 1) {
      // 受けが強制（リーチマス = 着地マスなので列番号は下位 4bit）
      MBUF[base] = (oLo !== 0 ? ctz32(oLo) : 32 + ctz32(oHi)) & 15;
      mn = 1;
    } else {
      for (col = 0; col < COLS; col++) {
        var h = heights[col];
        if (h >= N) continue;
        var sc = HIST[(player << 4) | col] + LPC[col + (h << 4)] * 3;
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

    // 静的ショートカット: 即勝ち / 受けの強制
    var tLo = thrLo[player] & PLo, tHi = thrHi[player] & PHi;
    if ((tLo | tHi) !== 0)
      return result((tLo !== 0 ? ctz32(tLo) : 32 + ctz32(tHi)) & 15, 0, WIN_SCORE, { forced: true });
    if (moveCnt >= CELLS) return result(-1, 0, 0);
    var opp = player ^ 1;
    var oLo = thrLo[opp] & PLo, oHi = thrHi[opp] & PHi;
    if ((oLo | oHi) !== 0) {
      // 受けは 1 通り（2 つ以上狙われていたら受からないが最善の抵抗として塞ぐ）
      return result((oLo !== 0 ? ctz32(oLo) : 32 + ctz32(oHi)) & 15, 0, 0, { forced: true });
    }

    // 定跡データベース（局面キー・8対称展開済み）
    var bookCand = BOOK[posKey(history)];
    if (bookCand) {
      var playable = [];
      for (i = 0; i < bookCand.length; i++)
        if (heights[bookCand[i]] < N) playable.push(bookCand[i]);
      if (playable.length > 0)
        return result(playable[(Math.random() * playable.length) | 0], 0, 0, { book: true });
    }

    // 定跡を外れた序盤（初手〜4手目）は隅（コーナーの最下段）が最善
    if (history.length <= 3) {
      var corners = [0, 3, 12, 15].filter(function (c) { return heights[c] === 0; });
      if (corners.length > 0)
        return result(corners[(Math.random() * corners.length) | 0], 0, 0, { book: true });
    }

    rootMoves.length = 0; rootScores.length = 0;
    var order = [];
    for (var col = 0; col < COLS; col++)
      if (heights[col] < N) order.push(col);
    order.sort(function (a, b) {
      return LPC[b + (heights[b] << 4)] - LPC[a + (heights[a] << 4)];
    });
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

  // 解析用のルート探索。searchRoot と違い (1) その手自体が 4 連を完成させる
  // 即勝ちを検出し、(2) 各手をフルウィンドウで評価して勝率表示用の正確な
  // スコアを得る（αβ で刈られた上限値ではなく実値）。
  function analyzeRoot(depth, player) {
    var opp = player ^ 1, best = -Infinity, bestMv = -1;
    for (var i = 0; i < rootMoves.length; i++) {
      var mv = rootMoves[i];
      var idx = mv + (heights[mv] << 4);
      var win = (idx < 32) ? (thrLo[player] & (1 << idx)) : (thrHi[player] & (1 << (idx - 32)));
      var v;
      if (win !== 0) {
        v = WIN_SCORE - 1;                 // この手で即 4 連（1 手勝ち）
      } else {
        make(mv, player);
        v = -negamax(depth - 1, 1, -Infinity, Infinity, opp);
        unmake(mv, player);
      }
      rootScores[i] = v;
      if (v > best) { best = v; bestMv = mv; liveBestCol = mv; }
    }
    var order = rootMoves.map(function (m, k) { return [m, rootScores[k], k]; });
    order.sort(function (a, b) { return (b[1] - a[1]) || (a[2] - b[2]); });
    for (i = 0; i < order.length; i++) { rootMoves[i] = order[i][0]; rootScores[i] = order[i][1]; }
    return { best: best, bestMv: bestMv };
  }

  // ---------- 形勢解析（勝率表示用） ----------
  // 定跡・強制手のショートカットを使わず、全ての合法手を実際に探索して
  // 上位手とその評価値（手番側から見た値）を返す。表示専用。
  //   戻り値: { topMoves: [{col, score}, ...], depth, player }
  //   score は手番側視点。詰みは ±(WIN_SCORE - ply) 相当の大きな値になる。
  function analyze(history, opts) {
    resetPosition();
    for (var i = 0; i < history.length; i++) make(history[i], i & 1);
    var player = history.length & 1;
    var budget = (opts && opts.timeMs) || 1200;
    var maxDepth = (opts && opts.maxDepth) || 16;
    var start = NOW();
    deadline = start + budget;
    nodes = 0;
    KILL1.fill(-1); KILL2.fill(-1); HIST.fill(0);

    // 合法手を着地セルの通過ライン数で初期整列
    rootMoves.length = 0; rootScores.length = 0;
    var order = [];
    for (var col = 0; col < COLS; col++) if (heights[col] < N) order.push(col);
    if (order.length === 0) return { topMoves: [], depth: 0, player: player, full: true };
    order.sort(function (a, b) {
      return LPC[b + (heights[b] << 4)] - LPC[a + (heights[a] << 4)];
    });
    for (i = 0; i < order.length; i++) { rootMoves.push(order[i]); rootScores.push(0); }

    // 完了した反復の結果だけを採用するためのスナップショット
    var snap = [];
    for (i = 0; i < rootMoves.length; i++) snap.push({ col: rootMoves[i], score: 0 });
    var reached = 0;
    var effMaxDepth = Math.min(maxDepth, CELLS - moveCnt);

    for (var d = 1; d <= effMaxDepth; d++) {
      if (d > 1 && NOW() - start > budget * 0.45) break;
      try {
        analyzeRoot(d, player);
      } catch (e) {
        if (e !== ABORT) throw e;
        break;   // 中断した反復は破棄し、直前の完了結果を使う
      }
      snap = [];
      for (i = 0; i < rootMoves.length; i++) snap.push({ col: rootMoves[i], score: rootScores[i] });
      reached = d;
      if (snap[0].score > WIN_THRESH || snap[0].score < -WIN_THRESH) break;
      for (i = 0; i < HIST.length; i++) HIST[i] >>= 1;
    }

    var top = snap.slice(0, 5);
    return { topMoves: top, depth: reached, player: player, nodes: nodes, elapsedMs: NOW() - start };
  }

  // ---------- テスト用: リーチマス等の差分更新が正しいかの自己検査 ----------
  // history を 1 手ずつ再現し、毎手ごとに全ラインからリーチマスを再計算して
  // 差分更新の結果と比較する。戻り値 ok=false のときは step 手目で不一致。
  function selfTest(history) {
    resetPosition();
    function check(step) {
      var expLo = [0, 0], expHi = [0, 0];
      for (var l = 0; l < LINE_COUNT; l++) {
        var p = -1;
        if (CNT[l] === 24) p = 0;         // 白3・黒0
        else if (CNT[l] === 3) p = 1;     // 白0・黒3
        if (p < 0) continue;
        var cc = emptyCellOf(l);
        if (cc < 32) expLo[p] |= (1 << cc); else expHi[p] |= (1 << (cc - 32));
      }
      var expPLo = 0, expPHi = 0;
      for (var col = 0; col < COLS; col++) {
        if (heights[col] >= N) continue;
        var idx = col + (heights[col] << 4);
        if (idx < 32) expPLo |= (1 << idx); else expPHi |= (1 << (idx - 32));
      }
      return expLo[0] === thrLo[0] && expHi[0] === thrHi[0] &&
             expLo[1] === thrLo[1] && expHi[1] === thrHi[1] &&
             expPLo === PLo && expPHi === PHi;
    }
    for (var i = 0; i < history.length; i++) {
      make(history[i], i & 1);
      if (!check(i)) return { ok: false, step: i, phase: 'make' };
    }
    for (i = history.length - 1; i >= 0; i--) {
      unmake(history[i], i & 1);
      if (!check(i)) return { ok: false, step: i, phase: 'unmake' };
    }
    return { ok: true };
  }

  return { search: search, analyze: analyze, lineCount: LINE_COUNT, selfTest: selfTest };
}

// ブラウザのメインスレッドから参照できるように公開（Worker 内では未定義）
if (typeof window !== 'undefined') window.SCORE4_ENGINE = SCORE4_ENGINE;
