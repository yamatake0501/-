/* =========================================================
 * 立体四目並べ (Score Four)
 * 4x4 に立てた 16 本の棒に玉を落とし、
 * 縦・横・斜め・対角線のいずれかに自分の色を 4 つ並べたら勝ち。
 * ========================================================= */
(function () {
  'use strict';

  // ---------- 定数 ----------
  var EMPTY = 0, WHITE = 1, BLACK = 2;
  var N = 4;                 // 一辺のマス数
  var COLS = N * N;          // 棒の本数 = 16
  var CELLS = N * N * N;     // マス数 = 64

  var SPACING = 1.6;         // 棒の間隔
  var BALL_R = 0.55;         // 玉の半径
  var ROD_R = 0.09;          // 棒の半径
  var ROD_H = BALL_R * 2 * N + 0.45;  // 棒の高さ

  // セル番号: idx = x + z*4 + y*16  (y は高さ 0..3)
  function cellIndex(x, z, y) { return x + z * N + y * N * N; }

  // ---------- 勝利ライン列挙 ----------
  // 4x4x4 の格子内で一直線に並ぶ 4 マスの組をすべて機械的に列挙する。
  // 縦16 + 各段の縦横斜め40 + 垂直面の斜め16 + 立体対角線4 = 76 本。
  var LINES = [];
  var LINES_BY_CELL = [];
  (function buildLines() {
    var d, dirs = [];
    for (var dx = -1; dx <= 1; dx++)
      for (var dy = -1; dy <= 1; dy++)
        for (var dz = -1; dz <= 1; dz++) {
          if (dx === 0 && dy === 0 && dz === 0) continue;
          // 逆向きの重複を除くため、最初の非ゼロ成分が正の方向だけ採用
          if (dx < 0) continue;
          if (dx === 0 && dz < 0) continue;
          if (dx === 0 && dz === 0 && dy < 0) continue;
          dirs.push([dx, dy, dz]);
        }
    for (var i = 0; i < CELLS; i++) LINES_BY_CELL.push([]);
    for (var x = 0; x < N; x++)
      for (var z = 0; z < N; z++)
        for (var y = 0; y < N; y++)
          for (var k = 0; k < dirs.length; k++) {
            d = dirs[k];
            var ex = x + d[0] * 3, ey = y + d[1] * 3, ez = z + d[2] * 3;
            if (ex < 0 || ex >= N || ey < 0 || ey >= N || ez < 0 || ez >= N) continue;
            var line = [];
            for (var s = 0; s < 4; s++) line.push(cellIndex(x + d[0] * s, z + d[2] * s, y + d[1] * s));
            var li = LINES.length;
            LINES.push(line);
            for (s = 0; s < 4; s++) LINES_BY_CELL[line[s]].push(li);
          }
    if (LINES.length !== 76) {
      console.warn('勝利ライン数が想定(76)と異なります: ' + LINES.length);
    }
  })();

  // ---------- 盤面ロジック ----------
  function Board() {
    this.cells = new Int8Array(CELLS);
    this.heights = new Int8Array(COLS);
    this.history = [];         // {col, x, z, y, player}
  }
  Board.prototype.currentPlayer = function () {
    return (this.history.length % 2 === 0) ? WHITE : BLACK;
  };
  Board.prototype.canDrop = function (col) { return this.heights[col] < N; };
  Board.prototype.validCols = function () {
    var v = [];
    for (var c = 0; c < COLS; c++) if (this.heights[c] < N) v.push(c);
    return v;
  };
  // 玉を落とす。落ちた段 y を返す（満杯なら -1）
  Board.prototype.drop = function (col) {
    if (this.heights[col] >= N) return -1;
    var x = col % N, z = (col / N) | 0;
    var y = this.heights[col];
    var player = this.currentPlayer();
    this.cells[cellIndex(x, z, y)] = player;
    this.heights[col]++;
    this.history.push({ col: col, x: x, z: z, y: y, player: player });
    return y;
  };
  Board.prototype.undo = function () {
    var mv = this.history.pop();
    if (!mv) return null;
    this.cells[cellIndex(mv.x, mv.z, mv.y)] = EMPTY;
    this.heights[mv.col]--;
    return mv;
  };
  // 直前の着手で勝ったか。勝ちならそのライン(セル番号4つ)を返す
  Board.prototype.winLineAt = function (x, z, y) {
    var idx = cellIndex(x, z, y);
    var player = this.cells[idx];
    var lids = LINES_BY_CELL[idx];
    for (var i = 0; i < lids.length; i++) {
      var line = LINES[lids[i]];
      if (this.cells[line[0]] === player &&
          this.cells[line[1]] === player &&
          this.cells[line[2]] === player &&
          this.cells[line[3]] === player) return line;
    }
    return null;
  };
  Board.prototype.isFull = function () { return this.history.length >= CELLS; };

  // ---------- CPU（コンピュータ） ----------
  var WIN_SCORE = 100000;
  var WEIGHTS = [0, 1, 8, 64];   // ライン中の自分の玉 1〜3 個の価値

  function evaluate(board, player) {
    var score = 0, cells = board.cells;
    for (var i = 0; i < LINES.length; i++) {
      var line = LINES[i], w = 0, b = 0;
      for (var s = 0; s < 4; s++) {
        var v = cells[line[s]];
        if (v === WHITE) w++; else if (v === BLACK) b++;
      }
      if (w > 0 && b > 0) continue;         // 両者混在 → 死にライン
      if (w > 0) score += (player === WHITE ? WEIGHTS[w] : -WEIGHTS[w]);
      else if (b > 0) score += (player === BLACK ? WEIGHTS[b] : -WEIGHTS[b]);
    }
    return score;
  }

  // 中央寄りの列を先に読む（枝刈り効率と自然な着手のため）
  var COL_ORDER = (function () {
    var order = [];
    for (var c = 0; c < COLS; c++) order.push(c);
    order.sort(function (a, b) {
      function d(c2) {
        var x = c2 % N, z = (c2 / N) | 0;
        return Math.abs(x - 1.5) + Math.abs(z - 1.5);
      }
      return d(a) - d(b);
    });
    return order;
  })();

  function negamax(board, depth, alpha, beta, ply) {
    var me = board.currentPlayer();
    var best = -Infinity, played = false;
    for (var i = 0; i < COL_ORDER.length; i++) {
      var col = COL_ORDER[i];
      if (!board.canDrop(col)) continue;
      played = true;
      var y = board.drop(col);
      var score;
      if (board.winLineAt(col % N, (col / N) | 0, y)) {
        score = WIN_SCORE - ply;             // 早い勝ちほど高評価
      } else if (board.isFull()) {
        score = 0;
      } else if (depth <= 1) {
        score = evaluate(board, me);
      } else {
        score = -negamax(board, depth - 1, -beta, -alpha, ply + 1);
      }
      board.undo();
      if (score > best) best = score;
      if (best > alpha) alpha = best;
      if (alpha >= beta) break;
    }
    return played ? best : 0;
  }

  function cpuChooseMove(board, level) {
    var cols = board.validCols();
    if (cols.length === 0) return -1;
    var me = board.currentPlayer();
    var opp = (me === WHITE) ? BLACK : WHITE;
    var i, col, y;

    // 1手で勝てるなら勝つ
    for (i = 0; i < cols.length; i++) {
      col = cols[i];
      y = board.drop(col);
      var win = board.winLineAt(col % N, (col / N) | 0, y);
      board.undo();
      if (win) return col;
    }
    // 相手の即勝ちは塞ぐ
    for (i = 0; i < cols.length; i++) {
      col = cols[i];
      // 相手が col に置いたと仮定して勝つか調べる
      var x = col % N, z = (col / N) | 0, h = board.heights[col];
      board.cells[cellIndex(x, z, h)] = opp;
      var oppWin = board.winLineAt(x, z, h);
      board.cells[cellIndex(x, z, h)] = EMPTY;
      if (oppWin) return col;
    }

    if (level <= 1) {
      // かんたん: 中央寄りをゆるく好むランダム
      var pool = [];
      for (i = 0; i < cols.length; i++) {
        col = cols[i];
        var cx = col % N, cz = (col / N) | 0;
        var wgt = 5 - Math.abs(cx - 1.5) - Math.abs(cz - 1.5);
        for (var k = 0; k < wgt; k++) pool.push(col);
      }
      return pool[(Math.random() * pool.length) | 0];
    }

    var depth = 2;   // レベル2。レベル3以上は engine.js（Worker）が担当する
    var best = -Infinity, bestCols = [];
    for (i = 0; i < COL_ORDER.length; i++) {
      col = COL_ORDER[i];
      if (!board.canDrop(col)) continue;
      y = board.drop(col);
      var score;
      if (board.winLineAt(col % N, (col / N) | 0, y)) score = WIN_SCORE;
      else if (board.isFull()) score = 0;
      else score = -negamax(board, depth - 1, -Infinity, Infinity, 1);
      board.undo();
      if (score > best + 0.5) { best = score; bestCols = [col]; }
      else if (score >= best - 0.5) bestCols.push(col);
    }
    return bestCols[(Math.random() * bestCols.length) | 0];
  }

  // ---------- 3D シーン ----------
  var stage = document.getElementById('stage');
  var renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.shadowMap.enabled = true;
  renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  stage.appendChild(renderer.domElement);

  var scene = new THREE.Scene();
  scene.background = new THREE.Color(0x1b2230);
  scene.fog = new THREE.Fog(0x1b2230, 26, 48);

  var camera = new THREE.PerspectiveCamera(45, 1, 0.1, 100);
  var CAM_TARGET = new THREE.Vector3(0, 2.0, 0);
  var camSph = { theta: Math.PI / 4, phi: 1.05, radius: 13 }; // 視点（球面座標）
  var CAM_HOME = { theta: Math.PI / 4, phi: 1.05, radius: 13 };

  function updateCamera() {
    camSph.phi = Math.max(0.15, Math.min(1.52, camSph.phi));
    camSph.radius = Math.max(6, Math.min(28, camSph.radius));
    var r = camSph.radius, p = camSph.phi, t = camSph.theta;
    camera.position.set(
      CAM_TARGET.x + r * Math.sin(p) * Math.sin(t),
      CAM_TARGET.y + r * Math.cos(p),
      CAM_TARGET.z + r * Math.sin(p) * Math.cos(t)
    );
    camera.lookAt(CAM_TARGET);
  }

  function resize() {
    var w = stage.clientWidth, h = stage.clientHeight;
    renderer.setSize(w, h);
    camera.aspect = w / h;
    camera.updateProjectionMatrix();
  }
  window.addEventListener('resize', resize);

  // 照明
  scene.add(new THREE.AmbientLight(0xffffff, 0.55));
  var sun = new THREE.DirectionalLight(0xfff2dd, 0.9);
  sun.position.set(8, 14, 6);
  sun.castShadow = true;
  sun.shadow.mapSize.set(2048, 2048);
  sun.shadow.camera.left = -8; sun.shadow.camera.right = 8;
  sun.shadow.camera.top = 8; sun.shadow.camera.bottom = -8;
  scene.add(sun);
  var fill = new THREE.DirectionalLight(0xaaccff, 0.25);
  fill.position.set(-6, 8, -8);
  scene.add(fill);

  // 台座
  var baseSize = SPACING * 3 + 2.2;
  var base = new THREE.Mesh(
    new THREE.BoxGeometry(baseSize, 0.4, baseSize),
    new THREE.MeshStandardMaterial({ color: 0x7a5230, roughness: 0.75, metalness: 0.05 })
  );
  base.position.y = -0.2;
  base.receiveShadow = true;
  scene.add(base);

  // 床: ライトの影響を受けない控えめな円盤 + 影だけを受ける層
  var ground = new THREE.Mesh(
    new THREE.CircleGeometry(16, 48),
    new THREE.MeshBasicMaterial({ color: 0x222b40 })
  );
  ground.rotation.x = -Math.PI / 2;
  ground.position.y = -0.42;
  scene.add(ground);

  var groundShadow = new THREE.Mesh(
    new THREE.CircleGeometry(16, 48),
    new THREE.ShadowMaterial({ opacity: 0.35 })
  );
  groundShadow.rotation.x = -Math.PI / 2;
  groundShadow.position.y = -0.415;
  groundShadow.receiveShadow = true;
  scene.add(groundShadow);

  function colPos(col) {
    var x = col % N, z = (col / N) | 0;
    return { x: (x - 1.5) * SPACING, z: (z - 1.5) * SPACING };
  }
  function ballY(level) { return BALL_R + level * BALL_R * 2; }

  // 棒 + クリック判定用の透明シリンダー + 番号ラベル
  var rodMats = [];
  var rodDefaultMat = new THREE.MeshStandardMaterial({ color: 0xc9a86a, roughness: 0.5, metalness: 0.35 });
  var rodHoverMat = new THREE.MeshStandardMaterial({ color: 0xffe08a, roughness: 0.35, metalness: 0.4, emissive: 0x664411 });
  var pickTargets = [];
  (function buildRods() {
    var rodGeo = new THREE.CylinderGeometry(ROD_R, ROD_R, ROD_H, 16);
    var capGeo = new THREE.SphereGeometry(ROD_R * 1.6, 12, 12);
    var pickGeo = new THREE.CylinderGeometry(SPACING * 0.46, SPACING * 0.46, ROD_H + 1.2, 8);
    var pickMat = new THREE.MeshBasicMaterial({ visible: false });
    for (var c = 0; c < COLS; c++) {
      var p = colPos(c);
      var rod = new THREE.Mesh(rodGeo, rodDefaultMat);
      rod.position.set(p.x, ROD_H / 2, p.z);
      rod.castShadow = true;
      scene.add(rod);
      rodMats.push(rod);

      var cap = new THREE.Mesh(capGeo, rodDefaultMat);
      cap.position.set(p.x, ROD_H, p.z);
      scene.add(cap);

      var pick = new THREE.Mesh(pickGeo, pickMat);
      pick.position.set(p.x, (ROD_H + 1.2) / 2 - 0.4, p.z);
      pick.userData.col = c;
      scene.add(pick);
      pickTargets.push(pick);

      scene.add(makeLabel(String(c + 1), p.x, 0.28, p.z + SPACING * 0.38));
    }
  })();

  function makeLabel(text, x, y, z) {
    var cv = document.createElement('canvas');
    cv.width = cv.height = 96;
    var ctx = cv.getContext('2d');
    ctx.font = 'bold 56px sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.lineWidth = 9;
    ctx.strokeStyle = 'rgba(20,24,36,0.9)';
    ctx.strokeText(text, 48, 50);
    ctx.fillStyle = '#ffe9a8';
    ctx.fillText(text, 48, 50);
    var tex = new THREE.CanvasTexture(cv);
    var spr = new THREE.Sprite(new THREE.SpriteMaterial({ map: tex, depthTest: true }));
    spr.scale.set(0.55, 0.55, 1);
    spr.position.set(x, y, z);
    return spr;
  }

  // 玉のマテリアル
  var whiteMat = new THREE.MeshStandardMaterial({ color: 0xf2f3f5, roughness: 0.25, metalness: 0.05 });
  var blackMat = new THREE.MeshStandardMaterial({ color: 0x23262e, roughness: 0.3, metalness: 0.25 });
  var whiteWinMat = whiteMat.clone(); whiteWinMat.emissive = new THREE.Color(0x2a6b2a);
  var blackWinMat = blackMat.clone(); blackWinMat.emissive = new THREE.Color(0x2a6b2a);
  var ghostWhiteMat = new THREE.MeshStandardMaterial({ color: 0xf2f3f5, transparent: true, opacity: 0.35, roughness: 0.4 });
  var ghostBlackMat = new THREE.MeshStandardMaterial({ color: 0x3a3f4c, transparent: true, opacity: 0.4, roughness: 0.4 });
  var ballGeo = new THREE.SphereGeometry(BALL_R, 28, 22);

  var ghostBall = new THREE.Mesh(ballGeo, ghostWhiteMat);
  ghostBall.visible = false;
  scene.add(ghostBall);

  // ---------- ゲーム状態 ----------
  var board = new Board();
  var ballMeshes = [];            // history と同順
  var gameState = 'playing';      // 'playing' | 'over'
  var winnerInfo = null;          // {winner, reason, line}
  var winMarkers = [];            // 勝利演出用オブジェクト
  var falling = null;             // 落下アニメーション中の玉
  var cpuTimer = null;
  var hoveredCol = -1;

  var settings = { mode: 'pvp', level: 2, timeLimit: 0 };
  var turnDeadline = 0;           // performance.now() 基準
  var timerActive = false;

  function isCpuTurn() {
    if (gameState !== 'playing') return false;
    if (settings.mode === 'cpu-white') return board.currentPlayer() === BLACK;
    if (settings.mode === 'cpu-black') return board.currentPlayer() === WHITE;
    return false;
  }
  function humanCanAct() {
    return gameState === 'playing' && !falling && !isCpuTurn();
  }

  // ---------- UI 要素 ----------
  var turnIndicator = document.getElementById('turnIndicator');
  var timerDisplay = document.getElementById('timerDisplay');
  var keyBufDisplay = document.getElementById('keyBufDisplay');
  var overlay = document.getElementById('overlay');
  var overlayMessage = document.getElementById('overlayMessage');
  var undoBtn = document.getElementById('undoBtn');

  function playerName(p) { return p === WHITE ? '白' : '黒'; }
  function ballIcon(p) { return '<span class="ball ' + (p === WHITE ? 'white' : 'black') + '"></span>'; }

  function updateStatus() {
    if (gameState === 'over') {
      if (winnerInfo.winner) {
        turnIndicator.innerHTML = ballIcon(winnerInfo.winner) + playerName(winnerInfo.winner) + 'の勝ち！' +
          (winnerInfo.reason === 'time' ? '（時間切れ）' : '');
      } else {
        turnIndicator.innerHTML = '引き分け';
      }
    } else {
      var p = board.currentPlayer();
      var who = '';
      if (settings.mode !== 'pvp') who = isCpuTurn() ? '（CPU）' : '（あなた）';
      turnIndicator.innerHTML = ballIcon(p) + playerName(p) + 'の番です' + who;
    }
    undoBtn.disabled = board.history.length === 0 || !!falling;
  }

  function startTurnTimer() {
    if (settings.timeLimit > 0 && gameState === 'playing') {
      turnDeadline = performance.now() + settings.timeLimit * 1000;
      timerActive = true;
      timerDisplay.classList.remove('hidden');
    } else {
      timerActive = false;
      timerDisplay.classList.add('hidden');
    }
  }

  function updateTimerDisplay(now) {
    if (!timerActive) return;
    if (falling) { turnDeadline += 16; return; }  // 落下演出中は進めない
    var rest = (turnDeadline - now) / 1000;
    if (rest <= 0) {
      timerActive = false;
      var loser = board.currentPlayer();
      endGame((loser === WHITE) ? BLACK : WHITE, 'time', null);
      return;
    }
    timerDisplay.textContent = '残り ' + rest.toFixed(1) + ' 秒';
    timerDisplay.classList.toggle('warn', rest < 5);
  }

  // ---------- 着手 ----------
  function tryMove(col) {
    if (gameState !== 'playing' || falling) return false;
    if (!board.canDrop(col)) return false;
    var player = board.currentPlayer();
    var y = board.drop(col);
    var p = colPos(col);
    var mesh = new THREE.Mesh(ballGeo, player === WHITE ? whiteMat : blackMat);
    mesh.castShadow = true;
    mesh.receiveShadow = true;
    mesh.position.set(p.x, ROD_H + BALL_R + 0.35, p.z);
    scene.add(mesh);
    ballMeshes.push(mesh);
    falling = {
      mesh: mesh,
      targetY: ballY(y),
      v: 0,
      bounced: false,
      x: p.x, z: p.z,
      moveX: col % N, moveZ: (col / N) | 0, moveY: y
    };
    hideGhost();
    updateStatus();
    return true;
  }

  function onLanded() {
    var f = falling;
    falling = null;
    var line = board.winLineAt(f.moveX, f.moveZ, f.moveY);
    if (line) {
      endGame(board.cells[line[0]], 'line', line);
      return;
    }
    if (board.isFull()) {
      endGame(0, 'draw', null);
      return;
    }
    startTurnTimer();
    updateStatus();
    maybeCpuMove();
  }

  function maybeCpuMove() {
    if (!isCpuTurn() || falling) return;
    clearTimeout(cpuTimer);
    if (settings.level <= 2) {
      cpuTimer = setTimeout(function () {
        if (!isCpuTurn() || falling) return;
        var col = cpuChooseMove(board, settings.level);
        if (col >= 0) tryMove(col);
      }, 450);
    } else {
      cpuTimer = setTimeout(startEngineSearch, 250);
    }
  }

  // ---------- 探索エンジン（レベル3以上・Worker で思考） ----------
  var thinkDisplay = document.getElementById('thinkDisplay');
  var engineWorker = null;
  var engineSearchId = 0;       // 古い探索結果を捨てるためのトークン
  var cpuThinking = false;
  var syncEngine = null;        // Worker が使えない環境用のフォールバック

  function makeEngineWorker() {
    try {
      var code =
        'var API = (' + SCORE4_ENGINE.toString() + ')();\n' +
        'self.onmessage = function (e) {\n' +
        '  var m = e.data;\n' +
        '  if (m.type !== "search") return;\n' +
        '  var r = API.search(m.history, m.opts, function (p) {\n' +
        '    p.type = "progress"; p.id = m.id; self.postMessage(p);\n' +
        '  });\n' +
        '  r.type = "result"; r.id = m.id; self.postMessage(r);\n' +
        '};\n';
      var url = URL.createObjectURL(new Blob([code], { type: 'application/javascript' }));
      var w = new Worker(url);
      URL.revokeObjectURL(url);
      return w;
    } catch (err) {
      return null;
    }
  }

  function showThinking(text) {
    thinkDisplay.textContent = text;
    thinkDisplay.classList.remove('hidden');
  }
  function hideThinking() {
    thinkDisplay.classList.add('hidden');
  }

  function cancelCpuSearch() {
    engineSearchId++;
    clearTimeout(cpuTimer);
    if (cpuThinking && engineWorker) {
      engineWorker.terminate();   // 探索は中断できないので Worker ごと破棄
      engineWorker = null;
    }
    cpuThinking = false;
    hideThinking();
  }

  function engineBudgetMs() {
    var budget = (settings.level >= 4) ? 50000 : 5000;
    if (settings.timeLimit > 0) {
      // 落下アニメーション等の余裕をみて制限時間内に収める
      budget = Math.max(400, Math.min(budget, settings.timeLimit * 1000 - 2500));
    }
    return budget;
  }

  function onEngineProgress(p) {
    showThinking('CPU思考中… 深さ' + p.depth +
      '（' + (p.elapsedMs / 1000).toFixed(1) + '秒・' +
      (p.nodes >= 1e6 ? (p.nodes / 1e6).toFixed(1) + 'M' : ((p.nodes / 1e3) | 0) + 'k') + '局面）');
  }

  function onEngineResult(res) {
    cpuThinking = false;
    hideThinking();
    if (!isCpuTurn() || falling || gameState !== 'playing') return;
    if (res.col >= 0 && board.canDrop(res.col)) {
      tryMove(res.col);
    } else {
      var col = cpuChooseMove(board, 2);   // 万一に備えたフォールバック
      if (col >= 0) tryMove(col);
    }
  }

  function startEngineSearch() {
    if (!isCpuTurn() || falling || gameState !== 'playing') return;
    var id = ++engineSearchId;
    cpuThinking = true;
    showThinking('CPU思考中…');
    var history = board.history.map(function (m) { return m.col; });
    var opts = { timeMs: engineBudgetMs(), maxDepth: 30 };

    if (engineWorker === null) engineWorker = makeEngineWorker();
    if (engineWorker) {
      engineWorker.onmessage = function (e) {
        var m = e.data;
        if (m.id !== engineSearchId) return;     // 古い探索の結果は捨てる
        if (m.type === 'progress') onEngineProgress(m);
        else if (m.type === 'result') onEngineResult(m);
      };
      engineWorker.onerror = function () {
        // Worker 内エラー時はフォールバックで手を返す
        if (id !== engineSearchId) return;
        engineWorker.terminate();
        engineWorker = null;
        onEngineResult({ col: -1 });
      };
      engineWorker.postMessage({ type: 'search', id: id, history: history, opts: opts });
    } else {
      // Worker が作れない環境: メインスレッドで短めに探索（UI は固まる）
      setTimeout(function () {
        if (id !== engineSearchId) return;
        if (!syncEngine) syncEngine = SCORE4_ENGINE();
        opts.timeMs = Math.min(opts.timeMs, 8000);
        var r = syncEngine.search(history, opts, null);
        if (id !== engineSearchId) return;
        onEngineResult(r);
      }, 60);
    }
  }

  function endGame(winner, reason, line) {
    cancelCpuSearch();
    gameState = 'over';
    timerActive = false;
    timerDisplay.classList.add('hidden');
    winnerInfo = { winner: winner, reason: reason, line: line };
    if (line) showWinLine(line);
    if (winner) {
      overlayMessage.innerHTML = ballIcon(winner) + playerName(winner) + 'の勝ち！' +
        (reason === 'time' ? '<small style="font-size:15px">（時間切れ）</small>' : '');
    } else {
      overlayMessage.textContent = '引き分けです';
    }
    overlay.classList.remove('hidden');
    updateStatus();
  }

  function showWinLine(line) {
    // 勝った 4 つの玉を光らせ、貫く光の棒を表示する
    var pts = [];
    for (var i = 0; i < 4; i++) {
      var idx = line[i];
      var x = idx % N, z = ((idx / N) | 0) % N, y = (idx / (N * N)) | 0;
      pts.push(new THREE.Vector3((x - 1.5) * SPACING, ballY(y), (z - 1.5) * SPACING));
      // 対応する玉メッシュを光らせる
      for (var m = 0; m < board.history.length; m++) {
        var mv = board.history[m];
        if (mv.x === x && mv.z === z && mv.y === y) {
          ballMeshes[m].material = (mv.player === WHITE) ? whiteWinMat : blackWinMat;
          winMarkers.push({ type: 'ball', mesh: ballMeshes[m], mat: mv.player === WHITE ? whiteMat : blackMat });
        }
      }
    }
    var a = pts[0], b = pts[3];
    var dir = new THREE.Vector3().subVectors(b, a);
    var len = dir.length() + BALL_R * 1.4;
    var beam = new THREE.Mesh(
      new THREE.CylinderGeometry(0.09, 0.09, len, 12),
      new THREE.MeshBasicMaterial({ color: 0x66ff88, transparent: true, opacity: 0.9 })
    );
    beam.position.copy(a).add(b).multiplyScalar(0.5);
    beam.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), dir.clone().normalize());
    scene.add(beam);
    winMarkers.push({ type: 'beam', mesh: beam });
  }

  function clearWinMarkers() {
    for (var i = 0; i < winMarkers.length; i++) {
      var w = winMarkers[i];
      if (w.type === 'beam') { scene.remove(w.mesh); w.mesh.geometry.dispose(); w.mesh.material.dispose(); }
      else w.mesh.material = w.mat;
    }
    winMarkers = [];
  }

  // ---------- 待った / 新規ゲーム ----------
  function undoOnce() {
    var mv = board.undo();
    if (!mv) return false;
    var mesh = ballMeshes.pop();
    scene.remove(mesh);
    return true;
  }

  function undoMove() {
    if (falling || board.history.length === 0) return;
    cancelCpuSearch();
    clearWinMarkers();
    overlay.classList.add('hidden');
    if (settings.mode === 'pvp') {
      undoOnce();
    } else {
      // CPU 戦では自分の手番に戻るまで（最大2手）戻す
      var human = (settings.mode === 'cpu-white') ? WHITE : BLACK;
      undoOnce();
      if (board.currentPlayer() !== human && board.history.length > 0) undoOnce();
    }
    gameState = 'playing';
    winnerInfo = null;
    startTurnTimer();
    updateStatus();
    maybeCpuMove();  // 自分が後手で初手まで戻した場合など、CPU 番なら指させる
  }

  function newGame() {
    cancelCpuSearch();
    clearWinMarkers();
    while (board.history.length > 0) undoOnce();
    falling = null;
    gameState = 'playing';
    winnerInfo = null;
    overlay.classList.add('hidden');
    keyBuf = '';
    updateKeyBufDisplay();
    startTurnTimer();
    updateStatus();
    maybeCpuMove();
  }

  // ---------- ゴースト表示（着地予告） ----------
  function showGhost(col) {
    if (!humanCanAct() || !board.canDrop(col)) { hideGhost(); return; }
    var p = colPos(col);
    ghostBall.material = (board.currentPlayer() === WHITE) ? ghostWhiteMat : ghostBlackMat;
    ghostBall.position.set(p.x, ballY(board.heights[col]), p.z);
    ghostBall.visible = true;
    rodMats[col].material = rodHoverMat;
  }
  function hideGhost() {
    ghostBall.visible = false;
    for (var c = 0; c < COLS; c++) rodMats[c].material = rodDefaultMat;
  }

  // ---------- マウス / タッチ操作 ----------
  var raycaster = new THREE.Raycaster();
  var pointerNdc = new THREE.Vector2();
  var dragging = false, dragMoved = false;
  var lastPX = 0, lastPY = 0, downPX = 0, downPY = 0;

  function pickCol(clientX, clientY) {
    var rect = renderer.domElement.getBoundingClientRect();
    pointerNdc.x = ((clientX - rect.left) / rect.width) * 2 - 1;
    pointerNdc.y = -((clientY - rect.top) / rect.height) * 2 + 1;
    raycaster.setFromCamera(pointerNdc, camera);
    var hits = raycaster.intersectObjects(pickTargets, false);
    return hits.length ? hits[0].object.userData.col : -1;
  }

  renderer.domElement.addEventListener('pointerdown', function (e) {
    dragging = true; dragMoved = false;
    lastPX = downPX = e.clientX; lastPY = downPY = e.clientY;
    renderer.domElement.setPointerCapture(e.pointerId);
  });

  renderer.domElement.addEventListener('pointermove', function (e) {
    if (dragging) {
      var dx = e.clientX - lastPX, dy = e.clientY - lastPY;
      lastPX = e.clientX; lastPY = e.clientY;
      if (Math.abs(e.clientX - downPX) + Math.abs(e.clientY - downPY) > 6) dragMoved = true;
      if (dragMoved) {
        camSph.theta -= dx * 0.008;
        camSph.phi -= dy * 0.006;
        updateCamera();
        hideGhost();
        hoveredCol = -1;
        return;
      }
    }
    var col = pickCol(e.clientX, e.clientY);
    if (col !== hoveredCol) {
      hoveredCol = col;
      if (col >= 0) showGhost(col); else hideGhost();
    } else if (col >= 0 && humanCanAct()) {
      showGhost(col);   // 手番が変わった直後にも追従させる
    }
  });

  renderer.domElement.addEventListener('pointerup', function (e) {
    if (!dragging) return;
    dragging = false;
    if (!dragMoved && e.button === 0) {
      var col = pickCol(e.clientX, e.clientY);
      if (col >= 0 && humanCanAct()) tryMove(col);
    }
  });

  renderer.domElement.addEventListener('pointerleave', function () {
    hoveredCol = -1;
    hideGhost();
  });

  renderer.domElement.addEventListener('wheel', function (e) {
    e.preventDefault();
    camSph.radius *= (e.deltaY > 0 ? 1.08 : 0.93);
    updateCamera();
  }, { passive: false });

  // ---------- キーボード操作 ----------
  var keyBuf = '';
  var keyBufTimer = null;

  function updateKeyBufDisplay() {
    if (keyBuf) {
      keyBufDisplay.textContent = '棒番号: ' + keyBuf + '_';
      keyBufDisplay.classList.remove('hidden');
    } else {
      keyBufDisplay.classList.add('hidden');
    }
  }
  function commitKeyBuf() {
    clearTimeout(keyBufTimer);
    var num = parseInt(keyBuf, 10);
    keyBuf = '';
    updateKeyBufDisplay();
    if (num >= 1 && num <= 16 && humanCanAct()) tryMove(num - 1);
  }

  window.addEventListener('keydown', function (e) {
    if (e.target.tagName === 'SELECT' || e.target.tagName === 'INPUT') return;
    if (e.key >= '0' && e.key <= '9') {
      clearTimeout(keyBufTimer);
      keyBuf += e.key;
      var num = parseInt(keyBuf, 10);
      if (num < 1 || num > 16) { keyBuf = ''; updateKeyBufDisplay(); return; }
      updateKeyBufDisplay();
      if (keyBuf.length >= 2 || num >= 2) commitKeyBuf();          // これ以上桁を足せない → 確定
      else keyBufTimer = setTimeout(commitKeyBuf, 900);            // "1" は 10〜16 の可能性を少し待つ
    } else if (e.key === 'Enter') {
      if (keyBuf) commitKeyBuf();
    } else if (e.key === 'Escape') {
      keyBuf = '';
      updateKeyBufDisplay();
    } else if (e.key === 'u' || e.key === 'U') {
      undoMove();
    }
  });

  // ---------- コントロール ----------
  var modeSelect = document.getElementById('modeSelect');
  var levelSelect = document.getElementById('levelSelect');
  var levelWrap = document.getElementById('levelWrap');
  var timeSelect = document.getElementById('timeSelect');

  modeSelect.addEventListener('change', function () {
    settings.mode = modeSelect.value;
    levelWrap.classList.toggle('hidden', settings.mode === 'pvp');
    newGame();
  });
  levelSelect.addEventListener('change', function () {
    settings.level = parseInt(levelSelect.value, 10);
    if (isCpuTurn()) {           // 思考中に強さが変わったら読み直す
      cancelCpuSearch();
      maybeCpuMove();
    }
  });
  timeSelect.addEventListener('change', function () {
    settings.timeLimit = parseInt(timeSelect.value, 10);
    if (gameState === 'playing') startTurnTimer();  // 現在の手番から適用
  });
  document.getElementById('newGameBtn').addEventListener('click', newGame);
  undoBtn.addEventListener('click', undoMove);
  document.getElementById('overlayUndoBtn').addEventListener('click', undoMove);
  document.getElementById('rematchBtn').addEventListener('click', newGame);
  document.getElementById('closeOverlayBtn').addEventListener('click', function () {
    overlay.classList.add('hidden');
  });
  document.getElementById('resetViewBtn').addEventListener('click', function () {
    camSph.theta = CAM_HOME.theta; camSph.phi = CAM_HOME.phi; camSph.radius = CAM_HOME.radius;
    updateCamera();
  });

  // ---------- メインループ ----------
  var GRAVITY = 55;           // 落下加速度（見た目調整用）
  var lastT = performance.now();

  function animate(now) {
    requestAnimationFrame(animate);
    var dt = Math.min((now - lastT) / 1000, 0.05);
    lastT = now;

    if (falling) {
      var f = falling;
      f.v += GRAVITY * dt;
      f.mesh.position.y -= f.v * dt;
      if (f.mesh.position.y <= f.targetY) {
        if (!f.bounced && f.v > 3.5) {
          f.mesh.position.y = f.targetY;
          f.v = -f.v * 0.18;      // 小さくはねる
          f.bounced = true;
        } else {
          f.mesh.position.y = f.targetY;
          onLanded();
        }
      }
    }

    // 勝利演出の点滅
    if (winMarkers.length) {
      var pulse = 0.35 + 0.3 * Math.sin(now * 0.006);
      for (var i = 0; i < winMarkers.length; i++) {
        var w = winMarkers[i];
        if (w.type === 'beam') w.mesh.material.opacity = 0.5 + 0.4 * Math.sin(now * 0.006);
      }
      whiteWinMat.emissive.setRGB(0.1, pulse, 0.15);
      blackWinMat.emissive.setRGB(0.1, pulse, 0.15);
    }

    updateTimerDisplay(now);
    renderer.render(scene, camera);
  }

  // ---------- 起動 ----------
  resize();
  updateCamera();
  updateStatus();
  startTurnTimer();
  requestAnimationFrame(animate);

  // デバッグ・検証用に公開
  window.game = {
    board: board,
    tryMove: tryMove,
    undoMove: undoMove,
    newGame: newGame,
    lines: LINES,
    isBusy: function () { return !!falling; },
    isThinking: function () { return cpuThinking; },
    cpuChooseMove: cpuChooseMove,
    state: function () { return { gameState: gameState, winner: winnerInfo, history: board.history.slice() }; }
  };
})();
