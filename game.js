// game.js — Don't Blink with MediaPipe FaceMesh blink detection
// Make sure index.html includes the MediaPipe face_mesh & camera_utils scripts before this file.

const video = document.getElementById("camera");
const statusEl = document.getElementById("status");
const timerEl = document.getElementById("timer");
const startBtn = document.getElementById("startBtn");
const restartBtn = document.getElementById("restartBtn");
const debugEl = document.getElementById("debug");

let cameraStream = null;
let cameraController = null;
let faceMesh = null;

let playing = false;
let startTime = 0;
let rafId = null;

// blink detection parameters (tweakable)
const BASE_EAR_THRESHOLD = 0.20; // starting threshold
let dynamicEarThreshold = BASE_EAR_THRESHOLD;
const MAX_EAR_THRESHOLD = 0.30; // cap sensitivity

// make a single closed frame count as a blink (strict)
const CLOSED_CONSEC_FRAMES = 1; // default frame count threshold
let dynamicClosedConsec = CLOSED_CONSEC_FRAMES;
let leftClosedFrames = 0;
let rightClosedFrames = 0;

let difficulty = 0; // increases over time
const DIFFICULTY_INTERVAL = 10; // seconds per difficulty step
const DIFFICULTY_EAR_STEP = 0.02; // how much threshold increases per step
const DIFFICULTY_FRAME_REDUCTION_STEP = 1; // how many frames to reduce per step (makes detection faster)

let partialBlinkCount = 0;
const PARTIAL_BLINK_ALLOWED = 1; // number of partial blinks allowed before losing
let lastPartialTime = 0;
const PARTIAL_WINDOW_MS = 2000; // time window to count partials

// AI-taunt / contextual taunts
let lastTauntTime = 0;
const TAUNT_COOLDOWN_MS = 2500;
function generateTaunt(severity){
  const mild = ["Careful...", "You're dipping...", "A bit sleepy?"];
  const mean = ["Eyes open!", "I saw that twitch.", "Not on my watch."];
  const savage = ["Blink and you're out.", "Nice try, but I noticed.", "Too slow!"];
  const pool = severity > 1 ? (severity > 2 ? savage : mean) : mild;
  return pool[Math.floor(Math.random()*pool.length)];
}
function maybeTaunt(severity){
  const now = performance.now();
  if (now - lastTauntTime < TAUNT_COOLDOWN_MS) return;
  lastTauntTime = now;
  const t = generateTaunt(severity);
  const prev = statusEl ? statusEl.textContent : "";
  if (statusEl) statusEl.textContent = t;
  setTimeout(()=> { if (playing && statusEl) statusEl.textContent = prev; }, 1600);
}

// Avatar mimic elements (cache)
const avatarLeftEye = document.querySelector("#avatarOverlay .small-eye.left");
const avatarRightEye = document.querySelector("#avatarOverlay .small-eye.right");
const avatarMouth = document.querySelector("#avatarOverlay .small-mouth");

// compute mouth openness (simple vertical distance normalized by face width)
// using approximate MediaPipe indices for mouth (upper/lower lip)
const MOUTH_TOP_IDX = 13;
const MOUTH_BOTTOM_IDX = 14;
function computeMouthOpenness(landmarks){
  if (!landmarks || !landmarks[MOUTH_TOP_IDX] || !landmarks[MOUTH_BOTTOM_IDX]) return 0;
  const top = landmarks[MOUTH_TOP_IDX];
  const bottom = landmarks[MOUTH_BOTTOM_IDX];
  const leftFace = landmarks[234] || landmarks[33];
  const rightFace = landmarks[454] || landmarks[263];
  const faceWidth = dist(leftFace, rightFace) || 1;
  return dist(top, bottom) / faceWidth; // ~0..0.5 typical
}

// --- Lighting / face-missing helpers (fixed & added) ---
let lowLightMode = false;
let faceMissingSince = 0;
const LOW_LIGHT_THRESHOLD = 0.12;      // normalized 0..1 (tweak as needed)
const FACE_MISSING_GRACE_MS = 700;     // allow ~0.7s brief loss before fail

// offscreen canvas for quick brightness sampling (small, fast)
const _brightnessCanvas = document.createElement('canvas');
const _brightnessCtx = _brightnessCanvas.getContext('2d');
function sampleVideoBrightness() {
  try {
    const W = 64, H = 48; // small for speed
    _brightnessCanvas.width = W;
    _brightnessCanvas.height = H;
    if (!video || !(video.readyState >= HTMLMediaElement.HAVE_CURRENT_DATA)) return 1.0;
    _brightnessCtx.drawImage(video, 0, 0, W, H);
    const data = _brightnessCtx.getImageData(0, 0, W, H).data;
    let sum = 0, count = 0;
    for (let i = 0; i < data.length; i += 4) {
      const r = data[i], g = data[i+1], b = data[i+2];
      // Rec.709 luminance
      sum += 0.2126 * r + 0.7152 * g + 0.0722 * b;
      count++;
    }
    return (count ? (sum / count) / 255 : 1.0);
  } catch (e) {
    return 1.0;
  }
}

// utility: distance between two points
function dist(a, b) {
  const dx = a.x - b.x;
  const dy = a.y - b.y;
  return Math.sqrt(dx*dx + dy*dy);
}

// compute Eye Aspect Ratio (EAR) for a set of 6 landmarks (MediaPipe indices)
function computeEAR(landmarks, idxs) {
  const p1 = landmarks[idxs[0]];
  const p2 = landmarks[idxs[1]];
  const p3 = landmarks[idxs[2]];
  const p4 = landmarks[idxs[3]];
  const p5 = landmarks[idxs[4]];
  const p6 = landmarks[idxs[5]];
  const v1 = dist(p2, p6);
  const v2 = dist(p3, p5);
  const h = dist(p1, p4);
  if (!h || h === 0) return 1.0;
  const ear = (v1 + v2) / (2.0 * h);
  return ear;
}

// MediaPipe FaceMesh eye landmark sets (commonly used indices)
const LEFT_EYE_IDXS  = [33, 160, 158, 133, 153, 144];
const RIGHT_EYE_IDXS = [263, 387, 385, 362, 380, 373];

// --- CameraShim (in case Camera util isn't present) ---
if (typeof Camera === "undefined") {
  class CameraShim {
    constructor(videoEl, { onFrame, width = 640, height = 480, fps = 60 } = {}) {
      this.video = videoEl;
      this.onFrame = onFrame;
      this.width = width;
      this.height = height;
      this.fpsCap = Math.max(5, fps);
      this._running = false;
      this._boundLoop = this._loop.bind(this);
      this._lastFrameTime = 0;
    }
    async _loop() {
      if (!this._running) return;
      try {
        const now = performance.now();
        const minInterval = 1000 / this.fpsCap;
        if (this.video && this.video.readyState >= HTMLMediaElement.HAVE_ENOUGH_DATA &&
            (now - this._lastFrameTime) >= minInterval) {
          this._lastFrameTime = now;
          await this.onFrame();
        }
      } catch (e) {
        console.warn("CameraShim onFrame error:", e);
      }
      requestAnimationFrame(this._boundLoop);
    }
    start() {
      if (this._running) return;
      this._running = true;
      this._lastFrameTime = 0;
      requestAnimationFrame(this._boundLoop);
    }
    stop() {
      this._running = false;
    }
  }
  window.Camera = CameraShim;
}

// New: improved blink detection helpers/history
const EAR_HISTORY_MS = 700;        // how far back to keep EAR samples
const SLOW_DROP_DELTA = 0.06;     // sustained drop considered a slow blink
const SLOW_WINDOW_MS = 500;       // window to evaluate sustained drop
const NEAR_THRESHOLD_MARGIN = 0.02; // treat slightly-above-threshold as "near closed" for frame counters
let earHistory = []; // {t, left, right}

// New: detect very quick blinks by looking for fast EAR drops between frames
const BLINK_DROP_DELTA_BASE = 0.08; // sudden drop in EAR considered a blink (base)
const DROP_MARGIN_BASE = 0.06;      // allow detection slightly above threshold if big drop occurs
let BLINK_DROP_DELTA_VAR = BLINK_DROP_DELTA_BASE;
let DROP_MARGIN_VAR = DROP_MARGIN_BASE;

// keep prevLeftEAR/prevRightEAR as before but prime them safely (null = not primed)
let prevLeftEAR = null;
let prevRightEAR = null;
let prevEarTimestamp = 0;

// --- dynamic detection update (low-light adjustments included) ---
function updateDynamicDetection(elapsedSec){
  const newDifficulty = Math.floor(elapsedSec / DIFFICULTY_INTERVAL);
  if (newDifficulty !== difficulty){
    difficulty = newDifficulty;
    dynamicEarThreshold = Math.min(MAX_EAR_THRESHOLD, BASE_EAR_THRESHOLD + difficulty * DIFFICULTY_EAR_STEP);
    dynamicClosedConsec = Math.max(1, CLOSED_CONSEC_FRAMES - Math.floor(difficulty * DIFFICULTY_FRAME_REDUCTION_STEP));
    const diffEl = document.getElementById("difficulty");
    if (diffEl) diffEl.textContent = `Difficulty: ${difficulty}`;
  }
  // Apply low-light adjustments (make detection slightly more conservative when lighting is poor)
  if (lowLightMode) {
    dynamicClosedConsec = Math.max(dynamicClosedConsec, CLOSED_CONSEC_FRAMES + 1);
    BLINK_DROP_DELTA_VAR = Math.max(0.12, BLINK_DROP_DELTA_BASE + 0.04);
    DROP_MARGIN_VAR = Math.min(0.14, DROP_MARGIN_BASE + 0.03);
  } else {
    BLINK_DROP_DELTA_VAR = BLINK_DROP_DELTA_BASE;
    DROP_MARGIN_VAR = DROP_MARGIN_BASE;
  }
}

// --- Face zone detection parameters (strict) ---
const ZONE_CENTER_X = 0.5; // normalized center of allowed region
const ZONE_CENTER_Y = 0.48;
const ZONE_MAX_DEVIATION = 0.22; // maximum normalized distance from center
const MIN_FACE_WIDTH = 0.16; // minimum normalized face width to be considered "in zone"

// compute face bounding box center and width (normalized coords)
function computeFaceBoxMetrics(landmarks) {
  if (!landmarks || landmarks.length === 0) return null;
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (let i = 0; i < landmarks.length; i++) {
    const p = landmarks[i];
    if (p.x < minX) minX = p.x;
    if (p.y < minY) minY = p.y;
    if (p.x > maxX) maxX = p.x;
    if (p.y > maxY) maxY = p.y;
  }
  const cx = (minX + maxX) / 2;
  const cy = (minY + maxY) / 2;
  const width = maxX - minX;
  return { cx, cy, width };
}

function isFaceInZone(landmarks) {
  const m = computeFaceBoxMetrics(landmarks);
  if (!m) return false;
  const dx = m.cx - ZONE_CENTER_X;
  const dy = m.cy - ZONE_CENTER_Y;
  const distFromCenter = Math.sqrt(dx*dx + dy*dy);
  if (distFromCenter > ZONE_MAX_DEVIATION) return false;
  if (m.width < MIN_FACE_WIDTH) return false;
  return true;
}

// --- Add/modify FaceMesh & Camera setup ---
async function setupFaceMesh() {
  if (!faceMesh) {
    faceMesh = new FaceMesh({
      locateFile: (file) => `https://cdn.jsdelivr.net/npm/@mediapipe/face_mesh@0.4/${file}`
    });

    faceMesh.setOptions({
      maxNumFaces: 1,
      refineLandmarks: true,
      minDetectionConfidence: 0.6,
      minTrackingConfidence: 0.6
    });

    faceMesh.onResults(onFaceResults);
  }

  if (cameraController) {
    try {
      if (!cameraController._running) cameraController.start();
      return;
    } catch (e) {
      try { cameraController.stop(); } catch (_) {}
      cameraController = null;
    }
  }

  cameraController = new Camera(video, {
    onFrame: async () => {
      await faceMesh.send({image: video});
    },
    width: 640,
    height: 480,
    fps: 60
  });
}

// --- Full, robust onFaceResults (integrated fixes) ---
function onFaceResults(results) {
  try {
    if (!playing) return;

    // brightness check (every results callback)
    const avgLuma = sampleVideoBrightness();
    if (avgLuma < LOW_LIGHT_THRESHOLD) {
      lowLightMode = true;
      if (statusEl) statusEl.classList.add("low-light");
      if (statusEl) statusEl.textContent = "Low light — detection adapting";
    } else {
      if (lowLightMode && statusEl) statusEl.textContent = "Lighting OK";
      lowLightMode = false;
      if (statusEl) statusEl.classList.remove("low-light");
    }

    // face missing grace
    if (!results.multiFaceLandmarks || results.multiFaceLandmarks.length === 0) {
      const now = performance.now();
      if (!faceMissingSince) faceMissingSince = now;
      if (now - faceMissingSince < FACE_MISSING_GRACE_MS) {
        if (debugEl) debugEl.textContent = "Face briefly lost…";
        return; // don't immediately lose
      } else {
        if (debugEl) debugEl.textContent = "Face not found";
        // treat as cheating (do not auto-submit)
        lose("Left camera zone — cheating detected", { submit: false });
        faceMissingSince = 0;
        return;
      }
    } else {
      faceMissingSince = 0;
    }

    const lm = results.multiFaceLandmarks[0];

    if (!isFaceInZone(lm)) {
      // immediate stop and mark as cheating (no auto-submit)
      lose("Left camera zone — cheating detected", { submit: false });
      return;
    }

    // compute EAR for both eyes (use dynamic threshold)
    const leftEAR  = computeEAR(lm, LEFT_EYE_IDXS);
    const rightEAR = computeEAR(lm, RIGHT_EYE_IDXS);
    const nowMs = performance.now();

    // debug display
    if (debugEl) debugEl.textContent = `l:${leftEAR.toFixed(3)} r:${rightEAR.toFixed(3)} thr:${dynamicEarThreshold.toFixed(3)}`;

    // maintain EAR history (prune old samples)
    earHistory.push({ t: nowMs, left: leftEAR, right: rightEAR });
    while (earHistory.length && nowMs - earHistory[0].t > EAR_HISTORY_MS) earHistory.shift();

    // === Avatar mimic ===
    try {
      const MIN_EAR_VIS = 0.02;
      const MAX_EAR_VIS = 0.30;
      const mapEarToScale = (ear) => {
        const norm = (ear - MIN_EAR_VIS) / (MAX_EAR_VIS - MIN_EAR_VIS);
        const clamped = Math.max(0.02, Math.min(1.0, norm));
        if (ear <= dynamicEarThreshold) return 0.02;
        return clamped;
      };

      const eyeScaleLeft = mapEarToScale(leftEAR);
      const eyeScaleRight = mapEarToScale(rightEAR);

      if (avatarLeftEye) {
        avatarLeftEye.style.transformOrigin = "center center";
        avatarLeftEye.style.transform = `scaleY(${eyeScaleLeft})`;
        avatarLeftEye.style.borderRadius = eyeScaleLeft < 0.06 ? "50%" : "50%";
        avatarLeftEye.style.background = eyeScaleLeft < 0.06 ? "rgba(0,0,0,0.85)" : "rgba(0,0,0,0.6)";
      }
      if (avatarRightEye) {
        avatarRightEye.style.transformOrigin = "center center";
        avatarRightEye.style.transform = `scaleY(${eyeScaleRight})`;
        avatarRightEye.style.borderRadius = eyeScaleRight < 0.06 ? "50%" : "50%";
        avatarRightEye.style.background = eyeScaleRight < 0.06 ? "rgba(0,0,0,0.85)" : "rgba(0,0,0,0.6)";
      }

      const mouthOpen = computeMouthOpenness(lm);
      if (avatarMouth) {
        const mouthH = Math.max(0.06, Math.min(0.28, mouthOpen*1.6));
        avatarMouth.style.height = (mouthH*100) + "%";
        avatarMouth.style.borderRadius = mouthOpen > 0.06 ? "6vmin 6vmin 18vmin 18vmin" : "0 0 18vmin 18vmin";
      }
    } catch(e){ /* ignore avatar errors */ }

    // update difficulty using elapsed time
    const elapsed = (nowMs - startTime) / 1000;
    updateDynamicDetection(elapsed);

    // --- Blink detection: combined checks ---

    // prime prev EARs on first reliable frame (avoid massive first-frame drops)
    if (prevLeftEAR === null || prevRightEAR === null || prevEarTimestamp === 0) {
      prevLeftEAR = leftEAR;
      prevRightEAR = rightEAR;
      prevEarTimestamp = nowMs;
      return; // skip drop-based checks for this first priming frame
    }

    // 1) Instant threshold: immediate closure
    const instantLeftClosed = (leftEAR <= dynamicEarThreshold);
    const instantRightClosed = (rightEAR <= dynamicEarThreshold);

    // 2) Fast drop detection (sudden drop between frames)
    const leftDrop = prevLeftEAR - leftEAR;
    const rightDrop = prevRightEAR - rightEAR;
    const leftFastBlink = (leftDrop > BLINK_DROP_DELTA_VAR) && (leftEAR <= dynamicEarThreshold + DROP_MARGIN_VAR);
    const rightFastBlink = (rightDrop > BLINK_DROP_DELTA_VAR) && (rightEAR <= dynamicEarThreshold + DROP_MARGIN_VAR);

    // 3) Consecutive-frame detection (treat near-threshold as closed to catch gradual closure)
    if (leftEAR <= dynamicEarThreshold || leftEAR <= dynamicEarThreshold + NEAR_THRESHOLD_MARGIN) {
      leftClosedFrames++;
    } else {
      leftClosedFrames = 0;
    }
    if (rightEAR <= dynamicEarThreshold || rightEAR <= dynamicEarThreshold + NEAR_THRESHOLD_MARGIN) {
      rightClosedFrames++;
    } else {
      rightClosedFrames = 0;
    }
    const leftConsecBlink = leftClosedFrames >= dynamicClosedConsec;
    const rightConsecBlink = rightClosedFrames >= dynamicClosedConsec;

    // 4) Sustained/smooth drop (slow blink): compare recent max/avg to current within SLOW_WINDOW_MS
    let slowLeftBlink = false;
    let slowRightBlink = false;
    const windowStart = nowMs - SLOW_WINDOW_MS;
    const windowSamples = earHistory.filter(s => s.t >= windowStart);
    if (windowSamples.length >= 2) {
      const maxLeft = Math.max(...windowSamples.map(s => s.left));
      const maxRight = Math.max(...windowSamples.map(s => s.right));
      const avgLeft = windowSamples.reduce((acc,v)=>acc+v.left,0)/windowSamples.length;
      const avgRight = windowSamples.reduce((acc,v)=>acc+v.right,0)/windowSamples.length;

      if ((maxLeft - leftEAR > SLOW_DROP_DELTA || avgLeft - leftEAR > (SLOW_DROP_DELTA*0.7)) &&
          leftEAR <= dynamicEarThreshold + DROP_MARGIN_VAR) slowLeftBlink = true;
      if ((maxRight - rightEAR > SLOW_DROP_DELTA || avgRight - rightEAR > (SLOW_DROP_DELTA*0.7)) &&
          rightEAR <= dynamicEarThreshold + DROP_MARGIN_VAR) slowRightBlink = true;
    }

    // Final decision: if any detection flags true -> lose
    if (instantLeftClosed || instantRightClosed ||
        leftFastBlink || rightFastBlink ||
        leftConsecBlink || rightConsecBlink ||
        slowLeftBlink || slowRightBlink) {
      lose("You blinked 😏");
      // update previous values before exiting
      prevLeftEAR = leftEAR;
      prevRightEAR = rightEAR;
      prevEarTimestamp = nowMs;
      return;
    }

    // normal: reset consecutive counters for next frame (they already update above on next frames)
    // update previous EARs and timestamp for next-frame drop checks
    prevLeftEAR = leftEAR;
    prevRightEAR = rightEAR;
    prevEarTimestamp = nowMs;

  } catch (err) {
    console.error("onFaceResults error:", err);
    if (debugEl) debugEl.textContent = "Detection error: " + (err && err.message ? err.message : String(err));
    // Do not call lose() here; allow the game to keep the camera live
  }
}

// start camera permission & face detection
async function startCameraAndFaceMesh() {
  const enableCameraBtnLocal = document.getElementById("enableCameraBtn");
  try {
    try {
      await tryInitCamera();
      if (statusEl) statusEl.textContent = "Camera ready. Press START";
      if (enableCameraBtnLocal) { enableCameraBtnLocal.classList.add("hidden"); }
    } catch (playErr) {
      console.warn("Autoplay or init blocked, awaiting user gesture:", playErr);
      if (statusEl) statusEl.textContent = "Tap 'Enable Camera' to start";
      if (debugEl) debugEl.textContent = String(playErr);
      if (enableCameraBtnLocal) {
        enableCameraBtnLocal.disabled = false;
        enableCameraBtnLocal.classList.remove("hidden");
      }
      throw playErr;
    }
  } catch (err) {
    console.error("camera error", err);
    if (statusEl) statusEl.textContent = "Camera access required (HTTPS or localhost).";
    if (debugEl) debugEl.textContent = String(err);
    throw err;
  }
}

// request media if we don't already have it
async function tryInitCamera() {
  if (!navigator.mediaDevices || typeof navigator.mediaDevices.getUserMedia !== "function") {
    const msg = "getUserMedia not supported by this browser.";
    console.error(msg);
    if (statusEl) statusEl.textContent = msg;
    throw new Error(msg);
  }

  if (!cameraStream) {
    cameraStream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: "user", width: 640, height: 480 }, audio: false });
    video.srcObject = cameraStream;
  }
  await video.play();

  await setupFaceMesh();
  if (cameraController && !cameraController._running) {
    cameraController.start();
  }
}

// start game
function startGame() {
  if (!cameraStream || !cameraController || !(video.readyState >= HTMLMediaElement.HAVE_ENOUGH_DATA)) {
    if (statusEl) statusEl.textContent = "Camera not ready. Tap 'Enable Camera' if needed.";
    return;
  }
  playing = true;
  startTime = performance.now();
  leftClosedFrames = rightClosedFrames = 0;
  prevLeftEAR = null; prevRightEAR = null; prevEarTimestamp = 0; // re-prime on next frames
  if (statusEl) statusEl.textContent = "Don't blink!";
  if (startBtn) startBtn.disabled = true;
  if (restartBtn) restartBtn.disabled = false;
  rafId = requestAnimationFrame(loop);
}

// main loop updates timer and random taunts
function loop(ts) {
  if (!playing) return;
  const elapsed = (ts - startTime) / 1000;
  if (timerEl) timerEl.textContent = elapsed.toFixed(1) + "s";

  // random taunt occasionally
  if (Math.random() < 0.006) {
    randomTaunt();
  }

  rafId = requestAnimationFrame(loop);
}

function randomTaunt(){
  const lines = ["Still staring?", "Don’t blink now.", "You look tense.", "Focus..."];
  if (statusEl) statusEl.textContent = lines[Math.floor(Math.random()*lines.length)];
}

// --- Leaderboard (localStorage) helpers ---
const playerNameInput = document.getElementById("playerName");
const leaderboardList = document.getElementById("leaderboardList");
const lbResetBtn = document.getElementById("lbResetBtn");
const lbExportBtn = document.getElementById("lbExportBtn");
const lbSubmitBtn = document.getElementById("lbSubmitBtn");

const LB_KEY = "db_leaderboard_v1";
function loadLeaderboard() {
  try {
    const raw = localStorage.getItem(LB_KEY);
    return raw ? JSON.parse(raw) : [];
  } catch (_) { return []; }
}
function saveLeaderboard(arr) {
  localStorage.setItem(LB_KEY, JSON.stringify(arr.slice(0,100)));
}
function submitLeaderboardEntry(name, score) {
  if (!name) name = "Anonymous";
  const arr = loadLeaderboard();
  arr.unshift({ name, score: Number(score), date: new Date().toISOString() });
  saveLeaderboard(arr.slice(0,100));
  renderLeaderboard();
}
function resetLeaderboard() {
  localStorage.removeItem(LB_KEY);
  renderLeaderboard();
}
function exportLeaderboardToClipboard() {
  const arr = loadLeaderboard();
  navigator.clipboard.writeText(JSON.stringify(arr, null, 2)).then(()=> {
    alert("Leaderboard JSON copied to clipboard.");
  }, ()=> {
    alert("Could not copy leaderboard.");
  });
}
function renderLeaderboard() {
  const listEl = document.getElementById("leaderboardList");
  if (!listEl) return;
  const arr = loadLeaderboard();
  listEl.innerHTML = "";
  if (arr.length === 0) {
    listEl.innerHTML = "<div class='lb-empty'>No scores yet</div>";
    return;
  }
  arr.forEach((e, idx) => {
    const el = document.createElement("div");
    el.className = "lb-entry";
    const dt = new Date(e.date);
    el.textContent = `${idx+1}. ${e.name} — ${e.score.toFixed(1)}s (${dt.toLocaleString()})`;
    listEl.appendChild(el);
  });
}

let lastRunScore = 0; // new: store last run time for sharing

// lose() — improved to be idempotent & robust
// modified signature to accept options { submit: boolean } (default true)
function lose(reason, opts = {}) {
  const { submit = true } = opts;
  if (!playing) {
    if (!reason) return;
  }
  playing = false;
  if (statusEl) statusEl.textContent = reason;
  document.body.style.background = "#2c0202";
  if (rafId) cancelAnimationFrame(rafId);

  // compute elapsed and update high score
  const elapsedSec = (performance.now() - startTime) / 1000;
  lastRunScore = elapsedSec; // store for sharing
  const prevHigh = parseFloat(localStorage.getItem("db_highscore") || "0");
  if (elapsedSec > prevHigh) {
    localStorage.setItem("db_highscore", elapsedSec.toString());
    const hsEl = document.getElementById("highscore");
    if (hsEl) hsEl.textContent = `High: ${elapsedSec.toFixed(1)}s`;
  }

  // auto-submit to leaderboard using name field if present and submit not disabled
  if (submit) {
    const name = playerNameInput ? (playerNameInput.value || "Anonymous") : "Anonymous";
    submitLeaderboardEntry(name, elapsedSec);
  }

  // enable share and leaderboard controls
  const shareBtn = document.getElementById("shareBtn");
  if (shareBtn) shareBtn.disabled = false;
  if (lbSubmitBtn) lbSubmitBtn.disabled = false;
  if (lbResetBtn) lbResetBtn.disabled = false;
  if (lbExportBtn) lbExportBtn.disabled = false;

  // disable start, enable restart
  if (startBtn) startBtn.disabled = true;
  if (restartBtn) restartBtn.disabled = false;
}

// --- Wire leaderboard buttons and render on init ---
async function init() {
  // register quick-lose handlers (if you had them)
  // populate high score UI
  const prevHigh = parseFloat(localStorage.getItem("db_highscore") || "0");
  const hsEl = document.getElementById("highscore");
  if (hsEl) hsEl.textContent = prevHigh > 0 ? `High: ${prevHigh.toFixed(1)}s` : "High: —";

  // wire share btn if exists
  const sb = document.getElementById("shareBtn");
  if (sb) sb.addEventListener("click", shareScore);

  if (lbResetBtn) {
    lbResetBtn.disabled = false;
    lbResetBtn.addEventListener("click", ()=>{ if(confirm("Reset leaderboard?")) resetLeaderboard(); });
  }
  if (lbExportBtn) {
    lbExportBtn.disabled = false;
    lbExportBtn.addEventListener("click", ()=> {
      exportLeaderboardToClipboard();
    });
  }

  const storedName = localStorage.getItem("db_player_name");
  if (lbSubmitBtn) lbSubmitBtn.disabled = !(storedName && storedName.length > 0);

  renderLeaderboard();

  try {
    const inIframe = (window.self !== window.top);
    const secure = (location.protocol === 'https:' || location.hostname === 'localhost' || location.hostname === '127.0.0.1');

    if (inIframe) {
      if (statusEl) statusEl.textContent = "Open in a new tab to enable camera (blocked in embed).";
      const enableCameraBtn = document.getElementById("enableCameraBtn");
      if (enableCameraBtn) { enableCameraBtn.disabled = false; enableCameraBtn.classList.remove("hidden"); }
    } else if (!secure) {
      if (statusEl) statusEl.textContent = "Camera requires HTTPS or localhost. Serve over HTTPS to enable camera.";
      const enableCameraBtn = document.getElementById("enableCameraBtn");
      if (enableCameraBtn) { enableCameraBtn.disabled = false; enableCameraBtn.classList.remove("hidden"); }
    } else {
      try {
        await startCameraAndFaceMesh();
        if (statusEl) statusEl.textContent = "Camera ready. Press START";
      } catch(e){
        console.warn("Camera/FaceMesh init failed:", e);
        const enableCameraBtn = document.getElementById("enableCameraBtn");
        if (enableCameraBtn) { enableCameraBtn.disabled = false; enableCameraBtn.classList.remove("hidden"); }
      }
    }
  } catch (e) {
    console.warn("init check failed:", e);
    if (statusEl) statusEl.textContent = "Ready. Use 'Enable Camera' to start.";
  }
}

// wire buttons (guarded)
if (startBtn) startBtn.addEventListener("click", startGame);
if (restartBtn) restartBtn.addEventListener("click", () => { restart(); });

// Persist player name behavior
if (typeof playerNameInput !== "undefined" && playerNameInput) {
  const savedName = localStorage.getItem("db_player_name");
  if (savedName) playerNameInput.value = savedName;
  playerNameInput.addEventListener("input", (e) => {
    try { localStorage.setItem("db_player_name", e.target.value); } catch (e) { /* ignore storage errors */ }
    if (lbSubmitBtn) lbSubmitBtn.disabled = !e.target.value;
  });
  if (lbSubmitBtn) lbSubmitBtn.disabled = !playerNameInput.value;
}

// wire new enable camera button (exists in HTML)
const enableCameraBtn = document.getElementById("enableCameraBtn");
if (enableCameraBtn) {
  enableCameraBtn.addEventListener('click', async () => {
    enableCameraBtn.disabled = true;
    enableCameraBtn.classList.add("hidden");
    if (statusEl) statusEl.textContent = "Enabling camera…";
    try {
      await tryInitCamera(); // attempt to (re)initialize media & face mesh
      if (statusEl) statusEl.textContent = "Camera ready. Press START";
    } catch (e) {
      console.warn("Enable camera failed:", e);
      if (statusEl) statusEl.textContent = "Camera enable failed. Check permissions.";
      enableCameraBtn.disabled = false;
      enableCameraBtn.classList.remove("hidden");
    }
  });
}

init();

// restart game (reset UI/state but keep camera running)
function restart() {
  playing = false;
  if (rafId) {
    cancelAnimationFrame(rafId);
    rafId = null;
  }

  if (statusEl) statusEl.textContent = "Ready";
  if (timerEl) timerEl.textContent = "0.0s";
  document.body.style.background = "";
  if (startBtn) startBtn.disabled = false;
  if (restartBtn) restartBtn.disabled = true;

  try {
    if (avatarLeftEye) {
      avatarLeftEye.style.transform = "scaleY(1)";
      avatarLeftEye.style.background = "rgba(0,0,0,0.6)";
    }
    if (avatarRightEye) {
      avatarRightEye.style.transform = "scaleY(1)";
      avatarRightEye.style.background = "rgba(0,0,0,0.6)";
    }
    if (avatarMouth) {
      avatarMouth.style.height = (Math.max(0.06, 0.06)*100) + "%";
    }
  } catch (e) { /* ignore */ }

  try {
    if (cameraController && !cameraController._running) cameraController.start();
  } catch (e) { console.warn("Could not restart cameraController:", e); }
}

// shareScore — implemented (Web Share API + clipboard fallback)
function shareScore() {
  const score = (typeof lastRunScore === "number" && lastRunScore > 0) ? lastRunScore.toFixed(1) + "s" : "—";
  const text = `Don't Blink — Score: ${score}\nI just played DON'T BLINK (v1.5 (2)). Can you beat me?\n${location.href}`;
  // Prefer native share
  if (navigator.share) {
    navigator.share({ title: "DON'T BLINK — my score", text }).catch(()=> {
      // ignore share cancellation
    });
    return;
  }
  // Clipboard fallback
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text).then(()=> {
      alert("Score copied to clipboard. Share it anywhere!");
    }, ()=> {
      prompt("Copy your score:", text);
    });
    return;
  }
  // Last resort: prompt
  prompt("Share your score (copy):", text);
}
