(function () {
  "use strict";

  const N_CTRL = 20;
  const MAX_INFLUENCE_DEGREE = Math.floor(N_CTRL / 2);
  const SPD_CUSTOM_MAX = 150;
  const REFL_CUSTOM_MAX = 100;
  const CMF_PATH = "CIE_xyz_1931_2deg.csv";
  const MANIFEST_PATH = "manifest.json";

  const PAD_L = 44;
  const PAD_R = 14;
  const PAD_T = 22;
  const PAD_B = 40;

  /** Visible / integration band (nm). Data and control points are restricted to this range. */
  const PLOT_WL_MIN = 380;
  const PLOT_WL_MAX = 700;

  /** Spectral strip maps this wavelength interval (matches plot band). */
  const STRIP_WL_MIN = 380;
  const STRIP_WL_MAX = 700;

  /** @type {{ wl: number[], x: number[], y: number[], z: number[] }} */
  let cmfGrid = { wl: [], x: [], y: [], z: [] };
  let wlMin = PLOT_WL_MIN;
  let wlMax = PLOT_WL_MAX;

  /** @type {number[]} */
  let spd = [];
  /** @type {number[]} */
  let refl = [];

  let customSpd = false;
  let customRefl = false;

  /** Control points: wavelength (nm), value */
  /** @type {{ wl: number[], v: number[] }} */
  let ctrlSpd = { wl: [], v: [] };
  /** @type {{ wl: number[], v: number[] }} */
  let ctrlRefl = { wl: [], v: [] };

  const canvasSpd = document.getElementById("canvasSpd");
  const canvasSpectral = document.getElementById("canvasSpectral");
  const canvasRefl = document.getElementById("canvasRefl");
  const canvasCmf = document.getElementById("canvasCmf");
  const ctxSpd = canvasSpd.getContext("2d");
  const ctxSpectral = canvasSpectral ? canvasSpectral.getContext("2d") : null;
  const ctxRefl = canvasRefl.getContext("2d");
  const ctxCmf = canvasCmf.getContext("2d");

  const intensitySlider = document.getElementById("intensitySlider");
  const intensityValue = document.getElementById("intensityValue");

  const tbodySpd = document.getElementById("tbodySpd");
  const tbodyRefl = document.getElementById("tbodyRefl");
  const tbodyCmf = document.getElementById("tbodyCmf");
  const tableScrollSpd = document.getElementById("tableScrollSpd");
  const tableScrollRefl = document.getElementById("tableScrollRefl");
  const tableScrollCmf = document.getElementById("tableScrollCmf");

  const colorSwatch = document.getElementById("colorSwatch");
  const colorSummary = document.getElementById("colorSummary");
  const tbodyCalc = document.getElementById("tbodyCalc");
  const tableScrollCalc = document.getElementById("tableScrollCalc");
  const errorBanner = document.getElementById("errorBanner");

  let dragTarget = null;

  function showError(msg) {
    errorBanner.textContent = msg;
    errorBanner.classList.add("visible");
  }

  function clearError() {
    errorBanner.textContent = "";
    errorBanner.classList.remove("visible");
  }

  function parseCSVLines(text) {
    const lines = text.split(/\r?\n/).filter((l) => l.trim().length > 0);
    const rows = [];
    for (const line of lines) {
      const parts = line.split(",").map((s) => s.trim());
      rows.push(parts);
    }
    return rows;
  }

  function isNumericHeader(cell) {
    const t = (cell || "").toLowerCase();
    return t === "wl" || t === "lambda" || t === "wavelength" || t === "sci" || t === "sce";
  }

  /**
   * @param {string[][]} rows
   * @returns {{ wl: number[], v: number[] }}
   */
  function parseReflectanceRows(rows) {
    if (rows.length === 0) return { wl: [], v: [] };
    const first = rows[0];
    const hasHeader = first.some(isNumericHeader) && !/^-?\d/.test(first[0]);
    let start = 0;
    let wlCol = 0;
    let valCol = 1;
    let sceCol = -1;
    if (hasHeader) {
      start = 1;
      const h = first.map((c) => c.toLowerCase());
      const sciIdx = h.indexOf("sci");
      if (sciIdx >= 0) valCol = sciIdx;
      else if (h.length >= 2) valCol = 1;
      const ix = h.indexOf("sce");
      if (ix >= 0) sceCol = ix;
    }
    const wl = [];
    const sci = [];
    const sce = [];
    for (let i = start; i < rows.length; i++) {
      const r = rows[i];
      if (r.length < 2) continue;
      const w = parseFloat(r[wlCol]);
      const vs = parseFloat(r[valCol]);
      if (!Number.isFinite(w) || !Number.isFinite(vs)) continue;
      wl.push(w);
      sci.push(vs);
      if (sceCol >= 0 && r.length > sceCol) {
        const ve = parseFloat(r[sceCol]);
        sce.push(Number.isFinite(ve) ? ve : 0);
      } else {
        sce.push(0);
      }
    }
    let maxSci = 0;
    for (let i = 0; i < sci.length; i++) if (Math.abs(sci[i]) > maxSci) maxSci = Math.abs(sci[i]);
    let maxSce = 0;
    for (let i = 0; i < sce.length; i++) if (Math.abs(sce[i]) > maxSce) maxSce = Math.abs(sce[i]);
    let v = sci.slice();
    if (maxSci < 1e-9 && maxSce > 1e-9) {
      v = sce.slice();
    }
    let maxV = 0;
    for (let i = 0; i < v.length; i++) if (v[i] > maxV) maxV = v[i];
    if (maxV > 1.5) {
      for (let i = 0; i < v.length; i++) v[i] /= 100;
    }
    return { wl, v };
  }

  /**
   * Single SPD value from one CSV row (illuminant).
   * @param {number[]} partsNums
   */
  function illuminantValueFromParts(partsNums) {
    if (partsNums.length === 0) return 0;
    if (partsNums.length === 1) return partsNums[0];
    const last = partsNums[partsNums.length - 1];
    const rest = last >= 100 && last <= 20000 ? partsNums.slice(0, -1) : partsNums;
    let s = 0;
    for (let i = 0; i < rest.length; i++) s += rest[i];
    return s;
  }

  /**
   * @param {string[][]} rows
   * @returns {{ wl: number[], v: number[] }}
   */
  function parseIlluminantRows(rows) {
    if (rows.length === 0) return { wl: [], v: [] };
    const wl = [];
    const v = [];
    for (let i = 0; i < rows.length; i++) {
      const r = rows[i];
      if (r.length < 2) continue;
      const w = parseFloat(r[0]);
      const nums = r.slice(1).map(parseFloat).filter((x) => Number.isFinite(x));
      if (!Number.isFinite(w)) continue;
      wl.push(w);
      v.push(illuminantValueFromParts(nums));
    }
    return { wl, v };
  }

  /**
   * @param {number[]} x
   * @param {number[]} y
   * @param {number} xq
   */
  function interpLinear(x, y, xq) {
    if (x.length === 0) return 0;
    if (xq < x[0] || xq > x[x.length - 1]) return 0;
    let lo = 0;
    let hi = x.length - 1;
    while (hi - lo > 1) {
      const mid = (lo + hi) >> 1;
      if (x[mid] <= xq) lo = mid;
      else hi = mid;
    }
    const t = (xq - x[lo]) / (x[hi] - x[lo]);
    return y[lo] * (1 - t) + y[hi] * t;
  }

  /**
   * Resample (wl,v) onto cmfGrid.wl; outside support → 0.
   * @param {number[]} srcWl
   * @param {number[]} srcV
   * @param {number[]} gridWl
   */
  function resampleToGrid(srcWl, srcV, gridWl) {
    const out = new Array(gridWl.length);
    for (let i = 0; i < gridWl.length; i++) {
      out[i] = interpLinear(srcWl, srcV, gridWl[i]);
    }
    return out;
  }

  /**
   * Build 1 nm grid from min to max inclusive.
   */
  function buildUniformGrid(minNm, maxNm) {
    const wl = [];
    for (let w = minNm; w <= maxNm; w++) wl.push(w);
    return wl;
  }

  /**
   * Parse CIE CMF file: wl, xbar, ybar, zbar
   * @param {string} text
   */
  function parseCMF(text) {
    const rows = parseCSVLines(text);
    const wl = [];
    const x = [];
    const y = [];
    const z = [];
    for (let i = 0; i < rows.length; i++) {
      const r = rows[i];
      if (r.length < 4) continue;
      const w = parseFloat(r[0]);
      const xv = parseFloat(r[1]);
      const yv = parseFloat(r[2]);
      const zv = parseFloat(r[3]);
      if (!Number.isFinite(w) || !Number.isFinite(xv)) continue;
      wl.push(w);
      x.push(xv);
      y.push(Number.isFinite(yv) ? yv : 0);
      z.push(Number.isFinite(zv) ? zv : 0);
    }
    if (wl.length < 2) throw new Error("Invalid CMF file");
    const step = wl[1] - wl[0];
    const uniform = Math.abs(step - 1) < 1e-6;
    wlMin = wl[0];
    wlMax = wl[wl.length - 1];
    const gridWl = buildUniformGrid(wlMin, wlMax);
    if (uniform && wl.length === gridWl.length) {
      cmfGrid = { wl: gridWl, x: x.slice(), y: y.slice(), z: z.slice() };
    } else {
      cmfGrid = {
        wl: gridWl,
        x: resampleToGrid(wl, x, gridWl),
        y: resampleToGrid(wl, y, gridWl),
        z: resampleToGrid(wl, z, gridWl),
      };
    }
    cropCmfToPlotBand();
  }

  /** Keep only 1 nm samples with λ ∈ [PLOT_WL_MIN, PLOT_WL_MAX]. */
  function cropCmfToPlotBand() {
    const w = cmfGrid.wl;
    const nx = [];
    const ny = [];
    const nz = [];
    const nw = [];
    for (let i = 0; i < w.length; i++) {
      const lambda = w[i];
      if (lambda >= PLOT_WL_MIN && lambda <= PLOT_WL_MAX) {
        nw.push(lambda);
        nx.push(cmfGrid.x[i]);
        ny.push(cmfGrid.y[i]);
        nz.push(cmfGrid.z[i]);
      }
    }
    if (nw.length < 2) {
      throw new Error("CMF has too few points in the 380–700 nm range");
    }
    cmfGrid = { wl: nw, x: nx, y: ny, z: nz };
    wlMin = PLOT_WL_MIN;
    wlMax = PLOT_WL_MAX;
  }

  function defaultControlWl() {
    const out = [];
    for (let i = 0; i < N_CTRL; i++) {
      const t = N_CTRL === 1 ? 0.5 : i / (N_CTRL - 1);
      out.push(wlMin + t * (wlMax - wlMin));
    }
    return out;
  }

  function interpControlPoints(ctrlWl, ctrlV, gridWl) {
    const v = new Array(gridWl.length);
    for (let i = 0; i < gridWl.length; i++) {
      const w = gridWl[i];
      if (w < ctrlWl[0] || w > ctrlWl[ctrlWl.length - 1]) {
        v[i] = 0;
        continue;
      }
      let k = 0;
      while (k < ctrlWl.length - 1 && !(ctrlWl[k] <= w && w <= ctrlWl[k + 1])) k++;
      const t = (w - ctrlWl[k]) / (ctrlWl[k + 1] - ctrlWl[k]);
      v[i] = ctrlV[k] * (1 - t) + ctrlV[k + 1] * t;
    }
    return v;
  }

  function initDefaultControls() {
    const wls = defaultControlWl();
    ctrlSpd.wl = wls.slice();
    ctrlSpd.v = wls.map(() => SPD_CUSTOM_MAX * 0.5);
    ctrlRefl.wl = wls.slice();
    ctrlRefl.v = wls.map(() => REFL_CUSTOM_MAX * 0.5);
  }

  function recomputeArraysFromControls() {
    const grid = cmfGrid.wl;
    if (customSpd) {
      spd = interpControlPoints(ctrlSpd.wl, ctrlSpd.v, grid);
      for (let i = 0; i < spd.length; i++) {
        spd[i] = Math.min(SPD_CUSTOM_MAX, Math.max(0, spd[i]));
      }
    }
    if (customRefl) {
      const raw = interpControlPoints(ctrlRefl.wl, ctrlRefl.v, grid);
      refl = raw.map((v) => Math.min(1, Math.max(0, v / REFL_CUSTOM_MAX)));
    }
  }

  /**
   * @returns {{ X: number, Y: number, Z: number }}
   */
  function integrateXYZ() {
    const g = cmfGrid.wl.length;
    let X = 0;
    let Y = 0;
    let Z = 0;
    for (let i = 0; i < g; i++) {
      const s = spd[i] * refl[i];
      X += s * cmfGrid.x[i];
      Y += s * cmfGrid.y[i];
      Z += s * cmfGrid.z[i];
    }
    return { X, Y, Z };
  }

  function getInfluenceDegree() {
    const el = document.getElementById("influenceDegree");
    if (!el) return 1;
    const d = parseInt(el.value, 10);
    if (!Number.isFinite(d)) return 1;
    return Math.min(MAX_INFLUENCE_DEGREE, Math.max(1, d));
  }

  /**
   * Weight for index distance from dragged point; degree d ⇒ radius d−1, smooth decay.
   * @param {number} dist - |j - idx|, integer ≥ 0
   * @param {number} degree - ≥ 1
   */
  function influenceWeightAtDist(dist, degree) {
    if (degree <= 1) return dist === 0 ? 1 : 0;
    if (dist > degree - 1) return 0;
    const t = 1 - dist / degree;
    return t * t;
  }

  /**
   * Apply vertical drag: center goes to targetNv; neighbors within radius get delta × weight.
   */
  function applyInfluenceDrag(ctrl, idx, targetNv, vmin, vmax) {
    const oldSnap = ctrl.v.slice();
    const delta = targetNv - oldSnap[idx];
    const deg = getInfluenceDegree();
    const n = ctrl.v.length;
    if (deg <= 1) {
      ctrl.v[idx] = Math.min(vmax, Math.max(vmin, targetNv));
      return;
    }
    const r = deg - 1;
    const j0 = Math.max(0, idx - r);
    const j1 = Math.min(n - 1, idx + r);
    for (let j = j0; j <= j1; j++) {
      const dist = Math.abs(j - idx);
      const w = influenceWeightAtDist(dist, deg);
      ctrl.v[j] = oldSnap[j] + delta * w;
    }
    for (let j = j0; j <= j1; j++) {
      ctrl.v[j] = Math.min(vmax, Math.max(vmin, ctrl.v[j]));
    }
  }

  function populateInfluenceSelect() {
    const sel = document.getElementById("influenceDegree");
    if (!sel) return;
    sel.innerHTML = "";
    for (let d = 1; d <= MAX_INFLUENCE_DEGREE; d++) {
      const opt = document.createElement("option");
      opt.value = String(d);
      opt.textContent = String(d);
      sel.appendChild(opt);
    }
    sel.value = "1";
  }

  function getIntensityScale() {
    if (!intensitySlider) return 0.28;
    const v = parseFloat(intensitySlider.value);
    if (!Number.isFinite(v)) return 0.28;
    return Math.min(1, Math.max(0.02, v));
  }

  /**
   * XYZ (Y normalized to 1) → sRGB display (gamma-encoded 0–1).
   * @param {number} [intensityScale=1] Uniform multiplier on linear RGB before gamma (same as scaling XYZ).
   */
  function xyzToSrgbGamma(X, Y, Z, intensityScale) {
    const s =
      intensityScale === undefined || intensityScale === null
        ? 1
        : Math.min(1, Math.max(0, intensityScale));
    let Rl = 3.2404542 * X + -1.5371385 * Y + -0.4985314 * Z;
    let Gl = -0.969266 * X + 1.8760108 * Y + 0.041556 * Z;
    let Bl = 0.0556434 * X + -0.2040259 * Y + 1.0572252 * Z;
    Rl *= s;
    Gl *= s;
    Bl *= s;

    function compand(c) {
      if (c <= 0) return 0;
      if (c >= 1) return 1;
      if (c <= 0.0031308) return 12.92 * c;
      return 1.055 * Math.pow(c, 1 / 2.4) - 0.055;
    }

    function clip01(x) {
      return Math.min(1, Math.max(0, x));
    }

    return {
      r: clip01(compand(clip01(Rl))),
      g: clip01(compand(clip01(Gl))),
      b: clip01(compand(clip01(Bl))),
    };
  }

  function updateColorDisplay() {
    let { X, Y, Z } = integrateXYZ();
    if (!Number.isFinite(Y) || Y <= 1e-15) {
      colorSwatch.style.background = "#888";
      if (colorSummary) {
        colorSummary.textContent =
          "XYZ integrals are zero or invalid — check SPD and reflectance.";
      }
      return;
    }
    const Xraw = X;
    const Yraw = Y;
    const Zraw = Z;
    X /= Y;
    Z /= Y;
    const Yn = 1;
    const bright = getIntensityScale();
    const rgb = xyzToSrgbGamma(X, Yn, Z, bright);
    const R8 = Math.round(rgb.r * 255);
    const G8 = Math.round(rgb.g * 255);
    const B8 = Math.round(rgb.b * 255);
    colorSwatch.style.background = `rgb(${R8},${G8},${B8})`;
    if (colorSummary) {
      colorSummary.textContent = `Brightness k = ${bright.toFixed(
        2
      )} on linear RGB (same as k×XYZ before the sRGB matrix). Y-normalized chromaticity: X = ${X.toFixed(
        4
      )}, Y = 1, Z = ${Z.toFixed(4)} · sRGB ${R8}, ${G8}, ${B8}`;
    }
    if (intensityValue) intensityValue.textContent = bright.toFixed(2);
    return { Xraw, Yraw, Zraw, Xn: X, Zn: Z, R8, G8, B8 };
  }

  function formatTableCell(v) {
    if (!Number.isFinite(v)) return "—";
    const a = Math.abs(v);
    if (a >= 1000 || (a > 0 && a < 1e-4)) return v.toExponential(4);
    return v.toFixed(6);
  }

  function round2(x) {
    if (!Number.isFinite(x)) return "0.00";
    return (Math.round(x * 100) / 100).toFixed(2);
  }

  function prodStr(a, b, c) {
    return `${round2(a)} × ${round2(b)} × ${round2(c)}`;
  }

  function formatIntegralFooter(v) {
    if (!Number.isFinite(v)) return "—";
    if (Math.abs(v) >= 1e5 || (Math.abs(v) > 0 && Math.abs(v) < 1e-4)) {
      return v.toExponential(3);
    }
    return v.toFixed(4);
  }

  function fillContributionTable() {
    if (!tbodyCalc) return;
    const grid = cmfGrid.wl;
    tbodyCalc.innerHTML = "";
    const frag = document.createDocumentFragment();
    for (let i = 0; i < grid.length; i++) {
      const S = spd[i];
      const R = refl[i];
      const tr = document.createElement("tr");
      const td0 = document.createElement("td");
      td0.textContent = String(grid[i]);
      tr.appendChild(td0);
      const tdX = document.createElement("td");
      tdX.textContent = prodStr(S, R, cmfGrid.x[i]);
      tr.appendChild(tdX);
      const tdY = document.createElement("td");
      tdY.textContent = prodStr(S, R, cmfGrid.y[i]);
      tr.appendChild(tdY);
      const tdZ = document.createElement("td");
      tdZ.textContent = prodStr(S, R, cmfGrid.z[i]);
      tr.appendChild(tdZ);
      frag.appendChild(tr);
    }
    const { X, Y, Z } = integrateXYZ();
    const foot = document.createElement("tr");
    foot.className = "calc-footer";
    const tdL = document.createElement("td");
    tdL.textContent = "Σ (XYZ)";
    foot.appendChild(tdL);
    const tdXi = document.createElement("td");
    tdXi.textContent = formatIntegralFooter(X);
    foot.appendChild(tdXi);
    const tdYi = document.createElement("td");
    tdYi.textContent = formatIntegralFooter(Y);
    foot.appendChild(tdYi);
    const tdZi = document.createElement("td");
    tdZi.textContent = formatIntegralFooter(Z);
    foot.appendChild(tdZi);
    frag.appendChild(foot);
    tbodyCalc.appendChild(frag);
  }

  function fillTable(tbody, cols) {
    tbody.innerHTML = "";
    const grid = cmfGrid.wl;
    const frag = document.createDocumentFragment();
    for (let i = 0; i < grid.length; i++) {
      const tr = document.createElement("tr");
      const td0 = document.createElement("td");
      td0.textContent = String(grid[i]);
      tr.appendChild(td0);
      for (let c = 0; c < cols.length; c++) {
        const td = document.createElement("td");
        td.textContent = formatTableCell(cols[c][i]);
        tr.appendChild(td);
      }
      frag.appendChild(tr);
    }
    tbody.appendChild(frag);
  }

  function syncTableHeights() {
    const hSpd = canvasSpd.clientHeight;
    const hRefl = canvasRefl.clientHeight;
    const hCmf = canvasCmf.clientHeight;
    tableScrollSpd.style.maxHeight = hSpd + "px";
    tableScrollRefl.style.maxHeight = hRefl + "px";
    tableScrollCmf.style.maxHeight = hCmf + "px";
    if (tableScrollCalc && canvasSpd) {
      tableScrollCalc.style.maxHeight = hSpd + "px";
    }
  }

  function drawAxes(ctx, w, h, vmin, vmax, ylab) {
    const innerH = h - PAD_T - PAD_B;
    ctx.save();
    ctx.fillStyle = "#fafafa";
    ctx.fillRect(0, 0, w, h);
    ctx.strokeStyle = "#d1d5db";
    ctx.lineWidth = 1;
    ctx.strokeRect(0.5, 0.5, w - 1, h - 1);
    ctx.fillStyle = "#6b7280";
    ctx.font = "11px system-ui,sans-serif";
    ctx.textAlign = "left";
    ctx.textBaseline = "bottom";
    ctx.fillText(
      String(Number.isFinite(vmax) ? vmax.toFixed(4) : vmax),
      PAD_L,
      PAD_T - 2
    );
    ctx.textBaseline = "top";
    ctx.fillText(
      String(Number.isFinite(vmin) ? vmin.toFixed(4) : vmin),
      PAD_L,
      PAD_T + innerH + 2
    );
    ctx.textAlign = "right";
    ctx.textBaseline = "bottom";
    ctx.fillText(ylab, w - 6, PAD_T - 2);
    ctx.restore();
  }

  function wlToX(wl, plotWlMin, plotWlMax, padL, innerW) {
    return padL + ((wl - plotWlMin) / (plotWlMax - plotWlMin)) * innerW;
  }

  function valToY(val, vmin, vmax, padT, innerH) {
    const t = vmax > vmin ? (val - vmin) / (vmax - vmin) : 0.5;
    return padT + (1 - t) * innerH;
  }

  function drawWlAxis(ctx, w, h, plotWlMin, plotWlMax) {
    const innerW = w - PAD_L - PAD_R;
    const ticks = [380, 400, 450, 500, 550, 600, 650, 700];
    ctx.save();
    ctx.font = "10px system-ui,sans-serif";
    ctx.fillStyle = "#6b7280";
    ctx.textBaseline = "top";
    for (let k = 0; k < ticks.length; k++) {
      const tw = ticks[k];
      if (tw < plotWlMin || tw > plotWlMax) continue;
      const px = wlToX(tw, plotWlMin, plotWlMax, PAD_L, innerW);
      ctx.textAlign = "center";
      ctx.fillText(tw + " nm", px, h - 18);
      ctx.beginPath();
      ctx.strokeStyle = "#9ca3af";
      ctx.lineWidth = 1;
      ctx.moveTo(px, h - PAD_B);
      ctx.lineTo(px, h - PAD_B + 5);
      ctx.stroke();
    }
    ctx.restore();
  }

  function drawSeries(
    ctx,
    canvas,
    gridWl,
    series,
    colors,
    plotWlMin,
    plotWlMax,
    vmin,
    vmax,
    ylab,
    ctrl,
    drawHandles
  ) {
    const rect = canvas.getBoundingClientRect();
    const w = rect.width;
    const h = rect.height;
    const innerW = w - PAD_L - PAD_R;
    const innerH = h - PAD_T - PAD_B;
    drawAxes(ctx, w, h, vmin, vmax, ylab);

    ctx.save();
    ctx.beginPath();
    ctx.rect(PAD_L, PAD_T, innerW, innerH);
    ctx.clip();

    for (let s = 0; s < series.length; s++) {
      const arr = series[s];
      ctx.strokeStyle = colors[s];
      ctx.lineWidth = 1.5;
      ctx.beginPath();
      for (let i = 0; i < gridWl.length; i++) {
        const px = wlToX(gridWl[i], plotWlMin, plotWlMax, PAD_L, innerW);
        const py = valToY(arr[i], vmin, vmax, PAD_T, innerH);
        if (i === 0) ctx.moveTo(px, py);
        else ctx.lineTo(px, py);
      }
      ctx.stroke();
    }

    if (drawHandles && ctrl && ctrl.wl.length) {
      ctx.fillStyle = "#111827";
      for (let i = 0; i < ctrl.wl.length; i++) {
        const px = wlToX(ctrl.wl[i], plotWlMin, plotWlMax, PAD_L, innerW);
        const py = valToY(ctrl.v[i], vmin, vmax, PAD_T, innerH);
        ctx.beginPath();
        ctx.arc(px, py, 5, 0, Math.PI * 2);
        ctx.fill();
        ctx.strokeStyle = "#fff";
        ctx.lineWidth = 1;
        ctx.stroke();
      }
    }
    ctx.restore();
    drawWlAxis(ctx, w, h, plotWlMin, plotWlMax);
  }

  /** Monochromatic color at λ from CMF (x̄/ȳ, 1, z̄/ȳ); fixed display gain for the strip. */
  function monoRgbForLambda(lambdaNm) {
    const xb = interpLinear(cmfGrid.wl, cmfGrid.x, lambdaNm);
    const yb = interpLinear(cmfGrid.wl, cmfGrid.y, lambdaNm);
    const zb = interpLinear(cmfGrid.wl, cmfGrid.z, lambdaNm);
    if (yb < 1e-14) {
      return { r: 0, g: 0, b: 0 };
    }
    return xyzToSrgbGamma(xb / yb, 1, zb / yb, 0.82);
  }

  function drawSpectralStrip() {
    if (!canvasSpectral || !ctxSpectral || cmfGrid.wl.length < 2) return;
    const rect = canvasSpectral.getBoundingClientRect();
    const w = Math.max(2, Math.floor(rect.width));
    const h = Math.max(2, Math.floor(rect.height));
    const wl0 = STRIP_WL_MIN;
    const wl1 = STRIP_WL_MAX;
    for (let ix = 0; ix < w; ix++) {
      const t = w <= 1 ? 0 : ix / (w - 1);
      const lambda = wl0 + t * (wl1 - wl0);
      const rgb = monoRgbForLambda(lambda);
      ctxSpectral.fillStyle = `rgb(${Math.round(rgb.r * 255)},${Math.round(rgb.g * 255)},${Math.round(
        rgb.b * 255
      )})`;
      ctxSpectral.fillRect(ix, 0, 1, h);
    }
    ctxSpectral.strokeStyle = "#d1d5db";
    ctxSpectral.lineWidth = 1;
    ctxSpectral.strokeRect(0.5, 0.5, w - 1, h - 1);
  }

  function drawAll() {
    recomputeArraysFromControls();
    const grid = cmfGrid.wl;
    const plotWlMin = wlMin;
    const plotWlMax = wlMax;

    let smin;
    let smax;
    if (customSpd) {
      smin = 0;
      smax = SPD_CUSTOM_MAX;
    } else {
      smin = Infinity;
      smax = -Infinity;
      for (let i = 0; i < spd.length; i++) {
        if (spd[i] < smin) smin = spd[i];
        if (spd[i] > smax) smax = spd[i];
      }
      if (!Number.isFinite(smin) || smin === smax) {
        smin = 0;
        smax = 1;
      } else {
        const padv = (smax - smin) * 0.08 || 0.01;
        smin -= padv;
        smax += padv;
      }
    }

    drawSeries(
      ctxSpd,
      canvasSpd,
      grid,
      [spd],
      ["#2563eb"],
      plotWlMin,
      plotWlMax,
      smin,
      smax,
      "S(λ)",
      customSpd ? ctrlSpd : null,
      customSpd
    );

    let rmin;
    let rmax;
    let reflDraw;
    if (customRefl) {
      rmin = 0;
      rmax = REFL_CUSTOM_MAX;
      reflDraw = refl.map((r) => r * REFL_CUSTOM_MAX);
    } else {
      rmin = Infinity;
      rmax = -Infinity;
      for (let i = 0; i < refl.length; i++) {
        if (refl[i] < rmin) rmin = refl[i];
        if (refl[i] > rmax) rmax = refl[i];
      }
      if (!Number.isFinite(rmin) || rmin === rmax) {
        rmin = 0;
        rmax = 1;
      } else {
        const padv = (rmax - rmin) * 0.08 || 0.01;
        rmin -= padv;
        rmax += padv;
      }
      reflDraw = refl;
    }

    drawSeries(
      ctxRefl,
      canvasRefl,
      grid,
      [reflDraw],
      ["#059669"],
      plotWlMin,
      plotWlMax,
      rmin,
      rmax,
      customRefl ? "R (%)" : "R(λ)",
      customRefl ? ctrlRefl : null,
      customRefl
    );

    let cmin = 0;
    let cmax = Math.max(
      0.0001,
      Math.max(...cmfGrid.x, ...cmfGrid.y, ...cmfGrid.z)
    );
    cmax *= 1.05;

    drawSeries(
      ctxCmf,
      canvasCmf,
      grid,
      [cmfGrid.x, cmfGrid.y, cmfGrid.z],
      ["#dc2626", "#16a34a", "#2563eb"],
      plotWlMin,
      plotWlMax,
      cmin,
      cmax,
      "CMF",
      null,
      false
    );

    fillTable(tbodySpd, [spd]);
    fillTable(tbodyRefl, [refl]);
    fillTable(tbodyCmf, [cmfGrid.x, cmfGrid.y, cmfGrid.z]);
    fillContributionTable();

    syncTableHeights();
    updateColorDisplay();
  }

  function resizeCanvases() {
    const dpr = window.devicePixelRatio || 1;
    const stripH = 36;
    [canvasSpd, canvasRefl, canvasCmf].forEach((cv) => {
      const rect = cv.getBoundingClientRect();
      const cw = Math.max(300, Math.floor(rect.width));
      const ch = 160;
      cv.width = Math.floor(cw * dpr);
      cv.height = Math.floor(ch * dpr);
      cv.getContext("2d").setTransform(dpr, 0, 0, dpr, 0, 0);
    });
    if (canvasSpectral && ctxSpectral) {
      const rect = canvasSpectral.getBoundingClientRect();
      const cw = Math.max(300, Math.floor(rect.width));
      canvasSpectral.width = Math.floor(cw * dpr);
      canvasSpectral.height = Math.floor(stripH * dpr);
      ctxSpectral.setTransform(dpr, 0, 0, dpr, 0, 0);
    }
    drawAll();
    drawSpectralStrip();
  }

  async function loadText(relPath) {
    const url = new URL(relPath, window.location.href);
    const res = await fetch(url.href);
    if (!res.ok) throw new Error(`Failed to load ${relPath}`);
    return res.text();
  }

  async function loadSpdFromFile(name) {
    const text = await loadText("illuminants/" + name);
    const parsed = parseIlluminantRows(parseCSVLines(text));
    if (parsed.wl.length < 2) throw new Error("Illuminant CSV has too few points");
    customSpd = false;
    canvasSpd.classList.remove("custom-mode");
    spd = resampleToGrid(parsed.wl, parsed.v, cmfGrid.wl);
    document.getElementById("hintSpd").textContent = `Loaded “${name}”. Switch to Custom to edit with ${N_CTRL} control points.`;
    setActiveButton("toolbarSpd", name);
    drawAll();
  }

  async function loadReflFromFile(name) {
    const text = await loadText("reflectance/" + name);
    const parsed = parseReflectanceRows(parseCSVLines(text));
    if (parsed.wl.length < 2) throw new Error("Reflectance CSV has too few points");
    customRefl = false;
    canvasRefl.classList.remove("custom-mode");
    refl = resampleToGrid(parsed.wl, parsed.v, cmfGrid.wl);
    document.getElementById("hintRefl").textContent = `Loaded “${name}”. Switch to Custom to edit with ${N_CTRL} control points.`;
    setActiveButton("toolbarRefl", name);
    drawAll();
  }

  function setActiveButton(toolbarId, name) {
    const tb = document.getElementById(toolbarId);
    tb.querySelectorAll("button[data-file]").forEach((b) => {
      b.classList.toggle("active", name != null && b.dataset.file === name);
    });
    const cb = tb.querySelector("button[data-role=custom]");
    if (cb) cb.classList.toggle("active", name == null);
  }

  function setupToolbar(toolbarId, files, onCustom, onPreset) {
    const tb = document.getElementById(toolbarId);
    tb.innerHTML = "";
    for (const f of files) {
      const btn = document.createElement("button");
      btn.type = "button";
      btn.dataset.file = f;
      btn.textContent = f.replace(/\.csv$/i, "");
      btn.addEventListener("click", () => {
        onPreset(f);
      });
      tb.appendChild(btn);
    }
    const custom = document.createElement("button");
    custom.type = "button";
    custom.dataset.role = "custom";
    custom.textContent = "Custom";
    custom.addEventListener("click", () => {
      onCustom();
    });
    tb.appendChild(custom);
  }

  function enableCustomSpd() {
    customSpd = true;
    ctrlSpd.wl = defaultControlWl();
    const smax = Math.max(...spd, 1e-12);
    ctrlSpd.v = ctrlSpd.wl.map((w) =>
      Math.min(
        SPD_CUSTOM_MAX,
        Math.max(0, (interpLinear(cmfGrid.wl, spd, w) / smax) * SPD_CUSTOM_MAX)
      )
    );
    recomputeArraysFromControls();
    canvasSpd.classList.add("custom-mode");
    document.getElementById("hintSpd").textContent = `Custom mode: drag the ${N_CTRL} handles vertically (0–${SPD_CUSTOM_MAX}).`;
    setActiveButton("toolbarSpd", null);
    drawAll();
  }


  function enableCustomRefl() {
    customRefl = true;
    ctrlRefl.wl = defaultControlWl();
    ctrlRefl.v = ctrlRefl.wl.map((w) =>
      Math.min(
        REFL_CUSTOM_MAX,
        Math.max(0, interpLinear(cmfGrid.wl, refl, w) * REFL_CUSTOM_MAX)
      )
    );
    recomputeArraysFromControls();
    canvasRefl.classList.add("custom-mode");
    document.getElementById("hintRefl").textContent = `Custom mode: drag the ${N_CTRL} handles vertically (0–${REFL_CUSTOM_MAX}).`;
    setActiveButton("toolbarRefl", null);
    drawAll();
  }


  function canvasCoords(canvas, clientX, clientY) {
    const rect = canvas.getBoundingClientRect();
    const x = clientX - rect.left;
    const y = clientY - rect.top;
    return { x, y, w: rect.width, h: rect.height };
  }

  function pickControl(canvas, ctrl, clientX, clientY, vmin, vmax) {
    const cc = canvasCoords(canvas, clientX, clientY);
    const plotWlMin = wlMin;
    const plotWlMax = wlMax;
    const cw = canvas.getBoundingClientRect().width;
    const ch = canvas.getBoundingClientRect().height;
    const innerW = cw - PAD_L - PAD_R;
    const innerH = ch - PAD_T - PAD_B;
    let best = -1;
    let bestD = 14;
    for (let i = 0; i < ctrl.wl.length; i++) {
      const px = wlToX(ctrl.wl[i], plotWlMin, plotWlMax, PAD_L, innerW);
      const py = valToY(ctrl.v[i], vmin, vmax, PAD_T, innerH);
      const dx = cc.x - px;
      const dy = cc.y - py;
      const d = Math.sqrt(dx * dx + dy * dy);
      if (d < bestD) {
        bestD = d;
        best = i;
      }
    }
    return best;
  }

  function setupDrag(canvas, getCtrl, getVRange, isCustom) {
    let idx = -1;

    canvas.addEventListener("mousedown", (e) => {
      if (!isCustom()) return;
      const ctrl = getCtrl();
      const { vmin, vmax } = getVRange();
      idx = pickControl(canvas, ctrl, e.clientX, e.clientY, vmin, vmax);
      if (idx >= 0) {
        dragTarget = canvas.id;
        canvas.classList.add("dragging");
      }
    });

    window.addEventListener("mousemove", (e) => {
      if (dragTarget !== canvas.id || idx < 0) return;
      const ctrl = getCtrl();
      const { vmin, vmax } = getVRange();
      const cc = canvasCoords(canvas, e.clientX, e.clientY);
      const innerH = cc.h - PAD_T - PAD_B;
      let t = (cc.h - PAD_B - cc.y) / innerH;
      t = Math.min(1, Math.max(0, t));
      let nv = vmin + t * (vmax - vmin);
      nv = Math.min(vmax, Math.max(vmin, nv));
      applyInfluenceDrag(ctrl, idx, nv, vmin, vmax);
      drawAll();
    });

    window.addEventListener("mouseup", () => {
      if (dragTarget === canvas.id) {
        dragTarget = null;
        canvas.classList.remove("dragging");
      }
      idx = -1;
    });
  }

  async function boot() {
    try {
      clearError();
      populateInfluenceSelect();
      const cmfText = await loadText(CMF_PATH);
      parseCMF(cmfText);
      initDefaultControls();

      spd = interpControlPoints(ctrlSpd.wl, ctrlSpd.v, cmfGrid.wl);
      refl = interpControlPoints(ctrlRefl.wl, ctrlRefl.v, cmfGrid.wl);

      let manifest = { illuminants: [], reflectance: [] };
      try {
        const mj = await loadText(MANIFEST_PATH);
        manifest = JSON.parse(mj);
      } catch {
        manifest = {
          illuminants: ["Daylight.csv", "Fluroscent.csv", "LED.csv"],
          reflectance: [
            "Green Rolling Cabinet.csv",
            "Macbeth Blue Flower.csv",
            "Wood Pine Treated.csv",
          ],
        };
      }

      setupToolbar("toolbarSpd", manifest.illuminants, enableCustomSpd, (f) => {
        loadSpdFromFile(f).catch((err) => showError(String(err.message || err)));
      });
      setupToolbar("toolbarRefl", manifest.reflectance, enableCustomRefl, (f) => {
        loadReflFromFile(f).catch((err) => showError(String(err.message || err)));
      });

      try {
        await loadSpdFromFile(manifest.illuminants[0]);
      } catch (e) {
        customSpd = true;
        spd = interpControlPoints(ctrlSpd.wl, ctrlSpd.v, cmfGrid.wl);
      }
      try {
        await loadReflFromFile(manifest.reflectance[0]);
      } catch (e) {
        customRefl = true;
        refl = interpControlPoints(ctrlRefl.wl, ctrlRefl.v, cmfGrid.wl);
      }

      setupDrag(
        canvasSpd,
        () => ctrlSpd,
        () => {
          if (customSpd) return { vmin: 0, vmax: SPD_CUSTOM_MAX };
          let smin = Infinity;
          let smax = -Infinity;
          for (let i = 0; i < spd.length; i++) {
            if (spd[i] < smin) smin = spd[i];
            if (spd[i] > smax) smax = spd[i];
          }
          if (!Number.isFinite(smin) || smin === smax) {
            smin = 0;
            smax = 1;
          } else {
            const padv = (smax - smin) * 0.08 || 0.01;
            smin -= padv;
            smax += padv;
          }
          return { vmin: smin, vmax: smax };
        },
        () => customSpd
      );

      setupDrag(
        canvasRefl,
        () => ctrlRefl,
        () => {
          if (customRefl) return { vmin: 0, vmax: REFL_CUSTOM_MAX };
          let rmin = Infinity;
          let rmax = -Infinity;
          for (let i = 0; i < refl.length; i++) {
            if (refl[i] < rmin) rmin = refl[i];
            if (refl[i] > rmax) rmax = refl[i];
          }
          if (!Number.isFinite(rmin) || rmin === rmax) {
            rmin = 0;
            rmax = 1;
          } else {
            const padv = (rmax - rmin) * 0.08 || 0.01;
            rmin -= padv;
            rmax += padv;
          }
          return { vmin: rmin, vmax: rmax };
        },
        () => customRefl
      );

      if (intensitySlider) {
        intensitySlider.addEventListener("input", () => {
          if (intensityValue) intensityValue.textContent = getIntensityScale().toFixed(2);
          updateColorDisplay();
        });
      }

      window.addEventListener("resize", resizeCanvases);
      requestAnimationFrame(resizeCanvases);
    } catch (err) {
      showError(String(err.message || err));
    }
  }

  boot();
})();
