// Minimal, robust renderer for the SPO "universe" panel.
// Implements:
// 1. Sorting circles by universe index in both Committee and Voters sections.
// 2. Left-side stats for Committee (total / persistent / non-persistent).
// 3. Updated Voters stats (total / persistent / non-persistent + in-committee vs outside breakdown).
// 4. "(this election)" and "(observed votes)" strings are handled in HTML, not here.

const $ = (sel) => document.querySelector(sel);

function setText(id, value) {
    const el = document.getElementById(id);
    if (el) el.textContent = value ?? "—";
}

function shortenHex(hex) {
    if (typeof hex !== "string") return "";
    const h = hex.startsWith("0x") ? hex.slice(2) : hex;
    if (h.length <= 12) return "0x" + h;
    return "0x" + h.slice(0, 6) + "…" + h.slice(-4);
}

// ---------- CSS bootstrap (minimal positioning only) ----------
function ensureUniverseStyles() {
    if (document.getElementById("universe-inline-css")) return;
    const style = document.createElement("style");
    style.id = "universe-inline-css";
    style.textContent = `
    :root {
      --dot-size: 30px;   /* diameter of each circle */
      --dot-gap: 5px;     /* space between circles */
    }

    #universe_canvas {
      min-height: calc(var(--dot-size) * 6);
      position: relative;
    }

    /* Grid that lays out the circles */
    .universe-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(var(--dot-size), var(--dot-size)));
      grid-auto-rows: var(--dot-size);
      gap: var(--dot-gap) var(--dot-gap);
      align-content: start;
      justify-content: start;
      padding-top: 8px;
    }

    /* Ensure each dot consumes the whole grid cell and is a perfect circle */
    .pool-dot {
      width: var(--dot-size);
      height: var(--dot-size);
      border-radius: 50%;
      position: relative; /* hosts the centered numeric label */
      display: inline-block;
    }

    /* Numeric label inside each dot */
    .pool-dot .node-label {
      position: absolute;
      top: 50%;
      left: 0;
      width: 100%;
      transform: translateY(-50%);
      text-align: center;
      font-weight: 700;
      color: #ffffff;              /* white text for contrast */
      text-shadow: 0 1px 2px rgba(0,0,0,0.4); /* subtle halo for readability */
      pointer-events: none;
      user-select: none;
    }
    .tooltip-box {
        position: absolute;
        background: rgba(30, 30, 30, 0.9);
        color: #fff;
        padding: 6px 8px;
        border-radius: 6px;
        font-size: 12px;
        line-height: 1.4;
        pointer-events: none;
        z-index: 1000;
        box-shadow: 0 2px 6px rgba(0,0,0,0.3);
    }
    .pool-dot.is-voter::after {
      content: "";
      position: absolute;
      inset: -3px;
      border: 2px solid #19c37d; /* green ring for voters */
      border-radius: 50%;
    }
    `;
    document.head.appendChild(style);
}

// ---------- grid column sync so rows align across sections ----------
function computeGridColumnsFrom(el) {
    // Derive how many columns the Universe grid is using based on the cell size and gaps.
    if (!el) return null;
    const cs = getComputedStyle(document.documentElement);
    const dot = parseFloat(cs.getPropertyValue("--dot-size")) || 30;
    const gap = parseFloat(cs.getPropertyValue("--dot-gap")) || 5;

    // Available width inside the container
    const width = el.clientWidth;
    if (!width || width <= 0) return null;

    // Each column uses dot width plus the horizontal gap, except the last column which has no trailing gap.
    // We approximate by including the gap to compute a safe floor.
    const cols = Math.max(1, Math.floor((width + gap) / (dot + gap)));
    return cols;
}

function applyFixedColumns(el, cols) {
    if (!el || !cols) return;
    el.style.display = "grid";
    el.style.gridTemplateColumns = `repeat(${cols}, var(--dot-size))`;
    el.style.gridAutoRows = "var(--dot-size)";
    el.style.gap = "var(--dot-gap)";
}

function syncGridColumns() {
    const universeEl = document.getElementById("universe_canvas");
    const cols = computeGridColumnsFrom(universeEl);
    if (!cols) return;
    const committeeEl = document.getElementById("committee_canvas");
    const votersEl = document.getElementById("voters_canvas");
    applyFixedColumns(committeeEl, cols);
    applyFixedColumns(votersEl, cols);
}

// Helper: Find 1-based universe index for a given poolId
function findUniverseIndexByPoolId(demo, poolId) {
    if (!demo || !Array.isArray(demo.universe)) return null;
    const i = demo.universe.findIndex(p => (p.pool_id || p.id) === poolId);
    return i >= 0 ? (i + 1) : null;
}

// Helper: Get a mapping from poolId to universe index (1-based)
function buildPoolIdToUniverseIndex(demo) {
    const map = new Map();
    if (!demo || !Array.isArray(demo.universe)) return map;
    for (let i = 0; i < demo.universe.length; ++i) {
        const poolId = demo.universe[i].pool_id || demo.universe[i].id;
        if (poolId) map.set(poolId, i + 1);
    }
    return map;
}

// ---------- main render ----------
function renderUniverse(universe) {
    ensureUniverseStyles();

    let pools = [];
    if (Array.isArray(universe)) {
        pools = universe;
    } else if (universe && typeof universe === "object" && Array.isArray(universe.pools)) {
        pools = universe.pools;
    }

    const total = pools.length;
    let persistentCount = 0;
    let nonPersistentCount = 0;

    pools.forEach((pool) => {
        const isPersistent =
            pool.is_persistent === true ||
            pool.persistent === true ||
            typeof pool.persistent_id !== "undefined";
        if (isPersistent) persistentCount++;
        else nonPersistentCount++;
    });

    setText("universe_total", total || "—");
    setText("universe_persistent", persistentCount || "—");
    setText("universe_nonpersistent", nonPersistentCount || "—");

    const container = $("#universe_canvas");
    if (!container) return;

    if (total === 0) {
        container.innerHTML = "<p style='color:#888;font-size:13px;'>No data available</p>";
        return;
    }

    container.classList.add("universe-grid");
    container.innerHTML = "";

    pools.forEach((pool, i) => {
        const isPersistent =
            pool.is_persistent === true ||
            pool.persistent === true ||
            typeof pool.persistent_id !== "undefined";
        const isSelected = pool.is_selected === true || pool.selected === true;
        const isElected = pool.is_elected === true || pool.elected === true;

        const div = document.createElement("div");
        div.classList.add("pool-dot");
        if (isPersistent) div.classList.add("is-persistent");
        else div.classList.add("is-nonpersistent");
        if (isSelected) div.classList.add("is-selected");
        if (isElected) div.classList.add("is-elected");

        div.style.position = "relative";

        const label = document.createElement("span");
        label.classList.add("node-label");
        const idx = i + 1;
        label.textContent = idx;
        label.style.fontSize = (idx >= 100 ? "11px" : "13px");
        div.appendChild(label);

        const poolId = pool.pool_id || pool.id || "";
        const stake = typeof pool.stake !== "undefined" ? pool.stake : "";
        div.setAttribute("data-tooltip-html", `<b>Pool ID:</b> ${poolId}<br><b>Stake:</b> ${stake}`);
        div.title = "";

        div.addEventListener("mouseenter", (e) => {
            const tooltip = document.createElement("div");
            tooltip.className = "tooltip-box";
            tooltip.innerHTML = div.getAttribute("data-tooltip-html");
            document.body.appendChild(tooltip);
            const rect = e.target.getBoundingClientRect();
            tooltip.style.left = rect.left + window.scrollX + "px";
            tooltip.style.top = rect.top + window.scrollY - 40 + "px";
            div._tooltip = tooltip;
        });
        div.addEventListener("mouseleave", () => {
            if (div._tooltip) {
                div._tooltip.remove();
                div._tooltip = null;
            }
        });
        container.appendChild(div);
    });
}

// ---------- committee render (selected pools) ----------
function buildPersistentSet(demo) {
    const set = new Set();
    if (demo && Array.isArray(demo.universe)) {
        for (const p of demo.universe) {
            if (p && (p.is_persistent === true || p.persistent === true || typeof p.persistent_id !== "undefined")) {
                const id = p.pool_id || p.id;
                if (id) set.add(id);
            }
        }
    }
    if (demo && demo.persistent_map && typeof demo.persistent_map === "object") {
        for (const k of Object.keys(demo.persistent_map)) {
            const pid = demo.persistent_map[k];
            if (pid) set.add(pid);
        }
    }
    return set;
}

function buildPersistentIdToPoolId(map) {
    const m = new Map();
    if (!map || typeof map !== "object") return m;
    for (const [k, v] of Object.entries(map)) m.set(Number(k), v);
    return m;
}

// For safety: get poolId from a committee member (support legacy/modern)
function getCommitteePoolId(x) {
    return x && (x.pool_id || x.id);
}

function renderCommitteeFromDemo(demo) {
    if (!demo || !Array.isArray(demo.committee)) return;
    ensureUniverseStyles();
    const container = document.getElementById("committee_canvas");
    if (!container) return;

    const committee = demo.committee;
    const persistentSet = buildPersistentSet(demo);
    const poolIdToUniverseIndex = buildPoolIdToUniverseIndex(demo);

    // For stats: count persistent/non-persistent
    let persistentCount = 0, nonPersistentCount = 0;
    for (const member of committee) {
        const poolId = getCommitteePoolId(member);
        if (persistentSet.has(poolId)) persistentCount++;
        else nonPersistentCount++;
    }
    setText("committee_total", committee.length || "—");
    setText("committee_persistent", persistentCount || "—");
    setText("committee_nonpersistent", nonPersistentCount || "—");

    // Sort committee members by universe index (ascending), fallback to original order
    const sorted = [...committee].sort((a, b) => {
        const idxA = poolIdToUniverseIndex.get(getCommitteePoolId(a)) ?? 99999;
        const idxB = poolIdToUniverseIndex.get(getCommitteePoolId(b)) ?? 99999;
        return idxA - idxB;
    });

    container.classList.add("universe-grid");
    container.innerHTML = "";
    sorted.forEach((member, i) => {
        const poolId = getCommitteePoolId(member) || "";
        const isPersistent = persistentSet.has(poolId);
        const universeIdx = poolIdToUniverseIndex.get(poolId) || "";

        const div = document.createElement("div");
        div.classList.add("pool-dot");
        div.classList.add(isPersistent ? "is-persistent" : "is-nonpersistent");

        // Numeric label: universe index (if known), else fallback to committee index
        const label = document.createElement("span");
        label.classList.add("node-label");
        const idx = universeIdx || (i + 1);
        label.textContent = idx;
        label.style.fontSize = (idx >= 100 ? "11px" : "13px");
        div.appendChild(label);

        const stake = typeof member.stake !== "undefined" ? member.stake : "";
        div.setAttribute("data-tooltip-html", `<b>Pool ID:</b> ${poolId}<br><b>Stake:</b> ${stake}`);
        div.title = "";

        div.addEventListener("mouseenter", (e) => {
            const tooltip = document.createElement("div");
            tooltip.className = "tooltip-box";
            tooltip.innerHTML = div.getAttribute("data-tooltip-html");
            document.body.appendChild(tooltip);
            const rect = e.target.getBoundingClientRect();
            tooltip.style.left = rect.left + window.scrollX + "px";
            tooltip.style.top = rect.top + window.scrollY - 40 + "px";
            div._tooltip = tooltip;
        });
        div.addEventListener("mouseleave", () => {
            if (div._tooltip) {
                div._tooltip.remove();
                div._tooltip = null;
            }
        });
        container.appendChild(div);
    });
}

function buildVoterPools(demo) {
    const pidToPool = buildPersistentIdToPoolId(demo && demo.persistent_map);
    const pids = (demo?.voters?.persistent_ids ?? []);
    const nonp = (demo?.voters?.nonpersistent_pool_ids ?? []);
    const persistentPools = pids.map(pid => pidToPool.get(pid)).filter(Boolean);
    const nonpersistentPools = nonp.filter(Boolean);
    return {
        persistentPools,
        nonpersistentPools,
        all: [...new Set([...persistentPools, ...nonpersistentPools])]
    };
}

function renderVotersFromDemo(demo) {
    if (!demo) return;
    const container = document.getElementById("voters_canvas");
    const { persistentPools, nonpersistentPools, all } = buildVoterPools(demo);
    const poolIdToUniverseIndex = buildPoolIdToUniverseIndex(demo);

    // Build a lookup for stakes so tooltips can show them for voters
    const poolIdToStake = new Map();
    if (Array.isArray(demo.universe)) {
        for (const p of demo.universe) {
            const id = p.pool_id || p.id;
            if (id) poolIdToStake.set(id, (typeof p.stake !== "undefined") ? p.stake : "");
        }
    }
    if (Array.isArray(demo.committee)) {
        for (const m of demo.committee) {
            const id = m.pool_id || m.id;
            if (id && !poolIdToStake.has(id)) {
                poolIdToStake.set(id, (typeof m.stake !== "undefined") ? m.stake : "");
            }
        }
    }

    // Stats: persistent/nonpersistent, and breakdown for *nonpersistent only*
    const persistentCount = persistentPools.length;
    const nonPersistentCount = nonpersistentPools.length;

    // Build a set of committee poolIds for quick membership checks
    const committeeSet = new Set();
    if (demo.committee) {
        for (const member of demo.committee) {
            const pid = getCommitteePoolId(member);
            if (pid) committeeSet.add(pid);
        }
    }

    // Count only among non-persistent voters
    let nonpInCommittee = 0, nonpOutsideCommittee = 0;
    for (const poolId of nonpersistentPools) {
        if (committeeSet.has(poolId)) nonpInCommittee++;
        else nonpOutsideCommittee++;
    }

    setText("voters_total", (persistentCount + nonPersistentCount) || "—");
    setText("voters_persistent", persistentCount || "—");
    setText("voters_nonpersistent", nonPersistentCount || "—");
    setText("voters_nonpersistent_in_committee", nonpInCommittee || "—");
    setText("voters_nonpersistent_outside_committee", nonpOutsideCommittee || "—");

    if (!container) return;
    ensureUniverseStyles();
    container.classList.add("universe-grid");
    container.innerHTML = "";

    // Sort by universe index (ascending)
    const sorted = [...all].sort((a, b) => {
        const idxA = poolIdToUniverseIndex.get(a) ?? 99999;
        const idxB = poolIdToUniverseIndex.get(b) ?? 99999;
        return idxA - idxB;
    });
    for (const poolId of sorted) {
        const div = document.createElement("div");
        div.className = "pool-dot";
        if (persistentPools.includes(poolId)) div.classList.add("is-persistent");
        else div.classList.add("is-nonpersistent");

        // label = 1-based index in universe
        const label = document.createElement("span");
        label.classList.add("node-label");
        const idx = poolIdToUniverseIndex.get(poolId) || "";
        label.textContent = idx ? String(idx) : "";
        label.style.fontSize = (idx >= 100 ? "11px" : "13px");
        div.appendChild(label);

        const stake = poolIdToStake.get(poolId);
        const stakeLine = (stake !== undefined && stake !== "") ? `<br><b>Stake:</b> ${stake}` : "";
        div.setAttribute("data-tooltip-html", `<b>Pool ID:</b> ${poolId}` + stakeLine);
        div.title = "";

        div.addEventListener("mouseenter", (e) => {
            const tip = document.createElement("div");
            tip.className = "tooltip-box";
            tip.innerHTML = div.getAttribute("data-tooltip-html");
            document.body.appendChild(tip);
            const rect = e.target.getBoundingClientRect();
            tip.style.left = rect.left + window.scrollX + "px";
            tip.style.top = rect.top + window.scrollY - 40 + "px";
            div._tooltip = tip;
        });
        div.addEventListener("mouseleave", () => {
            if (div._tooltip) { div._tooltip.remove(); div._tooltip = null; }
        });
        container.appendChild(div);
    }
}

// ---------- data loading ----------
function getRunFromURL() {
    const p = new URLSearchParams(window.location.search);
    const run = p.get("run");
    // default to run64 if not provided
    return run && /^run\d+$/i.test(run) ? run : "run64";
}

async function tryFetchJson(url) {
    try {
        const r = await fetch(url, { cache: "no-store" });
        if (!r.ok) return null;
        return await r.json();
    } catch {
        return null;
    }
}

async function loadDemoJson() {
    const run = getRunFromURL();
    let data = await tryFetchJson(`/demo/${run}`);
    if (!data) data = await tryFetchJson("/static/demo.json");
    if (!data) data = await tryFetchJson("/demo.json");
    return data;
}

function fillIdentifiers(obj) {
    if (!obj) return;
    const eid = obj.eid || obj.EID;
    const eb = obj.eb_hash || obj.eb || obj.EB || obj.ebHash;
    if (eid) {
        setText("eid", eid);
        setText("eid_value", eid);
    }
    if (eb) {
        setText("eb", eb);
        setText("ebhash_value", eb);
    }
}

// ---------- boot ----------
document.addEventListener("DOMContentLoaded", async () => {
    setText("universe_total", "—");
    setText("universe_persistent", "—");
    setText("universe_nonpersistent", "—");
    setText("committee_total", "—");
    setText("committee_persistent", "—");
    setText("committee_nonpersistent", "—");
    setText("eid", "—");
    setText("eb", "—");
    setText("eid_value", "—");
    setText("ebhash_value", "—");
    setText("voters_total", "—");
    setText("voters_persistent", "—");
    setText("voters_nonpersistent", "—");
    setText("voters_in_committee", "—");
    setText("voters_outside_committee", "—");

    const demo = await loadDemoJson();

    if (demo) {
        const universe = demo.universe || demo;
        renderUniverse(universe);
        fillIdentifiers(demo.identifiers);
        fillIdentifiers(demo.certificate);
        renderCommitteeFromDemo(demo);
        renderVotersFromDemo(demo);

        // Align grid columns across sections and keep them in sync on resize
        syncGridColumns();
        window.addEventListener("resize", () => {
            syncGridColumns();
        });
    } else {
        renderUniverse([]);
    }
});

// === Middle-ellipsis for long identifiers (keep start and end) ===
function shortenMiddle(str, keepStart = 26, keepEnd = 22) {
    if (!str || typeof str !== 'string') return str;
    if (str.length <= keepStart + keepEnd + 1) return str;
    return str.slice(0, keepStart) + '…' + str.slice(-keepEnd);
}

function watchAndEllipsize(id, opts = {}) {
    const el = document.getElementById(id);
    if (!el) return;
    const { keepStart = 26, keepEnd = 22, truncate = true } = opts;
    const apply = () => {
        const full = el.getAttribute('data-full') || el.textContent.trim();
        el.setAttribute('data-full', full);
        el.title = full;
        el.classList.add('mono');
        el.textContent = truncate ? shortenMiddle(full, keepStart, keepEnd) : full;
    };
    const mo = new MutationObserver(apply);
    mo.observe(el, { childList: true, characterData: true, subtree: true });
    apply();
}

document.addEventListener('DOMContentLoaded', () => {
    watchAndEllipsize('eid_value', { truncate: false });
    watchAndEllipsize('ebhash_value', { keepStart: 26, keepEnd: 22, truncate: true });
});