// Minimal, robust renderer for the SPO "universe" panel.
// - Tries /demo/<run> (default run64), then /static/demo.json, then /demo.json
// - If found, renders all pools as circles and fills counts + identifiers
// - If not found, renders a small placeholder message

// ---------- tiny helpers ----------
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
    `;
    document.head.appendChild(style);
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

    pools.forEach((pool) => {
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

        // 1‑based index for the pool number
        const idx = pools.indexOf(pool) + 1;
        label.textContent = idx;

        // Dynamic font size: slightly smaller for 3‑digit numbers so they fit
        label.style.fontSize = (idx >= 100 ? "11px" : "13px");
        div.appendChild(label);

        const poolId = pool.pool_id || pool.id || "";
        const stake = typeof pool.stake !== "undefined" ? pool.stake : "";
        // Use HTML tooltip (bold + spacing)
        div.setAttribute("data-tooltip-html", `<b>Pool ID:</b> ${poolId}<br><b>Stake:</b> ${stake}`);
        div.title = ""; // fallback plain title cleared

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

    // Update both legacy ids and the display ids
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
    setText("eid", "—");
    setText("eb", "—");
    setText("eid_value", "—");
    setText("ebhash_value", "—");

    const demo = await loadDemoJson();

    if (demo) {
        const universe = demo.universe || demo;
        renderUniverse(universe);

        // Try identifiers from either `identifiers` or `certificate` blocks
        fillIdentifiers(demo.identifiers);
        fillIdentifiers(demo.certificate);
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
        // Remember the full value once, then only display a truncated version
        const full = el.getAttribute('data-full') || el.textContent.trim();
        el.setAttribute('data-full', full);
        el.title = full;         // hover shows the complete hash
        el.classList.add('mono'); // monospace for readability
        el.textContent = truncate ? shortenMiddle(full, keepStart, keepEnd) : full;
    };

    // Re-apply if someone else overwrites the text
    const mo = new MutationObserver(apply);
    mo.observe(el, { childList: true, characterData: true, subtree: true });

    apply();
}

document.addEventListener('DOMContentLoaded', () => {
    // EID: show full; EB hash: show middle-ellipsized so both fit on one line
    watchAndEllipsize('eid_value', { truncate: false });
    watchAndEllipsize('ebhash_value', { keepStart: 26, keepEnd: 22, truncate: true });
});