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

function formatNumber(value) {
    if (value === null || value === undefined || value === "") return "—";
    const num = Number(value);
    if (Number.isFinite(num)) return num.toLocaleString();
    if (typeof value === "string") return value;
    return String(value);
}

function formatDuration(ms) {
    if (ms === null || ms === undefined || Number.isNaN(ms)) return null;
    const value = Number(ms);
    if (!Number.isFinite(value) || value < 0) return null;
    if (value < 1000) {
        if (value < 1) return "0 ms";
        return `${Math.round(value)} ms`;
    }
    if (value < 60000) {
        const display = value < 10000 ? (value / 1000).toFixed(2) : (value / 1000).toFixed(1);
        return `${display} s`;
    }
    const minutes = Math.floor(value / 60000);
    const seconds = Math.floor((value % 60000) / 1000);
    if (minutes && seconds) return `${minutes}m ${seconds}s`;
    if (minutes) return `${minutes}m`;
    return `${Math.round(value / 1000)} s`;
}

function updateVerificationResult(status, label) {
    const box = document.getElementById("verify_result_box");
    if (!box) return;
    box.classList.remove("is-success", "is-failure");
    let text = label ?? "—";
    if (!status) {
        box.textContent = text;
        return;
    }
    const normalized = String(status).toLowerCase();
    if (normalized === "success" || normalized === "ok" || normalized === "passed") {
        box.classList.add("is-success");
        text = label ?? "Success";
    } else if (normalized === "failure" || normalized === "failed" || normalized === "error") {
        box.classList.add("is-failure");
        text = label ?? "Failure";
    }
    box.textContent = text;
}

function updateVerificationCertificate() {
    const certEl = document.getElementById("verification_cert");
    if (!certEl) return;
    const data = latestCertificateRender;
    certEl.classList.remove("with-tooltip");
    certEl.style.width = "";
    certEl.style.minWidth = "";
    certEl.style.height = "";
    certEl.textContent = "Certificate";
    if (data) {
        if (data.width) certEl.style.width = data.width;
        if (data.minWidth) certEl.style.minWidth = data.minWidth;
        if (data.height) certEl.style.height = data.height;
        if (data.tooltipHtml) {
            attachTooltip(certEl, data.tooltipHtml);
            certEl.classList.add("with-tooltip");
        } else {
            attachTooltip(certEl, null);
        }
    } else {
        attachTooltip(certEl, null);
    }
}

function applyVerificationStatus(status) {
    latestVerificationStatus = status ?? null;
    let normalized = null;
    let label = "—";
    if (status !== undefined && status !== null) {
        normalized = String(status).toLowerCase();
        if (normalized === "success" || normalized === "ok" || normalized === "passed") {
            label = "Success";
        } else if (normalized === "failure" || normalized === "failed" || normalized === "error") {
            label = "Failure";
        } else {
            label = String(status);
            normalized = null;
        }
    }
    const statusEl = document.getElementById("verify_status");
    if (statusEl) {
        statusEl.classList.remove("text-green", "text-red");
        if (label === "Success") {
            statusEl.classList.add("text-green");
        } else if (label === "Failure") {
            statusEl.classList.add("text-red");
        }
    }
    setText("verify_status", label);
    updateVerificationResult(normalized, label !== "—" ? label : null);
}

function firstFinite(...values) {
    for (const value of values) {
        if (value === null || value === undefined || value === "") continue;
        const num = Number(value);
        if (Number.isFinite(num)) return num;
    }
    return null;
}

function createEmptyState(message) {
    const p = document.createElement("p");
    p.className = "empty-state";
    p.textContent = message;
    return p;
}

// --- Vote byte sizes (visualization constants) ---
const PERSISTENT_VOTE_BYTES = 134;   // bytes per persistent vote (viz)
const NONPERSISTENT_VOTE_BYTES = 247; // bytes per non-persistent vote (viz)

const FIXED_GRID_COLUMNS = 20; // circles per row for Voters alignment
const UNIVERSE_COLUMNS = 30;   // circles per row for Universe panel
const COMMITTEE_COLUMNS = 20;  // seat boxes per row for Committee
const COMMITTEE_ROW_HEIGHT = "calc(var(--seat-size) + 10px)";
const VOTE_RECT_HEIGHT = 36;

let latestDisplayedVoterCount = null;
let latestVerificationStatus = null;
let latestCertificateRender = null;

// ---------- tooltip helpers ----------
function positionTooltip(target, tooltip) {
    if (!target || !tooltip) return;
    const rect = target.getBoundingClientRect();
    const top = rect.top + window.scrollY - 40;
    tooltip.style.left = `${rect.left + window.scrollX}px`;
    tooltip.style.top = `${Math.max(window.scrollY + 4, top)}px`;
}

function attachTooltip(element, html) {
    if (!element) return;
    if (!html) {
        element.removeAttribute("data-tooltip-html");
        return;
    }

    element.dataset.tooltipHtml = html;
    element.removeAttribute("title");

    if (element._tooltipHandlers) return;

    const show = (event) => {
        const tooltip = document.createElement("div");
        tooltip.className = "tooltip-box";
        tooltip.innerHTML = element.dataset.tooltipHtml;
        document.body.appendChild(tooltip);
        positionTooltip(event.currentTarget, tooltip);
        element._tooltip = tooltip;
    };

    const move = (event) => {
        if (element._tooltip) {
            positionTooltip(event.currentTarget, element._tooltip);
        }
    };

    const hide = () => {
        if (element._tooltip) {
            element._tooltip.remove();
            element._tooltip = null;
        }
    };

    element.addEventListener("mouseenter", show);
    element.addEventListener("mousemove", move);
    element.addEventListener("mouseleave", hide);
    element._tooltipHandlers = { show, move, hide };
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

function applyFixedColumns(
    el,
    cols,
    columnSize = "var(--dot-size)",
    rowSize = "var(--dot-size)",
    gapSize = "var(--dot-gap)"
) {
    if (!el || !cols) return;
    el.style.display = "grid";
    el.style.gridTemplateColumns = `repeat(${cols}, ${columnSize})`;
    el.style.gridAutoRows = rowSize;
    el.style.gap = gapSize;
}

function syncGridColumns() {
    const committeeEl = document.getElementById("committee_canvas");
    if (committeeEl) {
        const seatCount = committeeEl.querySelectorAll(".seat-box").length;
        const committeeCols = seatCount ? Math.min(COMMITTEE_COLUMNS, seatCount) : COMMITTEE_COLUMNS;
        applyFixedColumns(
            committeeEl,
            committeeCols,
            "var(--seat-size)",
            COMMITTEE_ROW_HEIGHT,
            "var(--seat-gap)"
        );
    }
}
// Shared helper to compute vote rectangle width based on bytes
function voteWidthPx(bytes) {
    const maxBytes = Math.max(PERSISTENT_VOTE_BYTES, NONPERSISTENT_VOTE_BYTES) || 1;
    const maxWidthPx = 48; // width used for the largest vote (non-persistent)
    return Math.max(14, Math.round((bytes / maxBytes) * maxWidthPx));
}


// Human-readable byte formatter
function formatBytes(bytes) {
    if (bytes === null || bytes === undefined || isNaN(bytes)) return "—";
    const units = ['bytes', 'KB', 'MB', 'GB'];
    let b = Math.max(0, Number(bytes));
    let i = 0;
    while (b >= 1024 && i < units.length - 1) { b /= 1024; i++; }
    return `${b.toFixed(b < 10 && i > 0 ? 1 : 0)} ${units[i]}`;
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

    setText("universe_total", (total ?? "—"));
    setText("universe_persistent", (persistentCount ?? "—"));
    setText("universe_nonpersistent", (nonPersistentCount ?? "—"));
    // Add total stake calculation
    const totalStake = pools.reduce((sum, p) => sum + (Number(p.stake) || 0), 0);
    const hasStake = pools.some(p => p.stake !== undefined && p.stake !== null);
    setText("universe_stake", hasStake ? formatNumber(totalStake) : "—");

    const container = $("#universe_canvas");
    if (!container) return;

    if (total === 0) {
        container.classList.add("universe-grid");
        container.replaceChildren(createEmptyState("No data available"));
        return;
    }

    container.classList.add("universe-grid");
    container.style.gridTemplateColumns = `repeat(${UNIVERSE_COLUMNS}, var(--dot-size))`;
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

        const label = document.createElement("span");
        label.classList.add("node-label");
        const idx = i + 1;
        label.textContent = idx;
        label.style.fontSize = (idx >= 100 ? "11px" : "13px");
        div.appendChild(label);

        const poolId = pool.pool_id || pool.id || "";
        const stake = typeof pool.stake !== "undefined" ? pool.stake : pool.total_stake;
        const tooltipHtml = [
            `<b>Pool ID:</b> ${poolId || "—"}`,
            `<b>Stake:</b> ${formatNumber(stake)}`
        ].join("<br>");
        attachTooltip(div, tooltipHtml);

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

function buildPersistentIdToPoolId(demo) {
    const m = new Map();
    const raw = demo?.persistent_map;
    if (raw && typeof raw === "object") {
        for (const [k, v] of Object.entries(raw)) {
            if (v) {
                const numericKey = Number(k);
                if (!Number.isNaN(numericKey)) m.set(numericKey, v);
                m.set(String(k), v);
            }
        }
    }

    if (m.size === 0 && Array.isArray(demo?.committee?.seats)) {
        for (const seat of demo.committee.seats) {
            if (!seat || !seat.pool_id) continue;
            if (seat.position !== undefined) {
                const pos = Number(seat.position);
                m.set(pos, seat.pool_id);
                if (Number.isFinite(pos)) {
                    m.set(pos - 1, seat.pool_id);
                }
            }
            if (seat.index !== undefined) m.set(Number(seat.index), seat.pool_id);
        }
    }
    return m;
}

// For safety: get poolId from a committee member (support legacy/modern)
function getCommitteePoolId(x) {
    return x && (x.pool_id || x.id);
}

function renderCommitteeFromDemo(demo) {
    if (!demo) return;
    const container = document.getElementById("committee_canvas");
    if (!container) return;

    // Normalize seats source:
    // Prefer new model: demo.committee.seats = [{position, pool_id?, stake?, kind: "persistent"|"nonpersistent"}]
    // Fallback to legacy: demo.committee = [ {pool_id, stake?}, ... ] where all entries are persistent seats.
    let seats = [];
    if (demo.committee && Array.isArray(demo.committee.seats)) {
        seats = demo.committee.seats.slice().sort((a, b) => (a.position || 0) - (b.position || 0));
    } else if (Array.isArray(demo.committee)) {
        seats = demo.committee.map((m, i) => ({
            position: (m.position ?? (i + 1)),
            pool_id: getCommitteePoolId(m),
            stake: (typeof m.stake !== "undefined" ? m.stake : undefined),
            kind: "persistent"
        }));
    } else {
        // Nothing to render
        container.classList.remove("committee-grid");
        container.replaceChildren(createEmptyState("No committee seats"));
        return;
    }

    const poolIdToUniverseIndex = buildPoolIdToUniverseIndex(demo);

    // Stats: show total, persistent, and non-persistent seat counts.
    setText("committee_total", (seats.length ?? "—"));
    // Compute persistent/nonpersistent seat counts
    const persistentCount = seats.filter(s => s.kind === "persistent").length;
    const nonPersistentCount = seats.length - persistentCount;
    setText("committee_persistent", persistentCount);
    setText("committee_nonpersistent", nonPersistentCount);

    // Layout as seats (boxes), not dots
    container.classList.remove("universe-grid");
    container.classList.add("committee-grid");
    container.innerHTML = "";
    const initialCols = Math.max(1, Math.min(COMMITTEE_COLUMNS, seats.length));
    applyFixedColumns(
        container,
        initialCols,
        "var(--seat-size)",
        COMMITTEE_ROW_HEIGHT,
        "var(--seat-gap)"
    );

    for (const seat of seats) {
        const div = document.createElement("div");
        div.className = "seat-box";
        const hasPool = !!seat.pool_id;
        const isPersistentSeat = seat.kind === "persistent";
        div.classList.add(isPersistentSeat ? "is-persistent-seat" : "is-nonpersistent-seat");

        // Seat number at top-left
        const num = document.createElement("span");
        num.className = "seat-num";
        num.textContent = String(seat.position ?? "");
        div.appendChild(num);

        // If seat has a pool, add a pool-dot (reuse universal styling)
        if (hasPool) {
            const poolCircle = document.createElement("div");
            poolCircle.className = "pool-dot is-nonpersistent";
            const lbl = document.createElement("span");
            lbl.className = "node-label";
            const uidx = poolIdToUniverseIndex.get(seat.pool_id);
            lbl.textContent = uidx ? String(uidx) : "";
            lbl.style.fontSize = (uidx >= 100 ? "11px" : "13px");
            poolCircle.appendChild(lbl);
            div.appendChild(poolCircle);
        }

        // Set tooltip for assigned/non-assigned seats
        if (hasPool) {
            const poolId = seat.pool_id;
            const stake = (typeof seat.stake !== "undefined") ? seat.stake : "";
            const tooltipHtml = [
                `<b>Seat #${seat.position}</b>`,
                `<b>Pool ID:</b> ${poolId}`,
                stake !== "" ? `<b>Stake:</b> ${formatNumber(stake)}` : ""
            ].filter(Boolean).join("<br>");
            attachTooltip(div, tooltipHtml);
        } else {
            attachTooltip(div, `<b>Seat #${seat.position}</b><br>Empty non-persistent slot`);
        }

        container.appendChild(div);
    }
}

function buildVoterPools(demo) {
    const pidToPool = buildPersistentIdToPoolId(demo);

    const persistentMap = new Map();
    const nonPersistentMap = new Map();

    const toSeatIndex = (value, { isPosition = false } = {}) => {
        if (value === undefined || value === null) return null;
        const parsed = Number(value);
        if (!Number.isFinite(parsed)) return null;
        const intVal = Math.trunc(parsed);
        if (isPosition) {
            return Math.max(0, intVal - 1);
        }
        return Math.max(0, intVal);
    };

    const ensurePersistentEntry = (seatIndex) => {
        if (seatIndex === undefined || seatIndex === null) return null;
        const numericSeat = Number(seatIndex);
        if (!Number.isFinite(numericSeat)) return null;
        const normalizedSeat = Math.max(0, Math.trunc(numericSeat));
        const mapKey = String(normalizedSeat);
        let entry = persistentMap.get(mapKey);
        if (!entry) {
            const poolId = pidToPool.get(normalizedSeat) ?? pidToPool.get(mapKey) ?? null;
            entry = {
                seatIndex: normalizedSeat,
                seatPosition: normalizedSeat + 1,
                poolId,
                hasVote: false,
                signature: null,
                seat: null
            };
            persistentMap.set(mapKey, entry);
        }
        return entry;
    };

    const ensureNonPersistentEntry = (poolId) => {
        if (!poolId) return null;
        const key = String(poolId);
        let entry = nonPersistentMap.get(key);
        if (!entry) {
            entry = {
                poolId: key,
                eligibility: null,
                signature: null,
                hasVote: false
            };
            nonPersistentMap.set(key, entry);
        }
        return entry;
    };

    const votersObj = demo?.voters ?? demo?.voters_filtered ?? demo?.voters_unfiltered ?? null;
    if (votersObj && typeof votersObj === "object") {
        const persistentIds = votersObj.persistent_ids ?? [];
        for (const seatId of persistentIds) {
            const idx = toSeatIndex(seatId);
            if (idx !== null) ensurePersistentEntry(idx);
        }

        const nonIds = votersObj.nonpersistent_pool_ids ?? [];
        for (const poolId of nonIds) ensureNonPersistentEntry(poolId);
    }

    if (Array.isArray(demo?.votes_preview)) {
        for (const entry of demo.votes_preview) {
            if (!entry) continue;
            if (entry.type === "persistent") {
                const idx = toSeatIndex(entry.seat_id ?? entry.seatId ?? entry.id);
                const record = ensurePersistentEntry(idx);
                if (record) {
                    record.hasVote = true;
                    record.signature = entry.signature ?? entry.vote_signature ?? null;
                    if (!record.poolId && entry.pool_id) record.poolId = entry.pool_id;
                }
            } else if (entry.type === "nonpersistent") {
                const record = ensureNonPersistentEntry(entry.pool_id ?? entry.id);
                if (record) {
                    record.signature = record.signature ?? entry.signature ?? entry.vote_signature ?? null;
                    record.eligibility = record.eligibility ?? entry.eligibility_sigma_eid_prefix ?? entry.eligibility ?? null;
                    record.hasVote = true;
                }
            }
        }
    }

    const committeePersistentSeats = Array.isArray(demo?.committee?.seats)
        ? demo.committee.seats.filter(seat => seat && seat.kind === "persistent")
        : [];

    for (const seat of committeePersistentSeats) {
        const seatIdx = toSeatIndex(seat?.position, { isPosition: true });
        const record = ensurePersistentEntry(seatIdx);
        if (record) {
            if (!record.poolId && seat.pool_id) record.poolId = seat.pool_id;
            record.seatPosition = Number(seat.position) || (record.seatIndex + 1);
            record.seat = seat;
        }
    }

    const persistentEntries = Array.from(persistentMap.values());
    const nonPersistentEntries = Array.from(nonPersistentMap.values()).filter(entry => entry.hasVote);
    const persistentVotePoolIds = persistentEntries
        .filter(entry => entry.hasVote && entry.poolId)
        .map(entry => entry.poolId);
    const nonPersistentPoolIds = nonPersistentEntries
        .filter(entry => entry.poolId)
        .map(entry => entry.poolId);

    return {
        persistentEntries,
        nonPersistentEntries,
        persistentPoolIds: persistentVotePoolIds,
        nonPersistentPoolIds,
        persistentSeatCount: committeePersistentSeats.length,
        nonPersistentSeatCount: Array.isArray(demo?.committee?.seats)
            ? demo.committee.seats.filter(seat => seat && seat.kind === "nonpersistent").length
            : 0
    };
}

function renderVotersFromDemo(demo) {
    if (!demo) return;
    const container = document.getElementById("voters_canvas");
    const {
        persistentEntries,
        nonPersistentEntries,
        persistentPoolIds,
        nonPersistentPoolIds,
        persistentSeatCount,
        nonPersistentSeatCount
    } = buildVoterPools(demo);
    const poolIdToUniverseIndex = buildPoolIdToUniverseIndex(demo);
    const committeePositionLookup = new Map(
        Object.entries(demo?.lookup?.committee_position_by_pool_id || {}).map(([k, v]) => [k, Number(v)])
    );
    const committeeMembers = Array.isArray(demo?.committee?.seats)
        ? demo.committee.seats
        : (Array.isArray(demo?.committee) ? demo.committee : []);

    // Build a lookup for stakes so tooltips can show them for voters (on circle), and vote tooltips can show voter id
    const poolIdToStake = new Map();
    if (Array.isArray(demo.universe)) {
        for (const p of demo.universe) {
            const id = p.pool_id || p.id;
            if (id) poolIdToStake.set(id, (typeof p.stake !== "undefined") ? p.stake : "");
        }
    }
    for (const m of committeeMembers) {
        const id = m.pool_id || m.id;
        if (id && !poolIdToStake.has(id)) {
            poolIdToStake.set(id, (typeof m.stake !== "undefined") ? m.stake : "");
        }
    }

    // Quorum / fraction (if present). Accept many possible shapes/keys and strings.
    // Do NOT set any default if not found; simply show '—'.
    let q = (
        demo?.parameters?.vote_fraction ??
        demo?.parameters?.fraction ??
        demo?.voters?.fraction ??
        demo?.voters?.quorum ??
        demo?.vote_fraction ??
        demo?.fraction ??
        demo?.quorum ??
        demo?.metadata?.vote_fraction ??
        demo?.params?.vote_fraction ??
        demo?.params?.fraction ??
        demo?.params?.quorum ??
        demo?.params?.quorum_fraction
    );
    if (typeof q === 'string') q = parseFloat(q);
    if (q !== undefined && q !== null && !Number.isNaN(q)) {
        const pct = q <= 1 ? Math.round(q * 100) : Math.round(q);
        setText('voters_quorum', pct + '%');
    } else {
        setText('voters_quorum', '—');
    }

    // Stats: persistent/nonpersistent, and breakdown for nonpersistent only
    const persistentTotalSeats = persistentSeatCount;
    const persistentVotesCount = persistentEntries.filter(entry => entry.hasVote).length;
    const nonPersistentTotalSlots = nonPersistentSeatCount;

    const displayedPersistentVotes = persistentVotesCount;
    const targetNonPersistent = nonPersistentTotalSlots
        ? Math.min(Math.round(nonPersistentTotalSlots * 0.75), nonPersistentEntries.length)
        : Math.min(Math.round(nonPersistentEntries.length * 0.75), nonPersistentEntries.length);
    const targetNonPersistentCount = Math.max(targetNonPersistent, 0);

    setText("voters_persistent", `${displayedPersistentVotes}/${persistentTotalSeats || "—"}`);


    if (!container) return;

    container.classList.remove("universe-grid", "voting-list");
    container.classList.add("votes-board");
    container.innerHTML = "";

    if (!persistentEntries.length && !nonPersistentEntries.length) {
        container.appendChild(createEmptyState("No voters recorded"));
        return;
    }

    const persistentSorted = [...persistentEntries].sort((a, b) => {
        const seatA = Number(a.seatPosition);
        const seatB = Number(b.seatPosition);
        const idxA = Number.isFinite(seatA) ? seatA : (poolIdToUniverseIndex.get(a.poolId) ?? 99999);
        const idxB = Number.isFinite(seatB) ? seatB : (poolIdToUniverseIndex.get(b.poolId) ?? 99999);
        return idxA - idxB;
    });
    const nonPersistentSorted = [...nonPersistentEntries].sort((a, b) => {
        const idxA = poolIdToUniverseIndex.get(a.poolId) ?? 99999;
        const idxB = poolIdToUniverseIndex.get(b.poolId) ?? 99999;
        return idxA - idxB;
    });
    const displayedNonPersistent = nonPersistentSorted.slice(0, targetNonPersistentCount);
    const displayedNonPersistentCount = displayedNonPersistent.length;

    const totalVotersDisplayed = displayedPersistentVotes + displayedNonPersistentCount;
    latestDisplayedVoterCount = totalVotersDisplayed;
    setText("voters_total", `${totalVotersDisplayed}`);
    setText("voters_nonpersistent", `${displayedNonPersistentCount}/${nonPersistentTotalSlots || "—"}`);

    const poolIdToSeat = new Map();
    const positionToSeat = new Map();
    const nonPersistentSeatsOrdered = [];
    for (const seat of committeeMembers) {
        if (seat && seat.pool_id) {
            poolIdToSeat.set(seat.pool_id, seat);
        }
        if (seat && seat.position !== undefined) {
            positionToSeat.set(Number(seat.position), seat);
        }
        if (seat && seat.kind === "nonpersistent") {
            nonPersistentSeatsOrdered.push(seat);
        }
    }
    nonPersistentSeatsOrdered.sort((a, b) => (a.position || 0) - (b.position || 0));

    const createArrow = () => {
        const arrow = document.createElement("span");
        arrow.className = "vote-arrow vote-flow__arrow";
        return arrow;
    };

    const createSeatTile = (seat, poolId, variant = "persistent", seatPositionOverride = null) => {
        const seatTile = document.createElement("div");
        seatTile.className = `seat-box vote-seat-inline ${variant === "persistent" ? "is-persistent-seat" : "is-nonpersistent-seat"}`;

        let seatNum = seat?.position ?? seat?.index ?? null;
        if ((seatNum === null || seatNum === undefined) && seatPositionOverride !== null && seatPositionOverride !== undefined) {
            const numericSeatPos = Number(seatPositionOverride);
            if (Number.isFinite(numericSeatPos)) {
                seatNum = numericSeatPos;
            }
        }
        const numSpan = document.createElement("span");
        numSpan.className = "seat-num";
        if (seatNum !== null && seatNum !== undefined) {
            numSpan.textContent = String(seatNum);
        } else {
            numSpan.textContent = variant === "persistent" ? "—" : "";
        }
        seatTile.appendChild(numSpan);

        const dot = document.createElement("div");
        dot.className = "pool-dot is-nonpersistent";
        const label = document.createElement("span");
        label.className = "node-label";
        const resolvedPoolId = poolId ?? seat?.pool_id ?? null;
        let universeIdx = null;
        if (resolvedPoolId) {
            if (seat && seat.index !== undefined) {
                const seatIndexNumeric = Number(seat.index);
                universeIdx = Number.isFinite(seatIndexNumeric) ? (seatIndexNumeric + 1) : null;
            }
            if (universeIdx === null) {
                const lookupIdx = poolIdToUniverseIndex.get(resolvedPoolId) ?? committeePositionLookup.get(resolvedPoolId);
                if (lookupIdx !== undefined && lookupIdx !== null) {
                    universeIdx = Number(lookupIdx);
                    if (Number.isFinite(universeIdx)) universeIdx += 1;
                }
            }
        }
        label.textContent = universeIdx ? String(universeIdx) : "";
        label.style.fontSize = (universeIdx >= 100 ? "11px" : "13px");
        dot.appendChild(label);
        seatTile.appendChild(dot);

        const tooltip = [];
        if (seatNum) tooltip.push(`<b>Seat #${seatNum}</b>`);
        if (resolvedPoolId) tooltip.push(`<b>Pool ID:</b> ${resolvedPoolId}`);
        if (seat && seat.stake !== undefined) {
            tooltip.push(`<b>Stake:</b> ${formatNumber(seat.stake)}`);
        }
        attachTooltip(seatTile, tooltip.join("<br>"));
        return seatTile;
    };

    const createNodeTile = (poolId, isPersistent) => {
        const node = document.createElement("div");
        node.className = "vote-node";

        const dot = document.createElement("div");
        dot.className = "pool-dot";
        dot.classList.add(isPersistent ? "is-persistent" : "is-nonpersistent", "is-voter");
        const label = document.createElement("span");
        label.className = "node-label";
        const universeIdx = poolIdToUniverseIndex.get(poolId);
        label.textContent = universeIdx ? String(universeIdx) : "";
        label.style.fontSize = (universeIdx >= 100 ? "11px" : "13px");
        dot.appendChild(label);
        const stake = poolIdToStake.get(poolId);
        const lines = [];
        if (poolId) {
            lines.push(`<b>Pool ID:</b> ${poolId}`);
        }
        if (stake !== undefined && stake !== "") {
            lines.push(`<b>Stake:</b> ${formatNumber(stake)}`);
        }
        attachTooltip(dot, lines.join("<br>"));
        node.appendChild(dot);

        return node;
    };

    const createVoteRect = (info, isPersistent) => {
        const voteRect = document.createElement("div");
        voteRect.className = "vote-rect";
        voteRect.classList.add(isPersistent ? "is-persistent" : "is-nonpersistent");
        const vBytes = isPersistent ? PERSISTENT_VOTE_BYTES : NONPERSISTENT_VOTE_BYTES;
        voteRect.style.width = `${voteWidthPx(vBytes)}px`;

        const tooltip = [];
        if (isPersistent) {
            const seatNum = info.seatPosition ?? info.seat?.position ?? info.seat?.index ?? "—";
            tooltip.push(`<b>Seat #${seatNum}</b>`);
            tooltip.push(`<b>Size:</b> ${formatBytes(vBytes)}`);
            if (info.signature) tooltip.push(`<b>Signature:</b> ${info.signature}`);
        } else {
            tooltip.push(`<b>Pool ID:</b> ${info.poolId}`);
            if (info.eligibility) tooltip.push(`<b>Eligibility prefix:</b> ${info.eligibility}`);
            if (info.signature) tooltip.push(`<b>Signature:</b> ${info.signature}`);
            tooltip.push(`<b>Size:</b> ${formatBytes(vBytes)}`);
        }
        attachTooltip(voteRect, tooltip.join("<br>"));
        return voteRect;
    };

    const createPersistentRow = (entry, idx) => {
        const row = document.createElement("div");
        row.className = "vote-flow__row vote-flow__row--persistent";
        const seat = entry.seat ?? poolIdToSeat.get(entry.poolId) ?? positionToSeat.get(entry.seatPosition);
        row.appendChild(createSeatTile(seat, entry.poolId ?? seat?.pool_id ?? null, "persistent", entry.seatPosition));

        const arrow = createArrow();
        if (!entry.hasVote) {
            arrow.classList.add("placeholder");
        }
        row.appendChild(arrow);

        if (entry.hasVote) {
            row.appendChild(createVoteRect({ ...entry, seat }, true));
        } else {
            const placeholder = document.createElement("div");
            placeholder.className = "vote-rect placeholder persistent";
            placeholder.style.width = `${voteWidthPx(PERSISTENT_VOTE_BYTES)}px`;
            row.appendChild(placeholder);
        }
        return row;
    };

    const createNonPersistentRow = (entry, idx) => {
        const row = document.createElement("div");
        row.className = "vote-flow__row vote-flow__row--nonpersistent";
        const seat = entry.seat ?? nonPersistentSeatsOrdered[idx] ?? null;
        row.appendChild(createSeatTile(seat, entry.poolId, "nonpersistent"));
        row.appendChild(createArrow());
        row.appendChild(createVoteRect(entry, false));
        return row;
    };

    const appendFlow = (entries, buildRow, modifier) => {
        if (!entries.length) return;
        const flow = document.createElement("div");
        flow.className = "vote-flow";
        if (modifier) flow.classList.add(modifier);
        entries.forEach((entry, index) => {
            if (!entry.seat && buildRow === createNonPersistentRow) {
                entry.seat = nonPersistentSeatsOrdered[index] ?? null;
            }
            flow.appendChild(buildRow(entry, index));
        });
        container.appendChild(flow);
    };

    appendFlow(persistentSorted, createPersistentRow, "vote-flow--persistent");
    appendFlow(displayedNonPersistent, createNonPersistentRow, "vote-flow--nonpersistent");
}

function renderAggregationFromDemo(demo) {
    const container = document.getElementById('aggregation_canvas');
    if (!container) return;

    const {
        persistentEntries,
        nonPersistentEntries,
        nonPersistentSeatCount
    } = buildVoterPools(demo);

    const poolIdToUniverseIndex = buildPoolIdToUniverseIndex(demo);
    const committeeMembers = Array.isArray(demo?.committee?.seats)
        ? demo.committee.seats
        : (Array.isArray(demo?.committee) ? demo.committee : []);

    const poolIdToSeat = new Map();
    const positionToSeat = new Map();
    for (const seat of committeeMembers) {
        if (!seat) continue;
        if (seat.pool_id) poolIdToSeat.set(seat.pool_id, seat);
        if (seat.position !== undefined) positionToSeat.set(Number(seat.position), seat);
    }

    const persistentSorted = [...persistentEntries].sort((a, b) => {
        const seatA = Number(a.seatPosition);
        const seatB = Number(b.seatPosition);
        const idxA = Number.isFinite(seatA) ? seatA : (poolIdToUniverseIndex.get(a.poolId) ?? 99999);
        const idxB = Number.isFinite(seatB) ? seatB : (poolIdToUniverseIndex.get(b.poolId) ?? 99999);
        return idxA - idxB;
    });
    const persistentVotes = persistentSorted.filter(entry => entry.hasVote);

    const nonPersistentSorted = [...nonPersistentEntries].sort((a, b) => {
        const idxA = poolIdToUniverseIndex.get(a.poolId) ?? 99999;
        const idxB = poolIdToUniverseIndex.get(b.poolId) ?? 99999;
        return idxA - idxB;
    });
    const targetNonPersistentBase = nonPersistentSeatCount
        ? Math.min(Math.round(nonPersistentSeatCount * 0.75), nonPersistentSorted.length)
        : Math.min(Math.round(nonPersistentSorted.length * 0.75), nonPersistentSorted.length);
    const targetNonPersistentCount = Math.max(targetNonPersistentBase, 0);
    const displayedNonPersistent = nonPersistentSorted.slice(0, targetNonPersistentCount);

    const persistentBytes = persistentVotes.length * PERSISTENT_VOTE_BYTES;
    const nonPersistentBytes = displayedNonPersistent.length * NONPERSISTENT_VOTE_BYTES;
    const totalVotesBytes = persistentBytes + nonPersistentBytes;
    const certBytesRaw = firstFinite(
        demo?.certificate?.cert_bytes,
        demo?.certificate?.certificate_bytes,
        demo?.certificate?.bytes,
        demo?.aggregation?.certificate_bytes
    );
    const certBytes = Number(certBytesRaw);

    const votesEl = document.getElementById('agg_votes_size');
    if (votesEl) {
        const pieces = [
            `${formatNumber(totalVotesBytes)} B`,
            ` <span class="text-green">Persistent: ${formatNumber(persistentBytes)} B</span>`,
            ` <span class="text-blue">Non-persistent: ${formatNumber(nonPersistentBytes)} B</span>`
        ];
        votesEl.innerHTML = pieces.join('<br>');
    }

    setText('agg_cert_size', certBytes && isFinite(certBytes) ? formatBytes(certBytes) : '—');

    const gainEl = document.getElementById('agg_gain');
    if (gainEl) {
        const ratioVal = totalVotesBytes > 0 && Number(certBytes) > 0
            ? totalVotesBytes / Number(certBytes)
            : null;
        gainEl.textContent = ratioVal && isFinite(ratioVal) ? `${ratioVal.toFixed(2)}×` : '—';
    }

    container.classList.add('aggregation-row');
    container.innerHTML = '';

    if (persistentVotes.length + displayedNonPersistent.length === 0) {
        latestCertificateRender = null;
        updateVerificationCertificate();
        container.appendChild(createEmptyState("No votes recorded"));
        return;
    }

    const votesGrid = document.createElement('div');
    votesGrid.className = 'agg-votes';

    const addVoteRect = (entry, isPersistent) => {
        const vote = document.createElement('div');
        vote.className = 'vote-rect';
        vote.classList.add(isPersistent ? 'is-persistent' : 'is-nonpersistent');
        const bytes = isPersistent ? PERSISTENT_VOTE_BYTES : NONPERSISTENT_VOTE_BYTES;
        vote.style.width = `${voteWidthPx(bytes)}px`;
        const tooltip = [];
        if (isPersistent) {
            const seat = entry.seat ?? poolIdToSeat.get(entry.poolId) ?? positionToSeat.get(entry.seatPosition);
            const seatNum = entry.seatPosition ?? seat?.position ?? seat?.index ?? "—";
            tooltip.push(`<b>Seat #${seatNum}</b>`);
            tooltip.push(`<b>Size:</b> ${formatBytes(bytes)}`);
            if (entry.signature) tooltip.push(`<b>Signature:</b> ${entry.signature}`);
        } else {
            if (entry.poolId) tooltip.push(`<b>Pool ID:</b> ${entry.poolId}`);
            if (entry.eligibility) tooltip.push(`<b>Eligibility prefix:</b> ${entry.eligibility}`);
            if (entry.signature) tooltip.push(`<b>Signature:</b> ${entry.signature}`);
            tooltip.push(`<b>Size:</b> ${formatBytes(bytes)}`);
        }
        attachTooltip(vote, tooltip.join('<br>'));
        votesGrid.appendChild(vote);
    };

    persistentVotes.forEach(entry => addVoteRect(entry, true));
    displayedNonPersistent.forEach(entry => addVoteRect(entry, false));

    const arrow = document.createElement('span');
    arrow.className = 'big-arrow';
    arrow.textContent = '⇒';

    const cert = document.createElement('div');
    cert.className = 'certificate-rect';
    cert.textContent = 'Certificate';

    if (totalVotesBytes > 0 && isFinite(certBytes) && certBytes > 0) {
        const persistentWidth = persistentVotes.length * voteWidthPx(PERSISTENT_VOTE_BYTES);
        const nonPersistentWidth = displayedNonPersistent.length * voteWidthPx(NONPERSISTENT_VOTE_BYTES);
        const totalVoteWidth = persistentWidth + nonPersistentWidth;
        const voteArea = totalVoteWidth * VOTE_RECT_HEIGHT;
        const certificateArea = voteArea * (certBytes / totalVotesBytes);
        if (certificateArea > 0 && Number.isFinite(certificateArea)) {
            const minWidth = 12;
            const minHeight = VOTE_RECT_HEIGHT;
            const maxWidth = totalVoteWidth > 0 ? totalVoteWidth : null;

            let width = Math.sqrt(certificateArea);
            if (maxWidth && width > maxWidth) {
                width = maxWidth;
            }
            width = Math.max(minWidth, width);

            let height = certificateArea / width;

            if (height < minHeight) {
                height = minHeight;
                width = certificateArea / height;
                if (maxWidth && width > maxWidth) {
                    width = maxWidth;
                    height = certificateArea / width;
                }
            }

            if (!Number.isFinite(width) || width <= 0 || !Number.isFinite(height) || height <= 0) {
                width = Math.max(minWidth, Math.sqrt(Math.max(certificateArea, 1)));
                if (maxWidth && width > maxWidth) {
                    width = maxWidth;
                }
                height = certificateArea / width;
            }

            const widthPx = Math.max(1, width);
            const heightPx = Math.max(1, height);
            const widthStr = `${widthPx.toFixed(1)}px`;
            cert.style.width = widthStr;
            cert.style.minWidth = widthStr;
            cert.style.height = `${heightPx.toFixed(1)}px`;
        } else {
            cert.style.height = "110px";
            cert.style.width = "150px";
        }
    } else {
        cert.style.height = "110px";
        cert.style.width = "150px";
    }

    const certificateTooltip = [];
    const eid = demo?.certificate?.eid ?? demo?.identifiers?.eid;
    const eb = demo?.certificate?.eb_hash ?? demo?.identifiers?.eb_hash;
    const signer = demo?.certificate?.signer;
    if (signer) certificateTooltip.push(`<b>Signer:</b> ${signer}`);
    if (eid) certificateTooltip.push(`<b>EID:</b> ${eid}`);
    if (eb) certificateTooltip.push(`<b>EB hash:</b> ${eb}`);
    if (certBytes !== null) certificateTooltip.push(`<b>Size:</b> ${formatBytes(certBytes)}`);
    if (certificateTooltip.length) {
        attachTooltip(cert, certificateTooltip.join('<br>'));
    }

    latestCertificateRender = {
        width: cert.style.width || "",
        minWidth: cert.style.minWidth || "",
        height: cert.style.height || "",
        tooltipHtml: certificateTooltip.length ? certificateTooltip.join('<br>') : null
    };
    updateVerificationCertificate();

    container.appendChild(votesGrid);
    container.appendChild(arrow);
    container.appendChild(cert);
}

// ---------- data loading ----------
function getRunFromURL() {
    const p = new URLSearchParams(window.location.search);
    const run = p.get("run");
    // No default fallback here. Only accept valid runX format or null.
    return run && /^run\d+$/i.test(run) ? run : null;
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

async function tryFetchText(url) {
    try {
        const r = await fetch(url, { cache: "no-store" });
        if (!r.ok) return null;
        return (await r.text()).trim();
    } catch {
        return null;
    }
}

// Loads demo JSON for a specific run directory (runDir: string)
async function loadDemoJson(runDir) {
    if (!runDir || typeof runDir !== "string") return null;

    const data = await tryFetchJson(`/demo/${runDir}`);
    if (!data) return null;

    if (!data.identifiers) {
        const [eid, eb] = await Promise.all([
            tryFetchText(`/demo/${runDir}/eid.txt`),
            tryFetchText(`/demo/${runDir}/ebhash.txt`)
        ]);
        data.identifiers = {
            eid: eid || null,
            eb_hash: eb || null
        };
    }
    return data;
}

async function loadTimingsForRun(runDir) {
    if (!runDir || typeof runDir !== "string") {
        setText("committee_timing", "—");
        setText("voting_timing", "—");
        setText("voting_timing_avg", "—");
        setText("agg_timing", "—");
        setText("verify_time", "—");
        setText("verify_status", "—");
        applyVerificationStatus(null);
        return null;
    }
    const timings = await tryFetchJson(`/demo/${runDir}/timings.json`);
    if (timings && typeof timings === "object") {
        const committeeFormatted = formatDuration(timings.committee_selection_ms);
        const votingFormatted = formatDuration(timings.vote_casting_ms);
        const aggregationFormatted = formatDuration(timings.aggregation_ms);
        const verificationFormatted = formatDuration(timings.verification_ms);
        setText("committee_timing", committeeFormatted ?? "—");
        setText("voting_timing", votingFormatted ?? "—");
        setText("agg_timing", aggregationFormatted ?? "—");
        setText("verify_time", verificationFormatted ?? "—");
        const totalVoters = Number(latestDisplayedVoterCount);
        let avgText = "—";
        if (Number.isFinite(totalVoters) && totalVoters > 0) {
            const totalMs = Number(timings.vote_casting_ms);
            if (Number.isFinite(totalMs) && totalMs >= 0) {
                const avgMs = totalMs / totalVoters;
                if (avgMs < 1000) {
                    const precision = avgMs < 10 ? 2 : 1;
                    avgText = `${avgMs.toFixed(precision)} ms`;
                } else {
                    avgText = formatDuration(avgMs) ?? "—";
                }
            }
        }
        setText("voting_timing_avg", avgText);
        const statusSource = latestVerificationStatus ?? timings.verification_status ?? null;
        applyVerificationStatus(statusSource);
    } else {
        setText("committee_timing", "—");
        setText("voting_timing", "—");
        setText("voting_timing_avg", "—");
        setText("agg_timing", "—");
        setText("verify_time", "—");
        applyVerificationStatus(null);
    }
    return timings ?? null;
}

function fillIdentifiers(obj) {
    if (!obj) return;
    const eid = obj.eid || obj.EID;
    const eb = obj.eb_hash || obj.eb || obj.EB || obj.ebHash;
    if (eid) {
        setText("eid", eid);
    }
    if (eb) {
        setText("eb", eb);
    }
}

function applyEnvironmentInfo(environment) {
    const container = document.getElementById("demo_meta");
    const summaryEl = document.getElementById("machine_summary");

    if (!container || !summaryEl) return;

    const hasEnvironment = environment && typeof environment === "object";

    if (!hasEnvironment) {
        summaryEl.textContent = "—";
        container.hidden = true;
        return;
    }

    const parts = [];
    if (environment.os && environment.architecture) {
        parts.push(`${environment.os} (${environment.architecture})`);
    } else if (environment.os) {
        parts.push(environment.os);
    } else if (environment.architecture) {
        parts.push(environment.architecture);
    }

    if (environment.cpu_count !== undefined && environment.cpu_count !== null) {
        const cores = Number(environment.cpu_count);
        if (Number.isFinite(cores) && cores > 0) {
            parts.push(`${cores} ${cores === 1 ? "core" : "cores"}`);
        }
    }

    if (environment.memory_bytes !== undefined && environment.memory_bytes !== null) {
        const memoryBytes = Number(environment.memory_bytes);
        if (Number.isFinite(memoryBytes) && memoryBytes > 0) {
            parts.push(`${formatBytes(memoryBytes)} RAM`);
        }
    }

    if (!parts.length) {
        summaryEl.textContent = "—";
        container.hidden = true;
        return;
    }

    summaryEl.textContent = parts.join(" • ");
    container.hidden = false;
}

const FLOW_STEPS = [
    {
        wrapperId: "step_committee",
        buttonId: "btn_step_committee",
        targetId: "committee",
        nextWrapperId: "step_election"
    },
    {
        wrapperId: "step_election",
        buttonId: "btn_step_election",
        targetId: "identifiers",
        nextWrapperId: "step_voting"
    },
    {
        wrapperId: "step_voting",
        buttonId: "btn_step_voting",
        targetId: "voters",
        nextWrapperId: "step_aggregation"
    },
    {
        wrapperId: "step_aggregation",
        buttonId: "btn_step_aggregation",
        targetId: "aggregation",
        nextWrapperId: "step_verification"
    },
    {
        wrapperId: "step_verification",
        buttonId: "btn_step_verification",
        targetId: "verification",
        nextWrapperId: null
    }
];

let progressiveRevealInitialized = false;

function handleFlowButtonClick(step) {
    if (!step) return;
    const target = document.getElementById(step.targetId);
    if (target) {
        target.classList.remove("is-hidden");
        requestAnimationFrame(() => {
            target.scrollIntoView({ behavior: "smooth", block: "start" });
        });
    }
    const wrapper = document.getElementById(step.wrapperId);
    if (wrapper) wrapper.classList.add("is-hidden");
    if (step.nextWrapperId) {
        const nextWrapper = document.getElementById(step.nextWrapperId);
        if (nextWrapper) nextWrapper.classList.remove("is-hidden");
    }
    if (typeof syncGridColumns === "function") {
        try {
            syncGridColumns();
        } catch {
            // Ignore layout sync errors during reveal.
        }
    }
}

function resetProgressiveReveal() {
    FLOW_STEPS.forEach((step, index) => {
        const target = document.getElementById(step.targetId);
        if (target) target.classList.add("is-hidden");
        const wrapper = document.getElementById(step.wrapperId);
        if (wrapper) {
            if (index === 0) {
                wrapper.classList.remove("is-hidden");
            } else {
                wrapper.classList.add("is-hidden");
            }
        }
    });
}

function setupProgressiveReveal() {
    if (!progressiveRevealInitialized) {
        FLOW_STEPS.forEach((step) => {
            const button = document.getElementById(step.buttonId);
            if (!button) return;
            button.addEventListener("click", () => handleFlowButtonClick(step));
        });
        progressiveRevealInitialized = true;
    }
    resetProgressiveReveal();
}

// --- UI clearing helpers ---
function clearUIPlaceholders() {
    setText("universe_total", "—");
    setText("universe_persistent", "—");
    setText("universe_nonpersistent", "—");
    setText("committee_total", "—");
    setText("committee_persistent", "—");
    setText("committee_nonpersistent", "—");
    setText("committee_timing", "—");
    setText("voting_timing", "—");
    setText("voting_timing_avg", "—");
    setText("agg_timing", "—");
    setText("verify_time", "—");
    setText("verify_status", "—");
    setText("eid", "—");
    setText("eb", "—");
    setText("voters_total", "—");
    setText("voters_persistent", "—");
    setText("voters_nonpersistent", "—");
    setText('voters_quorum', '—');
    setText('agg_votes_size', '—');
    setText('agg_cert_size', '—');
    setText('agg_gain', '—');
    setText("machine_summary", "—");
    const metaEl = document.getElementById("demo_meta");
    if (metaEl) metaEl.hidden = true;
    // Clear main panels
    const clearIds = ["universe_canvas", "committee_canvas", "voters_canvas", "aggregation_canvas"];
    for (const id of clearIds) {
        const el = document.getElementById(id);
        if (el) el.innerHTML = "";
    }
    latestDisplayedVoterCount = null;
    latestCertificateRender = null;
    updateVerificationCertificate();
    applyVerificationStatus(null);
    resetProgressiveReveal();
}

// --- Data loading and rendering sequence for a given runDir ---
async function loadAndRenderRun(runDir) {
    clearUIPlaceholders();
    if (!runDir || typeof runDir !== "string") {
        renderUniverse([]);
        return;
    }
    const demo = await loadDemoJson(runDir);
    if (demo) {
        const universe = demo.universe || demo;
        renderUniverse(universe);
        fillIdentifiers(demo.identifiers);
        fillIdentifiers(demo.certificate);
        renderCommitteeFromDemo(demo);
        renderVotersFromDemo(demo);
        renderAggregationFromDemo(demo);
        applyEnvironmentInfo(demo?.environment ?? null);
        applyVerificationStatus(demo?.verification?.status ?? demo?.verification_status ?? null);
        const timings = await loadTimingsForRun(runDir);
        syncGridColumns();
        window.addEventListener("resize", syncGridColumns);
    } else {
        renderUniverse([]);
    }
}

// --- Boot logic: only auto-load if localStorage has lastRun ---
document.addEventListener("DOMContentLoaded", () => {
    clearUIPlaceholders();
    setupProgressiveReveal();

    // Setup form submission for run directory selection
    const form = document.getElementById("run-form");
    if (form) {
        form.addEventListener("submit", async (e) => {
            e.preventDefault();
            const input = form.querySelector("input[name='run']") || document.getElementById("run-input");
            if (!input) return;
            let runDir = input.value.trim();
            // Accept only runX format (e.g., run64, run5, etc.)
            if (!/^run\d+$/i.test(runDir)) {
                alert("Please enter a valid run directory (e.g., run64).");
                input.focus();
                return;
            }
            // Save last used run to localStorage
            localStorage.setItem("lastRun", runDir);
            await loadAndRenderRun(runDir);
        });
    }

    // Prefer run from URL param if present (e.g., /ui?run=run100)
    const runFromURL = getRunFromURL();
    if (runFromURL) {
        const inputUrl = document.querySelector("#run-form input[name='run']") || document.getElementById("run-input");
        if (inputUrl) inputUrl.value = runFromURL;
        localStorage.setItem("lastRun", runFromURL);
        loadAndRenderRun(runFromURL);
        return; // skip other auto-loading
    }

    // If localStorage has lastRun, auto-load it; else wait for user input
    const lastRun = localStorage.getItem("lastRun");
    if (lastRun && /^run\d+$/i.test(lastRun)) {
        // Optionally set the input field, if present
        const input = document.querySelector("#run-form input[name='run']") || document.getElementById("run-input");
        if (input) input.value = lastRun;
        loadAndRenderRun(lastRun);
    }
    // else: UI remains in cleared state, waiting for user to submit run directory
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
        const current = (el.textContent || "").trim();
        const stored = el.getAttribute('data-full');
        const full = current || stored || "";
        const next = truncate ? shortenMiddle(full, keepStart, keepEnd) : full;

        if (stored !== full) {
            el.setAttribute('data-full', full);
        }
        if (!el.classList.contains('mono')) {
            el.classList.add('mono');
        }
        el.title = full;
        if (el.textContent !== next) {
            el.textContent = next;
        }
    };
    const mo = new MutationObserver(apply);
    mo.observe(el, { childList: true, characterData: true, subtree: true });
    apply();
}

document.addEventListener('DOMContentLoaded', () => {
    watchAndEllipsize('eid', { truncate: false });
    watchAndEllipsize('eb', { keepStart: 26, keepEnd: 22, truncate: true });
});
