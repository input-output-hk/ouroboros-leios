// ---- utilities -------------------------------------------------------------

async function fetchJSON(url) {
    const r = await fetch(url);
    if (!r.ok) throw new Error(`${url} -> HTTP ${r.status}`);
    return r.json();
}
const $ = (id) => document.getElementById(id);

function setText(id, txt) {
    const el = $(id);
    if (el) el.textContent = txt ?? "—";
}

function setHidden(id, hidden) {
    const el = $(id);
    if (el) el.hidden = !!hidden;
}

function showError(msg) {
    const banner = $("error_banner");
    const text = $("error_text");
    if (banner) banner.hidden = !msg;
    if (text) text.textContent = msg || "";
}

function clearError() {
    showError("");
}

// Build a <li>text</li> and replace list content
function fillList(ulId, items) {
    const ul = $(ulId);
    if (!ul) return;
    ul.innerHTML = "";
    items.forEach((t) => {
        const li = document.createElement("li");
        li.textContent = t;
        ul.appendChild(li);
    });
}

function shortenHex(hex, head = 14, tail = 14) {
    if (!hex || typeof hex !== "string") return hex;
    const s = hex.trim();
    if (s.length <= head + tail) return s;
    return s.slice(0, head) + "…" + s.slice(-tail);
}

function formatBytes(n) {
    if (typeof n !== "number") return n ?? "—";
    return n.toLocaleString() + " B";
}

// Build a <tr><td>…</td>…</tr>
function tr(cells) {
    const tr = document.createElement("tr");
    cells.forEach((v) => {
        const td = document.createElement("td");
        td.textContent = v;
        tr.appendChild(td);
    });
    return tr;
}

// Replace tbody contents
function fillTbody(tbodyId, rows) {
    const tb = $(tbodyId);
    if (!tb) return;
    tb.innerHTML = "";
    rows.forEach((cells) => tb.appendChild(tr(cells)));
}

// Render persistent committee (if present)
function renderPersistent(committee) {
    const pcs = committee?.persistent_committee ?? [];
    const rows = pcs.map((e, i) => {
        // each entry: { persistent_id, pool_id, stake }
        const pid = (typeof e === "object" ? e.persistent_id : undefined);
        const pool = (typeof e === "object" ? e.pool_id : e);
        const stake = (typeof e === "object" ? e.stake : undefined);
        return [String(i + 1), (pid ?? "—"), shortenHex(pool ?? ""), stake ?? ""];
    });

    // header count
    const count = committee?.persistent_count ?? pcs.length ?? 0;
    setText("persistent_title_count", String(count || "0"));
    fillTbody("persistent_tbody", rows);

    // note text (shown only if no persistent seats)
    const hasPersistent = (count > 0);
    setHidden("persistent_note", hasPersistent);
}

// ---- renderers -------------------------------------------------------------

function renderSummary(cert) {
    setText("eid", cert?.eid ? shortenHex(cert.eid) : "—");
    const ebEl = $("eb");
    if (ebEl) {
        ebEl.textContent = cert?.eb ? shortenHex(cert.eb, 18, 18) : "—";
        ebEl.title = cert?.eb ?? "";
    }
    setText("votes_bytes", formatBytes(cert?.votes_bytes));
    setText("certificate_bytes", formatBytes(cert?.certificate_bytes));
    setText("compression_ratio", cert?.compression_ratio ?? "—");
}

function renderSelectedPools(committee) {
    const rows = [];
    const pools = committee?.selected_pools ?? [];

    pools.forEach((p, i) => {
        // Accept both object and string
        if (typeof p === "string") {
            rows.push([String(i + 1), shortenHex(p), ""]);
        } else {
            const pid = p.pool_id || p.id || p.voter_id || "";
            const stake = (p.stake ?? "") === "" ? "" : String(p.stake);
            rows.push([String(i + 1), shortenHex(pid), stake]);
        }
    });

    // header count
    const count = committee?.selected_count ?? pools.length ?? 0;
    setText("selected_title_count", String(count || "—"));

    fillTbody("selected_tbody", rows);
}

function renderElected(committee, votesFallback) {
    // Prefer enriched committee.elected (objects). Fall back to /votes.
    let elected = committee?.elected;
    if (!Array.isArray(elected) || elected.length === 0) {
        elected = votesFallback?.elected ?? [];
    }

    const rows = elected.map((e, i) => {
        if (typeof e === "string") {
            return [String(i + 1), shortenHex(e), ""];
        } else {
            const id = e.voter_id || e.id || "";
            const t = e.type || "";
            return [String(i + 1), shortenHex(id), t];
        }
    });

    const count =
        committee?.elected_count ??
        (Array.isArray(elected) ? elected.length : 0);
    setText("elected_title_count", String(count || "—"));

    fillTbody("elected_tbody", rows);
}

function renderNotes(committee) {
    // Note list
    const notes = Array.isArray(committee?.notes) ? committee.notes : [];
    fillList("notes_ul", notes);

    // If any note looks like an error, surface it.
    const err = notes.find((n) => typeof n === "string" && /^error/i.test(n));
    if (err) {
        showError(err);
    } else {
        clearError();
    }
}

function renderVoters(cert) {
    // persistent
    const pv = cert?.persistent_voters ?? cert?.persistent_voters_sample ?? [];
    const pvRows = pv.map((id, i) => [String(i + 1), shortenHex(id)]);
    setText("pv_count", String(pv.length || 0));
    fillTbody("pv_tbody", pvRows);

    // non-persistent
    const npv =
        cert?.nonpersistent_voters ??
        cert?.nonpersistent_voters_sample ??
        [];
    const npvRows = npv.map((id, i) => [String(i + 1), shortenHex(id)]);
    setText("npv_count", String(npv.length || 0));
    fillTbody("npv_tbody", npvRows);

    // “(sample)” badges
    $("pv_note") && ($("pv_note").hidden = Array.isArray(cert?.persistent_voters) && cert.persistent_voters.length > 0);
    $("npv_note") && ($("npv_note").hidden = Array.isArray(cert?.nonpersistent_voters) && cert.nonpersistent_voters.length > 0);
}

// ---- main load ------------------------------------------------------------

async function load(run) {
    try {
        // Force-refresh the pretty file (all=1 gives full voters if available)
        const [cert, committee, votes] = await Promise.all([
            fetchJSON(`/cert/${encodeURIComponent(run)}?all=1`),
            fetchJSON(`/committee/${encodeURIComponent(run)}`),
            fetchJSON(`/votes/${encodeURIComponent(run)}`)
        ]);

        renderSummary(cert);
        renderSelectedPools(committee);
        renderElected(committee, votes);
        renderVoters(cert);
        renderPersistent(committee);
        renderNotes(committee);
    } catch (err) {
        showError(`Failed to load data for ${run}: ${err.message}`);
        console.error(err);
    }
}

// ---- hooks ---------------------------------------------------------------

document.getElementById("run-form").addEventListener("submit", (e) => {
    e.preventDefault();
    const run = document.getElementById("run-input").value.trim();
    if (run) load(run);
});

// initial load
load(document.getElementById("run-input").value.trim() || "run32");