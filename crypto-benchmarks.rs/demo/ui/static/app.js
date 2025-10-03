async function fetchCert(run) {
    const res = await fetch(`/cert/${encodeURIComponent(run)}`);
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    return res.json();
}

function setText(id, text) {
    const el = document.getElementById(id);
    if (el) el.textContent = text ?? "—";
}

function fillTable(tableId, data) {
    const tbody = document.querySelector(`#${tableId} tbody`);
    if (!tbody) return;
    tbody.innerHTML = "";
    data.forEach((id, i) => {
        const tr = document.createElement("tr");
        const idx = document.createElement("td");
        idx.textContent = i + 1;
        const val = document.createElement("td");
        val.textContent = id;
        tr.append(idx, val);
        tbody.appendChild(tr);
    });
}

function firstAvailableList(full, sample) {
    if (Array.isArray(full) && full.length) return { list: full, sampled: false };
    if (Array.isArray(sample) && sample.length) return { list: sample, sampled: true };
    return { list: [], sampled: false };
}

function shortenHex(hex, head = 20, tail = 20) {
    if (!hex || typeof hex !== "string") return hex;
    const clean = hex.trim();
    if (clean.length <= head + tail) return clean;
    return clean.slice(0, head) + "…" + clean.slice(-tail);
}

function formatBytes(n) {
    if (typeof n !== "number") return n ?? "—";
    return n.toLocaleString() + " B";
}

async function load(run) {
    try {
        const data = await fetchCert(run);

        setText("eid", shortenHex(data.eid));
        const ebElem = document.getElementById("eb");
        ebElem.textContent = shortenHex(data.eb);
        ebElem.title = data.eb || "";

        setText("votes_bytes", formatBytes(data.votes_bytes));
        setText("certificate_bytes", formatBytes(data.certificate_bytes));
        setText("compression_ratio", data.compression_ratio);

        setText("pv_count", data.persistent_voters_count);
        setText("npv_count", data.nonpersistent_voters_count);

        const pv = firstAvailableList(data.persistent_voters, data.persistent_voters_sample);
        const npv = firstAvailableList(data.nonpersistent_voters, data.nonpersistent_voters_sample);

        fillTable("pv_table", pv.list);
        fillTable("npv_table", npv.list);

        document.getElementById("pv_note").hidden = !pv.sampled;
        document.getElementById("npv_note").hidden = !npv.sampled;
    } catch (e) {
        alert(`Failed to load certificate for ${run}: ${e.message}`);
    }
}

document.getElementById("run-form").addEventListener("submit", (e) => {
    e.preventDefault();
    const run = document.getElementById("run-input").value.trim();
    if (run) load(run);
});

// auto-load default
load(document.getElementById("run-input").value.trim());