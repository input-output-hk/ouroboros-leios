#!/usr/bin/env node
// Validate every public/traces/*.jsonl.gz against schema/trace.ui.schema.json,
// after filtering to the event types the UI actually renders (the same set
// the worker uses). Run via `npm run validate:traces`.

import Ajv from "ajv";
import { readdirSync, readFileSync } from "node:fs";
import { createReadStream } from "node:fs";
import { dirname, resolve } from "node:path";
import { createInterface } from "node:readline";
import { fileURLToPath } from "node:url";
import { createGunzip } from "node:zlib";

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, "..");
const schema = JSON.parse(
    readFileSync(resolve(here, "trace.ui.schema.json"), "utf8"),
);
const known = new Set(
    JSON.parse(readFileSync(resolve(here, "ui-message-types.json"), "utf8")),
);

const ajv = new Ajv({ allErrors: false, strict: false });
const validate = ajv.compile(schema);

const tracesDir = resolve(root, "public", "traces");
const files = readdirSync(tracesDir)
    .filter((f) => f.endsWith(".jsonl.gz"))
    .sort();

if (files.length === 0) {
    console.log(`No traces found in ${tracesDir}`);
    process.exit(0);
}

let failed = 0;
for (const file of files) {
    const filtered = [];
    const stream = createReadStream(resolve(tracesDir, file)).pipe(createGunzip());
    const rl = createInterface({ input: stream, crlfDelay: Infinity });
    for await (const line of rl) {
        if (!line) continue;
        const event = JSON.parse(line);
        if (known.has(event?.message?.type)) filtered.push(event);
    }

    const ok = validate(filtered);
    const status = ok ? "OK" : "FAIL";
    console.log(`${file.padEnd(40)} ${String(filtered.length).padStart(8)} UI events  ${status}`);
    if (!ok) {
        failed++;
        for (const err of (validate.errors ?? []).slice(0, 5)) {
            console.log(`  ${err.instancePath} ${err.message} (${err.schemaPath})`);
        }
    }
}

process.exit(failed === 0 ? 0 : 1);
