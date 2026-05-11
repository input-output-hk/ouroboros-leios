#!/usr/bin/env node
// Regenerate schema/trace.ui.schema.json and schema/ui-message-types.json
// from schema/trace.ui.d.ts. Run via `npm run gen:schema`.

import { execFileSync } from "node:child_process";
import { writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import prettier from "prettier";

const here = dirname(fileURLToPath(import.meta.url));
const source = resolve(here, "trace.ui.d.ts");
const schemaPath = resolve(here, "trace.ui.schema.json");
const typesPath = resolve(here, "ui-message-types.json");

const tjs = (typeName) =>
    execFileSync(
        "typescript-json-schema",
        ["--required", "--strictNullChecks", source, typeName],
        { encoding: "utf8", maxBuffer: 64 * 1024 * 1024 },
    );

const schema = await prettier.format(tjs("UITraceEvents"), { parser: "json" });
writeFileSync(schemaPath, schema);

const messageTypeSchema = JSON.parse(tjs("UIMessageType"));
const types = await prettier.format(
    JSON.stringify(messageTypeSchema.enum),
    { parser: "json" },
);
writeFileSync(typesPath, types);

console.log(`Wrote ${schemaPath}`);
console.log(`Wrote ${typesPath}`);
