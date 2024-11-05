import { parse } from "@iarna/toml";
import fs from "fs/promises";
import path from "path";

const fileContents = await fs.readFile(path.resolve(__dirname, "../../../../", "sim-rs/test_data", "simple.toml"), "utf-8");
await fs.writeFile(`${__dirname}/nodes.json`, JSON.stringify(parse(fileContents), (k, v) => typeof v === "bigint" ? Number(v.toString()) : v), "utf-8");