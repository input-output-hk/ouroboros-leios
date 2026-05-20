import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import { fileURLToPath } from "url";

const __dirname = fileURLToPath(new URL(".", import.meta.url));

export default defineConfig({
  plugins: [react()],
  server: {
    port: 3001,
    proxy: {
      "/api": "http://127.0.0.1:9100",
    },
  },
  resolve: {
    alias: [{ find: "@", replacement: __dirname + "src" }],
  },
});
