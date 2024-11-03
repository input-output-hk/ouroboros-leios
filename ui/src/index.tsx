import { createRoot } from "react-dom/client";
import { App } from "./App";

import "./index.css";

const el = document.querySelector("#app");
if (el) {
    const root = createRoot(el);
    root.render(<App />)
}