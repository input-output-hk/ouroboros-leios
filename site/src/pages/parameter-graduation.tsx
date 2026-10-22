import { useColorMode } from "@docusaurus/theme-common";
import useBaseUrl from "@docusaurus/useBaseUrl";
import Layout from "@theme/Layout";
import React, { useEffect, useRef } from "react";

// The tool is a standalone three.js page; the iframe keeps its global styles away from the site theme.
function GraduationTool(): React.ReactElement {
    const { colorMode } = useColorMode();
    const frame = useRef<HTMLIFrameElement>(null);
    const src = useBaseUrl("/tools/parameter-graduation.html");

    // The tool re-themes itself when data-theme changes on its root element.
    const syncTheme = () => {
        const root = frame.current?.contentDocument?.documentElement;
        if (root) root.setAttribute("data-theme", colorMode);
    };
    useEffect(syncTheme, [colorMode]);

    return (
        <iframe
            ref={frame}
            src={src}
            title="Leios parameter graduation plan"
            onLoad={syncTheme}
            style={{
                display: "block",
                width: "100%",
                height: "calc(100dvh - var(--ifm-navbar-height))",
                minHeight: "640px",
                border: 0,
            }}
        />
    );
}

export default function ParameterGraduation(): React.ReactElement {
    return (
        <Layout
            title="Parameter graduation"
            description="Interactive three-dimensional view of the Leios parameter graduation plan: EB size, Plutus budget and timing against the DeltaQ feasibility surface"
        >
            <main>
                <GraduationTool />
            </main>
        </Layout>
    );
}
