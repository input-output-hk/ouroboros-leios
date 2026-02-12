import useDocusaurusContext from "@docusaurus/useDocusaurusContext";
import Layout from "@theme/Layout";
import React from "react";

export default function Home(): React.ReactElement {
  const { siteConfig } = useDocusaurusContext();
  return (
    <Layout
      title={siteConfig.title}
      description="A high-throughput protocol for Cardano"
    >
      <main
        style={{
          height: "calc(100vh - var(--ifm-navbar-height))",
          overflow: "hidden",
        }}
      >
        <iframe
          src="https://engineering.iog.io/leios"
          title="Leios"
          style={{
            width: "100%",
            height: "100%",
            border: "none",
          }}
        />
      </main>
    </Layout>
  );
}
