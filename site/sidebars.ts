import type { SidebarsConfig } from "@docusaurus/plugin-content-docs";

/**
 * Creating a sidebar enables you to:
 - create an ordered group of docs
 - render a sidebar for each doc of that group
 - provide next/previous navigation

 The sidebars can be generated from the filesystem, or explicitly defined here.

 Create as many sidebars as you want.
 */
const sidebars: SidebarsConfig = {
  documentationSidebar: [
    "what-is-leios",
    "leios-use-cases",
    "roadmap",
    "resources",
    "monthly-reviews",
    "faq",
    "glossary",
  ],
  developmentSidebar: [
    {
      type: "category",
      label: "Research and development",
      items: [
        "development/overview",
        "development/throughput-simulation",
        "development/simulation-demonstration",
      ],
    },
  ],
  developmentMaterialSidebar: [
    {
      type: "category",
      label: "Development",
      collapsed: false,
      link: { type: "doc", id: "development/index" },
      items: [
        "development/status",
        "parameter-graduation",
        "development/benchmark-reports",
        "development/cost-estimator",
      ],
    },
  ],
  testnetSidebar: [
    {
      type: "category",
      label: "Testnet",
      collapsed: false,
      items: [
        "testnet/getting-started",
        "testnet/register-stake-pool",
        "testnet/rewards-program",
        "testnet/rewards-2026-jul-sep",
      ],
    },
  ],
};

export default sidebars;
