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
  documentationSidebar: ["roadmap", "strategy", "resources", "faq", "glossary"],
  developmentSidebar: [
    {
      type: "category",
      label: "Research and Development",
      items: [
        "development/overview",
        "development/throughput-simulation",
        "development/simulation-demonstration",
        "development/cost-estimator",
        {
          type: "link",
          href: "https://leios.cardano-scaling.org/visualizer",
          label: "Visualizer",
        },
      ],
    },
    "development/monthly-reviews",
    {
      type: "link",
      href: "https://leios.cardano-scaling.org/leios-design.pdf",
      label: "Technical Design",
    },
  ],
};

export default sidebars;
