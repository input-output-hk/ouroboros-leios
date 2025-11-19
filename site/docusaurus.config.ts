import type * as Preset from "@docusaurus/preset-classic";
import type { Config } from "@docusaurus/types";
import { themes as prismThemes } from "prism-react-renderer";

const config: Config = {
  title: "Ouroboros Leios",
  tagline: "A high-throughput protocol for Cardano",
  favicon: "img/favicon.ico",

  // Set the production url of your site here
  url: "https://leios.cardano-scaling.org/",
  // Set the /<baseUrl>/ pathname under which your site is served
  // For GitHub pages deployment, it is often '/<projectName>/'
  baseUrl: "/",

  // GitHub pages deployment config.
  // If you aren't using GitHub pages, you don't need these.
  organizationName: "input-output-hk", // Usually your GitHub org/user name.
  projectName: "ouroboros-leios", // Usually your repo name.

  onBrokenLinks: "throw",
  onBrokenMarkdownLinks: "warn",

  // Even if you don't use internationalization, you can use this field to set
  // useful metadata like html lang. For example, if your site is Chinese, you
  // may want to replace "en" with "zh-Hans".
  i18n: {
    defaultLocale: "en",
    locales: ["en"],
  },

  scripts: [
    {
      src: "https://plausible.io/js/script.js",
      defer: true,
      "data-domain": "leios.cardano-scaling.org",
    },
  ],

  // Configure static file serving
  staticDirectories: ["static", "public"],

  // Configure plugins
  plugins: [],

  presets: [
    [
      "classic",
      {
        docs: {
          sidebarPath: "./sidebars.ts",
        },
        blog: {
          path: "news/",
          routeBasePath: "news",
          blogTitle: "News",
          blogSidebarTitle: "Weekly updates",
          sortPosts: "descending",
          showReadingTime: true,
          authorsMapPath: "../authors.yaml",
        },
        theme: {
          customCss: "./src/css/custom.css",
        },
      } satisfies Preset.Options,
    ],
  ],

  themeConfig: {
    metadata: [
      {
        name: "description",
        content:
          "Ouroboros Leios is a high-throughput protocol designed to scale Cardano by optimizing transaction processing and network resource utilization.",
      },
    ],
    image: "img/social-preview.jpg",
    navbar: {
      logo: {
        alt: "Leios Logo",
        src: "img/logo.svg",
        srcDark: "img/logo-dark.svg",
      },
      items: [
        {
          type: "docSidebar",
          sidebarId: "documentationSidebar",
          position: "right",
          label: "Documentation",
        },
        {
          type: "docSidebar",
          sidebarId: "developmentSidebar",
          position: "right",
          label: "Development",
        },
        {
          to: "/formal-spec/",
          label: "Formal Specification",
          position: "right",
        },
        { to: "/docs/roadmap", label: "Roadmap", position: "right" },
        { to: "/news", label: "Weekly updates", position: "right" },
        {
          type: "dropdown",
          label: "Tools",
          position: "right",
          items: [
            {
              href: "https://www.insightmaker.com/insight/4DU4kmFVCFDaq30ux29PCe/Cardano-Throughput-v0-3",
              label: "Simulator",
            },
            {
              to: "https://leios.cardano-scaling.org/cost-estimator/",
              label: "Cost Estimator",
            },
            {
              to: "/traffic-estimator",
              label: "Traffic Estimator",
            },
            {
              to: "https://leios.cardano-scaling.org/visualizer",
              label: "Visualizer",
            },
          ],
        },
        {
          href: "https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md",
          label: "CIP",
          position: "right",
        },
        {
          href: "https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md",
          label: "CPS",
          position: "right",
        },
        {
          href: "https://github.com/input-output-hk/ouroboros-leios",
          html: `
    <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none">
      <mask id="mask0_6560_292" style="mask-type:alpha" maskUnits="userSpaceOnUse" x="0" y="0" width="24" height="24">
        <rect width="24" height="24" fill="currentColor"/>
      </mask>
      <g mask="url(#mask0_6560_292)">
        <path fill-rule="evenodd" clip-rule="evenodd" d="M11.697 0.4375C5.33255 0.4375 0.1875 5.70831 0.1875 12.229C0.1875 17.4414 3.48411 21.8535 8.05739 23.4151C8.62916 23.5325 8.8386 23.1614 8.8386 22.8492C8.8386 22.5759 8.81975 21.6389 8.81975 20.6626C5.61809 21.3655 4.95137 19.2569 4.95137 19.2569C4.43684 17.8904 3.67447 17.5391 3.67447 17.5391C2.62656 16.8168 3.7508 16.8168 3.7508 16.8168C4.9132 16.8949 5.52314 18.0272 5.52314 18.0272C6.55197 19.8231 8.20981 19.3156 8.87677 19.0032C8.97195 18.2418 9.27704 17.7147 9.60097 17.422C7.04741 17.1486 4.36074 16.1335 4.36074 11.6042C4.36074 10.3157 4.81779 9.26156 5.54199 8.44171C5.42773 8.14894 5.02746 6.93833 5.65649 5.31803C5.65649 5.31803 6.6283 5.00562 8.81952 6.5284C9.75766 6.27029 10.7251 6.13899 11.697 6.13788C12.6688 6.13788 13.6595 6.27468 14.5743 6.5284C16.7657 5.00562 17.7375 5.31803 17.7375 5.31803C18.3666 6.93833 17.9661 8.14894 17.8518 8.44171C18.5951 9.26156 19.0333 10.3157 19.0333 11.6042C19.0333 16.1335 16.3466 17.129 13.774 17.422C14.1933 17.7928 14.5552 18.4955 14.5552 19.6084C14.5552 21.1896 14.5363 22.4587 14.5363 22.849C14.5363 23.1614 14.746 23.5325 15.3176 23.4154C19.8908 21.8533 23.1874 17.4414 23.1874 12.229C23.2063 5.70831 18.0424 0.4375 11.697 0.4375Z" fill="currentColor"/>
      </g>
    </svg>
  `,
          position: "right",
        },
      ],
    },
    footer: {
      logo: {
        alt: "Leios Logo",
        src: "img/logo-footer.svg",
        srcDark: "img/logo-footer.svg",
      },
      links: [
        {
          title: "Docs",
          items: [
            {
              label: "Formal Specification",
              to: "/formal-spec/",
            },
            {
              label: "Resources",
              to: "/docs/resources",
            },
            {
              label: "FAQs",
              to: "/docs/faq",
            },
            {
              label: "Glossary",
              to: "/docs/glossary",
            },
          ],
        },
        {
          title: "Community",
          items: [
            {
              label: "Monthly review meetings",
              to: "/docs/development/monthly-reviews",
            },
            {
              label: "GitHub Discussions",
              href: "https://github.com/input-output-hk/ouroboros-leios/discussions",
            },
          ],
        },
        {
          title: "Legal",
          items: [
            {
              label: "Terms & Conditions",
              to: "https://static.iohk.io/terms/iohktermsandconditions.pdf",
            },
            {
              label: "Privacy Policy",
              to: "https://static.iohk.io/terms/iog-privacy-policy.pdf",
            },
            {
              label: "Contributors",
              to: "https://github.com/input-output-hk/ouroboros-leios/graphs/contributors",
            },
          ],
        },
        {
          title: "More resources",
          items: [
            {
              label: "IOHK research library",
              to: "https://iohk.io/en/research/library/",
            },
            {
              label: "Essential Cardano",
              to: "https://www.essentialcardano.io/",
            },
            {
              label: "Cardano Docs",
              to: "https://docs.cardano.org/",
            },
          ],
        },
      ],
      copyright: `Copyright © ${new Date().getFullYear()} IOG, Inc`,
    },
    prism: {
      theme: prismThemes.github,
      darkTheme: prismThemes.dracula,
    },
    socials: {
      github: "https://github.com/input-output-hk/ouroboros-leios",
      discord: "https://discord.gg/83aXYxy9",
    },
  } satisfies Preset.ThemeConfig,
};

export default config;
