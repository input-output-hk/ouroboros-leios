import type * as Preset from "@docusaurus/preset-classic";
import type { Config } from "@docusaurus/types";
import { themes as prismThemes } from "prism-react-renderer";

const config: Config = {
  title: "Ouroboros Leios",
  tagline:
    "A high throughput protocol for Cardano. Designed to increase transaction capacity while preserving security and ecosystem compatibility.",
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
  plugins: [
    [
      "@docusaurus/plugin-client-redirects",
      {
        redirects: [
          // Weekly updates replaced by monthly reviews (2026-01-29)
          {
            from: "/news",
            to: "/docs/development/monthly-reviews",
          },
        ],
      },
    ],
  ],

  presets: [
    [
      "classic",
      {
        docs: {
          sidebarPath: "./sidebars.ts",
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
        {
          type: "dropdown",
          label: "Tools",
          position: "right",
          items: [
            // Cost Estimator and Traffic Estimator are based on parallel Leios model,
            // not Linear Leios with linked EB proposal - hidden to avoid confusion
            // {
            //   to: "https://leios.cardano-scaling.org/cost-estimator/",
            //   label: "Cost Estimator",
            // },
            // {
            //   to: "/traffic-estimator",
            //   label: "Traffic Estimator",
            // },
            {
              to: "https://leios.cardano-scaling.org/visualizer",
              label: "Visualizer",
            },
            {
              to: "https://leios.cardano-scaling.org/mempool-viz/",
              label: "Mempool Visualizer",
            },
            {
              href: "https://www.insightmaker.com/insight/4DU4kmFVCFDaq30ux29PCe/Cardano-Throughput-v0-3",
              label: "Throughput model",
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
          title: "Documentation",
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
          title: "Development",
          items: [
            {
              label: "Roadmap",
              to: "/development/roadmap",
            },
            {
              label: "Strategy",
              to: "/docs/strategy",
            },
            {
              label: "Research Variants",
              to: "/docs/development/overview",
            },
            {
              label: "Simulation Results",
              to: "/docs/development/simulation-demonstration",
            },
          ],
        },
        {
          title: "Updates",
          items: [
            {
              label: "Mempool Visualizer",
              to: "https://leios.cardano-scaling.org/mempool-viz/",
            },
            {
              label: "Throughput Simulator",
              to: "https://www.insightmaker.com/insight/4DU4kmFVCFDaq30ux29PCe/Cardano-Throughput-v0-3",
            },
          ],
        },
        {
          title: "Community",
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
              to: "https://docs.cardano.org/",
            },
          ],
        },
      ],
      copyright: `Copyright © ${new Date().getFullYear()} Input Output Global <a href="https://static.iohk.io/terms/iog-privacy-policy.pdf" target="_blank" class="footer__link-item">Privacy Policy</a> <a href="https://static.iohk.io/terms/iohktermsandconditions.pdf" target="_blank" class="footer__link-item">Terms & Conditions</a> <small>Built with Docusaurus</small>`,
    },
    prism: {
      theme: prismThemes.github,
      darkTheme: prismThemes.dracula,
    },
    socials: {
      tagline: "Join the conversation",
      items: [
        { platform: "twitter", url: "https://x.com/inputoutputHK" },
        {
          platform: "github",
          url: "https://github.com/input-output-hk/ouroboros-leios",
        },
        {
          platform: "linkedIn",
          url: "https://www.linkedin.com/company/input-output-group/posts/?feedView=all",
        },
        { platform: "facebook", url: "https://www.facebook.com/iohk.io" },
        { platform: "discord", url: "https://discord.gg/83aXYxy9" },
      ],
    },
    legal: [
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
  } satisfies Preset.ThemeConfig,
};

export default config;
