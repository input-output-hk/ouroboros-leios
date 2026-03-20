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
            to: "/docs/monthly-reviews",
          },
          // Strategy integrated with roadmap (2026-03-13)
          {
            from: "/docs/strategy",
            to: "/docs/roadmap",
          },
          // Monthly reviews moved to top-level (2026-03-13)
          {
            from: "/docs/development/monthly-reviews",
            to: "/docs/monthly-reviews",
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
          label: "About Leios",
        },
        {
          type: "docSidebar",
          sidebarId: "developmentSidebar",
          position: "right",
          label: "Research and development",
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
              label: "Mempool visualizer",
            },
            {
              href: "https://www.insightmaker.com/insight/4DU4kmFVCFDaq30ux29PCe/Cardano-Throughput-v0-3",
              label: "Throughput model",
            },
          ],
        },
        {
          href: "https://discord.gg/83aXYxy9",
          html: `
    <svg xmlns="http://www.w3.org/2000/svg" width="24" height="18" viewBox="0 0 24 18" fill="none">
<path d="M20.3216 1.50051C18.7491 0.789438 17.0856 0.285036 15.3753 0.000674983C15.1663 0.375295 14.9106 0.878164 14.7399 1.27573C12.9367 1.00961 11.1022 1.00961 9.29895 1.27573C9.09542 0.83893 8.86774 0.413069 8.61691 0C6.90459 0.285743 5.23895 0.790313 3.6636 1.50051C0.86109 5.44837 -0.398512 10.2343 0.110585 15.0003C1.94696 16.3338 4.00803 17.3487 6.20226 18C6.6919 17.3421 7.12683 16.6476 7.50294 15.9231C6.7814 15.6646 6.08674 15.3405 5.42826 14.9551C5.59825 14.835 5.76127 14.7081 5.92289 14.5731C7.81506 15.4602 9.88987 15.921 11.9919 15.921C14.094 15.921 16.1688 15.4602 18.061 14.5731C18.2233 14.7081 18.3863 14.835 18.5563 14.9551C17.9078 15.3388 17.2237 15.6628 16.513 15.9231C16.8858 16.6493 17.3206 17.344 17.8129 18C20.0024 17.3481 22.0585 16.3331 23.89 15.0003C24.3986 10.2321 23.1336 5.44465 20.3216 1.50051ZM8.0136 12.27C7.40424 12.2277 6.83663 11.9544 6.4338 11.5094C6.03098 11.0644 5.82538 10.4835 5.86159 9.89268C5.82118 9.29933 6.02487 8.71462 6.42813 8.26636C6.83139 7.81809 7.40141 7.54275 8.0136 7.50051C8.62426 7.54111 9.19369 7.81361 9.59811 8.25878C10.0025 8.70395 10.2092 9.2858 10.1733 9.87783C10.2136 10.4724 10.0089 11.0581 9.604 11.5066C9.19912 11.9551 8.62715 12.2296 8.0136 12.27ZM15.9863 12.27C15.3755 12.2296 14.806 11.9571 14.4016 11.5119C13.9971 11.0667 13.7905 10.4847 13.8266 9.89268C13.7863 9.29813 13.991 8.71236 14.3959 8.26388C14.8008 7.81541 15.3727 7.54087 15.9863 7.50051C16.5958 7.54263 17.1635 7.81582 17.5665 8.26084C17.9695 8.70586 18.1752 9.28685 18.139 9.87783C18.1792 10.4712 17.9753 11.0559 17.572 11.5042C17.1686 11.9524 16.5985 12.2278 15.9863 12.27Z" fill="currentColor"/>
</svg>
  `,
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
              label: "Formal specification",
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
              label: "Overview",
              to: "/docs/development/overview",
            },
            {
              label: "Throughput simulation",
              to: "/docs/development/throughput-simulation",
            },
            {
              label: "Simulation demonstration",
              to: "/docs/development/simulation-demonstration",
            },
            {
              label: "Cost estimator",
              to: "/docs/development/cost-estimator",
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
              to: "https://github.com/input-output-hk/ouroboros-leios",
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
        label: "Cookie Policy",
        to: "https://static.iohk.io/terms/iog-cookie-policy.pdf",
      },
    ],
  } satisfies Preset.ThemeConfig,
};

export default config;
