import type * as Preset from "@docusaurus/preset-classic";
import type { Config } from "@docusaurus/types";
import { themes as prismThemes } from "prism-react-renderer";

const config: Config = {
    title: "Ouroboros Leios",
    tagline: "A high-throughput protocol for Cardano",
    favicon: "img/wave-logo.ico",

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
        metadata: [{
            name: "description",
            content:
                "Ouroboros Leios is a high-throughput protocol designed to scale Cardano by optimizing transaction processing and network resource utilization.",
        }],
        // Replace with your project's social card
        image: "img/docusaurus-social-card.jpg",
        navbar: {
            title: "Leios",
            logo: {
                alt: "Leios Logo",
                src: "img/wave-logo.svg",
            },
            items: [
                {
                    type: "docSidebar",
                    sidebarId: "documentationSidebar",
                    position: "left",
                    label: "Documentation",
                },
                {
                    type: "docSidebar",
                    sidebarId: "developmentSidebar",
                    position: "left",
                    label: "Development",
                },
                {
                    to: "/formal-spec/",
                    label: "Formal Specification",
                    position: "left",
                },
                { to: "/news", label: "Weekly updates", position: "right" },
                {
                    type: "dropdown",
                    label: "Tools",
                    position: "right",
                    items: [
                        {
                            href:
                                "https://www.insightmaker.com/insight/4DU4kmFVCFDaq30ux29PCe/Cardano-Throughput-v0-3",
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
                    href:
                        "https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md",
                    label: "CPS",
                    position: "right",
                },
                {
                    href: "https://github.com/input-output-hk/ouroboros-leios",
                    label: "GitHub",
                    position: "right",
                },
            ],
        },
        footer: {
            links: [
                {
                    title: "Docs",
                    items: [
                        {
                            label: "What is Ouroboros Leios?",
                            to: "/docs/overview",
                        },
                        {
                            label: "Protocol overview",
                            to: "/docs/protocol-overview",
                        },
                        {
                            label: "How it works",
                            to: "/docs/how-it-works",
                        },
                        {
                            label: "Formal Specification",
                            to: "/formal-spec/",
                        },
                        {
                            label: "FAQs",
                            to: "/docs/faq",
                        },
                        {
                            label: "Glossary",
                            to: "/docs/glossary",
                        },
                        {
                            label: "Resources",
                            to: "/docs/resources",
                        },
                        {
                            label: "CPS",
                            href:
                                "https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md",
                        },
                    ],
                },
                {
                    title: "Community",
                    items: [
                        {
                            label: "Discord",
                            href: "https://discord.gg/jm3WxeYT",
                        },
                        {
                            label: "GitHub Discussions",
                            href:
                                "https://github.com/input-output-hk/ouroboros-leios/discussions",
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
            copyright: `Copyright © ${
                new Date().getFullYear()
            } <strong>Input Output Global</strong> <br/> <a href="https://static.iohk.io/terms/iog-privacy-policy.pdf" target="_blank" class="footer__link-item">Privacy Policy</a> | <a href="https://static.iohk.io/terms/iohktermsandconditions.pdf" target="_blank" class="footer__link-item">Terms & Conditions</a> <br/> <small>Built with Docusaurus</small>`,
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
