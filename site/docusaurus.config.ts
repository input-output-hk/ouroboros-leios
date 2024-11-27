import { themes as prismThemes } from 'prism-react-renderer';
import type { Config } from '@docusaurus/types';
import type * as Preset from '@docusaurus/preset-classic';

const config: Config = {
    title: 'Leios',
    tagline: 'A high-throughput protocol for Cardano',
    favicon: 'img/wave-logo.ico',

    // Set the production url of your site here
    url: 'https://leios.cardano-scaling.org/',
    // Set the /<baseUrl>/ pathname under which your site is served
    // For GitHub pages deployment, it is often '/<projectName>/'
    baseUrl: '/',

    // GitHub pages deployment config.
    // If you aren't using GitHub pages, you don't need these.
    organizationName: 'input-output-hk', // Usually your GitHub org/user name.
    projectName: 'ouroboros-leios', // Usually your repo name.

    onBrokenLinks: 'throw',
    onBrokenMarkdownLinks: 'warn',

    // Even if you don't use internationalization, you can use this field to set
    // useful metadata like html lang. For example, if your site is Chinese, you
    // may want to replace "en" with "zh-Hans".
    i18n: {
        defaultLocale: 'en',
        locales: ['en'],
    },

    scripts: [
        {
            src: "https://plausible.io/js/script.js",
            defer: true,
            "data-domain": "leios.cardano-scaling.org",
        },
    ],

    presets: [
        [
            'classic',
            {
                docs: {
                    sidebarPath: './sidebars.ts',
                },
                blog: {
                    path: 'news/',
                    routeBasePath: 'news',
                    blogTitle: "News",
                    blogSidebarTitle: "Latest News",
                    sortPosts: 'descending',
                    showReadingTime: true,
                    authorsMapPath: "../authors.yaml",
                },
                theme: {
                    customCss: './src/css/custom.css',
                },
            } satisfies Preset.Options,
        ],
    ],

    themeConfig: {
        // Replace with your project's social card
        image: 'img/docusaurus-social-card.jpg',
        navbar: {
            title: 'Leios',
            logo: {
                alt: 'Leios Logo',
                src: 'img/wave-logo.svg',
            },
            items: [
                {
                    type: 'docSidebar',
                    sidebarId: 'tutorialSidebar',
                    position: 'left',
                    label: 'Documentation',
                },
                { to: '/news', label: 'Latest News', position: 'right' },
                {
                    href: 'https://www.insightmaker.com/insight/5B3Sq5gsrcGzTD11GyZJ0u/Cardano-Throughput-v0-2',
                    label: 'Throughput Simulation',
                    position: 'right',
                },
                {
                    to: 'pathname:///cost-estimator/',
                    label: 'Cost Estimator',
                    position: 'right',
                },
                {
                    href: 'https://github.com/input-output-hk/ouroboros-leios',
                    label: 'GitHub',
                    position: 'right',
                },
            ],
        },
        footer: {
            links: [
                {
                    title: 'Docs',
                    items: [
                        {
                            label: 'Introduction',
                            to: '/docs/intro',
                        },
                    ],
                },
                {
                    title: 'Community',
                    items: [
                        {
                            label: 'Discord',
                            href: 'https://discord.gg/83aXYxy9',
                        },
                        {
                            label: 'GitHub Discussions',
                            href: 'https://github.com/input-output-hk/ouroboros-leios/discussions',
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
                }],
            copyright: `Copyright © ${new Date().getFullYear()} <strong>Input Output Global</strong> <br/> <a href="https://static.iohk.io/terms/iog-privacy-policy.pdf" target="_blank" class="footer__link-item">Privacy Policy</a> | <a href="https://static.iohk.io/terms/iohktermsandconditions.pdf" target="_blank" class="footer__link-item">Terms & Conditions</a> <br/> <small>Built with Docusaurus</small>`,
        },
        prism: {
            theme: prismThemes.github,
            darkTheme: prismThemes.dracula,
        },
    } satisfies Preset.ThemeConfig,
};

export default config;
