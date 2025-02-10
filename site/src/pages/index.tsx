import Link from "@docusaurus/Link";
import { useColorMode } from "@docusaurus/theme-common";
import useDocusaurusContext from "@docusaurus/useDocusaurusContext";
import HomepageFeatures from "@site/src/components/HomepageFeatures";
import Heading from "@theme/Heading";
import Layout from "@theme/Layout";
import clsx from "clsx";

import styles from "./index.module.css";

function HomepageHeader() {
    const { siteConfig } = useDocusaurusContext();
    const { isDarkTheme } = useColorMode();

    return (
        <>
            <header className={clsx("hero hero--primary", styles.heroBanner)}>
                <div className="container">
                    <Heading as="h1" className="hero__title">
                        {siteConfig.title}
                    </Heading>
                    <p className="hero__subtitle">{siteConfig.tagline}</p>
                    <div className={styles.buttons}>
                        <Link
                            className="button button--secondary button--lg margin-right--md"
                            to="/docs/intro"
                        >
                            Start here 🚀
                        </Link>
                        <Link
                            className="button button--secondary button--lg"
                            to="/docs/faq"
                        >
                            FAQ 💭
                        </Link>
                    </div>
                </div>
            </header>
        </>
    );
}

function VideoSection() {
    return (
        <section className={clsx(styles.videoSection, styles.borderTop)}>
            <div className="container">
                <div className="row">
                    <div className="col col--8 col--offset-2">
                        <h2 className="text--center">
                            Leios in Action
                        </h2>
                        <p className={clsx("text--center", styles.subtitle)}>
                            Early simulation demonstrating the Leios protocol's
                            block propagation and network behavior
                        </p>
                        <div className={styles.videoWrapper}>
                            <iframe
                                className={styles.video}
                                src="https://drive.google.com/file/d/1aVgh0M-jurCVKy0xYQuLQMoj4ikLNBpH/preview"
                                allow="autoplay"
                                allowFullScreen
                            />
                        </div>
                    </div>
                </div>
            </div>
        </section>
    );
}

export default function Home(): JSX.Element {
    const { siteConfig } = useDocusaurusContext();
    return (
        <Layout
            title={`Hello from ${siteConfig.title}`}
            description="Description will go into a meta tag in <head />"
        >
            <HomepageHeader />
            <main>
                <HomepageFeatures />
                <VideoSection />
            </main>
        </Layout>
    );
}
