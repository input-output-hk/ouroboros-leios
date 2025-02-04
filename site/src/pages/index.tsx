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
                            className="button button--secondary button--lg"
                            to="/docs/intro"
                        >
                            Get Started 🚀
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

type FAQItem = {
    question: string;
    answer: string;
};

const faqItems: FAQItem[] = [
    {
        question: "What are downstream effects of deploying Leios?",
        answer:
            "Ongoing internal discussions - we will publish an answer/link here to our findings.",
    },
    {
        question: "Could the mempool be sized to the throughput of the system?",
        answer:
            "That's already the case. Default mempool size is a small multiple of current block size.",
    },
    {
        question:
            "Can the system be sharded according to resources (small nodes vs. big nodes)?",
        answer:
            "Leios' current design does not involve sharding in a sense of different resource " +
            "requirements for different nodes. In short, the Leios design does not involve sharding. " +
            "These are ideas in research and require more work. As of now, each node has to validate " +
            "all blocks, hence in a traditional sense, adding more nodes does not increase " +
            "throughput. Each node must cope with the throughput of the whole system.",
    },
    {
        question:
            "Can the system self-regulate instead of manually fine tuning?",
        answer:
            "The current system's load is imposed on each node through the protocol parameters. Thus, " +
            "it remains a democratic vote, not a choice made locally by nodes or automatically. " +
            "Given that the load is imposed on each node through the choice of the protocol " +
            "parameters, it remains a democratic vote to drive adaptation. In a sharded approach this " +
            "could be different. But in the current system there is no local or automatic choice " +
            "to be made by individual nodes.",
    },
];

function FAQSection() {
    return (
        <section className={clsx(styles.faqSection, styles.borderTop)}>
            <div className="container">
                <div className="row">
                    <div className="col col--8 col--offset-2">
                        <h2 className="text--center">
                            Frequently Asked Questions
                        </h2>
                        <div className={styles.faqWrapper}>
                            {faqItems.map((item, index) => (
                                <details key={index} className={styles.faqItem}>
                                    <summary className={styles.faqQuestion}>
                                        <span>{item.question}</span>
                                    </summary>
                                    <div className={styles.faqAnswer}>
                                        {item.answer}
                                    </div>
                                </details>
                            ))}
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
                <FAQSection />
            </main>
        </Layout>
    );
}
