import Link from "@docusaurus/Link";
import useDocusaurusContext from "@docusaurus/useDocusaurusContext";
import HomepageFeatures from "@site/src/components/HomepageFeatures";
import Heading from "@theme/Heading";
import Layout from "@theme/Layout";
import clsx from "clsx";
import React, { useEffect, useState } from "react";

import styles from "./index.module.css";

function HomepageHeader() {
    const { siteConfig } = useDocusaurusContext();

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
                            to="/docs/overview"
                        >
                            Start here 🚀
                        </Link>
                        <Link
                            className="button button--secondary button--lg"
                            to="/docs/faq"
                        >
                            FAQs 💭
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
                            Leios in action
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

function getLastWednesdayOfMonth(date = new Date()) {
    const year = date.getFullYear();
    const month = date.getMonth();
    // Start from the last day of the month
    const lastDay = new Date(Date.UTC(year, month + 1, 0));
    // 3 = Wednesday
    const lastWednesday = new Date(lastDay);
    while (lastWednesday.getUTCDay() !== 3) {
        lastWednesday.setUTCDate(lastWednesday.getUTCDate() - 1);
    }
    // Set to 14:00 UTC (2pm UTC)
    lastWednesday.setUTCHours(14, 0, 0, 0);
    return lastWednesday;
}

function getNextMeeting(now = new Date()) {
    const currentMonthMeeting = getLastWednesdayOfMonth(now);
    const meetingEndTime = new Date(
        currentMonthMeeting.getTime() + 60 * 60 * 1000,
    ); // 1 hour after start

    // If we're past the current month's meeting end time, get next month's meeting
    if (now >= meetingEndTime) {
        const nextMonth = new Date(now.getFullYear(), now.getMonth() + 1, 1);
        return getLastWednesdayOfMonth(nextMonth);
    }

    return currentMonthMeeting;
}

function isLiveTime(now = new Date()) {
    const currentMonthMeeting = getLastWednesdayOfMonth(now);
    const meetingStartTime = currentMonthMeeting.getTime();
    const meetingEndTime = meetingStartTime + 60 * 60 * 1000; // 1 hour after start
    const currentTime = now.getTime();

    return currentTime >= meetingStartTime && currentTime < meetingEndTime;
}

function formatCountdown(ms, isLive = false) {
    if (isLive) return "Live Now!";
    if (ms <= 0) return "Starting soon";
    const totalSeconds = Math.floor(ms / 1000);
    const weeks = Math.floor(totalSeconds / (7 * 24 * 3600));
    const days = Math.floor((totalSeconds % (7 * 24 * 3600)) / (24 * 3600));
    const hours = Math.floor((totalSeconds % (24 * 3600)) / 3600);
    const minutes = Math.floor((totalSeconds % 3600) / 60);
    const seconds = totalSeconds % 60;
    const parts = [];
    if (weeks) parts.push(`${weeks} week${weeks > 1 ? "s" : ""}`);
    if (days) parts.push(`${days} day${days > 1 ? "s" : ""}`);
    if (hours) parts.push(`${hours} hour${hours > 1 ? "s" : ""}`);
    if (minutes) parts.push(`${minutes} min${minutes > 1 ? "s" : ""}`);
    if (seconds && parts.length < 2) {
        parts.push(`${seconds} sec${seconds > 1 ? "s" : ""}`);
    }
    return `Starting in ${parts.slice(0, 2).join(", ")}`;
}

function MonthlyReviewsSection() {
    const [countdown, setCountdown] = useState("");
    const [nextDate, setNextDate] = useState("");
    const [isLive, setIsLive] = useState(false);

    useEffect(() => {
        function updateCountdown() {
            const now = new Date();
            const live = isLiveTime(now);
            const target = getNextMeeting(now);

            setIsLive(live);
            setCountdown(
                formatCountdown(target.getTime() - now.getTime(), live),
            );
            setNextDate(target.toLocaleString(undefined, {
                weekday: "short",
                year: "numeric",
                month: "short",
                day: "numeric",
                hour: "2-digit",
                minute: "2-digit",
                hour12: false,
            }));
        }
        updateCountdown();
        const interval = setInterval(updateCountdown, 1000);
        return () => clearInterval(interval);
    }, []);

    return (
        <section className={clsx(styles.videoSection, styles.borderTop)}>
            <div className="container">
                <div className="row">
                    <div className="col col--8 col--offset-2">
                        <h2 className="text--center">
                            Stay up to date
                        </h2>
                        <p className={clsx("text--center", styles.subtitle)}>
                            Catch up on the latest Leios progress, key
                            decisions, and Q&A in our monthly review videos
                        </p>
                        <div
                            className="text--center"
                            style={{
                                display: "flex",
                                flexDirection: "column",
                                justifyContent: "center",
                                alignItems: "center",
                                gap: 24,
                            }}
                        >
                            <div
                                className="text--center"
                                style={{
                                    display: "flex",
                                    flexDirection: "column",
                                    justifyContent: "center",
                                    alignItems: "center",
                                }}
                            >
                                <Link
                                    className="button button--primary button--lg"
                                    to="https://www.youtube.com/watch?v=wXqKpQT2H3Y&list=PLnPTB0CuBOBzWWpnojAK3ZaFy9RdofP6l&index=2"
                                    target="_blank"
                                    rel="noopener noreferrer"
                                    style={{
                                        display: "flex",
                                        flexDirection: "column",
                                        alignItems: "center",
                                        minWidth: 180,
                                    }}
                                >
                                    <span>
                                        {isLive ? "Join Live" : "Watch Live"}
                                    </span>
                                    {!isLive && (
                                        <span
                                            style={{
                                                fontSize: "0.68em",
                                                fontWeight: 600,
                                                color:
                                                    "var(--ifm-color-primary-contrast-background, #222)",
                                                marginTop: 2,
                                                lineHeight: 1.2,
                                            }}
                                        >
                                            {countdown}
                                        </span>
                                    )}
                                </Link>
                                {!isLive && (
                                    <div
                                        style={{
                                            fontSize: "1rem",
                                            marginTop: 10,
                                            color:
                                                "var(--ifm-color-emphasis-800)",
                                            textAlign: "center",
                                            fontWeight: 500,
                                        }}
                                    >
                                        Next update: {nextDate}
                                    </div>
                                )}
                            </div>
                            <Link
                                className={clsx(styles.underlineLink)}
                                to="/docs/development/monthly-reviews"
                            >
                                Catch up on past reviews
                            </Link>
                        </div>
                    </div>
                </div>
            </div>
        </section>
    );
}

export default function Home(): React.ReactElement {
    const { siteConfig } = useDocusaurusContext();
    return (
        <Layout
            title={`Hello from ${siteConfig.title}`}
            description="Description will go into a meta tag in <head />"
        >
            <HomepageHeader />
            <main>
                <HomepageFeatures />
                <MonthlyReviewsSection />
                <VideoSection />
            </main>
        </Layout>
    );
}
