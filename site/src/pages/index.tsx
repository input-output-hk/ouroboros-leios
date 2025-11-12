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
                </div>
            </header>
        </>
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

function UTCDateTime(year, month, day, hour, minute = 0, second = 0) {
    // NOTE: Not use constructor directly as it uses local time
    const date = new Date(year, month, day, hour, minute, second);
    date.setUTCHours(hour, minute, second);
    return date;
}

let exceptions = {
    "2025-9": UTCDateTime(2025, 9, 1, 14),
};

function getNextMeeting(now = new Date()) {
    let nextMeeting = getLastWednesdayOfMonth(now);
    const exception = exceptions[`${now.getFullYear()}-${now.getMonth() + 1}`];
    if (exception) {
        console.warn("Exceptional next meeting date:", exception);
        nextMeeting = exception;
    }
    const meetingEndTime = new Date(nextMeeting.getTime() + 60 * 60 * 1000); // 1 hour after start

    // If we're past the current month's meeting end time, get next month's meeting
    if (now >= meetingEndTime) {
        const nextMonth = new Date(now.getFullYear(), now.getMonth() + 1, 1);
        return getLastWednesdayOfMonth(nextMonth);
    }

    return nextMeeting;
}

function isLiveTime(now = new Date()) {
    const nextMeeting = getNextMeeting(now);
    const meetingStartTime = nextMeeting.getTime();
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

function LeiosSpecificationSection() {
    return (
        <section
            id="specification"
            className={clsx(styles.videoSection, styles.borderTop)}
        >
            <div className="container">
                <div className="row">
                    <div className="col col--10 col--offset-1">
                        <h2 className="text--center">
                            From Research to Reality
                        </h2>
                        <p className={clsx("text--center", styles.subtitle)}>
                            The{" "}
                            <Link
                                to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md"
                                target="_blank"
                                rel="noopener noreferrer"
                            >
                                published Leios CIP
                            </Link>{" "}
                            represents a strategic balance between throughput
                            gains and ecosystem compatibility
                        </p>
                        <div
                            className="row"
                            style={{ alignItems: "center", marginTop: "2rem" }}
                        >
                            <div className="col col--7">
                                <div className={styles.svgContainer}>
                                    <svg
                                        width="650"
                                        height="550"
                                        viewBox="0 0 650 550"
                                        xmlns="http://www.w3.org/2000/svg"
                                        className={styles.leiosSvg}
                                    >
                                        <rect
                                            width="650"
                                            height="550"
                                            fill="var(--svg-bg-color)"
                                        />
                                        <g transform="translate(300, 250)">
                                            <g
                                                stroke="var(--svg-border-color)"
                                                fill="none"
                                                strokeWidth="1"
                                            >
                                                <circle
                                                    cx="0"
                                                    cy="0"
                                                    r="160"
                                                    opacity="0.5"
                                                />
                                                <circle
                                                    cx="0"
                                                    cy="0"
                                                    r="120"
                                                    opacity="0.4"
                                                />
                                                <circle
                                                    cx="0"
                                                    cy="0"
                                                    r="80"
                                                    opacity="0.4"
                                                />
                                                <circle
                                                    cx="0"
                                                    cy="0"
                                                    r="40"
                                                    opacity="0.4"
                                                />
                                            </g>
                                            <g
                                                stroke="var(--svg-text-secondary)"
                                                strokeWidth="2"
                                            >
                                                <line
                                                    x1="0"
                                                    y1="0"
                                                    x2="0"
                                                    y2="-160"
                                                />
                                                <line
                                                    x1="0"
                                                    y1="0"
                                                    x2="160"
                                                    y2="0"
                                                />
                                                <line
                                                    x1="0"
                                                    y1="0"
                                                    x2="0"
                                                    y2="160"
                                                />
                                                <line
                                                    x1="0"
                                                    y1="0"
                                                    x2="-160"
                                                    y2="0"
                                                />
                                            </g>
                                            <polygon
                                                points="0,-155 150,0 0,140 -160,0"
                                                fill="rgba(255, 165, 0, 0.3)"
                                                stroke="#cc7a00"
                                                strokeWidth="2"
                                            />
                                            <polygon
                                                points="0,-135 65,0 0,42 -80,0"
                                                fill="rgba(75, 192, 192, 0.3)"
                                                stroke="#2e8b8b"
                                                strokeWidth="2"
                                            />
                                            <polygon
                                                points="0,-42 30,0 0,0 0,0"
                                                fill="rgba(220, 53, 69, 0.3)"
                                                stroke="#a71d2a"
                                                strokeWidth="2"
                                            />
                                            <g
                                                fill="rgba(255, 165, 0, 0.9)"
                                                stroke="#cc7a00"
                                                strokeWidth="2"
                                            >
                                                <circle
                                                    cx="0"
                                                    cy="-155"
                                                    r="4"
                                                />
                                                <circle cx="150" cy="0" r="4" />
                                                <circle cx="0" cy="140" r="4" />
                                                <circle
                                                    cx="-160"
                                                    cy="0"
                                                    r="4"
                                                />
                                            </g>
                                            <g
                                                fill="#4bc0c0"
                                                stroke="#2e8b8b"
                                                strokeWidth="2"
                                            >
                                                <circle
                                                    cx="0"
                                                    cy="-135"
                                                    r="4"
                                                />
                                                <circle cx="65" cy="0" r="4" />
                                                <circle cx="0" cy="42" r="4" />
                                                <circle cx="-80" cy="0" r="4" />
                                            </g>
                                            <g
                                                fill="rgba(220, 53, 69, 0.9)"
                                                stroke="#a71d2a"
                                                strokeWidth="2"
                                            >
                                                <circle cx="0" cy="-42" r="4" />
                                                <circle cx="30" cy="0" r="4" />
                                                <circle cx="0" cy="0" r="4" />
                                                <circle cx="0" cy="0" r="4" />
                                            </g>
                                            <text
                                                x="0"
                                                y="-185"
                                                textAnchor="middle"
                                                fontFamily="Arial"
                                                fontSize="14"
                                                fontWeight="bold"
                                                fill="var(--svg-text-color)"
                                            >
                                                Throughput
                                            </text>
                                            <text
                                                x="0"
                                                y="-171"
                                                textAnchor="middle"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-secondary)"
                                                fontWeight="bold"
                                            >
                                                (KiloBytes per Second)
                                            </text>
                                            <text
                                                x="200"
                                                y="5"
                                                textAnchor="start"
                                                fontFamily="Arial"
                                                fontSize="14"
                                                fontWeight="bold"
                                                fill="var(--svg-text-color)"
                                            >
                                                Inclusion Latency
                                            </text>
                                            <text
                                                x="200"
                                                y="19"
                                                textAnchor="start"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fontWeight="bold"
                                                fill="var(--svg-text-secondary)"
                                            >
                                                (Seconds)
                                            </text>
                                            <text
                                                x="0"
                                                y="190"
                                                textAnchor="middle"
                                                fontFamily="Arial"
                                                fontSize="14"
                                                fontWeight="bold"
                                                fill="var(--svg-text-color)"
                                            >
                                                Ecosystem Impact
                                            </text>
                                            <text
                                                x="0"
                                                y="204"
                                                textAnchor="middle"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fontWeight="bold"
                                                fill="var(--svg-text-secondary)"
                                            >
                                                (Adaptation Cost)
                                            </text>
                                            <text
                                                x="-185"
                                                y="5"
                                                textAnchor="end"
                                                fontFamily="Arial"
                                                fontSize="14"
                                                fontWeight="bold"
                                                fill="var(--svg-text-color)"
                                            >
                                                Time to Market
                                            </text>
                                            <text
                                                x="-185"
                                                y="19"
                                                textAnchor="end"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fontWeight="bold"
                                                fill="var(--svg-text-secondary)"
                                            >
                                                (Years)
                                            </text>
                                            <text
                                                x="12"
                                                y="-155"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                1,000+ TxkB/s
                                            </text>
                                            <text
                                                x="12"
                                                y="-115"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                100 TxkB/s
                                            </text>
                                            <text
                                                x="12"
                                                y="-75"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                10 TxkB/s
                                            </text>
                                            <text
                                                x="12"
                                                y="-35"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                1 TxkB/s
                                            </text>
                                            <text
                                                x="165"
                                                y="15"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                300s+
                                            </text>
                                            <text
                                                x="125"
                                                y="15"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                180s
                                            </text>
                                            <text
                                                x="85"
                                                y="15"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                90s
                                            </text>
                                            <text
                                                x="45"
                                                y="15"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                45s
                                            </text>
                                            <text
                                                x="12"
                                                y="155"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                Very High
                                            </text>
                                            <text
                                                x="12"
                                                y="115"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                High
                                            </text>
                                            <text
                                                x="12"
                                                y="75"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                Medium
                                            </text>
                                            <text
                                                x="12"
                                                y="35"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                Low
                                            </text>
                                            <text
                                                x="-165"
                                                y="15"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                3+ yr
                                            </text>
                                            <text
                                                x="-125"
                                                y="15"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                2 yr
                                            </text>
                                            <text
                                                x="-85"
                                                y="15"
                                                fontFamily="Arial"
                                                fontSize="11"
                                                fill="var(--svg-text-muted)"
                                            >
                                                1 yr
                                            </text>
                                        </g>
                                        <g transform="translate(325, 510)">
                                            <circle
                                                cx="-160"
                                                cy="0"
                                                r="4"
                                                fill="rgba(220, 53, 69, 0.9)"
                                                stroke="#a71d2a"
                                                strokeWidth="2"
                                            />
                                            <text
                                                x="-145"
                                                y="5"
                                                textAnchor="start"
                                                fontFamily="Arial"
                                                fontSize="12"
                                                fill="var(--svg-text-color)"
                                            >
                                                Ouroboros Praos
                                            </text>
                                            <circle
                                                cx="-20"
                                                cy="0"
                                                r="4"
                                                fill="#4bc0c0"
                                                stroke="#2e8b8b"
                                                strokeWidth="2"
                                            />
                                            <text
                                                x="-5"
                                                y="5"
                                                textAnchor="start"
                                                fontFamily="Arial"
                                                fontSize="12"
                                                fill="var(--svg-text-color)"
                                            >
                                                Proposed Leios
                                            </text>
                                            <circle
                                                cx="120"
                                                cy="0"
                                                r="4"
                                                fill="rgba(255, 165, 0, 0.9)"
                                                stroke="#cc7a00"
                                                strokeWidth="2"
                                            />
                                            <text
                                                x="135"
                                                y="5"
                                                textAnchor="start"
                                                fontFamily="Arial"
                                                fontSize="12"
                                                fill="var(--svg-text-color)"
                                            >
                                                Research Paper Leios
                                            </text>
                                        </g>
                                    </svg>
                                </div>
                            </div>
                            <div className="col col--5">
                                <p>
                                    The proposed Leios specification delivers a{" "}
                                    <strong>30-50x throughput increase</strong>{" "}
                                    (from ~4.5 TxkB/s to ~140-300 TxkB/s) while
                                    maintaining manageable ecosystem impact.
                                    Unlike the research paper's approach, which
                                    achieves higher throughput but requires
                                    extensive ecosystem changes and 2-3 minute
                                    confirmation times, the CIP specification
                                    strikes a strategic balance.
                                </p>
                                <p>
                                    Key advantages of the CIP approach include
                                    modest latency increases (45-60 seconds vs
                                    20 seconds), familiar transaction structures
                                    for ecosystem compatibility, and a realistic
                                    1-1.5 year deployment timeline compared to
                                    2.5-3 years for higher-concurrency
                                    alternatives.
                                </p>
                                <div style={{ marginTop: "1.5rem" }}>
                                    <Link
                                        className="button button--primary button--md"
                                        to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md"
                                        target="_blank"
                                        rel="noopener noreferrer"
                                    >
                                        Read the Full CIP
                                    </Link>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        </section>
    );
}

function HowLeiosWorksSection() {
    return (
        <section
            id="how"
            className={clsx(styles.videoSection, styles.borderTop)}
        >
            <div className="container">
                <div className="row">
                    <div className="col col--10 col--offset-1">
                        <h2 className="text--center">How Leios Works</h2>
                        <p className={clsx("text--center", styles.subtitle)}>
                            Block producers simultaneously create both a
                            standard Praos block and a larger secondary block
                            referencing additional transactions
                        </p>
                        <div
                            className="row"
                            style={{ alignItems: "center", marginTop: "2rem" }}
                        >
                            <div className="col col--5">
                                <p>
                                    Ouroboros Leios achieves higher transaction
                                    throughput by allowing block producers to
                                    create additional blocks alongside the
                                    regular Praos chain. These supplementary
                                    blocks, called{" "}
                                    <Link
                                        to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#endorser-blocks-ebs"
                                        target="_blank"
                                        rel="noopener noreferrer"
                                    >
                                        <strong>Endorser Blocks (EBs)</strong>
                                    </Link>
                                    , reference extra transactions that would
                                    otherwise wait for the standard Praos blocks
                                    (called{" "}
                                    <Link
                                        to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#ranking-blocks-rbs"
                                        target="_blank"
                                        rel="noopener noreferrer"
                                    >
                                        <strong>Ranking Blocks or RBs</strong>
                                    </Link>
                                    {") "}
                                    in this protocol in future active slots.
                                </p>
                                <p>
                                    To ensure data availability and correctness,
                                    these blocks undergo{" "}
                                    <Link
                                        to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#step-3-committee-validation"
                                        target="_blank"
                                        rel="noopener noreferrer"
                                    >
                                        committee validation
                                    </Link>{" "}
                                    before their transactions become part of the
                                    permanent ledger. The key insight is that we
                                    can maintain Praos's security guarantees
                                    while processing more transactions by
                                    carefully managing when and how these
                                    additional blocks are validated and included
                                    in the chain.
                                </p>
                                <p>
                                    EB inclusion is opportunistic rather than
                                    guaranteed, depending on the random timing
                                    of block production relative to the
                                    certification process. This design preserves
                                    the existing Praos chain structure while
                                    adding substantial transaction capacity
                                    through the secondary validation pathway.
                                </p>
                                <div style={{ marginTop: "1.5rem" }}>
                                    <Link
                                        className="button button--primary button--md"
                                        to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#specification"
                                        target="_blank"
                                        rel="noopener noreferrer"
                                    >
                                        Read the Technical Details
                                    </Link>
                                </div>
                            </div>
                            <div className="col col--7">
                                <div className={styles.svgContainer}>
                                    <svg
                                        width="1000"
                                        height="580"
                                        viewBox="0 0 1000 580"
                                        xmlns="http://www.w3.org/2000/svg"
                                        className={styles.leiosSvg}
                                    >
                                        <defs>
                                            <pattern
                                                id="timelinePattern"
                                                x="0"
                                                y="0"
                                                width="40"
                                                height="40"
                                                patternUnits="userSpaceOnUse"
                                            >
                                                <rect
                                                    width="40"
                                                    height="40"
                                                    fill="var(--svg-bg-color)"
                                                />
                                                <line
                                                    x1="0"
                                                    y1="40"
                                                    x2="40"
                                                    y2="0"
                                                    stroke="var(--svg-border-color)"
                                                    strokeWidth="0.5"
                                                />
                                            </pattern>
                                            <marker
                                                id="arrowhead"
                                                markerWidth="6"
                                                markerHeight="4"
                                                refX="5"
                                                refY="2"
                                                orient="auto"
                                            >
                                                <polygon
                                                    points="0 0, 6 2, 0 4"
                                                    fill="var(--svg-arrow-color)"
                                                />
                                            </marker>
                                            <marker
                                                id="votearrowhead"
                                                markerWidth="6"
                                                markerHeight="4"
                                                refX="5"
                                                refY="2"
                                                orient="auto"
                                            >
                                                <polygon
                                                    points="0 0, 6 2, 0 4"
                                                    fill="#f9a825"
                                                />
                                            </marker>
                                        </defs>

                                        <rect
                                            width="1000"
                                            height="580"
                                            fill="var(--svg-bg-color)"
                                        />

                                        {/* Slot Grid */}
                                        <g
                                            stroke="var(--svg-border-color)"
                                            strokeWidth="1"
                                        >
                                            <line
                                                x1="100"
                                                y1="80"
                                                x2="100"
                                                y2="560"
                                            />
                                            <line
                                                x1="250"
                                                y1="80"
                                                x2="250"
                                                y2="560"
                                            />
                                            <line
                                                x1="400"
                                                y1="80"
                                                x2="400"
                                                y2="560"
                                            />
                                            <line
                                                x1="550"
                                                y1="80"
                                                x2="550"
                                                y2="560"
                                            />
                                            <line
                                                x1="700"
                                                y1="80"
                                                x2="700"
                                                y2="560"
                                            />
                                            <line
                                                x1="850"
                                                y1="80"
                                                x2="850"
                                                y2="560"
                                            />
                                        </g>

                                        {/* Minor grid lines */}
                                        <g
                                            stroke="var(--svg-border-color)"
                                            strokeWidth="0.5"
                                            opacity="0.5"
                                        >
                                            <line
                                                x1="130"
                                                y1="80"
                                                x2="130"
                                                y2="560"
                                            />
                                            <line
                                                x1="160"
                                                y1="80"
                                                x2="160"
                                                y2="560"
                                            />
                                            <line
                                                x1="190"
                                                y1="80"
                                                x2="190"
                                                y2="560"
                                            />
                                            <line
                                                x1="220"
                                                y1="80"
                                                x2="220"
                                                y2="560"
                                            />
                                            <line
                                                x1="280"
                                                y1="80"
                                                x2="280"
                                                y2="560"
                                            />
                                            <line
                                                x1="310"
                                                y1="80"
                                                x2="310"
                                                y2="560"
                                            />
                                            <line
                                                x1="340"
                                                y1="80"
                                                x2="340"
                                                y2="560"
                                            />
                                            <line
                                                x1="370"
                                                y1="80"
                                                x2="370"
                                                y2="560"
                                            />
                                            <line
                                                x1="430"
                                                y1="80"
                                                x2="430"
                                                y2="560"
                                            />
                                            <line
                                                x1="460"
                                                y1="80"
                                                x2="460"
                                                y2="560"
                                            />
                                            <line
                                                x1="490"
                                                y1="80"
                                                x2="490"
                                                y2="560"
                                            />
                                            <line
                                                x1="520"
                                                y1="80"
                                                x2="520"
                                                y2="560"
                                            />
                                            <line
                                                x1="580"
                                                y1="80"
                                                x2="580"
                                                y2="560"
                                            />
                                            <line
                                                x1="610"
                                                y1="80"
                                                x2="610"
                                                y2="560"
                                            />
                                            <line
                                                x1="640"
                                                y1="80"
                                                x2="640"
                                                y2="560"
                                            />
                                            <line
                                                x1="670"
                                                y1="80"
                                                x2="670"
                                                y2="560"
                                            />
                                            <line
                                                x1="730"
                                                y1="80"
                                                x2="730"
                                                y2="560"
                                            />
                                            <line
                                                x1="760"
                                                y1="80"
                                                x2="760"
                                                y2="560"
                                            />
                                            <line
                                                x1="790"
                                                y1="80"
                                                x2="790"
                                                y2="560"
                                            />
                                            <line
                                                x1="820"
                                                y1="80"
                                                x2="820"
                                                y2="560"
                                            />
                                        </g>

                                        {/* Timeline */}
                                        <rect
                                            x="100"
                                            y="40"
                                            width="750"
                                            height="30"
                                            fill="url(#timelinePattern)"
                                            stroke="var(--svg-border-color)"
                                            strokeWidth="0.5"
                                        />
                                        <text
                                            x="475"
                                            y="60"
                                            fontFamily="Arial, sans-serif"
                                            fontSize="12"
                                            textAnchor="middle"
                                            fill="var(--svg-text-color)"
                                        >
                                            Time (slots) →
                                        </text>

                                        {/* RB Block */}
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#ranking-blocks-rbs"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <rect
                                                x="220"
                                                y="100"
                                                width="60"
                                                height="80"
                                                fill="#fce5cd"
                                                stroke="#783f04"
                                                strokeWidth="2"
                                                rx="6"
                                                style={{ cursor: "pointer" }}
                                            />
                                            <text
                                                x="250"
                                                y="135"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="20"
                                                fontWeight="bold"
                                                textAnchor="middle"
                                                fill="#783f04"
                                                style={{ cursor: "pointer" }}
                                            >
                                                RB
                                            </text>
                                            <text
                                                x="250"
                                                y="160"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="12"
                                                textAnchor="middle"
                                                fill="#783f04"
                                                style={{ cursor: "pointer" }}
                                            >
                                                [Txs]
                                            </text>
                                        </a>

                                        {/* EB Block */}
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#endorser-blocks-ebs"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <rect
                                                x="200"
                                                y="220"
                                                width="100"
                                                height="60"
                                                fill="#d9ead3"
                                                stroke="#274e13"
                                                strokeWidth="2"
                                                rx="6"
                                                style={{ cursor: "pointer" }}
                                            />
                                            <text
                                                x="250"
                                                y="250"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="18"
                                                fontWeight="bold"
                                                textAnchor="middle"
                                                fill="#274e13"
                                                style={{ cursor: "pointer" }}
                                            >
                                                EB
                                            </text>
                                            <text
                                                x="250"
                                                y="268"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="11"
                                                textAnchor="middle"
                                                fill="#274e13"
                                                style={{ cursor: "pointer" }}
                                            >
                                                [TxRefs]
                                            </text>
                                        </a>

                                        {/* RB' Block */}
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#ranking-blocks-rbs"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <rect
                                                x="670"
                                                y="100"
                                                width="60"
                                                height="80"
                                                fill="#fce5cd"
                                                stroke="#783f04"
                                                strokeWidth="2"
                                                rx="6"
                                                style={{ cursor: "pointer" }}
                                            />
                                            <text
                                                x="700"
                                                y="135"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="20"
                                                fontWeight="bold"
                                                textAnchor="middle"
                                                fill="#783f04"
                                                style={{ cursor: "pointer" }}
                                            >
                                                RB'
                                            </text>
                                        </a>

                                        {/* Certificate */}
                                        <g transform="translate(700, 185)">
                                            <a
                                                href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
                                                target="_blank"
                                                rel="noopener noreferrer"
                                            >
                                                <polygon
                                                    points="0,-20 20,-10 20,10 0,20 -20,10 -20,-10"
                                                    fill="#fff2cc"
                                                    stroke="#f9a825"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <text
                                                    x="0"
                                                    y="5"
                                                    fontSize="12"
                                                    fontWeight="bold"
                                                    textAnchor="middle"
                                                    fill="#7f6000"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                >
                                                    <tspan
                                                        fontFamily="serif"
                                                        fontStyle="italic"
                                                        fontSize="14"
                                                    >
                                                        C
                                                    </tspan>
                                                    <tspan
                                                        fontFamily="Arial, sans-serif"
                                                        fontSize="10"
                                                        fontStyle="normal"
                                                        dy="3"
                                                    >
                                                        EB
                                                    </tspan>
                                                </text>
                                            </a>
                                        </g>

                                        {/* Arrows and connections */}
                                        <path
                                            d="M 250 180 L 250 216"
                                            stroke="#783f04"
                                            strokeWidth="2"
                                            strokeDasharray="4,3"
                                        />
                                        <text
                                            x="255"
                                            y="200"
                                            fontFamily="Arial, sans-serif"
                                            fontSize="11"
                                            textAnchor="start"
                                            fill="#783f04"
                                        >
                                            announces
                                        </text>

                                        {/* Parameter brackets */}
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-hdr"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <path
                                                d="M 250 300 L 250 305 Q 250 310 255 310 L 335 310 Q 340 310 340 305 L 340 300"
                                                stroke="#f57c00"
                                                strokeWidth="2"
                                                fill="none"
                                                style={{ cursor: "pointer" }}
                                            />
                                            <text
                                                x="295"
                                                y="335"
                                                fontSize="18"
                                                textAnchor="middle"
                                                fill="#f57c00"
                                                style={{ cursor: "pointer" }}
                                            >
                                                <tspan
                                                    fontFamily="serif"
                                                    fontSize="24"
                                                >
                                                    3
                                                </tspan>
                                                <tspan
                                                    fontFamily="serif"
                                                    fontStyle="italic"
                                                    fontSize="24"
                                                >
                                                    L
                                                </tspan>
                                                <tspan
                                                    fontFamily="Arial, sans-serif"
                                                    fontSize="16"
                                                    dy="3"
                                                >
                                                    hdr
                                                </tspan>
                                            </text>
                                        </a>

                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-vote"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <path
                                                d="M 340 320 L 340 325 Q 340 330 345 330 L 455 330 Q 460 330 460 325 L 460 320"
                                                stroke="#f9a825"
                                                strokeWidth="2"
                                                fill="none"
                                                style={{ cursor: "pointer" }}
                                            />
                                            <text
                                                x="400"
                                                y="355"
                                                fontSize="18"
                                                textAnchor="middle"
                                                fill="#f9a825"
                                                style={{ cursor: "pointer" }}
                                            >
                                                <tspan
                                                    fontFamily="serif"
                                                    fontStyle="italic"
                                                    fontSize="24"
                                                >
                                                    L
                                                </tspan>
                                                <tspan
                                                    fontFamily="Arial, sans-serif"
                                                    fontSize="16"
                                                    dy="3"
                                                >
                                                    vote
                                                </tspan>
                                            </text>
                                        </a>

                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-diff"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <path
                                                d="M 460 340 L 460 345 Q 460 350 465 350 L 665 350 Q 670 350 670 345 L 670 340"
                                                stroke="#ffb74d"
                                                strokeWidth="2"
                                                fill="none"
                                                style={{ cursor: "pointer" }}
                                            />
                                            <text
                                                x="565"
                                                y="375"
                                                fontSize="18"
                                                textAnchor="middle"
                                                fill="#ffb74d"
                                                style={{ cursor: "pointer" }}
                                            >
                                                <tspan
                                                    fontFamily="serif"
                                                    fontStyle="italic"
                                                    fontSize="24"
                                                >
                                                    L
                                                </tspan>
                                                <tspan
                                                    fontFamily="Arial, sans-serif"
                                                    fontSize="16"
                                                    dy="3"
                                                >
                                                    diff
                                                </tspan>
                                            </text>
                                        </a>

                                        {/* Votes */}
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <rect
                                                x="352"
                                                y="305"
                                                width="6"
                                                height="6"
                                                fill="#f9a825"
                                                transform="rotate(45 355 308)"
                                                style={{ cursor: "pointer" }}
                                            />
                                        </a>
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <rect
                                                x="372"
                                                y="310"
                                                width="6"
                                                height="6"
                                                fill="#f9a825"
                                                transform="rotate(45 375 313)"
                                                style={{ cursor: "pointer" }}
                                            />
                                        </a>
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <rect
                                                x="392"
                                                y="300"
                                                width="6"
                                                height="6"
                                                fill="#f9a825"
                                                transform="rotate(45 395 303)"
                                                style={{ cursor: "pointer" }}
                                            />
                                        </a>
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <rect
                                                x="412"
                                                y="311"
                                                width="6"
                                                height="6"
                                                fill="#f9a825"
                                                transform="rotate(45 415 318)"
                                                style={{ cursor: "pointer" }}
                                            />
                                        </a>
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <rect
                                                x="432"
                                                y="305"
                                                width="6"
                                                height="6"
                                                fill="#f9a825"
                                                transform="rotate(45 435 308)"
                                                style={{ cursor: "pointer" }}
                                            />
                                        </a>

                                        {/* Delta network characteristics */}
                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-rb"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <g id="rb-diffusion">
                                                <line
                                                    x1="700"
                                                    y1="385"
                                                    x2="700"
                                                    y2="395"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="700"
                                                    y1="390"
                                                    x2="850"
                                                    y2="390"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    strokeDasharray="4,2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="850"
                                                    y1="385"
                                                    x2="850"
                                                    y2="395"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <text
                                                    x="777"
                                                    y="375"
                                                    fontFamily="Arial, sans-serif"
                                                    fontSize="20"
                                                    textAnchor="middle"
                                                    fill="#607d8b"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                >
                                                    Δ
                                                    <tspan fontSize="16" dy="3">
                                                        RB
                                                    </tspan>
                                                    <tspan
                                                        fontSize="14"
                                                        dy="-6"
                                                    >
                                                        W
                                                    </tspan>
                                                </text>
                                            </g>
                                        </a>

                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-applytxs"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <g id="tx-processing">
                                                <line
                                                    x1="775"
                                                    y1="425"
                                                    x2="775"
                                                    y2="435"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="775"
                                                    y1="430"
                                                    x2="850"
                                                    y2="430"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    strokeDasharray="4,2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="850"
                                                    y1="425"
                                                    x2="850"
                                                    y2="435"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <text
                                                    x="815"
                                                    y="415"
                                                    fontFamily="Arial, sans-serif"
                                                    fontSize="18"
                                                    textAnchor="middle"
                                                    fill="#607d8b"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                >
                                                    Δ
                                                    <tspan fontSize="14" dy="3">
                                                        applyTxs
                                                    </tspan>
                                                    <tspan
                                                        fontSize="12"
                                                        dy="-6"
                                                    >
                                                        W
                                                    </tspan>
                                                </text>
                                            </g>
                                        </a>

                                        <a
                                            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-eb-H"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <g id="network-chars-vote">
                                                <line
                                                    x1="250"
                                                    y1="425"
                                                    x2="250"
                                                    y2="435"
                                                    stroke="#8bc34a"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="250"
                                                    y1="430"
                                                    x2="460"
                                                    y2="430"
                                                    stroke="#8bc34a"
                                                    strokeWidth="2"
                                                    strokeDasharray="4,2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="460"
                                                    y1="425"
                                                    x2="460"
                                                    y2="435"
                                                    stroke="#8bc34a"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <text
                                                    x="355"
                                                    y="415"
                                                    fontFamily="Arial, sans-serif"
                                                    fontSize="18"
                                                    textAnchor="middle"
                                                    fill="#8bc34a"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                >
                                                    Δ
                                                    <tspan fontSize="14" dy="3">
                                                        EB
                                                    </tspan>
                                                    <tspan
                                                        fontSize="12"
                                                        dy="-6"
                                                    >
                                                        O
                                                    </tspan>
                                                </text>
                                            </g>
                                        </a>

                                        <g id="network-chars-after">
                                            <a
                                                href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-eb-A"
                                                target="_blank"
                                                rel="noopener noreferrer"
                                            >
                                                <line
                                                    x1="250"
                                                    y1="465"
                                                    x2="250"
                                                    y2="475"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="250"
                                                    y1="470"
                                                    x2="810"
                                                    y2="470"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    strokeDasharray="4,2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="810"
                                                    y1="465"
                                                    x2="810"
                                                    y2="475"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <text
                                                    x="530"
                                                    y="455"
                                                    fontFamily="Arial, sans-serif"
                                                    fontSize="18"
                                                    textAnchor="middle"
                                                    fill="#607d8b"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                >
                                                    Δ
                                                    <tspan fontSize="14" dy="3">
                                                        EB
                                                    </tspan>
                                                    <tspan
                                                        fontSize="12"
                                                        dy="-6"
                                                    >
                                                        W
                                                    </tspan>
                                                </text>
                                            </a>

                                            <a
                                                href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-reapply"
                                                target="_blank"
                                                rel="noopener noreferrer"
                                            >
                                                <line
                                                    x1="815"
                                                    y1="465"
                                                    x2="815"
                                                    y2="475"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="815"
                                                    y1="470"
                                                    x2="850"
                                                    y2="470"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    strokeDasharray="4,2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <line
                                                    x1="850"
                                                    y1="465"
                                                    x2="850"
                                                    y2="475"
                                                    stroke="#607d8b"
                                                    strokeWidth="2"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                />
                                                <text
                                                    x="835"
                                                    y="455"
                                                    fontFamily="Arial, sans-serif"
                                                    fontSize="18"
                                                    textAnchor="middle"
                                                    fill="#607d8b"
                                                    style={{
                                                        cursor: "pointer",
                                                    }}
                                                >
                                                    Δ
                                                    <tspan fontSize="14" dy="3">
                                                        reapply
                                                    </tspan>
                                                    <tspan
                                                        fontSize="12"
                                                        dy="-6"
                                                    >
                                                        W
                                                    </tspan>
                                                </text>
                                            </a>
                                        </g>

                                        {/* Certificate back arrow */}
                                        <path
                                            d="M 700 205 Q 475 250 300 250"
                                            stroke="#f9a825"
                                            strokeWidth="2"
                                            strokeDasharray="2,2"
                                            fill="none"
                                            markerEnd="url(#votearrowhead)"
                                        />

                                        {/* Additional arrows */}
                                        <path
                                            d="M 220 140 L 150 140"
                                            stroke="var(--svg-arrow-color)"
                                            strokeWidth="2"
                                            strokeDasharray="4,3"
                                            markerEnd="url(#arrowhead)"
                                        />
                                        <path
                                            d="M 670 140 L 280 140"
                                            stroke="var(--svg-arrow-color)"
                                            strokeWidth="2"
                                            markerEnd="url(#arrowhead)"
                                        />
                                        <path
                                            d="M 900 140 L 730 140"
                                            stroke="var(--svg-arrow-color)"
                                            strokeWidth="2"
                                            strokeDasharray="4,3"
                                            markerEnd="url(#arrowhead)"
                                        />

                                        {/* Legend */}
                                        <g id="legend">
                                            <rect
                                                x="20"
                                                y="420"
                                                width="220"
                                                height="118"
                                                fill="var(--svg-legend-bg)"
                                                stroke="var(--svg-border-color)"
                                                strokeWidth="1"
                                                rx="4"
                                            />
                                            <text
                                                x="30"
                                                y="440"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="12"
                                                fontWeight="bold"
                                                fill="var(--svg-text-color)"
                                            >
                                                Legend
                                            </text>

                                            {/* Certificate shape */}
                                            <g transform="translate(45, 455)">
                                                <polygon
                                                    points="0,-8 8,-4 8,4 0,8 -8,4 -8,-4"
                                                    fill="#fff2cc"
                                                    stroke="#f9a825"
                                                    strokeWidth="1"
                                                />
                                            </g>
                                            <text
                                                x="65"
                                                y="460"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="11"
                                                fill="var(--svg-text-color)"
                                            >
                                                Certificate
                                            </text>

                                            {/* Vote shape */}
                                            <g transform="translate(45, 475)">
                                                <rect
                                                    x="-3"
                                                    y="-3"
                                                    width="6"
                                                    height="6"
                                                    fill="#f9a825"
                                                    transform="rotate(45)"
                                                />
                                            </g>
                                            <text
                                                x="65"
                                                y="480"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="11"
                                                fill="var(--svg-text-color)"
                                            >
                                                Vote
                                            </text>

                                            <text
                                                x="30"
                                                y="500"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="12"
                                                fontWeight="bold"
                                                fill="var(--svg-text-color)"
                                            >
                                                Superscripts
                                            </text>
                                            <text
                                                x="30"
                                                y="515"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="11"
                                                fill="var(--svg-text-color)"
                                            >
                                                O = Optimistic
                                            </text>
                                            <text
                                                x="30"
                                                y="528"
                                                fontFamily="Arial, sans-serif"
                                                fontSize="11"
                                                fill="var(--svg-text-color)"
                                            >
                                                W = Worst-case
                                            </text>
                                        </g>
                                    </svg>
                                    <div className={styles.svgCaption}>
                                        Protocol timing showing the sequential
                                        process from RB announcement through EB
                                        validation to certificate inclusion. Key
                                        parameters:{" "}
                                        <Link
                                            to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-hdr"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <span
                                                style={{
                                                    fontSize: "1.25em",
                                                    fontFamily:
                                                        "Times New Roman, serif",
                                                }}
                                            >
                                                L
                                            </span>
                                            <sub>hdr</sub>
                                        </Link>{" "}
                                        (
                                        <Link
                                            to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#equivocation-detection"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            header diffusion
                                        </Link>
                                        ),{" "}
                                        <Link
                                            to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-vote"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <span
                                                style={{
                                                    fontSize: "1.25em",
                                                    fontFamily:
                                                        "Times New Roman, serif",
                                                }}
                                            >
                                                L
                                            </span>
                                            <sub>vote</sub>
                                        </Link>{" "}
                                        (
                                        <Link
                                            to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#voting-period"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            voting period
                                        </Link>
                                        ),{" "}
                                        <Link
                                            to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-diff"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            <span
                                                style={{
                                                    fontSize: "1.25em",
                                                    fontFamily:
                                                        "Times New Roman, serif",
                                                }}
                                            >
                                                L
                                            </span>
                                            <sub>diff</sub>
                                        </Link>{" "}
                                        (
                                        <Link
                                            to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#diffusion-period"
                                            target="_blank"
                                            rel="noopener noreferrer"
                                        >
                                            diffusion period
                                        </Link>
                                        ).
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        </section>
    );
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
            setNextDate(
                target.toLocaleString(undefined, {
                    weekday: "short",
                    year: "numeric",
                    month: "short",
                    day: "numeric",
                    hour: "2-digit",
                    minute: "2-digit",
                    hour12: false,
                }),
            );
        }
        updateCountdown();
        const interval = setInterval(updateCountdown, 1000);
        return () => clearInterval(interval);
    }, []);

    return (
        <section
            id="next"
            className={clsx(styles.videoSection, styles.borderTop)}
        >
            <div className="container">
                <div className="row">
                    <div className="col col--8 col--offset-2">
                        <h2 className="text--center">Stay up to date</h2>
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
                                    to="https://youtube.com/live/rraKzt-JIqM"
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
                                                color: "var(--ifm-color-primary-contrast-background, #222)",
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
                                            color: "var(--ifm-color-emphasis-800)",
                                            textAlign: "center",
                                            fontWeight: 500,
                                        }}
                                    >
                                        Next review meeting: {nextDate}
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
            title={siteConfig.title}
            description="A high-throughput protocol for Cardano"
        >
            <HomepageHeader />
            <main>
                <HomepageFeatures />
                <LeiosSpecificationSection />
                <HowLeiosWorksSection />
                <MonthlyReviewsSection />
            </main>
        </Layout>
    );
}
