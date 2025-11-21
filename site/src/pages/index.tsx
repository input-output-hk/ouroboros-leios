import Link from "@docusaurus/Link";

import useDocusaurusContext from "@docusaurus/useDocusaurusContext";
import HomepageFeatures from "@site/src/components/HomepageFeatures";
import Layout from "@theme/Layout";
import clsx from "clsx";
import React, { useEffect, useState } from "react";

import { LinkButton } from "../components/LinkButton/LinkButton";
import HowLeiosWorksGraphic from "./HowLeiosWorksGraphic";
import styles from "./index.module.css";
import ResearchGraphic from "./ResearchGraphic";
import VideoCamUrl from "@site/static/img/video-cam.png";

function HomepageHeader() {
  const { siteConfig } = useDocusaurusContext();

  return (
    <>
      <header className={clsx("hero hero--primary")}>
        <div className="container">
          <div className={clsx("container-padding", styles.heroBanner)}>
            <h1 className={styles.heroTitle}>{siteConfig.title}</h1>
            <p className={styles.heroStandfirst}>{siteConfig.tagline}</p>
          </div>
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
  return ` in \n ${parts.slice(0, 2).join(", ")}`;
}

function highlightNumbers(str: string) {
  return str.split(/(\d+)/).map((part, i) => {
    if (/^\d+$/.test(part)) {
      return (
        <span key={i} style={{ color: "#C219FF" }}>
          {part}
        </span>
      );
    }
    return part;
  });
}

function LeiosSpecificationSection() {
  return (
    <section id="specification" className="homepage-section-secondary">
      <div className="container">
        <div className="container-padding padding-section">
          <div className={styles.researchContentWrapper}>
            <div className={styles.researchContent}>
              <h2>From Research to Reality</h2>
              <p className={styles.subtitle}>
                The{" "}
                <Link
                  to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md"
                  target="_blank"
                  rel="noopener noreferrer"
                >
                  published Leios CIP
                </Link>{" "}
                represents a strategic balance between throughput gains and
                ecosystem compatibility
              </p>
              <p>
                The proposed Leios specification delivers a{" "}
                <strong>30-50x throughput increase</strong> (from ~4.5 TxkB/s to
                ~140-300 TxkB/s) while maintaining manageable ecosystem impact.
                Unlike the research paper's approach, which achieves higher
                throughput but requires extensive ecosystem changes and 2-3
                minute confirmation times, the CIP specification strikes a
                strategic balance.
              </p>
              <p>
                Key advantages of the CIP approach include modest latency
                increases (45-60 seconds vs 20 seconds), familiar transaction
                structures for ecosystem compatibility, and a realistic 1-1.5
                year deployment timeline compared to 2.5-3 years for
                higher-concurrency alternatives.
              </p>
              <div className={styles.researchContentinkButton}>
                <LinkButton
                  text="Read the Full CIP"
                  url="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md"
                />
              </div>
            </div>
            <div className={styles.svgContainer}>
              <ResearchGraphic />
            </div>
          </div>
        </div>
      </div>
    </section>
  );
}

function HowLeiosWorksSection() {
  return (
    <section id="how" className="homepage-section-primary">
      <div className="container">
        <div className="container-padding padding-section">
          <div className={styles.contentWrapper}>
            <div className={styles.howLeiosWorksContent}>
              <h2>How Leios Works</h2>
              <p className={styles.subtitle}>
                Block producers simultaneously create both a standard Praos
                block and a larger secondary block referencing additional
                transactions
              </p>
              <p>
                Ouroboros Leios achieves higher transaction throughput by
                allowing block producers to create additional blocks alongside
                the regular Praos chain. These supplementary blocks, called{" "}
                <Link
                  to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#endorser-blocks-ebs"
                  target="_blank"
                  rel="noopener noreferrer"
                >
                  <strong>Endorser Blocks (EBs)</strong>
                </Link>
                , reference extra transactions that would otherwise wait for the
                standard Praos blocks (called{" "}
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
                To ensure data availability and correctness, these blocks
                undergo{" "}
                <Link
                  to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#step-3-committee-validation"
                  target="_blank"
                  rel="noopener noreferrer"
                >
                  committee validation
                </Link>{" "}
                before their transactions become part of the permanent ledger.
                The key insight is that we can maintain Praos's security
                guarantees while processing more transactions by carefully
                managing when and how these additional blocks are validated and
                included in the chain.
              </p>
              <p>
                EB inclusion is opportunistic rather than guaranteed, depending
                on the random timing of block production relative to the
                certification process. This design preserves the existing Praos
                chain structure while adding substantial transaction capacity
                through the secondary validation pathway.
              </p>
              <div className={styles.howLeiosWorksContentinkButton}>
                <LinkButton
                  text="Read the Technical Details"
                  url="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#specification"
                  target="_blank"
                  rel="noopener noreferrer"
                />
              </div>
            </div>
            <div className={styles.svgContainer}>
              <HowLeiosWorksGraphic />
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
      const rawCountdown = formatCountdown(
        target.getTime() - now.getTime(),
        live,
      );
      //@ts-ignore
      setCountdown(highlightNumbers(rawCountdown));
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
    <section id="next" className="homepage-section-secondary">
      <div className="container">
        <div className="container-padding padding-section">
          <div className={styles.contentWrapper}>
            <div className={styles.stayUpToDateContent}>
              <h2 style={{ marginBottom: "1.25rem" }}>Stay up to date</h2>
              <p>
                Catch up on the latest Leios progress, key decisions, and Q&A in
                our monthly review videos
              </p>
              <Link
                style={{ justifySelf: "flex-end", marginTop: "auto" }}
                to="/docs/development/monthly-reviews"
              >
                Catch up on past reviews
              </Link>
            </div>
            <div className={styles.reviewMeetingContaner}>
              <div className={styles.backgroundGrid} />
              <div className={styles.cameraImageContainer}>
                <img src={VideoCamUrl} />
              </div>
              <div className={styles.countdownContainer}>
                <Link
                  className={styles.countdown}
                  to="https://youtube.com/live/rraKzt-JIqM"
                  target="_blank"
                  rel="noopener noreferrer"
                >
                  <span>{isLive ? "Join Live" : "Watch Live"}</span>
                  {!isLive && <span>{countdown}</span>}
                </Link>
                {!isLive && (
                  <>
                    <span className={styles.countdownLabel}>
                      Next review meeting:
                    </span>
                    <span className={styles.reviewDate}>{nextDate}</span>
                  </>
                )}
              </div>
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
