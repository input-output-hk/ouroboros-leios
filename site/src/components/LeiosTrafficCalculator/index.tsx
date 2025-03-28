import React, { useEffect, useMemo, useRef, useState } from "react";
import styles from "./styles.module.css";

interface CloudProvider {
    name: string;
    egressCost: number;
    freeAllowance: string;
}

interface SortConfig {
    key: string;
    direction: "asc" | "desc";
}

const cloudProviders: CloudProvider[] = [
    { name: "Google Cloud", egressCost: 0.120, freeAllowance: "0" },
    { name: "Railway", egressCost: 0.100, freeAllowance: "0" },
    { name: "AWS", egressCost: 0.090, freeAllowance: "100" },
    { name: "Microsoft Azure", egressCost: 0.087, freeAllowance: "100" },
    { name: "Alibaba Cloud", egressCost: 0.074, freeAllowance: "10" },
    { name: "DigitalOcean", egressCost: 0.010, freeAllowance: "100–10,000" },
    { name: "Oracle Cloud", egressCost: 0.0085, freeAllowance: "10,240" },
    { name: "Linode", egressCost: 0.005, freeAllowance: "1,024–20,480" },
    { name: "Hetzner", egressCost: 0.00108, freeAllowance: "1,024" },
    { name: "UpCloud", egressCost: 0, freeAllowance: "1,024–24,576" },
];

const IB_RATES = [1, 5, 10, 20, 30];
const SECONDS_PER_MONTH = 2_592_000; // 30 days

interface BlockSizes {
    ib: { header: number; body: number };
    eb: { header: number; body: number };
    rb: { header: number; body: number };
    vote: { size: number; countPerPipeline: number };
}

const blockSizes: BlockSizes = {
    ib: { header: 304, body: 98304 },
    eb: { header: 240, body: 32 },
    rb: { header: 1024, body: 90112 },
    vote: { size: 150, countPerPipeline: 900 }, // 600 votes per pipeline * 1.5 EBs per pipeline
};

const TX_FEE_PARAMS = {
    a: 0.155381, // Fixed fee in ADA
    b: 0.000043946, // Fee per byte in ADA
    avgTxSize: 1400, // Average size based on mainnet data (Epoch 500+)
};

interface BlockTraffic {
    headers: number;
    bodies: number;
}

interface VoteTraffic {
    votes: number;
}

interface TrafficBreakdown {
    ib: BlockTraffic;
    eb: BlockTraffic;
    rb: BlockTraffic;
    votes: VoteTraffic;
}

const LeiosTrafficCalculator: React.FC = () => {
    const [numPeers, setNumPeers] = useState(20);
    const [headerPropagationPercent, setHeaderPropagationPercent] = useState(
        100,
    );
    const [bodyRequestPercent, setBodyRequestPercent] = useState(25);
    const [blockUtilizationPercent, setBlockUtilizationPercent] = useState(100);
    const [adaToUsd, setAdaToUsd] = useState(0.5);
    const [totalNodes, setTotalNodes] = useState(10000);
    const [treasuryTaxRate, setTreasuryTaxRate] = useState(20);
    const [sortConfig, setSortConfig] = useState<SortConfig>({
        key: "egressCost",
        direction: "desc",
    });
    const [isSidebarOpen, setIsSidebarOpen] = useState(false);
    const [isToggleVisible, setIsToggleVisible] = useState(false);
    const controlsRef = useRef<HTMLDivElement>(null);

    useEffect(() => {
        const handleScroll = () => {
            if (controlsRef.current) {
                const controlsBottom =
                    controlsRef.current.getBoundingClientRect().bottom;
                setIsToggleVisible(controlsBottom < 0);
            }
        };

        window.addEventListener("scroll", handleScroll);
        return () => window.removeEventListener("scroll", handleScroll);
    }, []);

    const calculateTraffic = (
        ibRate: number,
    ): {
        traffic: TrafficBreakdown;
        totalTraffic: number;
        txFeeADA: number;
        totalTxs: number;
    } => {
        const ibCount = ibRate * SECONDS_PER_MONTH;
        const stagesPerMonth = SECONDS_PER_MONTH / 20;
        const ebRate = 1.5; // EBs per pipeline
        const ebCount = stagesPerMonth * ebRate;
        const rbCount = 0.05 * SECONDS_PER_MONTH;

        const headerPeers = Math.round(
            numPeers * (headerPropagationPercent / 100),
        );
        const bodyPeers = Math.round(numPeers * (bodyRequestPercent / 100));

        const traffic: TrafficBreakdown = {
            ib: {
                headers: ibCount * blockSizes.ib.header * headerPeers,
                bodies: ibCount * blockSizes.ib.body *
                    (blockUtilizationPercent / 100) * bodyPeers,
            },
            eb: {
                headers: ibRate * blockSizes.eb.header * ebRate * headerPeers *
                    stagesPerMonth,
                bodies: ibRate * blockSizes.eb.body * ebRate * bodyPeers *
                    stagesPerMonth,
            },
            rb: {
                headers: rbCount * blockSizes.rb.header * headerPeers,
                bodies: rbCount * blockSizes.rb.body * bodyPeers,
            },
            votes: {
                votes: ebCount * blockSizes.vote.size *
                    blockSizes.vote.countPerPipeline * headerPeers,
            },
        };

        const totalTraffic = Object.values(traffic).reduce(
            (acc, block) => {
                if ("votes" in block) {
                    return acc + block.votes;
                }
                return acc + block.headers + block.bodies;
            },
            0,
        );

        // Calculate transaction fees
        const txPerIB = Math.floor(
            (blockSizes.ib.body * (blockUtilizationPercent / 100)) /
                TX_FEE_PARAMS.avgTxSize,
        );
        const totalTxs = ibCount * txPerIB;
        // Calculate fee per transaction exactly: a + (b * avgTxSize)
        const feePerTx = TX_FEE_PARAMS.a +
            (TX_FEE_PARAMS.b * TX_FEE_PARAMS.avgTxSize);
        // Calculate total fees without any intermediate rounding
        const txFeeADA = totalTxs * feePerTx;

        return {
            traffic,
            totalTraffic,
            txFeeADA,
            totalTxs,
        };
    };

    const calculateCost = (trafficGB: number, provider: CloudProvider) => {
        const freeAllowance = parseInt(provider.freeAllowance.split("–")[0]);
        const billableGB = Math.max(0, trafficGB - freeAllowance);
        return billableGB * provider.egressCost;
    };

    const handleSort = (key: string) => {
        setSortConfig((prevConfig) => ({
            key,
            direction: prevConfig.key === key && prevConfig.direction === "asc"
                ? "desc"
                : "asc",
        }));
    };

    const sortedProviders = useMemo(() => {
        return [...cloudProviders].sort((a, b) => {
            if (sortConfig.key === "name") {
                return sortConfig.direction === "asc"
                    ? a.name.localeCompare(b.name)
                    : b.name.localeCompare(a.name);
            }
            if (sortConfig.key === "egressCost") {
                return sortConfig.direction === "asc"
                    ? a.egressCost - b.egressCost
                    : b.egressCost - a.egressCost;
            }
            if (sortConfig.key === "freeAllowance") {
                const aAllowance = parseInt(a.freeAllowance.split("–")[0]);
                const bAllowance = parseInt(b.freeAllowance.split("–")[0]);
                return sortConfig.direction === "asc"
                    ? aAllowance - bAllowance
                    : bAllowance - aAllowance;
            }
            if (sortConfig.key.startsWith("ib_")) {
                const rate = parseInt(sortConfig.key.split("_")[1]);
                const { totalTraffic: aTotal } = calculateTraffic(rate);
                const { totalTraffic: bTotal } = calculateTraffic(rate);
                const aCost = calculateCost(aTotal / 1e9, a);
                const bCost = calculateCost(bTotal / 1e9, b);
                return sortConfig.direction === "asc"
                    ? aCost - bCost
                    : bCost - aCost;
            }
            return 0;
        });
    }, [sortConfig]);

    const getSortIcon = (key: string) => {
        if (sortConfig.key !== key) return "↕️";
        return sortConfig.direction === "asc" ? "↑" : "↓";
    };

    const formatTraffic = (bytes: number) => {
        if (bytes >= 1024 * 1024 * 1024 * 1024) {
            return (bytes / (1024 * 1024 * 1024 * 1024)).toFixed(2) + " TiB";
        } else if (bytes >= 1024 * 1024 * 1024) {
            return (bytes / (1024 * 1024 * 1024)).toFixed(2) + " GiB";
        } else if (bytes >= 1024 * 1024) {
            return (bytes / (1024 * 1024)).toFixed(2) + " MiB";
        } else {
            return (bytes / 1024).toFixed(2) + " KiB";
        }
    };

    const formatTrafficForTable = (bytes: number) => {
        if (bytes >= 1024 * 1024 * 1024 * 1024) {
            return (bytes / (1024 * 1024 * 1024 * 1024)).toFixed(2);
        } else if (bytes >= 1024 * 1024 * 1024) {
            return (bytes / (1024 * 1024 * 1024)).toFixed(2);
        } else if (bytes >= 1024 * 1024) {
            return (bytes / (1024 * 1024)).toFixed(2);
        } else {
            return (bytes / 1024).toFixed(2);
        }
    };

    const Controls: React.FC<{ idPrefix?: string }> = ({ idPrefix = "" }) => (
        <div className={styles.controls}>
            <div className={styles.controlGroup}>
                <h4>Network Parameters</h4>
                <div className={styles.control}>
                    <label htmlFor={`${idPrefix}numPeers`}>
                        Number of Peers:
                    </label>
                    <input
                        type="number"
                        id={`${idPrefix}numPeers`}
                        value={numPeers}
                        onChange={(e) => setNumPeers(parseInt(e.target.value))}
                        min="1"
                    />
                </div>
                <div className={styles.control}>
                    <label htmlFor={`${idPrefix}totalNodes`}>
                        Total Network Nodes:
                    </label>
                    <input
                        type="number"
                        id={`${idPrefix}totalNodes`}
                        value={totalNodes}
                        onChange={(e) =>
                            setTotalNodes(parseInt(e.target.value))}
                        min="1"
                    />
                </div>
            </div>

            <div className={styles.controlGroup}>
                <h4>Block Parameters</h4>
                <div className={styles.control}>
                    <label htmlFor={`${idPrefix}headerPropagation`}>
                        Header Propagation (% of peers):
                    </label>
                    <input
                        type="number"
                        id={`${idPrefix}headerPropagation`}
                        value={headerPropagationPercent}
                        onChange={(e) =>
                            setHeaderPropagationPercent(
                                parseInt(e.target.value),
                            )}
                        min="0"
                        max="100"
                    />
                </div>
                <div className={styles.control}>
                    <label htmlFor={`${idPrefix}bodyRequest`}>
                        Body Request (% of peers):
                    </label>
                    <input
                        type="number"
                        id={`${idPrefix}bodyRequest`}
                        value={bodyRequestPercent}
                        onChange={(e) =>
                            setBodyRequestPercent(parseInt(e.target.value))}
                        min="0"
                        max="100"
                    />
                </div>
                <div className={styles.control}>
                    <label htmlFor={`${idPrefix}blockUtilization`}>
                        Input Block Utilization (%):
                    </label>
                    <input
                        type="number"
                        id={`${idPrefix}blockUtilization`}
                        value={blockUtilizationPercent}
                        onChange={(e) =>
                            setBlockUtilizationPercent(
                                parseInt(e.target.value),
                            )}
                        min="0"
                        max="100"
                    />
                </div>
            </div>

            <div className={styles.controlGroup}>
                <h4>Economic Parameters</h4>
                <div className={styles.control}>
                    <label htmlFor={`${idPrefix}adaToUsd`}>
                        ADA/USD Price:
                    </label>
                    <input
                        type="number"
                        id={`${idPrefix}adaToUsd`}
                        value={adaToUsd}
                        onChange={(e) =>
                            setAdaToUsd(parseFloat(e.target.value))}
                        min="0"
                        step="0.01"
                    />
                </div>
                <div className={styles.control}>
                    <label htmlFor={`${idPrefix}treasuryTaxRate`}>
                        Treasury Tax Rate (%):
                    </label>
                    <input
                        type="number"
                        id={`${idPrefix}treasuryTaxRate`}
                        value={treasuryTaxRate}
                        onChange={(e) =>
                            setTreasuryTaxRate(parseInt(e.target.value))}
                        min="0"
                        max="100"
                    />
                </div>
            </div>
        </div>
    );

    return (
        <div
            className={`${styles.container} ${
                isSidebarOpen ? styles.sidebarOpen : ""
            }`}
        >
            <div ref={controlsRef}>
                <Controls idPrefix="top-" />
            </div>

            <button
                className={`${styles.sidebarToggle} ${
                    isToggleVisible ? styles.visible : ""
                }`}
                onClick={() => setIsSidebarOpen(!isSidebarOpen)}
            >
                {isSidebarOpen ? "Hide Parameters" : "Show Parameters"}
            </button>

            <div
                className={`${styles.sidebar} ${
                    isSidebarOpen ? styles.open : ""
                }`}
            >
                <div className={styles.sidebarHeader}>
                    <h3>Parameters</h3>
                    <button
                        className={styles.closeButton}
                        onClick={() => setIsSidebarOpen(false)}
                    >
                        ×
                    </button>
                </div>
                <div className={styles.sidebarControls}>
                    <Controls idPrefix="sidebar-" />
                </div>
            </div>

            <div className={styles.calculationBreakdown}>
                <h3>Calculation Breakdown</h3>
                <div className={styles.breakdownGrid}>
                    <div className={styles.breakdownItem}>
                        <h4>General Parameters</h4>
                        <div className={styles.calculationSection}>
                            <div className={styles.calculationTitle}>
                                Time Period
                            </div>
                            <div className={styles.calculationCode}>
                                Seconds/Month ={" "}
                                {SECONDS_PER_MONTH.toLocaleString()}
                            </div>
                            <div className={styles.calculationTitle}>
                                Peer Distribution
                            </div>
                            <div className={styles.calculationCode}>
                                Header Peers = {numPeers} ×{" "}
                                {headerPropagationPercent}% = {Math.round(
                                    numPeers * (headerPropagationPercent / 100),
                                )}
                                {"\n"}Body Peers = {numPeers} ×{" "}
                                {bodyRequestPercent}% = {Math.round(
                                    numPeers * (bodyRequestPercent / 100),
                                )}
                            </div>
                            <div className={styles.calculationTitle}>
                                Transaction Parameters
                            </div>
                            <div className={styles.calculationCode}>
                                Avg Tx Size = {TX_FEE_PARAMS.avgTxSize} bytes
                                {"\n"}Base Fee = {TX_FEE_PARAMS.a} ₳
                                {"\n"}Fee/Byte = {TX_FEE_PARAMS.b} ₳
                                {"\n"}Txs/IB = {Math.floor(
                                    (blockSizes.ib.body *
                                        (blockUtilizationPercent / 100)) /
                                        TX_FEE_PARAMS.avgTxSize,
                                )} Txs
                                {"\n"}Fee/Tx = {(TX_FEE_PARAMS.a +
                                    TX_FEE_PARAMS.b * TX_FEE_PARAMS.avgTxSize)
                                    .toFixed(6)} ₳
                            </div>
                        </div>
                    </div>
                    <div className={styles.breakdownItem}>
                        <h4>Block Timing</h4>
                        <div className={styles.calculationSection}>
                            <div className={styles.calculationTitle}>
                                Endorsement Blocks (EB)
                            </div>
                            <div className={styles.calculationCode}>
                                Stage Length = 20 secs{"\n"}Stages/Month ={" "}
                                {(SECONDS_PER_MONTH / 20).toLocaleString()}{" "}
                                stages{"\n"}EBs/Stage = 1.5{"\n"}EBs/Month =
                                {" "}
                                {((SECONDS_PER_MONTH / 20) * 1.5)
                                    .toLocaleString()} EBs
                            </div>
                            <div className={styles.calculationTitle}>
                                Ranking Blocks (RB)
                            </div>
                            <div className={styles.calculationCode}>
                                RB/sec = 0.05{"\n"}RBs/month ={" "}
                                {(0.05 * SECONDS_PER_MONTH).toLocaleString()}
                                {" "}
                                RBs
                            </div>
                        </div>
                    </div>
                    <div className={styles.breakdownItem}>
                        <h4>Block Sizes</h4>
                        <div className={styles.calculationSection}>
                            <div className={styles.calculationTitle}>
                                Input Blocks (IB)
                            </div>
                            <div className={styles.calculationCode}>
                                Header Size = {blockSizes.ib.header} bytes{" "}
                                {"\n"}Body Size ={" "}
                                {blockSizes.ib.body.toLocaleString()} bytes
                            </div>
                            <div className={styles.calculationTitle}>
                                Endorsement Blocks (EB)
                            </div>
                            <div className={styles.calculationCode}>
                                Header Size = {blockSizes.eb.header} bytes{" "}
                                {"\n"}Body Size = {blockSizes.eb.body}{" "}
                                bytes/IB ref
                            </div>
                            <div className={styles.calculationTitle}>
                                Votes
                            </div>
                            <div className={styles.calculationCode}>
                                Vote Size = {blockSizes.vote.size} bytes{" "}
                                {"\n"}Votes per Pipeline ={" "}
                                {blockSizes.vote.countPerPipeline}{" "}
                                votes (600 votes × 1.5 EBs)
                            </div>
                            <div className={styles.calculationTitle}>
                                Ranking Blocks (RB)
                            </div>
                            <div className={styles.calculationCode}>
                                Header Size = {blockSizes.rb.header} bytes{" "}
                                {"\n"}Body Size ={" "}
                                {blockSizes.rb.body.toLocaleString()} bytes
                            </div>
                        </div>
                    </div>
                </div>
                <div className={styles.calculationNote}>
                    <p>Example calculation for 1 IB/s:</p>
                    <ul>
                        <li>
                            IB Headers: {SECONDS_PER_MONTH.toLocaleString()}
                            {" "}
                            secs × {blockSizes.ib.header} bytes × {Math.round(
                                numPeers * (headerPropagationPercent / 100),
                            )} peers = {formatTraffic(
                                SECONDS_PER_MONTH * blockSizes.ib.header *
                                    Math.round(
                                        numPeers *
                                            (headerPropagationPercent / 100),
                                    ),
                            )}
                        </li>
                        <li>
                            IB Bodies: {SECONDS_PER_MONTH.toLocaleString()}{" "}
                            secs × {blockSizes.ib.body.toLocaleString()} bytes ×
                            {" "}
                            {blockUtilizationPercent}% utilization ×{" "}
                            {Math.round(numPeers * (bodyRequestPercent / 100))}
                            {" "}
                            peers = {formatTraffic(
                                SECONDS_PER_MONTH * blockSizes.ib.body *
                                    (blockUtilizationPercent / 100) *
                                    Math.round(
                                        numPeers * (bodyRequestPercent / 100),
                                    ),
                            )}
                        </li>
                        <li>
                            EB Headers:{" "}
                            {((SECONDS_PER_MONTH / 20) * 1.5).toLocaleString()}
                            {" "}
                            seconds × {blockSizes.eb.header} bytes ×{" "}
                            {Math.round(
                                numPeers * (headerPropagationPercent / 100),
                            )} peers = {formatTraffic(
                                (SECONDS_PER_MONTH / 20) * 1.5 *
                                    blockSizes.eb.header *
                                    Math.round(
                                        numPeers *
                                            (headerPropagationPercent / 100),
                                    ),
                            )}
                        </li>
                        <li>
                            EB Bodies: 1 IB/s × {blockSizes.eb.body}{" "}
                            bytes × 1.5 EBs ×{" "}
                            {Math.round(numPeers * (bodyRequestPercent / 100))}
                            {" "}
                            peers × {(SECONDS_PER_MONTH / 20).toLocaleString()}
                            {" "}
                            stages = {formatTraffic(
                                1 * blockSizes.eb.body * 1.5 *
                                    Math.round(
                                        numPeers * (bodyRequestPercent / 100),
                                    ) *
                                    (SECONDS_PER_MONTH / 20),
                            )}
                        </li>
                        <li>
                            Votes:{" "}
                            {((SECONDS_PER_MONTH / 20) * 1.5).toLocaleString()}
                            {" "}
                            seconds × {blockSizes.vote.size} bytes ×{" "}
                            {blockSizes.vote.countPerPipeline} votes ×{" "}
                            {Math.round(
                                numPeers * (headerPropagationPercent / 100),
                            )} peers = {formatTraffic(
                                (SECONDS_PER_MONTH / 20) * 1.5 *
                                    blockSizes.vote.size *
                                    blockSizes.vote.countPerPipeline *
                                    Math.round(
                                        numPeers *
                                            (headerPropagationPercent / 100),
                                    ),
                            )}
                        </li>
                        <li>
                            RB Headers:{" "}
                            {(0.05 * SECONDS_PER_MONTH).toLocaleString()}{" "}
                            seconds × {blockSizes.rb.header} bytes ×{" "}
                            {Math.round(
                                numPeers * (headerPropagationPercent / 100),
                            )} peers = {formatTraffic(
                                0.05 * SECONDS_PER_MONTH *
                                    blockSizes.rb.header *
                                    Math.round(
                                        numPeers *
                                            (headerPropagationPercent / 100),
                                    ),
                            )}
                        </li>
                        <li>
                            RB Bodies:{" "}
                            {(0.05 * SECONDS_PER_MONTH).toLocaleString()}{" "}
                            seconds × {blockSizes.rb.body.toLocaleString()}{" "}
                            bytes ×{" "}
                            {Math.round(numPeers * (bodyRequestPercent / 100))}
                            {" "}
                            peers = {formatTraffic(
                                0.05 * SECONDS_PER_MONTH * blockSizes.rb.body *
                                    Math.round(
                                        numPeers * (bodyRequestPercent / 100),
                                    ),
                            )}
                        </li>
                        <li>
                            Transactions per IB:{" "}
                            {blockSizes.ib.body.toLocaleString()} bytes ×{" "}
                            {blockUtilizationPercent}% utilization ÷{" "}
                            {TX_FEE_PARAMS.avgTxSize} bytes/tx = {Math.floor(
                                (blockSizes.ib.body *
                                    (blockUtilizationPercent / 100)) /
                                    TX_FEE_PARAMS.avgTxSize,
                            )} txs
                        </li>
                        <li>
                            Monthly Transactions: {Math.floor(
                                (blockSizes.ib.body *
                                    (blockUtilizationPercent / 100)) /
                                    TX_FEE_PARAMS.avgTxSize,
                            )} txs/block × {SECONDS_PER_MONTH.toLocaleString()}
                            {" "}
                            blocks = {(SECONDS_PER_MONTH *
                                Math.floor(
                                    (blockSizes.ib.body *
                                        (blockUtilizationPercent / 100)) /
                                        TX_FEE_PARAMS.avgTxSize,
                                )).toLocaleString()} txs
                        </li>
                        <li>
                            Fee per Transaction: {TX_FEE_PARAMS.a}{" "}
                            ₳ + ({TX_FEE_PARAMS.b} ₳/byte ×{" "}
                            {TX_FEE_PARAMS.avgTxSize} bytes) ={" "}
                            {(TX_FEE_PARAMS.a +
                                TX_FEE_PARAMS.b * TX_FEE_PARAMS.avgTxSize)
                                .toFixed(6)} ₳
                        </li>
                        <li>
                            Monthly Fee Revenue: {(SECONDS_PER_MONTH *
                                Math.floor(
                                    (blockSizes.ib.body *
                                        (blockUtilizationPercent / 100)) /
                                        TX_FEE_PARAMS.avgTxSize,
                                )).toLocaleString()} txs × {(TX_FEE_PARAMS.a +
                                    TX_FEE_PARAMS.b * TX_FEE_PARAMS.avgTxSize)
                                .toFixed(6)} ₳ = {(SECONDS_PER_MONTH *
                                    Math.floor(
                                        (blockSizes.ib.body *
                                            (blockUtilizationPercent / 100)) /
                                            TX_FEE_PARAMS.avgTxSize,
                                    ) *
                                    (TX_FEE_PARAMS.a +
                                        TX_FEE_PARAMS.b *
                                            TX_FEE_PARAMS.avgTxSize))
                                .toLocaleString()} ₳
                        </li>
                    </ul>
                </div>
            </div>

            <h3>Monthly Traffic and Network Fees</h3>
            <div className={styles.tableContainer}>
                <table className={styles.table}>
                    <thead>
                        <tr>
                            <th>IB/s</th>
                            <th>IB Headers</th>
                            <th>IB Bodies</th>
                            <th>EB Headers</th>
                            <th>EB Bodies</th>
                            <th>Votes</th>
                            <th>RB Headers</th>
                            <th>RB Bodies</th>
                            <th>Total Traffic</th>
                            <th>Total Txs</th>
                        </tr>
                    </thead>
                    <tbody>
                        {IB_RATES.map((rate) => {
                            const {
                                traffic,
                                totalTraffic,
                                totalTxs,
                            } = calculateTraffic(rate);
                            return (
                                <tr key={rate}>
                                    <td>{rate}</td>
                                    <td>{formatTraffic(traffic.ib.headers)}</td>
                                    <td>{formatTraffic(traffic.ib.bodies)}</td>
                                    <td>{formatTraffic(traffic.eb.headers)}</td>
                                    <td>{formatTraffic(traffic.eb.bodies)}</td>
                                    <td>
                                        {formatTraffic(traffic.votes.votes)}
                                    </td>
                                    <td>{formatTraffic(traffic.rb.headers)}</td>
                                    <td>{formatTraffic(traffic.rb.bodies)}</td>
                                    <td>{formatTraffic(totalTraffic)}</td>
                                    <td>{totalTxs.toLocaleString()}</td>
                                </tr>
                            );
                        })}
                    </tbody>
                </table>
                <div className={styles.note}>
                    <div className={styles.noteTitle}>Network Revenue</div>
                    <div className={styles.noteContent}>
                        Transaction fees shown represent total network revenue
                        before expenses and taxes. Actual earnings depend on:
                        <ul>
                            <li>Node operator's stake percentage</li>
                            <li>
                                SPO's pool configuration (fixed & margin fees)
                            </li>
                            <li>Treasury tax (20%)</li>
                            <li>Other operational costs</li>
                        </ul>
                    </div>
                </div>
            </div>

            <h3>Monthly Node Egress Cost by Cloud Provider ($)</h3>
            <div className={styles.tableContainer}>
                <table className={styles.table}>
                    <thead>
                        <tr>
                            <th
                                onClick={() => handleSort("name")}
                                className={styles.sortable}
                            >
                                Provider {getSortIcon("name")}
                            </th>
                            <th
                                onClick={() => handleSort("egressCost")}
                                className={styles.sortable}
                            >
                                Price/GiB {getSortIcon("egressCost")}
                            </th>
                            <th
                                onClick={() => handleSort("freeAllowance")}
                                className={styles.sortable}
                            >
                                Free Allowance (GiB){" "}
                                {getSortIcon("freeAllowance")}
                            </th>
                            {IB_RATES.map((rate) => (
                                <th
                                    key={rate}
                                    onClick={() => handleSort(`ib_${rate}`)}
                                    className={styles.sortable}
                                >
                                    {rate} IB/s {getSortIcon(`ib_${rate}`)}
                                </th>
                            ))}
                        </tr>
                    </thead>
                    <tbody>
                        {sortedProviders.map((provider) => (
                            <tr key={provider.name}>
                                <td>{provider.name}</td>
                                <td>${provider.egressCost.toFixed(3)}</td>
                                <td>{provider.freeAllowance}</td>
                                {IB_RATES.map((rate) => {
                                    const { totalTraffic } = calculateTraffic(
                                        rate,
                                    );
                                    const egressCost = calculateCost(
                                        totalTraffic / 1e9,
                                        provider,
                                    );
                                    return (
                                        <td key={rate}>
                                            ${egressCost.toLocaleString(
                                                undefined,
                                                {
                                                    minimumFractionDigits: 2,
                                                    maximumFractionDigits: 2,
                                                },
                                            )}
                                        </td>
                                    );
                                })}
                            </tr>
                        ))}
                    </tbody>
                </table>
                <div className={styles.note}>
                    <div className={styles.noteTitle}>
                        Cloud Provider Selection
                    </div>
                    <div className={styles.noteContent}>
                        This cost comparison is for informational purposes only.
                        Beyond cost, consider:
                        <ul>
                            <li>Geographic availability and latency</li>
                            <li>Service reliability and support</li>
                            <li>Security and compliance features</li>
                            <li>Network performance and scalability</li>
                        </ul>
                        Hyperscale providers may offer advantages that justify
                        higher costs for production operations.
                    </div>
                </div>
            </div>

            <h3>Estimated Monthly Node Income*</h3>
            <div className={styles.tableContainer}>
                <table className={styles.table}>
                    <thead>
                        <tr>
                            <th>IB/s</th>
                            <th>Total Txs</th>
                            <th>Gross Network Revenue (₳)</th>
                            <th>After Treasury Tax (₳)</th>
                            <th>Per Node (₳)</th>
                            <th>Per Node (USD)</th>
                        </tr>
                    </thead>
                    <tbody>
                        {IB_RATES.map((rate) => {
                            const { txFeeADA, totalTxs } = calculateTraffic(
                                rate,
                            );
                            const afterTax = txFeeADA *
                                (1 - treasuryTaxRate / 100);
                            const perNode = afterTax / totalNodes;
                            return (
                                <tr key={rate}>
                                    <td>{rate}</td>
                                    <td>{totalTxs.toLocaleString()}</td>
                                    <td>
                                        {txFeeADA.toLocaleString(undefined, {
                                            minimumFractionDigits: 0,
                                            maximumFractionDigits: 6,
                                        }).replace(/\.?0+$/, "")} ₳
                                    </td>
                                    <td>
                                        {afterTax.toLocaleString(undefined, {
                                            minimumFractionDigits: 0,
                                            maximumFractionDigits: 6,
                                        }).replace(/\.?0+$/, "")} ₳
                                    </td>
                                    <td>
                                        {perNode.toLocaleString(undefined, {
                                            minimumFractionDigits: 0,
                                            maximumFractionDigits: 6,
                                        }).replace(/\.?0+$/, "")} ₳
                                    </td>
                                    <td>
                                        ${(perNode * adaToUsd).toLocaleString(
                                            undefined,
                                            {
                                                minimumFractionDigits: 2,
                                            },
                                        )}
                                    </td>
                                </tr>
                            );
                        })}
                    </tbody>
                </table>
                <div className={styles.note}>
                    <div className={styles.noteTitle}>
                        Estimated Node Income Disclaimer
                    </div>
                    <div className={styles.noteContent}>
                        These estimates are based on <b>several assumptions</b>:
                        <ul>
                            <li>
                                Equal distribution of rewards across all nodes
                            </li>
                            <li>No additional operational costs</li>
                            <li>No pool fees or other deductions</li>
                            <li>Constant ADA/USD price</li>
                            <li>
                                Network topology: Based on current mainnet
                                (~3,000 BP nodes), we estimate ~10,000 total
                                nodes to account for:
                                <ul>
                                    <li>BP nodes (behind relays)</li>
                                    <li>
                                        Relay nodes (typically 2+ per BP node)
                                    </li>
                                    <li>
                                        Additional relays for dApps and
                                        infrastructure
                                    </li>
                                    <li>Full node wallets</li>
                                </ul>
                                SPOs can multiply the per-node income by their
                                total number of nodes (BP + relays) to estimate
                                their total income.
                            </li>
                            <li>
                                Transaction fee calculation parameters (base fee
                                and per-byte fee) remain constant, though these
                                may be adjusted through governance
                            </li>
                        </ul>
                    </div>
                </div>
            </div>
        </div>
    );
};

export default LeiosTrafficCalculator;
