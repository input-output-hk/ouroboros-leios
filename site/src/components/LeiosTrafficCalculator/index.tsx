import React, { useMemo, useState } from "react";
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
}

const blockSizes: BlockSizes = {
    ib: { header: 304, body: 98304 },
    eb: { header: 240, body: 32 },
    rb: { header: 1024, body: 90112 },
};

const TX_FEE_PARAMS = {
    a: 0.155381, // Fixed fee in ADA
    b: 0.000043946, // Fee per byte in ADA
    avgTxSize: 300, // Average transaction size in bytes
};

const LeiosTrafficCalculator: React.FC = () => {
    const [numPeers, setNumPeers] = useState(20);
    const [headerPropagationPercent, setHeaderPropagationPercent] = useState(
        100,
    );
    const [bodyRequestPercent, setBodyRequestPercent] = useState(25);
    const [blockUtilizationPercent, setBlockUtilizationPercent] = useState(100);
    const [adaToUsd, setAdaToUsd] = useState(0.5);
    const [sortConfig, setSortConfig] = useState<SortConfig>({
        key: "egressCost",
        direction: "desc",
    });

    const calculateTraffic = (ibRate: number) => {
        const ibCount = ibRate * SECONDS_PER_MONTH;
        const stagesPerMonth = SECONDS_PER_MONTH / 20;
        const ebCount = stagesPerMonth * 1.5;
        const rbCount = 0.05 * SECONDS_PER_MONTH;

        const headerPeers = Math.round(
            numPeers * (headerPropagationPercent / 100),
        );
        const bodyPeers = Math.round(numPeers * (bodyRequestPercent / 100));

        const traffic = {
            ib: {
                headers: ibCount * blockSizes.ib.header * headerPeers,
                bodies: ibCount * blockSizes.ib.body *
                    (blockUtilizationPercent / 100) * bodyPeers,
            },
            eb: {
                headers: ebCount * blockSizes.eb.header * headerPeers,
                bodies: ebCount * blockSizes.eb.body * (ibRate * 20) *
                    bodyPeers,
            },
            rb: {
                headers: rbCount * blockSizes.rb.header * headerPeers,
                bodies: rbCount * blockSizes.rb.body * bodyPeers,
            },
        };

        const totalTraffic = Object.values(traffic).reduce(
            (acc, block) => acc + block.headers + block.bodies,
            0,
        );

        // Calculate transaction fees
        const txPerIB = Math.floor(
            (blockSizes.ib.body * (blockUtilizationPercent / 100)) /
                TX_FEE_PARAMS.avgTxSize,
        );
        const totalTxs = ibCount * txPerIB;
        const txFeeADA = totalTxs *
            (TX_FEE_PARAMS.a + TX_FEE_PARAMS.b * TX_FEE_PARAMS.avgTxSize);
        const txFeeUSD = txFeeADA * adaToUsd;

        return {
            traffic,
            totalTraffic,
            txFeeADA,
            txFeeUSD,
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
        if (bytes >= 1e12) {
            return (bytes / 1e12).toFixed(2) + " TB";
        } else if (bytes >= 1e9) {
            return (bytes / 1e9).toFixed(2) + " GB";
        } else if (bytes >= 1e6) {
            return (bytes / 1e6).toFixed(2) + " MB";
        } else {
            return (bytes / 1e3).toFixed(2) + " KB";
        }
    };

    const formatTrafficForTable = (bytes: number) => {
        if (bytes >= 1e12) {
            return (bytes / 1e12).toFixed(2);
        } else if (bytes >= 1e9) {
            return (bytes / 1e9).toFixed(2);
        } else if (bytes >= 1e6) {
            return (bytes / 1e6).toFixed(2);
        } else {
            return (bytes / 1e3).toFixed(2);
        }
    };

    const getTrafficUnit = (bytes: number) => {
        if (bytes >= 1e12) {
            return "TB";
        } else if (bytes >= 1e9) {
            return "GB";
        } else if (bytes >= 1e6) {
            return "MB";
        } else {
            return "KB";
        }
    };

    return (
        <div className={styles.container}>
            <div className={styles.controls}>
                <div className={styles.control}>
                    <label htmlFor="numPeers">Number of Peers:</label>
                    <input
                        type="number"
                        id="numPeers"
                        value={numPeers}
                        onChange={(e) => setNumPeers(parseInt(e.target.value))}
                        min="1"
                    />
                </div>
                <div className={styles.control}>
                    <label htmlFor="headerPropagation">
                        Header Propagation (% of peers):
                    </label>
                    <input
                        type="number"
                        id="headerPropagation"
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
                    <label htmlFor="bodyRequest">
                        Body Request (% of peers):
                    </label>
                    <input
                        type="number"
                        id="bodyRequest"
                        value={bodyRequestPercent}
                        onChange={(e) =>
                            setBodyRequestPercent(parseInt(e.target.value))}
                        min="0"
                        max="100"
                    />
                </div>
                <div className={styles.control}>
                    <label htmlFor="blockUtilization">
                        Input Block Utilization (%):
                    </label>
                    <input
                        type="number"
                        id="blockUtilization"
                        value={blockUtilizationPercent}
                        onChange={(e) =>
                            setBlockUtilizationPercent(
                                parseInt(e.target.value),
                            )}
                        min="0"
                        max="100"
                    />
                </div>
                <div className={styles.control}>
                    <label htmlFor="adaToUsd">
                        ADA/USD Price:
                    </label>
                    <input
                        type="number"
                        id="adaToUsd"
                        value={adaToUsd}
                        onChange={(e) =>
                            setAdaToUsd(parseFloat(e.target.value))}
                        min="0"
                        step="0.01"
                    />
                </div>
            </div>

            <div className={styles.calculationBreakdown}>
                <h3>Calculation Breakdown</h3>
                <div className={styles.breakdownGrid}>
                    <div className={styles.breakdownItem}>
                        <h4>Monthly Parameters</h4>
                        <ul>
                            <li>
                                Seconds per month:{" "}
                                {SECONDS_PER_MONTH.toLocaleString()}
                            </li>
                            <li>
                                Header propagation:{" "}
                                {headerPropagationPercent}% of {numPeers}{" "}
                                peers = {Math.round(
                                    numPeers * (headerPropagationPercent / 100),
                                )} peers
                            </li>
                            <li>
                                Body requests: {bodyRequestPercent}% of{" "}
                                {numPeers} peers = {Math.round(
                                    numPeers * (bodyRequestPercent / 100),
                                )} peers
                            </li>
                        </ul>
                    </div>
                    <div className={styles.breakdownItem}>
                        <h4>Block Timing</h4>
                        <ul>
                            <li>
                                Endorsement Blocks (EB):
                                <ul>
                                    <li>Stage length: 20 seconds</li>
                                    <li>
                                        Stages per month: {SECONDS_PER_MONTH}
                                        {" "}
                                        / 20 = {(SECONDS_PER_MONTH / 20)
                                            .toLocaleString()} stages
                                    </li>
                                    <li>EBs per stage: 1.5</li>
                                    <li>
                                        Total EBs: {(SECONDS_PER_MONTH / 20)
                                            .toLocaleString()} × 1.5 ={" "}
                                        {((SECONDS_PER_MONTH / 20) * 1.5)
                                            .toLocaleString()} EBs
                                    </li>
                                </ul>
                            </li>
                            <li>
                                Ranking Blocks (RB):
                                <ul>
                                    <li>RB generation rate: 0.05 RBs/second</li>
                                    <li>
                                        Total RBs:{" "}
                                        {SECONDS_PER_MONTH.toLocaleString()}
                                        {" "}
                                        × 0.05 = {(0.05 * SECONDS_PER_MONTH)
                                            .toLocaleString()} RBs
                                    </li>
                                </ul>
                            </li>
                        </ul>
                    </div>
                    <div className={styles.breakdownItem}>
                        <h4>Block Sizes</h4>
                        <ul>
                            <li>
                                Input Blocks (IB):
                                <ul>
                                    <li>
                                        Header: {blockSizes.ib.header} bytes
                                    </li>
                                    <li>
                                        Body:{" "}
                                        {blockSizes.ib.body.toLocaleString()}
                                        {" "}
                                        bytes
                                    </li>
                                </ul>
                            </li>
                            <li>
                                Endorsement Blocks (EB):
                                <ul>
                                    <li>
                                        Header: {blockSizes.eb.header} bytes
                                    </li>
                                    <li>
                                        Body: {blockSizes.eb.body}{" "}
                                        bytes per IB reference
                                    </li>
                                </ul>
                            </li>
                            <li>
                                Ranking Blocks (RB):
                                <ul>
                                    <li>
                                        Header: {blockSizes.rb.header} bytes
                                    </li>
                                    <li>
                                        Body:{" "}
                                        {blockSizes.rb.body.toLocaleString()}
                                        {" "}
                                        bytes
                                    </li>
                                </ul>
                            </li>
                        </ul>
                    </div>
                </div>
                <div className={styles.calculationNote}>
                    <p>Example calculation for 1 IB/s:</p>
                    <ul>
                        <li>
                            IB Headers: {SECONDS_PER_MONTH.toLocaleString()}
                            {" "}
                            seconds × {blockSizes.ib.header} bytes ×{" "}
                            {Math.round(
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
                            seconds × {blockSizes.ib.body.toLocaleString()}{" "}
                            bytes × {blockUtilizationPercent}% utilization ×
                            {" "}
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
                            EB Bodies:{" "}
                            {((SECONDS_PER_MONTH / 20) * 1.5).toLocaleString()}
                            {" "}
                            seconds × {blockSizes.eb.body} bytes × {20}{" "}
                            IBs per stage ×{" "}
                            {Math.round(numPeers * (bodyRequestPercent / 100))}
                            {" "}
                            peers = {formatTraffic(
                                (SECONDS_PER_MONTH / 20) * 1.5 *
                                    blockSizes.eb.body * 20 *
                                    Math.round(
                                        numPeers * (bodyRequestPercent / 100),
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
                    </ul>
                </div>
            </div>

            <h3>Monthly Traffic and Fees per Node</h3>
            <div className={styles.tableContainer}>
                <table className={styles.table}>
                    <thead>
                        <tr>
                            <th>IB/s</th>
                            <th>IB Headers</th>
                            <th>IB Bodies</th>
                            <th>EB Headers</th>
                            <th>EB Bodies</th>
                            <th>RB Headers</th>
                            <th>RB Bodies</th>
                            <th>Total Traffic</th>
                            <th>Total Txs</th>
                            <th>Tx Fees (₳)</th>
                            <th>Tx Fees (USD)</th>
                        </tr>
                    </thead>
                    <tbody>
                        {IB_RATES.map((rate) => {
                            const {
                                traffic,
                                totalTraffic,
                                txFeeADA,
                                txFeeUSD,
                                totalTxs,
                            } = calculateTraffic(rate);
                            return (
                                <tr key={rate}>
                                    <td>{rate}</td>
                                    <td>{formatTraffic(traffic.ib.headers)}</td>
                                    <td>{formatTraffic(traffic.ib.bodies)}</td>
                                    <td>{formatTraffic(traffic.eb.headers)}</td>
                                    <td>{formatTraffic(traffic.eb.bodies)}</td>
                                    <td>{formatTraffic(traffic.rb.headers)}</td>
                                    <td>{formatTraffic(traffic.rb.bodies)}</td>
                                    <td>{formatTraffic(totalTraffic)}</td>
                                    <td>{totalTxs.toLocaleString()}</td>
                                    <td>
                                        {txFeeADA.toLocaleString(undefined, {
                                            minimumFractionDigits: 0,
                                            maximumFractionDigits: 6,
                                        }).replace(/\.?0+$/, "")} ₳
                                    </td>
                                    <td>
                                        ${txFeeUSD.toLocaleString(undefined, {
                                            minimumFractionDigits: 2,
                                        })}
                                    </td>
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
                            <li>Treasury tax (20%)</li>
                            <li>Other operational costs</li>
                        </ul>
                    </div>
                </div>
            </div>

            <h3>Monthly Cost by Cloud Provider ($)</h3>
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
                                Price/GB {getSortIcon("egressCost")}
                            </th>
                            <th
                                onClick={() => handleSort("freeAllowance")}
                                className={styles.sortable}
                            >
                                Free Allowance (GB){" "}
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
        </div>
    );
};

export default LeiosTrafficCalculator;
