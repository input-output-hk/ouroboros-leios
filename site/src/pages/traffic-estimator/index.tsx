import LeiosTrafficCalculator from "@site/src/components/LeiosTrafficCalculator";
import Layout from "@theme/Layout";
import React from "react";

export default function TrafficEstimator(): React.ReactElement {
    return (
        <Layout
            title="Traffic Estimator"
            description="Estimate network traffic for Ouroboros Leios nodes"
        >
            <main className="container margin-vert--lg">
                <div className="row">
                    <div className="col col--12">
                        <h1>Leios Node Traffic Estimator</h1>
                        <p>
                            Use this calculator to estimate monthly egress
                            traffic and costs for running an Ouroboros Leios
                            node. Based on the default configuration with a
                            stage length of 20 slots, each stage (pipeline)
                            generates 1.5 Endorsement Blocks (EBs) that
                            reference Input Blocks (IBs) from that stage. Adjust
                            the number of peers and propagation parameters to
                            see how they affect your monthly traffic.
                        </p>
                        <LeiosTrafficCalculator />
                    </div>
                </div>
            </main>
        </Layout>
    );
}
