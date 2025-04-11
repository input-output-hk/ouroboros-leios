import Heading from "@theme/Heading";
import clsx from "clsx";
import styles from "./styles.module.css";

type FeatureItem = {
    title: string;
    Svg: React.ComponentType<React.ComponentProps<"svg">>;
    description: React.ReactElement;
};

const FeatureList: FeatureItem[] = [
    {
        title: "Scalable",
        Svg: require("@site/static/img/cargo-ship.svg").default,
        description: (
            <>
                Optimizes network bandwidth for faster transaction processing,
                significantly enhancing Cardano’s scalability. Transactions are
                confirmed with minimal delays for a seamless user experience.
            </>
        ),
    },
    {
        title: "Secure",
        Svg: require("@site/static/img/safe.svg").default,
        description: (
            <>
                Preserves Ouroboros' strong security properties with robust
                defenses against attacks while ensuring fair participation.
            </>
        ),
    },
    {
        title: "Flexible",
        Svg: require("@site/static/img/socket-chord.svg").default,
        description: (
            <>
                Ouroboros Leios supports diverse applications.
            </>
        ),
    },
];

function Feature({ title, Svg, description }: FeatureItem) {
    return (
        <div className={clsx("col col--4")}>
            <div className="text--center">
                <Svg className={styles.featureSvg} role="img" />
            </div>
            <div className="text--center padding-horiz--md">
                <Heading as="h3">{title}</Heading>
                <p>{description}</p>
            </div>
        </div>
    );
}

export default function HomepageFeatures(): React.ReactElement {
    return (
        <section className={styles.features}>
            <div className="container">
                <div className="row">
                    {FeatureList.map((props, idx) => (
                        <Feature key={idx} {...props} />
                    ))}
                </div>
            </div>
        </section>
    );
}
