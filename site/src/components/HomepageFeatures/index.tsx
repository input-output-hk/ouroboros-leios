import clsx from 'clsx';
import Heading from '@theme/Heading';
import styles from './styles.module.css';

type FeatureItem = {
    title: string;
    Svg: React.ComponentType<React.ComponentProps<'svg'>>;
    description: JSX.Element;
};

const FeatureList: FeatureItem[] = [
    {
        title: 'Fast',
        Svg: require('@site/static/img/cargo-ship.svg').default,
        description: (
            <>
                Ouroboros Leios is designed to maximise the use of available network bandwidth and therefore maximise overall throughput of the network.
            </>
        ),
    },
    {
        title: 'Secure',
        Svg: require('@site/static/img/safe.svg').default,
        description: (
            <>
                Ouroboros Leios maintains the strong security properties of the Ouroboros family of protocols.
            </>
        ),
    },
    {
        title: 'Flexible',
        Svg: require('@site/static/img/socket-chord.svg').default,
        description: (
            <>
                Being agnostic of the underlying Nakomoto consensus protocol, Ouroboros Leios can support a wide range of applications.
            </>
        ),
    },
];

function Feature({ title, Svg, description }: FeatureItem) {
    return (
        <div className={clsx('col col--4')}>
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

export default function HomepageFeatures(): JSX.Element {
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
