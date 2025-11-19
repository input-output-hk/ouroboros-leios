import { LinkButton } from "../LinkButton/LinkButton";
import styles from "./styles.module.css";

type FeatureItem = {
  title: string;
  svg: string;
  description: React.ReactElement;
  button: {
    text: string;
    url: string;
  };
};

const FeatureList: FeatureItem[] = [
  {
    title: "Scalable",
    svg: "/img/scale.svg",
    description: (
      <>
        Optimizes network bandwidth for faster transaction processing,
        significantly enhancing Cardano’s scalability. Transactions are
        confirmed with minimal delays for a seamless user experience.
      </>
    ),
    button: {
      text: "Link to Documentation",
      url: "/docs/development/overview",
    },
  },
  {
    title: "Secure",
    svg: "/img/secure.svg",
    description: (
      <>
        Preserves Ouroboros' strong security properties with robust defenses
        against attacks while ensuring fair participation.
      </>
    ),
    button: {
      text: "Link to Documentation",
      url: "/docs/development/overview",
    },
  },
  {
    title: "Flexible",
    svg: "/img/flexible.svg",
    description: <>Ouroboros Leios supports diverse applications.</>,
    button: {
      text: "Link to Documentation",
      url: "/docs/development/overview",
    },
  },
];

function Feature({ title, svg, description, button }: FeatureItem) {
  return (
    <div className={styles.feature}>
      <div className={styles.featureContent}>
        <img src={svg} className={styles.featureImg} />
        <div className="">
          <h2 className="">{title}</h2>
          <p>{description}</p>
        </div>
      </div>
      <LinkButton text={button.text} url={button.url} />
    </div>
  );
}

export default function HomepageFeatures(): React.ReactElement {
  return (
    <section className="padding-section">
      <div className="container">
        <div className="container-padding">
          <div className={styles.features}>
            {FeatureList.map((props, idx) => (
              <Feature key={idx} {...props} />
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}
