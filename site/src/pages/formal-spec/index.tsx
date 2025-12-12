import Layout from "@theme/Layout";
import React from "react";
import styles from "./styles.module.css";

// List of available Agda modules with their actual file paths
const AGDA_MODULES = [
  {
    name: "Leios Protocol",
    path: "Leios.Protocol.html",
    description: "Protocol state and transitions",
  },
  {
    name: "Leios Blocks",
    path: "Leios.Blocks.html",
    description: "Block structure and validation",
  },
  {
    name: "Leios Network",
    path: "Leios.Network.html",
    description: "Network communication and messages",
  },
  {
    name: "Short Leios Variant",
    path: "Leios.Short.html",
    description:
      "A specific variant of the Leios protocol with fewer stages per pipeline.",
  },
  {
    name: "Network Basic Broadcast",
    path: "Network.BasicBroadcast.html",
    description: "Basic broadcast network primitives",
  },
];

export default function FormalSpecPage(): React.ReactElement {
  return (
    <Layout
      title="Formal specification"
      description="Ouroboros Leios formal specification"
    >
      <main className={styles.main}>
        <div className="container">
          <div className="container-padding">
            <div className={styles.plainHero}>
              <h1>Ouroboros Leios formal specification</h1>
              <p>
                This section contains the formal specification of the Ouroboros
                Leios protocol, written in Agda. The specification provides a
                mathematical foundation for the protocol's properties and
                guarantees.
              </p>
            </div>

            <h2>Modules</h2>
            <div className={styles.fileGrid}>
              {AGDA_MODULES.map((module) => (
                <a
                  key={module.name}
                  href={`/formal-spec/${module.path}`}
                  className={styles.fileLink}
                  target="_blank"
                  rel="noopener noreferrer"
                >
                  <div className={styles.moduleName}>{module.name}</div>
                  <div className={styles.moduleDescription}>
                    {module.description}
                  </div>
                </a>
              ))}
            </div>
          </div>
        </div>
      </main>
    </Layout>
  );
}
