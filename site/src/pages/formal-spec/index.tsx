import React from 'react';
import Layout from '@theme/Layout';
import styles from './styles.module.css';

// List of available Agda modules with their actual file paths
const AGDA_MODULES = [
  { 
    name: 'Leios.Base',
    path: 'Leios.Base.html',
    description: 'Core definitions and types'
  },
  { 
    name: 'Leios.Voting',
    path: 'Leios.Voting.html',
    description: 'Voting mechanism and rules'
  },
  { 
    name: 'Leios.Protocol',
    path: 'Leios.Protocol.html',
    description: 'Protocol state and transitions'
  },
  { 
    name: 'Leios.Blocks',
    path: 'Leios.Blocks.html',
    description: 'Block structure and validation'
  },
  { 
    name: 'Leios.Network',
    path: 'Leios.Network.html',
    description: 'Network communication and messages'
  }
];

export default function FormalSpecPage(): React.ReactElement {
  return (
    <Layout
      title="Formal Specification"
      description="Ouroboros Leios Formal Specification"
    >
      <main className={styles.main}>
        <div className={styles.container}>
          <h1>Ouroboros Leios Formal Specification</h1>
          <p>
            This section contains the formal specification of the Ouroboros Leios protocol,
            written in Agda. The specification provides a mathematical foundation for the
            protocol's properties and guarantees.
          </p>
          
          <h2>Available Modules</h2>
          <div className={styles.fileGrid}>
            {AGDA_MODULES.map(module => (
              <a
                key={module.name}
                href={`/agda_html/${module.path}`}
                className={styles.fileLink}
                target="_blank"
                rel="noopener noreferrer"
              >
                <div className={styles.moduleName}>{module.name}</div>
                <div className={styles.moduleDescription}>{module.description}</div>
              </a>
            ))}
          </div>

          <h2>Getting Started</h2>
          <p>
            The formal specification is organized into modules, each focusing on different
            aspects of the protocol. Start with these key modules:
          </p>
          <ul>
            {AGDA_MODULES.slice(0, 3).map(module => (
              <li key={module.name}>
                <a href={`/agda_html/${module.path}`} target="_blank" rel="noopener noreferrer">
                  <strong>{module.name}</strong>
                </a>
                {' - '}{module.description}
              </li>
            ))}
          </ul>
        </div>
      </main>
    </Layout>
  );
} 