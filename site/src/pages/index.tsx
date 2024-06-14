import clsx from 'clsx';
import Link from '@docusaurus/Link';
import useDocusaurusContext from '@docusaurus/useDocusaurusContext';
import Layout from '@theme/Layout';
import HomepageFeatures from '@site/src/components/HomepageFeatures';
import Heading from '@theme/Heading';
import { useColorMode } from '@docusaurus/theme-common';


import styles from './index.module.css';

import HeaderBorderTop from '@site/static/img/hero-border-top.svg';
import HeaderBorderBottom from '@site/static/img/hero-border-bottom.svg';

import HeaderBorderTopDark from '@site/static/img/hero-border-top.svg';
import HeaderBorderBottomDark from '@site/static/img/hero-border-bottom.svg';

function HomepageHeader() {
    const { siteConfig } = useDocusaurusContext();
    const { isDarkTheme } = useColorMode();  
    
    return (
        <>
         <div style={{width: "100%", display: "flex"}}>
        {isDarkTheme ? <HeaderBorderTopDark style={{height: "auto", width: "inherit", marginBottom: "-1px"}} /> : <HeaderBorderTop style={{height: "auto", width: "inherit", marginBottom: "-1px"}}/>}
        </div>
        <header className={clsx('hero hero--primary', styles.heroBanner)}>
            <div className="container">
                <Heading as="h1" className="hero__title">
                    {siteConfig.title}
                </Heading>
                <p className="hero__subtitle">{siteConfig.tagline}</p>
                <div className={styles.buttons}>
                    <Link
                        className="button button--secondary button--lg"
                        to="/docs/intro">
                        Get Started 🚀
                    </Link>
                </div>
            </div>
        </header>
            <div style={{width: "100%", display: "flex"}}>
                {isDarkTheme ? <HeaderBorderBottomDark style={{height: "auto", width: "inherit",  marginTop: "-1px"}} /> : <HeaderBorderBottom style={{height: "auto", width: "inherit",  marginTop: "-1px"}}/>}
            </div>
        </>
    );
}

export default function Home(): JSX.Element {
    const { siteConfig } = useDocusaurusContext();
    return (
        <Layout
            title={`Hello from ${siteConfig.title}`}
            description="Description will go into a meta tag in <head />">
            <HomepageHeader />
            <main>
                <HomepageFeatures />
            </main>
        </Layout>
    );
}
