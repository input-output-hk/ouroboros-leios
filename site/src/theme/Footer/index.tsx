import React from 'react';
import Footer from '@theme-original/Footer';
import type FooterType from '@theme/Footer';
import type {WrapperProps} from '@docusaurus/types';
import styles from './index.module.css';
import clsx from 'clsx';


type Props = WrapperProps<typeof FooterType>;

export default function FooterWrapper(props: Props): JSX.Element {
  return (
    <div  className={clsx(styles.footerWrapper)}>
      <div className={clsx(styles.preFooter)} />
      <Footer {...props} />
    </div>
  );
}
