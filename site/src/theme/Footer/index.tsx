import React from 'react';
import Footer from '@theme-original/Footer';
import type FooterType from '@theme/Footer';
import type {WrapperProps} from '@docusaurus/types';
import { useColorMode } from '@docusaurus/theme-common';

import Prefooter from '@site/static/img/prefooter.svg';
import PrefooterDark from '@site/static/img/prefooter.svg';

type Props = WrapperProps<typeof FooterType>;

export default function FooterWrapper(props: Props): JSX.Element {
  const { isDarkTheme } = useColorMode();  
  return (
    <>
      <div style={{width: "100%", display: "flex"}}>
        {isDarkTheme ? <PrefooterDark style={{height: "auto", width: "inherit"}} /> : <Prefooter style={{height: "auto", width: "inherit"}}/>}
      </div>
      <Footer {...props} />
    </>
  );
}
