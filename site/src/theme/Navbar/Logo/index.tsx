import { useLocation } from "@docusaurus/router";
import Logo from "@theme/Logo";
import { JSX } from "react";

export default function NavbarLogo(): JSX.Element {
  const { pathname } = useLocation();
  if (pathname === "/") {
    return (
      <a className="navbar__brand" href="/">
        <img src="/img/logo-dark.svg" alt="Logo" />
      </a>
    );
  } else {
    return (
      <Logo
        className="navbar__brand"
        imageClassName=""
        titleClassName="navbar__title text--truncate"
      />
    );
  }
}
