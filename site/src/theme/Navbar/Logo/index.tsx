import Logo from "@theme/Logo";
import { JSX } from "react";

export default function NavbarLogo(): JSX.Element {
  return (
    <Logo
      className="navbar__brand"
      imageClassName=""
      titleClassName="navbar__title text--truncate"
    />
  );
}
