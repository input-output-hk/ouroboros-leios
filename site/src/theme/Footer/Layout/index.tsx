import type { Props } from "@theme/Footer/Layout";
import clsx from "clsx";
import { JSX } from "react";

export default function FooterLayout({
  style,
  links,
  logo,
  copyright,
}: Props): JSX.Element {
  return (
    <footer
      className={clsx("footer", {
        "footer--dark": style === "dark",
      })}
    >
      <div className="container">
        <div className="container-padding">
          {links}
          {(logo || copyright) && (
            <div className="footer__bottom">
              {logo && logo}
              {copyright}
            </div>
          )}
        </div>
      </div>
    </footer>
  );
}
