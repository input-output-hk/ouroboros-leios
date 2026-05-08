import { useLocation } from "@docusaurus/router";
import { useNavbarMobileSidebar } from "@docusaurus/theme-common/internal";
import { translate } from "@docusaurus/Translate";
import IconMenu from "@theme/Icon/Menu";
import clsx from "clsx";
import { type ReactNode } from "react";
import styles from "./styles.module.css";

export default function MobileSidebarToggle(): ReactNode {
  const { toggle, shown } = useNavbarMobileSidebar();
  const location = useLocation();
  const isHomepage = location.pathname === "/";
  return (
    <button
      onClick={toggle}
      aria-label={translate({
        id: "theme.docs.sidebar.toggleSidebarButtonAriaLabel",
        message: "Toggle navigation bar",
        description:
          "The ARIA label for hamburger menu button of mobile navigation",
      })}
      aria-expanded={shown}
      className={clsx(
        "navbar__toggle clean-btn",
        isHomepage ? styles.mobileIconDark : "",
      )}
      type="button"
    >
      <IconMenu />
    </button>
  );
}
