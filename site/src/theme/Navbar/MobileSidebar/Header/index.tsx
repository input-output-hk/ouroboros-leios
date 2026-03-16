import { useLocation } from "@docusaurus/router";
import { useNavbarMobileSidebar } from "@docusaurus/theme-common/internal";
import { translate } from "@docusaurus/Translate";
import IconClose from "@theme/Icon/Close";
import NavbarColorModeToggle from "@theme/Navbar/ColorModeToggle";
import NavbarLogo from "@theme/Navbar/Logo";
import clsx from "clsx";
import { type ReactNode } from "react";
function CloseButton() {
  const mobileSidebar = useNavbarMobileSidebar();
  const location = useLocation();
  const isHomepage = location.pathname === "/";
  return (
    <button
      type="button"
      aria-label={translate({
        id: "theme.docs.sidebar.closeSidebarButtonAriaLabel",
        message: "Close navigation bar",
        description: "The ARIA label for close button of mobile sidebar",
      })}
      className={clsx(
        "clean-btn navbar-sidebar__close",
        isHomepage ? "mobile-icon-dark" : "",
      )}
      onClick={() => mobileSidebar.toggle()}
    >
      <IconClose />
    </button>
  );
}

export default function NavbarMobileSidebarHeader(): ReactNode {
  return (
    <div className="navbar-sidebar__brand">
      <NavbarLogo />
      <NavbarColorModeToggle className="margin-right--md" />
      <CloseButton />
    </div>
  );
}
