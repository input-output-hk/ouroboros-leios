import { ErrorCauseBoundary, useThemeConfig } from "@docusaurus/theme-common";
import {
  splitNavbarItems,
  useNavbarMobileSidebar,
} from "@docusaurus/theme-common/internal";
import NavbarColorModeToggle from "@theme/Navbar/ColorModeToggle";
import NavbarLogo from "@theme/Navbar/Logo";
import NavbarMobileSidebarToggle from "@theme/Navbar/MobileSidebar/Toggle";
import NavbarSearch from "@theme/Navbar/Search";
import NavbarItem, { type Props as NavbarItemConfig } from "@theme/NavbarItem";
import SearchBar from "@theme/SearchBar";
import { JSX, type ReactNode } from "react";

import { useLocation } from "@docusaurus/router";
import styles from "./styles.module.css";

function useNavbarItems() {
  // TODO temporary casting until ThemeConfig type is improved
  return useThemeConfig().navbar.items as NavbarItemConfig[];
}

function NavbarItems({ items }: { items: NavbarItemConfig[] }): JSX.Element {
  return (
    <>
      {items.map((item, i) => (
        <ErrorCauseBoundary
          key={i}
          onError={() =>
            new Error(
              `A theme navbar item failed to render.
Please double-check the following navbar item (themeConfig.navbar.items) of your Docusaurus config:
${JSON.stringify(item, null, 2)}`
            )
          }
        >
          <NavbarItem {...item} />
        </ErrorCauseBoundary>
      ))}
    </>
  );
}

function NavbarContentLayout({
  left,
  right,
}: {
  left: ReactNode;
  right: ReactNode;
}) {
  const { pathname } = useLocation();
  return (
    <>
      {pathname === "/" || pathname === "/formal-spec/" ? (
        <div className="container">
          <div className="container-padding">
            <div className="navbar__inner">
              {/* <div className="navbar__items ">{left}</div> */}
              <NavbarLogo />
              <div className="navbar__items navbar__items--right">{right}</div>
            </div>
          </div>
        </div>
      ) : (
        <div className="navbar__non_homepage">
          {/* <div className="navbar__items">{left}</div> */}
          <NavbarLogo />

          <div className="navbar__items navbar__items--right">{right}</div>
        </div>
      )}
    </>
  );
}

//  <div className="navbar__inner">
//       <div className="navbar__items">{left}</div>
//       <div className="navbar__items navbar__items--right">{right}</div>
//     </div>

export default function NavbarContent(): JSX.Element {
  const mobileSidebar = useNavbarMobileSidebar();

  const items = useNavbarItems();
  const [leftItems, rightItems] = splitNavbarItems(items);

  const searchBarItem = items.find((item) => item.type === "search");

  return (
    <NavbarContentLayout
      left={
        // TODO stop hardcoding items?
        <>
          <NavbarItems items={leftItems} />
        </>
      }
      right={
        // TODO stop hardcoding items?
        // Ask the user to add the respective navbar items => more flexible
        <>
          {!mobileSidebar.disabled && <NavbarMobileSidebarToggle />}
          <div className="navbar_item_menu">
            <NavbarItems items={rightItems} />
            <NavbarColorModeToggle className={styles.colorModeToggle} />
            {!searchBarItem && (
              <NavbarSearch>
                <SearchBar />
              </NavbarSearch>
            )}
          </div>
        </>
      }
    />
  );
}
