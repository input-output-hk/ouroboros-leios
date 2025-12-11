"use client";

import { useLocation } from "@docusaurus/router";
import { useThemeConfig } from "@docusaurus/theme-common";
import {
  useHideableNavbar,
  useNavbarMobileSidebar,
} from "@docusaurus/theme-common/internal";
import { translate } from "@docusaurus/Translate";
import type { Props } from "@theme/Navbar/Layout";
import NavbarMobileSidebar from "@theme/Navbar/MobileSidebar";
import clsx from "clsx";
import { motion, useMotionValueEvent, useScroll } from "framer-motion";
import { JSX, useEffect, useState, type ComponentProps } from "react";

function NavbarBackdrop(props: ComponentProps<"div">) {
  return (
    <div
      role="presentation"
      {...props}
      className={clsx("navbar-sidebar__backdrop", props.className)}
    />
  );
}

export default function NavbarLayout({ children }: Props): JSX.Element {
  const {
    navbar: { hideOnScroll, style },
  } = useThemeConfig();
  const mobileSidebar = useNavbarMobileSidebar();
  const { navbarRef } = useHideableNavbar(hideOnScroll);
  const location = useLocation();
  const isHomepage = location.pathname === "/";

  const { scrollY } = useScroll();
  const [isVisible, setIsVisible] = useState(true);
  const [lastY, setLastY] = useState(0);

  // Hide/show on scroll similar to your previous code
  useMotionValueEvent(scrollY, "change", (latest) => {
    if (!isHomepage) return;
    if (mobileSidebar.shown) return;

    if (latest > lastY + 10) setIsVisible(false);
    else if (latest < lastY - 10) setIsVisible(true);

    setLastY(latest);
  });

  useEffect(() => {
    if (mobileSidebar.shown) setIsVisible(true);
  }, [mobileSidebar.shown]);

  const NavWrapper = isHomepage ? motion.nav : "nav";

  return (
    <NavWrapper
      ref={navbarRef}
      aria-label={translate({
        id: "theme.NavBar.navAriaLabel",
        message: "Main",
        description: "The ARIA label for the main navigation",
      })}
      className={clsx("navbar", "navbar--fixed-top", {
        "navbar--dark": style === "dark",
        "navbar--primary": style === "primary",
        "navbar-sidebar--show": mobileSidebar.shown,
      })}
      animate={isHomepage ? { y: isVisible ? 0 : "-100%" } : undefined}
      transition={
        isHomepage ? { type: "spring", stiffness: 300, damping: 30 } : undefined
      }
    >
      {children}
      <NavbarBackdrop onClick={mobileSidebar.toggle} />
      <NavbarMobileSidebar />
    </NavWrapper>
  );
}
