import NavbarContent from "@theme/Navbar/Content";
import NavbarLayout from "@theme/Navbar/Layout";
import { JSX } from "react";

export default function Navbar(): JSX.Element {
  return (
    <NavbarLayout>
      <NavbarContent />
    </NavbarLayout>
  );
}
