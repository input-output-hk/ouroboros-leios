import type { SVGProps } from "react";

import { forwardRef, memo, Ref } from "react";
const FacebookIcon = (
  props: SVGProps<SVGSVGElement>,
  ref: Ref<SVGSVGElement>,
) => (
  <svg
    xmlns="http://www.w3.org/2000/svg"
    width="13"
    height="24"
    viewBox="0 0 13 24"
    ref={ref}
    {...props}
  >
    <path
      d="M12.1387 13.5L12.812 9.156H8.6V6.33733C8.6 5.15067 9.18933 3.99067 11.0747 3.99067H12.9893V0.293333C12.9893 0.293333 11.252 0 9.59067 0C6.12267 0 3.856 2.08 3.856 5.84667V9.156H0V13.5H3.856V24H8.6V13.5H12.1387Z"
      fill="white"
    />
  </svg>
);
const ForwardRef = forwardRef(FacebookIcon);
const Memo = memo(ForwardRef);
export default Memo;
