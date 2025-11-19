import type { SVGProps } from "react";

import { forwardRef, memo, Ref } from "react";
const ArrowRightIcon = (
  props: SVGProps<SVGSVGElement>,
  ref: Ref<SVGSVGElement>
) => (
  <svg
    xmlns="http://www.w3.org/2000/svg"
    width={14}
    height={14}
    fill="none"
    viewBox="0 0 14 14"
    ref={ref}
    {...props}
  >
    <path
      d="M0.75 6.75H12.75M12.75 6.75L6.75 12.75M12.75 6.75L6.75 0.75"
      stroke="currentColor"
      stroke-width="1.5"
      stroke-linecap="round"
      stroke-linejoin="round"
    />
  </svg>
);
const ForwardRef = forwardRef(ArrowRightIcon);
const Memo = memo(ForwardRef);
export default Memo;
