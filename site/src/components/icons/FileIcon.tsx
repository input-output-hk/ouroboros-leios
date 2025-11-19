import type { SVGProps } from "react";

import { forwardRef, memo, Ref } from "react";
const FileIcon = (props: SVGProps<SVGSVGElement>, ref: Ref<SVGSVGElement>) => (
  <svg
    xmlns="http://www.w3.org/2000/svg"
    width={16}
    height={16}
    fill="none"
    viewBox="0 0 16 16"
    ref={ref}
    {...props}
  >
    <path
      d="M8.66699 1.33337H4.00033C3.6467 1.33337 3.30756 1.47385 3.05752 1.7239C2.80747 1.97395 2.66699 2.31309 2.66699 2.66671V13.3334C2.66699 13.687 2.80747 14.0261 3.05752 14.2762C3.30756 14.5262 3.6467 14.6667 4.00033 14.6667H12.0003C12.3539 14.6667 12.6931 14.5262 12.9431 14.2762C13.1932 14.0261 13.3337 13.687 13.3337 13.3334V6.00004M8.66699 1.33337L13.3337 6.00004M8.66699 1.33337V6.00004H13.3337"
      stroke="currentColor"
      stroke-linecap="round"
      stroke-linejoin="round"
    />
  </svg>
);
const ForwardRef = forwardRef(FileIcon);
const Memo = memo(ForwardRef);
export default Memo;
