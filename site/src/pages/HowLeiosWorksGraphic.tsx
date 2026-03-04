import Link from "@docusaurus/Link";
import HowLeiosWorksSvg from "@site/static/img/how-leios-works-graphic.svg";
import styles from "./index.module.css";

export default function HowLeiosWorksGraphic() {
  return (
    <>
      <HowLeiosWorksSvg className={styles.leiosSvg} />
      <div className={styles.svgCaption}>
        Protocol timing showing the sequential process from RB announcement
        through EB validation to certificate inclusion. Key parameters:{" "}
        <Link
          to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-hdr"
          target="_blank"
          rel="noopener noreferrer"
        >
          <span
            style={{
              fontSize: "1.25em",
              fontFamily: "Times New Roman, serif",
            }}
          >
            L
          </span>
          <sub>hdr</sub>
        </Link>{" "}
        (
        <Link
          to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#equivocation-detection"
          target="_blank"
          rel="noopener noreferrer"
        >
          header diffusion
        </Link>
        ),{" "}
        <Link
          to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-vote"
          target="_blank"
          rel="noopener noreferrer"
        >
          <span
            style={{
              fontSize: "1.25em",
              fontFamily: "Times New Roman, serif",
            }}
          >
            L
          </span>
          <sub>vote</sub>
        </Link>{" "}
        (
        <Link
          to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#voting-period"
          target="_blank"
          rel="noopener noreferrer"
        >
          voting period
        </Link>
        ),{" "}
        <Link
          to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-diff"
          target="_blank"
          rel="noopener noreferrer"
        >
          <span
            style={{
              fontSize: "1.25em",
              fontFamily: "Times New Roman, serif",
            }}
          >
            L
          </span>
          <sub>diff</sub>
        </Link>{" "}
        (
        <Link
          to="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#diffusion-period"
          target="_blank"
          rel="noopener noreferrer"
        >
          diffusion period
        </Link>
        ).
      </div>
    </>
  );
}
