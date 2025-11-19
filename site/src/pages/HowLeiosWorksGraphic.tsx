import Link from "@docusaurus/Link";
import styles from "./index.module.css";

export function HowLeiosWorksGraphic() {
  return (
    <>
      <svg
        width="1000"
        height="580"
        viewBox="0 0 1000 580"
        xmlns="http://www.w3.org/2000/svg"
        className={styles.leiosSvg}
      >
        <defs>
          <pattern
            id="timelinePattern"
            x="0"
            y="0"
            width="40"
            height="40"
            patternUnits="userSpaceOnUse"
          >
            <rect width="40" height="40" fill="var(--svg-bg-color)" />
            <line
              x1="0"
              y1="40"
              x2="40"
              y2="0"
              stroke="var(--svg-border-color)"
              strokeWidth="0.5"
            />
          </pattern>
          <marker
            id="arrowhead"
            markerWidth="6"
            markerHeight="4"
            refX="5"
            refY="2"
            orient="auto"
          >
            <polygon points="0 0, 6 2, 0 4" fill="var(--svg-arrow-color)" />
          </marker>
          <marker
            id="votearrowhead"
            markerWidth="6"
            markerHeight="4"
            refX="5"
            refY="2"
            orient="auto"
          >
            <polygon points="0 0, 6 2, 0 4" fill="#f9a825" />
          </marker>
        </defs>

        <rect width="1000" height="580" fill="var(--svg-bg-color)" />

        {/* Slot Grid */}
        <g stroke="var(--svg-border-color)" strokeWidth="1">
          <line x1="100" y1="80" x2="100" y2="560" />
          <line x1="250" y1="80" x2="250" y2="560" />
          <line x1="400" y1="80" x2="400" y2="560" />
          <line x1="550" y1="80" x2="550" y2="560" />
          <line x1="700" y1="80" x2="700" y2="560" />
          <line x1="850" y1="80" x2="850" y2="560" />
        </g>

        {/* Minor grid lines */}
        <g stroke="var(--svg-border-color)" strokeWidth="0.5" opacity="0.5">
          <line x1="130" y1="80" x2="130" y2="560" />
          <line x1="160" y1="80" x2="160" y2="560" />
          <line x1="190" y1="80" x2="190" y2="560" />
          <line x1="220" y1="80" x2="220" y2="560" />
          <line x1="280" y1="80" x2="280" y2="560" />
          <line x1="310" y1="80" x2="310" y2="560" />
          <line x1="340" y1="80" x2="340" y2="560" />
          <line x1="370" y1="80" x2="370" y2="560" />
          <line x1="430" y1="80" x2="430" y2="560" />
          <line x1="460" y1="80" x2="460" y2="560" />
          <line x1="490" y1="80" x2="490" y2="560" />
          <line x1="520" y1="80" x2="520" y2="560" />
          <line x1="580" y1="80" x2="580" y2="560" />
          <line x1="610" y1="80" x2="610" y2="560" />
          <line x1="640" y1="80" x2="640" y2="560" />
          <line x1="670" y1="80" x2="670" y2="560" />
          <line x1="730" y1="80" x2="730" y2="560" />
          <line x1="760" y1="80" x2="760" y2="560" />
          <line x1="790" y1="80" x2="790" y2="560" />
          <line x1="820" y1="80" x2="820" y2="560" />
        </g>

        {/* Timeline */}
        <rect
          x="100"
          y="40"
          width="750"
          height="30"
          fill="url(#timelinePattern)"
          stroke="var(--svg-border-color)"
          strokeWidth="0.5"
        />
        <text
          x="475"
          y="60"
          fontFamily="Arial, sans-serif"
          fontSize="12"
          textAnchor="middle"
          fill="var(--svg-text-color)"
        >
          Time (slots) →
        </text>

        {/* RB Block */}
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#ranking-blocks-rbs"
          target="_blank"
          rel="noopener noreferrer"
        >
          <rect
            x="220"
            y="100"
            width="60"
            height="80"
            fill="#fce5cd"
            stroke="#783f04"
            strokeWidth="2"
            rx="6"
            style={{ cursor: "pointer" }}
          />
          <text
            x="250"
            y="135"
            fontFamily="Arial, sans-serif"
            fontSize="20"
            fontWeight="bold"
            textAnchor="middle"
            fill="#783f04"
            style={{ cursor: "pointer" }}
          >
            RB
          </text>
          <text
            x="250"
            y="160"
            fontFamily="Arial, sans-serif"
            fontSize="12"
            textAnchor="middle"
            fill="#783f04"
            style={{ cursor: "pointer" }}
          >
            [Txs]
          </text>
        </a>

        {/* EB Block */}
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#endorser-blocks-ebs"
          target="_blank"
          rel="noopener noreferrer"
        >
          <rect
            x="200"
            y="220"
            width="100"
            height="60"
            fill="#d9ead3"
            stroke="#274e13"
            strokeWidth="2"
            rx="6"
            style={{ cursor: "pointer" }}
          />
          <text
            x="250"
            y="250"
            fontFamily="Arial, sans-serif"
            fontSize="18"
            fontWeight="bold"
            textAnchor="middle"
            fill="#274e13"
            style={{ cursor: "pointer" }}
          >
            EB
          </text>
          <text
            x="250"
            y="268"
            fontFamily="Arial, sans-serif"
            fontSize="11"
            textAnchor="middle"
            fill="#274e13"
            style={{ cursor: "pointer" }}
          >
            [TxRefs]
          </text>
        </a>

        {/* RB' Block */}
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#ranking-blocks-rbs"
          target="_blank"
          rel="noopener noreferrer"
        >
          <rect
            x="670"
            y="100"
            width="60"
            height="80"
            fill="#fce5cd"
            stroke="#783f04"
            strokeWidth="2"
            rx="6"
            style={{ cursor: "pointer" }}
          />
          <text
            x="700"
            y="135"
            fontFamily="Arial, sans-serif"
            fontSize="20"
            fontWeight="bold"
            textAnchor="middle"
            fill="#783f04"
            style={{ cursor: "pointer" }}
          >
            RB'
          </text>
        </a>

        {/* Certificate */}
        <g transform="translate(700, 185)">
          <a
            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
            target="_blank"
            rel="noopener noreferrer"
          >
            <polygon
              points="0,-20 20,-10 20,10 0,20 -20,10 -20,-10"
              fill="#fff2cc"
              stroke="#f9a825"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <text
              x="0"
              y="5"
              fontSize="12"
              fontWeight="bold"
              textAnchor="middle"
              fill="#7f6000"
              style={{
                cursor: "pointer",
              }}
            >
              <tspan fontFamily="serif" fontStyle="italic" fontSize="14">
                C
              </tspan>
              <tspan
                fontFamily="Arial, sans-serif"
                fontSize="10"
                fontStyle="normal"
                dy="3"
              >
                EB
              </tspan>
            </text>
          </a>
        </g>

        {/* Arrows and connections */}
        <path
          d="M 250 180 L 250 216"
          stroke="#783f04"
          strokeWidth="2"
          strokeDasharray="4,3"
        />
        <text
          x="255"
          y="200"
          fontFamily="Arial, sans-serif"
          fontSize="11"
          textAnchor="start"
          fill="#783f04"
        >
          announces
        </text>

        {/* Parameter brackets */}
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-hdr"
          target="_blank"
          rel="noopener noreferrer"
        >
          <path
            d="M 250 300 L 250 305 Q 250 310 255 310 L 335 310 Q 340 310 340 305 L 340 300"
            stroke="#f57c00"
            strokeWidth="2"
            fill="none"
            style={{ cursor: "pointer" }}
          />
          <text
            x="295"
            y="335"
            fontSize="18"
            textAnchor="middle"
            fill="#f57c00"
            style={{ cursor: "pointer" }}
          >
            <tspan fontFamily="serif" fontSize="24">
              3
            </tspan>
            <tspan fontFamily="serif" fontStyle="italic" fontSize="24">
              L
            </tspan>
            <tspan fontFamily="Arial, sans-serif" fontSize="16" dy="3">
              hdr
            </tspan>
          </text>
        </a>

        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-vote"
          target="_blank"
          rel="noopener noreferrer"
        >
          <path
            d="M 340 320 L 340 325 Q 340 330 345 330 L 455 330 Q 460 330 460 325 L 460 320"
            stroke="#f9a825"
            strokeWidth="2"
            fill="none"
            style={{ cursor: "pointer" }}
          />
          <text
            x="400"
            y="355"
            fontSize="18"
            textAnchor="middle"
            fill="#f9a825"
            style={{ cursor: "pointer" }}
          >
            <tspan fontFamily="serif" fontStyle="italic" fontSize="24">
              L
            </tspan>
            <tspan fontFamily="Arial, sans-serif" fontSize="16" dy="3">
              vote
            </tspan>
          </text>
        </a>

        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#l-diff"
          target="_blank"
          rel="noopener noreferrer"
        >
          <path
            d="M 460 340 L 460 345 Q 460 350 465 350 L 665 350 Q 670 350 670 345 L 670 340"
            stroke="#ffb74d"
            strokeWidth="2"
            fill="none"
            style={{ cursor: "pointer" }}
          />
          <text
            x="565"
            y="375"
            fontSize="18"
            textAnchor="middle"
            fill="#ffb74d"
            style={{ cursor: "pointer" }}
          >
            <tspan fontFamily="serif" fontStyle="italic" fontSize="24">
              L
            </tspan>
            <tspan fontFamily="Arial, sans-serif" fontSize="16" dy="3">
              diff
            </tspan>
          </text>
        </a>

        {/* Votes */}
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
          target="_blank"
          rel="noopener noreferrer"
        >
          <rect
            x="352"
            y="305"
            width="6"
            height="6"
            fill="#f9a825"
            transform="rotate(45 355 308)"
            style={{ cursor: "pointer" }}
          />
        </a>
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
          target="_blank"
          rel="noopener noreferrer"
        >
          <rect
            x="372"
            y="310"
            width="6"
            height="6"
            fill="#f9a825"
            transform="rotate(45 375 313)"
            style={{ cursor: "pointer" }}
          />
        </a>
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
          target="_blank"
          rel="noopener noreferrer"
        >
          <rect
            x="392"
            y="300"
            width="6"
            height="6"
            fill="#f9a825"
            transform="rotate(45 395 303)"
            style={{ cursor: "pointer" }}
          />
        </a>
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
          target="_blank"
          rel="noopener noreferrer"
        >
          <rect
            x="412"
            y="311"
            width="6"
            height="6"
            fill="#f9a825"
            transform="rotate(45 415 318)"
            style={{ cursor: "pointer" }}
          />
        </a>
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates"
          target="_blank"
          rel="noopener noreferrer"
        >
          <rect
            x="432"
            y="305"
            width="6"
            height="6"
            fill="#f9a825"
            transform="rotate(45 435 308)"
            style={{ cursor: "pointer" }}
          />
        </a>

        {/* Delta network characteristics */}
        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-rb"
          target="_blank"
          rel="noopener noreferrer"
        >
          <g id="rb-diffusion">
            <line
              x1="700"
              y1="385"
              x2="700"
              y2="395"
              stroke="#607d8b"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="700"
              y1="390"
              x2="850"
              y2="390"
              stroke="#607d8b"
              strokeWidth="2"
              strokeDasharray="4,2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="850"
              y1="385"
              x2="850"
              y2="395"
              stroke="#607d8b"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <text
              x="777"
              y="375"
              fontFamily="Arial, sans-serif"
              fontSize="20"
              textAnchor="middle"
              fill="#607d8b"
              style={{
                cursor: "pointer",
              }}
            >
              Δ
              <tspan fontSize="16" dy="3">
                RB
              </tspan>
              <tspan fontSize="14" dy="-6">
                W
              </tspan>
            </text>
          </g>
        </a>

        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-applytxs"
          target="_blank"
          rel="noopener noreferrer"
        >
          <g id="tx-processing">
            <line
              x1="775"
              y1="425"
              x2="775"
              y2="435"
              stroke="#607d8b"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="775"
              y1="430"
              x2="850"
              y2="430"
              stroke="#607d8b"
              strokeWidth="2"
              strokeDasharray="4,2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="850"
              y1="425"
              x2="850"
              y2="435"
              stroke="#607d8b"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <text
              x="815"
              y="415"
              fontFamily="Arial, sans-serif"
              fontSize="18"
              textAnchor="middle"
              fill="#607d8b"
              style={{
                cursor: "pointer",
              }}
            >
              Δ
              <tspan fontSize="14" dy="3">
                applyTxs
              </tspan>
              <tspan fontSize="12" dy="-6">
                W
              </tspan>
            </text>
          </g>
        </a>

        <a
          href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-eb-H"
          target="_blank"
          rel="noopener noreferrer"
        >
          <g id="network-chars-vote">
            <line
              x1="250"
              y1="425"
              x2="250"
              y2="435"
              stroke="#8bc34a"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="250"
              y1="430"
              x2="460"
              y2="430"
              stroke="#8bc34a"
              strokeWidth="2"
              strokeDasharray="4,2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="460"
              y1="425"
              x2="460"
              y2="435"
              stroke="#8bc34a"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <text
              x="355"
              y="415"
              fontFamily="Arial, sans-serif"
              fontSize="18"
              textAnchor="middle"
              fill="#8bc34a"
              style={{
                cursor: "pointer",
              }}
            >
              Δ
              <tspan fontSize="14" dy="3">
                EB
              </tspan>
              <tspan fontSize="12" dy="-6">
                O
              </tspan>
            </text>
          </g>
        </a>

        <g id="network-chars-after">
          <a
            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-eb-A"
            target="_blank"
            rel="noopener noreferrer"
          >
            <line
              x1="250"
              y1="465"
              x2="250"
              y2="475"
              stroke="#607d8b"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="250"
              y1="470"
              x2="810"
              y2="470"
              stroke="#607d8b"
              strokeWidth="2"
              strokeDasharray="4,2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="810"
              y1="465"
              x2="810"
              y2="475"
              stroke="#607d8b"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <text
              x="530"
              y="455"
              fontFamily="Arial, sans-serif"
              fontSize="18"
              textAnchor="middle"
              fill="#607d8b"
              style={{
                cursor: "pointer",
              }}
            >
              Δ
              <tspan fontSize="14" dy="3">
                EB
              </tspan>
              <tspan fontSize="12" dy="-6">
                W
              </tspan>
            </text>
          </a>

          <a
            href="https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#delta-reapply"
            target="_blank"
            rel="noopener noreferrer"
          >
            <line
              x1="815"
              y1="465"
              x2="815"
              y2="475"
              stroke="#607d8b"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="815"
              y1="470"
              x2="850"
              y2="470"
              stroke="#607d8b"
              strokeWidth="2"
              strokeDasharray="4,2"
              style={{
                cursor: "pointer",
              }}
            />
            <line
              x1="850"
              y1="465"
              x2="850"
              y2="475"
              stroke="#607d8b"
              strokeWidth="2"
              style={{
                cursor: "pointer",
              }}
            />
            <text
              x="835"
              y="455"
              fontFamily="Arial, sans-serif"
              fontSize="18"
              textAnchor="middle"
              fill="#607d8b"
              style={{
                cursor: "pointer",
              }}
            >
              Δ
              <tspan fontSize="14" dy="3">
                reapply
              </tspan>
              <tspan fontSize="12" dy="-6">
                W
              </tspan>
            </text>
          </a>
        </g>

        {/* Certificate back arrow */}
        <path
          d="M 700 205 Q 475 250 300 250"
          stroke="#f9a825"
          strokeWidth="2"
          strokeDasharray="2,2"
          fill="none"
          markerEnd="url(#votearrowhead)"
        />

        {/* Additional arrows */}
        <path
          d="M 220 140 L 150 140"
          stroke="var(--svg-arrow-color)"
          strokeWidth="2"
          strokeDasharray="4,3"
          markerEnd="url(#arrowhead)"
        />
        <path
          d="M 670 140 L 280 140"
          stroke="var(--svg-arrow-color)"
          strokeWidth="2"
          markerEnd="url(#arrowhead)"
        />
        <path
          d="M 900 140 L 730 140"
          stroke="var(--svg-arrow-color)"
          strokeWidth="2"
          strokeDasharray="4,3"
          markerEnd="url(#arrowhead)"
        />

        {/* Legend */}
        <g id="legend">
          <rect
            x="20"
            y="420"
            width="220"
            height="118"
            fill="var(--svg-legend-bg)"
            stroke="var(--svg-border-color)"
            strokeWidth="1"
            rx="4"
          />
          <text
            x="30"
            y="440"
            fontFamily="Arial, sans-serif"
            fontSize="12"
            fontWeight="bold"
            fill="var(--svg-text-color)"
          >
            Legend
          </text>

          {/* Certificate shape */}
          <g transform="translate(45, 455)">
            <polygon
              points="0,-8 8,-4 8,4 0,8 -8,4 -8,-4"
              fill="#fff2cc"
              stroke="#f9a825"
              strokeWidth="1"
            />
          </g>
          <text
            x="65"
            y="460"
            fontFamily="Arial, sans-serif"
            fontSize="11"
            fill="var(--svg-text-color)"
          >
            Certificate
          </text>

          {/* Vote shape */}
          <g transform="translate(45, 475)">
            <rect
              x="-3"
              y="-3"
              width="6"
              height="6"
              fill="#f9a825"
              transform="rotate(45)"
            />
          </g>
          <text
            x="65"
            y="480"
            fontFamily="Arial, sans-serif"
            fontSize="11"
            fill="var(--svg-text-color)"
          >
            Vote
          </text>

          <text
            x="30"
            y="500"
            fontFamily="Arial, sans-serif"
            fontSize="12"
            fontWeight="bold"
            fill="var(--svg-text-color)"
          >
            Superscripts
          </text>
          <text
            x="30"
            y="515"
            fontFamily="Arial, sans-serif"
            fontSize="11"
            fill="var(--svg-text-color)"
          >
            O = Optimistic
          </text>
          <text
            x="30"
            y="528"
            fontFamily="Arial, sans-serif"
            fontSize="11"
            fill="var(--svg-text-color)"
          >
            W = Worst-case
          </text>
        </g>
      </svg>
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
