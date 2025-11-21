import styles from "./index.module.css";

export default function ResearchGraphic() {
  return (
    <svg
      width="650"
      height="550"
      viewBox="0 0 650 550"
      xmlns="http://www.w3.org/2000/svg"
      className={styles.leiosSvg}
    >
      <rect width="650" height="550" fill="var(--svg-bg-color)" />
      <g transform="translate(300, 250)">
        <g stroke="var(--svg-border-color)" fill="none" strokeWidth="1">
          <circle cx="0" cy="0" r="160" opacity="0.5" />
          <circle cx="0" cy="0" r="120" opacity="0.4" />
          <circle cx="0" cy="0" r="80" opacity="0.4" />
          <circle cx="0" cy="0" r="40" opacity="0.4" />
        </g>
        <g stroke="var(--svg-text-secondary)" strokeWidth="2">
          <line x1="0" y1="0" x2="0" y2="-160" />
          <line x1="0" y1="0" x2="160" y2="0" />
          <line x1="0" y1="0" x2="0" y2="160" />
          <line x1="0" y1="0" x2="-160" y2="0" />
        </g>
        <polygon
          points="0,-155 150,0 0,140 -160,0"
          fill="rgba(255, 165, 0, 0.3)"
          stroke="#cc7a00"
          strokeWidth="2"
        />
        <polygon
          points="0,-135 65,0 0,42 -80,0"
          fill="rgba(75, 192, 192, 0.3)"
          stroke="#2e8b8b"
          strokeWidth="2"
        />
        <polygon
          points="0,-42 30,0 0,0 0,0"
          fill="rgba(220, 53, 69, 0.3)"
          stroke="#a71d2a"
          strokeWidth="2"
        />
        <g fill="rgba(255, 165, 0, 0.9)" stroke="#cc7a00" strokeWidth="2">
          <circle cx="0" cy="-155" r="4" />
          <circle cx="150" cy="0" r="4" />
          <circle cx="0" cy="140" r="4" />
          <circle cx="-160" cy="0" r="4" />
        </g>
        <g fill="#4bc0c0" stroke="#2e8b8b" strokeWidth="2">
          <circle cx="0" cy="-135" r="4" />
          <circle cx="65" cy="0" r="4" />
          <circle cx="0" cy="42" r="4" />
          <circle cx="-80" cy="0" r="4" />
        </g>
        <g fill="rgba(220, 53, 69, 0.9)" stroke="#a71d2a" strokeWidth="2">
          <circle cx="0" cy="-42" r="4" />
          <circle cx="30" cy="0" r="4" />
          <circle cx="0" cy="0" r="4" />
          <circle cx="0" cy="0" r="4" />
        </g>
        <text
          x="0"
          y="-185"
          textAnchor="middle"
          fontFamily="Arial"
          fontSize="14"
          fontWeight="bold"
          fill="var(--svg-text-color)"
        >
          Throughput
        </text>
        <text
          x="0"
          y="-171"
          textAnchor="middle"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-secondary)"
          fontWeight="bold"
        >
          (KiloBytes per Second)
        </text>
        <text
          x="200"
          y="5"
          textAnchor="start"
          fontFamily="Arial"
          fontSize="14"
          fontWeight="bold"
          fill="var(--svg-text-color)"
        >
          Inclusion Latency
        </text>
        <text
          x="200"
          y="19"
          textAnchor="start"
          fontFamily="Arial"
          fontSize="11"
          fontWeight="bold"
          fill="var(--svg-text-secondary)"
        >
          (Seconds)
        </text>
        <text
          x="0"
          y="190"
          textAnchor="middle"
          fontFamily="Arial"
          fontSize="14"
          fontWeight="bold"
          fill="var(--svg-text-color)"
        >
          Ecosystem Impact
        </text>
        <text
          x="0"
          y="204"
          textAnchor="middle"
          fontFamily="Arial"
          fontSize="11"
          fontWeight="bold"
          fill="var(--svg-text-secondary)"
        >
          (Adaptation Cost)
        </text>
        <text
          x="-185"
          y="5"
          textAnchor="end"
          fontFamily="Arial"
          fontSize="14"
          fontWeight="bold"
          fill="var(--svg-text-color)"
        >
          Time to Market
        </text>
        <text
          x="-185"
          y="19"
          textAnchor="end"
          fontFamily="Arial"
          fontSize="11"
          fontWeight="bold"
          fill="var(--svg-text-secondary)"
        >
          (Years)
        </text>
        <text
          x="12"
          y="-155"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          1,000+ TxkB/s
        </text>
        <text
          x="12"
          y="-115"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          100 TxkB/s
        </text>
        <text
          x="12"
          y="-75"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          10 TxkB/s
        </text>
        <text
          x="12"
          y="-35"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          1 TxkB/s
        </text>
        <text
          x="165"
          y="15"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          300s+
        </text>
        <text
          x="125"
          y="15"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          180s
        </text>
        <text
          x="85"
          y="15"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          90s
        </text>
        <text
          x="45"
          y="15"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          45s
        </text>
        <text
          x="12"
          y="155"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          Very High
        </text>
        <text
          x="12"
          y="115"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          High
        </text>
        <text
          x="12"
          y="75"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          Medium
        </text>
        <text
          x="12"
          y="35"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          Low
        </text>
        <text
          x="-165"
          y="15"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          3+ yr
        </text>
        <text
          x="-125"
          y="15"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          2 yr
        </text>
        <text
          x="-85"
          y="15"
          fontFamily="Arial"
          fontSize="11"
          fill="var(--svg-text-muted)"
        >
          1 yr
        </text>
      </g>
      <g transform="translate(325, 510)">
        <circle
          cx="-160"
          cy="0"
          r="4"
          fill="rgba(220, 53, 69, 0.9)"
          stroke="#a71d2a"
          strokeWidth="2"
        />
        <text
          x="-145"
          y="5"
          textAnchor="start"
          fontFamily="Arial"
          fontSize="12"
          fill="var(--svg-text-color)"
        >
          Ouroboros Praos
        </text>
        <circle
          cx="-20"
          cy="0"
          r="4"
          fill="#4bc0c0"
          stroke="#2e8b8b"
          strokeWidth="2"
        />
        <text
          x="-5"
          y="5"
          textAnchor="start"
          fontFamily="Arial"
          fontSize="12"
          fill="var(--svg-text-color)"
        >
          Proposed Leios
        </text>
        <circle
          cx="120"
          cy="0"
          r="4"
          fill="rgba(255, 165, 0, 0.9)"
          stroke="#cc7a00"
          strokeWidth="2"
        />
        <text
          x="135"
          y="5"
          textAnchor="start"
          fontFamily="Arial"
          fontSize="12"
          fill="var(--svg-text-color)"
        >
          Research Paper Leios
        </text>
      </g>
    </svg>
  );
}
