// Colour names map to the --pg-<name> custom properties in styles.module.css.
export type Color = "accent" | "dawn" | "blue" | "violet" | "ok";

export interface Step {
  id: string;
  // EB txs in kB; EB references follow as txs × 40/260.
  txs: number;
  // Plutus steps in G; memory and reference scripts follow from it.
  steps: number;
  // L_diff in seconds; L_vote = L_diff − 3·L_hdr.
  diff: number;
  color?: Color;
}

export interface Plan {
  name: string;
  title: string;
  color: Color;
  // Id of the step active on the network; earlier steps count as accomplished.
  current?: string;
  // Regenerates this plan from the milestones of plan `from`: outbound on one L_diff `plane`,
  // return at the minimum L_diff plus `margin`, steps named `prefix`1, `prefix`2, ….
  generate?: { from: string; plane: number; margin: number; prefix: string };
  steps: Step[];
}

export type Plans = Record<string, Plan>;

export type Status = "done" | "current" | "planned";

export function statuses(plan: Plan): Status[] {
  const ci = plan.current == null ? -1 : plan.steps.findIndex((s) => s.id === plan.current);
  return plan.steps.map((_, i) => (i < ci ? "done" : i === ci ? "current" : "planned"));
}
