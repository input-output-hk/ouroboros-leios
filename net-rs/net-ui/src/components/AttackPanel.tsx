import { useMemo, useState } from "react";
import {
  Box,
  Button,
  Divider,
  FormControl,
  InputLabel,
  MenuItem,
  Radio,
  RadioGroup,
  FormControlLabel,
  Select,
  Slider,
  Stack,
  TextField,
  Typography,
} from "@mui/material";
import { useStore } from "@/store";
import type {
  AttackRequest,
  BehaviourSelection,
  BehaviourSpec,
} from "@/types";

type BehaviourKind = "lazy-voter" | "rb-header-equivocator";
type SelectionKind =
  | "all"
  | "nodes"
  | "stake-random"
  | "stake-ordered"
  | "stake-fraction";

const numberFieldSx = {
  "& input[type=number]::-webkit-inner-spin-button, & input[type=number]::-webkit-outer-spin-button":
    {
      appearance: "auto",
      filter: "invert(1)",
    },
};

function parseIndices(csv: string): number[] {
  return csv
    .split(/[,\s]+/)
    .map((tok) => tok.trim())
    .filter((tok) => tok.length > 0)
    .map((tok) => Number(tok))
    .filter((n) => Number.isFinite(n) && Number.isInteger(n) && n >= 0);
}

export function AttackPanel() {
  const topology = useStore((s) => s.topology);
  const activeAttack = useStore((s) => s.activeAttack);
  const triggerAttack = useStore((s) => s.triggerAttack);
  const stopAttack = useStore((s) => s.stopAttack);

  const numNodes = topology?.nodes.length ?? 1;
  const countMax = Math.max(1, numNodes);

  const [behaviourKind, setBehaviourKind] = useState<BehaviourKind>("lazy-voter");
  const [ways, setWays] = useState("2");

  const [selectionKind, setSelectionKind] = useState<SelectionKind>("stake-ordered");
  const [nodeIndicesCsv, setNodeIndicesCsv] = useState("");
  const [count, setCount] = useState(1);
  const [fractionPct, setFractionPct] = useState(20);

  const indicesPreview = useMemo(() => parseIndices(nodeIndicesCsv), [nodeIndicesCsv]);

  const buildSpec = (): BehaviourSpec | null => {
    if (behaviourKind === "lazy-voter") return { kind: "lazy-voter" };
    if (behaviourKind === "rb-header-equivocator") {
      const w = Math.min(8, Math.max(2, Math.floor(Number(ways) || 2)));
      return { kind: "rb-header-equivocator", ways: w };
    }
    return null;
  };

  const buildSelection = (): BehaviourSelection | null => {
    switch (selectionKind) {
      case "all":
        return { kind: "all" };
      case "nodes":
        if (indicesPreview.length === 0) return null;
        return { kind: "nodes", indices: indicesPreview };
      case "stake-random":
        return { kind: "stake-random", count };
      case "stake-ordered":
        return { kind: "stake-ordered", count };
      case "stake-fraction":
        return { kind: "stake-fraction", fraction: fractionPct / 100 };
    }
  };

  const canTrigger = !!activeAttack ? false : buildSpec() !== null && buildSelection() !== null;

  const handleTrigger = () => {
    const spec = buildSpec();
    const selection = buildSelection();
    if (!spec || !selection) return;
    const req: AttackRequest = { behaviour: spec, selection };
    void triggerAttack(req);
  };

  const handleStop = () => {
    void stopAttack();
  };

  const indicesValid =
    selectionKind !== "nodes" ||
    (indicesPreview.length > 0 &&
      indicesPreview.every((i) => i < numNodes));

  return (
    <Box
      sx={{
        p: 2,
        display: "flex",
        flexDirection: "column",
        gap: 1.5,
        width: 280,
      }}
    >
      <Typography variant="subtitle2" sx={{ color: "#ff7043", fontWeight: 700 }}>
        Attack Trigger
      </Typography>

      {activeAttack ? (
        <Box
          sx={{
            p: 1,
            borderRadius: 1,
            border: "1px solid rgba(255,112,67,0.6)",
            bgcolor: "rgba(255,112,67,0.08)",
          }}
        >
          <Typography variant="caption" sx={{ color: "#ffab91" }}>
            Active: <b>{activeAttack.behaviour.kind}</b>
            {activeAttack.behaviour.kind === "rb-header-equivocator" &&
              ` (ways=${activeAttack.behaviour.ways})`}
            <br />
            {activeAttack.indices.length} node
            {activeAttack.indices.length === 1 ? "" : "s"}:&nbsp;
            {activeAttack.indices.slice(0, 8).join(", ")}
            {activeAttack.indices.length > 8 ? ", …" : ""}
          </Typography>
        </Box>
      ) : (
        <Typography variant="caption" sx={{ color: "text.secondary" }}>
          No attack active.
        </Typography>
      )}

      <Divider sx={{ borderColor: "rgba(255,255,255,0.1)" }} />

      <FormControl size="small" disabled={!!activeAttack}>
        <InputLabel id="behaviour-label">Behaviour</InputLabel>
        <Select
          labelId="behaviour-label"
          label="Behaviour"
          value={behaviourKind}
          onChange={(e) => setBehaviourKind(e.target.value as BehaviourKind)}
        >
          <MenuItem value="lazy-voter">LazyVoter</MenuItem>
          <MenuItem value="rb-header-equivocator">RbHeaderEquivocator</MenuItem>
        </Select>
      </FormControl>

      {behaviourKind === "rb-header-equivocator" && (
        <TextField
          label="ways"
          type="number"
          size="small"
          value={ways}
          onChange={(e) => setWays(e.target.value)}
          disabled={!!activeAttack}
          slotProps={{ htmlInput: { min: 2, max: 8, step: 1 } }}
          sx={numberFieldSx}
        />
      )}

      <Divider sx={{ borderColor: "rgba(255,255,255,0.1)" }} />

      <Typography variant="caption" sx={{ color: "text.secondary" }}>
        Target nodes
      </Typography>
      <RadioGroup
        value={selectionKind}
        onChange={(e) => setSelectionKind(e.target.value as SelectionKind)}
      >
        <FormControlLabel
          value="all"
          control={<Radio size="small" disabled={!!activeAttack} />}
          label="All"
        />
        <FormControlLabel
          value="stake-ordered"
          control={<Radio size="small" disabled={!!activeAttack} />}
          label={`Top ${count} by stake`}
        />
        <FormControlLabel
          value="stake-random"
          control={<Radio size="small" disabled={!!activeAttack} />}
          label={`${count} random (stake>0)`}
        />
        <FormControlLabel
          value="stake-fraction"
          control={<Radio size="small" disabled={!!activeAttack} />}
          label={`Stake fraction (${fractionPct}%)`}
        />
        <FormControlLabel
          value="nodes"
          control={<Radio size="small" disabled={!!activeAttack} />}
          label="Specific indices"
        />
      </RadioGroup>

      {(selectionKind === "stake-ordered" || selectionKind === "stake-random") && (
        <Stack direction="row" spacing={2} alignItems="center">
          <Slider
            value={count}
            min={1}
            max={countMax}
            step={1}
            onChange={(_, v) => setCount(v as number)}
            disabled={!!activeAttack}
          />
          <TextField
            type="number"
            size="small"
            value={count}
            onChange={(e) => {
              const n = Math.max(1, Math.min(countMax, Number(e.target.value) || 1));
              setCount(n);
            }}
            disabled={!!activeAttack}
            slotProps={{ htmlInput: { min: 1, max: countMax, step: 1 } }}
            sx={{ width: 80, ...numberFieldSx }}
          />
        </Stack>
      )}

      {selectionKind === "stake-fraction" && (
        <Stack direction="row" spacing={2} alignItems="center">
          <Slider
            value={fractionPct}
            min={1}
            max={100}
            step={1}
            onChange={(_, v) => setFractionPct(v as number)}
            disabled={!!activeAttack}
            valueLabelDisplay="auto"
            valueLabelFormat={(v) => `${v}%`}
          />
          <Typography variant="caption" sx={{ width: 40, textAlign: "right" }}>
            {fractionPct}%
          </Typography>
        </Stack>
      )}

      {selectionKind === "nodes" && (
        <TextField
          label="Node indices (csv)"
          size="small"
          value={nodeIndicesCsv}
          onChange={(e) => setNodeIndicesCsv(e.target.value)}
          disabled={!!activeAttack}
          placeholder="0, 2, 5"
          helperText={
            !indicesValid
              ? `Out of range (0..${numNodes - 1})`
              : indicesPreview.length > 0
                ? `→ ${indicesPreview.length} node(s)`
                : ""
          }
          error={!indicesValid && nodeIndicesCsv.length > 0}
        />
      )}

      <Divider sx={{ borderColor: "rgba(255,255,255,0.1)" }} />

      <Button
        variant="contained"
        color="warning"
        onClick={handleTrigger}
        disabled={!canTrigger || !indicesValid}
      >
        Trigger Attack
      </Button>
      <Button
        variant="outlined"
        color="warning"
        onClick={handleStop}
        disabled={!activeAttack}
      >
        Stop Attack
      </Button>
    </Box>
  );
}
