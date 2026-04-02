import { useEffect, useState } from "react";
import { Box, Button, CircularProgress, Divider, TextField, Typography } from "@mui/material";
import { useStore } from "@/store";

/** Dark-mode styling for number input spin buttons. */
const numberFieldSx = {
  "& input[type=number]::-webkit-inner-spin-button, & input[type=number]::-webkit-outer-spin-button": {
    appearance: "auto",
    filter: "invert(1)",
  },
};

export function ControlPanel() {
  const clusterConfig = useStore((s) => s.clusterConfig);
  const restarting = useStore((s) => s.restarting);
  const restartCluster = useStore((s) => s.restartCluster);

  // Store as strings so the user can freely delete and retype.
  const [numNodes, setNumNodes] = useState("5");
  const [degree, setDegree] = useState("3");
  const [minLatency, setMinLatency] = useState("5");
  const [maxLatency, setMaxLatency] = useState("300");
  const [seed, setSeed] = useState("");
  const [rbBodyValidationMs, setRbBodyValidationMs] = useState("1000");

  useEffect(() => {
    if (clusterConfig) {
      if (clusterConfig.num_nodes != null) setNumNodes(String(clusterConfig.num_nodes));
      if (clusterConfig.degree != null) setDegree(String(clusterConfig.degree));
      if (clusterConfig.min_latency_ms != null) setMinLatency(String(clusterConfig.min_latency_ms));
      if (clusterConfig.max_latency_ms != null) setMaxLatency(String(clusterConfig.max_latency_ms));
      setSeed(clusterConfig.seed != null ? String(clusterConfig.seed) : "");

      const nc = clusterConfig.node_config ?? {};
      const rbVal = nc["validation.rb_body_validation_ms_constant"];
      if (rbVal != null) setRbBodyValidationMs(String(rbVal));
    }
  }, [clusterConfig]);

  const numNodesN = Number(numNodes) || 0;
  const minLatencyN = Number(minLatency) || 0;
  const maxLatencyN = Number(maxLatency) || 0;
  const valid = numNodesN >= 1 && minLatencyN <= maxLatencyN;

  const handleRestart = () => {
    restartCluster({
      num_nodes: numNodesN,
      degree: Number(degree) || 1,
      min_latency_ms: minLatencyN,
      max_latency_ms: maxLatencyN,
      seed: seed !== "" ? Number(seed) : undefined,
      node_config: {
        "validation.rb_body_validation_ms_constant": Number(rbBodyValidationMs) || 0,
      },
    });
  };

  return (
    <Box sx={{
      p: 2,
      display: "flex",
      flexDirection: "column",
      gap: 1.5,
      width: 260,
    }}>
      <Typography variant="subtitle2" sx={{ color: "#90caf9", fontWeight: 700 }}>
        Cluster Topology
      </Typography>
      <TextField
        label="Nodes"
        type="number"
        size="small"
        value={numNodes}
        onChange={(e) => setNumNodes(e.target.value)}
        disabled={restarting}
        slotProps={{ htmlInput: { min: 1, max: 100 } }}
        sx={numberFieldSx}
      />
      <TextField
        label="Degree"
        type="number"
        size="small"
        value={degree}
        onChange={(e) => setDegree(e.target.value)}
        disabled={restarting}
        slotProps={{ htmlInput: { min: 1, max: 50 } }}
        sx={numberFieldSx}
      />
      <TextField
        label="Min latency (ms)"
        type="number"
        size="small"
        value={minLatency}
        onChange={(e) => setMinLatency(e.target.value)}
        disabled={restarting}
        slotProps={{ htmlInput: { min: 0 } }}
        sx={numberFieldSx}
      />
      <TextField
        label="Max latency (ms)"
        type="number"
        size="small"
        value={maxLatency}
        onChange={(e) => setMaxLatency(e.target.value)}
        disabled={restarting}
        slotProps={{ htmlInput: { min: 0 } }}
        sx={numberFieldSx}
      />
      <TextField
        label="Seed (optional)"
        type="number"
        size="small"
        value={seed}
        onChange={(e) => setSeed(e.target.value)}
        disabled={restarting}
        placeholder="random"
        sx={numberFieldSx}
      />

      <Divider sx={{ borderColor: "rgba(255,255,255,0.1)", my: 0.5 }} />

      <Typography variant="subtitle2" sx={{ color: "#90caf9", fontWeight: 700 }}>
        Node Config
      </Typography>
      <TextField
        label="RB body validation (ms)"
        type="number"
        size="small"
        value={rbBodyValidationMs}
        onChange={(e) => setRbBodyValidationMs(e.target.value)}
        disabled={restarting}
        slotProps={{ htmlInput: { min: 0, step: 100 } }}
        sx={numberFieldSx}
      />

      <Button
        variant="contained"
        onClick={handleRestart}
        disabled={restarting || !valid}
        sx={{ mt: 0.5 }}
      >
        {restarting ? (
          <>
            <CircularProgress size={18} sx={{ mr: 1 }} />
            Restarting...
          </>
        ) : (
          "Restart Cluster"
        )}
      </Button>
    </Box>
  );
}
