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
  const updating = useStore((s) => s.updating);
  const restartCluster = useStore((s) => s.restartCluster);
  const updateNodeConfig = useStore((s) => s.updateNodeConfig);

  // Store as strings so the user can freely delete and retype.
  const [numNodes, setNumNodes] = useState("5");
  const [degree, setDegree] = useState("3");
  const [minLatency, setMinLatency] = useState("5");
  const [maxLatency, setMaxLatency] = useState("300");
  const [seed, setSeed] = useState("");
  const [rbGenProb, setRbGenProb] = useState("0.05");
  const [rbBodyValidationMs, setRbBodyValidationMs] = useState("1000");

  const topologySource = clusterConfig?.topology_source ?? null;
  const isYaml = topologySource?.type === "yaml";

  useEffect(() => {
    if (clusterConfig) {
      if (topologySource?.type === "random") {
        setNumNodes(String(topologySource.num_nodes));
        setDegree(String(topologySource.degree));
        setMinLatency(String(topologySource.min_latency_ms));
        setMaxLatency(String(topologySource.max_latency_ms));
      }
      setSeed(clusterConfig.seed != null ? String(clusterConfig.seed) : "");

      const nc = clusterConfig.node_config ?? {};
      const rbGenVal = nc["production.rb_generation_probability"];
      if (rbGenVal != null) setRbGenProb(String(rbGenVal));
      const rbVal = nc["validation.rb_body_validation_ms_constant"];
      if (rbVal != null) setRbBodyValidationMs(String(rbVal));
    }
  }, [clusterConfig, topologySource]);

  const numNodesN = Number(numNodes) || 0;
  const minLatencyN = Number(minLatency) || 0;
  const maxLatencyN = Number(maxLatency) || 0;
  // YAML-mode restarts don't edit topology params, so we don't validate them.
  const valid = isYaml || (numNodesN >= 1 && minLatencyN <= maxLatencyN);

  const busy = restarting || updating;

  const nodeConfigPayload = () => ({
    "production.rb_generation_probability": Number(rbGenProb) || 0,
    "validation.rb_body_validation_ms_constant": Number(rbBodyValidationMs) || 0,
  });

  const handleRestart = () => {
    restartCluster({
      // In YAML mode we don't override topology_source — the cluster
      // restarts with whatever YAML was loaded at startup.  In random
      // mode we send back the edited params.
      topology_source: isYaml
        ? undefined
        : {
            type: "random",
            num_nodes: numNodesN,
            degree: Number(degree) || 1,
            min_latency_ms: minLatencyN,
            max_latency_ms: maxLatencyN,
            // Preserve whatever stake distribution the cluster was
            // configured with (we don't expose a UI for it yet).
            stake_distribution:
              topologySource?.type === "random"
                ? topologySource.stake_distribution
                : "equal",
          },
      seed: seed !== "" ? Number(seed) : undefined,
      node_config: nodeConfigPayload(),
    });
  };

  const handleUpdate = () => {
    updateNodeConfig(nodeConfigPayload());
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
        Node Config
      </Typography>
      <TextField
        label="RB gen probability"
        type="number"
        size="small"
        value={rbGenProb}
        onChange={(e) => setRbGenProb(e.target.value)}
        disabled={busy}
        slotProps={{ htmlInput: { min: 0, max: 1, step: 0.01 } }}
        sx={numberFieldSx}
      />
      <TextField
        label="RB body validation (ms)"
        type="number"
        size="small"
        value={rbBodyValidationMs}
        onChange={(e) => setRbBodyValidationMs(e.target.value)}
        disabled={busy}
        slotProps={{ htmlInput: { min: 0, step: 100 } }}
        sx={numberFieldSx}
      />

      <Button
        variant="contained"
        onClick={handleUpdate}
        disabled={busy}
        sx={{ mt: 0.5 }}
      >
        {updating ? (
          <>
            <CircularProgress size={18} sx={{ mr: 1 }} />
            Updating...
          </>
        ) : (
          "Update Nodes"
        )}
      </Button>

      <Divider sx={{ borderColor: "rgba(255,255,255,0.1)", my: 0.5 }} />

      <Typography variant="subtitle2" sx={{ color: "#90caf9", fontWeight: 700 }}>
        Cluster Topology
      </Typography>

      {isYaml && topologySource?.type === "yaml" && (
        <Box
          sx={{
            p: 1,
            borderRadius: 1,
            border: "1px solid rgba(255,255,255,0.1)",
            background: "rgba(144,202,249,0.05)",
            fontSize: 12,
            color: "rgba(255,255,255,0.75)",
          }}
        >
          <Typography variant="caption" sx={{ display: "block", color: "#90caf9", fontWeight: 600 }}>
            YAML-loaded topology
          </Typography>
          <Box sx={{ mt: 0.5, fontFamily: "ui-monospace, monospace", fontSize: 11, wordBreak: "break-all" }}>
            {topologySource.path}
          </Box>
          {topologySource.node_limit != null && (
            <Box sx={{ mt: 0.5 }}>
              capped at first <b>{topologySource.node_limit}</b> nodes (top-N by stake)
            </Box>
          )}
          <Box sx={{ mt: 0.5, opacity: 0.7 }}>
            Topology params (nodes / degree / latencies) come from the YAML file and aren't editable here.
            "Restart Cluster" reloads the same YAML.
          </Box>
        </Box>
      )}

      {!isYaml && (
        <>
          <TextField
            label="Nodes"
            type="number"
            size="small"
            value={numNodes}
            onChange={(e) => setNumNodes(e.target.value)}
            disabled={busy}
            slotProps={{ htmlInput: { min: 1, max: 100 } }}
            sx={numberFieldSx}
          />
          <TextField
            label="Degree"
            type="number"
            size="small"
            value={degree}
            onChange={(e) => setDegree(e.target.value)}
            disabled={busy}
            slotProps={{ htmlInput: { min: 1, max: 50 } }}
            sx={numberFieldSx}
          />
          <TextField
            label="Min latency (ms)"
            type="number"
            size="small"
            value={minLatency}
            onChange={(e) => setMinLatency(e.target.value)}
            disabled={busy}
            slotProps={{ htmlInput: { min: 0 } }}
            sx={numberFieldSx}
          />
          <TextField
            label="Max latency (ms)"
            type="number"
            size="small"
            value={maxLatency}
            onChange={(e) => setMaxLatency(e.target.value)}
            disabled={busy}
            slotProps={{ htmlInput: { min: 0 } }}
            sx={numberFieldSx}
          />
        </>
      )}

      <TextField
        label="Seed (optional)"
        type="number"
        size="small"
        value={seed}
        onChange={(e) => setSeed(e.target.value)}
        disabled={busy}
        placeholder="random"
        sx={numberFieldSx}
      />

      <Button
        variant="contained"
        color="secondary"
        onClick={handleRestart}
        disabled={busy || !valid}
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
