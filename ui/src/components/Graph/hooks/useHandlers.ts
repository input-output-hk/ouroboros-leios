import { useGraphContext } from "@/contexts/GraphContext/context";
import { ESpeedOptions } from "@/contexts/GraphContext/types";
import { useCallback } from "react";

export const useHandlers = () => {
  const { setSentTxs, setCurrentTime, setPlaying, setSpeed, simulationPauseTime, simulationStartTime, intervalId } = useGraphContext();

  const drawCanvas = useCallback(() => {

  }, [])

  const handleResetSim = useCallback(() => {
    setCurrentTime(0);
    setPlaying(false);
    setSentTxs(new Set());
    setSpeed(ESpeedOptions["3/10"]);
    simulationStartTime.current = 0;
    simulationPauseTime.current = 0;

    if (intervalId.current) {
      clearInterval(intervalId.current);
      intervalId.current = null;
    }

    drawCanvas();
  }, [])

  return {
    handleResetSim,
    drawCanvas
  }
}
