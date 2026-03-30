import { useEffect, useRef } from "react";

export function usePolling(callback: () => void, intervalMs: number) {
  const cbRef = useRef(callback);
  cbRef.current = callback;

  useEffect(() => {
    cbRef.current();
    const id = setInterval(() => cbRef.current(), intervalMs);
    return () => clearInterval(id);
  }, [intervalMs]);
}
