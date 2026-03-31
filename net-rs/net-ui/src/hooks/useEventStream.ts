import { useEffect, useRef } from "react";
import { useStore } from "@/store";
import type { OutputEvent } from "@/types";

const BASE = import.meta.env.VITE_API_URL ?? "";
const FLUSH_INTERVAL_MS = 50;

export function useEventStream() {
  const handleEvent = useStore((s) => s.handleEventBatch);
  const paused = useStore((s) => s.eventsPaused);
  const pausedRef = useRef(paused);
  pausedRef.current = paused;

  useEffect(() => {
    const url = `${BASE}/api/events/stream`;
    const source = new EventSource(url);
    let buffer: OutputEvent[] = [];
    let timer: ReturnType<typeof setTimeout> | null = null;

    function flush() {
      timer = null;
      if (buffer.length === 0) return;
      const batch = buffer;
      buffer = [];
      handleEvent(batch);
    }

    source.onmessage = (msg) => {
      if (pausedRef.current) return;
      try {
        const event: OutputEvent = JSON.parse(msg.data);
        buffer.push(event);
        if (!timer) {
          timer = setTimeout(flush, FLUSH_INTERVAL_MS);
        }
      } catch {
        // ignore parse errors
      }
    };

    source.onerror = () => {
      // EventSource auto-reconnects
    };

    return () => {
      source.close();
      if (timer) clearTimeout(timer);
      flush();
    };
  }, [handleEvent]);
}
