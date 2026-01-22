import pino from 'pino';
import type { Logger } from 'pino';

const isBrowser = typeof window !== 'undefined';

// Browser: use pino's built-in browser support (outputs to console)
// Node.js: use pino-pretty for formatted output
export let logger: Logger = isBrowser
  ? pino({ level: 'info', browser: { asObject: false } })
  : pino({
      level: 'info', // trace, debug, info, warn, error, fatal
      transport: {
        target: 'pino-pretty',
        options: {
          colorize: true,
          translateTime: 'SYS:standard',
          ignore: 'pid,hostname',
        },
      },
    });

export const makeLogger = (level: string, target?: string): void => {
  if (isBrowser) {
    logger = pino({ level, browser: { asObject: false } });
  } else {
    logger = pino({
      level, // trace, debug, info, warn, error, fatal
      transport: {
        target: target ?? 'pino-pretty',
        options: {
          colorize: true,
          translateTime: 'SYS:standard',
          ignore: 'pid,hostname',
        },
      },
    });
  }
};
