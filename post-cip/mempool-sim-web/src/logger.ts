import pino from 'pino';
import type { Logger } from 'pino';

const isBrowser = typeof window !== 'undefined';
const isNodeTestRuntime =
  !isBrowser &&
  typeof process !== 'undefined' &&
  (process.env.NODE_ENV === 'test' ||
    process.env.NODE_TEST_CONTEXT !== undefined ||
    process.argv.includes('--test'));

const makeNodeLogger = (level: string, target?: string): Logger => {
  // `pino.transport` spins up a worker; avoid that path for node:test.
  if (isNodeTestRuntime) {
    return pino({ level });
  }

  return pino({
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
};

// Browser: use pino's built-in browser support (outputs to console)
// Node.js: use pino-pretty for formatted output
export let logger: Logger = isBrowser
  ? pino({ level: 'warn', browser: { asObject: false } })
  : makeNodeLogger('info');

export const makeLogger = (level: string, target?: string): void => {
  if (isBrowser) {
    logger = pino({ level, browser: { asObject: false } });
  } else {
    logger = makeNodeLogger(level, target);
  }
};
