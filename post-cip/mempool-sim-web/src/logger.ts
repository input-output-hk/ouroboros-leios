import pino from 'pino';
import type { Logger } from 'pino';


export let logger: Logger = pino({
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

export const makeLogger = (level: string, target: string): void => {
  logger = pino({
  level, // trace, debug, info, warn, error, fatal
  transport: {
    target,
    options: {
      colorize: true,
      translateTime: 'SYS:standard',
      ignore: 'pid,hostname',
    },
  },
})};
