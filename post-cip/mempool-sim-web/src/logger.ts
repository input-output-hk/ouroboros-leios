import pino from 'pino';
import type { Logger } from 'pino';


export const logger: Logger = pino({
  level: 'info', // trace, debug, info, warn, error, fatal
  transport: {
    target: 'pino-pretty',
  //target: 'pino/file',
    options: {
      colorize: true,
      translateTime: 'SYS:standard',
      ignore: 'pid,hostname',
    },
  },
});
