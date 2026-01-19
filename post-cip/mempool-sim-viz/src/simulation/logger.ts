type LogLevel = 'trace' | 'debug' | 'info' | 'warn' | 'error' | 'fatal';

type LogHandler = (level: LogLevel, data: Record<string, unknown>, msg: string) => void;

let logHandler: LogHandler | null = null;
let currentLevel: LogLevel = 'info';

const levels: Record<LogLevel, number> = {
  trace: 10,
  debug: 20,
  info: 30,
  warn: 40,
  error: 50,
  fatal: 60,
};

function shouldLog(level: LogLevel): boolean {
  return levels[level] >= levels[currentLevel];
}

function log(level: LogLevel, data: Record<string, unknown>, msg: string): void {
  if (!shouldLog(level)) return;

  if (logHandler) {
    logHandler(level, data, msg);
  }
}

export const logger = {
  trace: (data: Record<string, unknown>, msg: string) => log('trace', data, msg),
  debug: (data: Record<string, unknown>, msg: string) => log('debug', data, msg),
  info: (data: Record<string, unknown>, msg: string) => log('info', data, msg),
  warn: (data: Record<string, unknown> | string, msg?: string) => {
    if (typeof data === 'string') {
      log('warn', {}, data);
    } else {
      log('warn', data, msg ?? '');
    }
  },
  error: (data: Record<string, unknown>, msg: string) => log('error', data, msg),
  fatal: (data: Record<string, unknown> | string, msg?: string) => {
    if (typeof data === 'string') {
      log('fatal', {}, data);
    } else {
      log('fatal', data, msg ?? '');
    }
  },
  setLevel: (level: LogLevel) => { currentLevel = level; },
  setHandler: (handler: LogHandler | null) => { logHandler = handler; },
};
