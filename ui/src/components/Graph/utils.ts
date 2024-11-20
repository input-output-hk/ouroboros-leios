
export const isWithinRange = (elapsedTimestamp: number, targetTimestamp: number, rangeInMilliseconds: number): boolean => {
  const difference = elapsedTimestamp - targetTimestamp;
  return difference >= 0 && difference <= rangeInMilliseconds;
}
