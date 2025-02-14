export const printBytes = (bytes: number) => {
  if (bytes >= 1024 * 1024 * 1024) {
    return `${(bytes / 1024 / 1024 / 1024).toFixed(3)} GB`;
  }
  if (bytes >= 1024 * 1024) {
    return `${(bytes / 1024 / 1024).toFixed(3)} MB`;
  }
  if (bytes >= 1024) {
    return `${(bytes / 1024).toFixed(3)} KB`;
  }
  return `${bytes} bytes`;
};
