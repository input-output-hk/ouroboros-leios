CREATE TABLE txCache (
    txHashBytes BLOB NOT NULL PRIMARY KEY   -- raw bytes
  ,
    txBytes BLOB NOT NULL   -- valid CBOR
  ,
    txBytesSize INTEGER NOT NULL
  ,
    expiryUnixEpoch INTEGER NOT NULL
  ) WITHOUT ROWID;
CREATE TABLE ebPoints (
    ebSlot INTEGER NOT NULL
  ,
    ebHashBytes BLOB NOT NULL
  ,
    PRIMARY KEY (ebSlot, ebHashBytes)
  ) WITHOUT ROWID;
CREATE TABLE ebTxs (
    ebHashBytes BLOB NOT NULL   -- foreign key ebPoints.ebHashBytes
  ,
    txOffset INTEGER NOT NULL
  ,
    txHashBytes BLOB NOT NULL   -- raw bytes
  ,
    txBytesSize INTEGER NOT NULL
  ,
    txBytes BLOB   -- valid CBOR
  ,
    PRIMARY KEY (ebHashBytes, txOffset)
  ) WITHOUT ROWID;
CREATE INDEX ebPointsExpiry
    ON ebPoints (ebSlot ASC, ebHashBytes ASC);
CREATE INDEX txCacheExpiry
    ON txCache (expiryUnixEpoch ASC, txHashBytes);
CREATE INDEX missingEbTxs
    ON ebTxs (ebHashBytes DESC, txOffset ASC)
    WHERE txBytes IS NULL;
CREATE INDEX acquiredEbTxs
    ON ebTxs (ebHashBytes DESC, txOffset ASC)
    WHERE txBytes IS NOT NULL;
