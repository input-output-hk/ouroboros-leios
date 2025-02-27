#!/usr/bin/env bash

HOST=thelio
DB=leios2025w09

mongo --host "$HOST" "$DB" << EOI
db.receipts.drop()
EOI

mongo --host "$HOST" "$DB" queries/haskell-receipts.js
mongo --host "$HOST" "$DB" queries/rust-receipts.js
