#!/usr/bin/env bash

HOST=thelio
DB=leios2025w09

mongo --host "$HOST" "$DB" << EOI
db.flight.drop()
EOI

mongo --host "$HOST" "$DB" queries/rust-flight.js
