#!/usr/bin/env bash

rsync -vazc --progress --stats $(cat ip):2025-11-19T21\:18\:04.log .
