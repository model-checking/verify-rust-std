#!/bin/bash
set -e

cd "$(dirname "$0")"
exec bash ../string.rs/verify.sh --negative
