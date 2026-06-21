#!/usr/bin/env bash
# Keep IDE-launched Lambdapi processes below 4 GB of virtual memory. A timeout
# is deliberately not used here because editor integrations may restart a
# timed-out server repeatedly.

ulimit -v 4194304
exec lambdapi "$@"
