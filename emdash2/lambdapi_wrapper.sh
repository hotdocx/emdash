#!/bin/bash
# Set a 30-second timeout and a 4GB memory limit (adjust as needed)
# The "timeout" command kills the process if it runs too long
# "ulimit" prevents the process from exceeding a memory cap

ulimit -v 4194304  # Limit virtual memory to 4GB (in KB)
# timeout 90s /home/user1/.opam/default/bin/lambdapi "$@"
lambdapi "$@"
