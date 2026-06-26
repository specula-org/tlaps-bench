#!/bin/bash
# Base entrypoint for tlaps-bench agent containers.
# Runs the command directly — firewall is applied by ContainerRunner
# AFTER the install script completes (install needs network access).
set -e
exec "$@"
