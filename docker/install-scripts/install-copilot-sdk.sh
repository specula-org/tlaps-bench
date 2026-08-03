#!/bin/bash
set -e

pip install --no-cache-dir --break-system-packages github-copilot-sdk
python3 -m copilot download-runtime
