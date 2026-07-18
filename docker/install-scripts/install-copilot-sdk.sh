#!/bin/bash
set -e

pip install --no-cache-dir --break-system-packages github-copilot-sdk==1.0.7
python3 -m copilot download-runtime
