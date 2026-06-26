#!/bin/bash
set -e
npm install -g @anthropic-ai/claude-code --cache /tmp/.npm && rm -rf /tmp/.npm
