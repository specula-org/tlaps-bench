#!/bin/bash
set -e
npm install -g --ignore-scripts @earendil-works/pi-coding-agent --cache /tmp/.npm && rm -rf /tmp/.npm
pi install npm:pi-provider-kiro
