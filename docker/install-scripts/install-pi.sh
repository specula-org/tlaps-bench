#!/bin/bash
set -e
npm install -g --ignore-scripts @earendil-works/pi-coding-agent@0.80.10 --cache /tmp/.npm && rm -rf /tmp/.npm
pi install npm:pi-provider-kiro@0.8.1
