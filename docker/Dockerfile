FROM ubuntu:24.04

# Avoid interactive prompts
ENV DEBIAN_FRONTEND=noninteractive

# Install minimal dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates git python3 \
    libstdc++6 libgmp10 make \
    iptables iproute2 dnsutils gosu \
    && rm -rf /var/lib/apt/lists/*

# Install Node.js 22 (for codex CLI)
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/*

# Install agent CLIs (codex for OpenAI, claude code for Anthropic, copilot for GitHub)
RUN npm install -g @openai/codex @anthropic-ai/claude-code @github/copilot && npm cache clean --force

# Install tlapm 1.6 pre-release (rolling, last refreshed upstream 2026-04-14).
# Tarball top-level dir is `tlapm/`, so extracting into /opt/ produces /opt/tlapm/.
# Drop tlapm_lsp (~40MB language server) — not needed for batch verification.
RUN curl -fsSL -o /tmp/tlapm.tar.gz \
    https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz \
    && tar -xzf /tmp/tlapm.tar.gz -C /opt/ \
    && rm /tmp/tlapm.tar.gz \
    && rm -f /opt/tlapm/bin/tlapm_lsp

# Vendor CommunityModules into tlapm's stdlib dir so that benchmarks which
# EXTEND SequencesExt / BagsExt / SequencesExtTheorems / ... resolve via
# `tlapm -I <stdlib>` — the path both the agent prompt and check_proof use.
# Pinned to the same tag as scripts/install_deps.sh (lib/community/).
RUN curl -fsSL -o /tmp/community.tar.gz \
    https://github.com/tlaplus/CommunityModules/archive/refs/tags/202604221529.tar.gz \
    && tar -xzf /tmp/community.tar.gz -C /tmp/ \
    && cp /tmp/CommunityModules-202604221529/modules/*.tla /opt/tlapm/lib/tlapm/stdlib/ \
    && rm -rf /tmp/community.tar.gz /tmp/CommunityModules-202604221529

# Lock down tlapm: prevent AI from tampering with library files
# Remove write permission — bench user cannot restore (not owner, no sudo)
# chattr +i is applied at container start in entrypoint.sh (needs CAP_LINUX_IMMUTABLE)
RUN chmod -R a-w /opt/tlapm

# Remove sudo
RUN apt-get purge -y sudo 2>/dev/null; rm -f /usr/bin/sudo /usr/sbin/sudo; true

# Create unprivileged user (remove default ubuntu user first to free UID 1000)
RUN userdel -r ubuntu 2>/dev/null || true; useradd -m -s /bin/bash -u 1000 bench

# Copy entrypoint
COPY entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh

WORKDIR /home/bench

# Start as root for iptables setup, then drop to bench user
ENTRYPOINT ["/entrypoint.sh"]
CMD ["bash"]
