FROM ubuntu:24.04

# Avoid interactive prompts
ENV DEBIAN_FRONTEND=noninteractive

# Install minimal dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates git python3 \
    libstdc++6 libgmp10 make \
    default-jre-headless \
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

# Lock down tlapm so the unprivileged bench user cannot tamper with the
# library: root-owned and read-only for everyone.
RUN chown -R root:root /opt/tlapm && chmod -R a-w /opt/tlapm

# ------------------------------------------------------------------
# Cheat checker (compiled binary) + SANY assets, all baked in so the
# cheat-detection logic is never exposed as source the agent could read.
# Layout under /opt/sany matches run.sh's REPO_ROOT math
# (sany-dump/../../.. == /opt/sany), so tla2tools.jar + community resolve.
# ------------------------------------------------------------------
COPY check_proof_bin /usr/local/bin/check_proof_bin
COPY lib/tla2tools.jar /opt/sany/lib/tla2tools.jar
COPY lib/community /opt/sany/lib/community
COPY src/dataset/sany-dump /opt/sany/src/dataset/sany-dump

# DumpSemantics is precompiled on the host (docker/build.sh runs sany-dump/build.sh)
# and the .class files are COPY'd in via the sany-dump dir above. The image ships
# only a JRE (no javac), so fail loudly if the precompiled class is missing, then
# stamp the .class files as newer than the .java (touch -c never creates files) so
# run.sh's `-nt` staleness check stays false and never tries to recompile.
RUN test -f /opt/sany/src/dataset/sany-dump/build/DumpSemantics.class \
      || { echo "ERROR: precompiled DumpSemantics.class missing from build context." >&2; \
           echo "       Build via 'bash docker/build.sh' (needs host javac) so the JRE-only image works." >&2; \
           exit 1; } \
    && touch -c /opt/sany/src/dataset/sany-dump/build/*.class

# SANY gate wiring (consumed by tlacore inside check_proof_bin).
ENV SANY_RUN_SH=/opt/sany/src/dataset/sany-dump/run.sh \
    TLAPS_LIB=/opt/tlapm/lib/tlapm/stdlib \
    COMMUNITY_LIB=/opt/sany/lib/community

# Lock down the checker + SANY assets: root-owned, read + execute only.
RUN chmod 0755 /usr/local/bin/check_proof_bin \
    && chown -R root:root /usr/local/bin/check_proof_bin /opt/sany \
    && chmod -R a-w /opt/sany

# Remove sudo
RUN apt-get purge -y sudo 2>/dev/null; rm -f /usr/bin/sudo /usr/sbin/sudo; true

# Create unprivileged user (remove default ubuntu user first to free UID 1000)
RUN userdel -r ubuntu 2>/dev/null || true; useradd -m -s /bin/bash -u 1000 bench

# Copy entrypoint (build context is the repo root)
COPY docker/entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh

WORKDIR /home/bench

# Start as root for iptables setup, then drop to bench user
ENTRYPOINT ["/entrypoint.sh"]
CMD ["bash"]
