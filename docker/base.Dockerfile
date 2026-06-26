# syntax=docker/dockerfile:1

# Stage 1: Compile check_proof_bin from source (no source leaks to final image)
FROM python:3.12-slim AS builder

RUN apt-get update && apt-get install -y --no-install-recommends binutils && rm -rf /var/lib/apt/lists/*
RUN pip install --no-cache-dir pyinstaller

COPY pyproject.toml /build/pyproject.toml
COPY src/ /build/src/

RUN cd /build && pyinstaller --onefile --name check_proof_bin \
        --paths src/common --paths src \
        --collect-submodules tlacheck \
        --collect-submodules tlacore \
        src/common/check_proof.py \
    && mv dist/check_proof_bin /check_proof_bin

# Stage 2: Final image (agent runtime)
FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive
SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

# Layer 1: System packages (rarely changes)
RUN --mount=type=cache,target=/var/cache/apt,sharing=locked \
    --mount=type=cache,target=/var/lib/apt,sharing=locked \
    rm -f /etc/apt/apt.conf.d/docker-clean \
    && apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates git python3 python3-pip \
    libstdc++6 libgmp10 make \
    default-jdk-headless \
    iptables iproute2 dnsutils libcap2-bin

# Layer 2: Node.js (rarely changes)
RUN --mount=type=cache,target=/var/cache/apt,sharing=locked \
    --mount=type=cache,target=/var/lib/apt,sharing=locked \
    rm -f /etc/apt/apt.conf.d/docker-clean \
    && curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get install -y --no-install-recommends nodejs

# Layer 3: tlapm (pinned version, ~850MB download, rarely changes)
ARG TLAPM_TAG=1.6.0-pre
ARG TLAPM_ASSET=tlapm-${TLAPM_TAG}-x86_64-linux-gnu.tar.gz
ARG TLAPM_URL=https://github.com/tlaplus/tlapm/releases/download/${TLAPM_TAG}/${TLAPM_ASSET}
RUN --mount=type=cache,target=/tmp/downloads \
    if [ ! -f /tmp/downloads/${TLAPM_ASSET} ]; then \
      curl -fsSL -o /tmp/downloads/${TLAPM_ASSET} "${TLAPM_URL}"; \
    fi \
    && tar -xzf /tmp/downloads/${TLAPM_ASSET} -C /opt/ \
    && rm -f /opt/tlapm/bin/tlapm_lsp

# Layer 4: tla2tools.jar / SANY (downloaded inside Docker — no host dependency)
ARG TLATOOLS_TAG=v1.8.0
ARG TLATOOLS_URL=https://github.com/tlaplus/tlaplus/releases/download/${TLATOOLS_TAG}/tla2tools.jar
RUN --mount=type=cache,target=/tmp/downloads \
    if [ ! -f /tmp/downloads/tla2tools-${TLATOOLS_TAG}.jar ]; then \
      curl -fsSL -o /tmp/downloads/tla2tools-${TLATOOLS_TAG}.jar "${TLATOOLS_URL}"; \
    fi \
    && mkdir -p /opt/sany/lib \
    && cp /tmp/downloads/tla2tools-${TLATOOLS_TAG}.jar /opt/sany/lib/tla2tools.jar

# Layer 5: Community modules (downloaded inside Docker — no host dependency)
ARG COMMUNITY_TAG=202604221529
ARG COMMUNITY_URL=https://github.com/tlaplus/CommunityModules/archive/refs/tags/${COMMUNITY_TAG}.tar.gz
RUN --mount=type=cache,target=/tmp/downloads \
    if [ ! -f /tmp/downloads/community-${COMMUNITY_TAG}.tar.gz ]; then \
      curl -fsSL -o /tmp/downloads/community-${COMMUNITY_TAG}.tar.gz "${COMMUNITY_URL}"; \
    fi \
    && mkdir -p /opt/community \
    && tar -xzf /tmp/downloads/community-${COMMUNITY_TAG}.tar.gz -C /tmp/ \
    && cp /tmp/CommunityModules-${COMMUNITY_TAG}/modules/*.tla /opt/community/ \
    && rm -rf /tmp/CommunityModules-${COMMUNITY_TAG}

# Layer 6: SANY DumpSemantics compilation (needs tla2tools.jar + JDK)
COPY src/dataset/sany-dump /opt/sany/src/dataset/sany-dump
RUN cp -r /opt/community /opt/sany/lib/community \
    && cd /opt/sany/src/dataset/sany-dump && bash build.sh

# Layer 7: check_proof_bin (changes when src/ changes)
COPY --from=builder /check_proof_bin /usr/local/bin/check_proof_bin

ENV SANY_RUN_SH=/opt/sany/src/dataset/sany-dump/run.sh \
    TLAPS_LIB=/opt/tlapm/lib/tlapm/stdlib \
    COMMUNITY_LIB=/opt/community \
    TLAPS_IN_CONTAINER=1

# Layer 8: LiteLLM agent script
COPY src/evaluator/backends/litellm_agent.py /opt/litellm_agent.py

# Lock down checker + SANY
RUN chmod 0755 /usr/local/bin/check_proof_bin \
    && chown -R root:root /usr/local/bin/check_proof_bin /opt/sany \
    && chmod -R a-w /opt/sany

# Layer 9: Install scripts + firewall + entrypoint (changes sometimes)
COPY docker/install-scripts /opt/install-scripts
RUN chmod -R +x /opt/install-scripts

COPY docker/firewall.sh /opt/firewall.sh
RUN chmod +x /opt/firewall.sh

COPY docker/base-entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh

WORKDIR /workspace

ENTRYPOINT ["/entrypoint.sh"]
CMD ["bash"]
