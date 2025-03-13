FROM ubuntu:22.04

# Install dependencies
RUN apt-get update && apt-get -y install \
    curl git build-essential cmake \
    python3 python3-pip python3-dev \
    --no-install-recommends \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz \
    && ./elan-init -y --default-toolchain leanprover/lean4:stable \
    && rm ./elan-init

# Add elan to path
ENV PATH="$HOME/.elan/bin:${PATH}"

# Set working directory
WORKDIR /workspace

# Non-root user setup
ARG USERNAME=vscode
ARG USER_UID=1000
ARG USER_GID=$USER_UID

RUN groupadd --gid $USER_GID $USERNAME \
    && useradd --uid $USER_UID --gid $USER_GID -m $USERNAME \
    && apt-get update \
    && apt-get install -y sudo \
    && echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME \
    && chmod 0440 /etc/sudoers.d/$USERNAME

# Switch to non-root user
USER $USERNAME
ENV HOME=/home/$USERNAME
ENV PATH="/home/$USERNAME/.elan/bin:${PATH}"

# Pre-install the lean toolchain for the non-root user
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y