# Pull base image.
FROM ubuntu:24.04

ARG USERNAME=ubuntu
ARG USER_UID=1000

ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=Etc/UTC

RUN apt-get update \
    && apt-get install -y \
        sudo \
        gnupg \
        locales \
        wget \
        nano \
        fonts-powerline \
        lsb-release \
        software-properties-common \
    && apt clean \
    && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* 

RUN locale-gen en_US.UTF-8 
 
RUN apt update \
    && apt install -y \
        build-essential \
        cmake \
        curl \
        cutils \
        git \
        make \
        pkg-config \
        python3 \
        python3-pip \
        neovim \
        bc \
        cpio \
        rsync \
	strace \
	ltrace \
	gdb \
    && apt clean \
    && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* 

RUN update-alternatives --install /usr/bin/python python /usr/bin/python3 1
RUN update-alternatives --set python /usr/bin/python3 

RUN apt update \
    && apt install -y \
        python3-ijson \
	libgtest-dev \
    && apt clean \
    && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* 

RUN apt update \
    && apt-get install -y \
    python3 python3-pip python3-dev \
    gcc-arm-none-eabi gcc-aarch64-linux-gnu gcc-10-riscv64-linux-gnu \
    build-essential libxml2-utils ccache \
    ncurses-dev librsvg2-bin device-tree-compiler cmake \
    ninja-build curl zlib1g-dev texlive-fonts-recommended \
    texlive-latex-extra texlive-metapost texlive-bibtex-extra \
    mlton-compiler python3.12-venv haskell-stack tmux \
    && apt clean \
    && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* 

RUN echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME
RUN chmod 0440 /etc/sudoers.d/$USERNAME

USER $USERNAME
ENV HOME /home/$USERNAME
WORKDIR /home/$USERNAME

RUN python3 -m venv .pyenv
RUN curl https://storage.googleapis.com/git-repo-downloads/repo > ./repo && chmod a+rx ./repo

RUN mkdir isabell-repo && cd isabell-repo \
	&& wget https://www.isa-afp.org/release/afp-2025-10-25.tar.gz \
	&& tar -xvf afp-2025-10-25.tar.gz \
	&& rm  -f afp-2025-10-25.tar.gz

RUN mkdir -p playground/tools && cd playground/tools \
	&& ../../repo init -c --depth 1 -u https://github.com/EugeniyKozhanov/ver-manifests \
	&& ../../repo sync -cd -j7 

RUN mkdir -p ~/.isabelle/etc
COPY isabell_settings $HOME/.isabelle/etc/settings

RUN export BUILD_AGENT=1 && playground/tools/isabelle/bin/isabelle components -a
RUN playground/tools/isabelle/bin/isabelle components -u isabell-repo/afp-2025-10-25/thys
RUN export BUILD_AGENT=1 && playground/tools/isabelle/bin/isabelle build -bv AutoCorres2
RUN export BUILD_AGENT=1 && playground/tools/isabelle/bin/isabelle build -bv AutoCorres2_Main

SHELL ["/bin/bash", "-c"]

RUN source ~/.pyenv/bin/activate && pip3 install --upgrade pip
RUN source ~/.pyenv/bin/activate && pip3 install sel4-deps

RUN stack upgrade --binary-only
RUN stack --resolver lts-24.20  install cabal-install


CMD source ~/.pyenv/bin/activate  && /bin/tmux
