# if you are (your terminal) in the same directory of this file, then:
#   $ docker build -t formosa-25519:latest -f Dockerfile ../../
#
# otherwise, if it is run at the root directory of this project:
#   $ docker build -t formosa-25519:latest -f scripts/docker/Dockerfile .

FROM debian:stable-slim
MAINTAINER Tiago Oliveira <tiago.oliveira@sandboxquantum.com>

ARG USER=formosa
ARG JASMIN_COMMIT=f2cd3bf19df5a2d1fa5e35a6d5fefd090849b626
ARG EASYCRYPT_COMMIT=2b3bbadffa084466fd3450f367b2102e032c1301

ARG ALTERGO_VERSION=2.5.2
# note: CVC4_VERSION cannot be set here. Below, you can find and replace the corresponding url.
ARG Z3_VERSION=4.12.4

SHELL ["/bin/bash", "-c"]
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get --quiet --assume-yes update && \
    apt-get --quiet --assume-yes upgrade && \
    apt-get --quiet --assume-yes install apt-utils && \
    apt-get --quiet --assume-yes install \
      sudo wget curl git time xz-utils libicu-dev \
      ocaml ocaml-native-compilers camlp4-extra opam \
      autoconf debianutils libgmp-dev pkg-config zlib1g-dev \
      vim build-essential python3 python3-pip m4 libgsl-dev \
      libpcre3-dev jq parallel valgrind bash-completion \
      qemu-user-static binutils-arm-linux-gnueabi* gcc-arm-linux-gnueabi \
      bsdmainutils

RUN apt-get --quiet --assume-yes clean

RUN echo "%sudo  ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/sudoers && \
    chown root:root /etc/sudoers.d/sudoers && \
    chmod 0400 /etc/sudoers.d/sudoers && \
    useradd --create-home --shell /bin/bash --home-dir /home/$USER --gid root --groups sudo --uid 1001 $USER

USER $USER
WORKDIR /home/$USER

RUN curl -L https://nixos.org/nix/install > nix-install && \
    sh nix-install

# jasmin ######################################################################

RUN git clone https://gitlab.com/jasmin-lang/jasmin-compiler.git jasmin_$JASMIN_COMMIT
RUN cd jasmin_$JASMIN_COMMIT/ && \
    git fetch --append && \
    git checkout $JASMIN_COMMIT && \
    cd compiler/ && \
    USER=$USER source /home/$USER/.nix-profile/etc/profile.d/nix.sh && \
    nix-channel --update && \
    nix-shell --command "make" && \
    sudo install -D jasminc /usr/local/bin/ && \
    sudo install -D jasmin-ct /usr/local/bin/

# easycrypt ###################################################################

ENV OPAMYES=true OPAMVERBOSE=0

# alt-ergo (via opam)
RUN export OPAMJOBS=$(nproc) && \
    opam init --disable-sandboxing && \
    opam install opam-depext && \
    opam pin add -n alt-ergo $ALTERGO_VERSION && \
    opam install alt-ergo && \
    opam clean

# cvc4 (for a different version replace the following url)
RUN wget --no-verbose --show-progress --progress=bar:force:noscroll --timeout=10 --waitretry=5 --tries=5 \
      -O cvc4 https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt && \
    sudo install -D cvc4 /usr/local/bin/

# z3
RUN wget --no-verbose --show-progress --progress=bar:force:noscroll --timeout=10 --waitretry=5 --tries=5 \
      https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION/z3-$Z3_VERSION-x64-glibc-2.31.zip && \
    unzip -j z3-$Z3_VERSION-x64-glibc-2.31.zip z3-$Z3_VERSION-x64-glibc-2.31/bin/z3 && \
    sudo install -D z3 /usr/local/bin/

# easycrypt
RUN export OPAMJOBS=$(nproc) && \
    opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git#${EASYCRYPT_COMMIT} && \
    opam depext easycrypt && \
    opam install easycrypt && \
    opam clean

RUN opam config exec -- why3 config detect

RUN echo "eval $(opam env)" >> /home/$USER/.bashrc

RUN mkdir -p /home/$USER/.config/easycrypt/ && \
    echo "[general]" > /home/$USER/.config/easycrypt/easycrypt.conf && \
    echo "idirs = Jasmin:/home/$USER/jasmin_$JASMIN_COMMIT/eclib/" >> /home/$USER/.config/easycrypt/easycrypt.conf

# formosa-25519 ###############################################################

RUN mkdir formosa-25519
COPY --chown=$USER:root . /home/$USER/formosa-25519
WORKDIR /home/$USER/formosa-25519

