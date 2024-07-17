# inspired by https://github.com/phadej/docker-haskell-example/blob/master/Dockerfile
FROM haskell:9.6.3 AS build

RUN apt-get update -y && \
    apt-get upgrade -y && \
    apt-get install -y automake build-essential pkg-config libffi-dev libgmp-dev libssl-dev libtinfo-dev libsystemd-dev zlib1g-dev make g++ tmux git jq wget libncursesw5 libtool autoconf

COPY ./cabal.project /app/cabal.project

RUN mkdir /app/leios-sim

COPY ./leios-sim/leios-sim.cabal /app/leios-sim/leios-sim.cabal

WORKDIR /app

RUN cabal update
RUN cabal build --dependencies-only all

COPY . /app

RUN cabal build all

# Make final binary a bit smaller
RUN strip dist-newstyle/build/x86_64-linux/ghc-9.6.3/leios-sim-0.1.0.0/x/leios/build/leios/leios

FROM ubuntu:22.04

# Set up locales
RUN apt-get update && \
    apt-get install -y locales && \
    rm -rf /var/lib/apt/lists/*
RUN locale-gen en_US.UTF-8 && \
    update-locale LC_ALL=en_US.UTF-8 LANG=en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LC_ALL en_US.UTF-8

WORKDIR /app
EXPOSE 8091

COPY --from=build /app/leios-sim/* /app/
COPY --from=build /app/dist-newstyle/build/x86_64-linux/ghc-9.6.3/leios-sim-0.1.0.0/x/leios/build/leios/leios /app

ENTRYPOINT ["/app/leios"]
