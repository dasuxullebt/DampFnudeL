FROM debian:stretch

ENV DEBIAN_FRONTEND noninteractive 
RUN apt-get update && apt-get install -y \
    time \
    ghc \
    libghc-shake-dev \
    libghc-persistent-dev \
    libghc-persistent-sqlite-dev \
    libghc-persistent-template-dev \
    libghc-digest-dev \
    coq \
    make \
    gawk \
    sqlite3

COPY ./* /var/deflate/
COPY diffarray-0.1.1 /var/diffarray

RUN cd /var/diffarray && \
    runhaskell Setup.hs configure && \
    runhaskell Setup.hs build && \
    runhaskell Setup.hs install

RUN /bin/bash
