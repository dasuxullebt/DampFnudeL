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

COPY alice29.txt coqdep.rb DiffStackT.hs Extraction.hs lcet10.txt Prefix.v TestCompress.hs asyoulik.txt coqfiles.mak DiffStack.v Extraction.v Lex.v ptt5 Transports.v asyoulik.txt.my CpdtTactics.v fields.c Quicksort.v xargs.1 Backreferences.v cp.html EffAlg.hs grammar.lsp LSB.v benchmark.hs DecompressHelper.hs EncodingRelationProperties2.v HashTable.v Makefile Repeat.v DecompressWithPheap.v EncodingRelationProperties.v Intervals.v NoRBRMain.hs Shorthand.v Combi.v DeflateCoding.v EncodingRelation.v kennedy.xls NoRBR.v StrongDec.v CompressMain.hs DiffStack.awk ExpListMain.hs KraftList.v Pheap.v sum Compress.v DiffStackMain.hs ExpList.v KraftVec.v plrabn12.txt Test.awk /var/deflate/

COPY diffarray-0.1.1 /var/diffarray

RUN cd /var/diffarray && \
    runhaskell Setup.hs configure && \
    runhaskell Setup.hs build && \
    runhaskell Setup.hs install

RUN /bin/bash
