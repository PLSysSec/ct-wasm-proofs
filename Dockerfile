FROM debian:stretch-slim
SHELL ["/bin/bash", "-c"]

ENV VERSION 2017

# packages
RUN apt-get -y update && \
  apt-get install -y curl less lib32stdc++6 libgomp1 libwww-perl rlwrap unzip wget texlive texlive-latex-extra texlive-math-extra && \
  apt-get clean

# user
RUN useradd -m isabelle && (echo isabelle:isabelle | chpasswd)
USER isabelle

# Isabelle
WORKDIR /home/isabelle
COPY Isabelle.tar.gz ./

RUN tar xzf Isabelle.tar.gz && \
  mv Isabelle${VERSION} Isabelle && \
  rm -rf Isabelle.tar.gz Isabelle/contrib/jdk/x86-linux

USER root
RUN mkdir /.isabelle && chmod -R 777 /.isabelle

ENTRYPOINT ["Isabelle/bin/isabelle"]
