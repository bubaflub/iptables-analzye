FROM debian:stretch

RUN apt-get update && \
    apt-get -y install z3 python-z3 python-ipaddress && \
    apt-get autoremove -y && \
    rm -rf /var/lib/apt/lists/*
COPY iptables-analyze.py /

