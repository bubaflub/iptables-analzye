build:
		docker build . -t iptables-analyze

run: build
		docker run -it iptables-analyze /bin/bash -l
