#!/bin/sh
# Re-record every Linux fixture of the corpus (plan §3.3).  Needs user
# namespaces and /dev/net/tun; no root.  Fixtures are committed: CI only
# replays them.
set -e
cd "$(dirname "$0")/../.."
lake build ember-host
R=tools/ember/record-linux.py
python3 $R responder icmp Tests/Ember/corpus/icmp
python3 $R responder udp Tests/Ember/corpus/udp
host=.lake/build/bin/ember-host
python3 $R client --name linux-ping --out Tests/Ember/corpus/icmp --host $host -- ping -c 3 -i 0.3 -s 56 10.0.0.1
python3 $R client --name linux-ping-s200 --out Tests/Ember/corpus/icmp --host $host -- ping -c 2 -i 0.3 -s 200 10.0.0.1
python3 $R client --name linux-nc-echo --out Tests/Ember/corpus/tcp --host $host -- sh -c 'printf "hello\n" | nc -N 10.0.0.1 7'
python3 $R client --name linux-nc-udp --out Tests/Ember/corpus/udp --host $host -- sh -c 'printf "hi\n" | nc -u -w1 10.0.0.1 7'
for s in echo bulk client-rst second-connection closed-port two-sessions; do
  python3 $R client --name linux-$s --out Tests/Ember/corpus/tcp --host $host -- python3 tools/ember/tcp-scenarios.py $s
done
python3 $R client --name linux-udp-echo --out Tests/Ember/corpus/udp --host $host -- python3 tools/ember/tcp-scenarios.py udp-echo
python3 $R client --name linux-server-close --settle 12 --out Tests/Ember/corpus/timer --host $host -- python3 tools/ember/tcp-scenarios.py server-close
# Ethernet + ARP (M1.11): Linux answering on a TAP device, and Linux as a client
python3 $R responder arp Tests/Ember/corpus/arp
python3 $R client --eth --name linux-eth-ping --out Tests/Ember/corpus/arp --host $host -- ping -c 2 -i 0.3 10.0.0.1
python3 $R client --eth --name linux-eth-tcp-echo --out Tests/Ember/corpus/arp --host $host -- python3 tools/ember/tcp-scenarios.py echo
# DHCP (M1.12) against dnsmasq; ~70 s to include a renewal at T1
python3 $R client --dnsmasq 10.0.0.50,10.0.0.50,2m --name linux-dhcp --settle 2 --out Tests/Ember/corpus/dhcp --host $host -- \
  sh -c 'for i in $(seq 1 40); do ping -c1 -W1 10.0.0.50 >/dev/null && echo bound && break; sleep 0.5; done; sleep 65; ping -c1 -W1 10.0.0.50 >/dev/null && echo still-bound'
# hand-written scenarios (Tests/Ember/Scenarios.lean)
lake exe ember-fixtures
