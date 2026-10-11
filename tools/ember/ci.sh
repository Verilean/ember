#!/bin/sh
# What CI runs for Ember (plan §5): the ember-spec, ember-lang, ember-net,
# ember-esp32, ember-z80 and ember-proofs jobs.  Run inside `nix-shell` (gcc, sdcc, tshark, python3).
#
#   tools/ember/ci.sh          all jobs
#   tools/ember/ci.sh spec     one job (spec | lang | net | esp32 | z80 | proofs | size)
set -e
cd "$(dirname "$0")/../.."
job=${1:-all}

lake build
lake build ember-host ember-diff ember-pcap ember-replay ember-fixtures ember-gen \
           ember-emit ember-fuzz ember-lockstep ember-z80

case $job in
  all)
    # lake test covers every job at CI counts (1 000 sessions per
    # protocol, 1 000 random programs, 1 000 sessions through the C)
    lake test
    python3 tools/ember/size-report.py ;;
  spec)
    lake exe ember-fixtures --check
    lake exe ember-replay Tests/Ember/corpus/*/*.trace
    lake exe ember-gen all 1000 --quiet ;;
  lang)
    lake exe ember-fuzz 1000 --quiet ;;
  net)
    lake exe ember-lockstep Tests/Ember/corpus Tests/Ember/regress --gen all 1000 --c ;;
  esp32)
    tools/ember/qemu-test.sh ;;
  z80)
    tools/ember/z80-test.sh ;;
  proofs)
    lake build Ember.Proof ;;
  size)
    python3 tools/ember/size-report.py ;;
  *)
    echo "unknown job $job"; exit 2 ;;
esac
