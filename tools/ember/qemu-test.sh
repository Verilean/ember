#!/bin/sh
# Build the ESP32-C3 images and run every QEMU test (plan M4, CI job
# `ember-esp32`).  Run inside nix-shell.
#
#   tools/ember/qemu-test.sh            build, then all tests
#   tools/ember/qemu-test.sh build      the images only
#   tools/ember/qemu-test.sh corpus --verbose      one test, with its options
#   SESSIONS=1000 tools/ember/qemu-test.sh         more generated sessions
#                                       (default 100 per protocol, x3 variants)
set -e
cd "$(dirname "$0")/../.."
out=.lake/build/esp32c3
mk() { make -s -f runtime/esp32c3/Makefile OUT=$out "$@"; }

lake build ember-emit ember-diff
mkdir -p $out
lake exe ember-emit net --profile rv32 > $out/net.c
lake exe ember-emit sliploop --profile rv32 > $out/sliploop.c
cmp -s $out/net.c Tests/Ember/golden/net.rv32.c || { echo "Tests/Ember/golden/net.rv32.c is stale (lake exe ember-emit --golden)"; exit 1; }

mk NAME=boot  DEFS="-DAPP=APP_BOOT"
mk NAME=trap  DEFS="-DAPP=APP_TRAP"
mk NAME=hello DEFS="-DAPP=APP_HELLO"
mk NAME=echo  DEFS="-DAPP=APP_ECHO"
mk NAME=sliploop PROG=$out/sliploop.c
# the stack: as shipped (500 ms tick), for fixture replay (ticks on
# request), and with QEMU's instruction counter in the idle line
mk NAME=stack        PROG=$out/net.c
mk NAME=stack-test   PROG=$out/net.c DEFS="-DEMBER_TICK_HOST=1"
mk NAME=stack-icount PROG=$out/net.c DEFS="-DEMBER_TICK_HOST=1 -DEMBER_ICOUNT=1"
# what a board would run: no trace at all
mk NAME=stack-quiet  PROG=$out/net.c DEFS="-DEMBER_TRACE=0"

[ "$1" = build ] && exit 0
if [ $# -gt 0 ]; then exec python3 tools/ember/esp32.py "$@"; fi
for t in boot trap hello echo slip corpus tick; do
  python3 tools/ember/esp32.py $t
done
# generated sessions (as generated, mutated, re-chunked) that the Spec and
# the interpreter agree on, replayed on the target
gen=$out/sessions
rm -rf $gen
lake exe ember-lockstep --gen slip ${SESSIONS:-100} --dump $gen > /dev/null
python3 tools/ember/esp32.py corpus $gen
