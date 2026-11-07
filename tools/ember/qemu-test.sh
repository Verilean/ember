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
lake exe ember-emit http --profile rv32 > $out/http.c
lake exe ember-emit crypto --profile rv32 > $out/crypto.c
lake exe ember-emit https --profile rv32 > $out/https.c
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
# the HTTP server of plan M8 (Net.Http, two connections): as shipped, and
# for replay; tools/ember/qemu-bridge.py puts the first on stdin/stdout
mk NAME=stack-http      PROG=$out/http.c
mk NAME=stack-http-test PROG=$out/http.c DEFS="-DEMBER_TICK_HOST=1"
# the crypto of plan M8.5 behind a request/answer loop (Net.Crypto.testProg)
mk NAME=crypto-test PROG=$out/crypto.c DEFS="-DEMBER_TICK_HOST=1"
# the HTTPS server of plan M8.7 (Net.Tls, two connections): as shipped, and for replay
mk NAME=stack-https      PROG=$out/https.c
mk NAME=stack-https-test PROG=$out/https.c DEFS="-DEMBER_TICK_HOST=1"

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
# HTTP (plan M8.4): the recorded curl session and the exchanges of
# Tests/Ember/HttpTests.lean (mutated, re-chunked, ticks mid-frame), with
# Spec.Srv's traces, replayed on the HTTP image
lake build test
rm -rf $out/http-sessions
EMBER_HTTP_DUMP=$out/http-sessions .lake/build/bin/test
python3 tools/ember/esp32.py corpus --image stack-http-test Tests/Ember/http $out/http-sessions
# the crypto (plan M8.5b): requests and the reference's answers, on the image
rm -rf $out/crypto-sessions
EMBER_CRYPTO_DUMP=$out/crypto-sessions .lake/build/bin/test
python3 tools/ember/esp32.py corpus --image crypto-test $out/crypto-sessions
# HTTPS (plan M8.7): the recorded curl and openssl sessions and the TLS
# sessions of Tests/Ember/TlsTests.lean, with Spec.Srv.Tls's traces, on the image
rm -rf $out/https-sessions
EMBER_HTTPS_DUMP=$out/https-sessions .lake/build/bin/test
python3 tools/ember/esp32.py corpus --image stack-https-test $out/https-sessions
