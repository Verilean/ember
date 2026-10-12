#!/bin/sh
# Build the Z80 images — with SDCC, and with the own back end — and run
# every Z80 test on the Lean model of the machine (plan M4z, M6; CI job
# `ember-z80`).  Run inside nix-shell.
#
#   tools/ember/z80-test.sh             build, then all tests
#   tools/ember/z80-test.sh build       the images only
#   SESSIONS=1000 FUZZ=2000 OWNFUZZ=20000 CHECK=500 tools/ember/z80-test.sh    more of each
set -e
cd "$(dirname "$0")/../.."
out=.lake/build/z80
mk() { make -s -f runtime/z80/Makefile OUT=$out "$@"; }
z80=.lake/build/bin/ember-z80

lake build ember-emit ember-z80 ember-lockstep
mkdir -p $out
lake exe ember-emit net --profile sdcc-z80 > $out/net.c
lake exe ember-emit sliploop --profile sdcc-z80 > $out/sliploop.c
cmp -s $out/net.c Tests/Ember/golden/net.sdcc-z80.c || { echo "Tests/Ember/golden/net.sdcc-z80.c is stale (lake exe ember-emit --golden)"; exit 1; }

mk NAME=echo PROG=runtime/z80/echo.c
mk NAME=sliploop PROG=$out/sliploop.c
mk NAME=stack PROG=$out/net.c
[ "$1" = build ] && exit 0

# the model itself against z88dk-ticks, random instruction streams
if command -v z88dk-ticks > /dev/null; then
  $z80 check ${CHECK:-50} --len 1000
  # the assembler of the own back end against z88dk's
  $z80 asm-check
else
  echo "z80 model vs z88dk-ticks, assembler vs z88dk-z80asm: z88dk not installed, skipped"
fi
$z80 echo $out/echo.ihx
$z80 slip $out/sliploop.ihx
$z80 replay $out/stack.ihx Tests/Ember/corpus Tests/Ember/regress
# generated sessions the Spec and the interpreter agree on
gen=$out/sessions
rm -rf $gen
lake exe ember-lockstep --gen slip ${SESSIONS:-10} --dump $gen > /dev/null
$z80 replay $out/stack.ihx $gen
$z80 fuzz ${FUZZ:-200}

# the own back end (plan M6): no C compiler from here on
$z80 rt-check
$z80 ir-fuzz ${OWNFUZZ:-2000}
$z80 own-fuzz ${OWNFUZZ:-2000}
$z80 own-build sliploop --out $out
$z80 slip $out/sliploop-own.ihx
$z80 own-build net --out $out
$z80 replay $out/net-own.ihx Tests/Ember/corpus Tests/Ember/regress
$z80 replay $out/net-own.ihx $gen
# the same without the passes on the assembly: the image the proofs of M7.3 speak of
$z80 own-fuzz ${PLAINFUZZ:-500} --plain
$z80 own-build sliploop --plain --out $out
$z80 slip $out/sliploop-own-plain.ihx
$z80 own-build net --plain --out $out
$z80 replay $out/net-own-plain.ihx Tests/Ember/corpus Tests/Ember/regress
# the static bound on the stack of each image: own-size fails when the analysis gives up or the bound
# exceeds the room above the static RAM
# (the exit status is that of own-size, not of a pipe into tail: on failure all it printed is shown)
size() {
  if o=$($z80 own-size "$@"); then
    printf '%s\n' "$o" | tail -1
  else
    printf '%s\n' "$o"
    echo "FAIL: own-size $*"
    return 1
  fi
}
for img in net sliploop; do
  size $img --trace 0 || exit 1
  size $img || exit 1
  size $img --plain || exit 1
done
