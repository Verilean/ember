#!/bin/sh
# Run an ESP32-C3 flash image in Espressif's QEMU (plan M4.0, §3.5).
#
#   tools/ember/qemu-run.sh IMAGE.bin [--dir D] [--timeout S] [--gdb] [--log] [--icount]
#
# UART0 (SLIP) is the unix socket D/uart0.sock, UART1 (trace) is
# D/uart1.sock; QEMU waits for neither.  Without --dir, UART0 is discarded
# and UART1 goes to stdout.  --timeout stops QEMU after S seconds (exit
# status 0: a timeout is the normal end of a run).  --gdb waits for gdb
# on :1234; --log writes interrupts and guest errors to D/qemu.log;
# --icount makes virtual time a function of executed instructions.
set -e
img=$1; shift
dir=; timeout=; extra=
while [ $# -gt 0 ]; do
  case $1 in
    --dir) dir=$2; shift ;;
    --timeout) timeout=$2; shift ;;
    --gdb) extra="$extra -s -S" ;;
    --log) log=1 ;;
    --icount) extra="$extra -icount shift=0,sleep=off" ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
  shift
done
if [ -n "$dir" ]; then
  mkdir -p "$dir"
  serial="-serial unix:$dir/uart0.sock,server=on,wait=off -serial unix:$dir/uart1.sock,server=on,wait=off"
  [ -n "$log" ] && extra="$extra -d int,guest_errors,unimp -D $dir/qemu.log"
else
  serial="-serial null -serial file:/dev/stdout"
  [ -n "$log" ] && extra="$extra -d int,guest_errors,unimp"
fi
# a private copy: QEMU opens the flash image for writing
run=$(mktemp "${TMPDIR:-/tmp}/ember-flash.XXXXXX")
trap 'rm -f "$run"' EXIT
cp "$img" "$run"
cmd="qemu-system-riscv32-esp -M esp32c3 -display none -monitor none -drive file=$run,if=mtd,format=raw $serial $extra"
if [ -n "$timeout" ]; then
  timeout "$timeout" $cmd || { s=$?; [ $s -eq 124 ] || exit $s; }
else
  $cmd
fi
