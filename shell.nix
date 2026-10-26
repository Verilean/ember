# Development shell for Ember.
#   gcc            host C differential tests (M2, M3)
#   sdcc           Z80 profile compile checks of the emitted C
#   python3        fixture recording (tools/ember/record-linux.py)
#   dnsmasq        DHCP fixtures
#   wireshark-cli  tshark checks of ember-pcap output
#   iproute2, netcat, iputils: fixture recording in a user namespace
#   z88dk          z88dk-ticks, the reference for the Z80 model (M4z, M6.1)
#   riscv32-none-elf-gcc, esptool, qemu-system-riscv32-esp, gnumake:
#                  the ESP32-C3 image and Espressif's QEMU (M4)
{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  name = "ember";
  # _FORTIFY_SOURCE warns at -O0, and the emitted C is compiled with -Werror
  hardeningDisable = [ "fortify" ];
  buildInputs = with pkgs; [
    elan gcc sdcc python3 dnsmasq wireshark-cli iproute2 netcat-openbsd iputils
    z88dk gnumake esptool pkgsCross.riscv32-embedded.buildPackages.gcc
    (callPackage ./tools/ember/nix/qemu-esp32c3.nix {})
  ];
}
