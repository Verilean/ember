# Development shell for Ember (M1–M3, host side).
#   gcc            host C differential tests (M2, M3)
#   sdcc           Z80 profile compile checks of the emitted C
#   python3        fixture recording (tools/ember/record-linux.py)
#   dnsmasq        DHCP fixtures
#   wireshark-cli  tshark checks of ember-pcap output
#   iproute2, netcat, iputils: fixture recording in a user namespace
{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  name = "ember";
  # _FORTIFY_SOURCE warns at -O0, and the emitted C is compiled with -Werror
  hardeningDisable = [ "fortify" ];
  buildInputs = with pkgs; [
    elan gcc sdcc python3 dnsmasq wireshark-cli iproute2 netcat-openbsd iputils
  ];
}
