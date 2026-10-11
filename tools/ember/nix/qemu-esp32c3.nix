# Espressif's QEMU fork (machine `esp32c3`), from Espressif's release
# binaries: nixpkgs' qemu has no ESP32 machines.  Used by M4.
{ pkgs ? import <nixpkgs> {} }:
pkgs.stdenv.mkDerivation rec {
  pname = "qemu-esp32c3";
  version = "9.2.2-20260417";
  src = pkgs.fetchurl {
    url = "https://github.com/espressif/qemu/releases/download/esp-develop-${version}/"
        + "qemu-riscv32-softmmu-esp_develop_${builtins.replaceStrings ["-"] ["_"] version}-x86_64-linux-gnu.tar.xz";
    sha256 = "0xsfv3i0fwcvvp099frwz5g5n7ywb80pszwzd6xjra818zh06zsl";
  };
  nativeBuildInputs = [ pkgs.autoPatchelfHook ];
  buildInputs = with pkgs; [ pixman libgcrypt SDL2 zlib libslirp glib stdenv.cc.cc.lib ];
  installPhase = ''
    mkdir -p $out
    cp -r bin share $out/
    mv $out/bin/qemu-system-riscv32 $out/bin/qemu-system-riscv32-esp
  '';
}
