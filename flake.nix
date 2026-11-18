{
  description = "sudo-rs development and verification environment (Charon/Aeneas -> Lean 4, Quint)";

  inputs = {
    aeneas.url = "github:AeneasVerif/aeneas/8f4466db9f0d59267b8e76b54473a21a005cf7be";
    # Reuse the nixpkgs pinned by Aeneas so the tool closure stays shared.
    nixpkgs.follows = "aeneas/nixpkgs";
  };

  outputs =
    { nixpkgs, aeneas, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (
        system: pkgs: {
          default = pkgs.mkShell {
            packages = [
              # Rust -> LLBC -> Lean extraction
              aeneas.packages.${system}.aeneas
              aeneas.packages.${system}.charon
              # Lean 4 (toolchain selected by proofs/lean/lean-toolchain)
              pkgs.elan
              # Building and testing sudo-rs itself
              pkgs.gcc
              pkgs.rustc
              pkgs.cargo
              pkgs.clippy
              pkgs.rustfmt
              pkgs.pkg-config
              pkgs.linux-pam
              # Lifecycle model checking
              pkgs.quint
              pkgs.jdk
            ];
          };
        }
      );
    };
}
