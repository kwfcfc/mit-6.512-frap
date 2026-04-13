{
  description = "MIT 6.5120 FRAP - Formal Reasoning About Programs dev environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { nixpkgs, flake-utils, ... }:
    with flake-utils.lib; eachSystem ["x86_64-linux" "aarch64-darwin"] (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Rocq 9.0 with standard library
        rocqStdlib = pkgs.rocqPackages.stdlib;

        # Lean 4 (for pset14 and LeanLectures)
        # elan = pkgs.elan;
      in
      {
        devShells.default = pkgs.mkShell {
          name = "frap-dev";

          buildInputs = [
            # Rocq prover + standard library
            pkgs.rocq-core
            rocqStdlib

            # Language server for VS Code (VsRocq)
            pkgs.rocqPackages.vsrocq-language-server

            # Lean 4 toolchain manager (handles lean-toolchain files)
            # elan

            # Build tools
            pkgs.gnumake

            # Optional: PDF generation for FRAP textbook
            # pkgs.texliveFull
          ];

          shellHook = ''
            echo "MIT 6.5120 FRAP Development Environment"
            echo "  Rocq:  $(rocq --version 2>/dev/null | head -1)"
            echo "  Lean:  managed by elan (run 'lake build' in pset14 to bootstrap)"
            echo ""
            echo "Quick start:"
            echo "  make -C frap lib          # Build FRAP library"
            echo "  cd pset01_ProgramAnalysis && make  # Build pset01"
            echo ""
          '';
        };
      }
    );
}
