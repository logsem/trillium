{
  description = "A devShell for Fairneris";

  inputs = {
    nixpkgs.url      = "github:ineol/nixpkgs/update-vscoq-lsp";
    flake-utils.url  = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
      in
      with pkgs;
      {
        devShell = mkShell rec {
          buildInputs = with coqPackages_8_19; [
            coq
            vscoq-language-server
          ];
        };
      }
      );
  }
