{
  description = "Fast, pure, dependently typed language.";
  inputs = {
    # array.url = "github:wrsturgeon/array";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };
  outputs = { flake-utils, nixpkgs, self }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pname = "adam";
        owner = "wrsturgeon";
        version = "0.0.1";
        src = ./.;
        os-pkgs = import nixpkgs { inherit system; };
        pkgs = os-pkgs.coqPackages;
        # flakes = map (p: p.packages.${system}.default);
      in {
        packages.default = pkgs.mkCoqDerivation {
          inherit pname version owner src;
          buildInputs = with os-pkgs; [ ocaml ];
          # propagatedBuildInputs = flakes [ array ];
        };
      });
}
