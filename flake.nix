{
  description = "Monkeyscript interpreter writen in Rust";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    let 
      meta = (builtins.fromTOML (builtins.readFile ./Cargo.toml)).package;
      inherit (meta) name version;
      overlays = [ 
        (import rust-overlay)
        (self: super: {
          rustToolchain = super.rust-bin.stable.latest.default.override {
            extensions = [ "rust-src" "rust-analyzer" "llvm-tools-preview" ];
          };
        })
      ];
    in flake-utils.lib.eachDefaultSystem(system:
      let 
        pkgs = import nixpkgs { inherit system overlays; };
      in
      {
        devShells = {
          default = pkgs.mkShell {
            buildInputs = with pkgs; [
              rustToolchain
            ];
          };
        };

        packages = rec {
          default = monkeyscript-rust;
          monkeyscript-rust = pkgs.rustPlatform.buildRustPackage rec {
            pname = name;
            inherit version;
            src = ./.;
            cargoLock = {
              lockFile = ./Cargo.lock;
            };
            release = true;
          };
        };
      }
    );
}
