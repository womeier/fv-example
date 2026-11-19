{
  description = "A minimal Rocq merge-sort example";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in {
      packages = forAllSystems (system:
        let pkgs = import nixpkgs { inherit system; };
        in {
          default = pkgs.stdenvNoCC.mkDerivation {
            pname = "sorting-example";
            version = "0.1.0";
            src = nixpkgs.lib.cleanSource self;
            nativeBuildInputs = [ pkgs.rocq-core pkgs.rocqPackages.stdlib ];
            buildPhase = "make";
            installPhase = ''
              mkdir -p $out/lib/rocq/user-contrib/SortingExample
              cp theories/*.v theories/*.vo $out/lib/rocq/user-contrib/SortingExample/
            '';
          };
        });

      devShells = forAllSystems (system:
        let pkgs = import nixpkgs { inherit system; };
        in {
          default = pkgs.mkShell {
            packages = [ pkgs.rocq-core pkgs.rocqPackages.stdlib pkgs.gnumake ];
          };
        });
    };
}
