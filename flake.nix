{
  description = "VST with Rocq 9.1 and mathcomp interoperability fixes";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/83199d0d373dd3ac2b9a1996b1d0263f76ab7a4c";
  inputs.rocq-mcp.url = "github:remix7531/rocq-mcp/46c7b0260b0b4d7c6facd71e087165280dd682ed";

  outputs =
    {
      self,
      nixpkgs,
      rocq-mcp,
    }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      # CompCert is unfree, so nixpkgs refuses to evaluate it, and with it VST,
      # unless it is admitted by name.
      eachSystem =
        f:
        nixpkgs.lib.genAttrs systems (
          system:
          f (
            import nixpkgs {
              inherit system;
              config.allowUnfreePredicate = pkg: builtins.elem (nixpkgs.lib.getName pkg) [ "compcert" ];
            }
          )
        );
      compCert316Overlay =
        { pkgs }:
        final: previous: {
          compcert = (previous.compcert.override { version = "3.16"; }).overrideAttrs (old: {
            patches = (old.patches or [ ]) ++ [
              (pkgs.fetchpatch {
                url = "https://github.com/AbsInt/CompCert/commit/5fd8013305ecf6fa7cd2ea5a0a6fa3ebb2bc31c5.patch";
                hash = "sha256-0bDqGSkvJM/rdCoFa6if/pJLJ4gYx2Bkld9wJaQDQOU=";
              })
            ];
          });
        };
      mkVST =
        {
          pkgs,
          coqPackages,
          src ? ./.,
        }:
        (coqPackages.callPackage (pkgs.path + /pkgs/development/rocq-modules/VST/default.nix) { })
        .overrideAttrs
          (_: {
            inherit src;
          });
    in
    {
      lib = { inherit compCert316Overlay mkVST; };

      packages = eachSystem (
        pkgs:
        let
          coqPackages = pkgs.coqPackages_9_1;
          VST = (mkVST { inherit pkgs coqPackages; }).overrideAttrs (old: {
            makeFlags = [
              "BITSIZE=64"
              "COMPCERT=bundled"
              "INSTALLDIR=$(out)/lib/coq/${coqPackages.coq.coq-version}/user-contrib/VST"
            ];
            propagatedBuildInputs = coqPackages.compcert.propagatedBuildInputs;
            postInstall = (old.postInstall or "") + ''
              mv $out/lib/coq/${coqPackages.coq.coq-version}/user-contrib/VST/compcert \
                $out/lib/coq/${coqPackages.coq.coq-version}/user-contrib/compcert
            '';
          });
        in
        {
          default = VST;
          inherit VST;
        }
      );

      devShells = eachSystem (
        pkgs:
        let
          coqPackages = pkgs.coqPackages_9_1;
          compcertTools =
            if pkgs.stdenv.hostPlatform.isx86_64 then
              pkgs.runCommand "compcert-tools" { } ''
                mkdir -p $out/bin
                ln -s ${coqPackages.compcert}/bin/clightgen $out/bin/clightgen
                ln -s ${coqPackages.compcert}/bin/ccomp $out/bin/ccomp
              ''
            else
              throw "The bundled VST proofs require an x86-64 CompCert generator.";
        in
        {
          default = pkgs.mkShell {
            inputsFrom = [ self.packages.${pkgs.stdenv.hostPlatform.system}.VST ];
            packages = [
              coqPackages.coq
              coqPackages.coq-lsp
              coqPackages.vsrocq-language-server
              coqPackages.iris
              coqPackages.mathcomp.ssreflect
              compcertTools
              rocq-mcp.packages.${pkgs.stdenv.hostPlatform.system}.default
              pkgs.bash
              pkgs.coreutils
              pkgs.findutils
              pkgs.gnugrep
              pkgs.gawk
              pkgs.gnumake
              pkgs.gcc
              pkgs.git
              pkgs.ripgrep
              pkgs.python3
              pkgs.nixfmt
            ];

            COMPCERT = "bundled";
            BITSIZE = "64";
            CLIGHTGEN = "${compcertTools}/bin/clightgen";

            shellHook = ''
              unset COQPATH
            '';
          };
        }
      );
    };
}
