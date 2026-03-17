# SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>
#
# SPDX-License-Identifier: EUPL-1.2

{
  description = "Build a cargo project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    advisory-db = {
      url = "github:rustsec/advisory-db";
      flake = false;
    };

    crane.url = "github:ipetkov/crane";
    crane-maturin.url = "github:vlaci/crane-maturin";

    git-hooks = {
      url = "github:cachix/git-hooks.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    shell-hooks.url = "github:vlaci/nix-shell-hooks";
  };

  outputs =
    {
      self,
      nixpkgs,
      crane,
      crane-maturin,
      advisory-db,
      git-hooks,
      shell-hooks,
      ...
    }:
    let
      supportedSystems = [
        "x86_64-linux"
        "x86_64-darwin"
        "aarch64-linux"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      nixpkgsFor = forAllSystems (
        system:
        import nixpkgs {
          inherit system;
          overlays = [
            self.overlays.default
            shell-hooks.overlays.default
          ];
        }
      );

      pre-commit-check = forAllSystems (
        system:
        let
          pkgs = nixpkgsFor.${system};
        in
        git-hooks.lib.${system}.run {
          src = ./.;
          package = pkgs.prek;
          hooks = {
            check-added-large-files.enable = true;
            end-of-file-fixer.enable = true;
            check-yaml.enable = true;
            check-toml.enable = true;
            nixfmt.enable = true;
            statix.enable = true;
            deadnix.enable = true;
            ruff.enable = true;
            ruff-format.enable = true;
            pyright.enable = true;
            cargo-check.enable = true;
            clippy = {
              enable = true;
              packageOverrides.cargo = pkgs.cargo;
              packageOverrides.clippy = pkgs.clippy;
            };
            rustfmt.enable = true;
            reuse.enable = true;
          };
        }
      );
    in
    {
      overlays.default =
        final: prev:
        let
          cmLib = crane-maturin.mkLib crane final;

          assetFilter =
            path: _type: builtins.match ".*pyi?$|.*/py\.typed$|.*/README.md$|.*/LICENSE$" path != null;
          sourceFilter = path: type: (assetFilter path type) || (cmLib.filterCargoSources path type);
          testFilter = p: _t: builtins.match ".*/(pyproject\.toml|tests|tests/.*\.py)$" p != null;
        in
        {
          pythonPackagesExtensions = prev.pythonPackagesExtensions ++ [
            (_python-final: _python-prev: {
              globlin = cmLib.buildMaturinPackage {
                pname = "globlin";
                src = final.lib.cleanSourceWith {
                  src = cmLib.path ./.;
                  filter = sourceFilter;
                };
                testSrc = final.lib.cleanSourceWith {
                  src = ./.;
                  filter = p: t: (sourceFilter p t) || (testFilter p t);
                };
                inherit advisory-db;
              };
            })
          ];
        };
      checks = forAllSystems (
        system:
        let
          inherit (nixpkgsFor.${system}.python3Packages) globlin;
        in
        globlin.passthru.tests
      );

      packages = forAllSystems (
        system:
        let
          inherit (nixpkgsFor.${system}.python3Packages) globlin;
        in
        {
          inherit globlin;
          default = globlin;
        }
      );

      devShells = forAllSystems (
        system:
        let
          pkgs = nixpkgsFor.${system};

        in
        {
          default = pkgs.mkShell {
            inherit (pre-commit-check.${system}) shellHook;
            packages =
              with pkgs;
              [
                cargo
                rustc
                cargo-msrv
                cargo-fuzz
                cargo-flamegraph
                cargo-llvm-cov
                uv
                python3Packages.uvVenvShellHook
                python3Packages.maturinImportShellHook
                python3Packages.autoPatchelfVenvShellHook
              ]
              ++ pre-commit-check.${system}.enabledPackages
              ++ lib.optional stdenv.hostPlatform.isLinux perf;
            env = with pkgs; {
              UV_LINK_MODE = "copy";
              LLVM_COV = "${llvmPackages_21.libllvm}/bin/llvm-cov";
              LLVM_PROFDATA = "${llvmPackages_21.libllvm}/bin/llvm-profdata";
            };
            uvExtraArgs = [
              "--group"
              "test"
            ];
          };
        }
      );
      formatter = forAllSystems (
        system:
        let
          pkgs = nixpkgsFor.${system};
          inherit (pre-commit-check.${system}.config) package configFile;
          script = ''
            ${pkgs.lib.getExe package} run --all-files --config ${configFile}
          '';
        in
        pkgs.writeShellScriptBin "pre-commit-run" script
      );
    };
}
