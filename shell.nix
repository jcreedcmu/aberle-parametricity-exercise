{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    (pkgs.agda.withPackages (ps: [ ps.standard-library ]))
  ];
}

# (load-file (let ((coding-system-for-read 'utf-8))
#                 (shell-command-to-string "agda-mode locate")))
