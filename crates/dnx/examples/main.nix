# `dnx eval --file main.nix` → 142.
#
# `import ./lib.nix` resolves relative to THIS file's directory (not the cwd),
# parses lib.nix in a fresh scope, and splices the resulting attrset in place.
# We then select a field from it (`lib.answer` = 42) and do arithmetic on it,
# showing a structured value crosses the import boundary (imports-design.md §6,
# `let x = import ./lib.nix; in x.y`).
let
  lib = import ./lib.nix;
in
  lib.answer + 100
