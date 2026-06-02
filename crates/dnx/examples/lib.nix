# A small library attrset, imported by main.nix.
# `import ./lib.nix` reads + parses this file in a fresh scope and splices the
# resulting value in place of the import expression (imports-design.md §2).
{
  answer = 42;
  base = 100;
  name = "dnx";
}
