# A minimal DNix flake — OUR semantics, not cppNix.
#
# `outputs` is a plain function of its inputs (here unused: this flake is
# non-self-referential, so it does not read `self` — `self`-fixpoint needs
# general recursion, which currently diverges). Its one package output is a
# derivation built by `derivationStrict`.
#
#   dnx flake show  crates/dnx/examples   # list outputs + the drvPath
#   dnx flake check crates/dnx/examples   # evaluate all outputs (0 = ok)
#
# Field-order note: the evaluator's attribute-set literal lowering trips an
# `insert` limit when a non-scalar field (a list, or a nested attribute set) is
# defined *after* another field. So the nested `packages` output precedes the
# scalar `description`, and the derivation uses only scalar attributes — no
# `args = [ … ]` list (which would hit that same limit). A drvPath is therefore
# computable (`show`/`check` instantiate, they do not build); `realize` of a
# builder needing list args is the eval-seam slice that stays blocked.
{
  outputs = inputs: {
    packages = {
      x86_64-linux = {
        default = builtins.derivationStrict {
          name = "hello";
          system = "x86_64-linux";
          builder = "/bin/sh";
        };
      };
    };
    description = "a minimal dnx flake producing one derivation";
  };
}
