# One substrate, two languages. This Python `derivation(...)` reads back as the
# byte-identical attrset that examples/hello.nix's `derivationStrict {...}` does,
# and instantiates to the same drvPath (dnx-py-interop.md §3, §5).
#
#   dnx py examples/hello.py        # Python frontend
#   dnx eval --file examples/hello.nix   # Nix frontend → SAME attrset
derivation(name="hello", builder="/bin/sh", system="x86_64-linux")
