# The Nix twin of examples/hello.py. Both lower to the same core derivation and
# instantiate to the same drvPath — only the surface syntax differs.
derivationStrict { name = "hello"; builder = "/bin/sh"; system = "x86_64-linux"; }
