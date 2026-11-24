# Group theory in Lean 4

[Read the 72 theorem declarations and their proofs in Groups/Basic.lean](Groups/Basic.lean). The development uses core Lean, with explicit hypotheses for the group operations. It covers identity and inverse laws, associative products, powers and element orders, and group laws for cyclic and dihedral groups.

The root module is [Groups.lean](Groups.lean). The other module files it imports are placeholders.

## Build

With Elan installed, run `lake build` from this directory. The project pins Lean 4.35.0 and has no package dependencies.
