# Comparator
Comparator is a trustworthy judge for Lean proofs. It relies having an existing Lean installation as
well as two additional binaries in `PATH`:
1. [`landrun`](https://github.com/Zouuup/landrun)
2. [`lean4export`](https://github.com/leanprover/lean4export/) at a version that is compatible with
   whatever Lean version your project is targeting.

The comparator is configured through a JSON file:
```
{
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["todo1"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": false
}
```
Where `Challenge.lean` contains at least a theorem named `todo1` that has a `sorry` (or any other proof)
and `Solution.lean` is provided by a party trying to convince you that they have proven `todo1` by
writing out the same theorem but with a proper proof attached.

Given the following assumptions:
1. Only the `Solution.lean` file is controlled by a potentially malicious party, all other files
   including most crucially `lakefile.toml`/`lakefile.lean` and `Challenge.lean` are controlled by
   you.
2. You have not previously tried to compile the `Solution` file (as that might compromise your
   `Challenge` file to make it seem like you are looking for a different proof than you actually are)
3. You have the `landrun` and `lean4export` binary in `PATH`
4. `landrun` works correctly on your system and `Solution.lean` does not
   exploit any bugs in `landrun` that allow a process to escape its sandbox
5. The Lean kernel is correct (in the future we will add support for running different kernels as
   well to increase trust further)
6. You are not running this under a privileged user

If the following command succeeds:
```
lake env path/to/comparator/binary path/to/config.json
```

All theorems in `Solution` that are listed in `theorem_names` are guaranteed to:
1. Prove the same statement as provided in `Challenge`
2. Use no more axioms than listed in `permitted_axioms`
3. Be accepted by the Lean kernel

Note that running `lake exe cache get` to download a Mathlib cache is acceptable before running the
comparator if you trust the cache to not be modified as to, e.g. contain different definitions from
the one you would expect.

Furthermore, it is possible to avoid trusting `landrun`'s ability to sandbox the `Solution.lean` file:
if you have obtained a fully pre-built `.lake` directory through other means and without compromising your
checking environment, `Solution.lean` will not be rebuilt.

## Checking with Additional Kernels
Comparator currently supports checking with the [nanoda](https://github.com/ammkrn/nanoda_lib)
kernel in addition to the builtin Lean one. To do this you need to set the `enable_nanoda` flag in
the JSON configuration to `true`. Note that this feature currently requires:
- The nanoda branch https://github.com/ammkrn/nanoda_lib/tree/debug

In the near term future this will be merged into the respective main branch and become
available by default. Furthermore, nanoda will be used by the default once this has happened.

To make nanoda available to comparator, you need to checkout the branch, install a recent Rust
version and compile nanoda using `cargo build --release`. Then you need to add the `target/release`
folder of the nanoda checkout to `PATH`.

## Internals:
We generally adopt a policy of not loading olean files as they just get mmaped into our address
space and then dereferenced and are as such a potential point of attack for sophisticated adversaries.

The comparator performs the following steps to ensure these properties:
1. Build `Challenge` using `lake` in a `landrun` sandbox that has:
  - read access to the entire file system and write access to `/dev`
  - write access to the `.lake` directory of the project
2. Run `lean4export` on the produced `Challenge.olean` in a `landrun` sandbox that has:
  - read access to the entire file system and write access to `/dev`
3. Repeat the same build sandboxed and export sandboxed steps with `Solution`
4. Verify that all declarations used in the statement of all relevant theorems in `Challenge`
   are the same as in the `Solution` environment.
   This always includes the declarations from `Init` with special meaning to the kernel. Both `Challenge`
   and `Solution` therefore need to import the default prelude.
5. Verify that the body of all relevant theorems in the `Solution` environment only uses axioms
   listed in `permitted_axioms`
6. Replay the `Solution` environment into the Lean kernel. Doing this within the same process as the
   comparator should be safe as the worst thing that can happen at this point is an exploit that
   makes the kernel accept when it should reject and that same exploit should also be applicable
   from within an external process.

Note that as `Challenge` is trusted, both the sandbox and lean4export step for `Challenge` are not
necessary to the best of our knowledge. We still adopt these rather free measures as additional
paranoia in case an adversary comes up with a mean of attack anyway.
