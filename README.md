# Comparator
Comparator is a trustworthy judge for Lean proofs. It relies on having an existing Lean installation as
well as:
1. [`landrun`](https://github.com/Zouuup/landrun), compiled from the `main` branch's source, present in `PATH`
2. [`lean4export`](https://github.com/leanprover/lean4export/), at a version that is compatible with whatever Lean version your project is targeting, present in `PATH`
3. On Linux, util-linux versions of `setpriv` and `unshare` present in `PATH`
4. (optional) [nanoda](https://github.com/ammkrn/nanoda_lib/), compiled with a recent version of Rust.
   This is only necessary if you want to check with the nanoda kernel in addition to the builtin one.
   `cargo build --release` will place `nanoda_bin` in the `target/release` directory of the checked-out directory,
   this directory must be present in `PATH`

> [!NOTE]
> Alternatively full paths to these binaries can be specified using the environment variables
> `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_NANODA`, `COMPARATOR_SETPRIV`, and
> `COMPARATOR_UNSHARE` when invoking Comparator.

Comparator is configured through a JSON file:
```
{
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["todo1"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```
Where `Challenge.lean` contains at least a theorem named `todo1` that has a `sorry` (or any other proof)
and `Solution.lean` is provided by a party trying to convince you that they have proven `todo1` by
writing out the same theorem but with a proper proof attached.

Given the following assumptions:
1. The transitive closure of imports of `Challenge.lean` as well as `lakefile.toml`/`lakefile.lean`
   are controlled by you or trustworthy.
2. You have not previously tried to compile the `Solution` file or any other potentially adversarial
   files (as that might compromise your `Challenge` file to make it seem like you are looking for a
   different proof than you actually are)
3. You have the `landrun` and `lean4export` binary in `PATH`
4. `landrun` works correctly on your system and `Solution.lean` does not
   exploit any bugs in `landrun` that allow a process to escape its sandbox
5. The Lean kernel is correct (with `external_kernels` this can be reduced to
   "At least one of the Lean kernel or the `external_kernels` is correct")
6. You are not running this under a privileged user
7. The host permits unprivileged user, PID, and mount namespaces, unless Comparator reports that it
   is falling back without descendant containment

If the following command succeeds:
```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory $(pwd) -- bash -c 'lake env path/to/comparator/binary path/to/config.json'
```

All theorems in `Solution` that are listed in `theorem_names` are guaranteed to:
1. Prove the same statement as provided in `Challenge`
2. Use no more axioms than listed in `permitted_axioms`
3. Be accepted by the Lean kernel

> [!NOTE]
> The Trusted Code Base of Landrun naturally includes the operating system and hardware it is running on, plus its sandboxing mechanism.
> The systemd-run part explicitly guard against a vulnerability in landrun, Comparator's current sandboxing solution, that will be fixed in Linux 7.1

Note that running `lake exe cache get` to download a Mathlib cache is acceptable before running the
comparator if you trust the cache to not be modified as to, e.g. contain different definitions from
the one you would expect.

Furthermore, it is possible to avoid trusting `landrun`'s ability to sandbox the `Solution.lean` file:
if you have obtained a fully pre-built `.lake` directory through other means and without compromising your
checking environment, `Solution.lean` will not be rebuilt.

## Checking with Additional Kernels
Comparator can additionally check solutions with external kernels. To do this you must register them
in the `external_kernels` list:
```
{
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["todo1"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "external_kernels": {
        "mykernel": ["kernel_bin", "--threads=4", "--paranoid"]
    }
}
```
Comparator will execute the command described by the `mykernel` array and additionally pass a
file, containing the solution export to the kernel, in this case: `kernel_bin --threads=4 --paranoid export.ndjson`

For backwards compatibility reasons users may instead set `enable_nanoda: true` to obtain a config
that calls `nanoda_bin`. Furthermore, comparator currently attempts to detect `nanoda`-style kernels
by checking whether the name contains the string `noda` and instead passing a `nanoda`-style
`config.json` to them. This is only intended as a migration path while the kernel ecosystem
moves toward having an option to receive the input file as a `CLI` argument.

For development purposes, comparator supports overriding `nanoda` specifically using the
`COMPARATOR_NANODA` environment variable.

## Refusing to Run Without Sandboxing and Descendant Containment

Comparator invokes Landrun with `--best-effort` so that the installed Landrun can use the best
Landlock ABI available on the running kernel. This also means Landrun may run without applying a
policy when Landlock is unavailable. That remains the backwards-compatible default.

Set `"fail_closed": true` in the configuration when silently running without filesystem sandboxing
or descendant containment is unacceptable. Before starting any workload command, Comparator runs a
namespace preflight and then runs its own executable
through Landrun and verifies that the normal Comparator policy denies a write to a file which is
writable outside the sandbox. If Landlock is unavailable or disabled, Landrun is missing, or a no-op
Landrun shim is configured, Comparator exits with an error ending in:

```
fail_closed is enabled, so no workload command was started
```

This is an end-to-end check for basic filesystem enforcement, not a check for a particular Landlock
ABI or every access right. Landrun and the kernel remain trusted to enforce the requested policy.

When the namespace preflight succeeds, every workload Landrun command is supervised by `setpriv` and
`unshare` in a fresh user, PID, and mount namespace with a private `/proc`. Remaining descendants are
killed when the command or Comparator dies. If the preflight fails and `fail_closed` is `false`,
Comparator warns once and runs Landrun without descendant containment. It never retries a workload
command.

The error includes the failing command's diagnostic and relevant sysctl suggestions. For example,
current disposable Ubuntu CI runners may require:

```sh
sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
```

Depending on the reported setting, a dedicated runner may instead require
`sudo sysctl -w user.max_user_namespaces=15000` or
`sudo sysctl -w kernel.unprivileged_userns_clone=1`. These settings affect the host: do not apply
them blindly on a shared machine. Ask its administrator or use a compatible runner. A container
which forbids mounting a private `/proc` cannot provide strict descendant containment.

The default is `false`, preserving compatibility with an explicit warning when containment is
unavailable.

## Definition Holes
Sometimes challenges want to leave open definitions for solutions to fill in. This can range from
simple things like filling in a `Prop` valued definition to resolve whether a conjecture is true or
false, all the way to constructing complex mathematical objects. For these types of solutions,
comparator can guarantee that:
1. They use no more axioms than listed in `permitted_axioms`
2. They are accepted by the Lean kernel
3. The name, type, universe levels and safety levels of all definition holes match

Crucially, many definition hole challenges can be gamed without additional oversight.
For example, given a conjecture-style challenge:
```lean
def ChallengeSolution : Prop := sorry
theorem challenge : RiemannHypothesis ↔ ChallengeSolution := sorry
```
a solution could define `ChallengeSolution` as:
```lean
def ChallengeSolution : Prop := RiemannHypothesis
```
and conduct a simple proof of `challenge` by reflexivity. The intention of the challenge though was
of course to ask for a `True` or `False` value for `ChallengeSolution`. For this reason, all
definition hole solutions **must** always be checked with an additional (potentially human)
verifier.

To establish a definition hole, the challenge must provide it as a sorried definition:
```lean
def large : Nat := sorry

theorem large_lt : 37 < large := sorry
```
All of the holes must then be put into the `definition_names` field in `configuration.json`:
```
{
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["large_lt"],
    "definition_names": ["large"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```
For all `definition_names`, comparator ensures that in the solution:
- the name, type, universe levels and safety level match
- the constant does not (transitively) refer to non-permitted axioms
- the constant type checks

Thus, the following solution would be accepted:
```lean
def large : Nat := 38

theorem large_lt : 37 < large := by decide
```

## Development

The `scripts/fake-landrun.sh` can be used to replace Landrun in development if you are not on a Linux system that supports landrun.

The following commands, starting from the root directory of a fresh git checkout, will build and run `comparator` on one of the test examples:

```sh
lake build lean4export comparator

cd tests/projects/simple_mismatch

cat > lakefile.toml <<EOF
name = "comparatortest"
version = "0.1.0"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "Challenge"
EOF

COMPARATOR_LANDRUN=$(realpath ../../../scripts/fake-landrun.sh) COMPARATOR_LEAN4EXPORT=$(realpath ../../../.lake/packages/lean4export/.lake/build/bin/lean4export) lake env ../../../.lake/build/bin/comparator config.json
```

The following commands, starting from the root directory of a fresh git checkout, will build and run the tests:

```sh
lake build lean4export comparator
COMPARATOR_LANDRUN=$(realpath scripts/fake-landrun.sh) COMPARATOR_LEAN4EXPORT=$(realpath .lake/packages/lean4export/.lake/build/bin/lean4export) lean --run runtests.lean
```

Replace the `landrun` and `lean4export` arguments as needed, or place the binaries in `PATH`.

## Internals
We generally adopt a policy of not loading olean files as they just get mmaped into our address
space and then dereferenced and are as such a potential point of attack for sophisticated adversaries.

The comparator performs the following steps to ensure these properties:
1. Preflight user, PID, and mount namespaces. When available, supervise every sandboxed command in a
   fresh PID namespace so its remaining descendants are killed before Comparator continues.
2. Build `Challenge` using `lake` in a `landrun` sandbox that has:
   - read access to the entire file system and write access to `/dev`
   - write access to the `.lake` directory of the project
3. Run `lean4export` on the produced `Challenge.olean` in a `landrun` sandbox that has:
   - read access to the entire file system and write access to `/dev`
4. Repeat the same build sandboxed and export sandboxed steps with `Solution`
5. Verify that all declarations used in the statement of all relevant theorems in `Challenge`
   are the same as in the `Solution` environment.
   This always includes the declarations from `Init` with special meaning to the kernel. Both `Challenge`
   and `Solution` therefore need to import the default prelude.
6. Verify that the body of all relevant theorems in the `Solution` environment only uses axioms
   listed in `permitted_axioms`
7. Replay the `Solution` environment into the Lean kernel. Doing this within the same process as the
   comparator should be safe as the worst thing that can happen at this point is an exploit that
   makes the kernel accept when it should reject and that same exploit should also be applicable
   from within an external process.

Note that as `Challenge` is trusted, both the sandbox and lean4export step for `Challenge` are not
necessary to the best of our knowledge. We still adopt these rather free measures as additional
paranoia in case an adversary comes up with a means of attack anyway.

## Acknowledgement
Comparator was originally developed by Lean FRO, with feedback from the AIMO team, in support of the
AIMO series of competitions and their goal of enabling trustworthy LLM Lean evaluation on Kaggle.
