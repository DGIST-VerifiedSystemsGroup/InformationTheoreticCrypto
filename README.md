# Information-Theoretic Cryptography in Lean

This repository formalizes the functional view of information-theoretic
distinguishing games from Section 3.1 of *Revisiting Multi-User Lifting
Theorems for Information-Theoretic Security*, and proves a native PRP/PRF
switching lemma on top of that semantics.

The main theorem bounds the advantage of every `q`-query distinguisher between
a uniformly random function and a uniformly random permutation on a finite,
nonempty type `X`:

```text
Advantage <= q * (q - 1) / (2 * |X|).
```

Both deterministic and randomized distinguishers are covered.

## Reading order

1. `InformationTheoreticCrypto/Section31.lean`
   formalizes systems, random systems, query functions, transcripts,
   distinguishers, acceptance probabilities, advantages, statistical distance,
   and tagged private/public query interfaces.
2. `InformationTheoreticCrypto/Section31NativeSwitching.lean`
   instantiates the Section 3.1 framework with random functions and random
   permutations and proves the switching lemma directly in that framework.

The native switching file imports only `Section31`. Its proof proceeds through:

- whole-oracle and lazy-sampling equivalence for random functions;
- completion of a partial injective table to a uniform permutation;
- whole-oracle and lazy-sampling equivalence for random permutations;
- a coupling of the two lazy executions;
- the collision bound; and
- deterministic and randomized Section 3.1 switching theorems.

The final theorem names are:

```lean
InformationTheoreticSecurity.Section31.NativeSwitching.deterministic_prp_prf_switching
InformationTheoreticSecurity.Section31.NativeSwitching.randomized_prp_prf_switching
```

## Archived development

`InformationTheoreticCrypto/Archive/` contains an earlier, independent
development of the switching lemma and a bridge from it to the Section 3.1
definitions. It is retained as proof history, but it is not imported by the
public library and is not needed to understand or verify the native proof.

## Modeling note

The paper gives a decision function the domain `T(Q)` of realizable
transcripts. For a simpler Lean interface, this formalization uses a total
function `Transcript X Y -> Bool`. These representations agree on every
transcript that can occur in the game; values outside `T(Q)` are unobservable.

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build

# Optional: also verify the archived development.
lake build InformationTheoreticCrypto.Archive.Section31Switching
```

The repository pins its Lean toolchain in `lean-toolchain` and its Mathlib
revision in `lakefile.toml` and `lake-manifest.json`.

## Scope

The tagged private/public interface from the end of Section 3.1 is formalized,
but the present PRP/PRF switching theorem uses a single oracle interface. The
repository does not yet formalize the paper's later multi-user lifting results.

## License

MIT
