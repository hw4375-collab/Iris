# Research changelog

This changelog records research checkpoints, representation boundaries, and
verified capabilities. It is not a generic software release history.

## 2026-10-04 — Dataset 1 verifier and branching proof-search checkpoint

### What changed

- Continued the generic relation-aware Pregroup derivation layer.
- Added dataset-supplied basic morphism witnesses and relation-aware pair
  contraction.
- Added branching reduction and exhaustive finite proof search.
- Extended Dataset 1 benchmark infrastructure for controlled natural-language
  compilation, reduction, and target checking.

### What was demonstrated

- Exact-contraction cases work.
- Basic-order-assisted derivations work, including the dataset witness `i ≤ j`.
- A greedy reducer can produce false negatives.
- Exhaustive proof search can recover valid derivations.
- Controlled natural-language benchmark sentences can be compiled into
  `FlatExpr` values and checked.

### Important research observation

Formal derivability, proof-search strategy, and representation faithfulness
are distinct questions. Some published lexical assignments require further
investigation; no unsupported relation has been silently added merely to make
an example pass.

### Not yet proved

The branching-search layer does not yet have a whole-search soundness theorem
of the form:

```text
checkTargetSearchR = true
    → DerivR Base expr.toTy target.toTy
```

Local contractions are proof-producing, but the current search procedure
returns states and discards the full proof path.

### Next step

Dataset 2: Arabic agreement representation-faithfulness pilot.

## 2026-09-30 — Dataset-aware basic morphism interface

### Natural-language benchmark interface

- Continued the frozen benchmark lexicon with entries supporting `She`,
  `sleeps`, `sees`, `him`, `may`, and `sleep`.
- Natural-language compilation now supports controlled whitespace-separated
  sentence strings.
- `checkSentence` provides the current natural-language-to-verifier interface.
- Confirmed current results:
  - `She sleeps` → `some true`;
  - `sleeps She` → `some false`;
  - `She sees him` → `some true`.

### Dataset-supplied basic type relation

The benchmark-level grammar introduces the witness `i ≤ j` as the explicit
proof object `BasicDeriv.i_to_j : BasicDeriv Atom.i Atom.j`. This relation
belongs to benchmark/dataset grammar knowledge, not to the generic Pregroup
kernel.

### Generic relation-aware derivation experiment

The generic relation-aware derivation family `DerivR Base` was added, where
`Base : Atom → Atom → Type`. It allows the generic Pregroup proof system to
consume externally supplied basic morphisms without hard-coding benchmark
atoms. Its current constructors are:

- `atomStep`;
- `refl`;
- `mono`;
- `leftContract`;
- `trans`.

### Verified witness chain

The current implementation constructs `i → j`; by monotonicity it constructs
`jˡ * i → jˡ * j`; and by left contraction it constructs `jˡ * i → 𝟙`.
This is the formal witness required for the published benchmark sentence
`She may sleep`, whose relevant local type pattern is `jˡ * i` and whose
benchmark supplies `i ≤ j`.

### Generic helper

`leftContractFromBase` proves generically:

```text
Base b a
    ⇒
DerivR Base ((atom a)ˡ * atom b) 𝟙
```

This abstracts the concrete `jˡ * i` derivation.

### Dataset lookup interface

The benchmark-side lookup interface for basic morphisms currently provides:

- `i → j`: available;
- `i → i`: reflexive;
- `j → i`: unavailable.

The generic reducer is intended to consume this interface later.

### Important current boundary

The new basic-relation machinery is not yet connected to the automatic
reducer. In particular:

- the old `contractPair?` remains the exact-contraction P0 baseline;
- no `contractPairR?` has been implemented;
- `reduceOnce`, `normalize`, and `checkTarget` still use the existing
  exact-contraction derivation layer;
- `She may sleep` is not yet expected to return `some true` through the
  automatic sentence checker.

This checkpoint proves that the required dataset-supplied witness can be
represented and composed generically. Automatic reducer integration remains
the next step.
