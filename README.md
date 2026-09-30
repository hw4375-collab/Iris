# LeanArabic

LeanArabic is a small 24-hour feasibility experiment for manually representing a
published fragment of Arabic Pregroup Grammar in Lean 4. It is based on Ahmad M.
Abd Al-Aziz (2018), *Parsing Arabic Verb Phrases Using Pregroup Grammars*.

The planned research path is:

```text
Published Arabic grammar
        ↓
Pregroup formalization
        ↓
Lean 4 proof objects
        ↓
machine-checkable grammatical derivations
```

The first planned manual experiments are:

1. **VSO** — `كَتَبَ أَحْمَدُ الدَّرْسَ` — “Ahmad wrote the lesson.”
2. **SVO** — `أَحْمَدُ كَتَبَ الدَّرْسَ` — “Ahmad wrote the lesson.”
3. **Future modifier** — `سَوْفَ يَكْتُبُ أَحْمَدُ رِسَالَةً` — “Ahmad will write a letter.”

This repository prepares only the Lean 4 environment. It does not yet formalize
Pregroup axioms, Lambek calculus, Arabic grammatical claims, or the examples above.
It is not intended to build a general Arabic parser. The feasibility question is what
additional guarantees become available when an existing Arabic linguistic formalism is
represented in a proof assistant.

## Current checkpoint

The initial environment has now grown into a certified Pregroup reducer baseline:

- generic `Ty` and proof-producing `Deriv` kernel;
- Arabic basic type experiments;
- `SignedAtom`, `FlatExpr`, `FlatExpr.toTy`, exact contractions, `reduceOnce`,
  `normalize`, and `checkTarget`;
- local contraction certificates, context lifting, and the soundness chain
  `reduceOnce_sound`, `normalizeAux_sound`, `normalize_sound`, and
  `checkTarget_sound`;
- local test/regression infrastructure.

The intended architecture is:

```text
Natural-language input          [not implemented]
        ↓
frozen lexical grammar/compiler [not implemented]
        ↓
FlatExpr → reduceOnce → normalize → checkTarget → Lean-checked Deriv certificate
```

Current limitations are deliberate: P0 supports only flat atomic types with first-order
adjoints and exact contractions; partial-order/subtyping relations, natural-language
compilation, a frozen lexicon, lexical ambiguity search, and Arabic gender/number/person
refinement are not implemented. The verifier establishes formal validity relative to the
chosen representation; it does not itself establish linguistic faithfulness.

## Build

This project uses Lean `v4.26.0` with no external dependencies.

```sh
lake build
```
