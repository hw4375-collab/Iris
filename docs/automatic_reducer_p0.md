# Automatic Pregroup Reducer — P0 Workspace

## Purpose

This workspace prepares a future automatic, proof-producing Pregroup reducer.
The research goal is to move from handwritten Pregroup proof terms to an
automatic reducer that produces explicit certificates in the existing Lean
`Deriv` kernel.

P0 is setup only. The core reduction algorithm will be designed and implemented
manually by the researcher; no reducer behavior is specified or implemented
here.

## Module boundary

```text
LeanArabic/Pregroup/Reducer/
├── Types.lean     # future flat-expression representation boundary
├── Reducer.lean   # future reduction and certificate boundary
└── Tests.lean     # future examples boundary
```

The P0 modules import only the generic Pregroup kernel. They deliberately do
not introduce a lexicon, Arabic data, Agreement experiment data, partial
orders, semantics, or higher-category machinery.

## Planned manual work

The following components remain intentionally unimplemented:

- `SignedAtom` and `FlatExpr`;
- `reduceOnce` and `normalize`;
- proof-producing reduction certificates using `Deriv`;
- a soundness theorem relating computed reduction to `Deriv`.

The future test phrase “She sees him” is recorded only as a placeholder. No
lexical types, reduction, or proof have been encoded for it.

## Kernel preservation

P0 does not change the semantics of the existing `Ty` or `Deriv` kernel. Any
future automated output must eventually be justified by an explicit derivation
certificate rather than by an unverified boolean success flag.
