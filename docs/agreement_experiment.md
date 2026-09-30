# MSA agreement-attraction pilot

This is a controlled Modern Standard Arabic (MSA) agreement-attraction feasibility pilot.
The first pilot consists of the four conditions from one published Experiment 1 stimulus:

| Local condition | Published Table 2 condition | NP2 | Main verb | Gold label |
|---|---|---|---|---|
| `matchGram` | Match/Gram | `المدير` | `يتكلم` | grammatical |
| `matchUngram` | Match/Ungram | `المدير` | `تتكلم` | ungrammatical |
| `mismatchGram` | NoMatch/Gram | `المديرة` | `يتكلم` | grammatical |
| `mismatchUngram` | NoMatch/Ungram | `المديرة` | `تتكلم` | ungrammatical |

The common token structure is:

```text
NP1 + complementizer + relative-clause verb + NP2 + adverb + main verb + continuation
```

The source is Tucker et al., *Attraction Effects for Verbal Gender and Number Are Similar
but Not Identical: Self-Paced Reading Evidence From Modern Standard Arabic*, Experiment 1,
Table 2. The published table names the mismatch conditions `NoMatch`; the local data API uses
`mismatch` to match the present experiment's terminology. `Dataset.lean` and
`data/pilot_e1_item01.jsonl` are parallel, human-readable transcriptions of that single table.

## Representation boundary

```text
Published linguistic data
        ↓
LeanArabic.Agreement.Dataset
        ↓
our mathematical encoding
        ↓
LeanArabic.Agreement.Coarse
        ↓
Pregroup derivability / later Lean certificates
```

`Dataset.lean` records experimental metadata, including the published gold label. `Coarse.lean`
does not use that label to construct or reject a derivation. Any later formal verdict must arise
from the manually selected formal representation and the existing Pregroup derivation system.

R0 is intentionally a frozen coarse baseline. The immediate goal is to test whether this coarse
Pregroup encoding collapses distinctions that matter to the linguistic gold labels. R1
(feature/dependency-aware) and R2 (higher-dimensional/coherence) are future representations and
are deliberately **not** implemented here.

**Lean derivability does not by itself establish linguistic or semantic faithfulness.**

## Out of scope for this workbench stage

- No gender-aware grammar rule or feature system is implemented.
- No type is assumed for `الذي`, the relative-clause construction, the adverb, or the continuation.
- No Arabic grammatical claim is encoded as an axiom.
- No four-condition result is proven, and no gold label is used to force an expected result.
