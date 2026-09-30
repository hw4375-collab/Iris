/-
R0: coarse Pregroup workbench for the MSA agreement-attraction pilot.

This module deliberately contains no gender-sensitive atoms, rules, or certificates. Its
purpose is to provide a stable boundary between the published data and a later, manually
chosen coarse encoding in the existing Pregroup kernel.
-/
import LeanArabic.Pregroup
import LeanArabic.ArabicTypes
import LeanArabic.Agreement.Dataset

namespace LeanArabic.Agreement.Coarse

open LeanArabic.Pregroup
open LeanArabic.ArabicTypes
open LeanArabic.Agreement.Dataset

/-
TODO (manual linguistic decisions required before any R0 encoding):
* a lexical type for the relative element `الذي`;
* the compositional type of the relative-clause construction;
* lexical treatment of the relative-clause verb and NP2;
* lexical treatment of the adverb `أحياناً`;
* lexical treatment of the continuation `خمس لغات بفصاحة`;
* the target sentence type and word-association convention for the full construction.

The published `goldLabel` is intentionally not consulted here. Future derivability questions
must be posed only over the manually selected formal representation.
-/

end LeanArabic.Agreement.Coarse
