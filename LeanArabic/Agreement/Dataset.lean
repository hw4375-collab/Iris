/-
Experimental data for the Modern Standard Arabic agreement-attraction pilot.

This module records published stimulus metadata only. It does not assign Pregroup types,
encode grammatical constraints, or make the gold label available to the proof system.
-/
namespace LeanArabic.Agreement.Dataset

/-- Gender values recorded in the published stimulus metadata. -/
inductive Gender where
  | masculine
  | feminine
  deriving Repr, DecidableEq

/-- Published grammaticality labels for an experimental stimulus. -/
inductive GoldLabel where
  | grammatical
  | ungrammatical
  deriving Repr, DecidableEq

/-- The four conditions used for the first controlled agreement-attraction item. -/
inductive Condition where
  | matchGram
  | matchUngram
  | mismatchGram
  | mismatchUngram
  deriving Repr, DecidableEq

/--
One condition from a published Modern Standard Arabic agreement-attraction stimulus.

The word-level fields reproduce the experiment's region structure: NP1, complementizer,
relative-clause verb, NP2, adverb, main verb, and continuation.
-/
structure StimulusCondition where
  itemId : String
  condition : Condition
  np1 : String
  complementizer : String
  relativeClauseVerb : String
  np2 : String
  adverb : String
  mainVerb : String
  continuation : String
  np1Gender : Gender
  np2Gender : Gender
  mainVerbGender : Gender
  goldLabel : GoldLabel
  deriving Repr, DecidableEq

/-- Experiment 1, Table 2: Match / grammatical. -/
def item01MatchGram : StimulusCondition :=
  { itemId := "E1-item01"
    condition := .matchGram
    np1 := "المترجم"
    complementizer := "الذي"
    relativeClauseVerb := "ساعد"
    np2 := "المدير"
    adverb := "أحياناً"
    mainVerb := "يتكلم"
    continuation := "خمس لغات بفصاحة"
    np1Gender := .masculine
    np2Gender := .masculine
    mainVerbGender := .masculine
    goldLabel := .grammatical }

/-- Experiment 1, Table 2: Match / ungrammatical. -/
def item01MatchUngram : StimulusCondition :=
  { itemId := "E1-item01"
    condition := .matchUngram
    np1 := "المترجم"
    complementizer := "الذي"
    relativeClauseVerb := "ساعد"
    np2 := "المدير"
    adverb := "أحياناً"
    mainVerb := "تتكلم"
    continuation := "خمس لغات بفصاحة"
    np1Gender := .masculine
    np2Gender := .masculine
    mainVerbGender := .feminine
    goldLabel := .ungrammatical }

/-- Experiment 1, Table 2: Mismatch / grammatical (published as NoMatch / Gram). -/
def item01MismatchGram : StimulusCondition :=
  { itemId := "E1-item01"
    condition := .mismatchGram
    np1 := "المترجم"
    complementizer := "الذي"
    relativeClauseVerb := "ساعد"
    np2 := "المديرة"
    adverb := "أحياناً"
    mainVerb := "يتكلم"
    continuation := "خمس لغات بفصاحة"
    np1Gender := .masculine
    np2Gender := .feminine
    mainVerbGender := .masculine
    goldLabel := .grammatical }

/-- Experiment 1, Table 2: Mismatch / ungrammatical (published as NoMatch / Ungram). -/
def item01MismatchUngram : StimulusCondition :=
  { itemId := "E1-item01"
    condition := .mismatchUngram
    np1 := "المترجم"
    complementizer := "الذي"
    relativeClauseVerb := "ساعد"
    np2 := "المديرة"
    adverb := "أحياناً"
    mainVerb := "تتكلم"
    continuation := "خمس لغات بفصاحة"
    np1Gender := .masculine
    np2Gender := .feminine
    mainVerbGender := .feminine
    goldLabel := .ungrammatical }

/-- The frozen four-condition data set for the first pilot item. -/
def item01Conditions : List StimulusCondition :=
  [item01MatchGram, item01MatchUngram, item01MismatchGram, item01MismatchUngram]

end LeanArabic.Agreement.Dataset
