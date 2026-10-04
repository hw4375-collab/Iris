import LeanArabic.Pregroup.Reducer.Benchmark.Compiler
import LeanArabic.Pregroup.Reducer.Benchmark.BasicOrder

namespace LeanArabic.Pregroup.Benchmark

open Reducer

#eval checkSentenceR "She sleeps" (.plain .s₁)

#eval checkSentenceR "sleeps She" (.plain .s₁)

#eval checkSentenceR "She may sleep" (.plain .s₁)

#eval checkSentenceR "She sees him" (.plain .s₁)

#eval checkSentenceR "She may see him" (.plain .s₁)

#eval checkSentenceR "She may see him tomorrow" (.plain .s₁)



def maySleepExpr : FlatExpr Atom :=
  [
    .plain .π₃,
    .right .π₃,
    .plain .s₁,
    .left .j,
    .plain .i
  ]

#eval reduceOnceR lookupBasic maySleepExpr


def maySleepAfterFirst : FlatExpr Atom :=
  [
    .plain .s₁,
    .left .j,
    .plain .i
  ]

#eval reduceOnceR lookupBasic maySleepAfterFirst



#eval normalizeR lookupBasic maySleepExpr



def branchingExpr : FlatExpr Atom :=
  [
    .left .j,
    .plain .i,
    .right .i,
    .plain .i
  ]

#eval reduceAllR lookupBasic branchingExpr

def tomorrowCore : FlatExpr Atom :=
  [
    .plain .s₁,
    .left .j,
    .plain .i,
    .right .i,
    .plain .i
  ]

#eval checkTargetSearchR
  lookupBasic
  tomorrowCore
  (.plain .s₁)

def checkSentenceSearchR
    (sentence : String)
    (target : SignedAtom Atom) :
    Option Bool :=
  match compileSentence sentence with
  | some expr =>
      some (checkTargetSearchR lookupBasic expr target)
  | none =>
      none

#eval checkSentenceSearchR
  "She may see him tomorrow"
  (.plain .s₁)

#eval checkSentenceSearchR
  "She may sleep"
  (.plain .s₁)

#eval checkSentenceSearchR
  "She sees him"
  (.plain .s₁)

#eval checkSentenceSearchR
  "She may see him in the university"
  (.plain .s₁)


#eval checkSentenceSearchR
  "Mary may see John"
  (.plain .s₁)


#eval checkSentenceSearchR
  "Mary may(new) see John"
  (.plain .s₁)
