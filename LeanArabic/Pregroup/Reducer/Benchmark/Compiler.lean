import LeanArabic.Pregroup.Reducer.Benchmark.Lexicon
import LeanArabic.Pregroup.Reducer.Reducer
import LeanArabic.Pregroup.Reducer.Benchmark.BasicOrder
 namespace LeanArabic.Pregroup.Benchmark

 open Reducer

 def compileWords : List String → Option (FlatExpr Atom)

  | [] =>
      some []

  | word :: rest =>
      match lookup word, compileWords rest with
      | some wordTy, some restTy =>
          some (wordTy ++ restTy)
      | _, _ =>
          none


def tokenize (sentence : String) : List String :=
  sentence.splitOn " "

def compileSentence (sentence : String) :
    Option (FlatExpr Atom) :=
  compileWords (tokenize sentence)


#eval compileWords ["She", "sleeps"]

#eval tokenize "She sleeps"

#eval compileSentence "She sleeps"




def checkSentence
    (sentence : String)
    (target : SignedAtom Atom) :
    Option Bool :=
  match compileSentence sentence with
  | some expr =>
      some (checkTarget expr target)
  | none =>
      none

def checkSentenceR
    (sentence : String)
    (target : SignedAtom Atom) :
    Option Bool :=
  match compileSentence sentence with
  | some expr =>
      some (checkTargetR lookupBasic expr target)
  | none =>
      none


#eval checkSentence "She sleeps" (.plain .s₁)

#eval checkSentence "sleeps She" (.plain .s₁)



#eval checkSentenceR "She may sleep" (.plain .s₁)


#eval checkSentenceR "She may sleep" (.plain .s₁)
