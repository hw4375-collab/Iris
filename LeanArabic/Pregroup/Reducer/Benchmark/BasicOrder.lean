import LeanArabic.Pregroup
import LeanArabic.Pregroup.Reducer.Benchmark.Lexicon

namespace LeanArabic.Pregroup.Benchmark

inductive BasicDeriv : Atom → Atom → Type where
  | refl : BasicDeriv a a
  | i_to_j : BasicDeriv .i .j


#check BasicDeriv.i_to_j
#check (BasicDeriv.refl : BasicDeriv .i .i)

#check DerivR.atomStep BasicDeriv.i_to_j





def jl_i_to_jl_j :
    DerivR BasicDeriv
      ((Ty.atom Atom.j)ˡ * Ty.atom Atom.i)
      ((Ty.atom Atom.j)ˡ * Ty.atom Atom.j) :=
  DerivR.mono
    (DerivR.refl ((Ty.atom Atom.j)ˡ))
    (DerivR.atomStep BasicDeriv.i_to_j)

#check jl_i_to_jl_j

def jl_i_contract :
    DerivR BasicDeriv
      ((Ty.atom Atom.j)ˡ * Ty.atom Atom.i)
      𝟙 :=
  DerivR.trans
    jl_i_to_jl_j
    DerivR.leftContract

#check jl_i_contract
#check leftContractFromBase BasicDeriv.i_to_j



def lookupBasic
    (a b : Atom) :
    Option (BasicDeriv a b) :=
  match a, b with
  | .i, .j =>
      some BasicDeriv.i_to_j

  | a, b =>
      if h : a = b then
        by
          subst b
          exact some BasicDeriv.refl
      else
        none

def hasBasicStep (a b : Atom) : Bool :=
  match lookupBasic a b with
  | some _ => true
  | none => false

#eval hasBasicStep .i .j
#eval hasBasicStep .i .i
#eval hasBasicStep .j .i
