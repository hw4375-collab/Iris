import LeanArabic.Pregroup
import LeanArabic.Pregroup.Reducer.Reducer
import LeanArabic.Pregroup.Reducer.Benchmark.Lexicon

namespace LeanArabic.Pregroup.Benchmark

open Reducer

inductive BasicDeriv : Atom → Atom → Type where
  | refl : BasicDeriv a a

  | π₁_to_π : BasicDeriv .π₁ .π
  | π₂_to_π : BasicDeriv .π₂ .π
  | π₃_to_π : BasicDeriv .π₃ .π
  | π₄_to_π : BasicDeriv .π₄ .π
  | π₅_to_π : BasicDeriv .π₅ .π
  | π₆_to_π : BasicDeriv .π₆ .π

  | s₁_to_s : BasicDeriv .s₁ .s
  | s₂_to_s : BasicDeriv .s₂ .s

  | q₁_to_q : BasicDeriv .q₁ .q
  | q₂_to_q : BasicDeriv .q₂ .q

  | n_to_π : BasicDeriv .n .π
  | n_to_o : BasicDeriv .n .o

  | nBar_to_π : BasicDeriv .nBar .π
  | nBar_to_o : BasicDeriv .nBar .o

  | i_to_j : BasicDeriv .i .j

  | q_to_qBar : BasicDeriv .q .qBar



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
    (x y : Atom) :
    Option (BasicDeriv x y) :=
  match x, y with

  | .π₁, .π => some BasicDeriv.π₁_to_π
  | .π₂, .π => some BasicDeriv.π₂_to_π
  | .π₃, .π => some BasicDeriv.π₃_to_π
  | .π₄, .π => some BasicDeriv.π₄_to_π
  | .π₅, .π => some BasicDeriv.π₅_to_π
  | .π₆, .π => some BasicDeriv.π₆_to_π

  | .s₁, .s => some BasicDeriv.s₁_to_s
  | .s₂, .s => some BasicDeriv.s₂_to_s

  | .q₁, .q => some BasicDeriv.q₁_to_q
  | .q₂, .q => some BasicDeriv.q₂_to_q

  | .n, .π => some BasicDeriv.n_to_π
  | .n, .o => some BasicDeriv.n_to_o

  | .nBar, .π => some BasicDeriv.nBar_to_π
  | .nBar, .o => some BasicDeriv.nBar_to_o

  | .i, .j => some BasicDeriv.i_to_j

  | .q, .qBar => some BasicDeriv.q_to_qBar

  | x, y =>
      if h : x = y then
        by
          subst y
          exact some BasicDeriv.refl
      else
        none

def hasBasicStep (x y : Atom) : Bool :=
  match lookupBasic x y with
  | some _ => true
  | none => false

#eval hasBasicStep .i .j
#eval hasBasicStep .i .i
#eval hasBasicStep .j .i


def canContractR
    (x y : SignedAtom Atom) : Bool :=
  match contractPairR? lookupBasic x y with
  | some _ => true
  | none => false


#eval canContractR (.left .j) (.plain .i)
#eval canContractR (.left .i) (.plain .j)

#check rightContractFromBase
  (BasicDeriv.refl : BasicDeriv .π₃ .π₃)


#eval canContractR (.plain .π₃) (.right .π₃)
#eval canContractR (.left .j) (.plain .i)
#eval canContractR (.plain .j) (.right .i)
#eval canContractR (.left .i) (.plain .j)


#eval hasBasicStep .π₃ .π₃

#print Reducer.contractPairR?


#eval hasBasicStep .π₃ .π
#eval hasBasicStep .s₁ .s
#eval hasBasicStep .q .qBar

#eval hasBasicStep .π .π₃
#eval hasBasicStep .s .s₁
#eval hasBasicStep .qBar .q

#eval hasBasicStep .π₆ .π
#eval hasBasicStep .s₂ .s
#eval hasBasicStep .q₂ .q
#eval hasBasicStep .n .π
#eval hasBasicStep .n .o
#eval hasBasicStep .nBar .π
#eval hasBasicStep .nBar .o
#eval hasBasicStep .i .j
#eval hasBasicStep .q .qBar

#eval hasBasicStep .π .π₆
#eval hasBasicStep .s .s₂
#eval hasBasicStep .o .n
#eval hasBasicStep .j .i
#eval hasBasicStep .qBar .q
