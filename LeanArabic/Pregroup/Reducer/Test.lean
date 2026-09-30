/-
P0 placeholder for future reducer tests.

The first intended example is “She sees him”. No lexicon, type assignment,
reduction, or proof is encoded at this stage.
-/
import LeanArabic.Pregroup.Reducer.Types
import LeanArabic.Pregroup.Reducer.Reducer

namespace LeanArabic.Pregroup.Reducer

/-
TODO (manual implementation; not part of P0 setup):

* encode the future “She sees him” test only after the reducer design is fixed.
-/

inductive TestAtom where
  | π₃
  | s₁
  | o
  deriving Repr, DecidableEq

def testExpr :  FlatExpr TestAtom :=
  [
    .plain .π₃,
    .right .π₃,
    .plain .s₁,
    .left .o,
    .plain .o
  ]



#check testExpr
#check FlatExpr.toTy testExpr
#reduce FlatExpr.toTy testExpr

example :
    FlatExpr.toTy testExpr
      =
    ((((Ty.atom TestAtom.π₃) *
       (Ty.atom TestAtom.π₃)ʳ) *
       Ty.atom TestAtom.s₁) *
       (Ty.atom TestAtom.o)ˡ) *
       Ty.atom TestAtom.o := by
  rfl



-- test1 : [π₃, π₃ʳ, s₁]
def test1 : FlatExpr TestAtom :=
  [
    .plain .π₃,
    .right .π₃,
    .plain .s₁
  ]

-- [π₃, π₃ʳ, s₁] → [s₁]
#eval reduceOnce test1



-- test2 : [π₃, π₃ˡ, s₁]
def test2 : FlatExpr TestAtom :=
  [
    .plain .π₃,
    .left .π₃,
    .plain .s₁
  ]

-- [π₃, π₃ˡ, s₁] → none
#eval reduceOnce test2




-- test3 : [π₃ˡ, π₃, s₁]
def test3 : FlatExpr TestAtom :=
  [
    .left .π₃,
    .plain .π₃,
    .plain .s₁
  ]

-- [π₃ˡ, π₃, s₁] → [s₁]
#eval reduceOnce test3




-- test4 : [s₁, oˡ, o]
def test4 : FlatExpr TestAtom :=
  [
    .plain .s₁,
    .left .o,
    .plain .o
  ]

--[s₁, oˡ, o] → [s₁]
#eval reduceOnce test4






#eval normalize testExpr


def testExpr_1 : FlatExpr TestAtom :=
  [
    .plain .s₁,
    .left .π₃,
    .plain .o,
    .right .o,
    .plain .π₃
  ]

#eval normalize testExpr_1


#eval checkTarget testExpr_1 (.plain .s₁)










example :
    (contractPair?
      (SignedAtom.plain TestAtom.π₃)
      (SignedAtom.right TestAtom.π₃)).isSome = true := by
    rfl


example :
    (contractPair?
      (SignedAtom.left TestAtom.o)
      (SignedAtom.plain TestAtom.o)).isSome = true := by
  rfl



example :
    (contractPair?
      (SignedAtom.plain TestAtom.π₃)
      (SignedAtom.right TestAtom.o)).isSome = false := by
  rfl

example :
    (contractPair?
      (SignedAtom.right TestAtom.π₃)
      (SignedAtom.plain TestAtom.π₃)).isSome = false := by
  rfl


  
end LeanArabic.Pregroup.Reducer
