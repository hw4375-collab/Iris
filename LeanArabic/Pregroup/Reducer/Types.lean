/-
P0 scaffold for the future automatic Pregroup reducer.

This module intentionally declares no reduction data types yet. In particular,
`SignedAtom` and `FlatExpr` remain design placeholders pending manual decisions
about a faithful flat representation of the existing `Ty` syntax.
-/
import LeanArabic.Pregroup

namespace LeanArabic.Pregroup.Reducer

/-
TODO (manual implementation; not part of P0 setup):

* define `SignedAtom`;
* define `FlatExpr`;
* specify their relation to the existing `Ty` kernel.
-/



/-
plain(a) ↔ a
left(a) ↔ aˡ
right(a) ↔ aʳ
-/

inductive SignedAtom (Atom : Type) where
  | plain  : Atom → SignedAtom Atom
  | left : Atom → SignedAtom Atom
  | right : Atom → SignedAtom Atom
  deriving Repr, DecidableEq


-- [π₃, π₃ʳ, s₁, oˡ, o]

abbrev FlatExpr (Atom : Type) :=
  List (SignedAtom Atom)



/-
plain(a) ↦ atom(a)
left(a) ↦ atom(a)ˡ
right(a) ↦ atom(a)ʳ
-/

def SignedAtom.toTy {Atom : Type} :
    SignedAtom Atom → Ty Atom
  | .plain a => Ty.atom a
  | .left a => (Ty.atom a)ˡ
  | .right a => (Ty.atom a)ʳ





/-
toTy([]) = 𝟙
toTy([x]) = x
toTy([x₁, ..., x\n ]) = (...((x₁ * x₂) * x₃)...) * x\n
-/


def FlatExpr.toTy {Atom : Type} :
    FlatExpr Atom → Ty Atom
  | [] => 𝟙
  | x :: xs =>
      List.foldl
        (fun (acc : Ty Atom) (y : SignedAtom Atom) =>
          acc * SignedAtom.toTy y)
        (SignedAtom.toTy x)
        xs



end LeanArabic.Pregroup.Reducer
