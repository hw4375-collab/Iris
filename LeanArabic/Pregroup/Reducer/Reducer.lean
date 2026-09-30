/-
P0 scaffold for an automatic, proof-producing Pregroup reducer.

-/
/-
Automatic proof-producing Pregroup reducer.

Architecture:

  FlatExpr
      │
      ▼
  reduceOnce
      │
      ▼
  normalize
      │
      ▼
  checkTarget

The computational reducer is separated from the trusted Pregroup
proof system `Deriv`.

Local contractions:

    X * Xʳ ⊢ 𝟙
    Xˡ * X ⊢ 𝟙

are certified by `contractPair?`.

Context-lifting lemmas then embed these local certificates into
larger expressions.

Final goal:

    reduceOnce expr = some next
        →
    Deriv expr.toTy next.toTy

and eventually:

    checkTarget expr target = true
        →
    Deriv expr.toTy target.toTy
-/



import LeanArabic.Pregroup.Reducer.Types

namespace LeanArabic.Pregroup.Reducer

/-
TODO (manual implementation; not part of P0 setup):

* `reduceOnce`: one explicit reduction step;
* `normalize`: repeated reduction to a normal form;
* proof-producing reduction certificates in the existing `Deriv` system;
* a soundness theorem connecting a computed reduction to `Deriv`.
-/






/-
Append any new type atom into list and keep the reduce checking
left associate:

extendTy(A, [x₁, ..., x\n]) = (((A * x₁) * x₂) ... * x\n)
i.e.
extendTy(A, [B, C, D]) = ((A * B) * C) * D
-/

def extendTy {Atom : Type}
    (base : Ty Atom)
    (xs : FlatExpr Atom) : Ty Atom :=
  List.foldl
    (fun (acc : Ty Atom) (z : SignedAtom Atom) =>
      acc * SignedAtom.toTy z)
    base
    xs







/-
XXʳ → 𝟙
XˡX → 𝟙
-/

def reduceOnce {Atom : Type} [DecidableEq Atom] :
    FlatExpr Atom → Option (FlatExpr Atom)

  | [] =>
      none

  | [_] =>
      none

  -- Exact right contraction:
  --
  --     X Xʳ → 𝟙
  --
  | .plain a :: .right b :: rest =>
      if a = b then
        some rest
      else
        match reduceOnce (.right b :: rest) with
        | some reducedTail =>
            some (.plain a :: reducedTail)
        | none =>
            none

  -- Exact left contraction:
  --
  --     Xˡ X → 𝟙
  --
  | .left a :: .plain b :: rest =>
      if a = b then
        some rest
      else
        match reduceOnce (.plain b :: rest) with
        | some reducedTail =>
            some (.left a :: reducedTail)
        | none =>
            none

  -- No contraction at the current position.
  -- Continue scanning from left to right.
  |
    x :: y :: rest =>
      match reduceOnce (y :: rest) with
      | some reducedTail =>
          some (x :: reducedTail)
      | none =>
          none




/-
E₁ → E₂ → E₃ → ...
until
reduceOnce(E\n) = none
-/

def normalizeAux {Atom : Type} [DecidableEq Atom] :
    Nat → FlatExpr Atom → FlatExpr Atom
  | 0, expr =>
      expr
  | n + 1, expr =>
      match reduceOnce expr with
      | none =>
          expr
      | some next =>
          normalizeAux n next


def normalize {Atom : Type} [DecidableEq Atom]
    (expr : FlatExpr Atom) : FlatExpr Atom :=
  normalizeAux expr.length expr






/-
checkTarget(E, t) = (normalize(E) = [t])
i.e.
[π₃, π₃ʳ, s₁, oˡ, o] → [s₁, oˡ, o] → [s₁]
-/


def checkTarget {Atom : Type} [DecidableEq Atom]
    (expr : FlatExpr Atom)
    (target : SignedAtom Atom) : Bool :=
  normalize expr == [target]





/-
Mathematical meaning:
Can I get a proof for :
    x * y ⊢ 𝟙
from the trusted Pregroup kernel?
-/

def contractPair? {Atom : Type} [DecidableEq Atom]
    (x y : SignedAtom Atom) :
    Option (Deriv (x.toTy * y.toTy) 𝟙) :=
  match x, y with

  | .plain a, .right b =>
      if h : a = b then
        by
          subst b
          exact some Deriv.rightContract
      else
        none

  | .left a, .plain b =>
      if h : a = b then
        by
          subst b
          exact some Deriv.leftContract
      else
        none

  | _, _ =>
      none




/-
Context lifting on the left.

Given a local contraction

    x * y ⊢ 𝟙

and an accumulated prefix type P, construct

    (P * x) * y ⊢ P.

Proof:

    (P * x) * y
        ⊢ P * (x * y)       associativity
        ⊢ P * 𝟙             monotonicity
        ⊢ P                 right unit
-/

def contractAfterPrefix {Atom : Type}
    (P : Ty Atom)
    {x y : SignedAtom Atom}
    (h : Deriv (SignedAtom.toTy x * SignedAtom.toTy y) 𝟙) :
    Deriv
      ((P * SignedAtom.toTy x) * SignedAtom.toTy y)
      P := by

  have hAssoc :
      ((P * SignedAtom.toTy x) * SignedAtom.toTy y)
        ⊢
      (P * (SignedAtom.toTy x * SignedAtom.toTy y)) := by
    exact Deriv.assocLR

  have hContract :
      (P * (SignedAtom.toTy x * SignedAtom.toTy y))
        ⊢
      (P * (𝟙 : Ty Atom)) := by
    exact Deriv.mono
      (Deriv.refl P)
      h

  exact Deriv.trans
    hAssoc
    (Deriv.trans
      hContract
      Deriv.rightUnitContract)




/-
A ⊢ B →
A * C ⊢ B * C →
(A * C) * D ⊢ (B * C) * D

that is,

A ⊢ B => extendTy(A, S) ⊢ extendTy(B, S)
-/



def liftThroughSuffix {Atom : Type} {A B : Ty Atom}
    (h : A ⊢ B) :
    (suffix : FlatExpr Atom) →
      Deriv
        (List.foldl
          (fun (acc : Ty Atom) (z : SignedAtom Atom) =>
            acc * SignedAtom.toTy z)
          A
          suffix)
        (List.foldl
          (fun (acc : Ty Atom) (z : SignedAtom Atom) =>
            acc * SignedAtom.toTy z)
          B
          suffix)
  | [] =>
      h

  | z :: zs =>
      liftThroughSuffix
        (Deriv.mono
          h
          (Deriv.refl (SignedAtom.toTy z)))
        zs







/-
For boundary situation prefiex = []
((𝟙 * A) * B) * C ⊢  (A * B) * C-
-/

def foldFromOneToTy {Atom : Type} :
    (xs : FlatExpr Atom) →
      Deriv
        (List.foldl
          (fun (acc : Ty Atom) (z : SignedAtom Atom) =>
            acc * SignedAtom.toTy z)
          (𝟙 : Ty Atom)
          xs)
        (FlatExpr.toTy xs)
  | [] =>
      Deriv.refl (𝟙 : Ty Atom)

  | z :: zs =>
      by
        have h :
            ((𝟙 : Ty Atom) * SignedAtom.toTy z)
              ⊢
            SignedAtom.toTy z := by
          exact Deriv.leftUnitContract

        exact liftThroughSuffix h zs





/-
（（（A* B） * x₁）* ... * x\n） ⊢ A * ((B * x₁) * ... * x\n)
-/

def reassocExtendLR {Atom : Type}
    (A B : Ty Atom) :
    (xs : FlatExpr Atom) →
      Deriv
        (extendTy (A * B) xs)
        (A * extendTy B xs)

  | [] =>
      Deriv.refl (A * B)

  | z :: zs =>
      by
        have hAssoc :
            extendTy
              ((A * B) * SignedAtom.toTy z)
              zs
              ⊢
            extendTy
              (A * (B * SignedAtom.toTy z))
              zs := by
          exact liftThroughSuffix Deriv.assocLR zs

        have hRest :
            extendTy
              (A * (B * SignedAtom.toTy z))
              zs
              ⊢
            A * extendTy
              (B * SignedAtom.toTy z)
              zs := by
          exact reassocExtendLR
            A
            (B * SignedAtom.toTy z)
            zs

        exact Deriv.trans hAssoc hRest




/-
A * ((B * x₁) * ... * x\n) ⊢ (((A * B) * x₁) * ... x\n)
-/



def reassocExtendRL {Atom : Type}
    (A B : Ty Atom) :
    (xs : FlatExpr Atom) →
      Deriv
        (A * extendTy B xs)
        (extendTy (A * B) xs)

  | [] =>
      Deriv.refl (A * B)

  | z :: zs =>
      by
        have hRest :
            A * extendTy
              (B * SignedAtom.toTy z)
              zs
              ⊢
            extendTy
              (A * (B * SignedAtom.toTy z))
              zs := by
          exact reassocExtendRL
            A
            (B * SignedAtom.toTy z)
            zs

        have hAssoc :
            extendTy
              (A * (B * SignedAtom.toTy z))
              zs
              ⊢
            extendTy
              ((A * B) * SignedAtom.toTy z)
              zs := by
          exact liftThroughSuffix Deriv.assocRL zs

        exact Deriv.trans hRest hAssoc





def consToProduct {Atom : Type}
    (x : SignedAtom Atom) :
    (xs : FlatExpr Atom) →
      Deriv
        (FlatExpr.toTy (x :: xs))
        (SignedAtom.toTy x * FlatExpr.toTy xs)

  | [] =>
      Deriv.rightUnitExpand

  | y :: ys =>
      reassocExtendLR
        (SignedAtom.toTy x)
        (SignedAtom.toTy y)
        ys

def productToCons {Atom : Type}
    (x : SignedAtom Atom) :
    (xs : FlatExpr Atom) →
      Deriv
        (SignedAtom.toTy x * FlatExpr.toTy xs)
        (FlatExpr.toTy (x :: xs))

  | [] =>
      Deriv.rightUnitContract

  | y :: ys =>
      reassocExtendRL
        (SignedAtom.toTy x)
        (SignedAtom.toTy y)
        ys

def prependDeriv {Atom : Type}
    (x : SignedAtom Atom)
    {xs ys : FlatExpr Atom}
    (h : Deriv
      (FlatExpr.toTy xs)
      (FlatExpr.toTy ys)) :
    Deriv
      (FlatExpr.toTy (x :: xs))
      (FlatExpr.toTy (x :: ys)) := by

  exact Deriv.trans
    (consToProduct x xs)
    (Deriv.trans
      (Deriv.mono
        (Deriv.refl (SignedAtom.toTy x))
        h)
      (productToCons x ys))






/-
CertifiedStep(E) = (E', E ⊢ E')
-/
structure CertifiedStep {Atom : Type} (before : FlatExpr Atom) where
  after : FlatExpr Atom
  proof : Deriv before.toTy after.toTy



def certifiedReduceOnce {Atom : Type} [DecidableEq Atom]
    (expr : FlatExpr Atom) :
    Option (CertifiedStep expr) :=
  match expr with

  | [] =>
      none

  | [_] =>
      none

  | [x, y] =>
      match contractPair? x y with
      | some h =>
          some {
            after := []
            proof := h
          }
      | none =>
            none

    | [a, x, y] =>
      match contractPair? x y with
      | some h =>
          by
            have hAssoc :
                ((a.toTy * x.toTy) * y.toTy)
                ⊢
                (a.toTy * (x.toTy * y.toTy)) := by
              exact Deriv.assocLR

            have hContract:
                (a.toTy * (x.toTy * y.toTy))
                ⊢
                (a.toTy * (𝟙: Ty Atom)) :=  by
              exact Deriv.mono
                (Deriv.refl a.toTy)
                h

            have hWhole :
                ((a.toTy * x.toTy) * y.toTy)
                ⊢
                a.toTy := by
              exact Deriv.trans
                hAssoc
                (Deriv.trans
                  hContract
                  Deriv.rightUnitContract)

            exact some {
                after := [a]
                proof := hWhole
            }


      | _ =>
        none

    | _ =>
      none




/-
Given any proof h : reduceOnce(E) = some(E')
I construct a specifc object:

  Derive(E.toTy, E'.toTy)
-/



noncomputable def reduceOnce_sound
    {Atom : Type}
    [DecidableEq Atom]
    {expr next : FlatExpr Atom}
    (h : reduceOnce expr = some next) :
    Deriv expr.toTy next.toTy := by

  induction expr generalizing next with

  -- ============================================================
  -- [] cannot reduce.
  -- ============================================================
  | nil =>
      simp [reduceOnce] at h


  -- ============================================================
  -- expr = x :: xs
  -- ============================================================
  | cons x xs ih =>

      cases xs with

      -- --------------------------------------------------------
      -- [x] cannot reduce.
      -- --------------------------------------------------------
      | nil =>
          simp [reduceOnce] at h


      -- --------------------------------------------------------
      -- expr = x :: y :: rest
      -- --------------------------------------------------------
      | cons y rest =>

          cases x with

          -- ====================================================
          -- x = plain a
          -- ====================================================
          | plain a =>

              cases y with

              -- ================================================
              -- plain a :: plain b :: rest
              --
              -- No local contraction is possible.
              -- Therefore reduceOnce must have reduced the tail.
              -- ================================================
              | plain b =>

                  cases hr :
                      reduceOnce
                        (SignedAtom.plain b :: rest) with

                  | none =>
                      simp [reduceOnce, hr] at h

                  | some reducedTail =>

                      have hnext :
                          SignedAtom.plain a :: reducedTail = next := by
                        simpa [reduceOnce, hr] using h

                      subst next

                      have hTail :
                          Deriv
                            (FlatExpr.toTy
                              (SignedAtom.plain b :: rest))
                            (FlatExpr.toTy reducedTail) :=
                        ih hr

                      exact
                        prependDeriv
                          (SignedAtom.plain a)
                          hTail


              -- ================================================
              -- plain a :: left b :: rest
              --
              -- No local contraction.
              -- ================================================
              | left b =>

                  cases hr :
                      reduceOnce
                        (SignedAtom.left b :: rest) with

                  | none =>
                      simp [reduceOnce, hr] at h

                  | some reducedTail =>

                      have hnext :
                          SignedAtom.plain a :: reducedTail = next := by
                        simpa [reduceOnce, hr] using h

                      subst next

                      have hTail :
                          Deriv
                            (FlatExpr.toTy
                              (SignedAtom.left b :: rest))
                            (FlatExpr.toTy reducedTail) :=
                        ih hr

                      exact
                        prependDeriv
                          (SignedAtom.plain a)
                          hTail


              -- ================================================
              -- plain a :: right b :: rest
              --
              -- Potential right contraction:
              --
              --     X Xʳ ⊢ 𝟙
              -- ================================================
              | right b =>

                  by_cases hab : a = b

                  -- --------------------------------------------
                  -- a = b:
                  --
                  -- contraction happens immediately:
                  --
                  --     a aʳ → 𝟙
                  -- --------------------------------------------
                  · subst b

                    have hnext :
                        rest = next := by
                      simpa [reduceOnce] using h

                    subst next

                    have hLocal :
                        Deriv
                          (SignedAtom.toTy
                              (SignedAtom.plain a) *
                           SignedAtom.toTy
                              (SignedAtom.right a))
                          (𝟙 : Ty Atom) :=
                      Deriv.rightContract

                    exact
                      Deriv.trans
                        (liftThroughSuffix hLocal rest)
                        (foldFromOneToTy rest)


                  -- --------------------------------------------
                  -- a ≠ b:
                  --
                  -- no contraction here;
                  -- recurse into right b :: rest.
                  -- --------------------------------------------
                  · cases hr :
                        reduceOnce
                          (SignedAtom.right b :: rest) with

                    | none =>
                        simp [reduceOnce, hab, hr] at h

                    | some reducedTail =>

                        have hnext :
                              SignedAtom.plain a ::
                                reducedTail  = next := by
                          simpa [reduceOnce, hab, hr] using h

                        subst next

                        have hTail :
                            Deriv
                              (FlatExpr.toTy
                                (SignedAtom.right b :: rest))
                              (FlatExpr.toTy reducedTail) :=
                          ih hr

                        exact
                          prependDeriv
                            (SignedAtom.plain a)
                            hTail



          -- ====================================================
          -- x = left a
          -- ====================================================
          | left a =>

              cases y with

              -- ================================================
              -- left a :: plain b :: rest
              --
              -- Potential left contraction:
              --
              --     Xˡ X ⊢ 𝟙
              -- ================================================
              | plain b =>

                  by_cases hab : a = b

                  -- --------------------------------------------
                  -- a = b:
                  --
                  --     aˡ a → 𝟙
                  -- --------------------------------------------
                  · subst b

                    have hnext :
                        rest = next := by
                      simpa [reduceOnce] using h

                    subst next

                    have hLocal :
                        Deriv
                          (SignedAtom.toTy
                              (SignedAtom.left a) *
                           SignedAtom.toTy
                              (SignedAtom.plain a))
                          (𝟙 : Ty Atom) :=
                      Deriv.leftContract

                    exact
                      Deriv.trans
                        (liftThroughSuffix hLocal rest)
                        (foldFromOneToTy rest)


                  -- --------------------------------------------
                  -- a ≠ b:
                  --
                  -- recurse into plain b :: rest.
                  -- --------------------------------------------
                  · cases hr :
                        reduceOnce
                          (SignedAtom.plain b :: rest) with

                    | none =>
                        simp [reduceOnce, hab, hr] at h

                    | some reducedTail =>

                        have hnext :
                              SignedAtom.left a ::
                                reducedTail  = next := by
                          simpa [reduceOnce, hab, hr] using h

                        subst next

                        have hTail :
                            Deriv
                              (FlatExpr.toTy
                                (SignedAtom.plain b :: rest))
                              (FlatExpr.toTy reducedTail) :=
                          ih hr

                        exact
                          prependDeriv
                            (SignedAtom.left a)
                            hTail


              -- ================================================
              -- left a :: left b :: rest
              --
              -- No local contraction.
              -- ================================================
              | left b =>

                  cases hr :
                      reduceOnce
                        (SignedAtom.left b :: rest) with

                  | none =>
                      simp [reduceOnce, hr] at h

                  | some reducedTail =>

                      have hnext :

                            SignedAtom.left a ::
                              reducedTail = next  := by
                        simpa [reduceOnce, hr] using h

                      subst next

                      have hTail :
                          Deriv
                            (FlatExpr.toTy
                              (SignedAtom.left b :: rest))
                            (FlatExpr.toTy reducedTail) :=
                        ih hr

                      exact
                        prependDeriv
                          (SignedAtom.left a)
                          hTail


              -- ================================================
              -- left a :: right b :: rest
              --
              -- No local contraction.
              -- ================================================
              | right b =>

                  cases hr :
                      reduceOnce
                        (SignedAtom.right b :: rest) with

                  | none =>
                      simp [reduceOnce, hr] at h

                  | some reducedTail =>

                      have hnext :

                            SignedAtom.left a ::
                              reducedTail = next := by
                        simpa [reduceOnce, hr] using h

                      subst next

                      have hTail :
                          Deriv
                            (FlatExpr.toTy
                              (SignedAtom.right b :: rest))
                            (FlatExpr.toTy reducedTail) :=
                        ih hr

                      exact
                        prependDeriv
                          (SignedAtom.left a)
                          hTail



          -- ====================================================
          -- x = right a
          -- ====================================================
          | right a =>

              cases y with

              -- ================================================
              -- right a :: plain b :: rest
              --
              -- No local contraction.
              -- ================================================
              | plain b =>

                  cases hr :
                      reduceOnce
                        (SignedAtom.plain b :: rest) with

                  | none =>
                      simp [reduceOnce, hr] at h

                  | some reducedTail =>

                      have hnext :

                            SignedAtom.right a ::
                              reducedTail = next := by
                        simpa [reduceOnce, hr] using h

                      subst next

                      have hTail :
                          Deriv
                            (FlatExpr.toTy
                              (SignedAtom.plain b :: rest))
                            (FlatExpr.toTy reducedTail) :=
                        ih hr

                      exact
                        prependDeriv
                          (SignedAtom.right a)
                          hTail


              -- ================================================
              -- right a :: left b :: rest
              --
              -- No local contraction.
              -- ================================================
              | left b =>

                  cases hr :
                      reduceOnce
                        (SignedAtom.left b :: rest) with

                  | none =>
                      simp [reduceOnce, hr] at h

                  | some reducedTail =>

                      have hnext :

                            SignedAtom.right a ::
                              reducedTail = next := by
                        simpa [reduceOnce, hr] using h

                      subst next

                      have hTail :
                          Deriv
                            (FlatExpr.toTy
                              (SignedAtom.left b :: rest))
                            (FlatExpr.toTy reducedTail) :=
                        ih hr

                      exact
                        prependDeriv
                          (SignedAtom.right a)
                          hTail


              -- ================================================
              -- right a :: right b :: rest
              --
              -- No local contraction.
              -- ================================================
              | right b =>

                  cases hr :
                      reduceOnce
                        (SignedAtom.right b :: rest) with

                  | none =>
                      simp [reduceOnce, hr] at h

                  | some reducedTail =>

                      have hnext :

                            SignedAtom.right a ::
                              reducedTail = next := by
                        simpa [reduceOnce, hr] using h

                      subst next

                      have hTail :
                          Deriv
                            (FlatExpr.toTy
                              (SignedAtom.right b :: rest))
                            (FlatExpr.toTy reducedTail) :=
                        ih hr

                      exact
                        prependDeriv
                          (SignedAtom.right a)
                          hTail


/-
So far:

    reduceOnce (E) = some (E') => Deriv (E.toTy, E'.toTy)

-/




noncomputable def normalizeAux_sound
    {Atom : Type}
    [DecidableEq Atom] :
    (fuel : Nat) →
    (expr : FlatExpr Atom) →
    Deriv expr.toTy (normalizeAux fuel expr).toTy

  | 0, expr =>
      Deriv.refl expr.toTy

  | fuel + 1, expr =>
      match h : reduceOnce expr with

      | none =>
          by
            simpa [normalizeAux, h] using
              (Deriv.refl expr.toTy)

      | some next =>
          by
            have hStep :
                Deriv expr.toTy next.toTy :=
              reduceOnce_sound h

            have hRest :
                Deriv next.toTy
                  (normalizeAux fuel next).toTy :=
              normalizeAux_sound fuel next

            have hWhole :
                Deriv expr.toTy
                  (normalizeAux fuel next).toTy :=
              Deriv.trans hStep hRest

            simpa [normalizeAux, h] using hWhole



noncomputable def normalize_sound
    {Atom : Type}
    [DecidableEq Atom]
    (expr : FlatExpr Atom) :
    Deriv expr.toTy (normalize expr).toTy := by
  simpa [normalize] using
    (normalizeAux_sound expr.length expr)






/-
From:
    checkTarget(expr, target) = true
obtain:
    normalize(expr) = [target]
and we have:
    expr ⊢ normalize(expr) ⊢ [target]
with :
    [target].toTy = target.toTy
we finally got:
  expr.toTy ⊢ target
-/


noncomputable def checkTarget_sound
    {Atom : Type}
    [DecidableEq Atom]
    {expr : FlatExpr Atom}
    {target : SignedAtom Atom}
    (h : checkTarget expr target = true) :
    Deriv expr.toTy target.toTy := by

  have hNorm :
      normalize expr = [target] := by
    simpa [checkTarget] using h

  have hDeriv :
      Deriv expr.toTy (normalize expr).toTy :=
    normalize_sound expr

  simpa [hNorm] using hDeriv


end LeanArabic.Pregroup.Reducer
