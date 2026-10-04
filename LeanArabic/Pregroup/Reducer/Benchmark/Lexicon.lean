import LeanArabic.Pregroup.Reducer.Types

namespace LeanArabic.Pregroup.Benchmark

open Reducer


inductive Atom where
  | π
  | π₁
  | π₂
  | π₃
  | π₄
  | π₅
  | π₆

  | o

  | s
  | s₁
  | s₂

  | q
  | q₁
  | q₂
  | qBar

  | n
  | n₀
  | n₁
  | n₂
  | nBar

  | a
  | aBar

  | i
  | j

  deriving Repr, DecidableEq



def lookup : String → Option (FlatExpr Atom)

/-
Norn
-/
  | "She" =>
      some [
        .plain .π₃
      ]

/-
Verb
-/
  | "sleeps" =>
      some [
        .right .π₃,
        .plain .s₁
      ]

  | "sleep" =>
      some [
        .plain .i
      ]


  | "see" =>
      some [
        .plain .i,
        .left .o
      ]

  | "sees" =>
      some [
        .right .π₃,
        .plain .s₁,
        .left .o
      ]

  | "him" =>
      some [
        .plain .o
      ]


  | "may" =>
      some [
        .right .π₃,
        .plain .s₁,
        .left .j
      ]

  | "tomorrow" =>
      some [
        .right .i,
        .plain .i
      ]

  | "in" =>
      some [
        .right .i,
        .plain .i,
        .left .o
      ]

  | "the" =>
      some [
        .plain .nBar,
        .left .n₁
      ]

  | "university" =>
      some [
        .plain .n₁
      ]


  | "Mary" =>
      some [
        .plain .n
      ]

  | "John" =>
      some [
        .plain .n
      ]

  | "may(new)" =>
      some [
        .right .π,
        .plain .s₁,
        .left .j
      ]



  | _ =>
      none
