import LeanArabic.Pregroup.Reducer.Types

namespace LeanArabic.Pregroup.Benchmark

open Reducer


inductive Atom where
  | π₃
  | s₁
  | i
  | j
  | o
  deriving Repr, DecidableEq



def lookup : String → Option (FlatExpr Atom)
  | "She" =>
      some [
        .plain .π₃
      ]

  | "sleeps" =>
      some [
        .right .π₃,
        .plain .s₁
      ]

  | "sleep" =>
      some [
        .plain .i
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


  | _ =>
      none
