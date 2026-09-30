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

  | _ =>
      none
