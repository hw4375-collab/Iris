import LeanArabic.Pregroup.Reducer.Benchmark.Compiler

namespace LeanArabic.Pregroup.Benchmark

#eval checkSentence "She sleeps" (.plain .s₁)

#eval checkSentence "sleeps She" (.plain .s₁)

#eval checkSentence "She sees him" (.plain .s₁)
