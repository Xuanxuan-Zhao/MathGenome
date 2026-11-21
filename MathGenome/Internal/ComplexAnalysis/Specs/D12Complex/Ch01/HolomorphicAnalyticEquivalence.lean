import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
Independent statements for paper.tex:247–266 (d12:01-04-equivalence),
using the three distinct canonical predicates from the Basic interface.
Openness is part of each predicate; no connectedness or nonemptiness is
required. The smoothness and derivative statements apply to each notion.
`HasDerivAt` explicitly asserts existence of the next derivative, as well
as identifying it with the total function `iteratedDeriv (n + 1) f`.
-/

open scoped ContDiff

namespace Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence

open _root_.D12Complex

def powerSeriesAnalyticAt_differentiableAt_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), PowerSeriesAnalyticAt f a → DifferentiableAt ℂ f a

def holomorphicOn_iff_c1HolomorphicOn_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f ↔ C1HolomorphicOn Ω f

def holomorphicOn_iff_powerSeriesAnalyticOn_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f ↔ PowerSeriesAnalyticOn Ω f

def c1HolomorphicOn_iff_powerSeriesAnalyticOn_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), C1HolomorphicOn Ω f ↔ PowerSeriesAnalyticOn Ω f

def three_notions_real_smooth_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    (HolomorphicOn Ω f ∨ C1HolomorphicOn Ω f ∨ PowerSeriesAnalyticOn Ω f) →
    ContDiffOn ℝ ∞ f Ω

def three_notions_iteratedDeriv_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    (HolomorphicOn Ω f ∨ C1HolomorphicOn Ω f ∨ PowerSeriesAnalyticOn Ω f) →
    ∀ n : ℕ, HolomorphicOn Ω (iteratedDeriv n f) ∧
      ∀ z ∈ Ω, HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f z) z

end Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence
