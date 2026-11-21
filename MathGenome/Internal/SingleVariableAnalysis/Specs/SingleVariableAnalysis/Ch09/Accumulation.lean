import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent statements of K03.09.accumulation (paper.tex:2366–2379).
All values are the proper Darboux integral from chapter 08. Integrability
includes boundedness and ordered endpoints. The accumulation is a function
on the closed interval, including its endpoints; its restriction integrals
are supplied by the conclusion rather than assumed. Both scalar choices
are covered, without a continuity hypothesis on the integrand.
-/
namespace Specs.SingleVariableAnalysis.Ch09.Accumulation
open Specs.SingleVariableAnalysis.Ch08

/-- Every interval between two points of the original interval is integrable,
in either orientation. -/
def realRestrictions : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ} (_hf : Integral.realIntegrableValue f a b)
    (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b →
    Oriented.realIntegrableValue f x y

def complexRestrictions : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ} (_hf : Integral.complexIntegrableValue f a b)
    (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b →
    Oriented.complexIntegrableValue f x y

/-- The asserted bound has the actual supremum of the norm on [a,b].
The final conjunct explicitly records Lipschitz continuity and continuity.
Proofs of integrability carry no additional mathematical assumptions. -/
def realAccumulation : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ} (_hf : Integral.realIntegrableValue f a b),
    let M := sSup ((fun t => ‖f t‖) '' Set.Icc a b)
    ∃ H : ∀ x : Set.Icc a b, Integral.realIntegrableValue f a x,
      (∀ x y : Set.Icc a b,
        ‖Integral.realIntegralValue f (H y) - Integral.realIntegralValue f (H x)‖ ≤
          M * |(y : ℝ) - (x : ℝ)|) ∧
      ∃ hM : 0 ≤ M,
        LipschitzWith ⟨M, hM⟩ (fun x : Set.Icc a b => Integral.realIntegralValue f (H x)) ∧
        Continuous (fun x : Set.Icc a b => Integral.realIntegralValue f (H x))

def complexAccumulation : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ} (_hf : Integral.complexIntegrableValue f a b),
    let M := sSup ((fun t => ‖f t‖) '' Set.Icc a b)
    ∃ H : ∀ x : Set.Icc a b, Integral.complexIntegrableValue f a x,
      (∀ x y : Set.Icc a b,
        ‖Integral.complexIntegralValue f (H y) - Integral.complexIntegralValue f (H x)‖ ≤
          M * |(y : ℝ) - (x : ℝ)|) ∧
      ∃ hM : 0 ≤ M,
        LipschitzWith ⟨M, hM⟩ (fun x : Set.Icc a b => Integral.complexIntegralValue f (H x)) ∧
        Continuous (fun x : Set.Icc a b => Integral.complexIntegralValue f (H x))

end Specs.SingleVariableAnalysis.Ch09.Accumulation
