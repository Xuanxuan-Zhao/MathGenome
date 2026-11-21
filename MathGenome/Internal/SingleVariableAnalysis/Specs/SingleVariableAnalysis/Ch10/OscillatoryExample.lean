import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! K03.10.oscillatory_example, paper.tex:3183–3203.
Convergence means a finite cofinal limit of proper Darboux truncations.
The recurring intervals and harmonic lower bound are explicit obligations. -/
namespace Specs.SingleVariableAnalysis.Ch10.OscillatoryExample
open OneEndpoint
open Specs.SingleVariableAnalysis.Ch08.Integral
open scoped BigOperators

noncomputable def sineOverXConverges : Prop :=
  rightConvergesValue .real (fun x => Real.sin x / x) 1 ⊤

noncomputable def recurringIntervals : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 2 ∧ ∀ k : ℕ, 1 ≤ k →
    let l := Real.pi / 2 + k * Real.pi - δ
    let u := Real.pi / 2 + k * Real.pi + δ
    1 ≤ l ∧ l < u ∧ u ≤ (k + 1 : ℝ) * Real.pi ∧
    (∀ x ∈ Set.Icc l u, (1 : ℝ) / 2 ≤ |Real.sin x|) ∧
    ∃ h : realIntegrableValue (fun x => |Real.sin x| / x) l u,
      δ / ((k + 1 : ℝ) * Real.pi) ≤ realIntegralValue _ h

noncomputable def harmonicLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
    ∃ h : realIntegrableValue (fun x => |Real.sin x| / x) 1
      ((N + 1 : ℝ) * Real.pi),
    c * ((∑ n ∈ Finset.range (N + 2), 1 / (n : ℝ)) - 1) ≤ realIntegralValue _ h

noncomputable def absoluteDiverges : Prop :=
  rightDivergesPosValue (fun x => |Real.sin x| / x) 1 ⊤

noncomputable def conditionalConvergence : Prop :=
  rightConvergesValue .real (fun x => Real.sin x / x) 1 ⊤ ∧
  ¬ rightConvergesValue .real (fun x : ℝ => (|Real.sin x / x| : ℝ)) 1 ⊤

end Specs.SingleVariableAnalysis.Ch10.OscillatoryExample
