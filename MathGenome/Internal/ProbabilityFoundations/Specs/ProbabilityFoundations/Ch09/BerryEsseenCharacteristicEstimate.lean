import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The quantitative transform stage of Berry–Esseen (paper.tex:3325–3345).
The two constants precede all probability spaces and distributions. Finiteness of
the third absolute moment is expressed as Bochner integrability; no local Taylor
or transform bounds are assumed. The real characteristic function is Mathlib's
canonical characteristic function of the pushforward law, with exp(i t x).
-/
open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch09.BerryEsseenCharacteristicEstimate

universe u

def Estimate : Prop :=
  ∃ c C₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < C₀ ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y : Ω → ℝ), Measurable Y →
      Integrable (fun ω => |Y ω| ^ 3) P →
      (∫ ω, Y ω ∂P) = 0 → (∫ ω, Y ω ^ 2 ∂P) = 1 →
      let ρ := ∫ ω, |Y ω| ^ 3 ∂P
      1 ≤ ρ ∧ ∀ (n : ℕ), 2 ≤ n → ∀ t : ℝ,
        |t| ≤ c * Real.sqrt (n : ℝ) / ρ →
        ‖charFun (P.map Y) (t / Real.sqrt (n : ℝ)) ^ n -
            (Real.exp (-t ^ 2 / 2) : ℂ)‖ ≤
          (C₀ * ρ / Real.sqrt (n : ℝ)) * |t| ^ 3 * Real.exp (-t ^ 2 / 6)

end Specs.ProbabilityFoundations.Ch09.BerryEsseenCharacteristicEstimate
