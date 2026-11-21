import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalLpContraction
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.BasicConditionalIdentities
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! Absolute value and Lp contraction, including the essential supremum case,
for Corollary 3.6 (paper.tex 986–1002). We apply Mathlib's full-range conditional
expectation bounds to the canonical project definition. Linearity transfers
the bound to differences. All functions remain on the original probability
space; no completion or regularity assumptions are added. -/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch03

universe u

theorem realConditionalExpectation_abs_le :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Integrable X P →
      ∀ᵐ ω ∂P, |realConditionalExpectation G P X ω| ≤
        realConditionalExpectation G P (fun ω => |X ω|) ω := by
  intro Ω G F P _ _hGF X _hX
  filter_upwards [norm_condExp_le (m := G) (μ := P) X] with ω hω
  simpa only [realConditionalExpectation, Real.norm_eq_abs] using hω

theorem realConditionalExpectation_lp_contraction :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (X : Ω → ℝ), MemLp X p P →
      Integrable X P ∧ MemLp (realConditionalExpectation G P X) p P ∧
        eLpNorm (realConditionalExpectation G P X) p P ≤ eLpNorm X p P ∧
        lpNorm (realConditionalExpectation G P X) p P ≤ lpNorm X p P := by
  intro Ω G F P _ _hGF p hp X hX
  exact ⟨memLp_one_iff_integrable.mp (hX.mono_exponent hp),
    hX.condExp hp, eLpNorm_condExp_le_eLpNorm X hp, hX.lpNorm_condExp_le_lpNorm hp⟩

theorem realConditionalExpectation_essSup_contraction :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), MemLp X ∞ P →
      essSup (fun ω => |realConditionalExpectation G P X ω|) P ≤
        essSup (fun ω => |X ω|) P := by
  intro Ω G F P _ _hGF X hX
  simpa only [realConditionalExpectation, Real.norm_eq_abs] using
    (hX.essSup_norm_condExp_le_essSup_norm (m := G))

theorem realConditionalExpectation_lp_distance_contraction :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (X Y : Ω → ℝ),
      Integrable X P → Integrable Y P → MemLp X p P → MemLp Y p P →
      MemLp (fun ω => realConditionalExpectation G P X ω -
        realConditionalExpectation G P Y ω) p P ∧
      eLpNorm (fun ω => realConditionalExpectation G P X ω -
        realConditionalExpectation G P Y ω) p P ≤
        eLpNorm (fun ω => X ω - Y ω) p P ∧
      lpNorm (fun ω => realConditionalExpectation G P X ω -
        realConditionalExpectation G P Y ω) p P ≤
        lpNorm (fun ω => X ω - Y ω) p P := by
  intro Ω G F P _ _hGF p hp X Y hXi hYi hX hY
  have hsub : condExp G P (X - Y) =ᵐ[P]
      (fun ω => realConditionalExpectation G P X ω -
        realConditionalExpectation G P Y ω) := condExp_sub hXi hYi G
  have hmem : MemLp (X - Y) p P := hX.sub hY
  refine ⟨(memLp_congr_ae hsub).mp (hmem.condExp hp), ?_, ?_⟩
  · rw [← eLpNorm_congr_ae hsub]
    exact eLpNorm_condExp_le_eLpNorm (X - Y) hp
  · change (eLpNorm _ p P).toReal ≤ (eLpNorm _ p P).toReal
    rw [← eLpNorm_congr_ae hsub]
    exact hmem.lpNorm_condExp_le_lpNorm hp

end ProbabilityFoundations.Ch03
