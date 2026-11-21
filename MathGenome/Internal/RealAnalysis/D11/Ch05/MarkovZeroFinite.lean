import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.MarkovZeroFinite
import MathGenome.Internal.RealAnalysis.D11.Ch05.AlgebraNull
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Markov's inequality and the zero/finite integral consequences of
paper.tex:1654–1690. The upstream finite-simple-supremum/lower-integral
bridge identifies the integrals. Ordinary a.e. is transported through its
proved measurable-null-envelope equivalence, without completing the space.
-/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u
noncomputable section
namespace D11.Ch05.MarkovZeroFinite

open NonnegativeIntegral
open D11.Ch04.AeCommonException

theorem restricted_markov : Specs.D11.Ch05.MarkovZeroFinite.restricted_markov := by
  intro X _ μ f t hf _ht
  change (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) ≤ f x} ≤
      nonnegativeIntegral (μ.restrict {x | (t : ℝ≥0∞) ≤ f x}) f ∧
    nonnegativeIntegral (μ.restrict {x | (t : ℝ≥0∞) ≤ f x}) f ≤
      nonnegativeIntegral μ f
  simp only [integral_eq_lintegral]
  constructor
  · calc
      (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) ≤ f x} =
          ∫⁻ _ in {x | (t : ℝ≥0∞) ≤ f x}, (t : ℝ≥0∞) ∂μ :=
        (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in {x | (t : ℝ≥0∞) ≤ f x}, f x ∂μ :=
        setLIntegral_mono hf (fun _ hx => hx)
  · exact setLIntegral_le_lintegral _ _

theorem markov_inverse : Specs.D11.Ch05.MarkovZeroFinite.markov_inverse := by
  intro X _ μ f t hf ht
  change μ {x | (t : ℝ≥0∞) ≤ f x} ≤ (t : ℝ≥0∞)⁻¹ * nonnegativeIntegral μ f
  rw [integral_eq_lintegral]
  simpa only [div_eq_mul_inv, mul_comm] using
    meas_ge_le_lintegral_div hf.aemeasurable (ENNReal.coe_ne_zero.mpr ht.ne')
      ENNReal.coe_ne_top

theorem zero_integral_iff : Specs.D11.Ch05.MarkovZeroFinite.zero_integral_iff := by
  intro X _ μ f hf
  change nonnegativeIntegral μ f = 0 ↔ aeEq μ f (fun _ => 0)
  rw [integral_eq_lintegral, aeEq_iff_native]
  exact lintegral_eq_zero_iff hf

theorem finite_values_ae : Specs.D11.Ch05.MarkovZeroFinite.finite_values_ae := by
  intro X _ μ f hf hfin
  change nonnegativeIntegral μ f < ∞ at hfin
  change almostEverywhere μ (fun x => f x < ∞)
  rw [almostEverywhere_iff_native]
  exact ae_lt_top hf (by simpa only [integral_eq_lintegral] using hfin.ne)

theorem sigmaFinite_positivity : Specs.D11.Ch05.MarkovZeroFinite.sigmaFinite_positivity := by
  intro X _ μ f hf hfin
  change nonnegativeIntegral μ f < ∞ at hfin
  change MeasurableSet {x | 0 < f x} ∧ ∃ E : ℕ → Set X,
    (∀ n, MeasurableSet (E n) ∧ E n ⊆ {x | 0 < f x} ∧ μ (E n) < ∞) ∧
    (⋃ n, E n) = {x | 0 < f x}
  let E : ℕ → Set X := fun n => {x | ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ f x}
  have hpos (n : ℕ) : (0 : ℝ≥0∞) < ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  refine ⟨measurableSet_lt measurable_const hf, E, ?_, ?_⟩
  · intro n
    refine ⟨measurableSet_le measurable_const hf, fun x hx => (hpos n).trans_le hx, ?_⟩
    have hbound := meas_ge_le_lintegral_div (μ := μ) hf.aemeasurable (hpos n).ne'
      (ENNReal.inv_ne_top.mpr (by simp))
    apply lt_of_le_of_lt hbound
    exact ENNReal.div_lt_top (by simpa only [integral_eq_lintegral] using hfin.ne)
      (hpos n).ne'
  · ext x
    simp only [mem_iUnion, mem_ofPred_eq, E]
    constructor
    · rintro ⟨n, hn⟩
      exact (hpos n).trans_le hn
    · intro hx
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx.ne'
      refine ⟨n, le_trans ?_ hn.le⟩
      exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)

end D11.Ch05.MarkovZeroFinite
