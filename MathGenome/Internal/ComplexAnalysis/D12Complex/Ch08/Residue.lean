import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.Residue
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Laurent

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace D12Complex.Residue

/-- The -1 coefficient integral has no kernel denominator. -/
theorem coefficientIntegral_neg_one (f : ℂ → ℂ) (a : ℂ) (ρ : ℝ) :
    Laurent.coefficientIntegral f a ρ (-1) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral f a ρ := by
  simp [Laurent.coefficientIntegral]

theorem differential_apply : Specs.D12Complex.Ch08.Residue.differential_apply_type := by
  intro f z v
  simp [differential]

theorem differential_coefficient :
    Specs.D12Complex.Ch08.Residue.differential_coefficient_type := by
  intro ω
  funext z
  ext
  simp [differential]

theorem differentialResidue_differential :
    Specs.D12Complex.Ch08.Residue.differentialResidue_differential_type := by
  intro f a
  simp [differentialResidue, differential]

/-- Radius independence makes the normalized integrals eventually constant as
ρ tends to zero from above. -/
theorem residue_eq_circleIntegral :
    Specs.D12Complex.Ch08.Residue.residue_eq_circleIntegral_type := by
  intro f a R hf ρ hρ hρR
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hρ)] with σ hσ hσρ
  have hσR : ENNReal.ofReal σ < R :=
    (ENNReal.ofReal_le_ofReal (le_of_lt hσρ)).trans_lt hρR
  simpa only [coefficientIntegral_neg_one] using
    (Laurent.coefficientIntegral_independent a 0 R f (le_refl 0) hf
      ρ σ hρ hρR hσ hσR (-1))

theorem residue_eq_laurentCoefficient :
    Specs.D12Complex.Ch08.Residue.residue_eq_laurentCoefficient_type := by
  intro f a R c hR hc
  obtain ⟨ρ, hρ, hρR⟩ := Laurent.exists_admissible_radius (le_refl (0 : ℝ))
    (by simpa using hR)
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hρ)] with σ hσ hσρ
  have hσR : ENNReal.ofReal σ < R :=
    (ENNReal.ofReal_le_ofReal (le_of_lt hσρ)).trans_lt hρR
  simpa only [coefficientIntegral_neg_one] using
    (Laurent.coefficientFormula_of_convergent (le_refl 0) hc hσ hσR (-1))

theorem exists_laurent_with_residue :
    Specs.D12Complex.Ch08.Residue.exists_laurent_with_residue_type := by
  intro f a R hR hf
  obtain ⟨c, hc, _⟩ := Laurent.laurent_exists a 0 R f (le_refl 0)
    (by simpa using hR) hf
  exact ⟨c, hc, residue_eq_laurentCoefficient f a R c hR
    (Laurent.convergent_of_hasLaurentSeriesOn hc)⟩

theorem circleIntegral_independent :
    Specs.D12Complex.Ch08.Residue.circleIntegral_independent_type := by
  intro f a R hf ρ σ hρ hρR hσ hσR
  have h := (residue_eq_circleIntegral f a R hf ρ hρ hρR).symm.trans
    (residue_eq_circleIntegral f a R hf σ hσ hσR)
  exact mul_left_cancel₀ (inv_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
    Complex.I_ne_zero)) h

theorem differentialResidue_eq_circleIntegral :
    Specs.D12Complex.Ch08.Residue.differentialResidue_eq_circleIntegral_type := by
  intro ω a R hf ρ hρ hρR
  exact residue_eq_circleIntegral (fun z => ω z 1) a R hf ρ hρ hρR

end D12Complex.Residue

/-! Candidate exports of the shared definitions, with checked value bindings. -/
namespace D12Complex.Residue.Definitions
abbrev differential : Specs.D12Complex.Ch08.Residue.differential_type :=
  D12Complex.Residue.differential
abbrev residue : Specs.D12Complex.Ch08.Residue.residue_type :=
  D12Complex.Residue.residue
abbrev differentialResidue : Specs.D12Complex.Ch08.Residue.differentialResidue_type :=
  D12Complex.Residue.differentialResidue
end D12Complex.Residue.Definitions
