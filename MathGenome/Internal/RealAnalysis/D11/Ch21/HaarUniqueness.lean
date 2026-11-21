import MathGenome.Internal.RealAnalysis.D11.Ch21.CompactKernelRatioIdentity
import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveRieszMarkov
import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarInversion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarUniqueness
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic.FieldSimp

/-!
Uniqueness on arbitrary locally compact Hausdorff groups. The compact-kernel
identity compares Cc integrals using finite compact rectangles. The common
positive test gives a finite positive ratio. Radon uniqueness then identifies
the Borel measures. Right uniqueness is transported through inversion.
-/
namespace D11.Ch21.HaarUniqueness

open MeasureTheory
open scoped ENNReal
open Specs.D11.Ch21.CompactKernelRatioIdentity (mass)
universe u
noncomputable section

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] in
private lemma positive_test :
    ∃ g : CompactlySupportedContinuousMap G ℝ, (∀ x, 0 ≤ g x) ∧ g ≠ 0 := by
  obtain ⟨f, hf, hnonneg, hone⟩ := exists_continuous_nonneg_pos (1 : G)
  let g : CompactlySupportedContinuousMap G ℝ := ⟨f, hf⟩
  refine ⟨g, hnonneg, ?_⟩
  intro h
  exact hone (congrArg (fun k : CompactlySupportedContinuousMap G ℝ => k 1) h)

/-- The source's full left uniqueness, including positivity and uniqueness
of the finite real scalar. -/
theorem left_uniqueness : Specs.D11.Ch21.HaarUniqueness.left_uniqueness := by
  intro G _ _ _ _ _ μ ν hμ hν
  obtain ⟨g, hg, hgne⟩ := positive_test (G := G)
  have hA := (HaarPositiveOpen.integral_pos μ (Or.inl hμ) g hg hgne).2
  have hB := (HaarPositiveOpen.integral_pos ν (Or.inl hν) g hg hgne).2
  let c : ℝ := (∫ x, g x ∂ν) / (∫ x, g x ∂μ)
  have hc : 0 < c := div_pos hB hA
  let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.2.1
  let : Measure.Regular ν := (D11.Ch18.isRadon_iff_regular ν).mp hν.2.1
  let : Measure.Regular (ENNReal.ofReal c • μ) :=
    Measure.Regular.smul ENNReal.ofReal_ne_top
  have heq : ν = ENNReal.ofReal c • μ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    have heμ := (CompactKernelRatioIdentity.ratio_identity μ ν hμ hν g hg hgne f).2.2.2
    have heν := (CompactKernelRatioIdentity.ratio_identity ν ν hν hν g hg hgne f).2.2.2
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul]
    rw [heμ, heν]
    dsimp [c]
    field_simp [hA.ne']
  refine ⟨c, ⟨hc, heq⟩, ?_⟩
  intro d hd
  have he := congrArg (fun ρ : @Measure G (borel G) => ∫ x, g x ∂ρ) hd.2
  rw [integral_smul_measure, ENNReal.toReal_ofReal hd.1.le, smul_eq_mul] at he
  exact (eq_div_iff hA.ne').mpr he.symm

/-- Inversion commutes with multiplication of a measure by a scalar. -/
lemma inversionMeasure_smul (a : ℝ≥0∞) (μ : @Measure G (borel G)) :
    HaarInversion.inversionMeasure (a • μ) = a • HaarInversion.inversionMeasure μ :=
  Measure.map_smul a measurable_inv.aemeasurable

/-- Right Haar uniqueness follows from the left result and the involutive
inversion pushforward; no right invariance of a left Haar measure is assumed. -/
theorem right_uniqueness : Specs.D11.Ch21.HaarUniqueness.right_uniqueness := by
  intro G _ _ _ _ _ μ ν hμ hν
  obtain ⟨c, hc, huniq⟩ := left_uniqueness
    (HaarInversion.inversionMeasure μ) (HaarInversion.inversionMeasure ν)
    (HaarInversion.leftHaar_inversionMeasure μ hμ)
    (HaarInversion.leftHaar_inversionMeasure ν hν)
  refine ⟨c, ⟨hc.1, ?_⟩, ?_⟩
  · have he := congrArg HaarInversion.inversionMeasure hc.2
    simpa only [inversionMeasure_smul, HaarInversion.inversionMeasure_involutive] using he
  · intro d hd
    apply huniq d
    refine ⟨hd.1, ?_⟩
    have he := congrArg HaarInversion.inversionMeasure hd.2
    simpa only [inversionMeasure_smul] using he

end
end D11.Ch21.HaarUniqueness
