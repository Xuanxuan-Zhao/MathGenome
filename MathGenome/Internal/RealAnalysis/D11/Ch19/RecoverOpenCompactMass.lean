import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveRieszMarkov
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.RecoverOpenCompactMass

/-!
Recover the masses of opens and compacts from their positive Cc functional.
Uniqueness identifies any representing measure with the preceding construction.
The compact formula follows by taking cutoffs inside each open neighborhood,
and then using outer regularity. Complex tests correspond exactly to real tests
under the canonical real inclusion and real-part maps.
-/

open Set MeasureTheory
open scoped ENNReal
open Specs.D11.Ch19.PositiveContentOuterMeasure (Positive)
open Specs.D11.Ch19.PositiveRieszMarkov (Represents ComplexPositive)

namespace D11.Ch19.RecoverOpenCompactMass
universe u
noncomputable section

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- The unique representing measure is the canonical positive construction. -/
lemma representing_measure_eq
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (μ : @Measure X (borel X)) (hμ : Represents I μ) :
    μ = PositiveContentOuterMeasure.borelMeasure I hI :=
  (PositiveRieszMarkov.real_representation I hI).unique hμ
    ⟨PositiveContentRadon.radon I hI, PositiveContentIntegral.integral_eq I hI⟩

/-- Open masses are suprema of nonnegative tests bounded by one. -/
theorem real_open_mass
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (μ : @Measure X (borel X)) (hμ : Represents I μ)
    (U : Set X) (hU : IsOpen U) :
    μ U = ⨆ f : CompactlySupportedContinuousMap X ℝ,
      ⨆ (_ : ∀ x, 0 ≤ f x ∧ f x ≤ 1),
        ⨆ (_ : closure {x | f x ≠ 0} ⊆ U), ENNReal.ofReal (I f) := by
  rw [representing_measure_eq I hI μ hμ]
  exact (PositiveContentOuterMeasure.openContent_eq I hI U hU).symm

/-- Compact masses are infima over all nonnegative majorants of one. -/
theorem real_compact_mass
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (μ : @Measure X (borel X)) (hμ : Represents I μ)
    (K : Set X) (hK : IsCompact K) :
    μ K = ⨅ g : CompactlySupportedContinuousMap X ℝ,
      ⨅ (_ : ∀ x, 0 ≤ g x), ⨅ (_ : ∀ x ∈ K, 1 ≤ g x), ENNReal.ofReal (I g) := by
  letI : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  apply le_antisymm
  · refine le_iInf fun g => le_iInf fun hg => le_iInf fun hgK => ?_
    rw [representing_measure_eq I hI μ hμ]
    exact PositiveContentRadon.outerMeasure_le_functional I hI K g hg hgK
  · rw [hμ.1.2.1 K hK.isClosed.measurableSet]
    refine le_iInf fun U => le_iInf fun hKU => le_iInf fun hU => ?_
    obtain ⟨g, hg, hgK, _, hgs⟩ := D11.Ch18.compact_cutoff X K U hK hU hKU
    calc
      (⨅ g : CompactlySupportedContinuousMap X ℝ,
        ⨅ (_ : ∀ x, 0 ≤ g x), ⨅ (_ : ∀ x ∈ K, 1 ≤ g x), ENNReal.ofReal (I g))
          ≤ ENNReal.ofReal (I g) :=
        iInf_le_of_le g (iInf_le_of_le (fun x => (hg x).1)
          (iInf_le_of_le (fun x hx => (hgK x hx).ge) le_rfl))
      _ ≤ μ U := by
        rw [real_open_mass I hI μ hμ U hU]
        exact le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hgs le_rfl))

omit [T2Space X] [LocallyCompactSpace X] in
/-- Taking the real part cannot enlarge closed support. -/
lemma realPart_support_subset (f : CompactlySupportedContinuousMap X ℂ) :
    closure {x | ccRe f x ≠ 0} ⊆ closure {x | f x ≠ 0} := by
  apply closure_mono
  intro x hx hzero
  exact hx (by simp [hzero])

omit [T2Space X] [LocallyCompactSpace X] in
/-- Real inclusion preserves the entire closed support, not just the nonzero set. -/
lemma ofReal_support_eq (f : CompactlySupportedContinuousMap X ℝ) :
    closure {x | ccOfReal f x ≠ 0} = closure {x | f x ≠ 0} := by
  congr 1
  ext x
  simp

/-- The same open formula for complex-linear positive functionals. -/
theorem complex_open_mass
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ) (hI : ComplexPositive I)
    (μ : @Measure X (borel X)) (hμ : Represents I μ)
    (U : Set X) (hU : IsOpen U) :
    μ U = ⨆ f : CompactlySupportedContinuousMap X ℂ,
      ⨆ (_ : ∀ x, 0 ≤ (f x).re ∧ (f x).re ≤ 1 ∧ (f x).im = 0),
        ⨆ (_ : closure {x | f x ≠ 0} ⊆ U), ENNReal.ofReal (I f).re := by
  have hJ := realRestriction_nonneg I hI
  have hμJ := (PositiveRieszMarkov.represents_realRestriction_iff I hI μ).mpr hμ
  rw [real_open_mass (realRestriction I) hJ μ hμJ U hU]
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => iSup_le fun hs => ?_
    have hfc : ∀ x, 0 ≤ (ccOfReal f x).re ∧
        (ccOfReal f x).re ≤ 1 ∧ (ccOfReal f x).im = 0 :=
      fun x => ⟨(hf x).1, (hf x).2, rfl⟩
    exact le_iSup_of_le (ccOfReal f) (le_iSup_of_le hfc
      (le_iSup_of_le (by rw [ofReal_support_eq]; exact hs) le_rfl))
  · refine iSup_le fun f => iSup_le fun hf => iSup_le fun hs => ?_
    rw [← realRestriction_re I hI f]
    exact le_iSup_of_le (ccRe f)
      (le_iSup_of_le (fun x => ⟨(hf x).1, (hf x).2.1⟩)
        (le_iSup_of_le ((realPart_support_subset f).trans hs) le_rfl))

/-- The same compact formula, with all nonnegative real-valued complex tests. -/
theorem complex_compact_mass
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ) (hI : ComplexPositive I)
    (μ : @Measure X (borel X)) (hμ : Represents I μ)
    (K : Set X) (hK : IsCompact K) :
    μ K = ⨅ g : CompactlySupportedContinuousMap X ℂ,
      ⨅ (_ : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0),
        ⨅ (_ : ∀ x ∈ K, 1 ≤ (g x).re), ENNReal.ofReal (I g).re := by
  have hJ := realRestriction_nonneg I hI
  have hμJ := (PositiveRieszMarkov.represents_realRestriction_iff I hI μ).mpr hμ
  rw [real_compact_mass (realRestriction I) hJ μ hμJ K hK]
  apply le_antisymm
  · refine le_iInf fun g => le_iInf fun hg => le_iInf fun hgK => ?_
    rw [← realRestriction_re I hI g]
    exact iInf_le_of_le (ccRe g) (iInf_le_of_le (fun x => (hg x).1)
      (iInf_le_of_le hgK le_rfl))
  · refine le_iInf fun g => le_iInf fun hg => le_iInf fun hgK => ?_
    exact iInf_le_of_le (ccOfReal g)
      (iInf_le_of_le (fun x => ⟨hg x, rfl⟩) (iInf_le_of_le hgK le_rfl))

end
end D11.Ch19.RecoverOpenCompactMass
