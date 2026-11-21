import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonFiniteInner
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonSigmaFiniteInner

/-!
# Inner regularity on sigma-finite Borel sets

This proves paper.tex:5366–5380 using the upstream finite-set result.
Finite unions of the given cover form an increasing finite-mass exhaustion.
Continuity from below transfers the compact suprema to their union, including
when its mass is infinite. The measure itself need not be sigma-finite.

The sigma-finite corollary intersects a finite-mass exhaustion of the whole
space with the specified Borel set. In the sigma-compact corollary the compact
covering has finite masses by the Radon hypothesis. All domains stay Borel.
-/
namespace D11.Ch18.RadonSigmaFiniteInner

open Set MeasureTheory
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X
local instance {X : Type u} [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- Local compact-inner regularity; no global sigma-finiteness is assumed. -/
theorem countable_union_inner_regular
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) (hμ : isRadon μ)
    (E : Set X) (_hE : MeasurableSet[borelSpace X] E)
    (hcover : ∃ A : ℕ → Set X,
      (∀ n, MeasurableSet[borelSpace X] (A n) ∧ μ (A n) < ∞) ∧ (⋃ n, A n) = E) :
    compactInnerRegularOn μ E := by
  obtain ⟨A, hA, hAE⟩ := hcover
  let F : ℕ → Set X := accumulate A
  have hFm (n : ℕ) : MeasurableSet (F n) := by
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => (hA i).1
  have hFfin (n : ℕ) : μ (F n) < ∞ :=
    measure_biUnion_lt_top (finite_Iic n) (fun i _ => (hA i).2)
  have hFE (n : ℕ) : F n ⊆ E := by
    rw [← hAE]
    exact iUnion₂_subset fun i _ => subset_iUnion A i
  have hFU : (⋃ n, F n) = E := by rw [iUnion_accumulate, hAE]
  have hlim : (⨆ n, μ (F n)) = μ E :=
    (Ch01.MeasureBoundsContinuity.continuity_from_below μ F E hFm
      monotone_accumulate hFU).2.1
  unfold compactInnerRegularOn
  apply le_antisymm
  · rw [← hlim]
    refine iSup_le fun n => ?_
    rw [RadonFiniteInner.finite_inner_regular μ hμ (F n) (hFm n) (hFfin n)]
    exact iSup_le fun K => iSup_le fun hKF => iSup_le fun hK =>
      le_iSup_of_le K (le_iSup_of_le (hKF.trans (hFE n)) (le_iSup_of_le hK le_rfl))
  · exact iSup_le fun K => iSup_le fun hKE => iSup_le fun _ => measure_mono hKE

/-- The local theorem phrased using the canonical sigma-finite-set predicate. -/
theorem sigmaFiniteSet_inner_regular
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) (hμ : isRadon μ)
    (E : Set X) (hE : Ch01.MeasureDefinitions.isSigmaFiniteSet μ E) :
    compactInnerRegularOn μ E := by
  obtain ⟨hE, A, hA, hAE⟩ := hE
  exact countable_union_inner_regular μ hμ E hE
    ⟨A, fun n => ⟨(hA n).1, (hA n).2.2⟩, hAE⟩

/-- Full Borel compact-inner and outer regularity in the sigma-finite case. -/
theorem sigmaFinite_fully_regular
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) (hμ : isRadon μ) (hσ : SigmaFinite μ) :
    isFullyRegular μ := by
  obtain ⟨F, hF, _, hFU⟩ :=
    (Ch01.ExhaustionRestriction.sigmaFinite_iff_increasing_exhaustion μ).mp hσ
  refine ⟨hμ, fun E hE => countable_union_inner_regular μ hμ E hE ?_⟩
  refine ⟨fun n => E ∩ F n, fun n => ⟨hE.inter (hF n).1,
    (measure_mono inter_subset_right).trans_lt (hF n).2⟩, ?_⟩
  rw [← inter_iUnion, hFU, inter_univ]

/-- A compact covering is a finite-mass Borel covering, giving both conclusions. -/
theorem sigmaCompact_regular
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] (μ : @Measure X (borelSpace X)) (hμ : isRadon μ) :
    SigmaFinite μ ∧ isFullyRegular μ := by
  have hσ : SigmaFinite μ := (Ch01.MeasureDefinitions.sigmaFinite_iff μ).mpr
    ⟨compactCovering X, fun n => ⟨(isCompact_compactCovering X n).measurableSet,
      hμ.1 _ (isCompact_compactCovering X n)⟩, iUnion_compactCovering X⟩
  exact ⟨hσ, sigmaFinite_fully_regular μ hμ hσ⟩

end D11.Ch18.RadonSigmaFiniteInner
