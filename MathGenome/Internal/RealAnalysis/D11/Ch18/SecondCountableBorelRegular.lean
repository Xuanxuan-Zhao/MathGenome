import MathGenome.Internal.RealAnalysis.D11.Ch18.LCHLocalFiniteBridge
import MathGenome.Internal.RealAnalysis.D11.Ch18.CountablePrecompactBase
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonSigmaFiniteInner
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.SecondCountableBorelRegular

/-!
# Compact-finite Borel measures when all opens are sigma-compact

This is `paper.tex:5382–5391`, including its second-countable specialization.
First, continuity from below gives compact inner approximation of any
sigma-compact set, for any Borel measure. In particular this applies to every
open set and to every finite restriction of the measure. Finite-measure Borel
induction then makes these restrictions outer regular. A countable finite-mass
open cover allows the outer regularity to be glued to the whole space.
The upstream sigma-compact Radon result supplies sigma-finiteness and full
Borel compact inner regularity. No metric or nonemptiness assumption is used.
-/
namespace D11.Ch18.SecondCountableBorelRegular

open Set MeasureTheory
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X
local instance {X : Type u} [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- A sigma-compact set is compact-inner regular for any Borel measure. -/
theorem sigmaCompact_inner_regular
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (μ : @Measure X (borelSpace X)) (E : Set X) (hE : IsSigmaCompact E) :
    compactInnerRegularOn μ E := by
  obtain ⟨K, hK, hKE⟩ := hE
  have hF (n : ℕ) : IsCompact (accumulate K n) := isCompact_accumulate hK n
  have hFE (n : ℕ) : accumulate K n ⊆ E := by
    rw [← hKE]
    exact iUnion₂_subset fun i _ => subset_iUnion K i
  have hμ : μ E = ⨆ n, μ (accumulate K n) := by
    rw [← Monotone.measure_iUnion monotone_accumulate, iUnion_accumulate, hKE]
  unfold compactInnerRegularOn
  apply le_antisymm
  · rw [hμ]
    exact iSup_le fun n => le_iSup_of_le (accumulate K n)
      (le_iSup_of_le (hFE n) (le_iSup_of_le (hF n) le_rfl))
  · exact iSup_le fun K => iSup_le fun hKE => iSup_le fun _ => measure_mono hKE

/-- The open-set hypothesis alone gives compact inner regularity on opens. -/
theorem open_inner_regular
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (hσ : ∀ U : Set X, IsOpen U → IsSigmaCompact U)
    (μ : @Measure X (borelSpace X)) : compactInnerRegularOpen μ :=
  fun U hU => sigmaCompact_inner_regular μ U (hσ U hU)

/-- Finite Borel measures are outer regular under the open-set hypothesis. -/
theorem finite_outer_regular
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (hσ : ∀ U : Set X, IsOpen U → IsSigmaCompact U)
    (μ : @Measure X (borelSpace X)) [IsFiniteMeasure μ] : Measure.OuterRegular μ := by
  have hi : μ.InnerRegularWRT IsCompact IsOpen :=
    (compactInnerRegularOpen_iff μ).mp (open_inner_regular hσ μ)
  have hc : μ.InnerRegularWRT IsClosed IsOpen := by
    intro U hU r hr
    obtain ⟨K, hKU, hK, hKr⟩ := hi hU r hr
    exact ⟨K, hKU, hK.isClosed, hKr⟩
  have : Measure.WeaklyRegular μ := hc.weaklyRegular_of_finite μ
  infer_instance

/-- Full source theorem: all-open sigma-compactness suffices without a metric.
Sigma-finiteness already follows in this more general case. -/
theorem all_open_sigmaCompact_regular
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (hσ : ∀ U : Set X, IsOpen U → IsSigmaCompact U)
    (μ : @Measure X (borelSpace X)) (hfin : compactFinite μ) :
    SigmaFinite μ ∧ isFullyRegular μ := by
  let : SigmaCompactSpace X := isSigmaCompact_univ_iff.mp (hσ univ isOpen_univ)
  let : IsLocallyFiniteMeasure μ := (locallyFinite_iff μ).mp
    ((compactFinite_iff_locallyFinite μ).mp hfin)
  let S := μ.finiteSpanningSetsInOpen
  have hout : Measure.OuterRegular μ := by
    apply Measure.OuterRegular.of_restrict (s := S.set) ?_ S.set_mem S.spanning.symm.subset
    intro n
    have : IsFiniteMeasure (μ.restrict (S.set n)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using S.finite n⟩
    exact finite_outer_regular hσ (μ.restrict (S.set n))
  have hRadon : isRadon μ :=
    ⟨hfin, (outerRegularBorel_iff μ).mpr hout, open_inner_regular hσ μ⟩
  exact RadonSigmaFiniteInner.sigmaCompact_regular μ hRadon

/-- The countable precompact-base result supplies compact covers of all opens. -/
theorem second_countable_regular
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X]
    (μ : @Measure X (borelSpace X)) (hfin : compactFinite μ) :
    SigmaFinite μ ∧ isFullyRegular μ := by
  apply all_open_sigmaCompact_regular (μ := μ) ?_ hfin
  intro U hU
  obtain ⟨K, hK, hKU⟩ := D11.Ch18.openCompactCover X U hU
  exact ⟨K, fun n => (hK n).1, hKU.symm⟩

end D11.Ch18.SecondCountableBorelRegular
