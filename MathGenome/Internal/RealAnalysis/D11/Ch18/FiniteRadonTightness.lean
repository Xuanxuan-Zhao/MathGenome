import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.D11.Ch01.ElementaryMeasuresLimits
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.FiniteRadonTightness
import Mathlib.Topology.Order.Compact

/-!
Finite Radon tightness and the escaping Dirac probabilities, paper.tex:5410–5417.
The finite Radon proof uses only compact-inner approximation of the open set X.
The counterexample has a single, fixed family of Borel probability measures.
-/
namespace D11.Ch18

open Set MeasureTheory
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X
local instance {X : Type u} [TopologicalSpace X] : @BorelSpace X _ (borel X) := ⟨rfl⟩

/-- A compact set captures all but any prescribed positive mass error. -/
def compactTight {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borelSpace X)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K, IsCompact K ∧ μ (univ \ K) < ε

/-- A single compact set works simultaneously for every measure in the family.
The predicate makes sense for any family; in particular for families of finite measures. -/
def uniformlyCompactTight {X : Type u} [TopologicalSpace X]
    (P : Set (@Measure X (borelSpace X))) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K, IsCompact K ∧ ∀ μ ∈ P, μ (univ \ K) < ε

/-- The Borel point masses at the nonnegative integers. -/
noncomputable def naturalDirac (n : ℕ) : @Measure ℝ (borel ℝ) :=
  Measure.dirac (n : ℝ)

def naturalDiracFamily : Set (@Measure ℝ (borel ℝ)) := Set.range naturalDirac

theorem finite_radon_compactTight {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (μ : @Measure X (borelSpace X))
    (hμ : isRadon μ) (hfin : μ univ < ∞) : compactTight μ := by
  intro ε hε
  have hin := (compactInnerRegularOpen_iff μ).mp hμ.2.2
  obtain ⟨K, hKX, hK, hmass⟩ :=
    hin.exists_subset_lt_add isCompact_empty isOpen_univ hfin.ne hε.ne'
  refine ⟨K, hK, ?_⟩
  exact measure_sdiff_lt_of_lt_add (μ := μ) hK.measurableSet.nullMeasurableSet hKX
    (ne_top_of_le_ne_top hfin.ne (measure_mono hKX)) hmass

theorem naturalDirac_probability_radon_tight (n : ℕ) :
    IsProbabilityMeasure (naturalDirac n) ∧ isRadon (naturalDirac n) ∧
      compactTight (naturalDirac n) := by
  have hprob : IsProbabilityMeasure (naturalDirac n) := by
    constructor
    exact Measure.dirac_apply_of_mem (mem_univ _)
  have hrad : isRadon (naturalDirac n) := by
    apply (isRadon_iff_regular _).mpr
    infer_instance
  refine ⟨hprob, hrad, ?_⟩
  intro ε hε
  refine ⟨{(n : ℝ)}, isCompact_singleton, ?_⟩
  simpa [naturalDirac, Measure.dirac_apply] using hε

theorem naturalDirac_escapes_compact (K : Set ℝ) (hK : IsCompact K) :
    ∃ n : ℕ, naturalDirac n (univ \ K) = 1 := by
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have hnK : (n : ℝ) ∉ K := fun h => (not_le_of_gt hn) (hb h)
  exact ⟨n, Measure.dirac_apply_of_mem ⟨mem_univ _, hnK⟩⟩

theorem naturalDirac_not_uniform_at_error (ε : ℝ≥0∞) (_hε : 0 < ε) (hε1 : ε < 1) :
    ¬ ∃ K : Set ℝ, IsCompact K ∧
      ∀ μ ∈ naturalDiracFamily, μ (univ \ K) < ε := by
  rintro ⟨K, hK, hmass⟩
  obtain ⟨n, hn⟩ := naturalDirac_escapes_compact K hK
  have h := hmass (naturalDirac n) (mem_range_self n)
  rw [hn] at h
  exact (lt_asymm hε1 h)

theorem naturalDirac_not_uniformlyCompactTight :
    ¬ uniformlyCompactTight naturalDiracFamily := by
  intro h
  exact naturalDirac_not_uniform_at_error (1 / 2) (by norm_num) (by norm_num)
    (h (1 / 2) (by norm_num))

end D11.Ch18
