import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Tightness

/-! Tightness and the escaping Dirac example (paper.tex, lines 1738–1747). -/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch06

universe u
noncomputable section

/-- Uniform tightness, with an extended nonnegative supremum (empty supremum zero). -/
def UniformlyTight {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (A : Set (ProbabilityMeasure S)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : Set S, IsCompact K ∧
    (⨆ μ ∈ A, (μ : Measure S) Kᶜ) < ENNReal.ofReal ε

/-- A law is tight when its singleton family is uniformly tight. -/
def Tight {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : ProbabilityMeasure S) : Prop := UniformlyTight {μ}

/-- A point mass as a canonical probability law. -/
def diracLaw {S : Type u} [MeasurableSpace S] (x : S) : ProbabilityMeasure S :=
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

/-- The positive integer point masses on the real line. -/
def naturalDiracFamily : Set (ProbabilityMeasure ℝ) :=
  (fun n : ℕ => diracLaw (n : ℝ)) '' Set.Ici 1

/-- Quantified uniform bounds, including the empty family. Shrinking epsilon
in the reverse implication controls the supremum strictly. -/
theorem uniformlyTight_iff {S : Type u} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] (A : Set (ProbabilityMeasure S)) :
    UniformlyTight A ↔ ∀ ε : ℝ, 0 < ε →
      ∃ K : Set S, IsCompact K ∧ ∀ μ ∈ A, (μ : Measure S) Kᶜ < ENNReal.ofReal ε := by
  constructor
  · intro h ε hε
    obtain ⟨K, hK, hbound⟩ := h ε hε
    exact ⟨K, hK, fun μ hμ => (le_iSup₂ μ hμ).trans_lt hbound⟩
  · intro h ε hε
    obtain ⟨K, hK, hbound⟩ := h (ε / 2) (half_pos hε)
    refine ⟨K, hK, (iSup₂_le fun μ hμ => (hbound μ hμ).le).trans_lt ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)

theorem uniformlyTight_empty {S : Type u} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] : UniformlyTight (∅ : Set (ProbabilityMeasure S)) := by
  rw [uniformlyTight_iff]
  exact fun ε _ => ⟨∅, isCompact_empty, by simp⟩

theorem tight_iff {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : ProbabilityMeasure S) :
    Tight μ ↔ ∀ ε : ℝ, 0 < ε →
      ∃ K : Set S, IsCompact K ∧ (μ : Measure S) Kᶜ < ENNReal.ofReal ε := by
  simp [Tight, uniformlyTight_iff]

theorem diracLaw_tight {S : Type u} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] (x : S) : Tight (diracLaw x) := by
  rw [tight_iff]
  intro ε hε
  refine ⟨{x}, isCompact_singleton, ?_⟩
  simpa [diracLaw] using (ENNReal.ofReal_pos.mpr hε)

theorem natural_dirac_tight (n : ℕ) (_hn : 1 ≤ n) :
    Tight (diracLaw (n : ℝ)) := diracLaw_tight _

theorem naturalDiracFamily_not_uniformlyTight : ¬ UniformlyTight naturalDiracFamily := by
  intro h
  obtain ⟨K, hK, hbound⟩ := (uniformlyTight_iff _).mp h 1 zero_lt_one
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have hnK : ((n + 1 : ℕ) : ℝ) ∉ K := by
    intro hmem
    have := hb hmem
    push_cast at this ⊢
    exact (not_le_of_gt (lt_trans hn (lt_add_one _))) this
  have hmem : diracLaw ((n + 1 : ℕ) : ℝ) ∈ naturalDiracFamily :=
    ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), rfl⟩
  have hbad := hbound _ hmem
  have hmass : (diracLaw ((n + 1 : ℕ) : ℝ) : Measure ℝ) Kᶜ = 1 :=
    Measure.dirac_apply_of_mem hnK
  rw [hmass] at hbad
  simpa using hbad

end
end ProbabilityFoundations.Ch06
