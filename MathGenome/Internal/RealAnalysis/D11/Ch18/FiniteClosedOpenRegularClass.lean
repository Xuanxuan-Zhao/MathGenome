import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.FiniteClosedOpenRegularClass

/-!
The finite-measure regularity argument shared by the LCH and metric proofs in
paper.tex:5382–5401. The main library theorem used below proves the general
finite-measure step by Borel induction, without any separation assumptions.
We first bridge the source's error estimates to its `InnerRegularWRT` hypothesis.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch18.FiniteClosedOpenRegularClass

variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (h : ∀ U : Set X, IsOpen U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Set X, F ⊆ U ∧ IsClosed F ∧ μ (U \ F) < ENNReal.ofReal ε)

include h

/-- The hypothesis in the paper implies precisely the library's open-set
closed inner regularity, and hence weak regularity for a finite Borel measure. -/
theorem weaklyRegular_of_open_inner : μ.WeaklyRegular := by
  apply Measure.InnerRegularWRT.weaklyRegular_of_finite μ
  intro U hU r hr
  obtain ⟨ε, _, hε, hεgap⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp (tsub_pos_iff_lt.mpr hr)
  obtain ⟨F, hFU, hFc, hF⟩ := h U hU ε (ENNReal.ofReal_pos.mp hε)
  refine ⟨F, hFU, hFc, ?_⟩
  have hlt : μ U - μ F < μ U - r :=
    le_measure_sdiff.trans_lt (hF.trans hεgap)
  have hcancel := ENNReal.sub_lt_of_sub_lt tsub_le_self
    (Or.inl (measure_ne_top μ U)) hlt
  simpa only [ENNReal.sub_sub_cancel (measure_ne_top μ U) hr.le] using hcancel

/-- A single sandwich whose entire gap has measure less than the requested error. -/
theorem borel_closed_open_approximation (E : Set X) (hE : MeasurableSet E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F V : Set X, IsClosed F ∧ IsOpen V ∧ F ⊆ E ∧ E ⊆ V ∧
      μ (V \ F) < ENNReal.ofReal ε := by
  have : μ.WeaklyRegular := weaklyRegular_of_open_inner μ h
  have hhalf : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  obtain ⟨F, hFE, hFc, hF⟩ := hE.exists_isClosed_sdiff_lt (measure_ne_top μ E) hhalf
  obtain ⟨V, hEV, hVo, _, hV⟩ := hE.exists_isOpen_sdiff_lt (measure_ne_top μ E) hhalf
  refine ⟨F, V, hFc, hVo, hFE, hEV, ?_⟩
  have hsub : V \ F ⊆ (V \ E) ∪ (E \ F) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inr ⟨hxE, hx.2⟩
    · exact Or.inl ⟨hx.1, hxE⟩
  calc
    μ (V \ F) ≤ μ ((V \ E) ∪ (E \ F)) := measure_mono hsub
    _ ≤ μ (V \ E) + μ (E \ F) := measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hV hF
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

/-- Every Borel set, and only a Borel set, belongs to the approximation class. -/
theorem mem_closedOpenClass_iff (E : Set X) :
    E ∈ closedOpenClass μ ↔ MeasurableSet E := by
  exact ⟨fun hE => hE.1, fun hE => ⟨hE, borel_closed_open_approximation μ h E hE⟩⟩

/-- Algebra closure together with countable-union closure is precisely the
sigma-algebra criterion from the shared set-system interface. -/
theorem closedOpenClass_sigmaAlgebra :
    IsSetAlgebra (closedOpenClass μ) ∧
    (∀ E : ℕ → Set X, (∀ n, E n ∈ closedOpenClass μ) →
      (⋃ n, E n) ∈ closedOpenClass μ) ∧
    (∀ U : Set X, IsOpen U → U ∈ closedOpenClass μ) := by
  have hm := mem_closedOpenClass_iff μ h
  refine ⟨⟨(hm ∅).mpr MeasurableSet.empty, ?_, ?_⟩, ?_, ?_⟩
  · intro E hE
    exact (hm Eᶜ).mpr ((hm E).mp hE).compl
  · intro E A hE hA
    exact (hm (E ∪ A)).mpr (((hm E).mp hE).union ((hm A).mp hA))
  · intro E hE
    exact (hm (⋃ n, E n)).mpr (MeasurableSet.iUnion fun n => (hm (E n)).mp (hE n))
  · intro U hU
    exact (hm U).mpr hU.measurableSet

/-- The same closed/open witnesses give the two error bounds stated in the goal. -/
theorem borel_inner_outer_approximation (E : Set X) (hE : MeasurableSet E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F V : Set X, IsClosed F ∧ IsOpen V ∧ F ⊆ E ∧ E ⊆ V ∧
      μ (E \ F) < ENNReal.ofReal ε ∧ μ (V \ E) < ENNReal.ofReal ε := by
  obtain ⟨F, V, hFc, hVo, hFE, hEV, hgap⟩ :=
    borel_closed_open_approximation μ h E hE ε hε
  exact ⟨F, V, hFc, hVo, hFE, hEV,
    (measure_mono (sdiff_subset_sdiff_left hEV)).trans_lt hgap,
    (measure_mono (sdiff_subset_sdiff_right hFE)).trans_lt hgap⟩

/-- Weak regularity upgrades to closed inner regularity on all Borel sets
because this measure is finite. -/
theorem borel_regularity : μ.OuterRegular ∧ μ.InnerRegularWRT IsClosed MeasurableSet := by
  have : μ.WeaklyRegular := weaklyRegular_of_open_inner μ h
  refine ⟨inferInstance, ?_⟩
  intro E hE r hr
  exact Measure.WeaklyRegular.innerRegular_measurable ⟨hE, measure_ne_top μ E⟩ r hr

/-- The qualitative regularity identities accompany the quantitative bounds. -/
theorem borel_measure_formulas (E : Set X) (hE : MeasurableSet E) :
    (μ E = ⨆ (F : Set X) (_ : F ⊆ E) (_ : IsClosed F), μ F) ∧
    (μ E = ⨅ (V : Set X) (_ : E ⊆ V) (_ : IsOpen V), μ V) := by
  have : μ.WeaklyRegular := weaklyRegular_of_open_inner μ h
  exact ⟨hE.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top μ E),
    E.measure_eq_iInf_isOpen μ⟩

end D11.Ch18.FiniteClosedOpenRegularClass
