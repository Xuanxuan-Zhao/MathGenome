import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.HarmonicMeasures
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.RegularDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.MeanValueStrongPrinciple
import Mathlib.Topology.ContinuousOn

noncomputable section
open Set Metric Filter
open scoped Topology BigOperators

namespace D12Complex.HarmonicMeasures

abbrev IsCompactBoundaryPartition :
    Specs.D12Complex.Ch14.HarmonicMeasures.IsCompactBoundaryPartition_type :=
  Specs.D12Complex.Ch14.HarmonicMeasures.IsCompactBoundaryPartition_value
abbrev componentBoundaryData :
    Specs.D12Complex.Ch14.HarmonicMeasures.componentBoundaryData_type :=
  Specs.D12Complex.Ch14.HarmonicMeasures.componentBoundaryData_value
abbrev harmonicMeasure : Specs.D12Complex.Ch14.HarmonicMeasures.harmonicMeasure_type :=
  Specs.D12Complex.Ch14.HarmonicMeasures.harmonicMeasure_value

variable {ι : Type} [Fintype ι] {Ω : Set ℂ} {C : ι → Set ℂ}

omit [Fintype ι] in
lemma part_subset_boundary (hC : IsCompactBoundaryPartition Ω C) (j : ι) :
    C j ⊆ frontier Ω := by
  rw [← hC.2.2.2]
  exact subset_iUnion C j

omit [Fintype ι] in
lemma boundaryData_on_part (hC : IsCompactBoundaryPartition Ω C) (j k : ι)
    {ξ : ℂ} (hξ : ξ ∈ C k) :
    componentBoundaryData C j ξ = @ite ℝ (j = k) (Classical.propDecidable _) 1 0 := by
  classical
  by_cases h : j = k
  · subst k
    simp [componentBoundaryData, Specs.D12Complex.Ch14.HarmonicMeasures.componentBoundaryData_value, hξ]
  · have hn : ξ ∉ C j := fun hj => Set.disjoint_left.mp (hC.2.2.1 h) hj hξ
    simp [componentBoundaryData, Specs.D12Complex.Ch14.HarmonicMeasures.componentBoundaryData_value, hn, h]

theorem boundaryData_continuous :
    Specs.D12Complex.Ch14.HarmonicMeasures.boundaryData_continuous_type := by
  intro ι _ Ω C hC j
  classical
  let K : Set ℂ := ⋃ k : {k : ι // k ≠ j}, C k
  have hK : IsClosed K := isClosed_iUnion_of_finite (fun k => (hC.1 k).isClosed)
  have hCK : C j ∪ K = frontier Ω := by
    rw [← hC.2.2.2]
    ext ξ
    simp only [K, mem_union, mem_iUnion, Subtype.exists]
    constructor
    · rintro (hj | ⟨k, _, hk⟩)
      · exact ⟨j, hj⟩
      · exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      by_cases he : k = j
      · exact Or.inl (he ▸ hk)
      · exact Or.inr ⟨k, he, hk⟩
  rw [← hCK]
  apply (continuousOn_union_iff_of_isClosed (hC.1 j).isClosed hK).mpr
  constructor
  · apply (continuousOn_const (c := (1 : ℝ))).congr
    intro ξ hξ
    simp [Specs.D12Complex.Ch14.HarmonicMeasures.componentBoundaryData_value, hξ]
  · apply (continuousOn_const (c := (0 : ℝ))).congr
    intro ξ hξ
    obtain ⟨⟨k, hk⟩, hξ⟩ := mem_iUnion.mp hξ
    have hn : ξ ∉ C j := fun hj => Set.disjoint_left.mp (hC.2.2.1 hk) hξ hj
    simp [Specs.D12Complex.Ch14.HarmonicMeasures.componentBoundaryData_value, hn]

theorem harmonicMeasure_solution :
    Specs.D12Complex.Ch14.HarmonicMeasures.harmonicMeasure_solution_type := by
  intro ι _ Ω C hΩ hb hr hC j
  have hsol := RegularDirichlet.perronSolution_isSolution hΩ hb hr
    (boundaryData_continuous Ω C hC j)
  exact ⟨hsol, fun u hu => RegularDirichlet.solution_unique hb hu hsol⟩

theorem harmonicMeasure_boundary :
    Specs.D12Complex.Ch14.HarmonicMeasures.harmonicMeasure_boundary_type := by
  intro ι _ Ω C hΩ hb hr hC j k ξ hξ
  exact ((harmonicMeasure_solution Ω C hΩ hb hr hC j).1.2.2
    (part_subset_boundary hC k hξ)).trans (boundaryData_on_part hC j k hξ)

lemma harmonic_const (hΩ : IsOpen Ω) (c : ℝ) : HarmonicOn Ω (fun _ => c) := by
  exact (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω _ hΩ).mpr
    (InnerProductSpace.harmonicOnNhd_const c)

lemma solution_const (hΩ : IsOpen Ω) (c : ℝ) :
    IsDirichletSolution Ω (fun _ => c) (fun _ => c) :=
  ⟨harmonic_const hΩ c, continuousOn_const, fun _ _ => rfl⟩

theorem harmonicMeasure_bounds :
    Specs.D12Complex.Ch14.HarmonicMeasures.harmonicMeasure_bounds_type := by
  intro ι _ Ω C hΩ hb hr hC j z hz
  have hs := (harmonicMeasure_solution Ω C hΩ hb hr hC j).1
  constructor
  · exact RegularDirichlet.solution_nonneg hb hs (by
      intro ξ _
      simp only [Specs.D12Complex.Ch14.HarmonicMeasures.componentBoundaryData_value]
      split_ifs <;> norm_num) z hz
  · exact RegularDirichlet.solution_comparison hb hs (solution_const hΩ.2.1 1) (by
      intro ξ _
      simp only [Specs.D12Complex.Ch14.HarmonicMeasures.componentBoundaryData_value]
      split_ifs <;> norm_num) z hz

omit [Fintype ι] in
/-- Finite real linear combinations of classical solutions are solutions. -/
lemma solution_finset_sum (hΩ : IsOpen Ω) (s : Finset ι)
    (φ u : ι → ℂ → ℝ) (hs : ∀ j ∈ s, IsDirichletSolution Ω (φ j) (u j)) :
    IsDirichletSolution Ω (fun z => ∑ j ∈ s, φ j z) (fun z => ∑ j ∈ s, u j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using solution_const hΩ 0
  | @insert a s ha ih =>
    have hsum := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert ha, one_mul] using
      RegularDirichlet.solution_linear (hs a (Finset.mem_insert_self a s)) hsum 1 1

lemma weighted_solution (hΩ : IsDomain Ω) (hb : Bornology.IsBounded Ω)
    (hr : ∀ ξ ∈ frontier Ω, RegularBoundaryPoint Ω ξ)
    (hC : IsCompactBoundaryPartition Ω C) (c : ι → ℝ) :
    IsDirichletSolution Ω (fun z => ∑ j, c j * componentBoundaryData C j z)
      (fun z => ∑ j, c j * harmonicMeasure Ω C j z) := by
  apply solution_finset_sum hΩ.2.1 Finset.univ
  intro j _
  simpa only [zero_mul, add_zero] using RegularDirichlet.solution_linear
    (harmonicMeasure_solution Ω C hΩ hb hr hC j).1 (solution_const hΩ.2.1 0) (c j) 0

lemma weighted_boundary (hC : IsCompactBoundaryPartition Ω C) (c : ι → ℝ)
    (k : ι) {ξ : ℂ} (hξ : ξ ∈ C k) :
    (∑ j, c j * componentBoundaryData C j ξ) = c k := by
  classical
  simp_rw [boundaryData_on_part hC _ k hξ]
  simp [mul_ite]

theorem harmonicMeasure_componentSolution :
    Specs.D12Complex.Ch14.HarmonicMeasures.harmonicMeasure_componentSolution_type := by
  intro ι _ Ω C hΩ hb hr hC c
  have hs := weighted_solution hΩ hb hr hC c
  have hdata := fun k ξ hξ => weighted_boundary hC c k (ξ := ξ) hξ
  refine ⟨hs.1, hs.2.1, ?_, ?_, ?_⟩
  · intro k ξ hξ
    exact (hs.2.2 (part_subset_boundary hC k hξ)).trans (hdata k ξ hξ)
  · intro u hu hc hvals
    apply RegularDirichlet.solution_unique hb (u := u) (v := fun z => ∑ j, c j * harmonicMeasure Ω C j z) _ hs
    refine ⟨hu, hc, ?_⟩
    intro ξ hξ
    rw [← hC.2.2.2] at hξ
    obtain ⟨k, hk⟩ := mem_iUnion.mp hξ
    exact (hvals k ξ hk).trans (hdata k ξ hk).symm
  · have hc : ContinuousOn (fun z => ∑ j, c j * componentBoundaryData C j z) (frontier Ω) :=
      continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul (boundaryData_continuous Ω C hC j))
    exact RegularDirichlet.solution_unique hb
      (RegularDirichlet.perronSolution_isSolution hΩ hb hr hc) hs

theorem harmonicMeasure_sum :
    Specs.D12Complex.Ch14.HarmonicMeasures.harmonicMeasure_sum_type := by
  intro ι _ Ω C hΩ hb hr hC z hz
  have hs := harmonicMeasure_componentSolution Ω C hΩ hb hr hC (fun _ => 1)
  have heq := hs.2.2.2.1 (fun _ => 1) (harmonic_const hΩ.2.1 1) continuousOn_const
    (fun _ _ _ => rfl) hz
  simpa only [one_mul] using heq.symm

/-- Constancy in the domain extends to its closure by continuity. -/
lemma constant_on_closure {u : ℂ → ℝ} {r : ℝ}
    (hc : ContinuousOn u (closure Ω)) (he : ∀ z ∈ Ω, u z = r) :
    ∀ z ∈ closure Ω, u z = r :=
  Set.EqOn.of_subset_closure he hc continuousOn_const subset_closure Subset.rfl

theorem harmonicMeasure_strict :
    Specs.D12Complex.Ch14.HarmonicMeasures.harmonicMeasure_strict_type := by
  intro ι _ Ω C hΩ hb hr hC hm j z hz
  classical
  have hs := (harmonicMeasure_solution Ω C hΩ hb hr hC j).1
  have hbounds := harmonicMeasure_bounds Ω C hΩ hb hr hC j
  constructor
  · have hn := (hbounds z (subset_closure hz)).1
    apply lt_of_le_of_ne hn
    intro he
    have heq := MeanValueStrongPrinciple.harmonic_minimum Ω _ hΩ hs.1 z hz
      (fun w hw => he ▸ (hbounds w (subset_closure hw)).1)
    have hzero : ∀ w ∈ closure Ω, harmonicMeasure Ω C j w = 0 :=
      constant_on_closure hs.2.1 (fun w hw => (heq w hw).trans he.symm)
    obtain ⟨ξ, hξ⟩ := hC.2.1 j
    have hone := harmonicMeasure_boundary Ω C hΩ hb hr hC j j ξ hξ
    have := hzero ξ (frontier_subset_closure (part_subset_boundary hC j hξ))
    simp only [ite_true] at hone
    linarith
  · have hn := (hbounds z (subset_closure hz)).2
    apply lt_of_le_of_ne hn
    intro he
    have heq := MeanValueStrongPrinciple.harmonic_maximum Ω _ hΩ hs.1 z hz
      (fun w hw => he ▸ (hbounds w (subset_closure hw)).2)
    have hone : ∀ w ∈ closure Ω, harmonicMeasure Ω C j w = 1 :=
      constant_on_closure hs.2.1 (fun w hw => (heq w hw).trans he)
    obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card hm j
    obtain ⟨ξ, hξ⟩ := hC.2.1 k
    have hzero := harmonicMeasure_boundary Ω C hΩ hb hr hC j k ξ hξ
    have := hone ξ (frontier_subset_closure (part_subset_boundary hC k hξ))
    simp only [ite_eq_right hk.symm] at hzero
    linarith

end D12Complex.HarmonicMeasures
