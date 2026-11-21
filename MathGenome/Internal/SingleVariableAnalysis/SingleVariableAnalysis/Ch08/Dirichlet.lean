import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Dirichlet
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Archimedean

/-! The rational indicator has both values on every nondegenerate subinterval.
Consequently its closed-cell Darboux sums are always 1 and 0. The same
density argument proves discontinuity relative to [0,1], also at 0 and 1.
-/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

namespace DirichletSpec
export Specs.SingleVariableAnalysis.Ch08.Dirichlet (dirichletValue)
end DirichletSpec

noncomputable abbrev dirichlet := DirichletSpec.dirichletValue

theorem dirichlet_rational_density :
    Specs.SingleVariableAnalysis.Ch08.Dirichlet.rationalDensity :=
  rational_density

theorem dirichlet_irrational_density :
    Specs.SingleVariableAnalysis.Ch08.Dirichlet.irrationalDensity := by
  intro a b hab
  exact exists_irrational_btwn hab

theorem dirichlet_of_rational {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∃ q : ℚ, (q : ℝ) = x) : dirichlet x = 1 := by
  simp [dirichlet, DirichletSpec.dirichletValue, hx, hq]

theorem dirichlet_of_irrational {x : ℝ} (hx : Irrational x) : dirichlet x = 0 := by
  have hq : ¬ ∃ q : ℚ, (q : ℝ) = x := hx
  simp [dirichlet, DirichletSpec.dirichletValue, hq]

theorem dirichlet_range (x : ℝ) : 0 ≤ dirichlet x ∧ dirichlet x ≤ 1 := by
  classical
  simp only [dirichlet, DirichletSpec.dirichletValue]
  split_ifs <;> norm_num

theorem dirichlet_bounded : Specs.SingleVariableAnalysis.Ch08.Dirichlet.bounded := by
  constructor
  · exact ⟨0, by rintro _ ⟨x, _, rfl⟩; exact (dirichlet_range x).1⟩
  · exact ⟨1, by rintro _ ⟨x, _, rfl⟩; exact (dirichlet_range x).2⟩

theorem dirichlet_interval_bounds :
    Specs.SingleVariableAnalysis.Ch08.Dirichlet.intervalBounds := by
  intro a b ha hab hb
  obtain ⟨q, haq, hqb⟩ := dirichlet_rational_density a b hab
  obtain ⟨r, hirr, har, hrb⟩ := dirichlet_irrational_density a b hab
  have h1 : (1 : ℝ) ∈ dirichlet '' Set.Icc a b := by
    refine ⟨q, ⟨haq.le, hqb.le⟩, ?_⟩
    exact dirichlet_of_rational ⟨ha.trans haq.le, hqb.le.trans hb⟩ ⟨q, rfl⟩
  have h0 : (0 : ℝ) ∈ dirichlet '' Set.Icc a b :=
    ⟨r, ⟨har.le, hrb.le⟩, dirichlet_of_irrational hirr⟩
  have hu : ∀ z ∈ dirichlet '' Set.Icc a b, z ≤ 1 := by
    rintro _ ⟨x, _, rfl⟩
    exact (dirichlet_range x).2
  have hl : ∀ z ∈ dirichlet '' Set.Icc a b, 0 ≤ z := by
    rintro _ ⟨x, _, rfl⟩
    exact (dirichlet_range x).1
  exact ⟨le_antisymm (csSup_le ⟨1, h1⟩ hu) (le_csSup ⟨1, hu⟩ h1),
    le_antisymm (csInf_le ⟨0, hl⟩ h0) (le_csInf ⟨0, h0⟩ hl)⟩

theorem dirichlet_cell_bounds : Specs.SingleVariableAnalysis.Ch08.Dirichlet.cellBounds := by
  intro P hf i
  have ha : 0 ≤ P.point i.castSucc := by
    simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i.castSucc)
  have hb : P.point i.succ ≤ 1 := by
    simpa only [P.last] using P.strictMono.monotone (Fin.le_last i.succ)
  exact dirichlet_interval_bounds _ _ ha (P.strictMono (Fin.castSucc_lt_succ (i := i))) hb

theorem dirichlet_partition_sums : Specs.SingleVariableAnalysis.Ch08.Dirichlet.partitionSums := by
  intro P hf
  change upperSum dirichlet P hf = 1 ∧ lowerSum dirichlet P hf = 0
  have hu : upperSum dirichlet P hf = ∑ i : Fin P.n, cellLength P i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(dirichlet_cell_bounds P hf i).1, one_mul]
  have hl : lowerSum dirichlet P hf = 0 := by
    change (∑ i : Fin P.n, cellInfimum dirichlet P hf i * cellLength P i) = 0
    simp only [(dirichlet_cell_bounds P hf _).2, zero_mul, Finset.sum_const_zero]
  refine ⟨?_, hl⟩
  rw [hu]
  change (∑ i : Fin P.n, (P.point i.succ - P.point i.castSucc)) = 1
  rw [sum_cell_differences, P.last, P.first, sub_zero]

theorem dirichlet_integral_bounds : Specs.SingleVariableAnalysis.Ch08.Dirichlet.integralBounds := by
  intro hf
  obtain ⟨P⟩ := partition_exists (by norm_num : (0 : ℝ) ≤ 1)
  have hl : Set.range (fun Q : Partition 0 1 => lowerSum dirichlet Q hf) = {0} := by
    ext z
    constructor
    · rintro ⟨Q, rfl⟩
      exact (dirichlet_partition_sums Q hf).2
    · intro hz
      exact ⟨P, (dirichlet_partition_sums P hf).2.trans (Set.mem_singleton_iff.mp hz).symm⟩
  have hu : Set.range (fun Q : Partition 0 1 => upperSum dirichlet Q hf) = {1} := by
    ext z
    constructor
    · rintro ⟨Q, rfl⟩
      exact (dirichlet_partition_sums Q hf).1
    · intro hz
      exact ⟨P, (dirichlet_partition_sums P hf).1.trans (Set.mem_singleton_iff.mp hz).symm⟩
  change sSup _ = 0 ∧ sInf _ = 1
  rw [hl, hu, csSup_singleton, csInf_singleton]
  exact ⟨rfl, rfl⟩

theorem dirichlet_not_integrable : Specs.SingleVariableAnalysis.Ch08.Dirichlet.notIntegrable := by
  rintro ⟨hab, hf, heq⟩
  have h := dirichlet_integral_bounds hf
  have : (0 : ℝ) = 1 := h.1.symm.trans (heq.trans h.2)
  norm_num at this

/-- Every relative ball contains a nondegenerate open interval in [0,1]. -/
theorem interval_inside_unit_neighborhood {x δ : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < δ) : ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      ∀ y ∈ Set.Ioo a b, dist y x < δ := by
  by_cases hx1 : x < 1
  · refine ⟨x, min 1 (x + δ), hx.1, lt_min hx1 (by linarith), min_le_left _ _, ?_⟩
    intro y hy
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hy.1)]
    have := hy.2.trans_le (min_le_right 1 (x + δ))
    linarith
  · have heq : x = 1 := le_antisymm hx.2 (le_of_not_gt hx1)
    refine ⟨max 0 (x - δ), x, le_max_left _ _, ?_, hx.2, ?_⟩
    · exact max_lt (by linarith) (by linarith)
    · intro y hy
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hy.2)]
      have := (le_max_right 0 (x - δ)).trans_lt hy.1
      linarith

theorem dirichlet_discontinuous_everywhere :
    Specs.SingleVariableAnalysis.Ch08.Dirichlet.discontinuousEverywhere := by
  intro x hx hc
  change ContinuousWithinAt dirichlet (Set.Icc (0 : ℝ) 1) x at hc
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousWithinAt_iff.mp hc (1/2) (by norm_num)
  obtain ⟨a, b, ha, hab, hb, hnear⟩ := interval_inside_unit_neighborhood hx hδ
  obtain ⟨q, haq, hqb⟩ := dirichlet_rational_density a b hab
  obtain ⟨r, hirr, har, hrb⟩ := dirichlet_irrational_density a b hab
  have hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.trans haq.le, hqb.le.trans hb⟩
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.trans har.le, hrb.le.trans hb⟩
  have hqc := hcδ hq (hnear _ ⟨haq, hqb⟩)
  have hrc := hcδ hr (hnear _ ⟨har, hrb⟩)
  have ht := dist_triangle (dirichlet (q : ℝ)) (dirichlet x) (dirichlet r)
  rw [dirichlet_of_rational hq ⟨q, rfl⟩, dirichlet_of_irrational hirr] at ht
  rw [dirichlet_of_rational hq ⟨q, rfl⟩] at hqc
  rw [dirichlet_of_irrational hirr] at hrc
  rw [dist_comm (dirichlet x) 0] at ht
  norm_num [Real.dist_eq] at ht hqc hrc
  linarith

end SingleVariableAnalysis.Riemann
