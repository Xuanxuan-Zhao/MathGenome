import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.TriangleRelaxation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace P205.Matching.Triangle

/-- The chosen coordinates list exactly the edges of `K₃`, without repetition. -/
theorem edge_enumeration : Function.Injective edge ∧
    ∀ s : Sym2 Vertex, s ∈ graph.edgeSet ↔ ∃ e : Edge, edge e = s := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [edge]
  · intro s
    induction s using Sym2.inductionOn with
    | _ u v =>
      fin_cases u <;> fin_cases v <;>
        simp [graph, edge, Fin.exists_fin_succ]

/-- Incidence sums in the fixed edge ordering. -/
theorem degreeSum_values (x : Coordinate) :
    degreeSum x 0 = x 0 + x 2 ∧
    degreeSum x 1 = x 0 + x 1 ∧
    degreeSum x 2 = x 1 + x 2 := by
  simp [degreeSum, edge, Fin.sum_univ_succ, Sym2.mem_iff]

/-- The graph degree formulation is precisely the three familiar inequalities. -/
theorem mem_degreeRelaxation_iff (x : Coordinate) :
    x ∈ degreeRelaxation ↔ (∀ e, 0 ≤ x e) ∧
      x 0 + x 1 ≤ 1 ∧ x 1 + x 2 ≤ 1 ∧ x 2 + x 0 ≤ 1 := by
  obtain ⟨h0, h1, h2⟩ := degreeSum_values x
  simp only [degreeRelaxation, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hn, hd⟩
    exact ⟨hn, h1 ▸ hd 1, h2 ▸ hd 2, by simpa [h0, add_comm] using hd 0⟩
  · rintro ⟨hn, h01, h12, h20⟩
    refine ⟨hn, fun v => ?_⟩
    fin_cases v
    · simpa [h0, add_comm] using h20
    · simpa [h1] using h01
    · simpa [h2] using h12

theorem half_feasible : half ∈ degreeRelaxation := by
  rw [mem_degreeRelaxation_iff]
  norm_num [half]

/-- Three tight degree equations have exactly the stated half-integral solution. -/
theorem eq_half_of_degree_equalities (x : Coordinate)
    (h01 : x 0 + x 1 = 1) (h12 : x 1 + x 2 = 1) (h20 : x 2 + x 0 = 1) :
    x = half := by
  funext e
  fin_cases e
  · change x 0 = 1 / 2
    linarith
  · change x 1 = 1 / 2
    linarith
  · change x 2 = 1 / 2
    linarith

/-- A tight upper bound of a strict convex combination is tight at its left endpoint. -/
private theorem tight_left {a b s t : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hs : s ≤ 1) (ht : t ≤ 1)
    (he : a * s + b * t = 1) : s = 1 := by
  have hbt := mul_le_mul_of_nonneg_left ht hb
  have hnonneg : 0 ≤ a * (1 - s) := mul_nonneg ha.le (sub_nonneg.mpr hs)
  have hzero : a * (1 - s) = 0 := by nlinarith
  have := (mul_eq_zero.mp hzero).resolve_left ha.ne'
  linarith

/-- The half point is an extreme point in Mathlib's usual open-segment sense. -/
theorem half_vertex : half ∈ degreeRelaxation.extremePoints ℝ := by
  refine ⟨half_feasible, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  obtain ⟨_, hy01, hy12, hy20⟩ := (mem_degreeRelaxation_iff y).mp hy
  obtain ⟨_, hz01, hz12, hz20⟩ := (mem_degreeRelaxation_iff z).mp hz
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, half] at h0 h1 h2
  apply eq_half_of_degree_equalities y
  · apply tight_left ha hb.le hab hy01 hz01
    nlinarith
  · apply tight_left ha hb.le hab hy12 hz12
    nlinarith
  · apply tight_left ha hb.le hab hy20 hz20
    nlinarith

theorem half_not_integral : ¬ Integral half := by
  intro h
  obtain ⟨z, hz⟩ := h 0
  have hz0 : (0 : ℝ) < z := by rw [← hz]; norm_num [half]
  have hz1 : (z : ℝ) < 1 := by rw [← hz]; norm_num [half]
  have h0 : (0 : ℤ) < z := by exact_mod_cast hz0
  have h1 : z < (1 : ℤ) := by exact_mod_cast hz1
  omega

/-- A matching in the actual triangle graph has at most one edge. -/
theorem matching_size (M : graph.Subgraph) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ 1 := by
  classical
  apply (Set.ncard_le_one (s := M.edgeSet)).mpr
  intro e he f hf
  obtain ⟨i, rfl⟩ := (edge_enumeration.2 e).mp (M.edgeSet_subset he)
  obtain ⟨j, rfl⟩ := (edge_enumeration.2 f).mp (M.edgeSet_subset hf)
  fin_cases i <;> fin_cases j
  all_goals simp only [edge] at he hf ⊢
  all_goals change M.Adj _ _ at he hf
  all_goals first
    | have h := hM.eq_of_adj_left he.symm hf; norm_num at h
    | have h := hM.eq_of_adj_left he hf.symm; norm_num at h

end P205.Matching.Triangle
