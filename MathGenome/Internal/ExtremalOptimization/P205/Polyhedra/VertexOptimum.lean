import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.VertexOptimum
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.ActiveRows
import MathGenome.Internal.ExtremalOptimization.P205.LinearProgramming.Certificates
import MathGenome.Internal.ExtremalOptimization.P205.LinearProgramming.StandardForm
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Max

noncomputable section
open Matrix Set
namespace P205.Polyhedra

/-- Moving to the first blocking row preserves all old active constraints and
activates a new one. Only nonnegative step lengths are needed. -/
lemma first_blocking_row {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x d : Coordinate n) (hx : x ∈ polyhedron A b)
    (hd : ∀ i ∈ activeRows A b x, rowCovector A i d = 0)
    (hp : ∃ i, 0 < rowCovector A i d) :
    ∃ t : ℝ, 0 ≤ t ∧ x + t • d ∈ polyhedron A b ∧
      activeRows A b x ⊆ activeRows A b (x + t • d) ∧
      ∃ i ∈ activeRows A b (x + t • d), i ∉ activeRows A b x := by
  classical
  let s := Finset.univ.filter (fun i => 0 < rowCovector A i d)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image
    (fun j => (b j - rowCovector A j x) / rowCovector A j d) hs
  have hip : 0 < rowCovector A i d := (Finset.mem_filter.mp hi).2
  let t := (b i - rowCovector A i x) / rowCovector A i d
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hx i)) hip.le
  have hit : rowCovector A i (x + t • d) = b i := by
    simp only [map_add, map_smul, smul_eq_mul]
    dsimp [t]
    rw [div_mul_cancel₀ _ hip.ne']
    ring
  refine ⟨t, ht, ?_, ?_, i, hit, ?_⟩
  · intro j
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases hj : 0 < rowCovector A j d
    · have hbound := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hmul : t * rowCovector A j d ≤ b j - rowCovector A j x :=
        (le_div_iff₀ hj).mp hbound
      linarith
    · have hmul := mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hj)
      linarith [hx j]
  · intro j hj
    change rowCovector A j (x + t • d) = b j
    simp only [map_add, map_smul, smul_eq_mul, hd j hj, mul_zero, add_zero]
    exact hj
  · intro hiold
    exact hip.ne' (hd i hiold)

/-- Optimality forces every two-sided locally feasible direction to have zero cost. -/
lemma cost_zero_on_active_kernel {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c x d : Coordinate n) (hx : x ∈ polyhedron A b)
    (hopt : ∀ y ∈ polyhedron A b, c ⬝ᵥ x ≤ c ⬝ᵥ y)
    (hd : ∀ i ∈ activeRows A b x, rowCovector A i d = 0) : c ⬝ᵥ d = 0 := by
  obtain ⟨ε, hε, he⟩ := feasible_small_steps A b x d hx hd
  have hp := hopt _ (he (ε / 2) (by rw [abs_of_pos (by positivity)]; linarith))
  have hn := hopt _ (he (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith))
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hp hn
  nlinarith

/-- Among the optimal points choose a maximal active set. Pointedness and a
first blocking row rule out any nonzero vector in its common kernel. -/
theorem vertex_optimizer_of_optimizer {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Coordinate n) (hpoint : IsPointed (polyhedron A b))
    (x₀ : Coordinate n) (hx₀ : x₀ ∈ polyhedron A b)
    (hopt₀ : ∀ y ∈ polyhedron A b, c ⬝ᵥ x₀ ≤ c ⬝ᵥ y) :
    ∃ x, IsVertex A b x ∧ c ⬝ᵥ x = c ⬝ᵥ x₀ ∧
      ∀ y ∈ polyhedron A b, c ⬝ᵥ x ≤ c ⬝ᵥ y := by
  classical
  let S := {x ∈ polyhedron A b | c ⬝ᵥ x = c ⬝ᵥ x₀}
  obtain ⟨x, hx, hmax⟩ := Set.Finite.exists_maximalFor'
    (activeRows A b) S (Set.toFinite _) ⟨x₀, hx₀, rfl⟩
  have hopt : ∀ y ∈ polyhedron A b, c ⬝ᵥ x ≤ c ⬝ᵥ y := by
    intro y hy
    rw [hx.2]
    exact hopt₀ y hy
  refine ⟨x, vertex_of_kernel_trivial A b x hx.1 ?_, hx.2, hopt⟩
  intro d hd
  by_contra hd0
  have hc := cost_zero_on_active_kernel A b c x d hx.1 hopt hd
  have hrow : ∃ i, rowCovector A i d ≠ 0 := by
    by_contra h
    push Not at h
    apply hpoint
    refine ⟨x, d, hd0, fun t i => ?_⟩
    simpa only [map_add, map_smul, smul_eq_mul, h i, mul_zero, add_zero] using hx.1 i
  have horient : ∃ e : Coordinate n,
      (∀ i ∈ activeRows A b x, rowCovector A i e = 0) ∧
      c ⬝ᵥ e = 0 ∧ ∃ i, 0 < rowCovector A i e := by
    obtain ⟨i, hi⟩ := hrow
    rcases lt_or_gt_of_ne hi with hi | hi
    · refine ⟨-d, ?_, ?_, i, ?_⟩
      · intro j hj
        simp only [map_neg, hd j hj, neg_zero]
      · simp only [dotProduct_neg, hc, neg_zero]
      · simpa only [map_neg] using neg_pos.mpr hi
    · exact ⟨d, hd, hc, i, hi⟩
  obtain ⟨e, he, hce, hep⟩ := horient
  obtain ⟨t, _, hnew, hsub, i, hia, hni⟩ := first_blocking_row A b x e hx.1 he hep
  have hcost : c ⬝ᵥ (x + t • e) = c ⬝ᵥ x₀ := by
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hce, mul_zero, add_zero]
    exact hx.2
  exact hni (hmax ⟨hnew, hcost⟩ hsub hia)

private def inequalityProblem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Coordinate n) :
    P205.LinearProgramming.StandardForm.Problem (Fin 0) (Fin m) (Fin 0) (Fin n) where
  equality := 0
  equalityBound := 0
  upper := A
  upperBound := b
  lower := 0
  lowerBound := 0
  cost := c

private lemma inequalityProblem_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Coordinate n) (x : Coordinate n) :
    P205.LinearProgramming.StandardForm.feasible (inequalityProblem A b c) x ↔
      x ∈ polyhedron A b := by
  simp [P205.LinearProgramming.StandardForm.feasible, inequalityProblem,
    polyhedron, rowCovector, Matrix.mulVec, dotProduct]

private lemma inequalityProblem_infimum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Coordinate n) :
    P205.LinearProgramming.StandardForm.infimum (inequalityProblem A b c) =
      objectiveInfimum A b c := by
  unfold P205.LinearProgramming.StandardForm.infimum
    P205.LinearProgramming.StandardForm.values
  rw [Set.image_image]
  have hset : {x | P205.LinearProgramming.StandardForm.feasible (inequalityProblem A b c) x}
      = polyhedron A b := by
    ext x
    exact inequalityProblem_feasible A b c x
  rw [hset]
  rfl

/-- Standard-form strong duality supplies attainment before any use of pointedness. -/
theorem finite_infimum_optimizer {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Coordinate n) (p : ℝ)
    (hne : (polyhedron A b).Nonempty) (hp : objectiveInfimum A b c = (p : EReal)) :
    ∃ x ∈ polyhedron A b, c ⬝ᵥ x = p ∧
      ∀ y ∈ polyhedron A b, c ⬝ᵥ x ≤ c ⬝ᵥ y := by
  let P := inequalityProblem A b c
  have hvalue : P205.LinearProgramming.StandardForm.infimum P = (p : EReal) :=
    (inequalityProblem_infimum A b c).trans hp
  obtain ⟨x₀, hx₀⟩ := hne
  have hfeas : P205.LinearProgramming.StandardForm.feasible P x₀ :=
    (inequalityProblem_feasible A b c x₀).mpr hx₀
  obtain ⟨q, r, hq, _, hqp, _⟩ :=
    P205.LinearProgramming.Certificates.finite_infimum_attained
      (P205.LinearProgramming.StandardForm.standardMatrix P)
      (P205.LinearProgramming.StandardForm.standardBound P)
      (P205.LinearProgramming.StandardForm.standardCost P) p
      ⟨_, P205.LinearProgramming.StandardForm.lift_feasible P x₀ hfeas⟩
      ((P205.LinearProgramming.StandardForm.infimum_preserved P).symm.trans hvalue)
  obtain ⟨x, hx, hxp⟩ :=
    (P205.LinearProgramming.StandardForm.attainment_correspondence P p).mpr ⟨q, hq, hqp⟩
  refine ⟨x, (inequalityProblem_feasible A b c x).mp hx.1, hxp, ?_⟩
  intro y hy
  exact hx.2 y ((inequalityProblem_feasible A b c y).mpr hy)

theorem finite_infimum_vertex : VertexOptimumSpecs.finite_infimum_vertex := by
  intro m n A b c p hne hpoint hp
  obtain ⟨x₀, hx₀, hxp, hopt⟩ := finite_infimum_optimizer A b c p hne hp
  obtain ⟨x, hx, hxx, hmin⟩ := vertex_optimizer_of_optimizer A b c hpoint x₀ hx₀ hopt
  exact ⟨x, hx, hxx.trans hxp, hmin⟩

/-- Objective negation exchanges extended infimum and supremum, including infinities. -/
lemma objectiveInfimum_neg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Coordinate n) :
    objectiveInfimum A b (-c) = -objectiveSupremum A b c := by
  let S := (fun x : Coordinate n => ((c ⬝ᵥ x : ℝ) : EReal)) '' polyhedron A b
  have himage : (fun x : Coordinate n => (((-c) ⬝ᵥ x : ℝ) : EReal)) '' polyhedron A b
      = Neg.neg '' S := by
    rw [Set.image_image]
    congr 1
    funext x
    simp only [neg_dotProduct, EReal.coe_neg]
  unfold objectiveInfimum objectiveSupremum
  rw [himage]
  have h := (EReal.negOrderIso.map_sSup S).symm
  change (⨅ a ∈ S, -a) = -sSup S at h
  simpa only [sInf_image] using h

theorem finite_supremum_vertex : VertexOptimumSpecs.finite_supremum_vertex := by
  intro m n A b c p hne hpoint hp
  have hneg : objectiveInfimum A b (-c) = ((-p : ℝ) : EReal) := by
    rw [objectiveInfimum_neg, hp, EReal.coe_neg]
  obtain ⟨x, hx, hxp, hopt⟩ := finite_infimum_vertex A b (-c) (-p) hne hpoint hneg
  simp only [neg_dotProduct, neg_inj] at hxp
  refine ⟨x, hx, hxp, ?_⟩
  intro y hy
  simpa only [neg_dotProduct, neg_le_neg_iff] using hopt y hy

end P205.Polyhedra
