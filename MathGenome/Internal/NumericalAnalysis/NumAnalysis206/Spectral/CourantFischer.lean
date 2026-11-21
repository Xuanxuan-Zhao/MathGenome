import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.CourantFischer
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators ComplexConjugate
namespace NumAnalysis206.CourantFischer
open MatrixData CourantFischerDefinitions

section Coordinates
variable {K E ι : Type*} [RCLike K] [NormedAddCommGroup E]
  [InnerProductSpace K E] [Fintype ι]

/-- Parseval expansion of a diagonal self-adjoint quadratic form. -/
lemma rayleigh_expansion (b : OrthonormalBasis ι K E) (T : E →ₗ[K] E)
    (hT : T.IsSymmetric) (μ : ι → ℝ)
    (hb : ∀ j, T (b j) = (μ j : K) • b j) (x : E) :
    RCLike.re (inner K x (T x)) = ∑ j, μ j * ‖inner K (b j) x‖ ^ 2 := by
  rw [← b.sum_inner_mul_inner x (T x), map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hT, hb, inner_smul_left, RCLike.conj_ofReal]
  rw [mul_left_comm, RCLike.re_ofReal_mul, inner_mul_symm_re_eq_norm]
  rw [norm_mul, norm_inner_symm x (b j)]
  ring

/-- The coordinates outside a selected basis span vanish. -/
lemma inner_eq_zero_of_mem_span (b : OrthonormalBasis ι K E) (s : Set ι)
    {x : E} (hx : x ∈ Submodule.span K (b '' s)) {j : ι} (hj : j ∉ s) :
    inner K (b j) x = 0 := by
  have hx' : x ∈ Submodule.span K (b.toBasis '' s) := hx
  have hs := b.toBasis.repr_support_subset_of_mem_span s hx'
  have hz : b.toBasis.repr x j = 0 := by
    by_contra hn
    exact hj (hs (Finsupp.mem_support_iff.mpr hn))
  simpa only [b.coe_toBasis_repr_apply, b.repr_apply_apply] using hz

lemma finrank_basis_span (b : OrthonormalBasis ι K E) (s : Finset ι) :
    Module.finrank K (Submodule.span K (b '' (s : Set ι))) = s.card := by
  classical
  rw [Set.image_eq_range]
  simpa [Function.comp_def] using
    (finrank_span_eq_card (b.orthonormal.linearIndependent.comp
      (fun j : (s : Set ι) => j.val) Subtype.val_injective))

lemma rayleigh_le_on_span (b : OrthonormalBasis ι K E) (T : E →ₗ[K] E)
    (hT : T.IsSymmetric) (μ : ι → ℝ)
    (hb : ∀ j, T (b j) = (μ j : K) • b j) (s : Set ι) (c : ℝ)
    (hc : ∀ j ∈ s, μ j ≤ c) {x : E}
    (hx : x ∈ Submodule.span K (b '' s)) (hn : ‖x‖ = 1) :
    RCLike.re (inner K x (T x)) ≤ c := by
  rw [rayleigh_expansion b T hT μ hb]
  calc
    _ ≤ ∑ j, c * ‖inner K (b j) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ s
      · exact mul_le_mul_of_nonneg_right (hc j hj) (sq_nonneg _)
      · simp [inner_eq_zero_of_mem_span b s hx hj]
    _ = c := by rw [← Finset.mul_sum, b.sum_sq_norm_inner_right, hn]; ring

lemma le_rayleigh_on_span (b : OrthonormalBasis ι K E) (T : E →ₗ[K] E)
    (hT : T.IsSymmetric) (μ : ι → ℝ)
    (hb : ∀ j, T (b j) = (μ j : K) • b j) (s : Set ι) (c : ℝ)
    (hc : ∀ j ∈ s, c ≤ μ j) {x : E}
    (hx : x ∈ Submodule.span K (b '' s)) (hn : ‖x‖ = 1) :
    c ≤ RCLike.re (inner K x (T x)) := by
  rw [rayleigh_expansion b T hT μ hb]
  calc
    c = ∑ j, c * ‖inner K (b j) x‖ ^ 2 := by
      rw [← Finset.mul_sum, b.sum_sq_norm_inner_right, hn]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ s
      · exact mul_le_mul_of_nonneg_right (hc j hj) (sq_nonneg _)
      · simp [inner_eq_zero_of_mem_span b s hx hj]

end Coordinates
section Dimension
variable {K E : Type*} [RCLike K] [NormedAddCommGroup E]
  [InnerProductSpace K E] [FiniteDimensional K E]

omit [FiniteDimensional K E] in
lemma exists_unit_in_subspace (S : Submodule K E) (hS : S ≠ ⊥) :
    ∃ x : E, x ∈ S ∧ ‖x‖ = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  exact ⟨(‖x‖⁻¹ : K) • x, S.smul_mem _ hx, norm_smul_inv_norm hx0⟩

/-- Subspaces whose dimensions sum to more than the ambient dimension
have a unit vector in their intersection. -/
lemma exists_unit_in_intersection (S T : Submodule K E)
    (h : Module.finrank K E < Module.finrank K S + Module.finrank K T) :
    ∃ x : E, x ∈ S ∧ x ∈ T ∧ ‖x‖ = 1 := by
  have hn : S ⊓ T ≠ ⊥ := by
    intro he
    have hd : Disjoint S T := disjoint_iff.mpr he
    exact (not_le_of_gt h) (Submodule.finrank_add_finrank_le_of_disjoint hd)
  obtain ⟨x, hx, hx1⟩ := exists_unit_in_subspace (S ⊓ T) hn
  exact ⟨x, hx.1, hx.2, hx1⟩

end Dimension

/-- The inner maximum and minimum exist on every nonzero subspace. -/
lemma inner_extrema {K : Type*} [RCLike K] {n : ℕ} (A : Mat K n n)
    (S : Submodule K (Vec K n)) (hS : 0 < Module.finrank K S) :
    ∃ a b : ℝ, IsLeast (unitRayleighValues A S) a ∧
      IsGreatest (unitRayleighValues A S) b := by
  let f : S → ℝ := fun x => rayleigh A x
  have hf : Continuous f := RCLike.continuous_re.comp
    (continuous_subtype_val.inner (A.toEuclideanLin.continuous_of_finiteDimensional.comp continuous_subtype_val))
  have hn : S ≠ ⊥ := by
    intro he
    exact (ne_of_gt hS) (Submodule.finrank_eq_zero.mpr he)
  obtain ⟨x, hx, hx1⟩ := exists_unit_in_subspace S hn
  have hne : (Metric.sphere (0 : S) 1).Nonempty :=
    ⟨⟨x, hx⟩, by simpa only [Metric.mem_sphere, dist_zero_right, ← Submodule.norm_coe] using hx1⟩
  have heq : unitRayleighValues A S = f '' Metric.sphere (0 : S) 1 := by
    ext r
    constructor
    · rintro ⟨y, hy, hy1, hyr⟩
      exact ⟨⟨y, hy⟩, by simpa only [Metric.mem_sphere, dist_zero_right, ← Submodule.norm_coe] using hy1, hyr⟩
    · rintro ⟨y, hy1, hyr⟩
      exact ⟨y, y.property, by simpa only [Metric.mem_sphere, dist_zero_right, ← Submodule.norm_coe] using hy1, hyr⟩
  have hc : IsCompact (unitRayleighValues A S) := by
    rw [heq]
    exact (isCompact_sphere (0 : S) 1).image hf
  have hv : (unitRayleighValues A S).Nonempty := heq ▸ hne.image f
  obtain ⟨a, ha⟩ := hc.exists_isLeast hv
  obtain ⟨b, hb⟩ := hc.exists_isGreatest hv
  exact ⟨a, b, ha, hb⟩

section Matrix
variable {K : Type*} [RCLike K] {n : ℕ}

lemma rayleigh_eigenbasis (A : Mat K n n) (hA : A.IsHermitian) (i : Fin n) :
    rayleigh A (eigenbasis A hA i) = eigenvalue A hA i := by
  change RCLike.re (inner K _ (A.toEuclideanLin _)) = _
  rw [eigenbasis_action, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (eigenbasis A hA).norm_eq_one]
  simp

/-- The first i+1 eigenvectors give the minimizing subspace. -/
lemma lower_span_extremizer (A : Mat K n n) (hA : A.IsHermitian) (i : Fin n) :
    ∃ S : Submodule K (Vec K n), Module.finrank K S = i.val + 1 ∧
      IsGreatest (unitRayleighValues A S) (eigenvalue A hA i) := by
  let b := eigenbasis A hA
  let S : Submodule K (Vec K n) := Submodule.span K (b '' Set.Iic i)
  refine ⟨S, ?_, ?_, ?_⟩
  · have h := finrank_basis_span b (Finset.Iic i)
    have he : ((Finset.Iic i : Finset (Fin n)) : Set (Fin n)) = Set.Iic i := by
      ext j; simp
    rw [he, Fin.card_Iic] at h
    exact h
  · exact ⟨b i, Submodule.subset_span ⟨i, by simp, rfl⟩,
      b.norm_eq_one i, rayleigh_eigenbasis A hA i⟩
  · rintro r ⟨x, hx, hx1, rfl⟩
    exact rayleigh_le_on_span b A.toEuclideanLin
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (eigenvalue A hA)
      (eigenbasis_action A hA) (Set.Iic i) (eigenvalue A hA i)
      (fun j hj => eigenvalue_monotone A hA hj) hx hx1

/-- The last n-i eigenvectors give the maximizing subspace. -/
lemma upper_span_extremizer (A : Mat K n n) (hA : A.IsHermitian) (i : Fin n) :
    ∃ S : Submodule K (Vec K n), Module.finrank K S = n - i.val ∧
      IsLeast (unitRayleighValues A S) (eigenvalue A hA i) := by
  let b := eigenbasis A hA
  let S : Submodule K (Vec K n) := Submodule.span K (b '' Set.Ici i)
  refine ⟨S, ?_, ?_, ?_⟩
  · have h := finrank_basis_span b (Finset.Ici i)
    have he : ((Finset.Ici i : Finset (Fin n)) : Set (Fin n)) = Set.Ici i := by
      ext j; simp
    rw [he, Fin.card_Ici] at h
    exact h
  · exact ⟨b i, Submodule.subset_span ⟨i, by simp, rfl⟩,
      b.norm_eq_one i, rayleigh_eigenbasis A hA i⟩
  · rintro r ⟨x, hx, hx1, rfl⟩
    exact le_rayleigh_on_span b A.toEuclideanLin
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (eigenvalue A hA)
      (eigenbasis_action A hA) (Set.Ici i) (eigenvalue A hA i)
      (fun j hj => eigenvalue_monotone A hA hj) hx hx1

/-- Every (i+1)-dimensional subspace has a unit vector with Rayleigh
value at least the indexed eigenvalue. -/
lemma exists_rayleigh_ge (A : Mat K n n) (hA : A.IsHermitian) (i : Fin n)
    (S : Submodule K (Vec K n)) (hS : Module.finrank K S = i.val + 1) :
    ∃ x : Vec K n, x ∈ S ∧ ‖x‖ = 1 ∧ eigenvalue A hA i ≤ rayleigh A x := by
  let b := eigenbasis A hA
  let T : Submodule K (Vec K n) := Submodule.span K (b '' Set.Ici i)
  have hT : Module.finrank K T = n - i.val := by
    have h := finrank_basis_span b (Finset.Ici i)
    have he : ((Finset.Ici i : Finset (Fin n)) : Set (Fin n)) = Set.Ici i := by
      ext j; simp
    rw [he, Fin.card_Ici] at h
    exact h
  have hd : Module.finrank K (Vec K n) < Module.finrank K S + Module.finrank K T := by
    rw [finrank_euclideanSpace_fin, hS, hT]
    have := i.isLt
    omega
  obtain ⟨x, hxS, hxT, hx1⟩ := exists_unit_in_intersection S T hd
  refine ⟨x, hxS, hx1, ?_⟩
  exact le_rayleigh_on_span b A.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (eigenvalue A hA)
    (eigenbasis_action A hA) (Set.Ici i) (eigenvalue A hA i)
    (fun j hj => eigenvalue_monotone A hA hj) hxT hx1

/-- Every (n-i)-dimensional subspace has a unit vector with Rayleigh
value at most the indexed eigenvalue. -/
lemma exists_rayleigh_le (A : Mat K n n) (hA : A.IsHermitian) (i : Fin n)
    (S : Submodule K (Vec K n)) (hS : Module.finrank K S = n - i.val) :
    ∃ x : Vec K n, x ∈ S ∧ ‖x‖ = 1 ∧ rayleigh A x ≤ eigenvalue A hA i := by
  let b := eigenbasis A hA
  let T : Submodule K (Vec K n) := Submodule.span K (b '' Set.Iic i)
  have hT : Module.finrank K T = i.val + 1 := by
    have h := finrank_basis_span b (Finset.Iic i)
    have he : ((Finset.Iic i : Finset (Fin n)) : Set (Fin n)) = Set.Iic i := by
      ext j; simp
    rw [he, Fin.card_Iic] at h
    exact h
  have hd : Module.finrank K (Vec K n) < Module.finrank K S + Module.finrank K T := by
    rw [finrank_euclideanSpace_fin, hS, hT]
    have := i.isLt
    omega
  obtain ⟨x, hxS, hxT, hx1⟩ := exists_unit_in_intersection S T hd
  refine ⟨x, hxS, hx1, ?_⟩
  exact rayleigh_le_on_span b A.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (eigenvalue A hA)
    (eigenbasis_action A hA) (Set.Iic i) (eigenvalue A hA i)
    (fun j hj => eigenvalue_monotone A hA hj) hxT hx1

end Matrix

/-- Both attained Courant--Fischer formulas in the source's increasing order. -/
theorem courant_fischer : Specs.NumAnalysis206.CourantFischer.courant_fischer := by
  intro K _ n A hA i
  refine ⟨inner_extrema A, ⟨lower_span_extremizer A hA i, ?_⟩,
    ⟨upper_span_extremizer A hA i, ?_⟩⟩
  · rintro r ⟨S, hS, hr⟩
    obtain ⟨x, hx, hx1, hbound⟩ := exists_rayleigh_ge A hA i S hS
    exact hbound.trans (hr.2 ⟨x, hx, hx1, rfl⟩)
  · rintro r ⟨S, hS, hr⟩
    obtain ⟨x, hx, hx1, hbound⟩ := exists_rayleigh_le A hA i S hS
    exact (hr.2 ⟨x, hx, hx1, rfl⟩).trans hbound

end NumAnalysis206.CourantFischer
