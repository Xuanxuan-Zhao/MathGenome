import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Gordan
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Separation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Matrix

universe w u v

namespace VariationalNotes.ConvexGeometry

private theorem negative_weighted_sum {m : Type u} [Fintype m]
    {μ x : m → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hne : μ ≠ 0)
    (hx : ∀ i, x i < 0) : ∑ i, μ i * x i < 0 := by
  classical
  have hex : ∃ i, μ i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  have h := Finset.sum_lt_sum (s := Finset.univ)
    (f := fun j => μ j * x j) (g := fun _ => (0 : ℝ))
    (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμ j) (hx j).le)
    ⟨i, Finset.mem_univ i, mul_neg_of_pos_of_neg (lt_of_le_of_ne (hμ i) (Ne.symm hi)) (hx i)⟩
  simpa using h

/-- Separation of the open negative orthant from the image of a linear map. -/
theorem gordan_linearMap : Specs.gordan_linearMap.{w, u} := by
  intro E _ _ m _ T
  classical
  have hexclusive : ¬ ((∃ d, ∀ i, T d i < 0) ∧
      (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧
        ∀ d : E, ∑ i, μ i * T d i = 0)) := by
    rintro ⟨⟨d, hd⟩, μ, hμ, hne, hz⟩
    have := negative_weighted_sum hμ hne hd
    rw [hz d] at this
    exact (lt_irrefl 0) this
  refine ⟨?_, hexclusive⟩
  by_cases hstrict : ∃ d, ∀ i, T d i < 0
  · exact Or.inl hstrict
  right
  let A : Set (m → ℝ) := {x | ∀ i, x i < 0}
  have hAc : Convex ℝ A := by
    simpa [A, Set.pi] using
      (convex_pi (𝕜 := ℝ) (s := Set.univ) (t := fun _ : m => Set.Iio (0 : ℝ))
        fun _ _ => convex_Iio (0 : ℝ))
  have hAo : IsOpen A := by
    have heq : A = ⋂ i, {x : m → ℝ | x i < 0} := by ext x; simp [A]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  have hdis : Disjoint A (LinearMap.range T : Set (m → ℝ)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨d, rfl⟩
    exact hstrict ⟨d, hx⟩
  obtain ⟨l, α, hl, hA, hT⟩ := open_separation
    A (LinearMap.range T : Set (m → ℝ))
    ⟨fun _ => -1, by intro i; norm_num⟩
    ⟨0, Submodule.zero_mem _⟩ hAc (LinearMap.range T).convex hdis hAo
  have hvanish : ∀ d, l (T d) = 0 := by
    intro d
    by_contra hne
    have h := hT (T (((α - 1) / l (T d)) • d)) ⟨_, rfl⟩
    rw [map_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
    linarith
  let μ : m → ℝ := fun i => l (Pi.single i 1)
  have hrepr : ∀ x, l x = ∑ i, μ i * x i := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Pi.single i (x i) = x i • Pi.single i (1 : ℝ) by
      ext j
      by_cases h : j = i <;> simp [h]]
    simp [μ, mul_comm]
  have hμ : ∀ i, 0 ≤ μ i := by
    intro i
    by_contra h
    have hi : μ i < 0 := lt_of_not_ge h
    let z : m → ℝ := fun _ => -1
    have hz : l z < α := hA z (by intro j; norm_num [z])
    let t : ℝ := (l z - α) / μ i
    have ht : 0 ≤ t := le_of_lt (div_pos_of_neg_of_neg (sub_neg.mpr hz) hi)
    have hx : z - t • Pi.single i (1 : ℝ) ∈ A := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, z]
        linarith
      · simp [Pi.single_eq_of_ne hji, z]
    have hv := hA _ hx
    rw [map_sub, map_smul, smul_eq_mul] at hv
    change l z - t * μ i < α at hv
    dsimp [t] at hv
    rw [div_mul_cancel₀ _ (ne_of_lt hi)] at hv
    linarith
  have hμne : μ ≠ 0 := by
    intro hzero
    apply hl
    ext x
    rw [hrepr x, hzero]
    simp
  exact ⟨μ, hμ, hμne, fun d => (hrepr (T d)).symm.trans (hvanish d)⟩

/-- The manuscript's matrix form, including empty matrices. -/
theorem gordan_alternative : Specs.gordan_alternative.{u, v} := by
  intro m n _ _ B
  classical
  have hcert : (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧
      ∀ d : n → ℝ, ∑ i, μ i * (B *ᵥ d) i = 0) ↔
      (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧ Bᵀ *ᵥ μ = 0) := by
    constructor
    · rintro ⟨μ, hμ, hne, hz⟩
      refine ⟨μ, hμ, hne, ?_⟩
      rw [Matrix.mulVec_transpose]
      apply dotProduct_eq_zero
      intro d
      rw [← Matrix.dotProduct_mulVec]
      exact hz d
    · rintro ⟨μ, hμ, hne, hz⟩
      refine ⟨μ, hμ, hne, ?_⟩
      intro d
      change μ ⬝ᵥ (B *ᵥ d) = 0
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hz, zero_dotProduct]
  simpa only [Matrix.mulVecLin_apply, hcert] using (gordan_linearMap B.mulVecLin)

/-- A finite basis supplies the coordinate matrix of the restriction to a
subspace; the alternative thus applies without ambient full dimensionality. -/
theorem gordan_subspace : Specs.gordan_subspace.{w, u} := by
  intro E _ _ S _ m _ T
  dsimp only
  let b := Module.finBasis ℝ S
  refine ⟨?_, gordan_linearMap (T.comp S.subtype)⟩
  intro d
  change (fun i j => T (b j) i) *ᵥ (fun j => b.repr d j) = T d
  have hd := congrArg (T.comp S.subtype) (b.sum_repr d)
  simp only [map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply] at hd
  ext i
  have hi := congrFun hd i
  simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm] using hi

end VariationalNotes.ConvexGeometry
