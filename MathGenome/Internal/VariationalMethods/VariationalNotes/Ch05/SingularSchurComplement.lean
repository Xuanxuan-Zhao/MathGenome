import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ConjugateQuadratic
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.SingularSchurComplement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped InnerProductSpace
open Matrix
universe u
namespace VariationalNotes.Ch05.SingularSchurComplement

def schurBlock {n : Type u} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (t : ℝ) (w : EuclideanSpace ℝ n) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ := Specs.schurBlock R t w

theorem pseudoinverse_conventions : Specs.pseudoinverse_conventions.{u} := by
  intro n _ _ R hR
  exact ⟨ConvexAnalysis.quadratic_range_kernel R hR,
    ConvexAnalysis.quadratic_pseudoinverse_conventions R hR⟩

theorem pseudoinverse_symmetric : Specs.pseudoinverse_symmetric.{u} := by
  intro n _ _ R hR
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hR
  have hc := ConvexAnalysis.quadratic_pseudoinverse_conventions R hR
  have hrange := ConvexAnalysis.quadratic_range_kernel R hR
  intro x y
  obtain ⟨kx, hkx, rx, hrx, hx⟩ :=
    R.toEuclideanLin.ker.exists_add_mem_mem_orthogonal x
  obtain ⟨ky, hky, ry, hry, hy⟩ :=
    R.toEuclideanLin.ker.exists_add_mem_mem_orthogonal y
  have hpx := hc.1 rx
  have hpy := hc.1 ry
  have hx0 : inner ℝ ((ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin rx)
      ky = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hky hpx
  have hy0 : inner ℝ kx
      ((ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin ry) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hkx hpy
  have htx := hc.2.1 rx (hrange.symm ▸ hrx)
  have hty := hc.2.1 ry (hrange.symm ▸ hry)
  rw [hx, hy, map_add, map_add, hc.2.2.2 kx hkx, hc.2.2.2 ky hky,
    zero_add, zero_add, inner_add_left, inner_add_right, hx0, hy0, zero_add, zero_add]
  simpa only [htx, hty] using
    (hT ((ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin rx)
      ((ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin ry)).symm

theorem pseudoinverse_coordinates : Specs.pseudoinverse_coordinates.{u} := by
  intro n _ _ R w
  simp [PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, RCLike.inner_apply, mul_comm]

lemma inner_matrix {n : Type u} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    inner ℝ x (R.toEuclideanLin y) = dotProduct (⇑x) (R.mulVec (⇑y)) := by
  simp [PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, RCLike.inner_apply, mul_comm]

lemma block_quadratic {n : Type u} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (t r : ℝ) (w v : EuclideanSpace ℝ n) :
    let x : Unit ⊕ n → ℝ := Sum.elim (fun _ => r) (⇑v)
    x ⬝ᵥ (Specs.schurBlock R t w *ᵥ x) =
      r ^ 2 * t + 2 * r * inner ℝ w v + inner ℝ v (R.toEuclideanLin v) := by
  dsimp only
  rw [inner_matrix]
  simp only [Specs.schurBlock, dotProduct, Matrix.mulVec,
    Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr]
  simp only [Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf
  have he : (∑ i, r * w i * v i) = ∑ i, r * v i * w i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, ← Finset.sum_mul]
  ring

lemma block_hermitian {n : Type u} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (hR : R.IsHermitian) (t : ℝ) (w : EuclideanSpace ℝ n) :
    (Specs.schurBlock R t w).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  funext i j
  cases i <;> cases j <;> simp [Specs.schurBlock, Matrix.fromBlocks]
  exact congrFun (congrFun hR _) _

/-- The block form as a scalar quadratic plus a translated PSD form. -/
lemma complete_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (w z : E) (hz : T z = w)
    (t r : ℝ) (v : E) :
    r ^ 2 * t + 2 * r * inner ℝ w v + inner ℝ v (T v) =
      r ^ 2 * (t - inner ℝ w z) + inner ℝ (v + r • z) (T (v + r • z)) := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial]
  rw [← hT z v, hz, real_inner_comm v w, real_inner_comm z w]
  ring

/-- A nonnegative affine function on the entire real line is constant. -/
lemma affine_nonneg_slope_zero (t a : ℝ) (h : ∀ s : ℝ, 0 ≤ t + 2 * s * a) :
    a = 0 := by
  by_contra ha
  have he : 2 * (-(t + 1) / (2 * a)) * a = -(t + 1) := by
    field_simp
  have hn := h (-(t + 1) / (2 * a))
  rw [he] at hn
  linarith

lemma block_posSemidef_iff {n : Type u} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (hR : R.IsHermitian) (t : ℝ) (w : EuclideanSpace ℝ n) :
    (Specs.schurBlock R t w).PosSemidef ↔
      ∀ (r : ℝ) (v : EuclideanSpace ℝ n),
        0 ≤ r ^ 2 * t + 2 * r * inner ℝ w v + inner ℝ v (R.toEuclideanLin v) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h r v
    rw [← block_quadratic]
    simpa only [star_trivial] using h.2 (Sum.elim (fun _ => r) (⇑v))
  · intro h
    refine ⟨block_hermitian R hR t w, ?_⟩
    intro x
    let v : EuclideanSpace ℝ n := WithLp.toLp 2 (fun i => x (Sum.inr i))
    have hx : Sum.elim (fun _ : Unit => x (Sum.inl ())) (⇑v) = x := by
      funext i
      cases i with
      | inl i => cases i; rfl
      | inr i => rfl
    have hn := h (x (Sum.inl ())) v
    rw [← block_quadratic, hx] at hn
    simpa only [star_trivial] using hn

lemma block_range {n : Type u} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (hR : R.IsHermitian) (t : ℝ) (w : EuclideanSpace ℝ n)
    (h : ∀ (r : ℝ) (v : EuclideanSpace ℝ n),
      0 ≤ r ^ 2 * t + 2 * r * inner ℝ w v + inner ℝ v (R.toEuclideanLin v)) :
    w ∈ R.toEuclideanLin.range := by
  rw [ConvexAnalysis.quadratic_range_kernel R hR, Submodule.mem_orthogonal]
  intro k hk
  rw [real_inner_comm]
  apply affine_nonneg_slope_zero t
  intro s
  have hk' : R.toEuclideanLin k = 0 := hk
  have hn := h 1 (s • k)
  simpa [map_smul, hk', inner_smul_right, mul_assoc] using hn

theorem singular_schur : Specs.singular_schur.{u} := by
  intro n _ _ R hR t w
  rw [block_posSemidef_iff R hR.isHermitian]
  let z := (ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin w
  have hT := Matrix.isPositive_toEuclideanLin_iff.mpr hR
  have hc := ConvexAnalysis.quadratic_pseudoinverse_conventions R hR.isHermitian
  constructor
  · intro h
    have hw := block_range R hR.isHermitian t w h
    have hz : R.toEuclideanLin z = w := hc.2.1 w hw
    refine ⟨hw, ?_⟩
    have hn := h 1 (-z)
    rw [complete_square _ hT.isSymmetric w z hz] at hn
    simpa using hn
  · rintro ⟨hw, ht⟩
    have hz : R.toEuclideanLin z = w := hc.2.1 w hw
    intro r v
    rw [complete_square _ hT.isSymmetric w z hz]
    exact add_nonneg (mul_nonneg (sq_nonneg r) (sub_nonneg.mpr ht))
      (hT.inner_nonneg_right _)

end VariationalNotes.Ch05.SingularSchurComplement
