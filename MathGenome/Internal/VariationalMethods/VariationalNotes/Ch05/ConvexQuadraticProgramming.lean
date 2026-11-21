import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.ConvexQuadraticProgramming
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.QuadraticProgramAttainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolyhedralTangentNormal
import Mathlib.Tactic.Ring

noncomputable section
open Set Matrix Filter
open scoped Topology
namespace VariationalNotes.Ch05

lemma quadraticObjective_expansion {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsHermitian) (c x v : Fin n → ℝ) (t : ℝ) :
    Specs.quadraticObjective Q c (x + t • v) = Specs.quadraticObjective Q c x +
      t * ((Q *ᵥ x + c) ⬝ᵥ v) + t^2 * (v ⬝ᵥ (Q *ᵥ v)) / 2 := by
  have hsym : x ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ (Q *ᵥ x) := by
    simpa only [star_trivial] using hQ.star_dotProduct_mulVec_comm x v
  simp only [Specs.quadraticObjective, mulVec_add, mulVec_smul,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    hsym, dotProduct_comm (Q *ᵥ x) v]
  ring

/-- A nonnegative polynomial on a right neighborhood of zero has
nonnegative linear coefficient. -/
lemma nonneg_linear_coefficient (A B : ℝ)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t*A + t^2*B) : 0 ≤ A := by
  let t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun k => A + t k * B) atTop (𝓝 A) := by
    simpa using tendsto_const_nhds.add (ht.mul_const B)
  apply ge_of_tendsto hl
  apply Eventually.of_forall
  intro k
  have hp : 0 < t k := by dsimp [t]; positivity
  have h1 : t k ≤ 1 := by
    dsimp [t]
    rw [div_le_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hh := h (t k) hp h1
  have heq : t k*A + t k^2*B = t k * (A + t k*B) := by ring
  rw [heq] at hh
  exact nonneg_of_mul_nonneg_right hh hp

lemma quadratic_optimal_iff_normal_of_convex {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (P : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (hQ : Q.PosSemidef) (hP : Convex ℝ P) (hx : x ∈ P) :
    (∀ y ∈ P, Specs.quadraticObjective Q c x.ofLp ≤ Specs.quadraticObjective Q c y.ofLp) ↔
      InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
        (-(WithLp.toLp 2 (Q *ᵥ x.ofLp + c))) ∈ ConvexGeometry.Specs.normalCone P x := by
  have heval (y : EuclideanSpace ℝ (Fin n)) :
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
        (-(WithLp.toLp 2 (Q *ᵥ x.ofLp + c)))) (y - x) =
      -((Q *ᵥ x.ofLp + c) ⬝ᵥ (y.ofLp - x.ofLp)) := by
    change inner ℝ (-(WithLp.toLp 2 (Q *ᵥ x.ofLp + c)) : EuclideanSpace ℝ (Fin n)) (y - x) = _
    rw [inner_neg_left, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, WithLp.ofLp_sub]
    rw [dotProduct_comm]
  constructor
  · intro hm y hy
    rw [heval]
    apply neg_nonpos.mpr
    apply nonneg_linear_coefficient _ ((y.ofLp - x.ofLp) ⬝ᵥ
      (Q *ᵥ (y.ofLp - x.ofLp)) / 2)
    intro t ht ht1
    have hmem : x + t • (y - x) ∈ P := hP.add_smul_mem hx (by simpa using hy) ⟨ht.le, ht1⟩
    have hh := hm _ hmem
    have hexp := quadraticObjective_expansion Q hQ.isHermitian c x.ofLp (y.ofLp - x.ofLp) t
    change Specs.quadraticObjective Q c x.ofLp ≤
      Specs.quadraticObjective Q c (x.ofLp + t • (y.ofLp - x.ofLp)) at hh
    rw [hexp] at hh
    nlinarith
  · intro hn y hy
    have hn' := hn y hy
    rw [heval] at hn'
    have hpos : 0 ≤ (y.ofLp - x.ofLp) ⬝ᵥ (Q *ᵥ (y.ofLp - x.ofLp)) := by
      simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg (y.ofLp - x.ofLp)
    have hexp := quadraticObjective_expansion Q hQ.isHermitian c x.ofLp (y.ofLp - x.ofLp) 1
    simp only [one_smul, add_sub_cancel, one_mul, one_pow] at hexp
    linarith

lemma convex_of_isPolyhedron {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} (hP : ConvexGeometry.Specs.IsPolyhedron P) : Convex ℝ P := by
  obtain ⟨s, rfl⟩ := hP
  intro x hx y hy u v hu hv huv a ha
  rw [Convex.combo_affine_apply huv]
  calc
    u • a x + v • a y ≤ u • (0 : ℝ) + v • (0 : ℝ) :=
      add_le_add (smul_le_smul_of_nonneg_left (hx a ha) hu)
        (smul_le_smul_of_nonneg_left (hy a ha) hv)
    _ = 0 := by simp

theorem convexQP_attainment : Specs.convexQP_attainment := by
  intro n Q c P p hQ hP hne hp
  let A := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  have hS : ConvexGeometry.Specs.IsPolyhedron (A '' P) :=
    ConvexGeometry.polyhedron_affine_image A.toLinearMap.toAffineMap P hP
  have himage : Specs.quadraticObjective Q c '' (A '' P) =
      (fun x : EuclideanSpace ℝ (Fin n) => Specs.quadraticObjective Q c x.ofLp) '' P := by
    rw [Set.image_image]
    rfl
  obtain ⟨v, hv, hval⟩ := quadraticProgram_attains_infimum n Q c (A '' P) p hQ hS
    (hne.image A) (by rwa [himage])
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨x, hx, hval⟩

theorem convexQP_optimal_iff_normal : Specs.convexQP_optimal_iff_normal := by
  intro n Q c P x hQ hP hx
  exact quadratic_optimal_iff_normal_of_convex Q c P x hQ (convex_of_isPolyhedron hP) hx

/-- Extend the active inequality coefficients by zero. Conversely,
complementarity removes every inactive contribution to the normal. -/
lemma polyhedral_normal_iff_kkt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → E) (b : I → ℝ) (e : J → E) (d : J → ℝ) (x z : E)
    (hx : x ∈ ConvexGeometry.Specs.polyhedralSet a b e d) :
    InnerProductSpace.toDual ℝ E (-z) ∈
        ConvexGeometry.Specs.normalCone (ConvexGeometry.Specs.polyhedralSet a b e d) x ↔
      ∃ (lam : I → ℝ) (nu : J → ℝ), (∀ i, 0 ≤ lam i) ∧
        z + (∑ i, lam i • a i) + (∑ j, nu j • e j) = 0 ∧
        (∀ i, lam i * (inner ℝ (a i) x - b i) = 0) := by
  classical
  constructor
  · intro hn
    have hn' : -z ∈ (InnerProductSpace.toDual ℝ E) ⁻¹'
        ConvexGeometry.Specs.normalCone (ConvexGeometry.Specs.polyhedralSet a b e d) x := hn
    rw [ConvexGeometry.polyhedral_normal a b e d x hx] at hn'
    obtain ⟨mu, nu, hmu, hz⟩ := hn'
    let lam : I → ℝ := fun i => if hi : inner ℝ (a i) x = b i then mu ⟨i, hi⟩ else 0
    have hsum : (∑ i, lam i • a i) =
        ∑ i : {i // inner ℝ (a i) x = b i}, mu i • a i.val := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => inner ℝ (a i) x = b i)
        (fun i => lam i • a i)]
      have hactive : (∑ i : {i // inner ℝ (a i) x = b i}, lam i.val • a i.val) =
          ∑ i : {i // inner ℝ (a i) x = b i}, mu i • a i.val := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [lam, dite_eq_left i.property]
      have hinactive : (∑ i : {i // ¬ inner ℝ (a i) x = b i}, lam i.val • a i.val) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [lam, dite_eq_right i.property, zero_smul]
      rw [hactive, hinactive, add_zero]
    refine ⟨lam, nu, ?_, ?_, ?_⟩
    · intro i
      dsimp [lam]
      split
      · exact hmu _
      · exact le_refl 0
    · calc
        z + (∑ i, lam i • a i) + (∑ j, nu j • e j) =
            z + ((∑ i : {i // inner ℝ (a i) x = b i}, mu i • a i.val) +
              ∑ j, nu j • e j) := by rw [hsum, add_assoc]
        _ = z + -z := by rw [← hz]
        _ = 0 := add_neg_cancel z
    · intro i
      by_cases hi : inner ℝ (a i) x = b i <;> simp [lam, hi]
  · rintro ⟨lam, nu, hlam, hstat, hcomp⟩ y hy
    have hz : -z = (∑ i, lam i • a i) + ∑ j, nu j • e j := by
      apply neg_eq_iff_add_eq_zero.mpr
      simpa only [add_assoc] using hstat
    change inner ℝ (-z) (y - x) ≤ 0
    rw [hz, inner_add_left, sum_inner, sum_inner]
    have hi : (∑ i, inner ℝ (lam i • a i) (y - x)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      rw [real_inner_smul_left, inner_sub_right, mul_sub]
      have hc : lam i * inner ℝ (a i) x = lam i * b i := by
        have := hcomp i
        rw [mul_sub] at this
        linarith
      rw [hc]
      exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left (hy.1 i) (hlam i))
    have hj : (∑ j, inner ℝ (nu j • e j) (y - x)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [real_inner_smul_left, inner_sub_right, hy.2 j, hx.2 j, sub_self]
    linarith

theorem convexQP_normal_iff_kkt : Specs.convexQP_normal_iff_kkt := by
  intro n Q c I J _ _ a b e d x hx
  exact polyhedral_normal_iff_kkt a b e d x (WithLp.toLp 2 (Q *ᵥ x.ofLp + c)) hx

theorem convexQP_optimal_iff_kkt : Specs.convexQP_optimal_iff_kkt := by
  intro n Q c I J _ _ a b e d x hQ hx
  exact (quadratic_optimal_iff_normal_of_convex Q c _ x hQ
    (ConvexGeometry.polyhedralSet_convex a b e d) hx).trans
      (polyhedral_normal_iff_kkt a b e d x (WithLp.toLp 2 (Q *ᵥ x.ofLp + c)) hx)

end VariationalNotes.Ch05
