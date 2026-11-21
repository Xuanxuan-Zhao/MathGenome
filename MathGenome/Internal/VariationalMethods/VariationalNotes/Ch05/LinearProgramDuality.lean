import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramDuality
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.LinearProgramAttainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolyhedralTangentNormal
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Set Matrix
open WithLp
universe u v
namespace VariationalNotes.Ch05.LinearProgramDuality
open VariationalNotes.Ch05.LinearProgramModels
open VariationalNotes.ConvexGeometry

/-- At a primal minimizer the polyhedral normal formula produces a dual
feasible vector with the same objective value. -/
lemma dual_witness_of_primalOptimal {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ) (c x : n → ℝ)
    (hx : PrimalOptimal A b c x) :
    ∃ y, dualFeasible A c y ∧ dualObjective b y = primalObjective c x := by
  classical
  let a : n → EuclideanSpace ℝ n := fun i => -EuclideanSpace.single i 1
  let e : m → EuclideanSpace ℝ n := fun j => toLp 2 (A j)
  let X : EuclideanSpace ℝ n := toLp 2 x
  let C : EuclideanSpace ℝ n := toLp 2 c
  have ha (i : n) (z : EuclideanSpace ℝ n) : inner ℝ (a i) z = -z i := by
    simp [a, inner_neg_left, EuclideanSpace.inner_single_left]
  have he (j : m) (z : EuclideanSpace ℝ n) : inner ℝ (e j) z = (A *ᵥ ofLp z) j := by
    simp [e, EuclideanSpace.inner_eq_star_dotProduct,
      mulVec, dotProduct_comm]
  have hfeas (z : EuclideanSpace ℝ n) :
      z ∈ polyhedralSet a (fun _ => 0) e b ↔ primalFeasible A b (ofLp z) := by
    change ((∀ i, inner ℝ (a i) z ≤ 0) ∧ (∀ j, inner ℝ (e j) z = b j)) ↔ _
    simp only [ha, he]
    change ((∀ i, -z i ≤ 0) ∧ (∀ j, (A *ᵥ ofLp z) j = b j)) ↔
      (A *ᵥ ofLp z = b ∧ ∀ i, 0 ≤ z i)
    simp only [neg_nonpos, funext_iff, and_comm]
  have hX : X ∈ polyhedralSet a (fun _ => 0) e b := (hfeas X).mpr hx.1
  have hnormal : -C ∈ (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) ⁻¹'
      VariationalNotes.ConvexGeometry.Specs.normalCone
        (VariationalNotes.ConvexGeometry.Specs.polyhedralSet a (fun _ => 0) e b) X := by
    intro z hz
    have hmin := ((primalOptimal_iff A b c x).mp hx).2 (ofLp z) ((hfeas z).mp hz)
    change inner ℝ (-C) (z - X) ≤ 0
    rw [inner_neg_left, inner_sub_right]
    have hc (w : EuclideanSpace ℝ n) : inner ℝ C w = primalObjective c (ofLp w) := by
      simp [C, primalObjective, LinearProgramModels.Specs.primalObjective,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rw [hc, hc]
    exact neg_nonpos.mpr (sub_nonneg.mpr hmin)
  rw [polyhedral_normal a (fun _ => 0) e b X hX] at hnormal
  obtain ⟨lam, nu, hlam, hrep⟩ := hnormal
  let y : m → ℝ := -nu
  refine ⟨y, ?_, ?_⟩
  · intro i
    have hcoord := congrArg (fun z : EuclideanSpace ℝ n => inner ℝ z (EuclideanSpace.single i 1)) hrep
    have hnonpos : (∑ k : {k // inner ℝ (a k) X = 0},
        inner ℝ (lam k • a k.val) (EuclideanSpace.single i 1)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      rw [real_inner_smul_left, ha]
      apply mul_nonpos_of_nonneg_of_nonpos (hlam k)
      simp only [EuclideanSpace.single, PiLp.single_apply]
      split <;> norm_num
    have hrow : (∑ j, inner ℝ (nu j • e j) (EuclideanSpace.single i 1)) =
        (Aᵀ *ᵥ nu) i := by
      simp [EuclideanSpace.inner_single_right, e,
        mulVec, dotProduct, mul_comm]
    rw [inner_add_left, sum_inner, sum_inner, hrow] at hcoord
    have hleft : inner ℝ (-C) (EuclideanSpace.single i 1) = -c i := by
      simp [C, EuclideanSpace.inner_single_right]
    rw [hleft] at hcoord
    change (Aᵀ *ᵥ (-nu)) i ≤ c i
    rw [mulVec_neg]
    change -(Aᵀ *ᵥ nu) i ≤ c i
    linarith
  · have hobj := congrArg (fun z : EuclideanSpace ℝ n => inner ℝ z X) hrep
    have hactive : (∑ k : {k // inner ℝ (a k) X = 0}, inner ℝ (lam k • a k.val) X) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [real_inner_smul_left, k.property, mul_zero]
    have hrow : (∑ j, inner ℝ (nu j • e j) X) = b ⬝ᵥ nu := by
      simp only [real_inner_smul_left, he]
      change (∑ j, nu j * (A *ᵥ x) j) = b ⬝ᵥ nu
      rw [hx.1.1]
      simp only [dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    rw [inner_add_left, sum_inner, sum_inner, hactive, zero_add, hrow] at hobj
    have hleft : inner ℝ (-C) X = -(c ⬝ᵥ x) := by
      simp [C, X, inner_neg_left, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rw [hleft] at hobj
    change b ⬝ᵥ (-nu) = c ⬝ᵥ x
    rw [dotProduct_neg]
    linarith

theorem feasible_pair_gap : Specs.feasible_pair_gap.{u,v} := by
  intro m n _ _ A b c x y hx _
  exact gap_identity A b c x y hx

theorem gap_zero_iff_complementarity : Specs.gap_zero_iff_complementarity.{u,v} := by
  intro m n _ _ A b c x y hx hy
  exact gap_eq_zero_iff A b c x y hx hy

theorem zero_gap_certificate : Specs.zero_gap_certificate.{u,v} := by
  intro m n _ _ A b c x y hx hy hgap
  have heq : primalObjective c x = dualObjective b y := sub_eq_zero.mp hgap
  constructor
  · apply (primalOptimal_iff A b c x).mpr
    refine ⟨hx, fun z hz => ?_⟩
    change primalObjective c x ≤ primalObjective c z
    rw [heq]
    exact weakDuality A b c z y hz hy
  · apply (dualOptimal_iff A b c y).mpr
    refine ⟨hy, fun z hz => ?_⟩
    change dualObjective b z ≤ dualObjective b y
    rw [← heq]
    exact weakDuality A b c x z hx hz

theorem strong_duality : Specs.strong_duality.{u,v} := by
  intro m n _ _ A b c p hfeas hp
  obtain hpa := LinearProgramAttainment.primal_attainment A b c p hfeas hp
  obtain ⟨x, hx, hxp⟩ := hpa
  obtain ⟨y, hy, hyx⟩ := dual_witness_of_primalOptimal A b c x hx
  have hcert := zero_gap_certificate A b c x y hx.1 hy (sub_eq_zero.mpr hyx.symm)
  have hda : DualAttains A b c p := ⟨y, hcert.2, hyx.trans hxp⟩
  have hdv := dualAttains_value A b c p hda
  exact ⟨⟨x, hx, hxp⟩, hda, hp.trans hdv.symm, hdv⟩

end VariationalNotes.Ch05.LinearProgramDuality
