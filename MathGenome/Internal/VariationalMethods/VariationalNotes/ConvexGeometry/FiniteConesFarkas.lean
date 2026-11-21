import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.FiniteConesFarkas
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Foundations
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolyhedraElimination
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Set
noncomputable section
universe u v w
namespace VariationalNotes.ConvexGeometry

/-- The nonnegative orthant is a finite intersection of linear halfspaces. -/
lemma polyhedron_nonnegative {ι : Type u} [Fintype ι] :
    IsPolyhedron {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
  classical
  refine ⟨Finset.univ.image (fun i =>
    (-(LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).toAffineMap), ?_⟩
  ext x
  simp

/-- A finite conic hull is the linear image of the nonnegative orthant. -/
theorem finite_conicHull_eq : Specs.finite_conicHull_eq.{u,v} := by
  intro ι _ E _ _ a
  classical
  let f := Fintype.linearCombination ℝ a
  let K := (PointedCone.positive ℝ (ι → ℝ)).map f
  have hK : PointedCone.hull ℝ (range a) = K := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, ?_, ?_⟩
      · change 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ)
        intro j
        simp only [Pi.single_apply]
        split <;> norm_num
      · simp [f]
    · rintro z ⟨c, hc, rfl⟩
      change (∑ i, c i • a i) ∈ PointedCone.hull ℝ (range a)
      exact Submodule.sum_mem _ fun i _ =>
        PointedCone.smul_mem _ (hc i) (PointedCone.subset_hull (mem_range_self i))
  change (PointedCone.hull ℝ (range a) : Set E) = _
  rw [hK]
  rfl

theorem finite_conicHull_isClosed : Specs.finite_conicHull_isClosed.{u,v} := by
  intro ι _ E _ _ _ _ _ _ _ a
  rw [finite_conicHull_eq a]
  have h := polyhedron_affine_image_isClosed
    (Fintype.linearCombination ℝ a).toAffineMap _ (polyhedron_nonnegative (ι := ι))
  exact h

/-- Evaluation of a functional on standard coordinates, including the empty basis. -/
lemma functional_eq_dotProduct {m : Type u} [Fintype m]
    [DecidableEq m] (f : (m → ℝ) →ₗ[ℝ] ℝ) (z : m → ℝ) :
    f z = dotProduct z (fun i => f (Pi.single i 1)) := by
  classical
  have hz : z = ∑ i, z i • (Pi.single i 1 : m → ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hz]
  simp [dotProduct]

lemma sum_columns_eq_mulVec {m : Type u} {n : Type v} [Fintype n]
    (A : Matrix m n ℝ) (x : n → ℝ) :
    (∑ i, x i • (fun j => A j i)) = A.mulVec x := by
  ext j
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Primal feasibility and the negative dual certificate are incompatible. -/
lemma farkas_exclusive {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ)
    (hp : ∃ x : n → ℝ, 0 ≤ x ∧ A.mulVec x = b)
    (hd : ∃ y : m → ℝ, 0 ≤ A.transpose.mulVec y ∧ dotProduct b y < 0) : False := by
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, hneg⟩ := hd
  have hnonneg : 0 ≤ dotProduct x (A.transpose.mulVec y) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hx i) (hy i)
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm] at hnonneg
  exact (not_lt_of_ge hnonneg) hneg

/-- Farkas' alternative, with componentwise inequalities and no dimension restrictions. -/
theorem farkas_alternative : Specs.farkas_alternative.{u,v} := by
  intro m n _ _ A b
  classical
  by_cases hp : ∃ x : n → ℝ, 0 ≤ x ∧ A.mulVec x = b
  · exact Or.inl ⟨hp, farkas_exclusive A b hp⟩
  · apply Or.inr
    refine ⟨?_, hp⟩
    let a : n → (m → ℝ) := fun i j => A j i
    let C : ProperCone ℝ (m → ℝ) :=
      ⟨PointedCone.hull ℝ (range a), finite_conicHull_isClosed a⟩
    have hb : b ∉ C := by
      intro hb
      change b ∈ Specs.conicHull (range a) at hb
      rw [finite_conicHull_eq a] at hb
      obtain ⟨x, hx, hxb⟩ := hb
      exact hp ⟨x, hx, (sum_columns_eq_mulVec A x).symm.trans hxb⟩
    obtain ⟨f, hfC, hfb⟩ := C.hyperplane_separation_point hb
    refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
    · intro i
      change 0 ≤ dotProduct (a i) (fun j => f (Pi.single j 1))
      calc
        0 ≤ f.toLinearMap (a i) :=
          hfC _ (PointedCone.subset_hull (mem_range_self i))
        _ = _ := functional_eq_dotProduct f.toLinearMap (a i)
    · change f.toLinearMap b < 0 at hfb
      rwa [functional_eq_dotProduct f.toLinearMap] at hfb

/-- Taking coordinates commutes with the finite linear combination. -/
lemma basis_sum_eq_mulVec {ι : Type u} {κ : Type w} [Fintype ι] [Fintype κ]
    {E : Type v} [AddCommGroup E] [Module ℝ E]
    (e : Module.Basis κ ℝ E) (a : ι → E) (x : ι → ℝ) :
    (fun k => e.repr (∑ i, x i • a i) k) =
      Matrix.mulVec (fun k i => e.repr (a i) k) x := by
  ext k
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem basis_conic_feasibility : Specs.basis_conic_feasibility.{u,v,w} := by
  intro ι κ _ _ E _ _ e a b
  have heq (x : ι → ℝ) : (∑ i, x i • a i) = b ↔
      Matrix.mulVec (fun k i => e.repr (a i) k) x = fun k => e.repr b k := by
    rw [← basis_sum_eq_mulVec]
    constructor
    · rintro rfl
      rfl
    · intro h
      apply e.repr.injective
      exact Finsupp.ext (congrFun h)
  simp_rw [heq]

theorem farkas_in_basis : Specs.farkas_in_basis.{u,v,w} := by
  intro ι κ _ _ E _ _ e a b
  rw [basis_conic_feasibility e a b]
  exact farkas_alternative _ _

end VariationalNotes.ConvexGeometry
