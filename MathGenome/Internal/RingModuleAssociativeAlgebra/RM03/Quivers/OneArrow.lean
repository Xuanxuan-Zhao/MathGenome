import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.OneArrow
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.ArrowIdealPowers
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.ModuleEquivalence
import Mathlib.Tactic.FinCases

/-! The one-arrow path algebra and its lower triangular matrix action. -/

open scoped Matrix ModuleCat

namespace RM03.OneArrow

open OneArrowSpec Module
open scoped OneArrowSpec

universe w d

private theorem pathAt_bijective : Function.Bijective pathAt := by
  constructor
  · intro i j h
    have hs := congrArg Path.source h
    have ht := congrArg Path.target h
    fin_cases i <;> fin_cases j <;>
      simp_all [pathAt, Path.source, Path.target, Path.vertex, Path.arrow, Path.ofPath]
  · rintro ⟨i, j, p⟩
    cases p with
    | nil =>
      cases i
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    | cons p a =>
      rcases a with ⟨⟨⟩, rfl, rfl⟩
      cases p with
      | nil => exact ⟨2, rfl⟩
      | cons p a => exact (Bool.noConfusion a.property.2)

noncomputable def pathBasis (k : Type w) [Field k] :
    Basis (Fin 3) k (PathAlgebra k Vertex) :=
  (PathAlgebra.basis k Vertex).reindex (Equiv.ofBijective pathAt pathAt_bijective).symm

@[simp] theorem pathBasis_apply {k : Type w} [Field k] (i : Fin 3) :
    pathBasis k i = PathAlgebra.ofPath k (pathAt i) := by
  simp [pathBasis, Equiv.ofBijective]

theorem orderedPathBasis : OrderedPathBasis.{w} :=
  ⟨pathAt_bijective, fun k _ => ⟨pathBasis k, pathBasis_apply⟩⟩

private theorem path_length_lt_two (p : Path Vertex) : p.length < 2 := by
  obtain ⟨i, rfl⟩ := pathAt_bijective.surjective p
  fin_cases i <;> decide

theorem squareZeroAndAdmissible : SquareZeroAndAdmissible.{w} := by
  intro k _
  change PathAlgebra.idealPower (PathAlgebra.arrowIdeal k Vertex) 2 = ⊥ ∧
    PathAlgebra.IsAdmissible (⊥ : TwoSidedIdeal (PathAlgebra k Vertex))
  have hs : PathAlgebra.idealPower (PathAlgebra.arrowIdeal k Vertex) 2 = ⊥ := by
    have hempty : {p : Path Vertex | 2 ≤ p.length} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      exact fun p => Nat.not_le_of_lt (path_length_lt_two p)
    apply TwoSidedIdeal.ext
    intro z
    change z ∈ (PathAlgebra.idealPower (PathAlgebra.arrowIdeal k Vertex) 2 :
      Set (PathAlgebra k Vertex)) ↔ z ∈ (⊥ : TwoSidedIdeal (PathAlgebra k Vertex))
    rw [PathAlgebra.arrowIdeal_power_eq_span 2 (by decide), hempty,
      Set.image_empty, Submodule.span_empty]
    simp
  exact ⟨hs, 2, by decide, by simp [hs], bot_le⟩

section Matrices

variable {k : Type w} [Field k]

private def matrixCoordinates : (Fin 3 → k) ≃ₗ[k] lowerTriangular k where
  toFun f := matrix (f 0) (f 2) (f 1)
  invFun m := ![(m : Matrix (Fin 2) (Fin 2) k) 0 0,
    (m : Matrix (Fin 2) (Fin 2) k) 1 1, (m : Matrix (Fin 2) (Fin 2) k) 1 0]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv m := by
    have hm : (m : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := m.property
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact hm.symm
    · rfl
    · rfl
  map_add' f g := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact (zero_add (0 : k)).symm
    · rfl
    · rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact (smul_zero c : c • (0 : k) = 0).symm
    · rfl
    · rfl

private noncomputable def toMatrix : PathAlgebra k Vertex ≃ₗ[k] lowerTriangular k :=
  (pathBasis k).equivFun.trans matrixCoordinates

private theorem toMatrix_basis (i : Fin 3) :
    toMatrix (pathBasis k i) =
      matrix (if i = 0 then 1 else 0) (if i = 2 then 1 else 0) (if i = 1 then 1 else 0) := by
  change matrix ((pathBasis k).equivFun (pathBasis k i) 0)
    ((pathBasis k).equivFun (pathBasis k i) 2) ((pathBasis k).equivFun (pathBasis k i) 1) = _
  simp only [Basis.equivFun_self]

private def vertexIndex : Vertex → Fin 2
  | false => 0
  | true => 1

private theorem vertexIndex_injective : Function.Injective vertexIndex := by
  intro i j h
  cases i <;> cases j <;> first | rfl | contradiction

private theorem toMatrix_path (p : Path Vertex) :
    (↑(toMatrix (PathAlgebra.ofPath k p)) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.single (vertexIndex p.target) (vertexIndex p.source) 1 := by
  obtain ⟨i, rfl⟩ := pathAt_bijective.surjective p
  rw [← pathBasis_apply, toMatrix_basis]
  apply Matrix.ext
  intro r c
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp [matrix, Matrix.single, pathAt, Path.source, Path.target,
      Path.vertex, Path.arrow, Path.ofPath, vertexIndex]

private theorem toMatrix_mul (x y : PathAlgebra k Vertex) :
    toMatrix (x * y) = toMatrix x * toMatrix y := by
  let L : PathAlgebra k Vertex →ₗ[k] lowerTriangular k := toMatrix.toLinearMap
  let left := (PathAlgebra.mulBilinear k Vertex).compr₂ₛₗ L
  let right := (LinearMap.mul k (lowerTriangular k)).compl₁₂ L L
  have h : left = right := by
    apply (PathAlgebra.basis k Vertex).ext
    intro p
    apply (PathAlgebra.basis k Vertex).ext
    intro q
    change toMatrix (PathAlgebra.basis k Vertex p * PathAlgebra.basis k Vertex q) =
      toMatrix (PathAlgebra.basis k Vertex p) * toMatrix (PathAlgebra.basis k Vertex q)
    rw [PathAlgebra.basis_apply, PathAlgebra.basis_apply, PathAlgebra.ofPath_mul_ofPath]
    apply Subtype.ext
    change (toMatrix _ : lowerTriangular k).val =
      (toMatrix (PathAlgebra.ofPath k p)).val * (toMatrix (PathAlgebra.ofPath k q)).val
    rw [toMatrix_path, toMatrix_path]
    by_cases hpq : p.source = q.target
    · rw [dite_eq_left hpq, toMatrix_path, Path.source_concat, Path.target_concat, hpq,
        Matrix.single_mul_single_same, one_mul]
    · have hne : vertexIndex p.source ≠ vertexIndex q.target :=
        fun he => hpq (vertexIndex_injective he)
      rw [dite_eq_right hpq, map_zero, Matrix.single_mul_single_of_ne (1 : k) _ _ _ hne 1]
      rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

private theorem toMatrix_one : toMatrix (1 : PathAlgebra k Vertex) = 1 := by
  rw [← PathAlgebra.sum_vertices, Fintype.sum_bool, map_add]
  apply Subtype.ext
  change (↑(toMatrix (PathAlgebra.ofPath k (Path.vertex true))) : Matrix (Fin 2) (Fin 2) k) +
    ↑(toMatrix (PathAlgebra.ofPath k (Path.vertex false))) = 1
  rw [toMatrix_path, toMatrix_path]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, vertexIndex, Path.vertex, Path.source,
      Path.target, Path.ofPath]

/-- The algebra isomorphism from the one-arrow path algebra to lower triangular matrices. -/
noncomputable def matrixEquiv : PathAlgebra k Vertex ≃ₐ[k] lowerTriangular k :=
  AlgEquiv.ofLinearEquiv toMatrix toMatrix_one toMatrix_mul

private theorem matrixEquiv_symm_matrix (x u y : k) :
    matrixEquiv.symm (matrix x u y) =
      x • PathAlgebra.vertex k false + y • PathAlgebra.vertex k true + u • PathAlgebra.arrow k edge := by
  change (pathBasis k).equivFun.symm ![x, y, u] = _
  rw [Basis.equivFun_symm_apply, Fin.sum_univ_three]
  simp only [pathBasis_apply]
  rfl

end Matrices

open QuiverModuleEquivalence (inverseObj coordinates coordinates_smul)

section Action

variable {k : Type w} [Field k] {V₁ V₂ : Type d}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]

open PathOperators (inclusion projection operator)

private theorem pair_inclusion_first (T : V₁ →ₗ[k] V₂) (v : V₁) :
    pair T (inclusion (representation T) false v) = (v, 0) := by
  apply Prod.ext
  · exact PathOperators.projection_inclusion (representation T) false v
  · exact PathOperators.projection_inclusion_of_ne (representation T)
      (i := true) (j := false) (by decide) v

private theorem pair_inclusion_second (T : V₁ →ₗ[k] V₂) (v : V₂) :
    pair T (inclusion (representation T) true v) = (0, v) := by
  apply Prod.ext
  · exact PathOperators.projection_inclusion_of_ne (representation T)
      (i := false) (j := true) (by decide) v
  · exact PathOperators.projection_inclusion (representation T) true v

private theorem pair_bijective (T : V₁ →ₗ[k] V₂) : Function.Bijective (pair T) := by
  constructor
  · intro x y h
    apply DirectSum.ext_component k
    intro i
    cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · rintro ⟨v₁, v₂⟩
    use inclusion (representation T) false v₁ + inclusion (representation T) true v₂
    rw [map_add, pair_inclusion_first, pair_inclusion_second]
    simp

private theorem arrow_map (T : V₁ →ₗ[k] V₂) :
    QuiverRepresentation.mapPath (representation T) edge.toPath = T :=
  QuiverRepresentation.arrow_ofArrows _ _ edge

set_option maxHeartbeats 800000 in
private theorem action_formula (T : V₁ →ₗ[k] V₂) (x u y : k)
    (v : inverseObj (representation T)) :
    pair T (coordinates (representation T) (matrixEquiv.symm (matrix x u y) • v)) =
      (x • (pair T (coordinates (representation T) v)).1,
        u • T (pair T (coordinates (representation T) v)).1 +
          y • (pair T (coordinates (representation T) v)).2) := by
  rw [coordinates_smul, matrixEquiv_symm_matrix]
  let F := representation T
  let z := coordinates F v
  have h₁ : pair T (operator F (Path.vertex false) z) = ((pair T z).1, 0) := by
    rw [PathOperators.operator_vertex_apply]
    exact pair_inclusion_first T (projection F false z)
  have h₂ : pair T (operator F (Path.vertex true) z) = (0, (pair T z).2) := by
    rw [PathOperators.operator_vertex_apply]
    exact pair_inclusion_second T (projection F true z)
  have ha : pair T (operator F (Path.arrow edge) z) = (0, T (pair T z).1) := by
    change pair T (inclusion F true (QuiverRepresentation.mapPath F edge.toPath
      (projection F false z))) = _
    rw [show QuiverRepresentation.mapPath F edge.toPath = T from arrow_map T]
    exact pair_inclusion_second T (T (pair T z).1)
  change pair T (PathOperators.linearExtension F
    (x • PathAlgebra.vertex k false + y • PathAlgebra.vertex k true + u • PathAlgebra.arrow k edge) z) =
    (x • (pair T z).1, u • T (pair T z).1 + y • (pair T z).2)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    PathAlgebra.vertex_eq_ofPath, PathAlgebra.arrow_eq_ofPath, PathOperators.linearExtension_ofPath,
    h₁, h₂, ha]
  apply Prod.ext <;> simp [add_comm]

end Action

theorem matrixAndAction : MatrixAndAction.{w, d} := by
  intro k _
  refine ⟨inferInstance, inferInstance, ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    matrixEquiv, ?_, ?_, ?_, ?_⟩
  · exact toMatrix_path (Path.vertex false)
  · exact toMatrix_path (Path.vertex true)
  · exact toMatrix_path (Path.arrow edge)
  · intro V₁ V₂ _ _ _ _ T
    exact ⟨pair_bijective T, inverseObj (representation T), coordinates (representation T),
      coordinates_smul (representation T), action_formula T⟩

end RM03.OneArrow
