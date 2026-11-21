import MathGenome.Internal.Specs.D05.M11.IsometryGroups
import MathGenome.Internal.D05.M03.EqualDimension
import MathGenome.Internal.D05.M11.Hermitian
import MathGenome.Internal.D05.M11.FormMatrix
import MathGenome.Internal.D05.M11.SymplecticBlocks
import Mathlib.Tactic.Ring

/-! Isometry groups, preserving the paper's first-slot-linear convention. -/
noncomputable section
namespace D05.M11.IsometryGroups
open Module Matrix
open Specs.D05.M11.IsometryGroups
open scoped BigOperators

/-- Form-preserving linear automorphisms, with the exact carrier proved below. -/
def bilinearIsometryGroup {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {S | ∀ u v, B (S u) (S v) = B u v}

def sesquilinearIsometryGroup {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : Sesq K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {S | ∀ u v, B (S u) (S v) = B u v}

theorem bilinear_operations : Specs.D05.M11.IsometryGroups.bilinear_operations := by
  intro K V _ _ _ B
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro S T hS hT u v
    exact (hS (T u) (T v)).trans (hT u v)
  · intro S hS u v
    simpa using (hS (S.symm u) (S.symm v)).symm

theorem sesquilinear_operations : Specs.D05.M11.IsometryGroups.sesquilinear_operations := by
  intro K V _ _ _ B
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro S T hS hT u v
    exact (hS (T u) (T v)).trans (hT u v)
  · intro S hS u v
    simpa using (hS (S.symm u) (S.symm v)).symm

theorem bilinear_mem : Specs.D05.M11.IsometryGroups.bilinear_mem := by
  intro K V _ _ _ B S
  let H : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {S | ∀ u v, B (S u) (S v) = B u v}
      one_mem' := (bilinear_operations B).1
      mul_mem' := fun hS hT => (bilinear_operations B).2.1 _ _ hS hT
      inv_mem' := fun hS => (bilinear_operations B).2.2 _ hS }
  constructor
  · exact fun h => ((Subgroup.closure_le H).mpr (show {S : V ≃ₗ[K] V | ∀ u v, B (S u) (S v) = B u v} ⊆ H from
      fun _ h => h)) h
  · intro h
    exact Subgroup.subset_closure (show S ∈ {S : V ≃ₗ[K] V | ∀ u v, B (S u) (S v) = B u v} from h)

theorem sesquilinear_mem : Specs.D05.M11.IsometryGroups.sesquilinear_mem := by
  intro K V _ _ _ B S
  let H : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {S | ∀ u v, B (S u) (S v) = B u v}
      one_mem' := (sesquilinear_operations B).1
      mul_mem' := fun hS hT => (sesquilinear_operations B).2.1 _ _ hS hT
      inv_mem' := fun hS => (sesquilinear_operations B).2.2 _ hS }
  constructor
  · exact fun h => ((Subgroup.closure_le H).mpr (show {S : V ≃ₗ[K] V | ∀ u v, B (S u) (S v) = B u v} ⊆ H from
      fun _ h => h)) h
  · intro h
    exact Subgroup.subset_closure (show S ∈ {S : V ≃ₗ[K] V | ∀ u v, B (S u) (S v) = B u v} from h)

theorem bilinear_injective : Specs.D05.M11.IsometryGroups.bilinear_injective := by
  intro K V _ _ _ B hn S hS
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply hn.1 v
  intro w
  rw [← hS, hv]
  simp

theorem sesquilinear_injective : Specs.D05.M11.IsometryGroups.sesquilinear_injective := by
  intro K V _ _ _ B hn S hS
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply hn.1 v
  intro w
  rw [← hS, hv]
  simp

theorem bilinear_automorphism : Specs.D05.M11.IsometryGroups.bilinear_automorphism := by
  intro K V _ _ _ _ B hn S hS
  obtain ⟨e, he⟩ := (D05.M03.EqualDimension.equal_dimension S rfl).2.1.mp
    (bilinear_injective B hn S hS)
  refine ⟨e, he, (bilinear_mem B e).mpr ?_⟩
  intro u v
  change B (e.toLinearMap u) (e.toLinearMap v) = B u v
  rw [he]
  exact hS u v

theorem sesquilinear_automorphism : Specs.D05.M11.IsometryGroups.sesquilinear_automorphism := by
  intro K V _ _ _ _ B hn S hS
  obtain ⟨e, he⟩ := (D05.M03.EqualDimension.equal_dimension S rfl).2.1.mp
    (sesquilinear_injective B hn S hS)
  refine ⟨e, he, (sesquilinear_mem B e).mpr ?_⟩
  intro u v
  change B (e.toLinearMap u) (e.toLinearMap v) = B u v
  rw [he]
  exact hS u v

theorem bilinear_matrix : Specs.D05.M11.IsometryGroups.bilinear_matrix := by
  intro K V _ _ _ n b B S
  have hm := B.toMatrix_comp b b S S
  rw [← D05.M11.FormMatrix.matrix_eq_toMatrix b B] at hm
  constructor
  · intro h
    have he : B.comp S S = B := by ext u v; exact h u v
    rw [he, ← D05.M11.FormMatrix.matrix_eq_toMatrix b B] at hm
    exact hm.symm
  · intro h
    have he : B.comp S S = B := (LinearMap.BilinForm.toMatrix b).injective (by
      rw [hm, h, D05.M11.FormMatrix.matrix_eq_toMatrix])
    intro u v
    exact congrArg (fun C : LinearMap.BilinForm K V => C u v) he

theorem sesquilinear_matrix : Specs.D05.M11.IsometryGroups.sesquilinear_matrix := by
  intro K V _ _ _ n b B S
  let C : Sesq K V := (B.compl₂ S).comp S
  have hm : Specs.D05.M11.Hermitian.formMatrix_value b C =
      (LinearMap.toMatrix b b S)ᵀ * Specs.D05.M11.Hermitian.formMatrix_value b B *
        (LinearMap.toMatrix b b S).map star := by
    ext i j
    change B (S (b i)) (S (b j)) = _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [D05.M11.Hermitian.matrix_formula b B (S (b i)) (S (b j))]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul,
      Specs.D05.M11.Hermitian.formMatrix_value, LinearMap.toMatrix_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    ring
  constructor
  · intro h
    have he : C = B := by ext u v; exact h u v
    rw [he] at hm
    exact hm.symm
  · intro h
    have he : C = B := LinearMap.ext_basis b b (fun i j => by
      have hij := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) (hm.trans h)
      exact hij)
    intro u v
    exact congrArg (fun D : Sesq K V => D u v) he

def orthogonalGroup {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (_hs : B.IsSymm)
    (_hp : ∀ v, v ≠ 0 → 0 < B v v) : Subgroup (V ≃ₗ[ℝ] V) :=
  bilinearIsometryGroup B

def unitaryGroup {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : Sesq ℂ V) (_hh : Specs.D05.M11.Hermitian.isHermitian_value B)
    (_hp : ∀ v, v ≠ 0 → 0 < (B v v).re) : Subgroup (V ≃ₗ[ℂ] V) :=
  sesquilinearIsometryGroup B

def symplecticGroup {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (_ha : B.IsAlt) (_hn : B.Nondegenerate) :
    Subgroup (V ≃ₗ[K] V) := bilinearIsometryGroup B

theorem real_positive_nondegenerate :
    Specs.D05.M11.IsometryGroups.real_positive_nondegenerate := by
  intro V _ _ B hp
  constructor <;> intro v hv <;> by_contra hn
  all_goals have h := hp v hn; rw [hv v] at h; exact (lt_irrefl 0 h)

theorem complex_positive_nondegenerate :
    Specs.D05.M11.IsometryGroups.complex_positive_nondegenerate := by
  intro V _ _ B hp
  constructor <;> intro v hv <;> by_contra hn
  all_goals have h := hp v hn; rw [hv v] at h; exact (lt_irrefl 0 h)

theorem orthogonal_mem : Specs.D05.M11.IsometryGroups.orthogonal_mem := by
  intro V _ _ B hs hp S
  exact bilinear_mem B S

theorem unitary_mem : Specs.D05.M11.IsometryGroups.unitary_mem := by
  intro V _ _ B hh hp S
  exact sesquilinear_mem B S

theorem symplectic_mem : Specs.D05.M11.IsometryGroups.symplectic_mem := by
  intro K V _ _ _ B ha hn S
  exact bilinear_mem B S

theorem symplectic_even_dimension : Specs.D05.M11.IsometryGroups.symplectic_even_dimension := by
  exact D05.M11.SymplecticBlocks.even_dimension

theorem bilinear_group_coordinates :
    Specs.D05.M11.IsometryGroups.bilinear_group_coordinates := by
  intro K V _ _ _ n b B S
  exact (bilinear_mem B S).trans (bilinear_matrix b B S.toLinearMap)

theorem sesquilinear_group_coordinates :
    Specs.D05.M11.IsometryGroups.sesquilinear_group_coordinates := by
  intro K V _ _ _ n b B S
  exact (sesquilinear_mem B S).trans (sesquilinear_matrix b B S.toLinearMap)

theorem complex_conventions_distinct :
    Specs.D05.M11.IsometryGroups.complex_conventions_distinct := by
  dsimp only [Specs.D05.M11.IsometryGroups.complex_conventions_distinct]
  constructor
  · ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  · intro h
    have h0 := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply, Matrix.of_apply] at h0
    have hre := congrArg Complex.re h0
    norm_num at hre

end D05.M11.IsometryGroups
