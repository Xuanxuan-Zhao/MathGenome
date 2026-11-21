import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootForm
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Type A part of LA-D08, notes/005, Matrix models, res:D08.
The algebra consists of traceless complex (n+1)-by-(n+1) matrices for every
`n`, including `n = 0`. The diagonal subalgebra is defined by vanishing
off-diagonal entries. -/
namespace Specs.LieAlgebrasAndRepresentations.ClassicalRootsA

abbrev sl (n : ℕ) := LieAlgebra.SpecialLinear.sl (Fin (n+1)) ℂ

/-- The traceless diagonal matrices. -/
def cartan (n : ℕ) : LieSubalgebra ℂ (sl n) where
  carrier := {X | (X.val).IsDiag}
  zero_mem' := Matrix.isDiag_zero
  add_mem' := fun hx hy => hx.add hy
  smul_mem' := fun c _ hx => hx.smul c
  lie_mem' := by
    intro X Y hx hy
    change (X.val * Y.val - Y.val * X.val).IsDiag
    rw [← hx.diagonal_diag, ← hy.diagonal_diag]
    simp only [Matrix.diagonal_mul_diagonal]
    exact (Matrix.isDiag_diagonal _).sub (Matrix.isDiag_diagonal _)

def epsilon (n : ℕ) (i : Fin (n+1)) : Module.Dual ℂ (cartan n) where
  toFun h := h.val.val i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def root (n : ℕ) (i j : Fin (n+1)) : Module.Dual ℂ (cartan n) :=
  epsilon n i - epsilon n j

def rootVector (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) : sl n :=
  LieAlgebra.SpecialLinear.single i j hij 1

/-- The diagonal matrix with entries +1 at i and -1 at j. -/
def coroot (n : ℕ) (i j : Fin (n+1)) : cartan n :=
  ⟨LieAlgebra.SpecialLinear.singleSubSingle i j 1, by
    intro a b hab
    change ((Matrix.single i i (1 : ℂ) - Matrix.single j j 1) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) a b = 0
    by_cases hi : i = a <;> by_cases hj : j = a <;>
      simp_all [Matrix.single]⟩

/-- Real Euclidean coordinates, with their ordinary dot product. -/
def euclideanRoot (n : ℕ) (i j : Fin (n+1)) : Fin (n+1) → ℝ :=
  Pi.single i 1 - Pi.single j 1

def coordinateEmbedding (n : ℕ) : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin (n+1) → ℂ) where
  toFun v a := (v a : ℂ)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Full classification, including weights which do not occur. -/
def rootSet_type : Prop := ∀ n : ℕ, ∀ α : Module.Dual ℂ (cartan n),
  α ∈ RootDecomposition.rootSet_value (cartan n) ↔
    ∃ i j : Fin (n+1), i ≠ j ∧ α = root n i j

def rootSpace_type : Prop := ∀ n : ℕ, ∀ (i j : Fin (n+1)) (hij : i ≠ j),
  RootDecomposition.rootSpace_value (cartan n) (root n i j) =
    Submodule.span ℂ {rootVector n i j hij}

def zeroSpace_type : Prop := ∀ n : ℕ,
  RootDecomposition.rootSpace_value (cartan n) 0 = (cartan n).toSubmodule

def dimension_type : Prop := ∀ n : ℕ, ∀ (i j : Fin (n+1)), i ≠ j →
  Module.finrank ℂ (RootDecomposition.rootSpace_value (cartan n) (root n i j)) = 1

def cartan_type : Prop := ∀ n : ℕ, (cartan n).IsCartanSubalgebra

def decomposition_type : Prop := ∀ n : ℕ,
  letI : DecidableEq (Option (RootDecomposition.rootSet_value (cartan n))) := Classical.decEq _
  DirectSum.IsInternal (RootDecomposition.rootSummand_value (cartan n))

def triple_type : Prop := ∀ n : ℕ, ∀ (i j : Fin (n+1)) (hij : i ≠ j),
  ⁅rootVector n i j hij, rootVector n j i hij.symm⁆ = (coroot n i j : sl n) ∧
  ⁅(coroot n i j : sl n), rootVector n i j hij⁆ = (2 : ℂ) • rootVector n i j hij ∧
  ⁅(coroot n i j : sl n), rootVector n j i hij.symm⁆ = (-2 : ℂ) • rootVector n j i hij.symm

def corootCoordinates_type : Prop := ∀ n : ℕ, ∀ (i j : Fin (n+1)), i ≠ j →
  let α := euclideanRoot n i j
  (∑ a, α a * α a) = 2 ∧
  (fun a => (coroot n i j).val.val a a) =
    coordinateEmbedding n ((2 / (∑ a, α a * α a)) • α)

/-- The real root vector represents the complex coordinate functional. -/
def rootCoordinates_type : Prop := ∀ n : ℕ, ∀ (i j : Fin (n+1)) (h : cartan n),
  (∑ a, coordinateEmbedding n (euclideanRoot n i j) a * h.val.val a a) = root n i j h

/-- Agreement with the Killing-form definition of coroot from LA-U07/D03. -/
def killingCoroot_type : Prop := ∀ n : ℕ, ∀ (i j : Fin (n+1)), i ≠ j →
  RootForm.coroot_value (cartan n) (root n i j) = coroot n i j

end Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
