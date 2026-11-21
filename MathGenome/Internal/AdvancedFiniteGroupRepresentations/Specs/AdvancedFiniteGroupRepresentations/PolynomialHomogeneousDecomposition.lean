import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorActions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! FR-D11, first paragraph of the proof, and the d = 0 convention.
The bases are arbitrary finite bases. Polynomial means polynomial in the
entries of g itself, with no determinant inverses. All degrees are natural.
-/
noncomputable section
open scoped BigOperators
open Module
universe u v
namespace Specs.AdvancedFiniteGroupRepresentations

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {d m : ℕ}

def matrixCoordinates (b : Basis (Fin d) ℂ V) (g : LinearGroup V) :
    (Fin d × Fin d) → ℂ :=
  fun ij => LinearMap.toMatrix b b g.toLinearMap ij.1 ij.2

def IsPolynomialRepresentation (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) : Prop :=
  ∀ i j, ∃ p : MvPolynomial (Fin d × Fin d) ℂ,
    ∀ g, MvPolynomial.eval (matrixCoordinates b g) p =
      LinearMap.toMatrix c c (ρ g) i j

def IsHomogeneousRepresentation (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ) : Prop :=
  ∀ i j, ∃ p : MvPolynomial (Fin d × Fin d) ℂ, p.IsHomogeneous n ∧
    ∀ g, MvPolynomial.eval (matrixCoordinates b g) p =
      LinearMap.toMatrix c c (ρ g) i j

def scalarElement (V : Type u) [AddCommGroup V] [Module ℂ V]
    (t : ℂˣ) : LinearGroup V := LinearEquiv.smulOfUnit t

def weightSpace (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ) : Submodule ℂ W where
  carrier := {w | ∀ t : ℂˣ, ρ (scalarElement V t) w = (t : ℂ) ^ n • w}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy t
    simp only [map_add, hx t, hy t, smul_add]
  smul_mem' := by
    intro a x hx t
    simp only [map_smul, hx t, smul_comm a]

def IsInvariant (ρ : LinearGroup V →* Module.End ℂ W) (U : Submodule ℂ W) : Prop :=
  ∀ g, ∀ w ∈ U, ρ g w ∈ U

def restrictedRepresentation (ρ : LinearGroup V →* Module.End ℂ W)
    (U : Submodule ℂ W) (h : IsInvariant ρ U) :
    LinearGroup V →* Module.End ℂ U where
  toFun g := (ρ g).restrict (h g)
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

/-- Complete output of the homogeneous decomposition theorem. In particular,
`homogeneous` is about polynomial matrix entries on the actual invariant
subspaces, and is not merely a condition on the scalar subgroup. -/
structure HomogeneousDecomposition [FiniteDimensional ℂ W]
    (b : Basis (Fin d) ℂ V) (ρ : LinearGroup V →* Module.End ℂ W) where
  bound : ℕ
  projection : ℕ → Module.End ℂ W
  zero_above : ∀ n, bound < n → projection n = 0
  orthogonal : ∀ i j, projection i * projection j = if i = j then projection i else 0
  sum_projection : ∑ n ∈ Finset.range (bound + 1), projection n = 1
  commute : ∀ n g, Commute (projection n) (ρ g)
  scalar_expansion : ∀ t : ℂˣ, ρ (scalarElement V t) =
    ∑ n ∈ Finset.range (bound + 1), (t : ℂ) ^ n • projection n
  invariant : ∀ n, IsInvariant ρ (LinearMap.range (projection n))
  internal : DirectSum.IsInternal (fun n => LinearMap.range (projection n))
  homogeneous : ∀ n, IsHomogeneousRepresentation b
    (Module.finBasis ℂ (LinearMap.range (projection n)))
    (restrictedRepresentation ρ (LinearMap.range (projection n)) (invariant n)) n
  weight_characterization : 0 < d → ∀ n, LinearMap.range (projection n) = weightSpace ρ n
  zero_dimension : d = 0 →
    LinearMap.range (projection 0) = ⊤ ∧
    ∀ n, 0 < n → LinearMap.range (projection n) = ⊥

abbrev HomogeneousDecompositionValue := @HomogeneousDecomposition

def homogeneous_decompositionType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (d m : ℕ) (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W),
    IsPolynomialRepresentation b c ρ → Nonempty (HomogeneousDecomposition b ρ)

def homogeneous_isPolynomialType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d m : ℕ)
    (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ),
    IsHomogeneousRepresentation b c ρ n → IsPolynomialRepresentation b c ρ

def zero_dimension_degree_zeroType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (m : ℕ)
    (b : Basis (Fin 0) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W), IsHomogeneousRepresentation b c ρ 0

def zero_dimension_no_positive_degreeType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (m : ℕ)
    (b : Basis (Fin 0) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ),
    0 < n → IsHomogeneousRepresentation b c ρ n → Subsingleton W

def scalar_polynomial_expansionType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d m : ℕ)
    (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W), IsPolynomialRepresentation b c ρ →
    ∃ (N : ℕ) (P : ℕ → Module.End ℂ W),
      (∀ n, N < n → P n = 0) ∧
      ∀ t : ℂˣ, ρ (scalarElement V t) =
        ∑ n ∈ Finset.range (N + 1), (t : ℂ) ^ n • P n

def matrixCoordinatesType :=
  {V : Type u} → [AddCommGroup V] → [Module ℂ V] → {d : ℕ} →
    Basis (Fin d) ℂ V → LinearGroup V → (Fin d × Fin d) → ℂ

def IsPolynomialRepresentationType :=
  {V : Type u} → {W : Type v} → [AddCommGroup V] → [Module ℂ V] →
    [AddCommGroup W] → [Module ℂ W] → {d m : ℕ} →
    Basis (Fin d) ℂ V → Basis (Fin m) ℂ W →
    (LinearGroup V →* Module.End ℂ W) → Prop

def IsHomogeneousRepresentationType :=
  {V : Type u} → {W : Type v} → [AddCommGroup V] → [Module ℂ V] →
    [AddCommGroup W] → [Module ℂ W] → {d m : ℕ} →
    Basis (Fin d) ℂ V → Basis (Fin m) ℂ W →
    (LinearGroup V →* Module.End ℂ W) → ℕ → Prop

def scalarElementType :=
  (V : Type u) → [AddCommGroup V] → [Module ℂ V] → ℂˣ → LinearGroup V

def weightSpaceType :=
  {V : Type u} → {W : Type v} → [AddCommGroup V] → [Module ℂ V] →
    [AddCommGroup W] → [Module ℂ W] →
    (LinearGroup V →* Module.End ℂ W) → ℕ → Submodule ℂ W

def IsInvariantType :=
  {V : Type u} → {W : Type v} → [AddCommGroup V] → [Module ℂ V] →
    [AddCommGroup W] → [Module ℂ W] →
    (LinearGroup V →* Module.End ℂ W) → Submodule ℂ W → Prop

def restrictedRepresentationType :=
  {V : Type u} → {W : Type v} → [AddCommGroup V] → [Module ℂ V] →
    [AddCommGroup W] → [Module ℂ W] →
    (ρ : LinearGroup V →* Module.End ℂ W) → (U : Submodule ℂ W) →
    IsInvariant ρ U → (LinearGroup V →* Module.End ℂ U)

def HomogeneousDecompositionType :=
  {V : Type u} → {W : Type v} → [AddCommGroup V] → [Module ℂ V] →
    [AddCommGroup W] → [Module ℂ W] → {d : ℕ} → [FiniteDimensional ℂ W] →
    Basis (Fin d) ℂ V → (LinearGroup V →* Module.End ℂ W) → Type v

def weightSpace_invariantType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ),
    IsInvariant ρ (weightSpace ρ n)

def invariant_subspace_isPolynomialType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d m : ℕ)
    (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W), IsPolynomialRepresentation b c ρ →
    ∀ (U : Submodule ℂ W) (hU : IsInvariant ρ U) (k : ℕ) (r : Basis (Fin k) ℂ U),
      IsPolynomialRepresentation b r (restrictedRepresentation ρ U hU)

def zero_dimension_group_trivialType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
    (b : Basis (Fin 0) ℂ V) (g : LinearGroup V), g = 1

def scalar_coefficients_sumType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : LinearGroup V →* Module.End ℂ W)
    (N : ℕ) (P : ℕ → Module.End ℂ W),
    (∀ t : ℂˣ, ρ (scalarElement V t) =
      ∑ n ∈ Finset.range (N + 1), (t : ℂ) ^ n • P n) →
    ∑ n ∈ Finset.range (N + 1), P n = 1

end Specs.AdvancedFiniteGroupRepresentations
