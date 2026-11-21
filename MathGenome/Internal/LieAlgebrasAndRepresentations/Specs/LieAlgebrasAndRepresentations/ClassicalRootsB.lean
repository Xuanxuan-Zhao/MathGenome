import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! LA-D08-B, `res:D08`, notes/005/lie-algebras-and-representations.tex,
1930–1983. The central coordinate is `none`, the positive and negative
coordinates are `some (inl i)` and `some (inr i)`. This is the order
(0,t₁,…,tₙ,−t₁,…,−tₙ), a permutation of the displayed order.
The form has central entry 1 and hyperbolic pairs of entry 1.
Weights are linear functionals on the parameters of the diagonal Cartan.
All weight spaces below are submodules of the actual matrix algebra, with
membership in the orthogonal algebra included, not abstract formal root lines. -/

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Specs.LieAlgebrasAndRepresentations.ClassicalRootsB

abbrev Index (n : ℕ) := Option (Fin n ⊕ Fin n)
abbrev Mat (n : ℕ) := Matrix (Index n) (Index n) ℂ
abbrev Parameters (n : ℕ) := Fin n → ℂ
abbrev Weight (n : ℕ) := Module.Dual ℂ (Parameters n)

def opposite {n : ℕ} : Index n → Index n
  | none => none
  | some (Sum.inl i) => some (Sum.inr i)
  | some (Sum.inr i) => some (Sum.inl i)

@[simp] theorem opposite_opposite {n : ℕ} (p : Index n) : opposite (opposite p) = p := by
  cases p with
  | none => rfl
  | some p => cases p <;> rfl

def form (n : ℕ) : Mat n := fun p q => if p = opposite q then 1 else 0

def algebra (n : ℕ) : LieSubalgebra ℂ (Mat n) :=
  skewAdjointMatricesLieSubalgebra (form n)

def epsilon {n : ℕ} (i : Fin n) : Weight n := LinearMap.proj i

def coordinateWeight {n : ℕ} : Index n → Weight n
  | none => 0
  | some (Sum.inl i) => epsilon i
  | some (Sum.inr i) => -epsilon i

noncomputable def diagonal (n : ℕ) : Parameters n →ₗ[ℂ] Mat n where
  toFun t := Matrix.diagonal (fun p => coordinateWeight p t)
  map_add' t u := by ext p q; simp [map_add, Matrix.diagonal_apply]; split <;> simp
  map_smul' c t := by ext p q; simp [Matrix.diagonal_apply]

/-- The displayed diagonal subalgebra, inside the orthogonal Lie algebra. -/
noncomputable def cartan (n : ℕ) : LieSubalgebra ℂ (algebra n) where
  __ := (LinearMap.range (diagonal n)).comap (algebra n).toSubmodule.subtype
  lie_mem' := by
    rintro X Y ⟨t, ht⟩ ⟨u, hu⟩
    change diagonal n t = (X : Mat n) at ht
    change diagonal n u = (Y : Mat n) at hu
    refine ⟨0, ?_⟩
    change diagonal n 0 = (X : Mat n) * (Y : Mat n) - (Y : Mat n) * (X : Mat n)
    rw [map_zero, ← ht, ← hu]
    have hc : diagonal n t * diagonal n u = diagonal n u * diagonal n t := by
      ext p q
      by_cases hpq : p = q <;> simp [diagonal, hpq, mul_comm]
    rw [hc, sub_self]

/-- The inverse coordinate chart reads the positive diagonal entries. -/
noncomputable def coordinates (n : ℕ) : cartan n →ₗ[ℂ] Parameters n where
  toFun h i := h.val.val (some (Sum.inl i)) (some (Sum.inl i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def character {n : ℕ} (a : Weight n) : Module.Dual ℂ (cartan n) :=
  a.comp (coordinates n)

noncomputable def weightSpace {n : ℕ} (a : Weight n) : Submodule ℂ (Mat n) :=
  (algebra n).toSubmodule ⊓ ⨅ t : Parameters n,
    LinearMap.ker (LieAlgebra.ad ℂ (Mat n) (diagonal n t) - a t • LinearMap.id)

def roots (n : ℕ) : Set (Weight n) := {a | a ≠ 0 ∧ weightSpace a ≠ ⊥}

def listedRoots (n : ℕ) : Set (Weight n) :=
  {a | (∃ i : Fin n, a = epsilon i ∨ a = -epsilon i) ∨
    ∃ i j : Fin n, i < j ∧
      (a = epsilon i + epsilon j ∨ a = epsilon i - epsilon j ∨
       a = -epsilon i + epsilon j ∨ a = -epsilon i - epsilon j)}

def rootVector {n : ℕ} (p q : Index n) : Mat n :=
  Matrix.single p q 1 - Matrix.single (opposite q) (opposite p) 1

/-- Complex bilinear extension of the standard Euclidean coordinate form. -/
def squaredLength {n : ℕ} (a : Weight n) : ℂ :=
  ∑ i : Fin n, (a (Pi.single i 1)) ^ 2

noncomputable def coroot {n : ℕ} (a : Weight n) : Mat n :=
  diagonal n (fun i => (2 / squaredLength a) * a (Pi.single i 1))

def form_properties_type : Prop := ∀ n : ℕ,
  (form n).transpose = form n ∧ form n * form n = 1 ∧
    Fintype.card (Index n) = 2 * n + 1

def form_nondegenerate_type : Prop := ∀ n : ℕ, (form n).Nondegenerate

def cartan_identification_type : Prop := ∀ n : ℕ,
  Function.Bijective (coordinates n) ∧ Function.Bijective (@character n)

def root_space_bridge_type : Prop := ∀ (n : ℕ) (a : Weight n),
  (LieModule.weightSpace (algebra n) (character a)).toSubmodule.map
    (algebra n).toSubmodule.subtype = weightSpace a

def algebra_entries_type : Prop := ∀ (n : ℕ) (X : Mat n),
  X ∈ algebra n ↔ ∀ p q, X p q = -X (opposite q) (opposite p)

def diagonal_injective_type : Prop := ∀ n : ℕ, Function.Injective (diagonal n)

def diagonal_mem_type : Prop := ∀ (n : ℕ) (t : Parameters n), diagonal n t ∈ algebra n

def weightSpace_entries_type : Prop := ∀ (n : ℕ) (a : Weight n) (X : Mat n),
  X ∈ weightSpace a ↔ X ∈ algebra n ∧
    ∀ p q, X p q ≠ 0 → a = coordinateWeight p - coordinateWeight q

def zero_space_type : Prop := ∀ n : ℕ,
  weightSpace (0 : Weight n) = LinearMap.range (diagonal n)

def roots_eq_type : Prop := ∀ (n : ℕ), roots n = listedRoots n

def root_spaces_type : Prop := ∀ (n : ℕ) (p q : Index n),
  p ≠ q → p ≠ opposite q →
    weightSpace (coordinateWeight p - coordinateWeight q) =
      Submodule.span ℂ {rootVector p q}

def root_dimensions_type : Prop := ∀ (n : ℕ), ∀ a ∈ roots n,
  Module.finrank ℂ (weightSpace a) = 1

/-- Both spanning and independence are asserted, including the zero space. -/
def decomposition_type : Prop := ∀ (n : ℕ),
  (⨆ a : Weight n, weightSpace a) = (algebra n).toSubmodule ∧
    iSupIndep (fun a : Weight n => weightSpace a)

/-- The Euclidean coroot matrix is verified by actual opposite root triples. -/
def coroot_triples_type : Prop := ∀ (n : ℕ), ∀ a ∈ roots n,
  squaredLength a ≠ 0 ∧ coroot a ∈ algebra n ∧
    ∃ e f : Mat n, e ∈ weightSpace a ∧ f ∈ weightSpace (-a) ∧
      e ≠ 0 ∧ f ≠ 0 ∧ ⁅e, f⁆ = coroot a ∧
      ⁅coroot a, e⁆ = (2 : ℂ) • e ∧ ⁅coroot a, f⁆ = (-2 : ℂ) • f

end Specs.LieAlgebrasAndRepresentations.ClassicalRootsB
