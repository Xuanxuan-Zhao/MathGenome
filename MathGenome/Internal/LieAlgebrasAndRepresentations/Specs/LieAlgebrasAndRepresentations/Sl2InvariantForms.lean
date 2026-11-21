import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TensorDualHom
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! LA-C06, invariant-form and self-duality assertions, source lines 1402–1470.
The basis normalization is (3.1), and the matrix is exactly (3.9).
Theorems are stated on any standard-basis realization of L_n, including n=0.
-/
noncomputable section
universe u v
namespace Specs.LieAlgebrasAndRepresentations.Sl2InvariantForms
open Module Sl2Model Sl2SimpleModules

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]

def form {n : ℕ} (b : Basis (Fin (n + 1)) k M) : LinearMap.BilinForm k M :=
  Matrix.toBilin b (Matrix.of fun i j => if i.val + j.val = n then (-1 : k) ^ i.val else 0)

def Invariant [LieRingModule (Model k) M] [LieModule k (Model k) M]
    (B : LinearMap.BilinForm k M) : Prop :=
  ∀ (x : Model k) (v w : M), B ⁅x, v⁆ w + B v ⁅x, w⁆ = 0

def form_type := ∀ (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module k M]
  (n : ℕ), Basis (Fin (n + 1)) k M → LinearMap.BilinForm k M

def form_value (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module k M]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M) := form b

def entriesExpected : Prop :=
  ∀ (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module k M]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M) (i j : Fin (n + 1)),
    form b (b i) (b j) = if i.val + j.val = n then (-1 : k)^i.val else 0

def propertiesExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M), IsStandardBasis b →
    Invariant (form b) ∧ (form b).Nondegenerate ∧ form b ≠ 0 ∧
    (Even n → (form b).IsSymm) ∧ (Odd n → (form b).IsAlt)

def uniquenessExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M), IsStandardBasis b →
    ∀ C : LinearMap.BilinForm k M, Invariant C →
      ∃! c : k, C = c • form b

def nonzeroExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M), IsStandardBasis b →
    ∀ C : LinearMap.BilinForm k M, Invariant C → C ≠ 0 →
      C.Nondegenerate ∧ ∃ c : k, c ≠ 0 ∧ C = c • form b

def selfDualExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M), IsStandardBasis b →
    ∃ φ : M ≃ₗ⁅k, Model k⁆ Module.Dual k M, ∀ v w, φ v w = form b v w
/-- Explicit existence on the coefficient-space models, with the standard action
and the coordinate basis. This makes applicability to every L_n concrete. -/
def modelsExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n : ℕ),
    ∃ (a : LieRingModule (Model k) (Fin (n+1) → k))
      (c : @LieModule k (Model k) (Fin (n+1) → k) _ _ _ _ _ a),
      letI := a
      letI := c
      let b := Pi.basisFun k (Fin (n+1))
      let B := form b
      IsStandardBasis b ∧ Invariant B ∧ B.Nondegenerate ∧ B ≠ 0 ∧
      (Even n → B.IsSymm) ∧ (Odd n → B.IsAlt) ∧
      (∀ C : LinearMap.BilinForm k (Fin (n+1) → k), Invariant C → ∃! c : k, C = c • B) ∧
      ∃ φ : (Fin (n+1) → k) ≃ₗ⁅k, Model k⁆ Module.Dual k (Fin (n+1) → k),
        ∀ v w, φ v w = B v w
end Specs.LieAlgebrasAndRepresentations.Sl2InvariantForms
