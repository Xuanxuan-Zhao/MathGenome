import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Radical

namespace Specs.Alg01SymmetricWitt.Witt.Coordinates

universe u v w

/-- The plane with quadratic form (x,y) ↦ x*y. -/
def hyperbolicPlane (k : Type u) [Field k] : QuadraticForm k (k × k) :=
  QuadraticMap.linMulLin (LinearMap.fst k k k) (LinearMap.snd k k k)

/-- The orthogonal sum of r copies of the hyperbolic plane. -/
def hyperbolicSum (k : Type u) [Field k] (r : ℕ) : QuadraticForm k (Fin r → k × k) :=
  QuadraticMap.pi (fun _ : Fin r => hyperbolicPlane k)

/-- The subspace formed by the first-coordinate lines in the hyperbolic sum. -/
def firstCoordinates (k : Type u) [Field k] (r : ℕ) : Submodule k (Fin r → k × k) where
  carrier := {x | ∀ i, (x i).2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    change (x i).2 + (y i).2 = 0
    rw [hx i, hy i, add_zero]
  smul_mem' := by
    intro a x hx i
    change a • (x i).2 = 0
    rw [hx i, smul_zero]

/-- The condition that q vanishes on every vector of a subspace. -/
def totallyIsotropic {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    (q : QuadraticForm k V) (T : Submodule k V) : Prop :=
  ∀ x ∈ T, q x = 0

def hyperbolicPlaneType :=
  ∀ (k : Type u) [Field k], QuadraticForm k (k × k)

def hyperbolicSumType :=
  ∀ (k : Type u) [Field k] (r : ℕ), QuadraticForm k (Fin r → k × k)

def firstCoordinatesType :=
  ∀ (k : Type u) [Field k] (r : ℕ), Submodule k (Fin r → k × k)

set_option linter.checkUnivs false in
def totallyIsotropicType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V],
    QuadraticForm k V → Submodule k V → Prop

def polarization : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] (q : QuadraticForm k V),
    let B := QuadraticMap.associated q
    (∀ x y, B x y = (q (x + y) - q x - q y) / 2) ∧
      B.IsSymm ∧
      (∀ x, B x x = q x) ∧
      (q.Nondegenerate ↔ ∀ x, (∀ y, B x y = 0) → x = 0) ∧
      (∀ T : Submodule k V, totallyIsotropic q T ↔ ∀ x ∈ T, ∀ y ∈ T, B x y = 0)

def preservesQuadraticIffBilinear : Prop :=
  ∀ {k : Type u} {V : Type v} {W : Type w} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (q : QuadraticForm k V) (q' : QuadraticForm k W) (e : V ≃ₗ[k] W),
    (∀ x, q' (e x) = q x) ↔
      ∀ x y, QuadraticMap.associated q' (e x) (e y) = QuadraticMap.associated q x y

def hyperbolicDiagonal : Prop :=
  ∀ (k : Type u) [Field k] [Invertible (2 : k)],
    ∃ e : ((QuadraticMap.sq (R := k)).prod
      ((-1 : k) • (QuadraticMap.sq (R := k) : QuadraticForm k k))).IsometryEquiv (hyperbolicPlane k),
      ∀ z : k × k, e z = (z.1 + z.2, z.1 - z.2)

def hyperbolicNondegenerate : Prop :=
  ∀ (k : Type u) [Field k] [Invertible (2 : k)],
    (hyperbolicPlane k).Nondegenerate ∧ ∀ r, (hyperbolicSum k r).Nondegenerate

end Specs.Alg01SymmetricWitt.Witt.Coordinates
