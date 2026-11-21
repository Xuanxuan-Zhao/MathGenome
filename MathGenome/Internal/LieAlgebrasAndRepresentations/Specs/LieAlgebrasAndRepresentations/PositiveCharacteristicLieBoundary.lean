import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-! LA-J09, positive characteristic example, source lines 5390–5401.
The vector space is the actual polynomial quotient, not a matrix model.
The coordinate Heisenberg algebra has [eD,eT]=eI in every characteristic.
-/
noncomputable section
universe u
namespace Specs.LieAlgebrasAndRepresentations.PositiveCharacteristicLieBoundary
open Polynomial
variable (k : Type u) [Field k] (p : ℕ)

def truncationIdeal : Ideal k[X] := Ideal.span {X ^ p}
abbrev V := k[X] ⧸ truncationIdeal k p

def q : k[X] →ₐ[k] V k p := Ideal.Quotient.mkₐ k (truncationIdeal k p)

variable [CharP k p]

/-- The relation defining the quotient is preserved by differentiation. -/
lemma derivative_relation {f : k[X]} (hf : f ∈ truncationIdeal k p) :
    derivative f ∈ truncationIdeal k p := by
  rw [truncationIdeal, Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨g, rfl⟩ := hf
  rw [derivative_mul]
  simp only [derivative_X_pow, CharP.cast_eq_zero, map_zero, zero_mul, zero_add]
  exact dvd_mul_right _ _

/-- Differentiation descends to k[t]/(t^p) precisely using characteristic p. -/
def D : Module.End k (V k p) :=
  ((truncationIdeal k p).restrictScalars k).mapQ
    ((truncationIdeal k p).restrictScalars k) derivative
    (fun _ hf => derivative_relation k p hf)

/-- Multiplication by the residue class of t. -/
def T : Module.End k (V k p) := Algebra.lmul k (V k p) (q k p X)
def I : Module.End k (V k p) := LinearMap.id

/-- Coordinates in the ordered basis eD,eT,eI. A separate type prevents
its nonabelian bracket from changing the usual product Lie algebra. -/
@[ext] structure Heisenberg where
  d : k
  t : k
  i : k

def coordinates : Heisenberg k ≃ k × k × k where
  toFun x := (x.d, x.t, x.i)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Heisenberg k) := (coordinates k).addCommGroup

def coordinatesAdd : Heisenberg k ≃+ k × k × k where
  __ := coordinates k
  map_add' _ _ := rfl

instance : Module k (Heisenberg k) := (coordinatesAdd k).module k

def coordinatesLinear : Heisenberg k ≃ₗ[k] k × k × k :=
  (coordinatesAdd k).linearEquiv k

instance : LieRing (Heisenberg k) where
  bracket x y := ⟨0, 0, x.d * y.t - y.d * x.t⟩
  add_lie x y z := by
    apply Heisenberg.ext
    · change (0 : k) = 0 + 0; simp
    · change (0 : k) = 0 + 0; simp
    · change (x.d + y.d) * z.t - z.d * (x.t + y.t) =
        (x.d * z.t - z.d * x.t) + (y.d * z.t - z.d * y.t)
      ring
  lie_add x y z := by
    apply Heisenberg.ext
    · change (0 : k) = 0 + 0; simp
    · change (0 : k) = 0 + 0; simp
    · change x.d * (y.t + z.t) - (y.d + z.d) * x.t =
        (x.d * y.t - y.d * x.t) + (x.d * z.t - z.d * x.t)
      ring
  lie_self x := by
    apply Heisenberg.ext
    · rfl
    · rfl
    · change x.d * x.t - x.d * x.t = 0; simp
  leibniz_lie x y z := by
    apply Heisenberg.ext
    · change (0 : k) = 0 + 0; simp
    · change (0 : k) = 0 + 0; simp
    · change x.d * 0 - 0 * x.t =
        (0 * z.t - z.d * 0) + (y.d * 0 - 0 * y.t)
      simp

instance : LieAlgebra k (Heisenberg k) where
  lie_smul a x y := by
    apply Heisenberg.ext
    · change (0 : k) = a * 0; simp
    · change (0 : k) = a * 0; simp
    · change x.d * (a * y.t) - (a * y.d) * x.t =
        a * (x.d * y.t - y.d * x.t)
      ring

def eD : Heisenberg k := ⟨1, 0, 0⟩
def eT : Heisenberg k := ⟨0, 1, 0⟩
def eI : Heisenberg k := ⟨0, 0, 1⟩

def action : Heisenberg k →ₗ[k] Module.End k (V k p) where
  toFun x := x.d • D k p + x.t • T k p + x.i • I k p
  map_add' x y := by
    change (x.d + y.d) • D k p + (x.t + y.t) • T k p +
      (x.i + y.i) • I k p = _
    simp only [add_smul]
    abel
  map_smul' t x := by
    change (t * x.d) • D k p + (t * x.t) • T k p + (t * x.i) • I k p = _
    simp [smul_add, smul_smul]

/-! Independent expected propositions. Endomorphism brackets are explicitly
composition commutators, avoiding the competing action-on-linear-maps instance. -/
local instance endLieRing : LieRing (Module.End k (V k p)) := LieRing.ofAssociativeRing
local instance endBracket : Bracket (Module.End k (V k p)) (Module.End k (V k p)) :=
  ⟨fun f g => f * g - g * f⟩

def D_q_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] (f : k[X]),
    D k p (q k p f) = q k p (derivative f)

def T_q_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] (f : k[X]),
    T k p (q k p f) = q k p (X * f)

def commutator_DT_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    ⁅D k p, T k p⁆ = I k p

def commutator_DI_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    ⁅D k p, I k p⁆ = 0

def commutator_TI_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    ⁅T k p, I k p⁆ = 0

def no_common_eigenvector_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] (v : V k p) (a b : k)
    (_hD : D k p v = a • v) (_hT : T k p v = b • v),
    v = 0

def quotient_dimension_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    Module.finrank k (V k p) = p

def quotient_finite_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    Module.Finite k (V k p)

def heisenberg_dimension_type :=
  ∀ (k : Type u) [Field k],
    Module.finrank k (Heisenberg k) = 3

def heisenberg_brackets_type :=
  ∀ (k : Type u) [Field k],
    ⁅eD k, eT k⁆ = eI k ∧ ⁅eD k, eI k⁆ = 0 ∧ ⁅eT k, eI k⁆ = 0

def heisenberg_nilpotent_type :=
  ∀ (k : Type u) [Field k],
    LieRing.IsNilpotent (Heisenberg k)

def heisenberg_solvable_type :=
  ∀ (k : Type u) [Field k],
    LieAlgebra.IsSolvable (Heisenberg k)

def representation_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    ∃ ρ : Heisenberg k →ₗ⁅k⁆ Module.End k (V k p),
    ρ.toLinearMap = action k p

def commutator_top_monomial_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    ⁅D k p, T k p⁆ (q k p (X ^ (p - 1))) = q k p (X ^ (p - 1))

def quotient_relation_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    q k p (X ^ p) = 0

def action_generators_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p],
    action k p (eD k) = D k p ∧
    action k p (eT k) = T k p ∧ action k p (eI k) = I k p

def identity_not_nilpotent_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p),
    ¬ IsNilpotent (I k p)

def counterexample_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p),
    Module.Finite k (V k p) ∧ Module.finrank k (V k p) = p ∧
    0 < Module.finrank k (V k p) ∧
    Module.finrank k (Heisenberg k) = 3 ∧
    LieRing.IsNilpotent (Heisenberg k) ∧ LieAlgebra.IsSolvable (Heisenberg k) ∧
    ∃ ρ : Heisenberg k →ₗ⁅k⁆ Module.End k (V k p),
      ρ (eD k) = D k p ∧ ρ (eT k) = T k p ∧ ρ (eI k) = I k p ∧
      ∀ v : V k p, (∀ x : Heisenberg k, ∃ a : k, ρ x v = a • v) → v = 0

end Specs.LieAlgebrasAndRepresentations.PositiveCharacteristicLieBoundary
