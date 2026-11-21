import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.Ring

/-! LA-U02, source lines 254–257. All constructions work over every field,
including characteristic two. Coordinates are in the ordered basis h,e. -/

universe u v
open Module
namespace LieAlgebrasAndRepresentations.Boundary

/-- The two-dimensional algebra with [h,e] = e. -/
def AffineLie (k : Type u) := k × k

variable (k : Type u) [Field k]

instance : AddCommGroup (AffineLie k) := inferInstanceAs (AddCommGroup (k × k))
instance : Module k (AffineLie k) := inferInstanceAs (Module k (k × k))

instance : LieRing (AffineLie k) where
  bracket x y := (0, x.1 * y.2 - y.1 * x.2)
  add_lie x y z := by
    apply Prod.ext
    · change (0 : k) = 0 + 0
      exact (zero_add 0).symm
    · change (x.1 + y.1) * z.2 - z.1 * (x.2 + y.2) =
        (x.1 * z.2 - z.1 * x.2) + (y.1 * z.2 - z.1 * y.2)
      ring
  lie_add x y z := by
    apply Prod.ext
    · change (0 : k) = 0 + 0
      exact (zero_add 0).symm
    · change x.1 * (y.2 + z.2) - (y.1 + z.1) * x.2 =
        (x.1 * y.2 - y.1 * x.2) + (x.1 * z.2 - z.1 * x.2)
      ring
  lie_self x := by
    apply Prod.ext
    · rfl
    · exact sub_self _
  leibniz_lie x y z := by
    apply Prod.ext
    · change (0 : k) = 0 + 0
      ring
    · change x.1 * (y.1 * z.2 - z.1 * y.2) - 0 * x.2 =
        (0 * z.2 - z.1 * (x.1 * y.2 - y.1 * x.2)) +
        (y.1 * (x.1 * z.2 - z.1 * x.2) - 0 * y.2)
      ring

instance : LieAlgebra k (AffineLie k) where
  lie_smul t x y := by
    apply Prod.ext
    · change (0 : k) = t * 0
      ring
    · change x.1 * (t * y.2) - (t * y.1) * x.2 =
        t * (x.1 * y.2 - y.1 * x.2)
      ring

def h : AffineLie k := (1, 0)
def e : AffineLie k := (0, 1)

/-- The line ke, specified by vanishing h-coordinate. -/
def lineIdeal : LieIdeal k (AffineLie k) where
  carrier := {x | x.1 = 0}
  zero_mem' := rfl
  add_mem' hx hy := by change _ + _ = (0 : k); rw [hx, hy, zero_add]
  smul_mem' t x hx := by change t * x.1 = 0; rw [hx, mul_zero]
  lie_mem := by intros; rfl

end LieAlgebrasAndRepresentations.Boundary

namespace Specs.LieAlgebrasAndRepresentations.NilpotentSolvableBoundary
open LieAlgebrasAndRepresentations.Boundary
open Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries

def derived_le_lower_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (r : ℕ),
    derivedSeries_value k L r ≤ lowerCentralSeries_value k L (r + 1)

def nilpotent_implies_solvable_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    LieRing.IsNilpotent L → LieAlgebra.IsSolvable L

/-- A basis with the specified vectors certifies dimension two. The ideal is
exactly ke; it and its quotient are abelian and nilpotent, while g is not nilpotent. -/
def affine_counterexample_type : Prop :=
  ∀ (k : Type u) [Field k],
    (∃ b : Basis (Fin 2) k (AffineLie k), b 0 = h k ∧ b 1 = e k) ∧
    ⁅h k, e k⁆ = e k ∧
    (lineIdeal k).toSubmodule = Submodule.span k {e k} ∧
    IsLieAbelian (lineIdeal k) ∧
    IsLieAbelian (AffineLie k ⧸ lineIdeal k) ∧
    LieRing.IsNilpotent (lineIdeal k) ∧
    LieRing.IsNilpotent (AffineLie k ⧸ lineIdeal k) ∧
    ¬ LieRing.IsNilpotent (AffineLie k)

end Specs.LieAlgebrasAndRepresentations.NilpotentSolvableBoundary
