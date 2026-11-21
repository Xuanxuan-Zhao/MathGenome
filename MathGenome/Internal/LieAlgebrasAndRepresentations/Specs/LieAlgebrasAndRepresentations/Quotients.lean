import Mathlib.Algebra.Lie.Quotient

/-!
LA-A01, notes/005/lie-algebras-and-representations.tex, lines 173–198.
The canonical objects are Mathlib's `LieRing`, `LieAlgebra`, `LieSubalgebra`,
`LieIdeal` and `LieHom`. `LieRing` retains the alternating axiom, in all
characteristics. The cyclic-Jacobi/Leibniz bridge below checks the convention.
No dimension, characteristic, or nontriviality assumption on the Lie algebra
is imposed. The commutator example (lines 200–203) belongs to LA-U01.
-/

universe u v w

namespace Specs.LieAlgebrasAndRepresentations.Quotients

variable {k : Type u} [Field k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]
variable {H : Type w} [LieRing H] [LieAlgebra k H]

def jacobi_iff_leibniz_type :=
  ∀ {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (B : V →ₗ[k] V →ₗ[k] V) (hAlt : ∀ x, B x x = 0),
  (∀ x y z, B x (B y z) + B y (B z x) + B z (B x y) = 0) ↔
      (∀ x y z, B x (B y z) = B (B x y) z + B y (B x z))

def bracket_axioms_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] (x y z : L) (a : k),
  ⁅x, x⁆ = 0 ∧
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 ∧
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ ∧
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ ∧
    ⁅a • x, y⁆ = a • ⁅x, y⁆ ∧ ⁅x, a • y⁆ = a • ⁅x, y⁆

def subalgebra_iff_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] (S : Submodule k L),
  (∃ K : LieSubalgebra k L, K.toSubmodule = S) ↔
    ∀ x y : L, x ∈ S → y ∈ S → ⁅x, y⁆ ∈ S

def ideal_iff_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] (S : Submodule k L),
  (∃ I : LieIdeal k L, I.toSubmodule = S) ↔
    ∀ x y : L, y ∈ S → ⁅x, y⁆ ∈ S

def homomorphism_iff_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] {H : Type w} [LieRing H] [LieAlgebra k H] (F : L →ₗ[k] H),
  (∃ f : L →ₗ⁅k⁆ H, f.toLinearMap = F) ↔
    ∀ x y : L, F ⁅x, y⁆ = ⁅F x, F y⁆

def quotient_structure_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] (I : LieIdeal k L),
  LieAlgebra k (L ⧸ I)

noncomputable def quotient_structure_value (I : LieIdeal k L) : LieAlgebra k (L ⧸ I) :=
  LieSubmodule.Quotient.lieQuotientLieAlgebra I

def quotient_bracket_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] (I : LieIdeal k L) (x y : L),
  ⁅(LieSubmodule.Quotient.mk x : L ⧸ I), (LieSubmodule.Quotient.mk y : L ⧸ I)⁆ =
    LieSubmodule.Quotient.mk ⁅x, y⁆

def quotient_projection_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] (I : LieIdeal k L),
  ∃ q : L →ₗ⁅k⁆ L ⧸ I,
    (∀ x, q x = LieSubmodule.Quotient.mk x) ∧
    Function.Surjective q ∧ q.ker = I

def kernel_membership_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] {H : Type w} [LieRing H] [LieAlgebra k H] (f : L →ₗ⁅k⁆ H) (x : L),
  x ∈ f.ker ↔ f x = 0

def kernel_is_ideal_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] {H : Type w} [LieRing H] [LieAlgebra k H] (f : L →ₗ⁅k⁆ H) (x y : L) (hy : f y = 0),
  f ⁅x, y⁆ = 0

def range_membership_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] {H : Type w} [LieRing H] [LieAlgebra k H] (f : L →ₗ⁅k⁆ H) (y : H),
  y ∈ f.range ↔ ∃ x : L, f x = y

def range_is_subalgebra_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] {H : Type w} [LieRing H] [LieAlgebra k H] (f : L →ₗ⁅k⁆ H) (x y : H) (hx : x ∈ f.range) (hy : y ∈ f.range),
  ⁅x, y⁆ ∈ f.range

def first_isomorphism_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] {H : Type w} [LieRing H] [LieAlgebra k H] (f : L →ₗ⁅k⁆ H),
  (L ⧸ f.ker) ≃ₗ⁅k⁆ f.range

noncomputable def first_isomorphism_value (f : L →ₗ⁅k⁆ H) : (L ⧸ f.ker) ≃ₗ⁅k⁆ f.range :=
  f.quotKerEquivRange

def first_isomorphism_apply_type :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L] {H : Type w} [LieRing H] [LieAlgebra k H] (f : L →ₗ⁅k⁆ H) (x : L),
  (f.quotKerEquivRange (LieSubmodule.Quotient.mk x) : H) = f x

end Specs.LieAlgebrasAndRepresentations.Quotients
