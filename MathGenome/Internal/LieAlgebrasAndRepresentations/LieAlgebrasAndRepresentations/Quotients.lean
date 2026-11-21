import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Quotients
import Mathlib.Tactic.Abel

/-!
LA-A01, notes/005/lie-algebras-and-representations.tex, lines 173–198.
The canonical objects are Mathlib's `LieRing`, `LieAlgebra`, `LieSubalgebra`,
`LieIdeal` and `LieHom`. `LieRing` retains the alternating axiom, in all
characteristics. The cyclic-Jacobi/Leibniz bridge below checks the convention.
No dimension, characteristic, or nontriviality assumption on the Lie algebra
is imposed. The commutator example (lines 200–203) belongs to LA-U01.
-/

universe u v w

namespace LieAlgebrasAndRepresentations

variable {k : Type u} [Field k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]
variable {H : Type w} [LieRing H] [LieAlgebra k H]

theorem jacobi_iff_leibniz {V : Type v} [AddCommGroup V] [Module k V]
    (B : V →ₗ[k] V →ₗ[k] V) (hAlt : ∀ x, B x x = 0) :
    (∀ x y z, B x (B y z) + B y (B z x) + B z (B x y) = 0) ↔
      (∀ x y z, B x (B y z) = B (B x y) z + B y (B x z)) := by
  have skew (x y : V) : B x y = -B y x := by
    have h := hAlt (x + y)
    simp only [map_add, LinearMap.add_apply, hAlt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
  constructor
  · intro h x y z
    have h := h x y z
    rw [skew z x, map_neg, skew z (B x y)] at h
    apply sub_eq_zero.mp
    calc
      B x (B y z) - (B (B x y) z + B y (B x z)) =
          B x (B y z) + -B y (B x z) + -B (B x y) z := by abel
      _ = 0 := h
  · intro h x y z
    rw [h x y z, skew z x, map_neg, skew z (B x y)]
    abel

theorem bracket_axioms (x y z : L) (a : k) :
    ⁅x, x⁆ = 0 ∧
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 ∧
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ ∧
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ ∧
    ⁅a • x, y⁆ = a • ⁅x, y⁆ ∧ ⁅x, a • y⁆ = a • ⁅x, y⁆ :=
  ⟨lie_self x, lie_jacobi x y z, add_lie x y z, lie_add x y z,
    smul_lie a x y, lie_smul a x y⟩

theorem subalgebra_iff (S : Submodule k L) :
    (∃ K : LieSubalgebra k L, K.toSubmodule = S) ↔
    ∀ x y : L, x ∈ S → y ∈ S → ⁅x, y⁆ ∈ S :=
  Submodule.exists_lieSubalgebra_coe_eq_iff S

theorem ideal_iff (S : Submodule k L) :
    (∃ I : LieIdeal k L, I.toSubmodule = S) ↔
    ∀ x y : L, y ∈ S → ⁅x, y⁆ ∈ S :=
  Submodule.exists_lieSubmodule_coe_eq_iff (L := L) S

theorem homomorphism_iff (F : L →ₗ[k] H) :
    (∃ f : L →ₗ⁅k⁆ H, f.toLinearMap = F) ↔
    ∀ x y : L, F ⁅x, y⁆ = ⁅F x, F y⁆ := by
  constructor
  · rintro ⟨f, rfl⟩ x y
    exact f.map_lie x y
  · intro h
    exact ⟨{ F with map_lie' := h _ _ }, rfl⟩

def quotient_structure (I : LieIdeal k L) :
    LieAlgebra k (L ⧸ I) :=
  LieSubmodule.Quotient.lieQuotientLieAlgebra I

theorem quotient_bracket (I : LieIdeal k L) (x y : L) :
    ⁅(LieSubmodule.Quotient.mk x : L ⧸ I), (LieSubmodule.Quotient.mk y : L ⧸ I)⁆ =
    LieSubmodule.Quotient.mk ⁅x, y⁆ :=
  (LieSubmodule.Quotient.mk_bracket I x y).symm

theorem quotient_projection (I : LieIdeal k L) :
    ∃ q : L →ₗ⁅k⁆ L ⧸ I,
    (∀ x, q x = LieSubmodule.Quotient.mk x) ∧
    Function.Surjective q ∧ q.ker = I := by
  let q : L →ₗ⁅k⁆ L ⧸ I :=
    { I.toSubmodule.mkQ with map_lie' := by intros; rfl }
  refine ⟨q, fun _ => rfl, ?_, ?_⟩
  · exact Quot.mk_surjective
  · ext x
    exact LieSubmodule.Quotient.mk_eq_zero'

theorem kernel_membership (f : L →ₗ⁅k⁆ H) (x : L) :
    x ∈ f.ker ↔ f x = 0 :=
  LieHom.mem_ker

theorem kernel_is_ideal (f : L →ₗ⁅k⁆ H) (x y : L) (hy : f y = 0) :
    f ⁅x, y⁆ = 0 :=
  by rw [f.map_lie, hy, lie_zero]

theorem range_membership (f : L →ₗ⁅k⁆ H) (y : H) :
    y ∈ f.range ↔ ∃ x : L, f x = y :=
  f.mem_range y

theorem range_is_subalgebra (f : L →ₗ⁅k⁆ H) (x y : H) (hx : x ∈ f.range) (hy : y ∈ f.range) :
    ⁅x, y⁆ ∈ f.range :=
  f.range.lie_mem hx hy

noncomputable def first_isomorphism (f : L →ₗ⁅k⁆ H) :
    (L ⧸ f.ker) ≃ₗ⁅k⁆ f.range :=
  f.quotKerEquivRange

theorem first_isomorphism_apply (f : L →ₗ⁅k⁆ H) (x : L) :
    (first_isomorphism f (LieSubmodule.Quotient.mk x) : H) = f x :=
  rfl

end LieAlgebrasAndRepresentations
