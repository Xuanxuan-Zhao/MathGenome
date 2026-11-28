import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.SimpleModule.Basic

open scoped MonoidAlgebra

universe u v w

namespace RepTheorySurvey.Modular.Specs

/-- A primitive idempotent in a commutative ring has no nonzero orthogonal splitting. -/
def primitiveIdempotent {C : Type*} [CommRing C] (b : C) : Prop :=
  IsIdempotentElem b ∧ b ≠ 0 ∧
    ∀ x y : C, IsIdempotentElem x → IsIdempotentElem y → x * y = 0 →
      x + y = b → x = 0 ∨ y = 0

/-- The block idempotents of the group algebra, represented in its center. -/
def blockIdempotent (R : Type u) (G : Type v) [CommRing R] [Group G] : Type (max u v) :=
  {b : Subalgebra.center R R[G] // primitiveIdempotent b}

end RepTheorySurvey.Modular.Specs

namespace RepTheorySurvey.Modular

/-- A nonzero primitive central idempotent of the coefficient group algebra. -/
abbrev BlockIdempotent := @Specs.blockIdempotent

namespace BlockIdempotent

variable {R : Type u} {G : Type v} [CommRing R] [Group G]

/-- The idempotent as an element of the group algebra. -/
def element (b : BlockIdempotent R G) : R[G] := b.1.1

theorem center_idempotent (b : BlockIdempotent R G) : IsIdempotentElem b.1 := b.2.1

theorem idempotent (b : BlockIdempotent R G) : IsIdempotentElem b.element :=
  b.center_idempotent.map (Subalgebra.center R R[G]).val

theorem central (b : BlockIdempotent R G) : IsMulCentral b.element := b.1.2

end BlockIdempotent

namespace Specs

variable {R : Type u} {G : Type v} [CommRing R] [Group G]

abbrev blockAlgebra (b : BlockIdempotent R G) : Type (max u v) := b.idempotent.Corner

abbrev blockCenter (b : BlockIdempotent R G) : Type (max u v) := b.center_idempotent.Corner

def belongsTo (b : BlockIdempotent R G) (M : Type w) [AddCommGroup M] [Module R[G] M] :
    Prop := ∀ m : M, b.element • m = m

end Specs

namespace BlockIdempotent

variable {R : Type u} {G : Type v} [CommRing R] [Group G]

/-- The block algebra with unit given by the block idempotent. -/
abbrev Algebra := @Specs.blockAlgebra

/-- The corner cut out by a block idempotent in the center of the group algebra. -/
abbrev Center := @Specs.blockCenter

/-- The projection to the block algebra sends `a` to `a * b`. -/
noncomputable def projection (b : BlockIdempotent R G) : R[G] →+* b.Algebra where
  toFun a := ⟨a * b.element,
    (Subsemigroup.mem_corner_iff_mem_range_mul_right b.idempotent b.central).mpr ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (zero_mul _)
  map_one' := Subtype.ext (one_mul _)
  map_add' a c := Subtype.ext (add_mul a c _)
  map_mul' a c := Subtype.ext <| by
    change (a * c) * b.element = (a * b.element) * (c * b.element)
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, (b.central.comm c).eq, mul_assoc, b.idempotent.eq]

noncomputable instance (b : BlockIdempotent R G) : _root_.Algebra R b.Algebra :=
  (b.projection.comp (algebraMap R R[G])).toAlgebra' fun r x => by
    let a := algebraMap R R[G] r
    let y := x.1
    have hy := (Subsemigroup.mem_corner_iff b.idempotent).mp x.2
    apply Subtype.ext
    change (a * b.element) * y = y * (a * b.element)
    calc
      (a * b.element) * y = a * (b.element * y) := mul_assoc ..
      _ = a * y := congrArg (a * ·) hy.1
      _ = y * a := _root_.Algebra.commutes r y
      _ = (y * b.element) * a := congrArg (· * a) hy.2.symm
      _ = y * (a * b.element) := by rw [mul_assoc, (b.central.comm a).eq]

/-- The left regular action on the block, restricted along its projection. -/
noncomputable instance (b : BlockIdempotent R G) : Module R[G] b.Algebra :=
  Module.compHom b.Algebra b.projection

/-- A left group-algebra module belongs to the block if the idempotent acts as identity. -/
abbrev BelongsTo := @Specs.belongsTo

end BlockIdempotent

namespace Specs

/-- The usual augmentation of a group algebra, extending the trivial character. -/
noncomputable def augmentation (R : Type u) (G : Type v) [CommRing R] [Group G] :
    R[G] →ₐ[R] R := MonoidAlgebra.lift R R G 1

/-- A total center-valued formula selecting the primitive idempotent of augmentation one. -/
noncomputable def principal (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] :
    Subalgebra.center k k[G] := by
  classical
  exact if h : ∃ b : BlockIdempotent k G, augmentation k G b.element = 1 then h.choose.1 else 0

def primitive_idempotent_type : Type _ := ∀ {C : Type u} [CommRing C], C → Prop

set_option linter.checkUnivs false in
def augmentation_type : Type _ :=
  ∀ (R : Type u) (G : Type v) [CommRing R] [Group G], R[G] →ₐ[R] R

set_option linter.checkUnivs false in
def principal_idempotent_type : Type _ :=
  ∀ (k : Type u) (G : Type v) [Field k] [Group G] [Finite G], Subalgebra.center k k[G]

def corner_mem_type : Prop :=
  ∀ {R : Type u} {G : Type v} [CommRing R] [Group G] (b : BlockIdempotent R G) (a : R[G]),
    a ∈ Subsemigroup.corner b.element ↔ ∃ x : R[G], x * b.element = a

def corner_ideal_type : Prop :=
  ∀ {R : Type u} {G : Type v} [CommRing R] [Group G] (b : BlockIdempotent R G) (a : R[G]),
    a ∈ Subsemigroup.corner b.element ↔ a ∈ Ideal.span {b.element}

def corner_smul_type : Prop :=
  ∀ {R : Type u} {G : Type v} [CommRing R] [Group G] (b : BlockIdempotent R G) (a : R[G])
    (x : b.Algebra), (a • x).1 = a * x.1

def corner_one_type : Prop :=
  ∀ {R : Type u} {G : Type v} [CommRing R] [Group G] (b : BlockIdempotent R G),
    (1 : b.Algebra).1 = b.element

def blocks_type : Prop :=
  ∀ (k : Type u) (G : Type v) [Field k] [Group G] [Finite G],
    ∃ s : Finset (BlockIdempotent k G), (∀ b, b ∈ s) ∧
      (∑ b ∈ s, b.element) = 1 ∧
      Pairwise (fun b c : BlockIdempotent k G => b.element * c.element = 0)

def finite_type : Prop :=
  ∀ (k : Type u) (G : Type v) [Field k] [Group G] [Finite G], Finite (BlockIdempotent k G)

def local_type : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
    (b : BlockIdempotent k G), IsLocalRing b.Center

def simple_membership_type : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
    (M : Type w) [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M],
    ∃! b : BlockIdempotent k G, b.BelongsTo M

def simple_quotient_type : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G]
    (b : BlockIdempotent k G),
    ∃ N : Submodule k[G] b.Algebra,
      IsSimpleModule k[G] (b.Algebra ⧸ N) ∧ b.BelongsTo (b.Algebra ⧸ N)

def augmentation_coefficients_type : Prop :=
  ∀ {R : Type u} {G : Type v} [CommRing R] [Group G] [Fintype G] (x : R[G]),
    augmentation R G x = ∑ g : G, x.coeff g

def trivial_membership_type : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (b : BlockIdempotent k G),
    b.BelongsTo (Representation.trivial k G k).asModule ↔ augmentation k G b.element = 1

def principal_unique_type : Prop :=
  ∀ (k : Type u) (G : Type v) [Field k] [Group G] [Finite G],
    ∃! b : BlockIdempotent k G, b.BelongsTo (Representation.trivial k G k).asModule

def principal_type : Prop :=
  ∀ (k : Type u) (G : Type v) [Field k] [Group G] [Finite G],
    ∃ b : BlockIdempotent k G,
      b.1 = principal k G ∧ b.BelongsTo (Representation.trivial k G k).asModule

def principal_augmentation_type : Prop :=
  ∀ (k : Type u) (G : Type v) [Field k] [Group G] [Finite G],
    augmentation k G (principal k G : k[G]) = 1

end Specs

end RepTheorySurvey.Modular
