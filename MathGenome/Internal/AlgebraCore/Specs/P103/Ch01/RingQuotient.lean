import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.Congruence.Hom

/-! The quotient of an associative unital ring by a two-sided ideal.
No nontriviality or commutativity assumption is imposed. -/
namespace P103.Ch01.RingQuotient

universe u v

/-- Cosets for the relation `x - y ∈ I`, with the canonical quotient ring structure.
The underlying additive group is the quotient by `I.ringCon.toAddCon`. -/
abbrev Cosets {R : Type u} [Ring R] (I : TwoSidedIdeal R) := I.ringCon.Quotient

/-- The canonical unital projection. -/
def projection {R : Type u} [Ring R] (I : TwoSidedIdeal R) : R →+* Cosets I :=
  I.ringCon.mk'

/-- A possibly different ring structure on the same quotient set makes the
set-theoretic projection a unital ring map. -/
def ProjectionIsUnital {R : Type u} [Ring R] (I : TwoSidedIdeal R)
    (A : Ring (Cosets I)) : Prop :=
  ∃ p : @RingHom R (Cosets I) inferInstance A.toNonAssocSemiring,
    ∀ r, p r = I.ringCon.toQuotient r

namespace Specs

/-- Identifies the classes with the original additive quotient, including its
surjective projection and its addition on representatives. -/
def Classes : Prop :=
  ∀ (R : Type u) [Ring R] (I : TwoSidedIdeal R),
    Function.Surjective (projection I) ∧
    (∀ x y, projection I x = projection I y ↔ x - y ∈ I) ∧
    (∀ x y, projection I (x + y) = projection I x + projection I y)

/-- Existence and equality, not just isomorphism, of the ring structure. -/
def RingStructure : Prop :=
  ∀ (R : Type u) [Ring R] (I : TwoSidedIdeal R),
    ∃! A : Ring (Cosets I), ProjectionIsUnital I A

/-- The universal property for unital maps and two-sided ideals. -/
def Factorization : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type v) [Ring S]
    (I : TwoSidedIdeal R) (f : R →+* S),
    (∃! g : Cosets I →+* S, g.comp (projection I) = f) ↔ I ≤ TwoSidedIdeal.ker f

/-- The quotient by the full ideal is the zero ring. -/
def FullIdealQuotient : Prop :=
  ∀ (R : Type u) [Ring R], Subsingleton (Cosets (⊤ : TwoSidedIdeal R))

/-- A unital factorization through `R/R` exists exactly when the target is zero. -/
def FullIdealFactorization : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type v) [Ring S] (f : R →+* S),
    (∃! g : Cosets (⊤ : TwoSidedIdeal R) →+* S,
      g.comp (projection (⊤ : TwoSidedIdeal R)) = f) ↔ Subsingleton S

end Specs
end P103.Ch01.RingQuotient
