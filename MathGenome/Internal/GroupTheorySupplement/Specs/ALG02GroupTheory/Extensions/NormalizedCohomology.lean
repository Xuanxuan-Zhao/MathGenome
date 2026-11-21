import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel

namespace ALG02GroupTheory.Extensions.NormalizedCohomology

universe u v

variable {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-- The inhomogeneous differential on one-cochains for the given left action. -/
def differential (a : Q → A) : (Q × Q → A) :=
  fun (q, r) => a q + q • a r - a (q * r)

/-- The inhomogeneous two-cocycle identity. -/
def IsTwoCocycle (c : Q × Q → A) : Prop :=
  ∀ q r t : Q, c (q, r) + c (q * r, t) = q • c (r, t) + c (q, r * t)

/-- Normalization at the identity in both arguments. -/
def IsNormalized (c : Q × Q → A) : Prop :=
  ∀ q : Q, c (1, q) = 0 ∧ c (q, 1) = 0

variable (Q A)

/-- The additive subgroup of inhomogeneous two-cocycles. -/
def twoCocycles : AddSubgroup (Q × Q → A) where
  carrier := {c | IsTwoCocycle c}
  zero_mem' := by
    change IsTwoCocycle (0 : Q × Q → A)
    intro q r t
    simp
  add_mem' := by
    intro c d (hc : IsTwoCocycle c) (hd : IsTwoCocycle d)
    change IsTwoCocycle (c + d)
    intro q r t
    simp only [Pi.add_apply, smul_add]
    rw [add_add_add_comm (c (q, r)), add_add_add_comm (q • c (r, t)), hc q r t, hd q r t]
  neg_mem' := by
    intro c (hc : IsTwoCocycle c)
    change IsTwoCocycle (-c)
    intro q r t
    simpa only [Pi.neg_apply, smul_neg, ← neg_add] using
      congrArg (fun x => -x) (hc q r t)

abbrev TwoCocycle := ↥(twoCocycles Q A)

variable {Q A}

private theorem differential_isTwoCocycle (a : Q → A) : IsTwoCocycle (differential a) := by
  intro q r t
  simp only [differential, smul_add, smul_sub, mul_smul, mul_assoc]
  abel

variable (Q A)

/-- The differential with codomain restricted to two-cocycles. -/
def coboundary : (Q → A) →+ TwoCocycle Q A :=
  (show (Q → A) →+ (Q × Q → A) from
    { toFun := differential
      map_zero' := by
        ext p
        rcases p with ⟨q, r⟩
        simp [differential]
      map_add' := by
        intro a b
        ext p
        rcases p with ⟨q, r⟩
        simp only [differential, Pi.add_apply, smul_add]
        abel }).codRestrict (twoCocycles Q A) differential_isTwoCocycle

/-- The subgroup of two-coboundaries inside the two-cocycles. -/
def twoCoboundaries : AddSubgroup (TwoCocycle Q A) := (coboundary Q A).range

/-- Second group cohomology in inhomogeneous coordinates. -/
abbrev H2 := TwoCocycle Q A ⧸ twoCoboundaries Q A

/-- The cohomology class of a two-cocycle. -/
abbrev classOf : TwoCocycle Q A →+ H2 Q A := QuotientAddGroup.mk' (twoCoboundaries Q A)

end ALG02GroupTheory.Extensions.NormalizedCohomology

namespace Specs.ALG02GroupTheory.Extensions.NormalizedCohomology

open _root_.ALG02GroupTheory.Extensions.NormalizedCohomology

universe u v

/-- Every class has a representative vanishing whenever either argument is the identity. -/
def NormalizedRepresentatives : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (x : H2 Q A), ∃ c : TwoCocycle Q A, IsNormalized c.val ∧ classOf Q A c = x

/-- Equality of normalized classes is difference by a normalized one-cochain's differential. -/
def NormalizedClassEquality : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (c d : TwoCocycle Q A), IsNormalized c.val → IsNormalized d.val →
      (classOf Q A c = classOf Q A d ↔
        ∃ a : Q → A, a 1 = 0 ∧ ∀ q r : Q, c.val (q, r) - d.val (q, r) = differential a (q, r))

end Specs.ALG02GroupTheory.Extensions.NormalizedCohomology
