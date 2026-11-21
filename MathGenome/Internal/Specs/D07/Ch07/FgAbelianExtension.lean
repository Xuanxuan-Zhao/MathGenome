import MathGenome.Internal.Specs.D07.Ch07.ClassificationDataConversion
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Rat.Defs

/-! Independent statements of K07.07.fg_abelian_extension, paper.tex:3501–3520.
Finite products represent finite direct sums. The existing invariant-factor
model includes the empty list; `IsInvariant` excludes factors of order one.
No finiteness is imposed on an abelian group except in the existence theorem.
-/
namespace Specs.D07.Ch07.FgAbelianExtension

universe u
open D07.Ch07.ClassificationDataConversion

abbrev Model (r : ℕ) (d : List ℕ) := (Fin r → ℤ) × InvariantGroup d

/-- Existence with the usual group-theoretic finite generation hypothesis. -/
def Existence : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [AddGroup.FG A],
    ∃ (r : ℕ) (d : List ℕ), IsInvariant d ∧ Nonempty (A ≃+ Model r d)

/-- The free coordinates vanish precisely on the intrinsic torsion subgroup.
The restriction to torsion identifies it with the displayed finite part. -/
def TorsionDescription : Prop :=
  ∀ (A : Type u) [AddCommGroup A] (r : ℕ) (d : List ℕ), IsInvariant d →
    ∀ E : A ≃+ Model r d,
      (∀ a : A, a ∈ AddCommGroup.torsion A ↔ (E a).1 = 0) ∧
      ∃ F : AddCommGroup.torsion A ≃+ InvariantGroup d,
        ∀ a, F a = (E a.val).2

/-- Projection onto the free coordinates induces the quotient isomorphism. -/
def QuotientDescription : Prop :=
  ∀ (A : Type u) [AddCommGroup A] (r : ℕ) (d : List ℕ), IsInvariant d →
    ∀ E : A ≃+ Model r d,
      ∃ F : (A ⧸ AddCommGroup.torsion A) ≃+ (Fin r → ℤ),
        ∀ a, F (QuotientAddGroup.mk a) = (E a).1

/-- Uniqueness includes both the rank and literal equality of normalized lists. -/
def Uniqueness : Prop :=
  ∀ (r r' : ℕ) (d e : List ℕ), IsInvariant d → IsInvariant e →
    (Model r d ≃+ Model r' e) → r = r' ∧ d = e

def FinitenessCriterion : Prop :=
  ∀ (A : Type u) [AddCommGroup A] (r : ℕ) (d : List ℕ), IsInvariant d →
    (A ≃+ Model r d) → (Finite A ↔ r = 0)

/-- A common positive denominator bounds every integer linear combination. -/
def RationalCommonDenominator : Prop :=
  ∀ l : List ℚ, ∃ d : ℕ, 0 < d ∧
    ∀ q ∈ AddSubgroup.closure (l.toFinset : Set ℚ),
      ∃ m : ℤ, q = (m : ℚ) / (d : ℚ)

/-- The next half-step cannot be an integer multiple of 1/d. -/
def RationalDenominatorObstruction : Prop :=
  ∀ d : ℕ, 0 < d → ¬ ∃ m : ℤ,
    (1 : ℚ) / (2 * (d : ℚ)) = (m : ℚ) / (d : ℚ)

def RationalNotFinitelyGenerated : Prop := ¬ AddGroup.FG ℚ

end Specs.D07.Ch07.FgAbelianExtension
