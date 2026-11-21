import MathGenome.Internal.Specs.D07.Ch01.ElementaryGroupLaws
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Nat.Defs

/-!
Independent specification of `K07.01.homomorphism_definition`
(paper.tex:292–302). The source's unbundled definition requires only
multiplicativity. Identity and inverse preservation are conclusions for
arbitrary groups; they are not additional hypotheses on the function.
-/

namespace Specs.D07.Ch01.HomomorphismDefinition

universe u v

/-- The type of assignments of bundled homomorphism types to two groups. -/
def GroupHomType : Type (max u v + 1) :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H], Type (max u v)

def groupHomValue : GroupHomType.{u, v} := fun G H _ _ => G →* H

/-- A predicate on an ordinary function between arbitrary groups. -/
def MultiplicativePredicateType : Type (max u v + 1) :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H], (G → H) → Prop

def multiplicativePredicateValue : MultiplicativePredicateType.{u, v} :=
  fun G _ _ _ f => ∀ x y : G, f (x * y) = f x * f y

/-- The chosen bundled representation satisfies the source definition. -/
def HomMultiplicative : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    multiplicativePredicateValue G H f

/-- Multiplication preservation alone forces identity preservation. -/
def MapOneOfMultiplicative : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G → H),
    multiplicativePredicateValue G H f → f 1 = 1

/-- Multiplication preservation alone forces inverse preservation. -/
def MapInvOfMultiplicative : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G → H),
    multiplicativePredicateValue G H f → ∀ x : G, f (x⁻¹) = (f x)⁻¹

/-- Bundling loses no maps: the same underlying function can be bundled
exactly when it satisfies the source's multiplicativity condition. -/
def MultiplicativeIffBundled : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G → H),
    multiplicativePredicateValue G H f ↔
      ∃ F : G →* H, (F : G → H) = f

/-- Identity preservation does not follow for arbitrary monoids: the
multiplicative monoid of natural numbers supplies a counterexample. -/
def MonoidCounterexample : Prop :=
  ∃ f : ℕ → ℕ, (∀ x y : ℕ, f (x * y) = f x * f y) ∧ f 1 ≠ 1

end Specs.D07.Ch01.HomomorphismDefinition
