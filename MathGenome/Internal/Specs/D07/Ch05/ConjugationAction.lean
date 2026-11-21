import MathGenome.Internal.Specs.D07.Ch05.ActionDefinition
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
Independent specification of `K07.05.conjugation_action`, paper.tex:874–876.
The action is on the underlying set of an arbitrary group, including trivial
and infinite groups. The explicitly selected action prevents confusion with
the usual action of a group on itself by left multiplication.
-/

namespace Specs.D07.Ch05.ConjugationAction

universe u

def ConjugationActionType : Type (u + 1) :=
  ∀ (G : Type u) [Group G], MulAction G G

/-- Shared canonical action with the source's precise formula. -/
def conjugationActionValue : ConjugationActionType.{u} := fun G _ =>
  { smul := fun g x => g * x * g⁻¹
    one_smul := by
      intro x
      change (1 : G) * x * (1 : G)⁻¹ = x
      simp
    mul_smul := by
      intro g h x
      change (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹
      simp [mul_assoc] }

def ConjugationFormula : Prop :=
  ∀ (G : Type u) [Group G] (g x : G),
    (conjugationActionValue G).smul g x = g * x * g⁻¹

def ConjugationLaws : Prop :=
  ∀ (G : Type u) [Group G],
    ActionDefinition.actionAxiomsValue G G (conjugationActionValue G).smul

def OrbitCarrier : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    @MulAction.orbit G G (conjugationActionValue G).toSMul x = {y : G | ∃ g : G, g * x * g⁻¹ = y}

def OrbitEqualsConjugacyClass : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    @MulAction.orbit G G (conjugationActionValue G).toSMul x = (ConjClasses.mk x).carrier

def StabilizerCarrier : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    letI : MulAction G G := conjugationActionValue G
    (MulAction.stabilizer G x : Set G) = {g : G | g * x = x * g}

def StabilizerEqualsCentralizer : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    letI : MulAction G G := conjugationActionValue G
    MulAction.stabilizer G x = Subgroup.centralizer {x}

def FixedPointsCarrier : Prop :=
  ∀ (G : Type u) [Group G],
    letI : MulAction G G := conjugationActionValue G
    MulAction.fixedPoints G G = {x : G | ∀ g : G, g * x = x * g}

def FixedPointsEqualsCenter : Prop :=
  ∀ (G : Type u) [Group G],
    letI : MulAction G G := conjugationActionValue G
    MulAction.fixedPoints G G = (Subgroup.center G : Set G)

end Specs.D07.Ch05.ConjugationAction
