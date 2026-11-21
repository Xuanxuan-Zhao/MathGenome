import MathGenome.Internal.Specs.D07.Ch01.ElementaryGroupLaws
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Action.Pretransitive

/-!
Independent specification of `K07.05.action_definition` (paper.tex:819–820).
The carriers may be empty or infinite; neither group nor action is required
to be nontrivial. Transitivity includes nonemptiness, unlike pretransitivity.
-/

namespace Specs.D07.Ch05.ActionDefinition

universe u v

def ActionStructureType : Type (max (u + 1) (v + 1)) :=
  (G : Type u) → (X : Type v) → [Group G] → Type (max u v)

def actionStructureValue : ActionStructureType.{u, v} :=
  fun G X _ => MulAction G X

def AxiomsPredicateType : Type (max (u + 1) (v + 1)) :=
  (G : Type u) → (X : Type v) → [Group G] → (G → X → X) → Prop

def actionAxiomsValue : AxiomsPredicateType.{u, v} := fun G X _ act =>
  (∀ x : X, act (1 : G) x = x) ∧
  (∀ (g h : G) (x : X), act (g * h) x = act g (act h x))

def ActionPredicateType : Type (max (u + 1) (v + 1)) :=
  (G : Type u) → (X : Type v) → [Group G] → [MulAction G X] → Prop

/-- Equality of the acting maps forces equality of group elements. -/
def faithfulValue : ActionPredicateType.{u, v} := fun G X _ _ =>
  ∀ g h : G, (fun x : X => g • x) = (fun x : X => h • x) → g = h

/-- Only the identity can fix any specified point. -/
def freeValue : ActionPredicateType.{u, v} := fun G X _ _ =>
  ∀ (g : G) (x : X), g • x = x → g = 1

/-- A transitive set must be nonempty, and any point can be moved to any other. -/
def transitiveValue : ActionPredicateType.{u, v} := fun G X _ _ =>
  Nonempty X ∧ ∀ x y : X, ∃ g : G, g • x = y

def ActionLaws : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    actionAxiomsValue G X (fun g x => g • x)

/-- The two displayed axioms suffice to realize exactly the given action map. -/
def AxiomsRealized : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] (act : G → X → X),
    actionAxiomsValue G X act → ∃ a : MulAction G X, a.smul = act

def InverseAction : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (g : G),
    (∀ x : X, g⁻¹ • (g • x) = x) ∧ (∀ x : X, g • (g⁻¹ • x) = x)

def ActingMapsBijective : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (g : G),
    Function.Bijective (fun x : X => g • x)

def FaithfulIffFaithfulSMul : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    faithfulValue G X ↔ FaithfulSMul G X

def TransitiveIffNonemptyPretransitive : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    transitiveValue G X ↔ Nonempty X ∧ MulAction.IsPretransitive G X

def EmptyActionAllowed : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G], IsEmpty X → Nonempty (MulAction G X)

def EmptyNotTransitive : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    IsEmpty X → ¬ transitiveValue G X

/-- For every nontrivial group there is a trivial action on a singleton which
is transitive but neither faithful nor free. The map itself is also specified. -/
def SingletonCounterexample : Prop :=
  ∀ (G : Type u) [Group G] [Nontrivial G],
    ∃ a : MulAction G PUnit.{v + 1},
      (∀ (g : G) (x : PUnit.{v + 1}), a.smul g x = x) ∧
      @transitiveValue G PUnit _ a ∧
      ¬ @faithfulValue G PUnit _ a ∧ ¬ @freeValue G PUnit _ a

end Specs.D07.Ch05.ActionDefinition
