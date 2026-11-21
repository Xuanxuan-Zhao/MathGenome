import Mathlib.Algebra.Group.PUnit
import Mathlib.Basic.IsEmpty.Defs

/-!
Independent specification of `K07.01.group_definition` (paper.tex:220–229).
The canonical structures are Mathlib's `Group` and `CommGroup`. The explicit
axioms below also record both inverse laws from the source, without imposing
commutativity or nontriviality. Multiplication's codomain expresses closure.
-/

namespace Specs.D07.Ch01.GroupDefinition

universe u

/-- The type of assignments of a group-structure type to each carrier. -/
def GroupStructureType : Type (u + 1) := Type u → Type u

def groupStructureValue : GroupStructureType.{u} := fun G => Group G

def commGroupStructureValue : GroupStructureType.{u} := fun G => CommGroup G

/-- A predicate on the chosen multiplication, identity, and inverse. -/
def AxiomsPredicateType : Type (u + 1) :=
  (G : Type u) → (G → G → G) → G → (G → G) → Prop

def groupAxiomsValue : AxiomsPredicateType.{u} := fun G mul one inv =>
  (∀ x y z : G, mul (mul x y) z = mul x (mul y z)) ∧
  (∀ x : G, mul one x = x) ∧
  (∀ x : G, mul x one = x) ∧
  (∀ x : G, mul x (inv x) = one) ∧
  (∀ x : G, mul (inv x) x = one)

def AbelianPredicateType : Type (u + 1) := ∀ (G : Type u) [Group G], Prop

def abelianPredicateValue : AbelianPredicateType.{u} :=
  fun G _ => ∀ x y : G, x * y = y * x

/-- The canonical group structure satisfies every displayed source axiom. -/
def GroupLaws : Prop :=
  ∀ (G : Type u) [Group G], groupAxiomsValue G (· * ·) 1 Inv.inv

/-- Conversely, the displayed axioms give a canonical group structure with
exactly the supplied operations; there is no extra mathematical assumption. -/
def AxiomsRealized : Prop :=
  ∀ (G : Type u) (mul : G → G → G) (one : G) (inv : G → G),
    groupAxiomsValue G mul one inv →
      ∃ g : Group G, g.mul = mul ∧ g.one = one ∧ g.inv = inv

/-- Commutativity is precisely what allows a given group to be abelian. -/
def AbelianIffCommGroup : Prop :=
  ∀ (G : Type u) (g : Group G),
    @abelianPredicateValue G g ↔ ∃ c : CommGroup G, c.toGroup = g

def GroupNonempty : Prop := ∀ (G : Type u) [Group G], Nonempty G

/-- In particular, no empty carrier can support any group structure. -/
def EmptyHasNoGroup : Prop :=
  ∀ (G : Type u), IsEmpty G → ¬ Nonempty (Group G)

/-- The one-element carrier supports even an abelian group. -/
def TrivialGroupAllowed : Prop :=
  Nonempty (CommGroup PUnit.{u + 1}) ∧
    ∀ x y : PUnit.{u + 1}, x = y

end Specs.D07.Ch01.GroupDefinition
