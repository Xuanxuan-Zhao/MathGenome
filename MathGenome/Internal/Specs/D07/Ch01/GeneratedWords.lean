import MathGenome.Internal.Specs.D07.Ch01.SubgroupLattice
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
Independent specification of `K07.01.generated_words`
(paper.tex:284–291; chapters/M07.01.tex:69–76).

The generated subgroup is the canonical `Subgroup.closure`, identified with
the source's intersection by the upstream specification. A word is a finite
ordered list of ambient group elements, each of which is a generator or the
inverse of a generator. Lists may be empty, with product `1`. The group and
generating set are arbitrary; no finiteness, commutativity, or nontriviality
is imposed.
-/

namespace Specs.D07.Ch01.GeneratedWords

universe u

/-- Membership in the generated subgroup is exactly representability by a
finite word in the generators and their inverses, allowing the empty word. -/
def MemGeneratedIffWord : Prop :=
  ∀ (G : Type u) [Group G] (S : Set G) (x : G),
    x ∈ Subgroup.closure S ↔
      ∃ w : List G, (∀ a ∈ w, a ∈ S ∨ ∃ s ∈ S, a = s⁻¹) ∧ w.prod = x

/-- Any predicate true on the generators and identity and closed under
multiplication and inverses holds on the whole generated subgroup. -/
def GenerationInduction : Prop :=
  ∀ (G : Type u) [Group G] (S : Set G) (P : G → Prop),
    (∀ s ∈ S, P s) → P 1 →
    (∀ x y : G, P x → P y → P (x * y)) →
    (∀ x : G, P x → P x⁻¹) →
    ∀ x ∈ Subgroup.closure S, P x

end Specs.D07.Ch01.GeneratedWords
