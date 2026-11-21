import MathGenome.Internal.Specs.D07.Ch01.IsomorphismDefinition
import MathGenome.Internal.Specs.D07.Ch03.SubgroupProductCounting

/-!
Independent specification of K07.04.internal_direct_product
(paper.tex:777–783, chapters/M07.04.tex:118–124).

All groups are arbitrary, including trivial and infinite groups. Intersection
and the pointwise product are those of the original subgroups, and the forward
map of the isomorphism must be multiplication in the ambient group. The converse
uses the coordinate subgroups A × {1} and {1} × B of a binary external product.
-/
namespace Specs.D07.Ch04.InternalDirectProduct

open scoped Pointwise
universe u v

/-- Trivial intersection and normality imply elementwise commutation;
no hypothesis that the factors generate the ambient group is needed. -/
def NormalFactorsCommute : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
    H ⊓ K = ⊥ → ∀ (h : H) (k : K), Commute (h : G) (k : G)

/-- The multiplication map itself is an isomorphism, with the full source
hypotheses and no finiteness or commutativity assumption on the ambient group. -/
def MultiplicationIsomorphism : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
    H ⊓ K = ⊥ → (H : Set G) * (K : Set G) = Set.univ →
      ∃ e : H × K ≃* G, ∀ p : H × K, e p = (p.1 : G) * (p.2 : G)

/-- The coordinate subgroups of an arbitrary binary external product are
normal, have trivial intersection, multiply to the full group, and commute.
The carriers are exactly A × {1} and {1} × B. -/
def CoordinateSubgroups : Prop :=
  ∀ (A : Type u) (B : Type v) [Group A] [Group B],
    let H : Subgroup (A × B) := (⊤ : Subgroup A).prod (⊥ : Subgroup B)
    let K : Subgroup (A × B) := (⊥ : Subgroup A).prod (⊤ : Subgroup B)
    H.Normal ∧ K.Normal ∧ H ⊓ K = ⊥ ∧
      (H : Set (A × B)) * (K : Set (A × B)) = Set.univ ∧
      ∀ (h : H) (k : K), Commute (h : A × B) (k : A × B)

end Specs.D07.Ch04.InternalDirectProduct
