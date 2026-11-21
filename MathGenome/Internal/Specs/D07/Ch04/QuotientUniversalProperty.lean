import MathGenome.Internal.Specs.D07.Ch01.GroupNormalQuotient

/-!
Independent specification of K07.04.quotient_universal_property,
paper.tex:682–689 (Theorem `quotient-universal`).

The quotient and projection are the canonical ones from the upstream normal
quotient specification, whose fibers identify quotient elements with left
cosets. All groups are arbitrary, and every quotient operation explicitly
requires normality. Factorization means equality of bundled homomorphisms
after composition with the projection. The three statements record the
existence criterion, uniqueness, and the value on every representative.
-/

namespace Specs.D07.Ch04.QuotientUniversalProperty

universe u v

def FactorizationIff : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H),
    (∃ fbar : G ⧸ N →* H, fbar.comp (QuotientGroup.mk' N) = f) ↔ N ≤ f.ker

def FactorizationUnique : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H)
    (fbar₁ fbar₂ : G ⧸ N →* H),
    fbar₁.comp (QuotientGroup.mk' N) = f →
    fbar₂.comp (QuotientGroup.mk' N) = f → fbar₁ = fbar₂

def FactorizationFormula : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H) (fbar : G ⧸ N →* H),
    fbar.comp (QuotientGroup.mk' N) = f →
    ∀ g : G, fbar (QuotientGroup.mk' N g) = f g

end Specs.D07.Ch04.QuotientUniversalProperty
