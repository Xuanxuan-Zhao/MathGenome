import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Completion

/-! Residual finiteness and separation by finite quotients (GR02-C05.06). -/

namespace Specs.ALG02GroupTheory.Profinite

universe u

def ResiduallyFiniteIffFiniteHom : Prop :=
  ∀ (G : Type u) [Group G],
    Group.ResiduallyFinite G ↔
      ∀ g : G, g ≠ 1 →
        ∃ (H : Type u) (_ : Group H) (_ : Finite H) (f : G →* H), f g ≠ 1

def ResiduallyFiniteIffFiniteQuotient : Prop :=
  ∀ (G : Type u) [Group G],
    Group.ResiduallyFinite G ↔
      ∀ g : G, g ≠ 1 →
        ∃ N : FiniteIndexNormalSubgroup G, QuotientGroup.mk' N.toSubgroup g ≠ 1

def ResiduallyFiniteIffEtaInjective : Prop :=
  ∀ (G : Type u) [Group G],
    Group.ResiduallyFinite G ↔ Function.Injective (etaValue G)

def FiniteSubsetSeparatesInQuotient : Prop :=
  ∀ (G : Type u) [Group G], Group.ResiduallyFinite G →
    ∀ S : Set G, S.Finite →
      ∃ N : FiniteIndexNormalSubgroup G, Set.InjOn (QuotientGroup.mk' N.toSubgroup) S

def SubsingletonSubsetSeparatesInTrivialQuotient : Prop :=
  ∀ (G : Type u) [Group G] (S : Set G), S.Subsingleton →
    Set.InjOn (QuotientGroup.mk' (topIndexValue G).toSubgroup) S

end Specs.ALG02GroupTheory.Profinite
