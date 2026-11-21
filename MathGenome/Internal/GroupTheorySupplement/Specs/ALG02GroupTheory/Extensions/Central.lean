import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.IsPerfect

/-! Independent specifications for the definitions in paper.tex:663–667. -/

namespace Specs.ALG02GroupTheory.Extensions

universe u v w t u' v'

-- The types retain the separate universes used by the exact extension model.
set_option linter.checkUnivs false in
def ExtensionPredicateType :=
  ∀ {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G],
    GroupExtension N E G → Prop

def isCentralExtensionValue : ExtensionPredicateType.{u, v, w} :=
  fun {_ E _} _ _ _ S => S.inl.range ≤ Subgroup.center E

-- The comparison universe is a parameter of the universal property.
set_option linter.checkUnivs false in
/-- The target kernel and middle group are quantified independently in a common universe. -/
def isUniversalCentralExtensionValue : ExtensionPredicateType.{u, v, w} :=
  fun {_ E G} _ _ _ S =>
    isCentralExtensionValue S ∧
      ∀ {K D : Type (max v w t)} [Group K] [Group D] (T : GroupExtension K D G),
        isCentralExtensionValue T →
          ∃! f : E →* D, T.rightHom.comp f = S.rightHom

def IsPerfectType := ∀ (G : Type w) [Group G], Prop

def isPerfectValue : IsPerfectType.{w} := fun G _ => Group.IsPerfect G

def IsPerfectIff : Prop :=
  ∀ (G : Type w) [Group G], isPerfectValue G ↔ commutator G = ⊤

def IsCentralExtensionIffKerLeCenter : Prop :=
  ∀ {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G),
    isCentralExtensionValue S ↔ S.rightHom.ker ≤ Subgroup.center E

/-- The common-universe property applies to target groups in two separate universes. -/
def ExistsUniqueHomOver : Prop :=
  ∀ {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]
    {S : GroupExtension N E G} {K : Type u'} {D : Type v'} [Group K] [Group D]
    (_ : isUniversalCentralExtensionValue.{u, v, w, max t u' v'} S) (T : GroupExtension K D G),
    isCentralExtensionValue T →
      ∃! f : E →* D, T.rightHom.comp f = S.rightHom

/-- The same universality hypothesis applies to every central extension over the prescribed base,
with no restriction relating the target universes to the comparison universe. -/
def ExistsUniqueHomOverArbitrary : Prop :=
  ∀ {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]
    {S : GroupExtension N E G} {K : Type u'} {D : Type v'} [Group K] [Group D]
    (_ : isUniversalCentralExtensionValue.{u, v, w, t} S) (T : GroupExtension K D G),
    isCentralExtensionValue T →
      ∃! f : E →* D, T.rightHom.comp f = S.rightHom

end Specs.ALG02GroupTheory.Extensions
