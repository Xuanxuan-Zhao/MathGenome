import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DefectGroups

namespace RepTheorySurvey.Modular.PrincipalBlockDefectSpec

universe u v

/-- The defect groups of the block of the trivial representation are precisely
the Sylow subgroups at the characteristic of the coefficient field. -/
def principalBlockDefectType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP k p] (b : BlockIdempotent k G),
    b.BelongsTo (Representation.trivial k G k).asModule →
    ∀ P : Subgroup G, DefectGroupsSpec.isDefectGroup p b P ↔
      ∃ S : Sylow p G, (S : Subgroup G) = P

end RepTheorySurvey.Modular.PrincipalBlockDefectSpec
