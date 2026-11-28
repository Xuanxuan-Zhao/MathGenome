import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.PrincipalBlockDefect
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplittingSystem
import Mathlib.RingTheory.SimpleModule.Basic

namespace RepTheorySurvey.Modular.DefectZeroSpec

universe u v

/-- The defect groups of the principal block are precisely the Sylow
subgroups. An arbitrary block has defect zero exactly when its unital
block algebra is semisimple. -/
def principalBlocksAndDefectZeroType : Prop :=
  PrincipalBlockDefectSpec.principalBlockDefectType.{u, v} ∧
  ∀ {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (_ : MR01Spec.splitMatrixAlgebraValue k (MR01Spec.radicalQuotientValue k G))
    (b : BlockIdempotent k G),
    (∀ D : Subgroup G, DefectGroupsSpec.isDefectGroup p b D → D = ⊥) ↔
      IsSemisimpleRing b.Algebra

end RepTheorySurvey.Modular.DefectZeroSpec
