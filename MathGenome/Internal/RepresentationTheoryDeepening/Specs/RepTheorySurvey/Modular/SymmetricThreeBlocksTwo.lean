import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.PrincipalBlockDefect
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeModules

namespace RepTheorySurvey.Modular.SymmetricThree.BlocksTwoSpec

universe u v

open IsLocalRing (ResidueField)

/-- The two blocks of the residual group algebra of (S₃) at (p = 2),
their actions on the reduced standard and trivial modules, and their defect groups. -/
def blocks : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData Spec.GroupValue 2 O K →
    let k := ResidueField O
    let c := Spec.threeCycleValue
    let basis := MonoidAlgebra.of k Spec.GroupValue
    ∃ b bPrincipal : BlockIdempotent k Spec.GroupValue,
      b.element = basis c + basis c⁻¹ ∧
      bPrincipal.element = 1 - b.element ∧
      b ≠ bPrincipal ∧
      (∀ b' : BlockIdempotent k Spec.GroupValue, b' = b ∨ b' = bPrincipal) ∧
      b.BelongsTo (Spec.standardValue k).asModule ∧
      (∀ m : (Spec.trivialValue k).asModule, b.element • m = 0) ∧
      bPrincipal.BelongsTo (Spec.trivialValue k).asModule ∧
      (∀ P : Subgroup Spec.GroupValue, DefectGroupsSpec.isDefectGroup 2 b P ↔ P = ⊥) ∧
      (∀ P : Subgroup Spec.GroupValue, DefectGroupsSpec.isDefectGroup 2 bPrincipal P ↔
        ∃ S : Sylow 2 Spec.GroupValue, (S : Subgroup Spec.GroupValue) = P)

end RepTheorySurvey.Modular.SymmetricThree.BlocksTwoSpec
