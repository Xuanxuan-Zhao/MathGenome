import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplittingSystem
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RepresentationTheory.Character

/-! The ordinary character basis used in the spanning argument of MR05. -/

namespace RepTheorySurvey.Modular.OrdinaryCharacterBasisSpec

universe uK uG uI uV

/-- The group character of a group-algebra module with its restricted field action. -/
noncomputable def moduleCharacter {K : Type uK} [Field K] {G : Type uG} [Group G]
    (V : ModuleCat.{uV} (MonoidAlgebra K G)) : G → K :=
  @Representation.character G K (RestrictScalars K (MonoidAlgebra K G) (V : Type uV)) _ _ _
    (RestrictScalars.module K (MonoidAlgebra K G) (V : Type uV))
    (Representation.ofModule (k := K) (G := G) (V : Type uV))

/-- Over the given split field the characters of any complete irredundant family of
ordinary simple modules are a basis of all class functions. The module universe
contains the field universe so that it contains every simple matrix column. -/
def ordinaryCharacterBasisType : Prop :=
  ∀ {K : Type uK} [Field K] {G : Type uG} [Group G] [Finite G]
    {ι : Type uI} (V : ι → ModuleCat.{max uK uV} (MonoidAlgebra K G)),
    MR01Spec.splitMatrixAlgebraValue K (MonoidAlgebra K G) →
    MR01Spec.SimpleRepresentativeFamily V →
    ∃ b : Module.Basis ι K (ConjClasses G → K),
      ∀ i (g : G), b i (ConjClasses.mk g) = moduleCharacter (V i) g

end RepTheorySurvey.Modular.OrdinaryCharacterBasisSpec
