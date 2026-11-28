import Mathlib.Algebra.Module.Projective
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DefectGroups
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeDecompositionTwo
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeDecompositionThree

/-! The decomposition matrices, Cartan matrices and block defects of the symmetric group
of degree three at the primes two and three. -/

namespace RepTheorySurvey.Modular.SymmetricThree.ExampleSpec

universe u v

open IsLocalRing (ResidueField)

local notation "G" => Spec.GroupValue

/-- A projective cover is a projective module with a surjection such that only the entire
domain surjects onto the target. -/
def IsProjectiveCover {A : Type u} [Ring A] (P S : ModuleCat.{u} A) : Prop :=
  Module.Projective A P ∧
    ∃ f : P →ₗ[A] S, Function.Surjective f ∧
      ∀ U : Submodule A P, U.map f = ⊤ → U = ⊤

/-- Projective covers exist, and their composition multiplicities, with the column for
the cover of `S j` and the row for the factor `S i`, give the specified Cartan matrix. -/
def HasCartanMatrix {F : Type u} [Field F]
    (S : Fin 2 → ModuleCat.{u} (MonoidAlgebra F G)) (C : Matrix (Fin 2) (Fin 2) ℕ) : Prop :=
  (∃ P : Fin 2 → ModuleCat.{u} (MonoidAlgebra F G), ∀ j, IsProjectiveCover (P j) (S j)) ∧
  ∀ P : Fin 2 → ModuleCat.{u} (MonoidAlgebra F G), (∀ j, IsProjectiveCover (P j) (S j)) →
    ∀ i j, CompositionMultiplicity.Spec.multiplicity F G (P j) (S i) = C i j

/-- At two the modular columns are trivial and standard, and there are two blocks. -/
def atTwo : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K]
    (system : MR01Spec.SplittingSystemData G 2 O K),
    let k := ResidueField O
    let V := Spec.ordinaryFamilyValue K
    let S := DecompositionTwoSpec.modularFamilyValue k
    MR01Spec.SimpleRepresentativeFamily V ∧ MR01Spec.SimpleRepresentativeFamily S ∧
      MR06Spec.decompositionMatrixValue system V S = !![1, 0; 1, 0; 0, 1] ∧
      HasCartanMatrix S !![2, 0; 0, 1] ∧
      (∃ b bPrincipal : BlockIdempotent k G,
        bPrincipal.BelongsTo (Spec.trivialValue k).asModule ∧ b ≠ bPrincipal ∧
        (∀ d : BlockIdempotent k G, d = b ∨ d = bPrincipal) ∧
        (∀ P : Subgroup G, DefectGroupsSpec.isDefectGroup 2 b P ↔ P = ⊥) ∧
        (∀ P : Subgroup G, DefectGroupsSpec.isDefectGroup 2 bPrincipal P ↔
          ∃ Q : Sylow 2 G, (Q : Subgroup G) = P))

/-- At three the modular columns are trivial and sign, and there is one block. -/
def atThree : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K]
    (system : MR01Spec.SplittingSystemData G 3 O K),
    let k := ResidueField O
    let V := Spec.ordinaryFamilyValue K
    let S := DecompositionThreeSpec.modularFamilyValue k
    MR01Spec.SimpleRepresentativeFamily V ∧ MR01Spec.SimpleRepresentativeFamily S ∧
      MR06Spec.decompositionMatrixValue system V S = !![1, 0; 0, 1; 1, 1] ∧
      HasCartanMatrix S !![2, 1; 1, 2] ∧
      (∃ b : BlockIdempotent k G,
        b.BelongsTo (Spec.trivialValue k).asModule ∧
        (∀ d : BlockIdempotent k G, d = b) ∧
        ∃ Q : Sylow 3 G,
          (Q : Subgroup G) = Subgroup.zpowers Spec.threeCycleValue ∧
          Nat.card Q = 3 ∧
          ∀ P : Subgroup G, DefectGroupsSpec.isDefectGroup 3 b P ↔ P = (Q : Subgroup G))

end RepTheorySurvey.Modular.SymmetricThree.ExampleSpec
