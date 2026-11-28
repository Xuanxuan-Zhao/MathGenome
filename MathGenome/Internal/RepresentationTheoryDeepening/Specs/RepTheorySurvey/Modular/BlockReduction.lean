import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DecompositionMatrix
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.ModularBlocks

/-! Independent specifications for block compatibility with lattice reduction (MR08). -/

namespace RepTheorySurvey.Modular.MR08Spec

universe uG uO uK uV uS

open IsLocalRing (ResidueField)

set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

/-- The integral group-algebra action on a stable lattice restricts the fraction-field action. -/
def latticeAlgebraAction : Prop :=
  ∀ {O : Type uO} [CommRing O] {K : Type uK} [Field K] [Algebra O K]
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    (L : MR04LatticeSpec.NativeLatticeData O K G V) (a : MonoidAlgebra O G),
    letI : Module O (RestrictScalars K (MonoidAlgebra K G) V) := Module.restrictScalars O K _
    letI : IsScalarTower O K (RestrictScalars K (MonoidAlgebra K G) V) :=
      IsScalarTower.restrictScalars O K _
    ∀ x : L.carrier,
      RestrictScalars.addEquiv K (MonoidAlgebra K G) V
        ((MR04LatticeSpec.integralAction O L).asAlgebraHom a x).val =
      MR01Spec.fractionMapValue O K G a • RestrictScalars.addEquiv K (MonoidAlgebra K G) V x.val

/-- If an integral block acts as identity on an ordinary module, its residual block
acts as identity on the reduction of every stable lattice in that module. -/
def blockActsOnReduction : Prop :=
  ∀ {O : Type uO} [CommRing O] [IsLocalRing O] {K : Type uK} [Field K] [Algebra O K]
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    (b : BlockIdempotent O G) (bResidue : BlockIdempotent (ResidueField O) G),
    MR01Spec.reductionValue O G b.element = bResidue.element →
    (∀ v : V, MR01Spec.fractionMapValue O K G b.element • v = v) →
    ∀ L : MR04LatticeSpec.NativeLatticeData O K G V,
      bResidue.BelongsTo (MR04LatticeSpec.nativeReduction L)

/-- An ordinary simple in a lifted block has zero decomposition coefficient at every
modular simple outside the corresponding residual block. -/
def decompositionMultiplicityZero : Prop :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (system : MR01Spec.SplittingSystemData G p O K)
    (V : Type uV) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [IsSimpleModule (MonoidAlgebra K G) V]
    (S : Type uS) [AddCommGroup S] [Module (MonoidAlgebra (ResidueField O) G) S]
    [IsSimpleModule (MonoidAlgebra (ResidueField O) G) S]
    (b : BlockIdempotent O G) (bResidue : BlockIdempotent (ResidueField O) G),
    MR01Spec.reductionValue O G b.element = bResidue.element →
    (∀ v : V, MR01Spec.fractionMapValue O K G b.element • v = v) →
    ¬ bResidue.BelongsTo S →
    MR06Spec.decompositionMultiplicityValue system V S = 0

end RepTheorySurvey.Modular.MR08Spec
