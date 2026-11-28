import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.BrauerCharacterLaws
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.StableLattices

/-! The character equality for reduction of every stable lattice in MR04. -/

namespace RepTheorySurvey.Modular.MR04Spec

universe uG uO uK uV uU uN

open IsLocalRing (ResidueField)

set_option backward.isDefEq.respectTransparency false

/-- Converting a representation to a group-algebra module and restricting scalars
recovers its original scalar space. -/
noncomputable def asModuleScalarEquiv {F G W : Type*} [Field F] [Group G]
    [AddCommGroup W] [Module F W] (ρ : Representation F G W) :
    RestrictScalars F (MonoidAlgebra F G) ρ.asModule ≃ₗ[F] W where
  toAddEquiv := (RestrictScalars.addEquiv F (MonoidAlgebra F G) ρ.asModule).trans
    ρ.asModuleEquiv.toAddEquiv
  map_smul' r x := by
    change ρ.asModuleEquiv (RestrictScalars.addEquiv F (MonoidAlgebra F G) ρ.asModule
      (r • x)) = r • ρ.asModuleEquiv (RestrictScalars.addEquiv F (MonoidAlgebra F G)
        ρ.asModule x)
    rw [RestrictScalars.addEquiv_map_smul, Representation.asModuleEquiv_map_smul,
      AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]
    rfl

section FiniteReduction

variable {G : Type uG} [Group G]
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K]
  (V : Type uV) [AddCommGroup V] [Module (MonoidAlgebra K G) V]

local notation "k" => ResidueField O
local notation "kG" => MonoidAlgebra k G

/-- The canonical reduction of a finite lattice is finite dimensional over the residue field. -/
theorem nativeReductionFinite (L : MR04LatticeSpec.NativeLatticeData O K G V) :
    Module.Finite k (RestrictScalars k kG (MR04LatticeSpec.nativeReduction L)) := by
  let : Module O (RestrictScalars K (MonoidAlgebra K G) V) := Module.restrictScalars O K _
  let := IsScalarTower.restrictScalars O K (RestrictScalars K (MonoidAlgebra K G) V)
  let := L.finite
  change Module.Finite k (RestrictScalars k kG
    (MR04LatticeSpec.residueAction (MR04LatticeSpec.integralAction O L)).asModule)
  exact Module.Finite.equiv
    (asModuleScalarEquiv (MR04LatticeSpec.residueAction (MR04LatticeSpec.integralAction O L))).symm

end FiniteReduction

/-- Reducing any stable lattice gives the ordinary character on regular elements after
embedding the lifted Brauer values into the fraction field. -/
def characterReduction :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K)
    (V : Type uV) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)]
    (L : MR04LatticeSpec.NativeLatticeData O K G V),
    letI := nativeReductionFinite V L
    ∀ g : MR01Spec.pRegularValue G p,
      algebraMap O K (MR03Spec.brauerCharacterValue S (MR04LatticeSpec.nativeReduction L) g) =
        MR03Spec.ordinaryCharacterValue (K := K) V g.val

/-- The same equality on the subtype of regular conjugacy classes. -/
def classCharacterReduction :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K)
    (V : Type uV) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)]
    (L : MR04LatticeSpec.NativeLatticeData O K G V),
    letI := nativeReductionFinite V L
    ∀ c : MR03Spec.pRegularConjClassesValue G p,
      algebraMap O K (MR03Spec.brauerClassCharacterValue S (MR04LatticeSpec.nativeReduction L) c) =
        MR03Spec.ordinaryClassCharacterValue (K := K) V c.val

/-- The class-function, short exact sequence, and stable lattice statements of MR04. -/
def brauerCharactersAndStableLattices :=
  MR03Spec.brauerCharacterEqOfIsConj.{uG, uO, uK, uV} ∧
  MR04CharacterLawsSpec.brauerCharacterAddOfExact.{uG, uO, uK, uU, uV, uN} ∧
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K)
    (V : Type uV) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)],
    Nonempty (MR04LatticeSpec.NativeLatticeData O K G V) ∧
      ∀ (L : MR04LatticeSpec.NativeLatticeData O K G V),
        letI := nativeReductionFinite V L
        ∀ g : MR01Spec.pRegularValue G p,
          algebraMap O K (MR03Spec.brauerCharacterValue S (MR04LatticeSpec.nativeReduction L) g) =
            MR03Spec.ordinaryCharacterValue (K := K) V g.val

end RepTheorySurvey.Modular.MR04Spec
