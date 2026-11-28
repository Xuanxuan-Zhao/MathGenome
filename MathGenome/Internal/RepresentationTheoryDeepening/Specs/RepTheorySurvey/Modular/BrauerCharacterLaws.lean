import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.Characters
import Mathlib.Algebra.Exact.Basic

/-! Independent specifications for the Brauer-character laws in MR04 and MR05. -/

namespace RepTheorySurvey.Modular.MR04CharacterLawsSpec

universe uG uO uK uU uM uN

open IsLocalRing (ResidueField)

set_option backward.isDefEq.respectTransparency false

/-- The Brauer character is constant on each p-regular conjugacy class. -/
def brauerCharacterEqOfSameClass :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K),
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)],
    ∀ {g h : MR01Spec.pRegularValue G p},
      MR03Spec.pRegularConjClassValue g = MR03Spec.pRegularConjClassValue h →
      MR03Spec.brauerCharacterValue S M g = MR03Spec.brauerCharacterValue S M h

/-- The ordinary character is constant on conjugacy classes. -/
def ordinaryCharacterEqOfIsConj :=
  ∀ {G : Type uG} [Group G] {K : Type uK} [Field K]
    (V : Type uM) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)] {g h : G},
    IsConj g h → MR03Spec.ordinaryCharacterValue (K := K) V g =
      MR03Spec.ordinaryCharacterValue (K := K) V h

/-- Additivity of the pointwise Brauer character on a short exact sequence. -/
def brauerCharacterAddOfExact :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K),
    ∀ (U : Type uU) [AddCommGroup U] [Module (MonoidAlgebra (ResidueField O) G) U]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) U)],
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)],
    ∀ (N : Type uN) [AddCommGroup N] [Module (MonoidAlgebra (ResidueField O) G) N]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) N)],
    ∀ (i : U →ₗ[MonoidAlgebra (ResidueField O) G] M)
      (q : M →ₗ[MonoidAlgebra (ResidueField O) G] N),
      Function.Injective i → Function.Surjective q → Function.Exact i q →
    ∀ g : MR01Spec.pRegularValue G p,
      MR03Spec.brauerCharacterValue S M g =
        MR03Spec.brauerCharacterValue S U g + MR03Spec.brauerCharacterValue S N g

/-- Additivity as an equality of functions on p-regular conjugacy classes. -/
def brauerClassCharacterAddOfExact :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K),
    ∀ (U : Type uU) [AddCommGroup U] [Module (MonoidAlgebra (ResidueField O) G) U]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) U)],
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)],
    ∀ (N : Type uN) [AddCommGroup N] [Module (MonoidAlgebra (ResidueField O) G) N]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) N)],
    ∀ (i : U →ₗ[MonoidAlgebra (ResidueField O) G] M)
      (q : M →ₗ[MonoidAlgebra (ResidueField O) G] N),
      Function.Injective i → Function.Surjective q → Function.Exact i q →
      MR03Spec.brauerClassCharacterValue S M =
        MR03Spec.brauerClassCharacterValue S U + MR03Spec.brauerClassCharacterValue S N

/-- Reduction of the integral Brauer character gives the trace of the same group action. -/
def residueBrauerCharacter :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K),
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)],
    ∀ g : MR01Spec.pRegularValue G p,
      IsLocalRing.residue O (MR03Spec.brauerCharacterValue S M g) =
        LinearMap.trace (ResidueField O)
          (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)
          (Representation.ofModule (k := ResidueField O) M g.val)

/-- The reduced Brauer class function is the modular trace class function on regular classes. -/
def residueBrauerClassCharacter :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K),
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)],
    ∀ c : MR03Spec.pRegularConjClassesValue G p,
      IsLocalRing.residue O (MR03Spec.brauerClassCharacterValue S M c) =
        MR03Spec.ordinaryClassCharacterValue (K := ResidueField O) M c.val

end RepTheorySurvey.Modular.MR04CharacterLawsSpec
