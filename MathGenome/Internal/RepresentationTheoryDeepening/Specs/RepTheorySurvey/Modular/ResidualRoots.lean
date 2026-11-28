import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplittingSystem

/-! Independent specifications for the roots-of-unity part of Lemma MR02. -/

namespace RepTheorySurvey.Modular.MR02RootsSpec

universe uG uO uK

/-- Every `m`-th root in the fraction field comes from an `m`-th root in the DVR. -/
def fractionRootsSurjective :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData G p O K →
      Function.Surjective (restrictRootsOfUnity (algebraMap O K) (MR01Spec.primeToPartValue G p))

-- The type exposes separate universes for the group, DVR, and fraction field.
set_option linter.checkUnivs false in
def residualRootLiftType :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData G p O K →
      rootsOfUnity (MR01Spec.primeToPartValue G p) (IsLocalRing.ResidueField O) →
      rootsOfUnity (MR01Spec.primeToPartValue G p) O

/-- The inverse of the canonical residue map, characterized by the isomorphism below. -/
noncomputable def residualRootLiftValue : residualRootLiftType.{uG, uO, uK} :=
  @fun G _ _ p O _ _ _ _ _ _ _S =>
    Function.invFun (restrictRootsOfUnity (IsLocalRing.residue O) (MR01Spec.primeToPartValue G p))

/-- The multiplicative equivalence acts by reduction and its inverse gives the lift. -/
def residualRootsIsomorphism :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K),
    let m := MR01Spec.primeToPartValue G p
    ∃ e : rootsOfUnity m O ≃* rootsOfUnity m (IsLocalRing.ResidueField O),
      (∀ u, e u = restrictRootsOfUnity (IsLocalRing.residue O) m u) ∧
      (∀ v, e.symm v = residualRootLiftValue S v)

/-- The residue field contains a primitive root of order `m`. -/
def residuePrimitiveRoot :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData G p O K →
      ∃ ζ : IsLocalRing.ResidueField O, IsPrimitiveRoot ζ (MR01Spec.primeToPartValue G p)

end RepTheorySurvey.Modular.MR02RootsSpec
