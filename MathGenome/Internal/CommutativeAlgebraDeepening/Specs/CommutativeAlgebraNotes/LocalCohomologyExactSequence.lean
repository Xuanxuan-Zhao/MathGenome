import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.LieHochschildSerre
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

/-! The cochain connecting morphisms and long exact sequence of local cohomology. -/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors (ExactPair)
open AdvancedHomologicalAlgebra.LieHochschildSerre (mapExtendIso)

namespace Specs.CommutativeAlgebraNotes.LocalCohomologyExactSequence

open Specs.CommutativeAlgebraNotes.IdealTorsion

universe v u

set_option linter.checkUnivs false

noncomputable section

variable {R : Type u} [CommRing R]

/-- Applying ideal torsion to a degreewise split row leaves it short exact. -/
theorem mappedShortExact (I : Ideal R) {T : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ)}
    (split : SplitsDegreewise T) :
    (T.map ((idealTorsionFunctor I).mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  obtain ⟨s⟩ := split n
  exact (s.map (idealTorsionFunctor I)).shortExact

/-- A cochain horseshoe with the prescribed injective resolutions as endpoints. -/
theorem existsResolvingRow {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (P : InjectiveResolution S.X₁) (Q : InjectiveResolution S.X₃) :
    ∃ H : ResolvingRow S P.ι' Q.ι', H.IsHorseshoe :=
  AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe.exists_horseshoe _ S hS
    _ _ P.ι' Q.ι' inferInstance inferInstance
    ⟨⟨0, fun _ h => CochainComplex.isZero_of_isStrictlyGE _ 0 _ h⟩, fun _ => inferInstance⟩
    ⟨⟨0, fun _ h => CochainComplex.isZero_of_isStrictlyGE _ 0 _ h⟩, fun _ => inferInstance⟩

/-- The comparison from natural-indexed cohomology to cohomology after extension by zero. -/
def extendResolutionIso (I : Ideal R) (n : ℕ) {M : ModuleCat.{v} R}
    (P : InjectiveResolution M) :
    (((idealTorsionFunctor I).mapHomologicalComplex (.up ℕ)).obj P.cocomplex).homology n ≅
      (((idealTorsionFunctor I).mapHomologicalComplex (.up ℤ)).obj P.cochainComplex).homology
        (n : ℤ) :=
  let F := idealTorsionFunctor I
  let e := ComplexShape.embeddingUpNat
  (((F.mapHomologicalComplex (.up ℕ)).obj P.cocomplex).extendHomologyIso e
      (rfl : e.f n = (n : ℤ))).symm ≪≫
    (homologyFunctor _ (.up ℤ) (n : ℤ)).mapIso (mapExtendIso F e P.cocomplex).symm

variable [Small.{v} R]

/-- The canonical computation of local cohomology on a resolution extended by zero. -/
def resolutionIso (I : Ideal R) (n : ℕ) {M : ModuleCat.{v} R} (P : InjectiveResolution M) :
    (localCohomology I (n : ℤ)).obj M ≅
      (((idealTorsionFunctor I).mapHomologicalComplex (.up ℤ)).obj P.cochainComplex).homology
        (n : ℤ) :=
  P.isoRightDerivedObj (idealTorsionFunctor I) n ≪≫ extendResolutionIso I n P

/-- The ordinary cochain boundary transported to the given right-derived functors.
In negative degrees its source is zero. -/
def boundary (I : Ideal R) {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (q : ℤ) :
    (localCohomology I q).obj S.X₃ ⟶ (localCohomology I (q + 1)).obj S.X₁ :=
  match q with
  | .ofNat n =>
    let P := injectiveResolution S.X₁
    let Q := injectiveResolution S.X₃
    let ex := existsResolvingRow hS P Q
    let hT := mappedShortExact I ex.choose_spec.2.2.2
    (resolutionIso I n Q).hom ≫ hT.δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) ≫
      (resolutionIso I (n + 1) P).inv
  | .negSucc _ => 0

/-- The degree-zero identification sends a derived class to its section of Γ. -/
abbrev degreeZeroIso (I : Ideal R) [PreservesFiniteLimits (idealTorsionFunctor.{v} I)] :
    localCohomology.{v} I 0 ≅ idealTorsionFunctor I :=
  (idealTorsionFunctor I).rightDerivedZeroIsoSelf

def boundaryType :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    {S : ShortComplex (ModuleCat.{v} R)}, S.ShortExact → ∀ q : ℤ,
      (localCohomology I q).obj S.X₃ ⟶ (localCohomology I (q + 1)).obj S.X₁

/-- The boundary is the cochain lift-then-differentiate boundary on every
horseshoe with prescribed endpoints, including in degree zero. -/
def boundaryOnResolutionType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (P : InjectiveResolution S.X₁) (Q : InjectiveResolution S.X₃)
    (H : ResolvingRow S P.ι' Q.ι') (hH : H.IsHorseshoe) (n : ℕ),
    boundary I hS (n : ℤ) ≫ (resolutionIso I (n + 1) P).hom =
      (resolutionIso I n Q).hom ≫
        (mappedShortExact I hH.2.2.2).δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp)

def exactSequenceType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact) (q : ℤ),
    ExactPair ((localCohomology I q).map S.f) ((localCohomology I q).map S.g) ∧
    ExactPair ((localCohomology I q).map S.g) (boundary I hS q) ∧
    ExactPair (boundary I hS q) ((localCohomology I (q + 1)).map S.f)

def boundaryNaturalType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    {S T : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (q : ℤ),
    (localCohomology I q).map φ.τ₃ ≫ boundary I hT q =
      boundary I hS q ≫ (localCohomology I (q + 1)).map φ.τ₁

def naturalityType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    {S T : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (q : ℤ),
    let H := localCohomology I q
    H.map S.f ≫ H.map φ.τ₂ = H.map φ.τ₁ ≫ H.map T.f ∧
    H.map S.g ≫ H.map φ.τ₃ = H.map φ.τ₂ ≫ H.map T.g ∧
    H.map φ.τ₃ ≫ boundary I hT q = boundary I hS q ≫ (localCohomology I (q + 1)).map φ.τ₁

/-- The degree-zero edge map is the actual inclusion of ideal torsion into the module. -/
abbrev edge (I : Ideal R) [PreservesFiniteLimits (idealTorsionFunctor.{v} I)] :
    localCohomology.{v} I 0 ⟶ 𝟭 (ModuleCat.{v} R) :=
  (degreeZeroIso I).hom ≫ idealTorsionInclusion I

def degreeZeroIsoType :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    [PreservesFiniteLimits (idealTorsionFunctor.{v} I)],
      localCohomology.{v} I 0 ≅ idealTorsionFunctor I

def edgeType :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    [PreservesFiniteLimits (idealTorsionFunctor.{v} I)],
      localCohomology.{v} I 0 ⟶ 𝟭 (ModuleCat.{v} R)

def degreeZeroUnitType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R),
    IsIso (idealTorsionFunctor.{v} I).toRightDerivedZero

def monoZeroType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
    {S : ShortComplex (ModuleCat.{v} R)}, S.ShortExact → Mono ((localCohomology I 0).map S.f)

end

end Specs.CommutativeAlgebraNotes.LocalCohomologyExactSequence
