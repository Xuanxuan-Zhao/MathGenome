import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel

noncomputable section

open CategoryTheory
open CochainComplex HomComplex
open IsLocalRing (maximalIdeal)
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel

namespace Specs.CommutativeAlgebraNotes.DualizingComplexHomothety

universe u w

/-- The actual map from the regular module in degree zero sends a scalar to
multiplication by that scalar on the coinduced complex. -/
def homothety {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R) (J : Complex S) :
    stalk R 0 (ModuleCat.of R R) ⟶
      linearHomComplex R (dualizingComplex f J) (dualizingComplex f J) := by
  let D := dualizingComplex f J
  let h : ModuleCat.of R R ⟶ (linearHomComplex R D D).X 0 :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (Cochain.ofHom (𝟙 D)))
  refine HomologicalComplex.mkHomFromSingle h (fun k _ => ?_)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change δ 0 k (r • Cochain.ofHom (𝟙 D)) = 0
  simp

def HomothetyType :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R) (J : Complex S),
    stalk R 0 (ModuleCat.of R R) ⟶
      linearHomComplex R (dualizingComplex f J) (dualizingComplex f J)

/-- Localization of the homothety at quasi-isomorphisms for the chosen resolution
of the shifted source ring. Its target is the signed Hom into the bounded
injective representative of the dualizing complex. -/
def derivedHomothety {S R : Type u} [CommRing S] [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (f : S →+* R) {n : ℕ}
    (J : ShiftedRingResolution S n) :
    DerivedCategory.Q.obj (stalk R 0 (ModuleCat.of R R)) ⟶
      DerivedCategory.Q.obj
        (linearHomComplex R (dualizingComplex f J.complex) (dualizingComplex f J.complex)) :=
  DerivedCategory.Q.map (homothety f J.complex)

set_option linter.checkUnivs false in
def DerivedHomothetyType :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : S →+* R) {n : ℕ} (J : ShiftedRingResolution S n),
    DerivedCategory.Q.obj (stalk R 0 (ModuleCat.of R R)) ⟶
      DerivedCategory.Q.obj
        (linearHomComplex R (dualizingComplex f J.complex) (dualizingComplex f J.complex))

/-- Under the coinduction adjunction the homothety at a scalar is evaluation
at that scalar, degree by degree. -/
def HomothetyEvaluation : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R) (J : Complex S)
    (r : R) (p : ℤ) (i : (dualizingComplex f J).X p),
    let D := dualizingComplex f J
    let r₀ := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv r
    let z : Cochain D D 0 := (homothety f J).f 0 r₀
    LocalQuotientAdjunction.adjunction f (D.X p) (J.X p) (z.v p p (add_zero p)) i =
      (show (ModuleCat.coextendScalars f).obj (J.X p) from i) r

/-- The chain-level homothety for a fixed complete regular local cover is a
quasi-isomorphism, for every bounded injective resolution of S[n]. -/
def HomothetyQuasiIso : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal S) S]
    [IsAdicComplete (maximalIdeal R) R] (f : S →+* R) [IsLocalHom f],
    Function.Surjective f → ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n), QuasiIso (homothety f J.complex)

/-- The same homothety in the derived category is an isomorphism. -/
def DerivedHomothetyIsIso : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal S) S]
    [IsAdicComplete (maximalIdeal R) R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n), IsIso (derivedHomothety f J)

end Specs.CommutativeAlgebraNotes.DualizingComplexHomothety
