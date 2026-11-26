import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechDualizingComplexModel
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section

open CategoryTheory
open HomologicalComplex (homologyFunctor)
open IsLocalRing (maximalIdeal)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs
  (matlisDualValue residueFieldEnvelopeValue)
open _root_.CommutativeAlgebraNotes.ExactDualCochainCohomologySpecs (precomp)

namespace Specs.CommutativeAlgebraNotes.CompleteLocalDuality

open RegularCoverDualizingModel (Complex ShiftedRingResolution dualizingComplex)
open CechDualizingComplexModel (cechDual)
open CochainComplex (linearHomComplex singleFunctor)
open CochainComplex.HomComplex (Cochain)

universe u w

variable {R : Type u} [CommRing R]

/-- The full subcategory on finitely generated modules. -/
abbrev finiteModules (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M => Module.Finite R M

/-- The signed linear Hom complex out of a module placed in degree zero,
with precomposition as its contravariant action. -/
def homFromModule (D : Complex R) : (ModuleCat.{u} R)ᵒᵖ ⥤ Complex R where
  obj X := linearHomComplex R ((singleFunctor (ModuleCat.{u} R) 0).obj X.unop) D
  map g := precomp ((singleFunctor (ModuleCat.{u} R) 0).map g.unop) D
  map_id _ := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simp [precomp]
  map_comp _ _ := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    simp [precomp, Cochain.zero_cochain_comp_v _ _ p q hpq]

/-- A dualizing model is represented by the Čech dual for every list of
maximal-ideal generators. For a K-injective model, the signed linear Hom
complex computes the derived Hom in the natural cohomology comparison. -/
def LocalDualityForModel [IsLocalRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (E : residueFieldEnvelopeValue R) (D : Complex R) : Prop :=
  (∀ rs : List R, Ideal.span {r | r ∈ rs} = maximalIdeal R →
    Nonempty (DerivedCategory.Q.obj (cechDual E rs) ≅ DerivedCategory.Q.obj D)) ∧
  ∀ i : ℤ, Nonempty
    ((finiteModules R).ι.op ⋙ (IdealTorsion.localCohomology.{u} (maximalIdeal R) i).op ⋙
        matlisDualValue E ≅
      (finiteModules R).ι.op ⋙ homFromModule D ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-i))

/-- Local duality for the model of the normalized dualizing object from any
complete regular local cover and any bounded injective resolution of its
shifted ring. The residue-field envelope can be chosen arbitrarily. -/
def LocalDualityType : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal S) S] [IsAdicComplete (maximalIdeal R) R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n) (E : residueFieldEnvelopeValue R),
      LocalDualityForModel E (dualizingComplex f J.complex)

end Specs.CommutativeAlgebraNotes.CompleteLocalDuality
