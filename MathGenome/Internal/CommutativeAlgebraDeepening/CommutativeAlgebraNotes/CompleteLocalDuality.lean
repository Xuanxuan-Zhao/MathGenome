import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CechDualizingComplexModel
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorFlip

noncomputable section

open CategoryTheory Opposite
open HomologicalComplex
open IsLocalRing (maximalIdeal)
open CochainComplex (linearHomComplex)

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.CompleteLocalDuality
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel (Complex)
open ExactDualCochainCohomologySpecs (precomp)

universe u w

variable {R : Type u} [CommRing R]

private abbrev stalkFunctor (R : Type u) [CommRing R] :=
  CochainComplex.singleFunctor (ModuleCat.{u} R) 0

private abbrev cohomology (R : Type u) [CommRing R] (j : ℤ) :=
  homologyFunctor (ModuleCat.{u} R) (.up ℤ) j

section ChangeModel

open DerivedCategory
open RegularCoverDualizingModel (homologyHomEquiv homPrecomposition)

open private homologyHomEquiv_precomp from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable {D I : Complex R} [D.IsKInjective] [I.IsKInjective]

/-- The cohomology of Hom into K-injective models depends naturally on the
source and only on the isomorphism class of the target in the derived category. -/
private def homCohomologyIsoOfDerivedIso (e : Q.obj D ≅ Q.obj I) (j : ℤ) :
    homFromModule D ⋙ cohomology R j ≅ homFromModule I ⋙ cohomology R j := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let shiftIso : Q.obj (D⟦j⟧) ≅ Q.obj (I⟦j⟧) :=
    (Q.commShiftIso j).app D ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) j).mapIso e ≪≫
      (Q.commShiftIso j).symm.app I
  let comparison (X : ModuleCat.{u} R) :
      (linearHomComplex R ((stalkFunctor R).obj X) D).homology j ≃ₗ[R]
        (linearHomComplex R ((stalkFunctor R).obj X) I).homology j :=
    (homologyHomEquiv j).trans <|
      (Linear.homCongr R (Iso.refl _) shiftIso).trans (homologyHomEquiv j).symm
  refine NatIso.ofComponents (fun X => (comparison X.unop).toModuleIso) ?_
  intro X Y g
  let a := (stalkFunctor R).map g.unop
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (linearHomComplex R ((stalkFunctor R).obj X.unop) D).homology j at x
  change comparison Y.unop (homologyMap (homPrecomposition a D) j x) =
    homologyMap (homPrecomposition a I) j (comparison X.unop x)
  apply (homologyHomEquiv (I := I) j).injective
  have h (X₀ : ModuleCat.{u} R)
      (z : (linearHomComplex R ((stalkFunctor R).obj X₀) D).homology j) :
      homologyHomEquiv (I := I) j (comparison X₀ z) =
        homologyHomEquiv j z ≫ shiftIso.hom := by
    simp only [comparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      Linear.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rw [h, homologyHomEquiv_precomp (I := I), h X.unop x,
    homologyHomEquiv_precomp (I := D) a j x, Category.assoc]

end ChangeModel

section TensorSymmetry

open MonoidalCategory

private abbrev tensorBicomplex (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K L : Complex R) :=
  ((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L

private def tensorBicomplexBraiding (K L : Complex R) :
    tensorBicomplex (curriedTensor (ModuleCat.{u} R)) K L ≅
      tensorBicomplex (curriedTensor (ModuleCat.{u} R)).flip K L := by
  refine Hom.isoOfComponents (fun p => Hom.isoOfComponents (fun q => β_ (K.X p) (L.X q)) ?_)
    ?_
  · intro q q' _
    exact (BraidedCategory.braiding_naturality_right (K.X _) (L.d q q')).symm
  · intro p p' _
    apply HomologicalComplex.hom_ext
    intro q
    exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm

/-- The interchange of the tensor factors uses the symmetry of total
complexes, with its Koszul sign, and the symmetry of tensor products. -/
private def tensorSwap (K L : Complex R) : HomologicalComplex.tensorObj K L ≅
    HomologicalComplex.tensorObj L K :=
  HomologicalComplex₂.total.mapIso (tensorBicomplexBraiding K L) (.up ℤ) ≪≫
    mapBifunctorFlipIso L K (curriedTensor (ModuleCat.{u} R)) (.up ℤ)

private lemma tensorSwap_natural {K K' : Complex R} (g : K ⟶ K') (L : Complex R) :
    HomologicalComplex.tensorHom g (𝟙 L) ≫ (tensorSwap K' L).hom =
      (tensorSwap K L).hom ≫ HomologicalComplex.tensorHom (𝟙 L) g := by
  let F := curriedTensor (ModuleCat.{u} R)
  change mapBifunctorMap g (𝟙 L) F (.up ℤ) ≫
      HomologicalComplex₂.total.map (tensorBicomplexBraiding K' L).hom (.up ℤ) ≫
        (mapBifunctorFlipIso L K' F (.up ℤ)).hom =
    (HomologicalComplex₂.total.map (tensorBicomplexBraiding K L).hom (.up ℤ) ≫
      (mapBifunctorFlipIso L K F (.up ℤ)).hom) ≫ mapBifunctorMap (𝟙 L) g F (.up ℤ)
  simp only [Category.assoc]
  rw [← mapBifunctorFlipIso_hom_naturality (𝟙 L) g F (.up ℤ),
    ← Category.assoc, ← Category.assoc]
  let B := F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let B' := F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  change (HomologicalComplex₂.total.map ((B.map g).app L ≫ (B.obj K').map (𝟙 L)) _ ≫
    HomologicalComplex₂.total.map (tensorBicomplexBraiding K' L).hom _) ≫ _ =
    (HomologicalComplex₂.total.map (tensorBicomplexBraiding K L).hom _ ≫
      HomologicalComplex₂.total.map ((B'.map g).app L ≫ (B'.obj K').map (𝟙 L)) _) ≫ _
  rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
  congr 2
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  simp [B, B', F, tensorBicomplexBraiding]
  exact BraidedCategory.braiding_naturality_left (g.f p) (L.X q)

end TensorSymmetry

section CechComparison

open CochainTensorHom (homMap homMap_apply tensorHomIso tensorHomIso_natural)
open CochainComplex.HomComplex (Cochain)
open MatlisDualFunctorSpecs (residueFieldEnvelopeValue matlisDualValue)
open ExactDualCochainCohomologySpecs (hullInDegreeZero dualComplexValue)

private lemma homMap_id_target {K L : Complex R} (g : K ⟶ L) (Z : Complex R) :
    homMap g (𝟙 Z) = precomp g Z := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change Cochain L Z i at z
  apply Cochain.ext
  intro p q h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homMap g (𝟙 Z)).f i z).v p q h x = ((precomp g Z).f i z).v p q h x
  rw [homMap_apply g (𝟙 Z) h z x]
  simp [precomp, Cochain.zero_cochain_comp_v _ _ p q h]

private lemma precomp_id {K : Complex R} (Z : Complex R) :
    precomp (R := R) (𝟙 K) Z = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact Cochain.id_comp z

private abbrev cechCoefficientFunctor (R : Type u) [CommRing R] (rs : List R) :=
  stalkFunctor R ⋙ Specs.CommutativeAlgebraNotes.AugmentedCechComplex.tensorFunctor R rs

variable [IsLocalRing R]

/-- Currying the dual of the coefficient Čech complex gives ordinary
cochain Hom into the Čech dual, naturally in the coefficient module. -/
private def cechCurryingIso (E : residueFieldEnvelopeValue R) (rs : List R) :
    (cechCoefficientFunctor R rs).op ⋙ dualComplexValue E ≅ homFromModule (cechDual E rs) := by
  let C := Specs.CommutativeAlgebraNotes.AugmentedCechComplex.complex R rs
  let Z := hullInDegreeZero E
  refine NatIso.ofComponents (fun X =>
    (dualComplexValue E).mapIso (tensorSwap ((stalkFunctor R).obj X.unop) C).op ≪≫
      tensorHomIso ((stalkFunctor R).obj X.unop) C Z) ?_
  intro X Y g
  let P := (stalkFunctor R).obj X.unop
  let P' := (stalkFunctor R).obj Y.unop
  let a : P' ⟶ P := (stalkFunctor R).map g.unop
  have hswap : precomp (R := R) (HomologicalComplex.tensorHom (𝟙 C) a) Z ≫
      precomp (tensorSwap P' C).hom Z =
      precomp (tensorSwap P C).hom Z ≫
        precomp (HomologicalComplex.tensorHom a (𝟙 C)) Z := by
    let F := dualComplexValue E
    change F.map (HomologicalComplex.tensorHom (𝟙 C) a).op ≫ F.map (tensorSwap P' C).hom.op =
      F.map (tensorSwap P C).hom.op ≫ F.map (HomologicalComplex.tensorHom a (𝟙 C)).op
    have h := congrArg (fun b => F.map b.op) (tensorSwap_natural a C)
    simpa only [op_comp, Functor.map_comp] using h.symm
  have hcurrying := tensorHomIso_natural a (𝟙 C) (𝟙 Z)
  rw [homMap_id_target, homMap_id_target, precomp_id] at hcurrying
  rw [homMap_id_target] at hcurrying
  change precomp (HomologicalComplex.tensorHom (𝟙 C) a) Z ≫
      precomp (tensorSwap P' C).hom Z ≫ (tensorHomIso P' C Z).hom =
    (precomp (tensorSwap P C).hom Z ≫ (tensorHomIso P C Z).hom) ≫
      precomp a (linearHomComplex R C Z)
  rw [← Category.assoc, hswap, Category.assoc, hcurrying, Category.assoc]

variable [IsNoetherianRing R]

private theorem cechLocalDuality (E : residueFieldEnvelopeValue R) (rs : List R)
    (hrs : Ideal.span {r | r ∈ rs} = maximalIdeal R) (i : ℤ) :
    Nonempty
      ((Specs.CommutativeAlgebraNotes.IdealTorsion.localCohomology.{u}
          (maximalIdeal R) i).op ⋙ matlisDualValue E ≅
        homFromModule (cechDual E rs) ⋙ cohomology R (-i)) := by
  let F := cechCoefficientFunctor R rs
  obtain ⟨e⟩ := localCohomologyCechComparison (maximalIdeal R) rs hrs i
  let b := Functor.isoWhiskerLeft F.op (ExactDualCochainCohomology.cohomologyIso E (-i))
  change (F.op ⋙ dualComplexValue E ⋙ cohomology R (-i)) ≅
    (F.op ⋙ (cohomology R (-(-i))).op ⋙ matlisDualValue E) at b
  rw [neg_neg] at b
  let M := matlisDualValue E
  exact ⟨Functor.isoWhiskerRight (NatIso.op e.symm ≪≫ Functor.opComp F (cohomology R i)) M ≪≫
    Functor.associator F.op (cohomology R i).op M ≪≫ b.symm ≪≫
    (Functor.associator F.op (dualComplexValue E) (cohomology R (-i))).symm ≪≫
    Functor.isoWhiskerRight (cechCurryingIso E rs) (cohomology R (-i))⟩

end CechComparison

open private exists_generating_list from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange

/-- Local duality over a complete Noetherian local ring, natural on finite
modules and valid for every regular cover and every choice of Čech generators. -/
theorem completeLocalDuality : LocalDualityType.{u, w} := by
  intro S R _ _ _ _ _ _ _ _ f _ hf n hn J E
  let D := Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel.dualizingComplex f J.complex
  have hmodel (rs : List R) (hrs : Ideal.span {r | r ∈ rs} = maximalIdeal R) :
      Nonempty (DerivedCategory.Q.obj (cechDual E rs) ≅ DerivedCategory.Q.obj D) :=
    cechDual_represents_dualizingObject f hf hn J E rs hrs
  refine ⟨hmodel, ?_⟩
  obtain ⟨rs, hrs⟩ := exists_generating_list (maximalIdeal R)
  obtain ⟨e⟩ := hmodel rs hrs
  let : (cechDual E rs).IsKInjective := (cechDual_bounded_injective E rs).2.2.2
  let : D.IsKInjective :=
    (RegularCoverDualizingModel.coinduced_bounded_injective f J).2.2.2
  intro i
  obtain ⟨d⟩ := cechLocalDuality E rs hrs i
  exact ⟨Functor.isoWhiskerLeft (finiteModules R).ι.op
    (d ≪≫ homCohomologyIsoOfDerivedIso e (-i))⟩

end CommutativeAlgebraNotes
