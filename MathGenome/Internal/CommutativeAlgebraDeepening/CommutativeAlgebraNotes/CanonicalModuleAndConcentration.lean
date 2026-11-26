import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CanonicalModuleAndConcentration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ArtinianLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CohenMacaulayLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteMatlisDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.CanonicalQuotient
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalRing (maximalIdeal)
open ModuleCat (restrictScalars)

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.CanonicalModuleAndConcentration
  (CanonicalModuleProperties CanonicalModuleAndConcentrationType
    CanonicalModuleForCoverType CanonicalModuleExtType)
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel (Complex stalk dualizingComplex)
open Specs.CommutativeAlgebraNotes.CechDualizingComplexModel (cechDual)
open Specs.CommutativeAlgebraNotes.CompleteLocalDuality (finiteModules)
open MatlisDualFunctorSpecs
  (matlisBidualEvaluationValue matlisDualValue residueFieldEnvelopeValue)
open RegularCoverDualizingModel (regularHomComplexIso shiftedHomEquiv)
open private cechLocalDuality from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteLocalDuality
open private shiftedStalkHomEquivExt from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel

universe u w

abbrev canonicalModule :=
  @Specs.CommutativeAlgebraNotes.CanonicalModuleAndConcentration.canonicalModule

variable {R : Type u} [CommRing R]

private abbrev ringLocalCohomology [IsLocalRing R] (i : ℤ) : ModuleCat.{u} R :=
  (Specs.CommutativeAlgebraNotes.IdealTorsion.localCohomology
    (maximalIdeal R) i).obj (ModuleCat.of R R)

private theorem isZero_matlisDual_iff [IsLocalRing R]
    (E : residueFieldEnvelopeValue R) (M : ModuleCat.{u} R) :
    IsZero ((matlisDualValue E).obj (op M)) ↔ IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton,
    ← not_nontrivial_iff_subsingleton, ← not_nontrivial_iff_subsingleton]
  exact not_congr (matlisDual_nontrivial_iff E M)

private theorem derivedIsoShift_iff [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (D : Complex R) (d : ℕ) :
    Nonempty (DerivedCategory.Q.obj D ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (canonicalModule D d))⟦(d : ℤ)⟧) ↔
      ∀ j : ℤ, j ≠ -(d : ℤ) → IsZero (D.homology j) := by
  let k : ℤ := -(d : ℤ)
  let X := DerivedCategory.Q.obj D
  let single := DerivedCategory.singleFunctor (ModuleCat.{u} R) k
  let h (j : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u} R) j
  let evaluation (j : ℤ) : (h j).obj X ≅ D.homology j :=
    (DerivedCategory.homologyFunctorFactors _ j).app D
  let shift : ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (canonicalModule D d))⟦(d : ℤ)⟧ ≅ single.obj (canonicalModule D d) :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso (d : ℤ) k 0
      (add_neg_cancel (d : ℤ))).app _
  constructor
  · rintro ⟨e⟩ j hj
    have hz : IsZero ((h j).obj (single.obj (canonicalModule D d))) := by
      rcases lt_or_gt_of_ne hj with hj | hj
      · exact DerivedCategory.isZero_of_isGE _ k j hj
      · exact DerivedCategory.isZero_of_isLE _ k j hj
    exact hz.of_iso ((evaluation j).symm ≪≫ (h j).mapIso (e ≪≫ shift))
  · intro vanish
    have : X.IsGE k := (DerivedCategory.isGE_iff X k).2
      fun j hj => (vanish j hj.ne).of_iso (evaluation j)
    have : X.IsLE k := (DerivedCategory.isLE_iff X k).2
      fun j hj => (vanish j hj.ne').of_iso (evaluation j)
    obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X k
    let eM : canonicalModule D d ≅ M := (evaluation k).symm ≪≫ (h k).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) k).app M
    exact ⟨e ≪≫ single.mapIso eM.symm ≪≫ shift.symm⟩

private theorem canonicalModuleProperties_of_duality [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (E : residueFieldEnvelopeValue R) (D : Complex R) (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (comparison : ∀ i : ℤ,
      Nonempty ((matlisDualValue E).obj (op (ringLocalCohomology (R := R) i)) ≅
        D.homology (-i))) : CanonicalModuleProperties E D d := by
  classical
  let H : ModuleCat.{u} R := ringLocalCohomology (d : ℤ)
  let W := canonicalModule D d
  let dual := matlisDualValue E
  have : IsArtinian R H := localCohomology_artinian (ModuleCat.of R R) (d : ℤ)
  obtain ⟨e⟩ := comparison (d : ℤ)
  let e : W ≅ dual.obj (op H) := e.symm
  have : Module.Finite R (dual.obj (op H)) := matlisDual_finite_of_isArtinian E H
  let b := (LinearEquiv.ofBijective _ (matlisEvaluation_bijective_of_isArtinian E H)).toModuleIso
  refine ⟨Module.Finite.equiv e.toLinearEquiv.symm,
    ⟨e, b ≪≫ dual.mapIso e.op, rfl⟩, ?_, ?_⟩
  · intro M _ h
    obtain ⟨a⟩ := h
    let bM := (LinearEquiv.ofBijective _ (matlisEvaluation_bijective_of_finite E M)).toModuleIso
    exact ⟨bM ≪≫ dual.mapIso a.op.symm ≪≫ e.symm⟩
  · obtain ⟨d', hd', _, criterion⟩ := cohenMacaulayRing_iff_localCohomology_concentrated R
    have heq : d' = d := by exact_mod_cast hd'.symm.trans hd
    subst d'
    rw [criterion, derivedIsoShift_iff]
    have vanishes (i : ℤ) :
        IsZero (ringLocalCohomology (R := R) i) ↔ IsZero (D.homology (-i)) := by
      obtain ⟨c⟩ := comparison i
      exact (isZero_matlisDual_iff E _).symm.trans c.isZero_iff
    constructor
    · intro h j hj
      simpa only [neg_neg] using (vanishes (-j)).1 (h (-j) (by omega))
    · intro h i hi
      exact (vanishes i).2 (h (-i) (by omega))

/-- The depth criterion and Matlis characterization for the dualized Čech model. -/
theorem canonicalModuleAndConcentration : CanonicalModuleAndConcentrationType.{u, w} := by
  intro R _ _ _ _ _ d hd E rs hrs
  apply canonicalModuleProperties_of_duality E (cechDual E rs) d hd
  intro i
  obtain ⟨e⟩ := cechLocalDuality E rs hrs i
  exact ⟨e.app (op (ModuleCat.of R R)) ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) (-i)).mapIso
      (regularHomComplexIso (cechDual E rs)).symm⟩

/-- The same characterization for every injective model from a regular cover. -/
theorem canonicalModuleForCover : CanonicalModuleForCoverType.{u, w} := by
  intro S R _ _ _ _ _ _ _ _ f _ hf n d hn hd J E
  let D := dualizingComplex f J.complex
  apply canonicalModuleProperties_of_duality E D d hd
  intro i
  obtain ⟨e⟩ := (completeLocalDuality f hf hn J E).2 i
  let X : (finiteModules R).FullSubcategory := ⟨ModuleCat.of R R, inferInstance⟩
  exact ⟨e.app (op X) ≪≫ (HomologicalComplex.homologyFunctor _ (.up ℤ) (-i)).mapIso
    (regularHomComplexIso D).symm⟩

open AdvCommAlg.Gorenstein AdvCommAlg.Gorenstein.ConcentratedChangeOfRings in
/-- The Ext comparison is linear for the quotient action from the first argument. -/
theorem canonicalModuleExt : CanonicalModuleExtType.{u} := by
  intro S R _ _ _ _ _ _ _ f _ hf n d hn hd hCM J
  let _ := f.toAlgebra
  let _ := HasDerivedCategory.standard (ModuleCat.{u} S)
  have hG := regularLocal_gorenstein S
  have hdn := canonicalQuotient_dimension_le S R hf hG hCM n d hn hd
  obtain ⟨hfin, hcanonical, _⟩ := canonicalQuotient_properties S R hf hG hCM n d hn hd
  refine ⟨hdn, ?_, ⟨hfin, hcanonical⟩⟩
  let D := dualizingComplex f J.complex
  let M := ModuleCat.of R R
  let X := (restrictScalars f).obj M
  let Y := ModuleCat.of S S
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-(d : ℤ))
  let e₀ := (restrictScalars f).mapIso
    (H.mapIso (RegularCoverDualizingModel.regularHomComplexIso D))
  have hdeg : (n : ℤ) + -(d : ℤ) = ((n - d : ℕ) : ℤ) := by omega
  let e := e₀.toLinearEquiv.trans
    ((shiftedHomEquiv f M (Iso.refl X) J (-(d : ℤ)) ((n - d : ℕ) : ℤ) hdeg).trans
      (shiftedStalkHomEquivExt X Y (n - d)))
  let a := firstExtAddEquiv f M Y (n - d)
  let b : canonicalModule D d ≃ₗ[R] FirstExt f M Y (n - d) :=
    { toAddEquiv := e.toAddEquiv.trans a.symm
      map_smul' := fun r x => by
        obtain ⟨s, rfl⟩ := hf r
        apply a.injective
        let x₀ : (restrictScalars f).obj (H.obj D) := x
        change a (a.symm (e (s • x₀))) = a (f s • a.symm (e x₀))
        calc
          _ = s • e x₀ := by rw [a.apply_symm_apply, e.map_smul]
          _ = _ := by
            rw [show a (f s • a.symm (e x₀)) = s • a (a.symm (e x₀)) from
              firstExt_smul_of_base f M Y (n - d) s _]
            rw [a.apply_symm_apply] }
  exact ⟨b.toModuleIso⟩

end CommutativeAlgebraNotes
