import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalQuotientAdjunction
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.GorensteinExtProfile
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularAndCompleteIntersection

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

set_option linter.style.haveILetI false
open CochainComplex HomologicalComplex HomComplex
open ModuleCat (restrictScalars coextendScalars)
open IsLocalRing (ResidueField maximalIdeal)
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel

namespace CommutativeAlgebraNotes.RegularCoverDualizingModel

universe u w

abbrev dualizingComplex : DualizingComplexType.{u} :=
  @Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel.dualizingComplex

abbrev dualizingObject : DualizingObjectType.{u, w} :=
  @Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel.dualizingObject

private def cycleSequence {S : Type u} [CommRing S] (K : Complex S) (i : ℤ) :
    ShortComplex (ModuleCat.{u} S) :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (by
    rw [← cancel_mono (K.iCycles (i + 1)), Category.assoc, toCycles_i, zero_comp]
    exact K.iCycles_d i (i + 1))

private theorem cycleSequence_shortExact {S : Type u} [CommRing S] (K : Complex S)
    (i : ℤ) (h : K.ExactAt (i + 1)) : (cycleSequence K i).ShortExact := by
  have h' : (K.sc' i (i + 1) (i + 1 + 1)).Exact :=
    (K.exactAt_iff' i (i + 1) (i + 1 + 1) (by simp) (by simp)).mp h
  let T := ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1))
  let φ : cycleSequence K i ⟶ T :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := K.iCycles (i + 1)
      comm₂₃ := by simp [cycleSequence, T] }
  have he : Epi (K.toCycles i (i + 1)) := by
    let e := K.cyclesIsoSc' i (i + 1) (i + 1 + 1) (by simp) (by simp)
    have he : Epi (K.toCycles i (i + 1) ≫ e.hom) := by
      rw [K.toCycles_cyclesIsoSc'_hom]
      exact h'.epi_toCycles
    rw [← Category.comp_id (K.toCycles i (i + 1)), ← e.hom_inv_id, ← Category.assoc]
    infer_instance
  have : Epi φ.τ₁ := by
    change Epi (𝟙 (K.cycles i))
    infer_instance
  have : IsIso φ.τ₂ := by
    change IsIso (𝟙 (K.X i))
    infer_instance
  have : Mono φ.τ₃ := by
    change Mono (K.iCycles (i + 1))
    infer_instance
  exact
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
        (T.exact_of_f_is_kernel (K.cyclesIsKernel i (i + 1) (by simp)))
      mono_f := inferInstanceAs (Mono (K.iCycles i))
      epi_g := he }

private theorem cycles_dimension {S : Type u} [CommRing S] {X : ModuleCat.{u} S}
    (J : InjectiveResolution X) (d : ℕ) (hd : HasInjectiveDimensionLE X d) :
    ∀ k : ℕ, k ≤ d → HasInjectiveDimensionLE (J.cochainComplex.cycles (k : ℤ)) (d - k) := by
  intro k
  induction k with
  | zero =>
    intro _
    let K := J.cochainComplex
    have hz : K.d (-1) 0 = 0 := (K.isZero_of_isStrictlyGE 0 (-1)).eq_of_src _ _
    let e : X ≅ K.cycles 0 :=
      (singleObjHomologySelfIso (.up ℤ) 0 X).symm ≪≫
        asIso (homologyMap J.ι' 0) ≪≫ (K.isoHomologyπ (-1) 0 (by simp) hz).symm
    simpa using (hasInjectiveDimensionLT_of_iso e (d + 1))
  | succ k ih =>
    intro hk
    have hle : (0 : ℤ) < (k : ℤ) + 1 := by omega
    have hs := cycleSequence_shortExact J.cochainComplex (k : ℤ)
      ((isLE_iff J.cochainComplex 0).mp inferInstance _ hle)
    have hdim : HasInjectiveDimensionLT (J.cochainComplex.cycles (k : ℤ))
        (d - (k + 1) + 1 + 1) := by
      convert (ih (by omega)) using 1
      omega
    have h := (hs.hasInjectiveDimensionLT_X₃_iff (d - (k + 1))
      (inferInstanceAs (Injective (J.cochainComplex.X (k : ℤ))))).mpr hdim
    simpa only [cycleSequence, Int.natCast_succ] using h

set_option maxHeartbeats 700000 in
theorem shiftedRingResolution_exists : ShiftedRingResolutionExists.{u} := by
  intro S _ _ n hn
  let X := ModuleCat.of S S
  have hdim : HasInjectiveDimensionLE X n := (injectiveDimension_le_iff X n).mp (by
    rw [AdvCommAlg.Gorenstein.localGorenstein_injectiveDimension S
      (AdvCommAlg.Gorenstein.regularLocal_gorenstein S), hn])
  let I := InjectiveResolution.of X
  let K := I.cochainComplex
  let L := K.truncLE (n : ℤ)
  let K₀ := stalk S 0 X
  haveI : K₀.IsStrictlyLE (n : ℤ) := K₀.isStrictlyLE_of_le 0 _ (by omega)
  let a : K₀ ⟶ L := inv (K₀.ιTruncLE (n : ℤ)) ≫ truncLEMap I.ι' (n : ℤ)
  haveI : QuasiIso (truncLEMap I.ι' (n : ℤ)) :=
    (CochainComplex.quasiIso_truncLEMap_iff I.ι' (n : ℤ)).mpr fun _ _ => inferInstance
  haveI : QuasiIso a := by dsimp [a]; infer_instance
  have hL (i : ℤ) : Injective (L.X i) := by
    rcases lt_trichotomy i (n : ℤ) with h | rfl | h
    · exact Injective.of_iso (K.truncLEXIso _ _ h).symm inferInstance
    · have hi := cycles_dimension I n hdim n le_rfl
      rw [Nat.sub_self, ← injective_iff_hasInjectiveDimensionLE_zero] at hi
      exact Injective.of_iso (K.truncLEXIsoCycles _).symm hi
    · exact (L.isZero_of_isStrictlyLE _ _ h).injective
  haveI : L.IsStrictlyGE 0 := (isStrictlyGE_iff L 0).mpr fun i hi =>
    IsZero.of_iso (K.isZero_of_isStrictlyGE 0 i hi)
      (K.truncLEXIso _ _ (by omega))
  refine ⟨{ complex := L⟦(n : ℤ)⟧
            ι := (CategoryTheory.shiftFunctor (Complex S) (n : ℤ)).map a
            quasiIso := inferInstance
            injective := fun i => Injective.of_iso
              (L.shiftFunctorObjXIso (n : ℤ) i _ rfl).symm (hL _)
            lower := -(n : ℤ)
            upper := 0
            isStrictlyGE := L.isStrictlyGE_shift 0 _ _ (by omega)
            isStrictlyLE := L.isStrictlyLE_shift (n : ℤ) _ _ (by omega) }, rfl, rfl⟩

private theorem bounded_isKInjective {S : Type u} [CommRing S] {K : Complex S}
    (J : BoundedInjectiveResolution K) : J.complex.IsKInjective := by
  letI := J.isStrictlyGE
  haveI := J.injective
  exact isKInjective_of_injective J.complex J.lower

theorem coinduced_bounded_injective : CoinducedBoundedInjective.{u} := by
  intro S R _ _ f K J
  let I := dualizingComplex f J.complex
  have hI (i : ℤ) : Injective (I.X i) := coinduction_injective f _ (J.injective i)
  letI := J.isStrictlyGE
  letI := J.isStrictlyLE
  letI := (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  have hge : I.IsStrictlyGE J.lower := (isStrictlyGE_iff I J.lower).mpr fun i hi =>
    (coextendScalars f).map_isZero (J.complex.isZero_of_isStrictlyGE _ _ hi)
  have hle : I.IsStrictlyLE J.upper := (isStrictlyLE_iff I J.upper).mpr fun i hi =>
    (coextendScalars f).map_isZero (J.complex.isZero_of_isStrictlyLE _ _ hi)
  exact ⟨hI, hge, hle, isKInjective_of_injective I J.lower⟩

theorem resolution_independence : ResolutionIndependence.{u} := by
  intro S R _ _ f K J J'
  letI := HasDerivedCategory.standard (ModuleCat.{u} S)
  letI := bounded_isKInjective J
  letI := bounded_isKInjective J'
  letI := J.quasiIso
  letI := J'.quasiIso
  let F := HomotopyCategory.quotient (ModuleCat.{u} S) (.up ℤ)
  let Qh := DerivedCategory.Qh (C := ModuleCat.{u} S)
  have hJ : IsIso (Qh.map (F.map J.ι)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)) J.ι).mpr
      (inferInstanceAs (IsIso (DerivedCategory.Q.map J.ι)))
  have hJ' : IsIso (Qh.map (F.map J'.ι)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)) J'.ι).mpr
      (inferInstanceAs (IsIso (DerivedCategory.Q.map J'.ι)))
  obtain ⟨b, hb⟩ := (IsKInjective.Qh_map_bijective (F.obj J.complex) J'.complex).surjective
    (inv (Qh.map (F.map J.ι)) ≫ Qh.map (F.map J'.ι))
  obtain ⟨g, hg⟩ := F.map_surjective b
  have hc : F.map (J.ι ≫ g) = F.map J'.ι := by
    apply (IsKInjective.Qh_map_bijective (F.obj K) J'.complex).injective
    rw [F.map_comp, Qh.map_comp, hg, hb, IsIso.hom_inv_id_assoc]
  have hq : QuasiIso g := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} S) g).mp
    apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)) g).mp
    change IsIso (Qh.map (F.map g))
    rw [hg, hb]
    infer_instance
  obtain ⟨e, rfl⟩ := (IsKInjective.quasiIso_iff g).mp hq
  letI := (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  exact ⟨e, ⟨HomotopyCategory.homotopyOfEq _ _ hc⟩,
    (coextendScalars f).mapHomotopyEquiv e, rfl, rfl⟩

theorem derived_adjunction : DerivedAdjunction.{u} := by
  intro S R _ _ f K J U
  exact coinductionCochainAdjunction f U J.complex

section HomComparison

variable {R : Type u} [CommRing R] {U V I : Complex R}

open DerivedCategory in
private def classToDerived [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (q : ℤ) : CohomologyClass U I q →ₗ[R] (Q.obj U ⟶ Q.obj (I⟦q⟧)) where
  toFun z :=
    (quotientCompQhIso (ModuleCat R)).inv.app U ≫ Qh.map z.toHom ≫
      (quotientCompQhIso (ModuleCat R)).hom.app (I⟦q⟧)
  map_add' x y := by simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r z := by
    obtain ⟨z, rfl⟩ := z.mk_surjective
    simp [← CohomologyClass.mk_smul, CohomologyClass.toHom_mk,
      Cocycle.equivHomShift_symm_smul, Linear.comp_smul, Linear.smul_comp]

open DerivedCategory in
/-- Cohomology of a signed Hom complex into a K-injective complex computes
morphisms into the corresponding shifts in the derived category. -/
def homologyHomEquiv [HasDerivedCategory.{w} (ModuleCat.{u} R)] [I.IsKInjective]
    (q : ℤ) :
    (linearHomComplex R U I).homology q ≃ₗ[R] (Q.obj U ⟶ Q.obj (I⟦q⟧)) :=
  (homologyLinearEquiv R U I q).trans <|
    LinearEquiv.ofBijective (classToDerived q) (by
      exact (Iso.homCongr ((quotientCompQhIso (ModuleCat R)).app U)
        ((quotientCompQhIso (ModuleCat R)).app (I⟦q⟧))).bijective.comp
        ((IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj U)
          (I⟦q⟧)).comp (CohomologyClass.toHom_bijective U I q)))

/-- The signed Hom map given by precomposing with a cochain map. -/
def homPrecomposition (α : U ⟶ V) (I : Complex R) :
    linearHomComplex R V I ⟶ linearHomComplex R U I where
  f q := ModuleCat.ofHom
    { toFun := fun z => (Cochain.ofHom α).comp z (zero_add q)
      map_add' := fun x y => Cochain.comp_add _ x y _
      map_smul' := fun r z => Cochain.comp_smul _ r z _ }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_ofHom_comp α z j

private theorem homologyLinearEquiv_precomp (α : U ⟶ V) (q : ℤ) (z : Cocycle V I q) :
    homologyLinearEquiv R U I q
      (homologyMap (homPrecomposition α I) q
        ((homologyLinearEquiv R V I q).symm (CohomologyClass.mk z))) =
      CohomologyClass.mk (z.precomp α) := by
  let hV := linearLeftHomologyData R V I q
  let hU := linearLeftHomologyData R U I q
  let φ := (shortComplexFunctor (ModuleCat R) (.up ℤ) q).map (homPrecomposition α I)
  let γ := ShortComplex.leftHomologyMapData φ hV hU
  have hz : γ.φK.hom z = z.precomp α := by
    apply Subtype.ext
    exact congrArg (fun a => a.hom z) γ.commi
  have hπ := congrArg (fun a => a.hom z) γ.commπ
  change γ.φH.hom (CohomologyClass.mk z) = CohomologyClass.mk (γ.φK.hom z) at hπ
  change (((hV.homologyIso.inv ≫ ShortComplex.homologyMap φ) ≫ hU.homologyIso.hom).hom
    (CohomologyClass.mk z)) = _
  rw [Category.assoc, γ.homologyMap_comm, Iso.inv_hom_id_assoc]
  rwa [hz] at hπ

open DerivedCategory in
private theorem homologyHomEquiv_precomp [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [I.IsKInjective] (α : U ⟶ V) (q : ℤ) (x : (linearHomComplex R V I).homology q) :
    homologyHomEquiv q (homologyMap (homPrecomposition α I) q x) =
      Q.map α ≫ homologyHomEquiv q x := by
  obtain ⟨z, hz⟩ := (CohomologyClass.mk_surjective (K := V) (L := I) (n := q))
    (homologyLinearEquiv R V I q x)
  rw [← (homologyLinearEquiv R V I q).symm_apply_apply x, ← hz]
  simp only [homologyHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, homologyLinearEquiv_precomp]
  change classToDerived q (CohomologyClass.mk (z.precomp α)) =
    Q.map α ≫ classToDerived q (CohomologyClass.mk z)
  unfold classToDerived
  simp only [LinearMap.coe_mk, AddHom.coe_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp, Category.assoc]
  rw [← quotientCompQhIso_inv_naturality_assoc]

theorem derivedHom_precomposition : DerivedHomPrecomposition.{u} := by
  intro R _ U V I α hα hI
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  refine ⟨homPrecomposition α I, ?_, fun q z p j h => by simp [homPrecomposition]⟩
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  have he : Function.Bijective (fun (g : DerivedCategory.Q.obj V ⟶
      DerivedCategory.Q.obj (I⟦q⟧)) => DerivedCategory.Q.map α ≫ g) :=
    (asIso (DerivedCategory.Q.map α)).symm.homFromEquiv.bijective
  have hcomp := he.comp (homologyHomEquiv (U := V) (I := I) q).bijective
  apply (homologyHomEquiv (U := U) (I := I) q).bijective.of_comp_iff' _ |>.mp
  convert hcomp using 1
  ext x
  exact homologyHomEquiv_precomp α q x

end HomComparison

section Restriction

open Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction
variable {S R : Type u} [CommRing S] [CommRing R]

private abbrev restrictComplex (f : S →+* R) :=
  (restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)

private def restrictedHomTermEquiv (f : S →+* R) (U : Complex R) (J : Complex S) (q : ℤ) :
    (restrictScalars f).obj ((restrictedHomComplex f U J).X q) ≃ₗ[S]
      (linearHomComplex S (RestrictedComplex f U) J).X q where
  toAddEquiv := AddEquiv.refl (Cochain (RestrictedComplex f U) J q)
  map_smul' s z := by
    change Cochain (RestrictedComplex f U) J q at z
    change @SMul.smul R _ (precompositionCochainModule f U J q).toSMul (f s) z =
      (s • z)
    apply Cochain.ext
    intro i j h
    rw [Cochain.smul_v]
    change (restrictScalars f).map (f s • 𝟙 (U.X i)) ≫
      z.v i j h = _
    have hs : (restrictScalars f).map (f s • 𝟙 (U.X i)) =
        s • 𝟙 ((RestrictedComplex f U).X i) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    rw [hs]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact fun x => (z.v i j h).hom.map_smul s x

/-- After restriction to S, the Hom complex with the action on its argument
has the ordinary S-linear Hom differential and scalar action. -/
def restrictedHomIso (f : S →+* R) (U : Complex R) (J : Complex S) :
    (restrictComplex f).obj (restrictedHomComplex f U J) ≅
      linearHomComplex S (RestrictedComplex f U) J :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (restrictedHomTermEquiv f U J q).toModuleIso) (fun _ _ _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rfl)

private def homologyRestrictIso (f : S →+* R) (U : Complex R) (q : ℤ) :
    ((restrictComplex f).obj U).homology q ≅ (restrictScalars f).obj (U.homology q) :=
  (U.sc q).mapHomologyIso (restrictScalars f)

private def restrictStalkIso (f : S →+* R) (M : ModuleCat.{u} R) :
    RestrictedComplex f (stalk R 0 M) ≅ stalk S 0 ((restrictScalars f).obj M) :=
  (singleMapHomologicalComplex (restrictScalars f) (.up ℤ) 0).app M

private def regularHomEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.of R R ⟶ M) ≃ₗ[R] M :=
  ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R M)

/-- Evaluation at one identifies Hom from the free rank-one stalk with
the target complex. -/
def regularHomComplexIso (I : Complex R) :
    I ≅ linearHomComplex R (stalk R 0 (ModuleCat.of R R)) I := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q => ((regularHomEquiv (I.X q)).symm.trans
      (Cochain.fromSingleLinearEquiv (R := R) (zero_add q)).symm).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change δ i j (Cochain.fromSingleMk ((regularHomEquiv (I.X i)).symm x) (zero_add i)) =
    Cochain.fromSingleMk ((regularHomEquiv (I.X j)).symm (I.d i j x)) (zero_add j)
  rw [Cochain.δ_fromSingleMk _ _ _ _ (zero_add j)]
  congr 1
  apply (regularHomEquiv (I.X j)).injective
  change I.d i j (((regularHomEquiv (I.X i)).symm x) 1) =
    (regularHomEquiv (I.X j)) ((regularHomEquiv (I.X j)).symm (I.d i j x))
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (I.d i j) ((regularHomEquiv (I.X i)).apply_symm_apply x)

end Restriction

section ShiftedHom

open Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction
open DerivedCategory (Q)
variable {S R : Type u} [CommRing S] [CommRing R]

/-- Restricting to S and taking cohomology computes the derived morphisms
from the restricted module into the translated ring. The source module
may be identified with any isomorphic S-module. -/
def shiftedHomEquiv [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (f : S →+* R) (M : ModuleCat.{u} R) {X : ModuleCat.{u} S}
    (e : (restrictScalars f).obj M ≅ X) {n : ℕ} (J : ShiftedRingResolution S n)
    (q j : ℤ) (h : (n : ℤ) + q = j) :
    (restrictScalars f).obj ((linearHomComplex R (stalk R 0 M)
      (dualizingComplex f J.complex)).homology q) ≃ₗ[S]
      (Q.obj (stalk S 0 X) ⟶ Q.obj ((stalk S 0 (ModuleCat.of S S))⟦j⟧)) := by
  haveI := bounded_isKInjective J
  haveI := J.quasiIso
  let U := stalk R 0 M
  let A := linearHomComplex R U (dualizingComplex f J.complex)
  let c := (restrictComplex f).mapIso (coinductionHomComplexIso f U J.complex) ≪≫
    restrictedHomIso f U J.complex
  let se : Q.obj (RestrictedComplex f U) ≅ Q.obj (stalk S 0 X) :=
    Q.mapIso (restrictStalkIso f M ≪≫ (CochainComplex.singleFunctor _ 0).mapIso e)
  let te : Q.obj (J.complex⟦q⟧) ≅ Q.obj ((stalk S 0 (ModuleCat.of S S))⟦j⟧) :=
    (asIso (Q.map (J.ι⟦q⟧'))).symm ≪≫
      Q.mapIso ((CategoryTheory.shiftFunctorAdd' (Complex S) (n : ℤ) q j h).symm.app _)
  exact ((homologyRestrictIso f A q).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) q).mapIso c).toLinearEquiv.trans
    ((homologyHomEquiv q).trans (Linear.homCongr S se te))

private def shiftedStalkHomEquivExt [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (X Y : ModuleCat.{u} S) (j : ℕ) :
    (Q.obj (stalk S 0 X) ⟶ Q.obj ((stalk S 0 Y)⟦(j : ℤ)⟧)) ≃ₗ[S] Ext X Y j :=
  (Linear.homCongr S (Iso.refl _) ((Q.commShiftIso (j : ℤ)).app (stalk S 0 Y))).trans
    (Ext.homLinearEquiv (R := S)).symm

private theorem shiftedStalkHom_subsingleton [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (X Y : ModuleCat.{u} S) (j : ℤ) (hj : j < 0) :
    Subsingleton (Q.obj (stalk S 0 X) ⟶ Q.obj ((stalk S 0 Y)⟦j⟧)) := by
  have := (stalk S 0 Y).isStrictlyGE_shift 0 j (-j) (by omega)
  exact DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE _
    _ 0 (-j) (by omega)

private def fromRestriction (f : S →+* R) (A : ModuleCat.{u} R) :
    (restrictScalars f).obj A →ₛₗ[f] A where
  toFun a := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finite_cohomology : FiniteCohomology.{u} := by
  intro S R _ _ _ _ _ _ _ f _ hf n _ J q
  letI := HasDerivedCategory.standard (ModuleCat.{u} S)
  let A := dualizingComplex f J.complex
  let X := (restrictScalars f).obj (ModuleCat.of R R)
  let Y := ModuleCat.of S S
  let map : S →ₗ[S] X :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_mul }
  haveI : Module.Finite S X := Module.Finite.of_surjective map hf
  let U := stalk R 0 (ModuleCat.of R R)
  let H := (linearHomComplex R U A).homology q
  haveI : Module.Finite S ((restrictScalars f).obj H) := by
    by_cases h : 0 ≤ (n : ℤ) + q
    · let j := ((n : ℤ) + q).toNat
      have hj : (j : ℤ) = (n : ℤ) + q := Int.toNat_of_nonneg h
      let e := shiftedHomEquiv f (ModuleCat.of R R) (Iso.refl X) J q j hj.symm
      exact Module.Finite.equiv (e.trans (shiftedStalkHomEquivExt X Y j)).symm
    · haveI := shiftedStalkHom_subsingleton X Y ((n : ℤ) + q) (by omega)
      let e := shiftedHomEquiv f (ModuleCat.of R R) (Iso.refl X) J q ((n : ℤ) + q) rfl
      haveI := e.injective.subsingleton
      exact Module.Finite.of_surjective (0 : S →ₗ[S] _) fun x => ⟨0, Subsingleton.elim _ x⟩
  let e' : (restrictScalars f).obj (A.homology q) ≅ (restrictScalars f).obj H :=
    (restrictScalars f).mapIso
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) q).mapIso
        (regularHomComplexIso A))
  haveI := Module.Finite.equiv e'.toLinearEquiv.symm
  exact Module.Finite.of_surjective (fromRestriction f (A.homology q)) fun x => ⟨x, rfl⟩

private def residueRestrictionEquiv [IsLocalRing S] [IsLocalRing R] (f : S →+* R)
    [IsLocalHom f] (hf : Function.Surjective f) :
    ResidueField S ≃ₗ[S] (restrictScalars f).obj (ModuleCat.of R (ResidueField R)) where
  toAddEquiv := (RingEquiv.ofBijective (ResidueField.map f)
    (localQuotient_residue_bijective f hf)).toAddEquiv
  map_smul' s z := by
    change ResidueField.map f (IsLocalRing.residue S s * z) =
      IsLocalRing.residue R (f s) * ResidueField.map f z
    rw [map_mul, ResidueField.map_residue]

private def upgradeRestriction (f : S →+* R) (hf : Function.Surjective f)
    {A B : ModuleCat.{u} R}
    (e : (restrictScalars f).obj A ≃ₗ[S] (restrictScalars f).obj B) : A ≃ₗ[R] B where
  toAddEquiv := e.toAddEquiv
  map_smul' r x := by
    obtain ⟨s, rfl⟩ := hf r
    exact e.map_smul s x

open AdvCommAlg.Gorenstein in
theorem normalization : Normalization.{u, w} := by
  intro S R _ _ _ _ _ _ _ _ f _ hf n hn J
  letI := HasDerivedCategory.standard (ModuleCat.{u} S)
  let M := ModuleCat.of R (ResidueField R)
  let X := ModuleCat.of S (ResidueField S)
  let Y := ModuleCat.of S S
  let A := linearHomComplex R (stalk R 0 M) (dualizingComplex f J.complex)
  let e := residueRestrictionEquiv f hf
  let hG := regularLocal_gorenstein S
  have hzero (q : ℤ) (hq : q ≠ 0) : IsZero (A.homology q) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    have : Subsingleton ((restrictScalars f).obj (A.homology q)) := by
      by_cases h : 0 ≤ (n : ℤ) + q
      · let j := ((n : ℤ) + q).toNat
        have hj : (j : ℤ) = (n : ℤ) + q := Int.toNat_of_nonneg h
        have hne : j ≠ n := by
          intro he
          rw [he] at hj
          omega
        haveI : Subsingleton (Ext X Y j) := localGorenstein_ext_vanishing S hG n hn j hne
        let a := shiftedHomEquiv f M e.symm.toModuleIso J q j hj.symm
        exact (a.trans (shiftedStalkHomEquivExt X Y j)).injective.subsingleton
      · haveI := shiftedStalkHom_subsingleton X Y ((n : ℤ) + q) (by omega)
        exact (shiftedHomEquiv f M e.symm.toModuleIso J q ((n : ℤ) + q) rfl).injective.subsingleton
    exact this
  obtain ⟨ε⟩ := localGorenstein_ext_equiv S hG n hn
  have a₀ : (restrictScalars f).obj (A.homology 0) ≃ₗ[S]
      (Q.obj (stalk S 0 X) ⟶ Q.obj ((stalk S 0 Y)⟦(n : ℤ)⟧)) :=
    shiftedHomEquiv f M e.symm.toModuleIso J 0 (n : ℤ) (add_zero _)
  let e₀ : A.homology 0 ≅ M :=
    (upgradeRestriction f hf
      (a₀.trans ((shiftedStalkHomEquivExt X Y n).trans ((ε.restrictScalars S).trans e)))).toModuleIso
  haveI : A.IsLE 0 := (isLE_iff A 0).mpr fun i hi =>
    (exactAt_iff_isZero_homology A i).mpr (hzero i (by omega))
  haveI : A.IsGE 0 := (isGE_iff A 0).mpr fun i hi =>
    (exactAt_iff_isZero_homology A i).mpr (hzero i (by omega))
  obtain ⟨B, ⟨a⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj A) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat R) 0
  let c := DerivedCategory.homologyFunctorFactors (ModuleCat R) 0
  let b : A.homology 0 ≅ B :=
    (c.app A).symm ≪≫ H.mapIso a ≪≫ c.app (stalk R 0 B) ≪≫ singleObjHomologySelfIso _ _ _
  exact ⟨a ≪≫ (DerivedCategory.singleFunctor (ModuleCat R) 0).mapIso (b.symm ≪≫ e₀)⟩

end ShiftedHom

end CommutativeAlgebraNotes.RegularCoverDualizingModel
