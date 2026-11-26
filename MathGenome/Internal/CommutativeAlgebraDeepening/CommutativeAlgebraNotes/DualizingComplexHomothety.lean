import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DualizingComplexHomothety
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Dual.Lemmas
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex CochainComplex HomComplex
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
open Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction
open ModuleCat (restrictScalars coextendScalars)

namespace CommutativeAlgebraNotes.DualizingComplexHomothety

open Specs.CommutativeAlgebraNotes.DualizingComplexHomothety

open CommutativeAlgebraNotes.RegularCoverDualizingModel (homPrecomposition restrictedHomIso)
open private restrictStalkIso bounded_isKInjective from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel

universe u w

abbrev homothety : HomothetyType.{u} :=
  @Specs.CommutativeAlgebraNotes.DualizingComplexHomothety.homothety

abbrev derivedHomothety : DerivedHomothetyType.{u, w} :=
  @Specs.CommutativeAlgebraNotes.DualizingComplexHomothety.derivedHomothety

theorem homothety_evaluation : HomothetyEvaluation.{u} := by
  intro S R _ _ f J r p i
  dsimp only
  have hz : ((homothety f J).f 0
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv r) :
      Cochain (dualizingComplex f J) (dualizingComplex f J) 0) =
        r • Cochain.ofHom (𝟙 (dualizingComplex f J)) := by
    unfold homothety Specs.CommutativeAlgebraNotes.DualizingComplexHomothety.homothety
    rw [mkHomFromSingle_f, ← ModuleCat.comp_apply]
    rw [Iso.inv_hom_id_assoc]
    rfl
  rw [hz, Cochain.smul_v, Cochain.ofHom_v, id_f]
  change (r • (show (coextendScalars f).obj (J.X p) from i)) (1 : R) = _
  rw [ModuleCat.CoextendScalars.smul_apply, one_mul]

private abbrev complexHom {S : Type u} [CommRing S] (P J : Complex S) := linearHomComplex S P J

section Biduality

variable {S : Type u} [CommRing S]

/-- Signed evaluation in a single degree. -/
private def bidualTerm (P J : Complex S) (a : ℤ) :
    P.X a ⟶ (complexHom (complexHom P J) J).X a :=
  ModuleCat.ofHom
    { toFun := fun x => Cochain.mk fun p q h =>
        ModuleCat.ofHom
          { toFun := fun z => (p * a).negOnePow • (z.v a q (by omega)) x
            map_add' := by intro z w; simp [smul_add]
            map_smul' := by
              intro r z
              rw [Cochain.smul_v]
              change (p * a).negOnePow • (r • (z.v a q _) x) =
                r • ((p * a).negOnePow • (z.v a q _) x)
              exact smul_comm _ _ _ }
      map_add' := by
        intro x y
        apply Cochain.ext
        intro p q h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change (p * a).negOnePow • (z.v a q _) (x + y) = _
        simp only [Cochain.add_v]
        change (p * a).negOnePow • (z.v a q _) (x + y) =
          (p * a).negOnePow • (z.v a q _) x + (p * a).negOnePow • (z.v a q _) y
        rw [map_add, smul_add]
      map_smul' := by
        intro r x
        apply Cochain.ext
        intro p q h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        simp only [Cochain.smul_v]
        change (p * a).negOnePow • (z.v a q _) (r • x) =
          r • ((p * a).negOnePow • (z.v a q _) x)
        rw [map_smul]
        exact smul_comm _ _ _ }

private lemma bidualTerm_apply (P J : Complex S) (a : ℤ) (x : P.X a) (p q : ℤ)
    (h : p + a = q) (z : Cochain P J p) :
    (show Cochain (complexHom P J) J a from bidualTerm P J a x).v p q h z =
      (p * a).negOnePow • (z.v a q (by omega)) x := rfl

private lemma negOnePow_bidual (p a : ℤ) :
    (a + 1).negOnePow * ((p + 1) * a).negOnePow = -(p * a).negOnePow := by
  rw [← Int.negOnePow_add, show a + 1 + (p + 1) * a = p * a + 2 * a + 1 by ring,
    Int.negOnePow_succ, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- The evaluation cochain map with the Koszul sign. -/
private def biduality (P J : Complex S) : P ⟶ complexHom (complexHom P J) J where
  f := bidualTerm P J
  comm' a b hab := by
    have hb : a + 1 = b := hab
    subst b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    symm
    change bidualTerm P J (a + 1) (P.d a (a + 1) x) =
      δ a (a + 1) (bidualTerm P J a x)
    apply Cochain.ext
    intro p q h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (show Cochain (complexHom P J) J _ from _).v p q h z =
      (δ a (a + 1) (bidualTerm P J a x)).v p q h z
    rw [δ_v a (a + 1) rfl _ p q h (a + p) (p + 1) (by omega) rfl]
    simp only [bidualTerm_apply]
    change (p * (a + 1)).negOnePow • (z.v (a + 1) q _) (P.d a (a + 1) x) =
      J.d (a + p) q ((p * a).negOnePow • (z.v a (a + p) _) x) +
        (a + 1).negOnePow • (((p + 1) * a).negOnePow •
          ((δ p (p + 1) z).v a q _) x)
    rw [δ_v p (p + 1) rfl z a q (by omega) (a + p) (a + 1) (by omega) rfl]
    change (p * (a + 1)).negOnePow • (z.v (a + 1) q _) (P.d a (a + 1) x) =
      J.d (a + p) q ((p * a).negOnePow • (z.v a (a + p) _) x) +
        (a + 1).negOnePow • (((p + 1) * a).negOnePow •
          (J.d (a + p) q ((z.v a (a + p) _) x) +
            (p + 1).negOnePow • (z.v (a + 1) q _) (P.d a (a + 1) x)))
    have hs : (-(p * a).negOnePow) * (p + 1).negOnePow = (p * (a + 1)).negOnePow := by
      rw [Int.negOnePow_succ, neg_mul_neg, ← Int.negOnePow_add, mul_add, mul_one]
    rw [smul_smul, negOnePow_bidual]
    simp only [smul_add, smul_smul, hs, Units.neg_smul]
    simp only [Units.smul_def, map_zsmul]
    abel

private def homPostcomposition (P : Complex S) {J K : Complex S} (g : J ⟶ K) :
    complexHom P J ⟶ complexHom P K where
  f i := ModuleCat.ofHom
    { toFun := fun z => z.comp (Cochain.ofHom g) (add_zero i)
      map_add' := fun x y => Cochain.add_comp x y _ _
      map_smul' := fun r z => Cochain.smul_comp r z _ _ }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_comp_ofHom z g j

private lemma precomp_apply {P Q : Complex S} (g : P ⟶ Q) (J : Complex S)
    (i p q : ℤ) (h : p + i = q) (z : Cochain Q J i) :
    (show Cochain P J i from (homPrecomposition g J).f i z).v p q h =
      g.f p ≫ z.v p q h := by simp [homPrecomposition]

private lemma postcomp_apply (P : Complex S) {J K : Complex S} (g : J ⟶ K)
    (i p q : ℤ) (h : p + i = q) (z : Cochain P J i) :
    (show Cochain P K i from (homPostcomposition P g).f i z).v p q h =
      z.v p q h ≫ g.f q := by simp [homPostcomposition]

private lemma biduality_natural {P Q : Complex S} (g : P ⟶ Q) (J : Complex S) :
    biduality P J ≫ homPrecomposition (homPrecomposition g J) J = g ≫ biduality Q J := by
  ext a : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (homPrecomposition (homPrecomposition g J) J).f a (bidualTerm P J a x) =
    bidualTerm Q J a (g.f a x)
  apply Cochain.ext
  intro p q h
  rw [precomp_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.comp_apply, bidualTerm_apply, bidualTerm_apply, precomp_apply, ModuleCat.comp_apply]

private lemma biduality_target_natural (P : Complex S) {J K : Complex S} (g : J ⟶ K) :
    biduality P J ≫ homPostcomposition (complexHom P J) g =
      biduality P K ≫ homPrecomposition (homPostcomposition P g) K := by
  ext a : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (homPostcomposition (complexHom P J) g).f a (bidualTerm P J a x) =
    (homPrecomposition (homPostcomposition P g) K).f a (bidualTerm P K a x)
  apply Cochain.ext
  intro p q h
  rw [postcomp_apply, precomp_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, bidualTerm_apply, bidualTerm_apply,
    postcomp_apply, ModuleCat.comp_apply]
  simp only [Units.smul_def, map_zsmul]

open private classToDerived from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel

private lemma homologyLinearEquiv_postcomp (P : Complex S) {J K : Complex S} (g : J ⟶ K)
    (i : ℤ) (z : Cocycle P J i) :
    homologyLinearEquiv S P K i
      (homologyMap (homPostcomposition P g) i
        ((homologyLinearEquiv S P J i).symm (CohomologyClass.mk z))) =
      CohomologyClass.mk (z.postcomp g) := by
  let hJ := linearLeftHomologyData S P J i
  let hK := linearLeftHomologyData S P K i
  let φ := (shortComplexFunctor (ModuleCat S) (.up ℤ) i).map (homPostcomposition P g)
  let γ := ShortComplex.leftHomologyMapData φ hJ hK
  have hz : γ.φK.hom z = z.postcomp g := by
    apply Subtype.ext
    exact congrArg (fun a => a.hom z) γ.commi
  have hπ := congrArg (fun a => a.hom z) γ.commπ
  change γ.φH.hom (CohomologyClass.mk z) = CohomologyClass.mk (γ.φK.hom z) at hπ
  change (((hJ.homologyIso.inv ≫ ShortComplex.homologyMap φ) ≫ hK.homologyIso.hom).hom
    (CohomologyClass.mk z)) = _
  rw [Category.assoc, γ.homologyMap_comm, Iso.inv_hom_id_assoc]
  rwa [hz] at hπ

open DerivedCategory in
private def projectiveHomologyEquiv [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (P J : Complex S) [P.IsKProjective] (i : ℤ) :
    (complexHom P J).homology i ≃ (Q.obj P ⟶ Q.obj (J⟦i⟧)) :=
  (homologyLinearEquiv S P J i).toEquiv.trans <|
    Equiv.ofBijective (classToDerived i) (by
      exact (Iso.homCongr ((quotientCompQhIso (ModuleCat S)).app P)
        ((quotientCompQhIso (ModuleCat S)).app (J⟦i⟧))).bijective.comp
        ((IsKProjective.Qh_map_bijective P _).comp (CohomologyClass.toHom_bijective P J i)))

open DerivedCategory in
private lemma homPostcomposition_quasiIso (P : Complex S) [P.IsKProjective]
    {J K : Complex S} (g : J ⟶ K) [QuasiIso g] : QuasiIso (homPostcomposition P g) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} S)
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  have he : Function.Bijective
      (fun h : Q.obj P ⟶ Q.obj (J⟦i⟧) => h ≫ Q.map (g⟦i⟧')) :=
    (asIso (Q.map (g⟦i⟧'))).homToEquiv.bijective
  have hc := he.comp (projectiveHomologyEquiv P J i).bijective
  apply ((projectiveHomologyEquiv P K i).bijective.of_comp_iff' _).mp
  convert hc using 1
  ext x
  obtain ⟨z, hz⟩ := (CohomologyClass.mk_surjective (K := P) (L := J) (n := i))
    (homologyLinearEquiv S P J i x)
  rw [← (homologyLinearEquiv S P J i).symm_apply_apply x, ← hz]
  simp only [Function.comp_apply, projectiveHomologyEquiv, Equiv.trans_apply,
    LinearEquiv.coe_toEquiv, LinearEquiv.apply_symm_apply, homologyLinearEquiv_postcomp]
  change classToDerived i (CohomologyClass.mk (z.postcomp g)) =
    classToDerived i (CohomologyClass.mk z) ≫ Q.map (g⟦i⟧')
  unfold classToDerived
  simp only [LinearMap.coe_mk, AddHom.coe_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_postcomp, Functor.map_comp, Category.assoc]
  rw [quotientCompQhIso_hom_naturality]

private def homToRingTermEquiv (P : Complex S) (d i j : ℤ) (h : j + i = d) :
    (complexHom P (stalk S d (ModuleCat.of S S))).X i ≃ₗ[S] Module.Dual S (P.X j) :=
  (Cochain.toSingleLinearEquiv h).trans ModuleCat.homLinearEquiv

private lemma homToRingTermEquiv_apply (P : Complex S) (d i j : ℤ) (h : j + i = d)
    (z : Cochain P (stalk S d (ModuleCat.of S S)) i) (x : P.X j) :
    homToRingTermEquiv P d i j h z x =
      (singleObjXSelf (.up ℤ) d (ModuleCat.of S S)).hom (z.v j d h x) := rfl

private lemma homToRing_isKProjective (P : Complex S) (b d : ℤ) [P.IsStrictlyGE b]
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite S (P.X i)] :
    (complexHom P (stalk S d (ModuleCat.of S S))).IsKProjective := by
  let K := complexHom P (stalk S d (ModuleCat.of S S))
  have e (i : ℤ) := homToRingTermEquiv P d i (d - i) (by omega)
  have : K.IsStrictlyLE (d - b) := (isStrictlyLE_iff K _).mpr fun i hi => by
    have : Subsingleton (P.X (d - i)) := ModuleCat.isZero_iff_subsingleton.mp
      (P.isZero_of_isStrictlyGE b _ (by omega))
    exact ModuleCat.isZero_iff_subsingleton.mpr ((e i).injective.subsingleton)
  have (i : ℤ) : Projective (K.X i) := by
    let D := ModuleCat.of S (Module.Dual S (P.X (d - i)))
    have : Module.Projective S D := inferInstanceAs (Module.Projective S (Module.Dual S _))
    exact Projective.of_iso (e i).toModuleIso.symm (inferInstanceAs (Projective D))
  exact isKProjective_of_projective K (d - b)

private lemma biduality_stalk_isIso (P : Complex S) (d : ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite S (P.X i)] :
    IsIso (biduality P (stalk S d (ModuleCat.of S S))) := by
  let J := stalk S d (ModuleCat.of S S)
  have (a : ℤ) : IsIso ((biduality P J).f a) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let Q := complexHom P J
    let e := homToRingTermEquiv P d (d - a) a (by omega)
    let E := (homToRingTermEquiv Q d a (d - a) (by omega)).trans e.symm.dualMap
    have h : ∀ x : P.X a, E (bidualTerm P J a x) =
        ((d - a) * a).negOnePow • Module.Dual.eval S (P.X a) x := by
      intro x
      apply LinearMap.ext
      intro z
      change homToRingTermEquiv Q d a (d - a) _ (bidualTerm P J a x) (e.symm z) =
        ((d - a) * a).negOnePow • z x
      rw [homToRingTermEquiv_apply, bidualTerm_apply]
      simp only [Units.smul_def, map_zsmul]
      congr 1
      have hz := congrArg (fun φ : Module.Dual S (P.X a) => φ x) (e.apply_symm_apply z)
      exact hz
    apply (E.bijective.of_comp_iff' _).mp
    have H := (MulAction.bijective (((d - a) * a).negOnePow)).comp
      (Module.bijective_dual_eval S (P.X a))
    convert H using 1
    funext x
    exact h x
  exact Hom.isIso_of_components (biduality P J)

open CommutativeAlgebraNotes.RegularCoverDualizingModel (derivedHom_precomposition)

private lemma homPrecomposition_quasiIso {P Q J : Complex S} (g : P ⟶ Q)
    [QuasiIso g] [J.IsKInjective] : QuasiIso (homPrecomposition g J) := by
  obtain ⟨k, hk, h⟩ := derivedHom_precomposition g ‹QuasiIso g› ‹J.IsKInjective›
  have he : k = homPrecomposition g J := by
    ext i : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    rw [h i z p q hpq, precomp_apply]
  rwa [he] at hk

/-- Evaluate first on a bounded finite projective resolution, then compare the
two choices of target and precompose back to the augmented complex. -/
private lemma biduality_quasiIso_of_resolution {A : Complex S} {n : ℕ}
    (J : ShiftedRingResolution S n) (P : Complex S) (b t : ℤ)
    [P.IsStrictlyGE b] [P.IsStrictlyLE t] [∀ i, Projective (P.X i)]
    [∀ i, Module.Finite S (P.X i)] (π : P ⟶ A) [QuasiIso π] :
    QuasiIso (biduality A J.complex) := by
  let K := stalk S (-(n : ℤ)) (ModuleCat.of S S)
  let e : shiftedRing S n ≅ K := ((CochainComplex.singleFunctors (ModuleCat.{u} S)).shiftIso
    (n : ℤ) (-(n : ℤ)) 0 (by omega)).app (ModuleCat.of S S)
  have := J.quasiIso
  have := bounded_isKInjective J
  let ι : K ⟶ J.complex := e.inv ≫ J.ι
  have : QuasiIso ι := inferInstanceAs (QuasiIso (e.inv ≫ J.ι))
  have : P.IsKProjective := isKProjective_of_projective P t
  have : (complexHom P K).IsKProjective := homToRing_isKProjective P b _
  have : IsIso (biduality P K) := biduality_stalk_isIso P _
  have := homPostcomposition_quasiIso P ι
  let a := homPostcomposition P ι
  have : QuasiIso a := ‹QuasiIso (homPostcomposition P ι)›
  have := homPostcomposition_quasiIso (complexHom P K) ι
  have := homPrecomposition_quasiIso (J := J.complex) a
  have hP : QuasiIso (biduality P J.complex) := by
    apply (quasiIso_iff_comp_right _ (homPrecomposition a J.complex)).mp
    rw [show biduality P J.complex ≫ homPrecomposition a J.complex =
      biduality P K ≫ homPostcomposition (complexHom P K) ι from
        (biduality_target_natural P ι).symm]
    infer_instance
  let c := homPrecomposition π J.complex
  have : QuasiIso c := homPrecomposition_quasiIso π
  have := homPrecomposition_quasiIso (J := J.complex) c
  apply (quasiIso_iff_comp_left π _).mp
  rw [← biduality_natural π J.complex]
  infer_instance

private lemma biduality_stalk_quasiIso [IsRegularLocalRing S]
    (M : ModuleCat.{u} S) [Module.Finite S M] {n : ℕ}
    (hn : ringKrullDim S = (n : WithBot ℕ∞)) (J : ShiftedRingResolution S n) :
    QuasiIso (biduality (stalk S 0 M) J.complex) := by
  obtain ⟨F, hF⟩ := AdvCommAlg.exists_minimalFreeResolution M
  have hv := AdvCommAlg.minimalFreeResolution_vanishes_above M F hF n
    (AdvCommAlg.CohenMacaulay.regularLocal_projectiveDimension_le S M n hn)
  let P := F.cochainComplex
  have : P.IsStrictlyGE (-(n : ℤ)) := (isStrictlyGE_iff P _).mpr fun i hi => by
    obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat (show i ≤ 0 by omega)
    have hk := hv k (by omega)
    exact (ModuleCat.isZero_iff_subsingleton.mpr hk).of_iso (F.cochainComplexXIso (-k) k)
  have (i : ℤ) : Module.Finite S (P.X i) := by
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
      have := hF.finite k
      exact Module.Finite.equiv (F.cochainComplexXIso (-k) k).toLinearEquiv.symm
    · have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp
        (P.isZero_of_isStrictlyLE 0 i (by omega))
      exact Module.Finite.of_surjective (0 : S →ₗ[S] P.X i)
        (fun x => ⟨0, Subsingleton.elim _ _⟩)
  exact biduality_quasiIso_of_resolution J P (-(n : ℤ)) 0 F.π'

end Biduality

section Coinduction

variable {S R : Type u} [CommRing S] [CommRing R]

private abbrev restrictedRegular (f : S →+* R) := (restrictScalars f).obj (ModuleCat.of R R)

private def coinducedTermEquiv (f : S →+* R) (Y : ModuleCat.{u} S) :
    (restrictScalars f).obj ((coextendScalars f).obj Y) ≃ₗ[S] (restrictedRegular f →ₗ[S] Y) where
  toAddEquiv := (ModuleCat.CoextendScalars.equiv f Y).toAddEquiv
  map_smul' s z := by
    apply LinearMap.ext
    intro r
    change (ModuleCat.CoextendScalars.equiv f Y z) ((show R from r) * f s) =
      s • (ModuleCat.CoextendScalars.equiv f Y z) r
    rw [mul_comm]
    exact (ModuleCat.CoextendScalars.equiv f Y z).map_smul s r

private def coinducedAsHom (f : S →+* R) (J : Complex S) :
    RestrictedComplex f (dualizingComplex f J) ≅ complexHom (stalk S 0 (restrictedRegular f)) J := by
  refine Hom.isoOfComponents (fun i => ((coinducedTermEquiv f (J.X i)).trans
    (ModuleCat.homLinearEquiv.symm.trans
      (Cochain.fromSingleLinearEquiv (zero_add i)).symm)).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ i j (Cochain.fromSingleMk (ModuleCat.ofHom (coinducedTermEquiv f (J.X i) z))
    (zero_add i)) =
      Cochain.fromSingleMk (ModuleCat.ofHom (coinducedTermEquiv f (J.X j)
        ((coextendScalars f).map (J.d i j) z))) (zero_add j)
  rw [Cochain.δ_fromSingleMk _ _ j j (zero_add j)]
  rfl

private def homAdjunctionIso (f : S →+* R) (U : Complex R) (J : Complex S) :
    RestrictedComplex f (linearHomComplex R U (dualizingComplex f J)) ≅
      complexHom (RestrictedComplex f U) J :=
  ((restrictScalars f).mapHomologicalComplex (.up ℤ)).mapIso
      (coinductionHomComplexIso f U J) ≪≫ restrictedHomIso f U J

private lemma restricted_homothety_eq_biduality (f : S →+* R) (J : Complex S) :
    let D := dualizingComplex f J
    (restrictStalkIso f (ModuleCat.of R R)).inv ≫
      ((restrictScalars f).mapHomologicalComplex (.up ℤ)).map (homothety f J) ≫
      (homAdjunctionIso f D J).hom ≫ homPrecomposition (coinducedAsHom f J).inv J =
      biduality (stalk S 0 (restrictedRegular f)) J := by
  dsimp only
  let A := stalk S 0 (restrictedRegular f)
  let D := dualizingComplex f J
  let e₀ := restrictStalkIso f (ModuleCat.of R R)
  let e := coinducedAsHom f J
  let c := homAdjunctionIso f D J
  apply from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let r := (singleObjXSelf (.up ℤ) 0 (restrictedRegular f)).hom x
  have hx : e₀.inv.f 0 x = (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv r := by
    change ((singleMapHomologicalComplex (restrictScalars f) (.up ℤ) 0).inv.app
      (ModuleCat.of R R)).f 0 x = _
    rw [singleMapHomologicalComplex_inv_app_self, ModuleCat.comp_apply]
    rfl
  apply Cochain.ext₀
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let y : Cochain (RestrictedComplex f D) J 0 :=
    c.hom.f 0 ((homothety f J).f 0 (e₀.inv.f 0 x))
  change (show Cochain (complexHom A J) J 0 from (homPrecomposition e.inv J).f 0 y).v
    p p (add_zero p) z = (bidualTerm A J 0 x : Cochain (complexHom A J) J 0).v p p
      (add_zero p) z
  rw [precomp_apply, ModuleCat.comp_apply, bidualTerm_apply, mul_zero, Int.negOnePow_zero,
    one_smul]
  have hy : y.v p p (add_zero p) =
      adjunction f (D.X p) (J.X p)
        (((homothety f J).f 0 (e₀.inv.f 0 x) : Cochain D D 0).v p p (add_zero p)) := rfl
  rw [hy, hx, homothety_evaluation f J r p (e.inv.f p z)]
  rfl

end Coinduction

theorem homothety_quasiIso : HomothetyQuasiIso.{u} := by
  intro S R _ _ _ _ _ _ _ f _ hf n hn J
  let A := restrictedRegular f
  let k : S →ₗ[S] A :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_mul }
  have : Module.Finite S A := Module.Finite.of_surjective k hf
  let g := homothety f J.complex
  rw [← quasiIso_map_iff_of_preservesHomology g (restrictScalars f)]
  let e₀ := restrictStalkIso f (ModuleCat.of R R)
  let e := homAdjunctionIso f (dualizingComplex f J.complex) J.complex
  let a := homPrecomposition (coinducedAsHom f J.complex).inv J.complex
  have hJ := bounded_isKInjective J
  have ha : QuasiIso a := homPrecomposition_quasiIso _
  let G := (restrictScalars f).mapHomologicalComplex (.up ℤ)
  change QuasiIso (G.map g)
  apply (quasiIso_iff_comp_right _ (e.hom ≫ a)).mp
  apply (quasiIso_iff_comp_left e₀.inv _).mp
  rw [restricted_homothety_eq_biduality]
  exact biduality_stalk_quasiIso A hn J

theorem derivedHomothety_isIso : DerivedHomothetyIsIso.{u, w} := by
  intro S R _ _ _ _ _ _ _ _ f _ hf n hn J
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) (homothety f J.complex)).mpr
    (homothety_quasiIso f hf hn J)

end CommutativeAlgebraNotes.DualizingComplexHomothety
