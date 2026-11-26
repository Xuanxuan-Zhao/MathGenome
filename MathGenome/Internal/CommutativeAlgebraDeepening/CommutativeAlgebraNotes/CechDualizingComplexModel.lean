import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechDualizingComplexModel
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CochainLinearTensorHomAdjunction
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.EndomorphismsOfResidueHull
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExactDualCochainCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.RingTheory.Flat.CategoryTheory

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open CochainComplex HomComplex HomologicalComplex
open scoped ChangeOfRings

namespace CommutativeAlgebraNotes

universe u w

open Specs.CommutativeAlgebraNotes.CechDualizingComplexModel
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
  (Complex ShiftedRingResolution shiftedRing stalk)
open ExactDualCochainCohomologySpecs (hull hullInDegreeZero)
open ModuleCat (restrictScalars coextendScalars extendScalars)

abbrev cechDual : CechDualType.{u} :=
  @Specs.CommutativeAlgebraNotes.CechDualizingComplexModel.cechDual

section DualTerms

private def intoStalkTerm {A : Type u} [CommRing A] (K : Complex A)
    (J : ModuleCat.{u} A) (i : ℤ) :
    (linearHomComplex A K (stalk A 0 J)).X i ≃ₗ[A] (K.X (-i) ⟶ J) :=
  Cochain.toSingleLinearEquiv (neg_add_cancel i)

private theorem intoStalkTerm_d {A : Type u} [CommRing A] (K : Complex A)
    (J : ModuleCat.{u} A) (i j : ℤ) (z : (linearHomComplex A K (stalk A 0 J)).X i) :
    intoStalkTerm K J j ((linearHomComplex A K (stalk A 0 J)).d i j z) =
      j.negOnePow • (K.d (-j) (-i) ≫ intoStalkTerm K J i z) := by
  obtain ⟨g, hg⟩ := Cochain.toSingleMk_surjective
    (show Cochain K (stalk A 0 J) i from z) (-i) (neg_add_cancel i)
  change intoStalkTerm K J j (δ i j (show Cochain K (stalk A 0 J) i from z)) = _
  rw [← hg, Cochain.δ_toSingleMk _ _ _ _ (neg_add_cancel j)]
  simp only [Units.smul_def, map_zsmul]
  have he (a : ℤ) (f : K.X (-a) ⟶ J) :
      intoStalkTerm K J a (Cochain.toSingleMk f (neg_add_cancel a)) = f :=
    Cochain.toSingleEquiv_toSingleMk f (neg_add_cancel a)
  rw [he, he]

variable {R : Type u} [CommRing R] [IsLocalRing R]

private def dualTerm (E : ResidueFieldEnvelope R) (K : Complex R) (i : ℤ) :
    ((matlisDualCochain E).obj (op K)).X i ≃ₗ[R] (K.X (-i) ⟶ hull E) :=
  intoStalkTerm K (hull E) i

private theorem dualTerm_isZero (E : ResidueFieldEnvelope R) (K : Complex R) (i : ℤ)
    (h : IsZero (K.X (-i))) : IsZero (((matlisDualCochain E).obj (op K)).X i) := by
  let : Subsingleton (K.X (-i) ⟶ hull E) := ⟨h.eq_of_src⟩
  have := (dualTerm E K i).injective.subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

theorem cechDual_bounded_injective : BoundedInjectiveCechDual.{u} := by
  intro R _ _ E rs
  let K := CechComplex rs
  let W := cechDual E rs
  have hI (i : ℤ) : Injective (W.X i) := by
    let A := K.X (-i)
    let : Module.Flat R A := Cech.flat rs (-i)
    have hE : Injective (hull E) :=
      (Module.injective_iff_injective_object R E.carrier).mp E.isEnvelope.injectiveModule
    exact Injective.of_iso (dualTerm E K i).toModuleIso.symm
      ((ihom.adjunction A).map_injective _ hE)
  have hge : W.IsStrictlyGE (-(rs.length : ℤ)) := (isStrictlyGE_iff _ _).mpr fun i hi =>
    dualTerm_isZero E K i (Cech.isZero_X rs (-i) (Or.inr (by omega)))
  have hle : W.IsStrictlyLE 0 := (isStrictlyLE_iff _ _).mpr fun i hi =>
    dualTerm_isZero E K i (Cech.isZero_X rs (-i) (Or.inl (by omega)))
  exact ⟨hI, hge, hle, isKInjective_of_injective W (-(rs.length : ℤ))⟩

end DualTerms

section DerivedDual

variable {R : Type u} [CommRing R] [IsLocalRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

private def dualOfDerivedIso (E : ResidueFieldEnvelope R) {K L : Complex R}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj ((matlisDualCochain E).obj (op L)) ≅
      DerivedCategory.Q.obj ((matlisDualCochain E).obj (op K)) := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)
  let F := matlisDualCochain E ⋙ Q
  have hF : W.op.IsInvertedBy F := by
    intro U V f hf
    have hq : QuasiIso f.unop := hf
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      (matlisDualCochain_quasiIso E f.unop hq)
  let D := Localization.lift F hF Q.op
  let a := Localization.fac F hF Q.op
  exact (a.app (op L)).symm ≪≫ D.mapIso e.op ≪≫ a.app (op K)

private theorem cech_computes_derivedTorsionOfRing [IsNoetherianRing R]
    (rs : List R) (hrs : Ideal.span {r | r ∈ rs} = maximalIdeal R) :
    Nonempty (Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology.derivedTorsionOfRing R ≅
      DerivedCategory.Q.obj (CechComplex rs)) := by
  let A := ModuleCat.of R R
  let K : CochainComplex.Plus (ModuleCat.{u} R) := ⟨stalk R 0 A, ⟨0, inferInstance⟩⟩
  let h : (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj A ≅
      DerivedCategory.Plus.Q.obj K := Iso.refl _
  obtain ⟨T, ⟨e₁⟩, ⟨e₂⟩⟩ := derivedCechComparison (maximalIdeal R) rs hrs
  let C := (idealTorsionFunctor (maximalIdeal R)).rightDerivedFunctorPlus
  exact ⟨DerivedCategory.Plus.ι.mapIso (C.mapIso h ≪≫ e₂.app _) ≪≫ e₁.app K ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor (CechComplex rs))⟩

theorem cechDual_generator_independence : CechDualGeneratorIndependence.{u, w} := by
  intro R _ _ _ _ E rs ts hrs hts
  obtain ⟨e⟩ := cech_computes_derivedTorsionOfRing rs hrs
  obtain ⟨e'⟩ := cech_computes_derivedTorsionOfRing ts hts
  exact ⟨dualOfDerivedIso E (e'.symm ≪≫ e)⟩

end DerivedDual

section Resolution

variable {S : Type u} [CommRing S] [IsLocalRing S]

/-- Dualizing a stalk in degree `i` produces a stalk in degree `-i`. -/
private def dualStalkIso (E : ResidueFieldEnvelope S) (A : ModuleCat.{u} S) (i : ℤ) :
    (matlisDualCochain E).obj (op (stalk S i A)) ≅
      stalk S (-i) (ModuleCat.of S (A ⟶ hull E)) := by
  let K := stalk S i A
  let W := (matlisDualCochain E).obj (op K)
  let B := ModuleCat.of S (A ⟶ hull E)
  let hzero (j : ℤ) (hj : j ≠ -i) : IsZero (W.X j) :=
    dualTerm_isZero E K j (isZero_single_obj_X _ _ _ _ (by omega))
  let htop : W.X (-i) ≅ B :=
    (dualTerm E K (-i)).toModuleIso ≪≫
      ((linearCoyoneda S (ModuleCat.{u} S)).mapIso
        (singleObjXIsoOfEq (.up ℤ) i A (- -i) (by omega)).symm.op).app (hull E)
  refine HomologicalComplex.Hom.isoOfComponents (fun j => ?_) (fun j k h => ?_)
  · by_cases hj : j = -i
    · exact W.XIsoOfEq hj ≪≫ htop ≪≫ (singleObjXIsoOfEq (.up ℤ) (-i) B j hj).symm
    · exact (hzero j hj).iso (isZero_single_obj_X _ _ _ _ hj)
  · have hd : W.d j k = 0 := by
      by_cases hj : j = -i
      · change j + 1 = k at h
        exact (hzero k (by omega)).eq_of_tgt _ _
      · exact (hzero j hj).eq_of_src _ _
    change _ = W.d j k ≫ _
    rw [hd]
    simp [stalk, CochainComplex.singleFunctor]

omit [IsLocalRing S] in
private theorem exists_quasiIso_into_KInjective
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] {K L : Complex S} [L.IsKInjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    ∃ ι : K ⟶ L, QuasiIso ι := by
  let F := HomotopyCategory.quotient (ModuleCat.{u} S) (.up ℤ)
  let a := DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)
  obtain ⟨b, hb⟩ := (IsKInjective.Qh_map_bijective (F.obj K) L).surjective
    (a.inv.app K ≫ e.hom ≫ a.hom.app L)
  obtain ⟨ι, hι⟩ := F.map_surjective b
  refine ⟨ι, (DerivedCategory.isIso_Q_map_iff_quasiIso _ ι).mp ?_⟩
  apply (NatIso.isIso_map_iff a ι).mp
  change IsIso (DerivedCategory.Qh.map (F.map ι))
  rw [hι, hb]
  exact (a.symm.app K ≪≫ e ≪≫ a.app L).isIso_hom

theorem cechDual_resolution : CechDualResolution.{u} := by
  intro S _ _ _ n hn E ss hss
  let := HasDerivedCategory.standard (ModuleCat.{u} S)
  let A := hull E
  let K := stalk S (n : ℤ) A
  let Q := DerivedCategory.Q (C := ModuleCat.{u} S)
  obtain ⟨eC⟩ := cech_computes_derivedTorsionOfRing ss hss
  obtain ⟨eT⟩ := gorenstein_top_localCohomology
    (AdvCommAlg.Gorenstein.regularLocal_gorenstein S) n hn E
  let eShift := (DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso
    (-(n : ℤ)) (n : ℤ) 0 (neg_add_cancel _)
  have e : Q.obj (CechComplex ss) ≅ Q.obj K := eC.symm ≪≫ eT ≪≫ eShift.app A
  let endIso : S ≃ₗ[S] (A ⟶ A) :=
    (AdicCompletion.ofLinearEquiv (maximalIdeal S) S).trans
      ((residueHullEndomorphismEquiv E).toLinearEquiv.trans
        (ModuleCat.homLinearEquiv (R := S) (S := S) (M := A) (N := A)).symm)
  let single := CochainComplex.singleFunctor (ModuleCat.{u} S) (-(n : ℤ))
  let eRing : shiftedRing S n ≅ stalk S (-(n : ℤ)) (ModuleCat.of S (A ⟶ A)) :=
    ((CochainComplex.singleFunctors (ModuleCat.{u} S)).shiftIso (n : ℤ) (-(n : ℤ)) 0
      (add_neg_cancel _)).app (ModuleCat.of S S) ≪≫ single.mapIso endIso.toModuleIso
  have eW : Q.obj (shiftedRing S n) ≅ Q.obj (cechDual E ss) :=
    Q.mapIso (eRing ≪≫ (dualStalkIso E A n).symm) ≪≫ dualOfDerivedIso E e
  obtain ⟨hI, hge, hle, hK⟩ := cechDual_bounded_injective E ss
  obtain ⟨ι, hι⟩ := exists_quasiIso_into_KInjective eW
  exact ⟨⟨cechDual E ss, ι, hι, hI, -(ss.length : ℤ), 0, hge, hle⟩, rfl⟩

end Resolution

open private extendCech extendComplex exists_generating_list span_map_list
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange

section ChangeOfRings

variable {S R : Type u} [CommRing S] [CommRing R]

private abbrev restrictedRing (f : S →+* R) : ModuleCat.{u} S :=
  (restrictScalars f).obj (ModuleCat.of R R)

/-- Transpose the two arguments in `Hom_S(R, Hom_S(X, A))`. -/
private def transposeCoinducedHom (f : S →+* R) (X A : ModuleCat.{u} S)
    (g : (coextendScalars f).obj (ModuleCat.of S (X ⟶ A))) :
    X ⟶ (restrictScalars f).obj ((coextendScalars f).obj A) :=
  ModuleCat.ofHom (X := X) (Y := (restrictScalars f).obj ((coextendScalars f).obj A))
    { toFun := fun x =>
        (ModuleCat.CoextendScalars.equiv f A).symm
          { toFun := fun r => g r x
            map_add' := fun r r' => by
              change ((ModuleCat.CoextendScalars.equiv f _ g) (r + r')) x = _
              rw [map_add]
              rfl
            map_smul' := fun s r => by
              change ((ModuleCat.CoextendScalars.equiv f _ g) (s • r)) x = _
              rw [map_smul]
              rfl }
      map_add' := fun x y => by
        apply ModuleCat.CoextendScalars.ext
        ext r
        exact (g r).hom.map_add x y
      map_smul' := fun s x => by
        apply ModuleCat.CoextendScalars.ext
        ext r
        change g r (s • x) = g ((show R from r) * f s) x
        rw [mul_comm (show R from r)]
        change g r (s • x) = ((ModuleCat.CoextendScalars.equiv f _ g)
          (s • (r : restrictedRing f))) x
        rw [(ModuleCat.CoextendScalars.equiv f _ g).map_smul]
        exact (g r).hom.map_smul s x }

private def untransposeCoinducedHom (f : S →+* R) (X A : ModuleCat.{u} S)
    (g : X ⟶ (restrictScalars f).obj ((coextendScalars f).obj A)) :
    (coextendScalars f).obj (ModuleCat.of S (X ⟶ A)) :=
  (ModuleCat.CoextendScalars.equiv f _).symm
    { toFun := fun r => ModuleCat.ofHom
        { toFun := fun x => (show (coextendScalars f).obj A from g x) r
          map_add' := fun x y => by
            change ((ModuleCat.CoextendScalars.equiv f A) (g (x + y))) r = _
            rw [g.hom.map_add]
            exact (ModuleCat.CoextendScalars.equiv f A).map_add (g x) (g y) |>
              congrArg (fun h => h r)
          map_smul' := fun s x => by
            change ((ModuleCat.CoextendScalars.equiv f A) (g (s • x))) r = _
            rw [map_smul]
            change (show (coextendScalars f).obj A from g x) ((show R from r) * f s) =
              s • (show (coextendScalars f).obj A from g x) r
            rw [mul_comm (show R from r)]
            exact (ModuleCat.CoextendScalars.equiv f A (g x)).map_smul s
              (r : restrictedRing f) }
      map_add' := fun r r' => by
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => (ModuleCat.CoextendScalars.equiv f A (g x)).map_add r r'
      map_smul' := fun s r => by
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => (ModuleCat.CoextendScalars.equiv f A (g x)).map_smul s r }

private def coinducedHomEquiv (f : S →+* R) (X A : ModuleCat.{u} S) :
    (coextendScalars f).obj (ModuleCat.of S (X ⟶ A)) ≃ₗ[R]
      ((extendScalars f).obj X ⟶ (coextendScalars f).obj A) := by
  let e := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homAddEquiv
    X ((coextendScalars f).obj A)
  refine
    { toFun := fun g => e.symm (transposeCoinducedHom f X A g)
      invFun := fun g => untransposeCoinducedHom f X A (e g)
      left_inv := fun g => ?_
      right_inv := fun g => ?_
      map_add' := fun g h => ?_
      map_smul' := fun r g => ?_ }
  · apply e.injective
    simp only [map_add, e.apply_symm_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ModuleCat.CoextendScalars.ext
    ext r
    rfl
  · have he (g : (extendScalars f).obj X ⟶ (coextendScalars f).obj A) (x : X) :
        (show (coextendScalars f).obj A from e g x) = g ((1 : R) ⊗ₜ[S,f] x) := rfl
    apply e.injective
    rw [e.apply_symm_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ModuleCat.CoextendScalars.ext
    ext t
    change g ((show R from t) * r) x =
      (show (coextendScalars f).obj A from e (r • e.symm (transposeCoinducedHom f X A g)) x) t
    rw [he]
    change g ((show R from t) * r) x =
      (r • e.symm (transposeCoinducedHom f X A g) ((1 : R) ⊗ₜ[S,f] x)) t
    rw [← he, e.apply_symm_apply]
    rfl
  · change untransposeCoinducedHom f X A (e (e.symm (transposeCoinducedHom f X A g))) = g
    rw [e.apply_symm_apply]
    apply ModuleCat.CoextendScalars.ext
    ext r x
    rfl
  · apply e.injective
    rw [e.apply_symm_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ModuleCat.CoextendScalars.ext
    ext r
    rfl

private theorem coinducedHomEquiv_precomp (f : S →+* R) {X Y : ModuleCat.{u} S}
    (A : ModuleCat.{u} S) (v : X ⟶ Y)
    (g : (coextendScalars f).obj (ModuleCat.of S (Y ⟶ A))) :
    coinducedHomEquiv f X A ((coextendScalars f).map ((MonoidalClosed.pre v).app A) g) =
      (extendScalars f).map v ≫ coinducedHomEquiv f Y A g := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} f
  apply (adj.homEquiv X ((coextendScalars f).obj A)).injective
  rw [adj.homEquiv_naturality_left]
  change adj.homEquiv X _
      ((adj.homEquiv X _).symm (transposeCoinducedHom f X A
        ((coextendScalars f).map ((MonoidalClosed.pre v).app A) g))) =
    v ≫ adj.homEquiv Y _ ((adj.homEquiv Y _).symm (transposeCoinducedHom f Y A g))
  simp only [Equiv.apply_symm_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ModuleCat.CoextendScalars.ext
  ext r
  rfl

open Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction (CoinducedComplex)

private def coinducedStalkDualIso (f : S →+* R) (K : Complex S) (A : ModuleCat.{u} S) :
    CoinducedComplex f (linearHomComplex S K (stalk S 0 A)) ≅
      linearHomComplex R ((extendComplex f).obj K) (stalk R 0 ((coextendScalars f).obj A)) := by
  letI := (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  let F := coextendScalars.{u, u, u} f
  let V := (extendComplex f).obj K
  let B := F.obj A
  let a := fun i => F.mapIso (intoStalkTerm K A i).toModuleIso
  let b := fun i => coinducedHomEquiv f (K.X (-i)) A
  let c := fun i => intoStalkTerm V B i
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => a i ≪≫ (b i).toModuleIso ≪≫ (c i).symm.toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (c j).injective
  change c j ((linearHomComplex R V (stalk R 0 B)).d i j ((c i).symm (b i ((a i).hom z)))) =
    c j ((c j).symm (b j ((a j).hom (F.map ((linearHomComplex S K (stalk S 0 A)).d i j) z))))
  rw [intoStalkTerm_d, (c j).apply_symm_apply, (c i).apply_symm_apply]
  let v := K.d (-j) (-i)
  have hd : (linearHomComplex S K (stalk S 0 A)).d i j ≫ (intoStalkTerm K A j).toModuleIso.hom =
      j.negOnePow • ((intoStalkTerm K A i).toModuleIso.hom ≫ (MonoidalClosed.pre v).app A) := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => intoStalkTerm_d K A i j x
  have hm := congrArg (fun g => F.map g) hd
  simp only [Functor.map_comp] at hm
  have hz := ConcreteCategory.congr_hom hm z
  change (a j).hom (F.map ((linearHomComplex S K (stalk S 0 A)).d i j) z) =
      j.negOnePow • F.map ((MonoidalClosed.pre v).app A) ((a i).hom z) at hz
  rw [hz]
  let z' : (coextendScalars f).obj (ModuleCat.of S (K.X (-j) ⟶ A)) :=
    F.map ((MonoidalClosed.pre v).app A) ((a i).hom z)
  simp only [Units.smul_def]
  change _ = b j ((j.negOnePow : ℤ) • z')
  rw [map_zsmul]
  exact congrArg (fun h : V.X (-j) ⟶ B => (j.negOnePow : ℤ) • h)
    (coinducedHomEquiv_precomp f A v ((a i).hom z)).symm

open CochainTensorHom (homMap homMap_apply)

private theorem homMap_inv_id {K L A B : Complex R} (e : K ≅ L) (a : A ≅ B) :
    homMap e.inv a.hom ≫ homMap e.hom a.inv = 𝟙 (linearHomComplex R K A) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, homMap_apply,
    HomologicalComplex.id_f, ModuleCat.id_apply]
  change ((a.hom ≫ a.inv).f q) (z.v p q hpq (((e.hom ≫ e.inv).f p) x)) = z.v p q hpq x
  rw [a.hom_inv_id, e.hom_inv_id]
  rfl

private def homComplexCongr {K L A B : Complex R} (e : K ≅ L) (a : A ≅ B) :
    linearHomComplex R K A ≅ linearHomComplex R L B where
  hom := homMap e.inv a.hom
  inv := homMap e.hom a.inv
  hom_inv_id := homMap_inv_id e a
  inv_hom_id := homMap_inv_id e.symm a.symm

theorem coinduced_cechDual_iso_of_image : DescendedCechDualComparison.{u} := by
  intro S R _ _ _ _ _ _ f _ hf E F ss _
  obtain ⟨e, _⟩ := localQuotient_envelope_equiv f hf E F
  let b := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).mapIso e.toModuleIso.symm
  exact ⟨coinducedStalkDualIso f (CechComplex ss) (hull E) ≪≫
    homComplexCongr (extendCech f ss) b⟩

end ChangeOfRings

open RegularCoverDualizingModel (dualizingComplex dualizingObject resolution_independence)

theorem cechDual_represents_dualizingObject : CechDualRepresentsDualizingObject.{u, w} := by
  intro S R _ _ _ _ _ _ _ _ f _ hf n hn J F rs hrs
  obtain ⟨ss, hss⟩ := exists_generating_list (maximalIdeal S)
  obtain ⟨E⟩ := residueFieldEnvelope_exists S
  obtain ⟨K, hK⟩ := cechDual_resolution hn E ss hss
  obtain ⟨e⟩ := coinduced_cechDual_iso_of_image f hf E F ss hss
  have hm : Ideal.span {r | r ∈ ss.map f} = maximalIdeal R := by
    rw [span_map_list, hss, IsLocalRing.map_maximalIdeal_of_surjective f hf]
  obtain ⟨a⟩ := cechDual_generator_independence F rs (ss.map f) hrs hm
  obtain ⟨_, _, g, _, _⟩ := resolution_independence f K J
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let b : Q.obj (dualizingComplex f (cechDual E ss)) ≅ Q.obj (dualizingComplex f K.complex) :=
    Q.mapIso (eqToIso (congrArg (dualizingComplex f) hK.symm))
  let d := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  let eJ := d.symm.app _ ≪≫ DerivedCategory.Qh.mapIso (HomotopyCategory.isoOfHomotopyEquiv g) ≪≫
    d.app _
  exact ⟨a ≪≫ Q.mapIso e.symm ≪≫ b ≪≫ eJ⟩

theorem dualizingObject_regularCover_independence : RegularCoverIndependence.{u, w} := by
  intro S T R _ _ _ _ _ _ _ _ _ _ _ f g _ _ hf hg n m hn hm J K
  obtain ⟨rs, hrs⟩ := exists_generating_list (maximalIdeal R)
  obtain ⟨F⟩ := residueFieldEnvelope_exists R
  obtain ⟨a⟩ := cechDual_represents_dualizingObject f hf hn J F rs hrs
  obtain ⟨b⟩ := cechDual_represents_dualizingObject g hg hm K F rs hrs
  exact ⟨a.symm ≪≫ b⟩

end CommutativeAlgebraNotes
