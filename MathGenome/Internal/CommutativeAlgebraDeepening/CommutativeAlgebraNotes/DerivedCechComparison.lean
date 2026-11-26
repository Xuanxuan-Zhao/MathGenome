import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveCechComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.BoundedAboveFlatTensor
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivedCechComparison
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechToCohomology

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped ZeroObject

namespace CommutativeAlgebraNotes

noncomputable section

universe u w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

private abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R
private abbrev Cpx (R : Type u) [CommRing R] := CochainComplex (Mod R) ℤ
private abbrev CpxPlus (R : Type u) [CommRing R] := CochainComplex.Plus (Mod R)

local notation "upZ" => ComplexShape.up ℤ

private theorem cechTensor_isStrictlyGE (rs : List R) (K : Cpx R) (a : ℤ)
    [K.IsStrictlyGE a] : ((cechTensorFunctor rs).obj K).IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  change IsZero ((HomologicalComplex.tensorObj (CechComplex rs) K).X n)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  by_cases hp : p < 0
  · exact ((tensorRight (K.X q)).map_isZero
      (Cech.isZero_X rs p (Or.inl hp))).eq_of_src _ _
  · exact ((tensorLeft ((CechComplex rs).X p)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE (K := K) a q (by omega))).eq_of_src _ _

private def cechTensorPlus (rs : List R) : CpxPlus R ⥤ CpxPlus R :=
  ObjectProperty.lift _ (CochainComplex.Plus.ι (Mod R) ⋙ cechTensorFunctor rs)
    (fun ⟨K, a, _ha⟩ => ⟨a, cechTensor_isStrictlyGE rs K a⟩)

private theorem cechTensor_quasiIso (rs : List R) {K L : Cpx R} (f : K ⟶ L)
    (hf : QuasiIso f) : QuasiIso ((cechTensorFunctor rs).map f) := by
  apply boundedAboveFlatTensorQuasiIso R (CechComplex rs) (Cech.flat rs) _ f hf
  refine ⟨rs.length, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩
  intro n hn
  exact Cech.isZero_X rs n (Or.inr hn)

open private singleTensorTerm from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveCechComparison

private abbrev stalk (R : Type u) [CommRing R] := single (Mod R) upZ 0
private abbrev unit (R : Type u) [CommRing R] := tensorUnit (Mod R) upZ

private def rowFunctor (F : Cpx R) : Mod R ⥤ Cpx R where
  obj M := ((tensorRight M).mapHomologicalComplex upZ).obj F
  map {M N} f := {
    f i := F.X i ◁ f
    comm' i j _ := by
      change (F.X i ◁ f) ≫ (F.d i j ▷ N) = (F.d i j ▷ M) ≫ (F.X j ◁ f)
      exact whisker_exchange _ _ }
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro i
    exact whiskerLeft_id (F.X i) M
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro i
    exact whiskerLeft_comp (F.X i) f g

/-- A row of the tensor double complex of a complex and a concentrated module. -/
private def rowIso (F : Cpx R) :
    rowFunctor F ≅ stalk R ⋙ tensorLeft F :=
  NatIso.ofComponents (fun M => HomologicalComplex.Hom.isoOfComponents (singleTensorTerm F M)
    (fun i j h => by
      change i + 1 = j at h
      subst j
      let B := (stalk R).obj M
      change ιTensorObj F B i 0 i _ ≫ (HomologicalComplex.tensorObj F B).d i (i + 1) =
        (F.d i (i + 1) ▷ B.X 0) ≫ ιTensorObj F B (i + 1) 0 (i + 1) _
      have h₂ := mapBifunctor.d₂_eq F B (curriedTensor (Mod R)) upZ i
        (show (upZ).Rel (0 : ℤ) (1 : ℤ) from rfl) (i + 1) rfl
      rw [mapBifunctor.d_eq F B (curriedTensor (Mod R)) upZ, Preadditive.comp_add,
        mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
        mapBifunctor.d₁_eq _ _ _ _ (show (upZ).Rel i (i + 1) from rfl) _ _ (add_zero _), h₂]
      change (1 : ℤˣ) • (_ : _ ⟶ _) +
        i.negOnePow • ((F.X i ◁ B.d 0 1) ≫ _) = _
      have hz : B.d 0 1 = 0 := rfl
      rw [hz, MonoidalPreadditive.whiskerLeft_zero, zero_comp, smul_zero, add_zero, one_smul]
      rfl)) (fun {M N} f => by
    apply HomologicalComplex.hom_ext
    intro i
    change (F.X i ◁ f) ≫ ιTensorObj F ((stalk R).obj N) i 0 i _ =
      ιTensorObj F ((stalk R).obj M) i 0 i _ ≫
        (HomologicalComplex.tensorHom (𝟙 F) ((stalk R).map f)).f i
    unfold HomologicalComplex.tensorHom
    rw [ι_mapBifunctorMap, id_f, (curriedTensor (Mod R)).map_id, NatTrans.id_app, id_comp]
    rfl)

private def unitRowIso : rowFunctor (unit R) ≅ stalk R :=
  rowIso (unit R) ≪≫ Functor.isoWhiskerLeft (stalk R)
    (leftUnitorNatIso (Cpx R)) ≪≫ Functor.rightUnitor _

open AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations (FiniteDiagonals)
open AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations (quadrantFinite)
open AdvancedHomologicalAlgebra.DoubleComplexConvergence (double_complex_comparison)

private abbrev doubleTensor (F K : Cpx R) : HomologicalComplex₂ (Mod R) upZ upZ :=
  (((curriedTensor (Mod R)).mapBifunctorHomologicalComplex upZ upZ).obj F).obj K

private theorem doubleTensor_finite (F K : Cpx R) (a : ℤ)
    (hF : ∀ p < 0, IsZero (F.X p)) [K.IsStrictlyGE a] :
    FiniteDiagonals (doubleTensor F K) := by
  apply quadrantFinite _ 0 a
  intro p q h
  change IsZero (F.X p ⊗ K.X q)
  by_cases hp : p < 0
  · exact (tensorRight (K.X q)).map_isZero (hF p hp)
  · exact (tensorLeft (F.X p)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE (K := K) a q (by omega))

private theorem tensorLeft_map_total (F : Cpx R) {K L : Cpx R} (f : K ⟶ L) :
    (tensorLeft F).map f = HomologicalComplex₂.total.map
      ((((curriedTensor (Mod R)).mapBifunctorHomologicalComplex upZ upZ).obj F).map f) upZ := by
  change mapBifunctorMap (𝟙 F) f (curriedTensor (Mod R)) upZ = _
  unfold mapBifunctorMap
  rw [((curriedTensor (Mod R)).mapBifunctorHomologicalComplex upZ upZ).map_id]
  simp only [NatTrans.id_app, Category.id_comp]

section TotalComparison

variable (I : Ideal R) (rs : List R)

private abbrev torsionComplex := (idealTorsionFunctor I).mapHomologicalComplex upZ

private def rowComparison
    (η : idealTorsionFunctor I ⋙ stalk R ⟶ stalk R ⋙ tensorLeft (CechComplex rs)) :
    idealTorsionFunctor I ⋙ rowFunctor (unit R) ⟶ rowFunctor (CechComplex rs) :=
  (Functor.isoWhiskerLeft _ unitRowIso).hom ≫ η ≫ (rowIso (CechComplex rs)).inv

private def doubleComparison
    (η : idealTorsionFunctor I ⋙ stalk R ⟶ stalk R ⋙ tensorLeft (CechComplex rs))
    (K : Cpx R) :
    doubleTensor (unit R) ((torsionComplex I).obj K) ⟶ doubleTensor (CechComplex rs) K :=
  HomologicalComplex₂.homMk
    (fun pq => ((rowComparison I rs η).app (K.X pq.2)).f pq.1)
    (fun p p' q _ => ((rowComparison I rs η).app (K.X q)).comm p p')
    (fun p q q' _ =>
      (HomologicalComplex.congr_hom ((rowComparison I rs η).naturality (K.d q q')) p).symm)

private def totalComparison
    (η : idealTorsionFunctor I ⋙ stalk R ⟶ stalk R ⋙ tensorLeft (CechComplex rs)) :
    torsionComplex I ⟶ cechTensorFunctor rs where
  app K := (λ_ ((torsionComplex I).obj K)).inv ≫
    HomologicalComplex₂.total.map (doubleComparison I rs η K) upZ
  naturality K L f := by
    change (torsionComplex I).map f ≫ (λ_ ((torsionComplex I).obj L)).inv ≫
        HomologicalComplex₂.total.map (doubleComparison I rs η L) upZ =
      ((λ_ ((torsionComplex I).obj K)).inv ≫
        HomologicalComplex₂.total.map (doubleComparison I rs η K) upZ) ≫
          (cechTensorFunctor rs).map f
    rw [leftUnitor_inv_naturality_assoc, Category.assoc]
    congr 1
    change (tensorLeft (unit R)).map ((torsionComplex I).map f) ≫
        HomologicalComplex₂.total.map (doubleComparison I rs η L) upZ =
      HomologicalComplex₂.total.map (doubleComparison I rs η K) upZ ≫
        (tensorLeft (CechComplex rs)).map f
    rw [tensorLeft_map_total, tensorLeft_map_total]
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
    congr 1
    apply HomologicalComplex.hom_ext
    intro p
    apply HomologicalComplex.hom_ext
    intro q
    exact HomologicalComplex.congr_hom ((rowComparison I rs η).naturality (f.f q)) p

private theorem totalComparison_quasiIso
    (η : idealTorsionFunctor I ⋙ stalk R ⟶ stalk R ⋙ tensorLeft (CechComplex rs))
    (hη : ∀ Q : Mod R, Injective Q → QuasiIso (η.app Q))
    (K : CpxPlus R) (hK : ∀ n, Injective (K.obj.X n)) :
    QuasiIso ((totalComparison I rs η).app K.obj) := by
  obtain ⟨a, ha⟩ := K.property
  have hsrc : CochainComplex.IsStrictlyGE ((torsionComplex I).obj K.obj) a := by infer_instance
  have hunit (p : ℤ) (hp : p < 0) : IsZero ((unit R).X p) :=
    isZero_single_obj_X upZ 0 (𝟙_ (Mod R)) p (by omega)
  have htotal : QuasiIso (HomologicalComplex₂.total.map (doubleComparison I rs η K.obj) upZ) := by
    apply double_complex_comparison _ _
      (doubleTensor_finite _ _ a hunit)
      (doubleTensor_finite _ _ a (fun p hp => Cech.isZero_X rs p (Or.inl hp)))
    right
    intro q
    have h := hη (K.obj.X q) (hK q)
    change QuasiIso ((rowComparison I rs η).app (K.obj.X q))
    dsimp only [rowComparison, NatTrans.comp_app]
    infer_instance
  let := htotal
  exact quasiIso_comp _ _

end TotalComparison

section Derived

variable [HasDerivedCategory.{w} (Mod R)]

private theorem cechTensorPlus_inverts (rs : List R) :
    (CochainComplex.Plus.quasiIso (Mod R)).IsInvertedBy
      (cechTensorPlus rs ⋙ DerivedCategory.Plus.Q) := by
  intro K L f hf
  have h : QuasiIso f.hom := hf
  have := cechTensor_quasiIso rs f.hom h
  change IsIso (DerivedCategory.Plus.Q.map ((cechTensorPlus rs).map f))
  apply Localization.inverts _ (CochainComplex.Plus.quasiIso (Mod R))
  exact ‹QuasiIso ((cechTensorFunctor rs).map f.hom)›

private def cechDerived (rs : List R) :
    DerivedCategory.Plus (Mod R) ⥤ DerivedCategory.Plus (Mod R) :=
  Localization.lift (cechTensorPlus rs ⋙ DerivedCategory.Plus.Q)
    (cechTensorPlus_inverts rs) DerivedCategory.Plus.Q

private def cechDerivedFac (rs : List R) :
    DerivedCategory.Plus.Q ⋙ cechDerived rs ≅ cechTensorPlus rs ⋙ DerivedCategory.Plus.Q :=
  Localization.fac _ (cechTensorPlus_inverts rs) _

private def cechDerivedUnderlyingFac (rs : List R) :
    ((DerivedCategory.Plus.Q ⋙ cechDerived rs) ⋙ DerivedCategory.Plus.ι) ≅
      (CochainComplex.Plus.ι (Mod R) ⋙ cechTensorFunctor rs) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (cechDerivedFac rs) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.Plus.QCompιIso (Mod R)) ≪≫
    (Functor.associator _ _ _).symm

variable [IsNoetherianRing R] (I : Ideal R) (rs : List R)

private def plusComparison
    (η : idealTorsionFunctor I ⋙ stalk R ⟶ stalk R ⋙ tensorLeft (CechComplex rs)) :
    (idealTorsionFunctor I).mapCochainComplexPlus ⟶ cechTensorPlus rs where
  app K := ObjectProperty.homMk ((totalComparison I rs η).app K.obj)
  naturality K L f := by
    apply ObjectProperty.hom_ext
    exact (totalComparison I rs η).naturality f.hom

private def derivedComparisonOfRows
    (η : idealTorsionFunctor I ⋙ stalk R ⟶ stalk R ⋙ tensorLeft (CechComplex rs))
    (hη : ∀ Q : Mod R, Injective Q → QuasiIso (η.app Q)) :
    (idealTorsionFunctor I).rightDerivedFunctorPlus ≅ cechDerived rs := by
  let F := idealTorsionFunctor I
  let W := CochainComplex.Plus.quasiIso (Mod R)
  let Q : CpxPlus R ⥤ DerivedCategory.Plus (Mod R) := DerivedCategory.Plus.Q
  let β : F.mapCochainComplexPlus ⋙ Q ⟶ Q ⋙ cechDerived rs :=
    Functor.whiskerRight (plusComparison I rs η) Q ≫ (cechDerivedFac rs).inv
  let t := F.rightDerivedFunctorPlus.rightDerivedDesc F.rightDerivedFunctorPlusUnit W _ β
  have hi (L : CochainComplex.Plus (InjectiveObject (Mod R))) :
      IsIso (t.app (Q.obj ((InjectiveObject.ι (Mod R)).mapCochainComplexPlus.obj L))) := by
    let J := (InjectiveObject.ι (Mod R)).mapCochainComplexPlus.obj L
    have hJ (n : ℤ) : Injective (J.obj.X n) := (L.obj.X n).property
    have hz : W ((plusComparison I rs η).app J) :=
      totalComparison_quasiIso I rs η hη J hJ
    have : IsIso (Q.map ((plusComparison I rs η).app J)) := Localization.inverts Q W _ hz
    have hb : IsIso (β.app J) := by
      change IsIso (Q.map ((plusComparison I rs η).app J) ≫ (cechDerivedFac rs).inv.app J)
      infer_instance
    have h := F.rightDerivedFunctorPlus.rightDerived_fac_app
      F.rightDerivedFunctorPlusUnit W (cechDerived rs) β J
    have hu : IsIso (F.rightDerivedFunctorPlusUnit.app J) :=
      inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι (Mod R)).mapCochainComplexPlus.obj L)))
    rw [← h] at hb
    exact IsIso.of_isIso_comp_left (F.rightDerivedFunctorPlusUnit.app J) _
  have ht (K : DerivedCategory.Plus (Mod R)) : IsIso (t.app K) := by
    obtain ⟨a, ha⟩ := K.property
    have : K.IsGE a := (K.isGE_ι_obj_iff a).mp ha
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K a
    exact (NatTrans.isIso_app_iff_of_iso t e).mp (hi L)
  letI : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

end Derived

/-- Bounded-below derived torsion is computed by the localized Čech tensor functor. -/
theorem derivedCechComparison :
    Specs.CommutativeAlgebraNotes.DerivedCechComparison.DerivedComparison.{u,w} := by
  intro R _ _ _ I rs hI
  obtain ⟨η, _, hη⟩ := idealTorsionCechComparison I rs hI
  exact ⟨cechDerived rs, ⟨cechDerivedUnderlyingFac rs⟩,
    ⟨derivedComparisonOfRows I rs η hη⟩⟩

private def stalkPlus (R : Type u) [CommRing R] : Mod R ⥤ CpxPlus R :=
  ObjectProperty.lift _ (stalk R) (fun M => ⟨0, by
    change ((CochainComplex.singleFunctor (Mod R) 0).obj M).IsStrictlyGE 0
    infer_instance⟩)

private def stalkPlusDerivedIso [HasDerivedCategory.{w} (Mod R)] :
    DerivedCategory.Plus.singleFunctor (Mod R) 0 ≅ stalkPlus R ⋙ DerivedCategory.Plus.Q :=
  ((Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι (C := Mod R))).whiskeringRight (Mod R)).preimageIso
    (DerivedCategory.singleFunctorIsoCompQ (Mod R) 0)

open AdvancedHomologicalAlgebra.CechToCohomology (natRightDerivedIso)
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues (rightValue)

private def moduleComparisonNonneg [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) (rs : List R)
    (T : DerivedCategory.Plus (Mod R) ⥤ DerivedCategory.Plus (Mod R))
    (eT : ((DerivedCategory.Plus.Q ⋙ T) ⋙ DerivedCategory.Plus.ι) ≅
      (CochainComplex.Plus.ι (Mod R) ⋙ cechTensorFunctor rs) ⋙ DerivedCategory.Q)
    (e : (idealTorsionFunctor I).rightDerivedFunctorPlus ≅ T) (n : ℕ) :
    (idealTorsionFunctor I).rightDerived n ≅
      (stalk R ⋙ cechTensorFunctor rs) ⋙ homologyFunctor (Mod R) upZ (n : ℤ) := by
  let H := DerivedCategory.homologyFunctor (Mod R) (n : ℤ)
  calc
    _ ≅ rightValue (idealTorsionFunctor I) n := (natRightDerivedIso _ n).symm
    _ ≅ (DerivedCategory.Plus.singleFunctor (Mod R) 0 ⋙
          (idealTorsionFunctor I).rightDerivedFunctorPlus) ⋙ DerivedCategory.Plus.ι ⋙ H :=
      (Functor.associator _ _ _).symm
    _ ≅ (DerivedCategory.Plus.singleFunctor (Mod R) 0 ⋙ T) ⋙ DerivedCategory.Plus.ι ⋙ H :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ e) _
    _ ≅ (((stalkPlus R ⋙ DerivedCategory.Plus.Q) ⋙ T) ⋙ DerivedCategory.Plus.ι) ⋙ H :=
      (Functor.associator (DerivedCategory.Plus.singleFunctor (Mod R) 0 ⋙ T)
        DerivedCategory.Plus.ι H).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight stalkPlusDerivedIso T) DerivedCategory.Plus.ι) H
    _ ≅ (stalkPlus R ⋙ ((DerivedCategory.Plus.Q ⋙ T) ⋙ DerivedCategory.Plus.ι)) ⋙ H :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
          Functor.associator _ _ _) _
    _ ≅ ((stalk R ⋙ cechTensorFunctor rs) ⋙ DerivedCategory.Q) ⋙ H :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ eT ≪≫
        (Functor.associator _ _ _).symm) _
    _ ≅ _ := Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors (Mod R) (n : ℤ))

/-- Local cohomology in every integer degree is naturally the cohomology of
the Čech complex with module coefficients. -/
theorem localCohomologyCechComparison :
    Specs.CommutativeAlgebraNotes.DerivedCechComparison.ModuleComparison.{u} := by
  intro R _ _ I rs hI q
  cases q with
  | ofNat n =>
    let := HasDerivedCategory.standard (Mod R)
    obtain ⟨T, ⟨eT⟩, ⟨e⟩⟩ := derivedCechComparison I rs hI
    exact ⟨moduleComparisonNonneg I rs T eT e n⟩
  | negSucc n =>
    change Nonempty ((0 : Mod R ⥤ Mod R) ≅ _)
    refine ⟨(isZero_zero (Mod R ⥤ Mod R)).iso (Functor.isZero _ ?_)⟩
    intro M
    have hM : CochainComplex.IsStrictlyGE ((stalk R).obj M) 0 := by
      change ((CochainComplex.singleFunctor (Mod R) 0).obj M).IsStrictlyGE 0
      infer_instance
    have h := cechTensor_isStrictlyGE rs ((stalk R).obj M) 0
    exact CochainComplex.isZero_of_isGE ((cechTensorFunctor rs).obj ((stalk R).obj M))
      0 (Int.negSucc n) (Int.negSucc_lt_zero n)

end

end CommutativeAlgebraNotes
