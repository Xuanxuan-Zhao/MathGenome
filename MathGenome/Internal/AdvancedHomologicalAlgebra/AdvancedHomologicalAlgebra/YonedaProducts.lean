import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.YonedaProducts
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.HigherYonedaClasses
import Mathlib.Data.Nat.Choose.Basic

/-! HA-R15: geometric splicing and its cochain sign normalization. -/
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses
open Specs.AdvancedHomologicalAlgebra.YonedaProducts

namespace AdvancedHomologicalAlgebra.YonedaProducts
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The comparison sign in degree i is +1 at the junction i = -n. -/
def translationSign (n i : ℤ) : ℤˣ := (n * (i+n)).negOnePow

lemma translationSign_next (n i j : ℤ) (h : i+1=j) :
    translationSign n j = translationSign n i * n.negOnePow := by
  dsimp [translationSign]
  rw [← Int.negOnePow_add]
  congr 1
  rw [← h]
  ring

/-- The unsigned row translation and the signed cochain shift are isomorphic.
The component at the common endpoint has sign +1. -/
noncomputable def translateIsoShift (K : CochainComplex 𝒜 ℤ) (n : ℤ) :
    (translate n).obj K ≅ K⟦n⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i =>
      { hom := translationSign n i • 𝟙 _
        inv := translationSign n i • 𝟙 _
        hom_inv_id := by simp [← mul_smul, Int.units_mul_self]
        inv_hom_id := by simp [← mul_smul, Int.units_mul_self] })
    (by
      intro i j hij
      change (translationSign n i • 𝟙 _) ≫ (n.negOnePow • K.d (i+n) (j+n)) =
        K.d (i+n) (j+n) ≫ (translationSign n j • 𝟙 _)
      change i+1=j at hij
      rw [translationSign_next n i j hij]
      simp [translate, smul_smul, mul_comm])

@[reassoc]
lemma translateIsoShift_naturality {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) (n : ℤ) :
    (translate n).map f ≫ (translateIsoShift L n).hom =
      (translateIsoShift K n).hom ≫ f⟦n⟧' := by
  ext i
  simp [translate, translateIsoShift]

/-- Pullback along an epimorphic quasi-isomorphism preserves quasi-isomorphisms.
This is the abelian-complex statement, with no resolution assumptions. -/
lemma quasiIso_pullback_fst {K L M : CochainComplex 𝒜 ℤ}
    (f : K ⟶ M) (g : L ⟶ M) [Epi g] [QuasiIso g] :
    QuasiIso (pullback.fst f g) := by
  let S := ShortComplex.kernelSequence g
  have : Epi S.g := ‹Epi g›
  have : QuasiIso S.g := ‹QuasiIso g›
  have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact _ }
  exact HigherYonedaClasses.EndpointPush.quasiIso_of_shortExact_of_acyclic_left
    (hS.pull f) (HigherYonedaClasses.EndpointPull.acyclic_left_of_shortExact_of_quasiIso (S := S) hS)

/-- The complete previously established classification with its sign convention. -/
theorem classification : Specs.AdvancedHomologicalAlgebra.YonedaProducts.classificationType := by
  exact ⟨HigherYonedaClasses.degree_zero_classification,
    HigherYonedaClasses.degree_zero_naturality,
    HigherYonedaClasses.natural_additive_classification,
    HigherYonedaClasses.degree_one_boundary⟩

lemma zeroHom_eq_mk₀ [HasDerivedCategory.{w} 𝒜] {X Y : 𝒜} (f : X ⟶ Y) :
    Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom f =
      ShiftedHom.mk₀ (0 : ℤ) rfl ((_root_.DerivedCategory.singleFunctor 𝒜 0).map f) := by
  simp [Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom,
    ShiftedHom.mk₀, shiftFunctorZero']

/-- Postcomposition by a degree-zero class agrees with every geometric pushout. -/
theorem pushout_product [HasDerivedCategory.{w} 𝒜] {X Y Z : 𝒜} {n : ℕ}
    (f : Y ⟶ Z) (B : Extension X Y n) (O : B.PushoutData f) :
    O.row.yonedaClass = ShiftedHom.comp B.yonedaClass
      (Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom f) (zero_add _) := by
  rw [zeroHom_eq_mk₀, ShiftedHom.comp_mk₀]
  simpa using
    (HigherYonedaClasses.map_naturality 𝒜 X Y X Z n B O.row (𝟙 X) f O.comparison).symm

/-- Precomposition by a degree-zero class agrees with every geometric pullback. -/
theorem pullback_product [HasDerivedCategory.{w} 𝒜] {X Y Z : 𝒜} {m : ℕ}
    (A : Extension Y Z m) (f : X ⟶ Y) (P : A.PullbackData f) :
    P.row.yonedaClass = ShiftedHom.comp
      (Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom f) A.yonedaClass (add_zero _) := by
  rw [zeroHom_eq_mk₀, ShiftedHom.mk₀_comp]
  simpa using HigherYonedaClasses.map_naturality 𝒜 X Z Y Z m P.row A f (𝟙 Z) P.comparison

theorem left_zero : leftZeroType := by
  intro 𝒜 _ _ _ X Y Z n f B
  let O := HigherYonedaClasses.pushoutData B f
  exact ⟨O, pushout_product f B O⟩

theorem right_zero : rightZeroType := by
  intro 𝒜 _ _ _ X Y Z m A f
  let P := HigherYonedaClasses.pullbackData A f
  exact ⟨P, pullback_product A f P⟩

theorem zero_zero : zeroZeroType := by
  intro 𝒜 _ _ _ X Y Z f g
  simp only [product, zeroHom_eq_mk₀]
  rw [ShiftedHom.mk₀_comp_mk₀ _ _ _ rfl rfl, ← Functor.map_comp]
  rfl

lemma triangle_add (n m : ℕ) :
    (n+m)*(n+m-1)/2 = n*(n-1)/2 + m*(m-1)/2 + n*m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, Nat.triangle_succ, Nat.triangle_succ, ih]
    ring

lemma normalization_add (n m : ℕ) :
    Extension.normalization (n+m) = Extension.normalization n *
      Extension.normalization m * (((n*m : ℕ) : ℤ).negOnePow) := by
  unfold Extension.normalization
  rw [triangle_add]
  simp only [Nat.cast_add, Int.negOnePow_add]

lemma quasiIso_translate_map {K L : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) [QuasiIso f] (n : ℤ) : QuasiIso ((translate n).map f) := by
  have h : QuasiIso ((translate n).map f ≫ (translateIsoShift L n).hom) := by
    rw [translateIsoShift_naturality]
    infer_instance
  exact quasiIso_of_comp_right _ (translateIsoShift L n).hom

lemma epi_translate_map {K L : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) [Epi f] (n : ℤ) : Epi ((translate n).map f) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  change Epi (f.f (i+n))
  infer_instance

variable {X Y Z : 𝒜} {m n : ℕ}

lemma translatedAugmentation_quasiIso (A : Extension Y Z m) (n : ℕ) :
    QuasiIso (translatedAugmentation A n) := by
  have := quasiIso_translate_map A.augmentation (n : ℤ)
  dsimp [translatedAugmentation]
  infer_instance

lemma translatedAugmentation_epi (A : Extension Y Z m) (n : ℕ) :
    Epi (translatedAugmentation A n) := by
  have := HigherYonedaClasses.EndpointPull.augmentation_epi A
  have := epi_translate_map A.augmentation (n : ℤ)
  dsimp [translatedAugmentation]
  infer_instance

noncomputable def spliceComplex (A : Extension Y Z m) (B : Extension X Y n) :
    CochainComplex 𝒜 ℤ := pullback B.projection (translatedAugmentation A n)

noncomputable def spliceA (A : Extension Y Z m) (B : Extension X Y n) :
    spliceComplex A B ⟶ B.complex := pullback.fst _ _

noncomputable def spliceB (A : Extension Y Z m) (B : Extension X Y n) :
    spliceComplex A B ⟶ (translate (n : ℤ)).obj A.complex := pullback.snd _ _

lemma splice_isPullback (A : Extension Y Z m) (B : Extension X Y n) :
    IsPullback (spliceA A B) (spliceB A B) B.projection (translatedAugmentation A n) :=
  IsPullback.of_hasPullback _ _

lemma splice_isPullback_at (A : Extension Y Z m) (B : Extension X Y n) (i : ℤ) :
    IsPullback ((spliceA A B).f i) ((spliceB A B).f i)
      (B.projection.f i) ((translatedAugmentation A n).f i) :=
  (splice_isPullback A B).map (HomologicalComplex.eval 𝒜 (.up ℤ) i)

lemma spliceB_isIso (A : Extension Y Z m) (B : Extension X Y n)
    (i : ℤ) (hi : i < -(n : ℤ)) : IsIso ((spliceB A B).f i) := by
  have : IsIso (B.projection.f i) :=
    (B.complex.isZero_of_isStrictlyGE _ i hi).isIso
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-(n : ℤ)) Y i (by omega)) _
  exact (splice_isPullback_at A B i).isIso_snd_of_isIso

lemma spliceA_isIso (A : Extension Y Z m) (B : Extension X Y n)
    (i : ℤ) (hi : 0 < i) : IsIso ((spliceA A B).f i) := by
  have hz : IsZero (((translate (n : ℤ)).obj A.complex).X i) :=
    A.complex.isZero_of_isStrictlyLE 0 (i+(n : ℤ)) (by omega)
  have : IsIso ((translatedAugmentation A n).f i) := hz.isIso
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-(n : ℤ)) Y i (by omega)) _
  exact (splice_isPullback_at A B i).isIso_fst_of_isIso

/-- The literal unsigned splice, with its left copy of Z fixed positively. -/
noncomputable def splice (A : Extension Y Z m) (B : Extension X Y n) :
    Extension X Z (n+m) where
  positive := by have := A.positive; omega
  complex := spliceComplex A B
  supportedGE := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hm := A.positive
    have := spliceB_isIso A B i (by omega)
    exact (A.complex.isZero_of_isStrictlyGE (-(m : ℤ)) (i+(n : ℤ))
      (by omega)).of_iso (asIso ((spliceB A B).f i))
  supportedLE := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have := spliceA_isIso A B i hi
    exact (B.complex.isZero_of_isStrictlyLE 0 i hi).of_iso (asIso ((spliceA A B).f i))
  left := by
    have hm := A.positive
    have := spliceB_isIso A B (-((n+m : ℕ) : ℤ)) (by omega)
    exact asIso ((spliceB A B).f _) ≪≫ A.complex.XIsoOfEq (by omega) ≪≫ A.left
  augmentation := spliceA A B ≫ B.augmentation
  exact := by
    have := translatedAugmentation_epi A n
    have := translatedAugmentation_quasiIso A n
    have := quasiIso_pullback_fst B.projection (translatedAugmentation A n)
    exact inferInstanceAs (QuasiIso (pullback.fst B.projection (translatedAugmentation A n) ≫ B.augmentation))

noncomputable def spliceData (A : Extension Y Z m) (B : Extension X Y n) :
    SpliceData A B where
  row := splice A B
  a := spliceA A B
  b := spliceB A B
  square := splice_isPullback A B
  augmentation := rfl
  left := rfl

theorem splice_exists : spliceExistsType := by
  intro 𝒜 _ _ X Y Z m n A B
  exact ⟨spliceData A B⟩

/-- Compatibility with the augmentation at the unsigned junction. -/
lemma translatedAugmentation_eq (A : Extension Y Z m) (n : ℕ) :
    translatedAugmentation A n = (translateIsoShift A.complex (n : ℤ)).hom ≫
      A.augmentation⟦(n : ℤ)⟧' ≫
      ((CochainComplex.singleFunctors 𝒜).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).hom.app Y := by
  apply HomologicalComplex.to_single_hom_ext
  simp [translatedAugmentation, translateSingleIso, translate, translateIsoShift,
    translationSign, CochainComplex.singleFunctors, HomologicalComplex.single,
    HomologicalComplex.Hom.isoOfComponents, HomologicalComplex.comp_f]

/-- The map from the spliced row into the signed shift of the left row. -/
noncomputable def signedSpliceMap (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) : S.row.complex ⟶ A.complex⟦(n : ℤ)⟧ :=
  S.b ≫ (translateIsoShift A.complex (n : ℤ)).hom

lemma signedSpliceMap_augmentation (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) :
    signedSpliceMap A B S ≫ A.augmentation⟦(n : ℤ)⟧' =
      S.a ≫ B.projection ≫
      ((CochainComplex.singleFunctors 𝒜).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app Y := by
  apply (cancel_mono (((CochainComplex.singleFunctors 𝒜).shiftIso
    (n : ℤ) (-(n : ℤ)) 0 (by omega)).hom.app Y)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, comp_id]
  dsimp only [signedSpliceMap]
  simp only [Category.assoc]
  rw [← translatedAugmentation_eq]
  exact S.square.w.symm

/-- The only extra factor at the left endpoint is (-1)^(nm). -/
lemma signedSpliceMap_projection (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) :
    signedSpliceMap A B S ≫ A.projection⟦(n : ℤ)⟧' ≫
      ((CochainComplex.singleFunctors 𝒜).shiftIso (n : ℤ)
        (-((n+m : ℕ) : ℤ)) (-(m : ℤ)) (by omega)).hom.app Z =
      (((n*m : ℕ) : ℤ).negOnePow) • S.row.projection := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, signedSpliceMap,
    CochainComplex.shiftFunctor_map_f', Extension.projection]
  have hleft := congrArg
    (fun f => ((((n*m : ℕ) : ℤ).negOnePow) • f) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-((n+m : ℕ) : ℤ)) Z).inv) S.left
  convert hleft using 1 <;>
    simp [translateIsoShift, translationSign,
      HomologicalComplex.single, HomologicalComplex.Hom.isoOfComponents,
      HomologicalComplex.mkHomToSingle, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.XIsoOfEq,
      Category.assoc, Units.smul_def]


section Derived
variable [HasDerivedCategory.{w} 𝒜]

noncomputable def derivedSpliceMap (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) : _root_.DerivedCategory.Q.obj S.row.complex ⟶
      (_root_.DerivedCategory.Q.obj A.complex)⟦(n : ℤ)⟧ :=
  _root_.DerivedCategory.Q.map (signedSpliceMap A B S) ≫
    (_root_.DerivedCategory.Q.commShiftIso (n : ℤ)).hom.app A.complex

lemma derivedSpliceMap_augmentation (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) :
    derivedSpliceMap A B S ≫ (_root_.DerivedCategory.Q.map A.augmentation)⟦(n : ℤ)⟧' =
      _root_.DerivedCategory.Q.map S.a ≫ _root_.DerivedCategory.Q.map B.projection ≫
      ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso
        (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app Y := by
  dsimp only [derivedSpliceMap]
  simp only [Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality]
  rw [← Functor.map_comp_assoc, signedSpliceMap_augmentation]
  simp [_root_.DerivedCategory.singleFunctors, SingleFunctors.postcomp_shiftIso_inv_app,
    Functor.map_comp, Category.assoc]

lemma derivedSpliceMap_projection (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) :
    derivedSpliceMap A B S ≫ (_root_.DerivedCategory.Q.map A.projection)⟦(n : ℤ)⟧' ≫
      ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso (n : ℤ)
        (-((n+m : ℕ) : ℤ)) (-(m : ℤ)) (by omega)).hom.app Z =
      (((n*m : ℕ) : ℤ).negOnePow) • _root_.DerivedCategory.Q.map S.row.projection := by
  dsimp only [derivedSpliceMap]
  simp only [Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality_assoc]
  simp only [_root_.DerivedCategory.singleFunctors, SingleFunctors.postcomp_shiftIso_hom_app,
    Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, signedSpliceMap_projection]
  simp [Units.smul_def]

/-- Unscaled roofs compose with the cochain crossing sign (-1)^(nm). -/
lemma roof_product (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) :
    product A.roof B.roof = (((n*m : ℕ) : ℤ).negOnePow) • S.row.roof := by
  have hs := derivedSpliceMap_augmentation A B S
  have hp := derivedSpliceMap_projection A B S
  have hp' : derivedSpliceMap A B S ≫
      (_root_.DerivedCategory.Q.map A.projection)⟦(n : ℤ)⟧' =
      ((((n*m : ℕ) : ℤ).negOnePow) • _root_.DerivedCategory.Q.map S.row.projection) ≫
      ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso (n : ℤ)
        (-((n+m : ℕ) : ℤ)) (-(m : ℤ)) (by omega)).inv.app Z := by
    rw [← hp]
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj]
    exact congrArg (fun f => derivedSpliceMap A B S ≫ f)
      (Category.comp_id ((_root_.DerivedCategory.Q.map A.projection)⟦(n : ℤ)⟧')).symm
  apply (cancel_epi (_root_.DerivedCategory.Q.map S.row.augmentation)).mp
  rw [← S.augmentation, Functor.map_comp]
  simp only [product, ShiftedHom.comp, Extension.roof, Functor.map_comp, Category.assoc,
    IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% hs]
  simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hp']
  have hshift := (_root_.DerivedCategory.singleFunctors 𝒜).shiftIso_add'_inv_app
    (n : ℤ) (m : ℤ) ((n+m : ℕ) : ℤ) (by omega)
    (-((n+m : ℕ) : ℤ)) (-(m : ℤ)) 0 (by omega) (by omega) Z
  rw [← hshift]
  have haug := congrArg (fun f => _root_.DerivedCategory.Q.map f) S.augmentation
  simp only [Functor.map_comp] at haug
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  rw [reassoc_of% haug]
  simp

lemma product_units_smul
    (α : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext Y Z (m : ℤ))
    (β : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (n : ℤ)) (r s : ℤˣ) :
    product (r • α) (s • β) = (s*r) • product α β := by
  simp [product, ShiftedHom.comp, Units.smul_def, smul_smul, mul_comm]

/-- Normalization cancels precisely the crossing sign of the unscaled roofs. -/
lemma yonedaClass_product (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) : S.row.yonedaClass = product A.yonedaClass B.yonedaClass := by
  simp only [Extension.yonedaClass, product_units_smul, roof_product A B S, smul_smul]
  rw [normalization_add]

end Derived

theorem positive_product : positiveProductType := by
  intro 𝒜 _ _ _ X Y Z m n A B S
  exact yonedaClass_product A B S

/-- All terms on the right and left are the actual terms of B and A,
respectively, via the two projections of the geometric pullback. -/
theorem splice_terms : spliceTermsType := by
  intro 𝒜 _ _ X Y Z m n A B S i
  have sq : IsPullback (S.a.f i) (S.b.f i) (B.projection.f i)
      ((translatedAugmentation A n).f i) :=
    S.square.map (HomologicalComplex.eval 𝒜 (.up ℤ) i)
  constructor
  · intro hi
    have hz : IsZero (((translate (n : ℤ)).obj A.complex).X i) :=
      A.complex.isZero_of_isStrictlyLE 0 (i+(n : ℤ)) (by omega)
    have : IsIso ((translatedAugmentation A n).f i) := hz.isIso
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-(n : ℤ)) Y i (by omega)) _
    exact sq.isIso_fst_of_isIso
  · intro hi
    have : IsIso (B.projection.f i) := by
      by_cases he : i = -(n : ℤ)
      · subst i
        simp only [Extension.projection, HomologicalComplex.mkHomToSingle_f]
        infer_instance
      · exact (B.complex.isZero_of_isStrictlyGE (-(n : ℤ)) i (by omega)).isIso
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-(n : ℤ)) Y i he) _
    exact sq.isIso_snd_of_isIso

@[reassoc]
private lemma translatedAugmentation_at_junction (A : Extension Y Z m) (n : ℕ) :
    (translatedAugmentation A n).f (-(n : ℤ)) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-(n : ℤ)) Y).hom =
    (A.complex.XIsoOfEq (show -(n : ℤ) + (n : ℤ) = 0 by omega)).hom ≫
      A.augmentation.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom := by
  rw [← HomologicalComplex.XIsoOfEq_hom_naturality_assoc]
  simp only [translatedAugmentation, HomologicalComplex.comp_f, Category.assoc]
  change A.augmentation.f (-(n : ℤ) + (n : ℤ)) ≫ _ = _
  congr 1
  simp [translateSingleIso, translate, HomologicalComplex.single,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.Hom.isoOfComponents, HomologicalComplex.XIsoOfEq]
  erw [comp_id]

/-- In the splice coordinates, the differential at the junction is the
augmentation of the left row followed by the first arrow of the right row. -/
theorem splice_junction (A : Extension Y Z m) (B : Extension X Y n) (S : SpliceData A B) :
    S.row.complex.d (-(n : ℤ)) (-(n : ℤ) + 1) ≫ S.a.f (-(n : ℤ) + 1) =
      S.b.f (-(n : ℤ)) ≫
        (A.complex.XIsoOfEq (show -(n : ℤ) + (n : ℤ) = 0 by omega)).hom ≫
        A.augmentation.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom ≫
        B.left.inv ≫ B.complex.d (-(n : ℤ)) (-(n : ℤ) + 1) := by
  have h := congrArg (fun f => HomologicalComplex.Hom.f f (-(n : ℤ))) S.square.w
  simp only [HomologicalComplex.comp_f, Extension.projection,
    HomologicalComplex.mkHomToSingle_f] at h
  rw [← S.a.comm]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    translatedAugmentation_at_junction_assoc] using
    congrArg (fun f => f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) (-(n : ℤ)) Y).hom ≫
      B.left.inv ≫ B.complex.d (-(n : ℤ)) (-(n : ℤ) + 1)) h

lemma classification_positive [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜) (k : ℕ) (hk : 0 < k) :
    ∃ e : Quotient (Extension.extensionSetoid X Y k) ≃
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (k : ℤ),
      ∀ E : Extension X Y k, e ⟦E⟧ = E.yonedaClass := by
  cases k with
  | zero => omega
  | succ k => exact HigherYonedaClasses.classification 𝒜 X Y k

/-- The induced operation on equivalence classes is geometric splicing. -/
theorem class_product : classProductType := by
  intro 𝒜 _ _ _ X Y Z m n
  obtain ⟨eA, hA⟩ := classification_positive Y Z (m+1) (by omega)
  obtain ⟨eB, hB⟩ := classification_positive X Y (n+1) (by omega)
  obtain ⟨eC, hC⟩ := classification_positive X Z ((n+1)+(m+1)) (by omega)
  let op := fun a b => eC.symm (product (eA a) (eB b))
  refine ⟨eA, eB, eC, op, hA, hB, hC, ?_, ?_⟩
  · intro A B S
    apply eC.injective
    change eC (eC.symm _) = eC ⟦S.row⟧
    rw [Equiv.apply_symm_apply, hA, hB, hC, yonedaClass_product A B S]
  · intro a b
    exact eC.apply_symm_apply _

end AdvancedHomologicalAlgebra.YonedaProducts
