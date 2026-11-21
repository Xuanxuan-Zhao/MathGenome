import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergTotalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CartanEilenbergComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped Classical
universe v u v' u' w w'
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AdvancedHomologicalAlgebra.CartanEilenbergTotalization
open CartanEilenbergData DoubleTotalization FiniteDiagonalFiltrations
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma resolution_finite {K : CochainComplex C ℤ} (R : ResolutionData K) :
    FiniteDiagonals R.bicomplex := by
  obtain ⟨L, hL⟩ := R.boundedBelow
  apply quadrantFinite R.bicomplex L 0
  intro p q h
  by_cases hp : p < L
  · exact hL p q hp
  · exact R.nonnegative p q (by omega)

theorem finiteSupport : Specs.FiniteSupport.{v,u} := by
  intro C _ _ K R
  exact ⟨resolution_finite R, (totalizationsExist _ (resolution_finite R)).1⟩

lemma resolution_homology_zero {A : C} {J : CochainComplex C ℤ} {ι : A ⟶ J.X 0}
    (hJ : IsInjectiveResolution A J ι) (q : ℤ) (hq : q ≠ 0) :
    IsZero (J.homology q) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  by_cases hpos : 0 < q
  · exact hJ.exact_pos q hpos
  · exact ShortComplex.exact_of_isZero_X₂ _ (hJ.zero_neg q (by omega))

lemma resolution_homology_zero_iso {A : C} {J : CochainComplex C ℤ} {ι : A ⟶ J.X 0}
    (hJ : IsInjectiveResolution A J ι)
    (z : ∀ q, (ComplexShape.up ℤ).Rel 0 q → ι ≫ J.d 0 q = 0) :
    IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex.mkHomFromSingle (K := J) (j := 0) ι z) 0) := by
  let f := HomologicalComplex.mkHomFromSingle (K := J) (j := 0) ι z
  apply (quasiIsoAt_iff_isIso_homologyMap f 0).1
  rw [quasiIsoAt_iff' f (-1) 0 1 (by simp) (by simp)]
  rw [ShortComplex.quasiIso_iff_of_zeros _
    (HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 A (-1) 0)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 A 0 1)
    ((hJ.zero_neg (-1) (by omega)).eq_of_src _ _)]
  have hm : Mono ι := hJ.mono
  constructor
  · exact ShortComplex.exact_of_iso
      (S₁ := ShortComplex.mk ι (J.d 0 1) hJ.augmentation_d)
      (ShortComplex.isoMk
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).symm
        (Iso.refl _) (Iso.refl _)
        (by simp [f, HomologicalComplex.mkHomFromSingle_f]) (by simp)) hJ.exact_zero
  · change Mono (f.f 0)
    rw [HomologicalComplex.mkHomFromSingle_f]
    change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ ι)
    infer_instance

theorem augmentation : Specs.Augmentation.{v,u} := by
  intro C _ _ K R _
  let z : ∀ p q, (ComplexShape.up ℤ).Rel 0 q →
      R.augmentation.f p ≫ (R.bicomplex.X p).d 0 q = 0 := by
    intro p q hq
    have : q = 1 := by simpa using hq.symm
    subst q
    exact R.augmentation_d p
  exact AugmentedDoubleComplexComparison.cochain_column_assembly R.bicomplex
    (resolution_finite R) R.nonnegative K R.augmentation z
    (fun p => resolution_homology_zero_iso (R.terms p) (z p))
    (fun p q hq => resolution_homology_zero (R.terms p) q hq)

theorem boundedInjective : Specs.BoundedInjective.{v,u} := by
  intro C _ _ K R _
  constructor
  · obtain ⟨L,hL⟩ := R.boundedBelow
    refine ⟨L, fun n hn => ?_⟩
    apply (IsZero.iff_id_eq_zero _).2
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    have hz : IsZero ((R.bicomplex.X p).X q) := by
      by_cases hp : p < L
      · exact hL p q hp
      · exact R.nonnegative p q (by change p+q=n at h; omega)
    exact hz.eq_of_src _ _
  · intro n
    let : ∀ n, HasBiproduct (diagonalFamily R.bicomplex n) :=
      diagonalBiproducts _ (resolution_finite R)
    let : ∀ i : Diagonal n, Injective (diagonalFamily R.bicomplex n i) := by
      intro i
      by_cases hq : 0 ≤ i.val.2
      · exact (R.terms i.val.1).injective i.val.2 hq
      · exact (R.nonnegative i.val.1 i.val.2 (by omega)).injective
    exact Injective.of_iso (sumBiproductIso R.bicomplex n).symm inferInstance

theorem augmentationComparison : Specs.AugmentationComparison.{v,u} := by
  intro C _ _ K L R S _ _ f a ha r s hr hs
  ext n
  simp only [HomologicalComplex.comp_f, hr, hs, Category.assoc]
  exact CartanEilenbergComparison.totalAugmentationCompatibility R S f a ha n

section FiniteBicones
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {J : Type*} {f : J → C}

/-- A finite sum of the orthogonal projections resolves the identity even
when the ambient indexing type is infinite and the other objects vanish. -/
lemma finite_bicone_total (b : Bicone f) (hb : b.IsBilimit) (s : Finset J)
    (hz : ∀ j, j ∉ s → IsZero (f j)) :
    ∑ j ∈ s, b.π j ≫ b.ι j = 𝟙 b.pt := by
  apply hb.isColimit.hom_ext
  rintro ⟨j⟩
  change b.ι j ≫ (∑ k ∈ s, b.π k ≫ b.ι k) = b.ι j ≫ 𝟙 _
  by_cases hj : j ∈ s
  · simp [Preadditive.comp_sum, ← Category.assoc, b.ι_π, CategoryTheory.dite_comp, hj]
  · exact (hz j hj).eq_of_src _ _

/-- Only a finite set of nonzero legs is used by either universal property. -/
def finiteBiconeIsBilimit (b : Bicone f) (s : Finset J)
    (hz : ∀ j, j ∉ s → IsZero (f j))
    (ht : ∑ j ∈ s, b.π j ≫ b.ι j = 𝟙 b.pt) : b.IsBilimit where
  isLimit := Fan.IsLimit.mk _
    (fun c => ∑ j ∈ s, c.proj j ≫ b.ι j)
    (by
      intro c j
      by_cases hj : j ∈ s
      · simp [Preadditive.sum_comp, Category.assoc, b.ι_π, CategoryTheory.comp_dite, hj]
      · exact (hz j hj).eq_of_tgt _ _)
    (by
      intro c m hm
      rw [← Category.comp_id m]
      change m ≫ 𝟙 b.pt = _
      rw [← ht, Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Category.assoc]
      exact congrArg (fun t => t ≫ b.ι j) (hm j))
  isColimit := Cofan.IsColimit.mk _
    (fun c => ∑ j ∈ s, b.π j ≫ c.inj j)
    (by
      intro c j
      by_cases hj : j ∈ s
      · simp [Preadditive.comp_sum, ← Category.assoc, b.ι_π, CategoryTheory.dite_comp, hj]
      · exact (hz j hj).eq_of_src _ _)
    (by
      intro c m hm
      rw [← Category.id_comp m]
      change 𝟙 b.pt ≫ m = _
      rw [← ht, Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Category.assoc]
      exact congrArg (fun t => b.π j ≫ t) (hm j))

/-- Additivity suffices for a diagonal with finite nonzero support. -/
def mapFiniteBicone (U : C ⥤ D) [U.Additive]
    (hf : {j | ¬ IsZero (f j)}.Finite) (b : Bicone f) (hb : b.IsBilimit) :
    (U.mapBicone b).IsBilimit := by
  let s := hf.toFinset
  have hz : ∀ j, j ∉ s → IsZero (f j) := by
    intro j hj
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hj
  apply finiteBiconeIsBilimit _ s (fun j hj => U.map_isZero (hz j hj))
  change ∑ j ∈ s, U.map (b.π j) ≫ U.map (b.ι j) = 𝟙 (U.obj b.pt)
  simp only [← U.map_comp, ← U.map_sum, finite_bicone_total b hb s hz, U.map_id]

end FiniteBicones

section AdditiveFunctor
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (U : C ⥤ D) [U.Additive]

lemma map_finite (I : DoubleComplex C) (hI : FiniteDiagonals I) :
    FiniteDiagonals ((mapDouble U).obj I) := by
  intro n
  apply (hI n).subset
  intro i hi hz
  exact hi (U.map_isZero hz)

theorem additiveSupport : Specs.AdditiveSupport.{v,u,v',u'} := by
  intro C _ _ D _ _ U _ K R
  have h := map_finite U R.bicomplex (resolution_finite R)
  exact ⟨h, (totalizationsExist _ h).1⟩

variable (I : DoubleComplex C) [I.HasTotal (ComplexShape.up ℤ)]
  [((mapDouble U).obj I).HasTotal (ComplexShape.up ℤ)]

/-- The inverse comparison is induced by the images of the diagonal injections.
Its construction requires no preservation of arbitrary coproducts. -/
def additiveTotalInverse : sumTotal ((mapDouble U).obj I) ⟶
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj (sumTotal I) where
  f n := ((mapDouble U).obj I).totalDesc (fun p q h => U.map (sumInjection I p q n h))
  comm' n m h := by
    have hm : m = n + 1 := by simpa using h.symm
    subst m
    apply HomologicalComplex₂.total.hom_ext
    intro p q e
    change p + q = n at e
    change _ ≫ _ ≫ U.map ((sumTotal I).d n (n+1)) = _
    rw [HomologicalComplex₂.ι_totalDesc_assoc, ← U.map_comp]
    rw [DoubleTotalization.sumDifferential I p (p+1) q (q+1) n (n+1)
      rfl rfl e (by omega) (by omega)]
    rw [← Category.assoc, DoubleTotalization.sumDifferential ((mapDouble U).obj I)
      p (p+1) q (q+1) n (n+1) rfl rfl e (by omega) (by omega)]
    simp only [U.map_add, U.map_units_smul, U.map_comp,
      Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex₂.ι_totalDesc]
    rfl

@[reassoc (attr := simp)]
lemma injection_additiveTotalInverse (p q n : ℤ) (h : p+q=n) :
    sumInjection ((mapDouble U).obj I) p q n h ≫ (additiveTotalInverse U I).f n =
      U.map (sumInjection I p q n h) := by
  dsimp only [additiveTotalInverse]
  exact HomologicalComplex₂.ι_totalDesc _ _ _ _ _

variable [hI : Fact (FiniteDiagonals I)]
local instance sourceBiproducts : ∀ n, HasBiproduct (diagonalFamily I n) :=
  diagonalBiproducts I hI.out
local instance targetBiproducts : ∀ n,
    HasBiproduct (diagonalFamily ((mapDouble U).obj I) n) :=
  diagonalBiproducts _ (map_finite U I hI.out)
local instance preservesDiagonal (n : ℤ) : PreservesBiproduct (diagonalFamily I n) U where
  preserves {b} hb := ⟨mapFiniteBicone U (hI.out n) b hb⟩

/-- The ordinary finite biproduct comparison in each total degree. -/
def additiveTotalIsoX (n : ℤ) : U.obj ((sumTotal I).X n) ≅
    (sumTotal ((mapDouble U).obj I)).X n :=
  U.mapIso (sumBiproductIso I n) ≪≫ U.mapBiproduct (diagonalFamily I n) ≪≫
    (sumBiproductIso ((mapDouble U).obj I) n).symm

lemma map_biproduct_injection {J : Type*} (f : J → C) [HasBiproduct f]
    [PreservesBiproduct f U] (i : J) :
    U.map (biproduct.ι f i) ≫ (U.mapBiproduct f).hom = biproduct.ι (U.obj ∘ f) i := by
  apply (cancel_mono (U.mapBiproduct f).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Functor.mapBiproduct_inv, biproduct.ι_desc]

@[reassoc]
lemma injection_additiveTotalIsoX (n : ℤ) (i : Diagonal n) :
    U.map (sumInjection I i.val.1 i.val.2 n i.property) ≫
      (additiveTotalIsoX U I n).hom =
        sumInjection ((mapDouble U).obj I) i.val.1 i.val.2 n i.property := by
  apply (cancel_mono (sumBiproductIso ((mapDouble U).obj I) n).hom).1
  dsimp only [additiveTotalIsoX, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← U.map_comp_assoc, injection_sumBiproductIso]
  rw [map_biproduct_injection, injection_sumBiproductIso]
  rfl

instance additiveTotalInverse_isIso : IsIso (additiveTotalInverse U I) := by
  have hc : ∀ n, IsIso ((additiveTotalInverse U I).f n) := by
    intro n
    have he : (additiveTotalInverse U I).f n = (additiveTotalIsoX U I n).inv := by
      apply HomologicalComplex₂.total.hom_ext
      intro p q h
      rw [injection_additiveTotalInverse]
      apply (cancel_mono (additiveTotalIsoX U I n).hom).1
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact injection_additiveTotalIsoX U I n ⟨(p,q),h⟩
    rw [he]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The chain isomorphism is oriented as U(Tot I) ≅ Tot(UI). -/
def additiveTotalIso :
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj (sumTotal I) ≅
      sumTotal ((mapDouble U).obj I) := (asIso (additiveTotalInverse U I)).symm

lemma additiveTotalIso_formula : SummandFormula U I (additiveTotalIso U I) := by
  intro p q n h
  apply (cancel_mono ((additiveTotalIso U I).inv.f n)).1
  rw [Category.assoc, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f]
  erw [Category.comp_id]
  exact (injection_additiveTotalInverse U I p q n h).symm

omit hI in
/-- A diagonal sub-biproduct inclusion is split, irrespective of the choice
of its bilimit bicone. This justifies applying a merely additive functor. -/
lemma split_diagonal_inclusion (axis : ℤ × ℤ → ℤ) (a n : ℤ)
    (b : Bicone (fun i : {i : Diagonal n // a ≤ axis i.val} =>
      diagonalFamily I n i.val)) (hb : b.IsBilimit)
    (j : b.pt ⟶ (sumTotal I).X n)
    (hj : ∀ i, b.ι i ≫ j = sumInjection I i.val.val.1 i.val.val.2 n i.val.property) :
    IsSplitMono j := by
  let r : (sumTotal I).X n ⟶ b.pt := I.totalDesc (fun p q h =>
    if h' : a ≤ axis (p,q) then b.ι ⟨⟨(p,q),h⟩,h'⟩ else 0)
  refine IsSplitMono.mk' ⟨r, ?_⟩
  apply hb.isColimit.hom_ext
  rintro ⟨i⟩
  change b.ι i ≫ (j ≫ r) = b.ι i ≫ 𝟙 _
  rw [← Category.assoc, hj]
  dsimp only [r]
  rw [HomologicalComplex₂.ι_totalDesc]
  simp only [i.property, dite_true, Category.comp_id]

lemma additiveTotalIso_filtrations : SplitFiltrationFormula U I (additiveTotalIso U I) := by
  intro axis haxis a n b hb j hj hlegs
  have hf : {i : {i : Diagonal n // a ≤ axis i.val} |
      ¬ IsZero (diagonalFamily I n i.val)}.Finite :=
    (hI.out n).preimage (fun _ _ _ _ h => Subtype.ext h)
  have hs : IsSplitMono j := split_diagonal_inclusion I axis a n b hb j hlegs
  have hm : Mono (U.map j) := inferInstance
  refine ⟨⟨mapFiniteBicone U hf b hb⟩, inferInstance, ?_⟩
  intro i
  rw [← U.map_comp_assoc, hlegs]
  exact additiveTotalIso_formula U I _ _ _ _

omit hI in
/-- Identify the actual filtration objects and their inclusions in each total degree. -/
lemma filtration_step_iso
    (e : (U.mapHomologicalComplex (.up ℤ)).obj (sumTotal I) ≅
      sumTotal ((mapDouble U).obj I))
    (he : SplitFiltrationFormula U I e)
    (axis : ℤ × ℤ → ℤ) (haxis : axis = Prod.fst ∨ axis = Prod.snd)
    (F : Filtration (sumTotal I)) (G : Filtration (sumTotal ((mapDouble U).obj I)))
    (hF : HasFiltrationFormula I axis F)
    (hG : HasFiltrationFormula ((mapDouble U).obj I) axis G) (a n : ℤ) :
    ∃ t : U.obj (F.piece a n : C) ≅ (G.piece a n : D),
      t.hom ≫ (G.piece a n).arrow = U.map (F.piece a n).arrow ≫ e.hom.f n := by
  obtain ⟨b, hb, j, hj, hF', hlegs⟩ := hF a n
  obtain ⟨c, hc, k, hk, hG', hlegs'⟩ := hG a n
  obtain ⟨⟨hUb⟩, _, hUlegs⟩ := he axis haxis a n b hb j hj hlegs
  let t := hUb.isColimit.coconePointUniqueUpToIso hc.isColimit
  have ht : t.hom ≫ k = U.map j ≫ e.hom.f n := by
    apply hUb.isColimit.hom_ext
    rintro ⟨i⟩
    rw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    change c.ι i ≫ k = U.map (b.ι i) ≫ U.map j ≫ e.hom.f n
    rw [hlegs']
    exact (hUlegs i).symm
  rw [← hF', ← hG']
  refine ⟨U.mapIso (Subobject.underlyingIso j) ≪≫ t ≪≫
    (Subobject.underlyingIso k).symm, ?_⟩
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Subobject.underlyingIso_arrow, ht, ← U.map_comp_assoc,
    Subobject.underlyingIso_hom_comp_eq_mk]

omit hI in
/-- The inverse leg formula also makes naturality independent of any chosen
realizations of diagonal coproducts and biproducts. -/
lemma summandFormula_inv
    (e : (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj (sumTotal I) ≅
      sumTotal ((mapDouble U).obj I)) (he : SummandFormula U I e)
    (p q n : ℤ) (h : p+q=n) :
    sumInjection ((mapDouble U).obj I) p q n h ≫ e.inv.f n =
      U.map (sumInjection I p q n h) := by
  rw [← he p q n h, Category.assoc, ← HomologicalComplex.comp_f,
    e.hom_inv_id, HomologicalComplex.id_f]
  erw [Category.comp_id]

end AdditiveFunctor

theorem additiveComparison : Specs.AdditiveComparison.{v,u,v',u'} := by
  intro C _ _ D _ _ U _ K R _ _
  let : Fact (FiniteDiagonals R.bicomplex) := ⟨resolution_finite R⟩
  exact ⟨additiveTotalIso U R.bicomplex, additiveTotalIso_formula U R.bicomplex,
    additiveTotalIso_filtrations U R.bicomplex⟩

theorem additiveNaturality : Specs.AdditiveNaturality.{v,u,v',u'} := by
  intro C _ _ D _ _ U _ K L R S _ _ _ _ e e' he he' a
  apply (cancel_epi e.inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change _ ≫ (e.inv.f n ≫ U.map ((HomologicalComplex₂.total.map a
    (ComplexShape.up ℤ)).f n) ≫ e'.hom.f n) = _
  rw [← Category.assoc, summandFormula_inv U R.bicomplex e he p q n h]
  rw [← U.map_comp_assoc, HomologicalComplex₂.ιTotal_map, U.map_comp]
  rw [Category.assoc, he' p q n h, HomologicalComplex₂.ιTotal_map]
  rfl

section Derived

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C]

private lemma isIso_unit_on_injectives (U : C ⥤ D) [U.Additive]
    (I : CochainComplex.Plus C) (hI : ∀ n, Injective (I.obj.X n)) :
    IsIso (U.rightDerivedFunctorPlusUnit.app I) := by
  obtain ⟨I, n, hn⟩ := I
  let J : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty (isInjective C) I hI
  have hJ : J.IsStrictlyGE n := by
    rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C)]
  let J' : CochainComplex.Plus (InjectiveObject C) := ⟨J, n, hJ⟩
  exact inferInstanceAs
    (IsIso (U.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj J')))

/-- Compute the right derived value on a given augmented injective replacement. -/
def replacementComparison (U : C ⥤ D) [U.Additive] {K I : CochainComplex.Plus C}
    (a : K ⟶ I) (ha : QuasiIso a.hom) (hI : ∀ n, Injective (I.obj.X n)) :
    ReplacementComparison U K I a := by
  letI := isIso_unit_on_injectives U I hI
  letI := Localization.inverts (DerivedCategory.Plus.Q (C := C))
    (CochainComplex.Plus.quasiIso C) a ((CochainComplex.Plus.quasiIso_iff C a).2 ha)
  let e := U.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map a)) ≪≫
    (asIso (U.rightDerivedFunctorPlusUnit.app I)).symm
  exact ⟨ha, hI, e, by simp [e]⟩

/-- The shared model for the two filtrations, using the signed totalization of
the given Cartan–Eilenberg resolution. -/
def derivedTotalComparison (U : C ⥤ D) [U.Additive] (K : CochainComplex.Plus C)
    (R : ResolutionData K.obj) [R.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble U).obj R.bicomplex).HasTotal (.up ℤ)] : DerivedTotalComparison U K R := by
  let h := augmentation R
  let a := h.choose
  have hBound : CochainComplex.plus C (sumTotal R.bicomplex) := by
    obtain ⟨L, hL⟩ := (boundedInjective R).1
    exact ⟨L, (CochainComplex.isStrictlyGE_iff _ _).2 hL⟩
  let a' : K ⟶ (⟨sumTotal R.bicomplex, hBound⟩ : CochainComplex.Plus C) :=
    ObjectProperty.homMk a
  letI : Fact (FiniteDiagonals R.bicomplex) := ⟨resolution_finite R⟩
  exact ⟨hBound, a', h.choose_spec.2,
    replacementComparison U a' h.choose_spec.1 (boundedInjective R).2,
    additiveTotalIso U R.bicomplex, additiveTotalIso_formula U R.bicomplex⟩

end Derived

end AdvancedHomologicalAlgebra.CartanEilenbergTotalization
