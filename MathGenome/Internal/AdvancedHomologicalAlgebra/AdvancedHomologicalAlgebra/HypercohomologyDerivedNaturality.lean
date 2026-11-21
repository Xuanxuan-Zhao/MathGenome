import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ColumnHypercohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.RowHypercohomology

/-! HA-G03: the two hypercohomology spectral sequences and descent of the
row sequence, with all target filtration steps, to the bounded-below derived category. -/
noncomputable section
set_option linter.style.haveILetI false
set_option linter.checkUnivs false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u v' u' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
open CartanEilenbergData CartanEilenbergTotalization DoubleTotalization
open FiniteDiagonalFiltrations FiniteFiltrationConvergence DoubleComplexFirstPages
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

/-- Realization of the second-axis filtration and all its actual pages. -/
def rowModel (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    (R : ResolutionData K) : RowModel F R := by
  let hI := (additiveSupport F R).1
  let ht := (additiveSupport F R).2
  letI := ht
  let hf := filtrations ((mapDouble F).obj R.bicomplex) hI
  let Fr := Classical.choose (Classical.choose_spec hf)
  let hr := (Classical.choose_spec (Classical.choose_spec hf)).2.1
  let hp := filtered_page_cohomology Fr
  let D := Classical.choose hp
  let C := Classical.choice (Classical.choose_spec hp)
  exact ⟨ht, Fr, hr, D, C, rowData _ Fr hr D,
    DoubleComplexConvergence.converges_of_finite Fr
      (DoubleComplexConvergence.formula_finite _ hI _ (Or.inr rfl) Fr hr)⟩

/-- Filtered total map for every double-complex map. -/
def modelLift (F : A ⥤ B) [F.Additive] {K L : CochainComplex A ℤ}
    {R : ResolutionData K} {S : ResolutionData L}
    (M : RowModel F R) (N : RowModel F S) (a : R.bicomplex ⟶ S.bicomplex) :
    letI := M.total; letI := N.total
    {g : FilteredMap (modelFiltered F M) (modelFiltered F N) //
      g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)} := by
  letI := M.total
  letI := N.total
  exact ⟨Classical.choose (formula_filteredMap _ _ Prod.snd _ _ M.formula N.formula
    ((mapDouble F).map a)), Classical.choose_spec (formula_filteredMap _ _ Prod.snd _ _
      M.formula N.formula ((mapDouble F).map a))⟩

section Derived
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- Compute E₂ by taking homology of the signed first-page comparison and
using the augmentation of the simultaneous cohomology column. The abutment
uses the same augmented total comparison as the column spectral sequence. -/
def data (K : CochainComplex.Plus A) (R : ResolutionData K.obj) : Data F K R := by
  let M := rowModel F R
  letI := M.total
  letI := (finiteSupport R).2
  let comparison := RowHypercohomology.secondPageComputation F R M.filtration
    M.formula M.pages M.next
  exact { M with
    secondComparison := comparison
    secondIso := fun p q => comparison.iso F R M.filtration M.formula M.pages (p : ℤ) q
    secondIso_eq := fun _ _ => rfl
    negative := RowHypercohomology.rowSecond_negative F R M.filtration M.formula M.pages
    targetComparison := derivedTotalComparison F K R
    targetIso := fun n => (ColumnHypercohomology.totalValueIso R F n).symm
    targetIso_eq := fun _ => rfl }

def lift {K L : CochainComplex.Plus A} (R : ResolutionData K.obj)
    (S : ResolutionData L.obj) (a : R.bicomplex ⟶ S.bicomplex) :
    LiftData F (data F K R) (data F L S) a :=
  let g := modelLift F (data F K R).toRowModel (data F L S).toRowModel a
  ⟨g.val, g.property, FilteredPageFunctoriality.mapData g.val _ _⟩

lemma lift_second_naturality {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a) (p : ℕ) (q : ℤ) :
    (lift F R S a).maps.map 2 (p:ℤ) ((p:ℤ)+q) ≫
        ((data F L S).secondIso p q).hom =
      ((data F K R).secondIso p q).hom ≫
        (rightValue F p).map (HomologicalComplex.homologyMap f.hom q) := by
  let M := data F K R
  let N := data F L S
  let g := lift F R S a
  letI := M.total
  letI := N.total
  have naturality := RowHypercohomology.computedRowSecondIso_naturality F R S
    M.filtration N.filtration M.formula N.formula M.pages N.pages
    a g.filtered g.hom_eq g.maps f.hom ha (p : ℤ) q
  rw [RowHypercohomology.computedRowSecondIso_eq F R _ _ _ M.next,
    RowHypercohomology.computedRowSecondIso_eq F S _ _ _ N.next] at naturality
  exact naturality

/-- Homology naturality on the second page gives equality whenever the input
maps agree on ordinary cohomology, including homotopic input maps. -/
lemma lift_eq_of_homologyMap_eq {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f g : K ⟶ L) (a b : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a)
    (hb : CartanEilenbergComparison.IsLift R S g.hom b)
    (hfg : ∀ q, HomologicalComplex.homologyMap f.hom q = HomologicalComplex.homologyMap g.hom q)
    (r : ℤ) (hr : 2 ≤ r) : ∀ p n,
    (lift F R S a).maps.map r p n = (lift F R S b).maps.map r p n := by
  apply RowHypercohomology.pageMaps_eq_of_eq (lift F R S a).maps (lift F R S b).maps
    2 (by omega) _ r hr
  intro p n
  let q : ℤ := n-p
  have h : (lift F R S a).maps.map 2 p (p+q) =
      (lift F R S b).maps.map 2 p (p+q) := by
    by_cases hp : 0 ≤ p
    · lift p to ℕ using hp
      apply (cancel_mono ((data F L S).secondIso p q).hom).1
      rw [lift_second_naturality F R S f a ha,
        lift_second_naturality F R S g b hb, hfg]
    · exact ((data F K R).negative p q (by omega)).eq_of_src _ _
  have hn : p+q=n := by dsimp [q]; omega
  exact hn ▸ h

lemma lift_id (K : CochainComplex.Plus A) (R : ResolutionData K.obj) (r p n : ℤ) :
    (lift F R R (𝟙 R.bicomplex)).maps.map r p n = 𝟙 _ := by
  letI := (data F K R).total
  have h : (lift F R R (𝟙 R.bicomplex)).filtered =
      FilteredMap.id (modelFiltered F (data F K R).toRowModel) := by
    apply ColumnHypercohomology.filteredMap_ext
    rw [(lift F R R (𝟙 R.bicomplex)).hom_eq, CategoryTheory.Functor.map_id]
    exact HomologicalComplex₂.total.map_id _ _
  change FilteredPageFunctoriality.pageMap (lift F R R (𝟙 R.bicomplex)).filtered
    (data F K R).pages (data F K R).pages r p n = _
  rw [h, FilteredPageFunctoriality.pageMap_id]

lemma lift_comp {K L T : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (U : ResolutionData T.obj)
    (a : R.bicomplex ⟶ S.bicomplex) (b : S.bicomplex ⟶ U.bicomplex) (r p n : ℤ) :
    (lift F R U (a ≫ b)).maps.map r p n =
      (lift F R S a).maps.map r p n ≫ (lift F S U b).maps.map r p n := by
  letI := (data F K R).total
  letI := (data F L S).total
  letI := (data F T U).total
  have h : (lift F R U (a ≫ b)).filtered =
      (lift F R S a).filtered.comp (lift F S U b).filtered := by
    apply ColumnHypercohomology.filteredMap_ext
    change _ = (lift F R S a).filtered.hom ≫ (lift F S U b).filtered.hom
    rw [(lift F R U (a ≫ b)).hom_eq, (lift F R S a).hom_eq,
      (lift F S U b).hom_eq, CategoryTheory.Functor.map_comp, HomologicalComplex₂.total.map_comp]
  change FilteredPageFunctoriality.pageMap (lift F R U (a ≫ b)).filtered
      (data F K R).pages (data F T U).pages r p n =
    FilteredPageFunctoriality.pageMap (lift F R S a).filtered
      (data F K R).pages (data F L S).pages r p n ≫
    FilteredPageFunctoriality.pageMap (lift F S U b).filtered
      (data F L S).pages (data F T U).pages r p n
  rw [h, FilteredPageFunctoriality.pageMap_comp]

lemma lift_target_naturality {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a) (n : ℤ) :
    HomologicalComplex.homologyMap (lift F R S a).filtered.hom n ≫
        ((data F L S).targetIso n).hom =
      ((data F K R).targetIso n).hom ≫ targetMap F f n := by
  letI := (finiteSupport R).2
  letI := (finiteSupport S).2
  letI := (data F K R).total
  letI := (data F L S).total
  change _ ≫ (ColumnHypercohomology.totalValueIso S F n).inv =
    (ColumnHypercohomology.totalValueIso R F n).inv ≫ _
  rw [(lift F R S a).hom_eq]
  apply (cancel_epi (ColumnHypercohomology.totalValueIso R F n).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← ColumnHypercohomology.totalValueIso_naturality F R S f a ha n]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Quasi-isomorphisms are invertible on E₂ by its ordinary derived-value
formula, then on every later page, and finally on every target filtration step. -/
lemma lift_quasiIso_comparison {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a) (hf : QuasiIso f.hom) :
    (∀ r, 2 ≤ r → ∀ p n, IsIso ((lift F R S a).maps.map r p n)) ∧
    S03Specs.TargetIsomorphisms (lift F R S a).filtered := by
  have htwo (p n : ℤ) : IsIso ((lift F R S a).maps.map 2 p n) := by
    let q : ℤ := n-p
    have hpq : IsIso ((lift F R S a).maps.map 2 p (p+q)) := by
      by_cases hp : 0 ≤ p
      · lift p to ℕ using hp
        letI := hf
        have hh := lift_second_naturality F R S f a ha p q
        have he : (lift F R S a).maps.map 2 (p:ℤ) ((p:ℤ)+q) =
            ((data F K R).secondIso p q).hom ≫
            (rightValue F p).map (HomologicalComplex.homologyMap f.hom q) ≫
            ((data F L S).secondIso p q).inv := by
          rw [← Category.assoc, ← hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [he]
        infer_instance
      · exact IsZero.isIso ((data F K R).negative p q (by omega))
          ((data F L S).negative p q (by omega)) _
    have hn : p+q=n := by dsimp [q]; omega
    exact hn ▸ hpq
  exact ⟨fun r hr => FilteredPageFunctoriality.comparison
      (lift F R S a).maps 2 (by omega) htwo r hr,
    FiniteTargetComparison.target_isomorphisms (lift F R S a).filtered
      (data F K R).convergence.finite (data F L S).convergence.finite
      _ _ (lift F R S a).maps 2 (by omega) htwo⟩

lemma targetPiece_eq_mk {K : CochainComplex.Plus A} {R : ResolutionData K.obj}
    (M : Data F K R) (p n : ℤ) :
    targetPiece F M p n = Subobject.mk
      ((cohomologyPiece M.filtration p n).arrow ≫ (M.targetIso n).hom) := by
  unfold targetPiece
  calc
    _ = (Subobject.map (M.targetIso n).hom).obj
        (Subobject.mk (cohomologyPiece M.filtration p n).arrow) :=
      congrArg (Subobject.map (M.targetIso n).hom).obj
        (Subobject.mk_arrow (cohomologyPiece M.filtration p n)).symm
    _ = _ := Subobject.map_mk _ _

lemma target_preserves {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (f : K ⟶ L) (p n : ℤ) :
    (targetPiece F (data F L S) p n).Factors
      ((targetPiece F (data F K R) p n).arrow ≫ targetMap F f n) := by
  obtain ⟨a,ha⟩ := CartanEilenbergComparison.liftExists R S f.hom
  let M := data F K R
  let N := data F L S
  let i := (cohomologyPiece M.filtration p n).arrow ≫ (M.targetIso n).hom
  let j := (cohomologyPiece N.filtration p n).arrow ≫ (N.targetIso n).hom
  have hs : cohomologyStepMap (lift F R S a).filtered p n ≫ j =
      i ≫ targetMap F f n := by
    dsimp only [i,j]
    rw [← Category.assoc, cohomologyStepMap_arrow, Category.assoc,
      lift_target_naturality F R S f a ha n, ← Category.assoc]
  rw [targetPiece_eq_mk F M, targetPiece_eq_mk F N]
  apply (Subobject.factors_iff _ _).2
  refine ⟨(Subobject.underlyingIso i).hom ≫
    cohomologyStepMap (lift F R S a).filtered p n ≫ (Subobject.underlyingIso j).inv, ?_⟩
  change (_ ≫ _ ≫ (Subobject.underlyingIso j).inv) ≫ (Subobject.mk j).arrow = _
  simp only [Category.assoc, Subobject.underlyingIso_arrow]
  rw [hs, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]

/-- All resolutions and all comparison lifts are included in one row system. -/
def system : System F where
  data := data F
  resolution := (ColumnHypercohomology.system F).resolution
  comparison := (ColumnHypercohomology.system F).comparison
  lift := lift F
  second_naturality := lift_second_naturality F
  next_naturality R S a r hr p n := FilteredPageFunctoriality.next_naturality
    (lift F R S a).maps (data F _ R).next (data F _ S).next r hr p n
  target_naturality := lift_target_naturality F
  limit_naturality R S a r p n I J hI hJ :=
    limitIso_naturality (lift F R S a).filtered _ _ _ r p n I J hI
  target_decreasing K R p n :=
    (Subobject.map ((data F K R).targetIso n).hom).monotone
      (cohomologyPiece_decreasing (data F K R).filtration p n)
  target_finite K R n := by
    obtain ⟨a,b,ha,hb⟩ := (data F K R).convergence.target.finite n
    refine ⟨a,b,fun p hp => ?_,fun p hp => ?_⟩
    · rw [targetPiece, ha p hp, Subobject.map_top, Subobject.mk_eq_top_of_isIso]
    · rw [targetPiece, hb p hp, Subobject.map_bot]
  target_preserves := target_preserves F
  target_resolution_independent K R S p n := by
    apply le_antisymm <;> apply Subobject.le_of_factors
    · simpa only [targetMap, ColumnHypercohomology.targetMap, CategoryTheory.Functor.map_id, Category.comp_id]
        using target_preserves F R S (𝟙 K) p n
    · simpa only [targetMap, ColumnHypercohomology.targetMap, CategoryTheory.Functor.map_id, Category.comp_id]
        using target_preserves F S R (𝟙 K) p n
  independent R S f a b ha hb :=
    lift_eq_of_homologyMap_eq F R S f f a b ha hb (fun _ => rfl)
  map_id := lift_id F
  map_comp := lift_comp F
  homotopy_compatible R S f g h a b ha hb :=
    lift_eq_of_homologyMap_eq F R S f g a b ha hb (fun q => h.homologyMap_eq q)
  quasiIso_comparison := lift_quasiIso_comparison F
  resolution_independence K R S := by
    obtain ⟨a,b,ha,hb,_,_⟩ := CartanEilenbergComparison.verticalInverseComparisons R S
    have ht := lift_quasiIso_comparison F R S (𝟙 K) a ha (by dsimp; infer_instance)
    exact ⟨a,b,ha,hb,ht.1,ht.2⟩

end Derived
namespace RowDiagram
/-- Componentwise invertibility includes every filtration step. -/
lemma isIso_of_components {X Y : RowDiagram B} (f : X ⟶ Y)
    (hp : ∀ r p n, IsIso (f.page r p n)) (ht : ∀ n, IsIso (f.target n))
    (hs : ∀ p n, IsIso (f.step p n)) : IsIso f := by
  letI := hp
  letI := ht
  letI := hs
  have hd : ∀ r p n, inv (f.page r p n) ≫ X.differential r p n =
      Y.differential r p n ≫ inv (f.page r (p+((r:ℤ)+2)) (n+1)) := by
    intro r p n
    apply (cancel_mono (f.page r (p+((r:ℤ)+2)) (n+1))).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← f.differential_comm, IsIso.inv_hom_id_assoc]
  let g : Y ⟶ X := {
    page := fun r p n => inv (f.page r p n)
    target := fun n => inv (f.target n)
    step := fun p n => inv (f.step p n)
    differential_comm := hd
    next_comm := by
      intro r p n
      apply (cancel_epi (f.page (r+1) (p+((r:ℤ)+2)) (n+1))).1
      rw [IsIso.hom_inv_id_assoc, ← Category.assoc, f.next_comm, Category.assoc,
        ← ShortComplex.homologyMap_comp]
      have h : pageComplexMap f.page f.differential_comm r p n ≫
          pageComplexMap (fun r p n => inv (f.page r p n)) hd r p n =
          𝟙 (pageComplex X r p n) := by
        ext <;> dsimp [pageComplexMap] <;> exact IsIso.hom_inv_id _
      rw [h, ShortComplex.homologyMap_id, Category.comp_id]
    inclusion_comm := by
      intro p n
      apply (cancel_mono (f.target n)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← f.inclusion_comm, IsIso.inv_hom_id_assoc]
    down_comm := by
      intro p n
      apply (cancel_mono (f.step p n)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← f.down_comm, IsIso.inv_hom_id_assoc] }
  let e : X ≅ Y := {
    hom := f
    inv := g
    hom_inv_id := by
      apply Hom.ext <;> funext <;> exact IsIso.hom_inv_id _
    inv_hom_id := by
      apply Hom.ext <;> funext <;> exact IsIso.inv_hom_id _ }
  exact e.isIso_hom
end RowDiagram

section DescentConstruction
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive] (S : System F)

/-- The filtration inclusions are monomorphisms even after transport to RF. -/
instance diagram_inclusion_mono {K : CochainComplex.Plus A} {R : ResolutionData K.obj}
    (M : Data F K R) (p n : ℤ) : Mono ((diagram F M).inclusion p n) := by
  dsimp [diagram]
  infer_instance

/-- Once the page and ambient maps agree, the maps on all filtration steps
agree because their inclusions are monic. -/
lemma diagram_hom_ext {K L : CochainComplex.Plus A}
    {R : ResolutionData K.obj} {U : ResolutionData L.obj}
    {M : Data F K R} {N : Data F L U} {f g : diagram F M ⟶ diagram F N}
    (hp : ∀ r p n, f.page r p n = g.page r p n)
    (ht : ∀ n, f.target n = g.target n) : f = g := by
  apply RowDiagram.Hom.ext
  · funext r p n; exact hp r p n
  · funext n; exact ht n
  · funext p n
    apply (cancel_mono ((diagram F N).inclusion p n)).1
    rw [f.inclusion_comm, g.inclusion_comm, ht]

def chosenResolution (K : CochainComplex.Plus A) : ResolutionData K.obj :=
  Classical.choice (S.resolution K)

def chosenLift {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (chosenResolution F S K).bicomplex ⟶ (chosenResolution F S L).bicomplex :=
  Classical.choose (S.comparison (chosenResolution F S K) (chosenResolution F S L) f)

lemma chosenLift_isLift {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    CartanEilenbergComparison.IsLift (chosenResolution F S K) (chosenResolution F S L)
      f.hom (chosenLift F S f) :=
  Classical.choose_spec (S.comparison (chosenResolution F S K) (chosenResolution F S L) f)

/-- A functor whose objects and maps are the actual row diagram. -/
def rowFunctor : CochainComplex.Plus A ⥤ RowDiagram B where
  obj K := diagram F (S.data K (chosenResolution F S K))
  map f := diagramMap F S f (chosenLift F S f) (chosenLift_isLift F S f)
  map_id K := by
    apply diagram_hom_ext F
    · intro r p n
      change (S.lift _ _ (chosenLift F S (𝟙 K))).maps.map ((r:ℤ)+2) p n = 𝟙 _
      rw [S.independent _ _ (𝟙 K) _ (𝟙 _) (chosenLift_isLift F S (𝟙 K))
        (CartanEilenbergComparison.isLift_id _) _ (by omega), S.map_id]
    · intro n
      change targetMap F (𝟙 K) n = 𝟙 _
      simp only [targetMap, ColumnHypercohomology.targetMap, CategoryTheory.Functor.map_id]
  map_comp {K L T} f g := by
    apply diagram_hom_ext F
    · intro r p n
      change (S.lift _ _ (chosenLift F S (f ≫ g))).maps.map ((r:ℤ)+2) p n =
        (S.lift _ _ (chosenLift F S f)).maps.map ((r:ℤ)+2) p n ≫
        (S.lift _ _ (chosenLift F S g)).maps.map ((r:ℤ)+2) p n
      rw [S.independent _ _ (f ≫ g) _ (chosenLift F S f ≫ chosenLift F S g)
        (chosenLift_isLift F S (f ≫ g))
        (CartanEilenbergComparison.isLift_comp _ _ _
          (chosenLift_isLift F S f) (chosenLift_isLift F S g)) _ (by omega), S.map_comp]
    · intro n
      change targetMap F (f ≫ g) n = targetMap F f n ≫ targetMap F g n
      simp only [targetMap, ColumnHypercohomology.targetMap, CategoryTheory.Functor.map_comp]

lemma rowFunctor_homotopy {K L : CochainComplex.Plus A}
    (f g : K ⟶ L) (h : Homotopy f.hom g.hom) :
    (rowFunctor F S).map f = (rowFunctor F S).map g := by
  apply diagram_hom_ext F
  · intro r p n
    exact S.homotopy_compatible _ _ f g h _ _ (chosenLift_isLift F S f)
      (chosenLift_isLift F S g) _ (by omega) p n
  · intro n
    have hq : DerivedCategory.Plus.Q.map f = DerivedCategory.Plus.Q.map g := by
      apply DerivedCategory.Plus.ι.map_injective
      exact DerivedCategory.Q_map_eq_of_homotopy A h
    change targetMap F f n = targetMap F g n
    unfold targetMap ColumnHypercohomology.targetMap
    rw [hq]

/-- Invertibility in the bundled category uses S03 on each image filtration
step, in addition to invertibility of pages and the underlying target. -/
lemma rowFunctor_isIso {K L : CochainComplex.Plus A}
    (f : K ⟶ L) (hf : QuasiIso f.hom) : IsIso ((rowFunctor F S).map f) := by
  let R := chosenResolution F S K
  let U := chosenResolution F S L
  let a := chosenLift F S f
  have h := S.quasiIso_comparison R U f a (chosenLift_isLift F S f) hf
  apply RowDiagram.isIso_of_components
  · intro r p n
    exact h.1 _ (by omega) p n
  · intro n
    change IsIso (targetMap F f n)
    letI : IsIso (DerivedCategory.Plus.Q.map f) :=
      Localization.inverts _ (CochainComplex.Plus.quasiIso A) f hf
    dsimp [targetMap, ColumnHypercohomology.targetMap]
    infer_instance
  · intro p n
    obtain ⟨e,he,hstep⟩ := h.2 n
    obtain ⟨eStep,hStep,_⟩ := hstep p
    change IsIso (cohomologyStepMap (S.lift R U a).filtered p n)
    rw [← hStep]
    infer_instance

/-- The localization universal property applied to the entire row diagram. -/
theorem system_descends : Descends F S := by
  let T := rowFunctor F S
  have hT : (CochainComplex.Plus.quasiIso A).IsInvertedBy T :=
    fun _ _ f hf => rowFunctor_isIso F S f hf
  let D := Localization.lift T hT (DerivedCategory.Plus.Q (C := A))
  refine ⟨chosenResolution F S, T, D, fun _ => rfl, ?_,
    ⟨Localization.fac T hT DerivedCategory.Plus.Q⟩, ?_, ?_, ?_⟩
  · intro K L f
    exact ⟨chosenLift F S f, chosenLift_isLift F S f, HEq.rfl⟩
  · intro K L f g h
    exact rowFunctor_homotopy F S f g (Classical.choice h)
  · intro K L f hf
    exact rowFunctor_isIso F S f hf
  · intro E hE
    letI : Localization.Lifting (DerivedCategory.Plus.Q (C := A))
        (CochainComplex.Plus.quasiIso A) T E := ⟨Classical.choice hE⟩
    exact ⟨Localization.liftNatIso DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso A) T T E D (Iso.refl T)⟩
end DescentConstruction

/-- Both spectral sequences, finite convergence and naturality, and descent
of the entire row diagram, including every target filtration step. -/
theorem hypercohomology.{u₀,v₀,u₁,v₁,w₀,w₁} :
    Specs.FullStatement.{u₀,v₀,u₁,v₁,w₀,w₁} := by
  refine ⟨ColumnHypercohomology.column_hypercohomology, ?_⟩
  intro A B _ _ _ _ _ _ _ F _ _
  exact ⟨system F, system_descends F (system F)⟩

end AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
