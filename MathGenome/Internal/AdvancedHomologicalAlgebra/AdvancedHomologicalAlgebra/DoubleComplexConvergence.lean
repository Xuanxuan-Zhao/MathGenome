import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexFirstPages
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiniteTargetComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexConvergence

/-! HA-B04: finite-diagonal convergence and comparison for both filtrations. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra.DoubleComplexConvergence
open DoubleTotalization FiniteDiagonalFiltrations FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The prescribed summand inclusions determine the filtration subobjects. -/
theorem filtration_formula_unique (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
    (axis : ℤ × ℤ → ℤ) (F G : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K axis F) (hG : HasFiltrationFormula K axis G) :
    ∀ a n, F.piece a n = G.piece a n := by
  have hle (F G : Filtration (sumTotal K))
      (hF : HasFiltrationFormula K axis F) (hG : HasFiltrationFormula K axis G) (a n : ℤ) :
      F.piece a n ≤ G.piece a n := by
    obtain ⟨b, hb, ι, hι, eι, hbi⟩ := hF a n
    rw [← eι]
    let g := hb.isColimit.desc (Cofan.mk (G.piece a n : A) (fun i =>
      DoubleComplexFirstPages.summandToStep K axis G hG a i.val.val.1 i.val.val.2 n
        i.val.property i.property))
    apply Subobject.mk_le_of_comm g
    apply hb.isColimit.hom_ext
    rintro ⟨i⟩
    change b.ι i ≫ (g ≫ (G.piece a n).arrow) = b.ι i ≫ ι
    rw [← Category.assoc, show b.ι i ≫ g = _ from hb.isColimit.fac _ ⟨i⟩]
    change DoubleComplexFirstPages.summandToStep K axis G hG a i.val.val.1 i.val.val.2 n
      i.val.property i.property ≫ (G.piece a n).arrow = b.ι i ≫ ι
    rw [DoubleComplexFirstPages.summandToStep_arrow, hbi i]
  intro a n
  exact le_antisymm (hle F G hF hG a n) (hle G F hG hF a n)

/-- Transfer degreewise finiteness from HA-B02 to any realization of its formulas. -/
theorem formula_finite (K : Bicomplex A) (hK : FiniteDiagonals K)
    [K.HasTotal (ComplexShape.up ℤ)] (axis : ℤ × ℤ → ℤ)
    (ha : axis = Prod.fst ∨ axis = Prod.snd) (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K axis F) :
    FiniteFiltrationConvergence.DegreewiseFinite F := by
  obtain ⟨Fc, Fr, hc, hr, hfc, hfr⟩ := FiniteDiagonalFiltrations.filtrations K hK
  rcases ha with rfl | rfl
  · intro n
    obtain ⟨a,b,h⟩ := hfc n
    refine ⟨a,b,?_,?_⟩
    · intro p hp
      rw [filtration_formula_unique K _ F Fc hF hc p n]
      exact (h p).1 hp
    · intro p hp
      rw [filtration_formula_unique K _ F Fc hF hc p n]
      exact (h p).2 hp
  · intro n
    obtain ⟨a,b,h⟩ := hfr n
    refine ⟨a,b,?_,?_⟩
    · intro p hp
      rw [filtration_formula_unique K _ F Fr hF hr p n]
      exact (h p).1 hp
    · intro p hp
      rw [filtration_formula_unique K _ F Fr hF hr p n]
      exact (h p).2 hp

/-- Apply the finite convergence theorem without identifying the two axes. -/
theorem converges_of_finite {T : CochainComplex A ℤ} (F : Filtration T)
    (hF : FiniteFiltrationConvergence.DegreewiseFinite F) : Converges F where
  finite := hF
  target := cohomology_filtration F hF
  stabilization := uniform_stabilization F hF
  limit D r p n _ h := ⟨limitIso F D r p n h⟩
  differential := by
    intro D n
    obtain ⟨R,hR,h⟩ := uniform_stabilization F hF n
    exact ⟨R,hR,fun r hr hR' p => differential_zero_of_stabilized F D r hr p n (h r hR' p)⟩

theorem double_complex_convergence : Specs.Convergence.{v,u} := by
  intro A _ _ K hK _ Fc Fr hc hr
  exact ⟨converges_of_finite Fc (formula_finite K hK _ (Or.inl rfl) Fc hc),
    converges_of_finite Fr (formula_finite K hK _ (Or.inr rfl) Fr hr)⟩

theorem double_complex_limit_naturality : Specs.Naturality.{v,u} := by
  intro A _ _ K L hK hL _ _ axis ha F G hF hG f g hg D E M r p n I J hI hJ
  exact limitIso_naturality g D E M r p n I J hI

/-- A columnwise quasi-isomorphism gives an isomorphism on every first-page term. -/
theorem column_page_isIso (K L : Bicomplex A)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (sumTotal K)) (G : Filtration (sumTotal L))
    (hF : HasFiltrationFormula K Prod.fst F) (hG : HasFiltrationFormula L Prod.fst G)
    (D : F03Specs.PageData F) (E : F03Specs.PageData G) (f : K ⟶ L)
    (g : FilteredMap ⟨sumTotal K,F⟩ ⟨sumTotal L,G⟩)
    (hg : g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E)
    (h : ∀ p, QuasiIso (f.f p)) (p n : ℤ) :
    IsIso (M.map 1 p n) := by
  let q := n-p
  have := h p
  have heq := DoubleComplexFirstPages.columnFirstIsoAt_naturality K F hF G hG D E
    f g hg M p q n (by dsimp [q]; omega)
  have hm : M.map 1 p n =
      (DoubleComplexFirstPages.columnFirstIsoAt K F hF D p q n (by dsimp [q]; omega)).hom ≫
      HomologicalComplex.homologyMap (f.f p) q ≫
      (DoubleComplexFirstPages.columnFirstIsoAt L G hG E p q n (by dsimp [q]; omega)).inv := by
    rw [← Category.assoc, ← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hm]
  infer_instance

/-- The row first-page square gives the other comparison, with its own filtration. -/
theorem row_page_isIso (K L : Bicomplex A)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (sumTotal K)) (G : Filtration (sumTotal L))
    (hF : HasFiltrationFormula K Prod.snd F) (hG : HasFiltrationFormula L Prod.snd G)
    (D : F03Specs.PageData F) (E : F03Specs.PageData G) (f : K ⟶ L)
    (g : FilteredMap ⟨sumTotal K,F⟩ ⟨sumTotal L,G⟩)
    (hg : g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E)
    (h : ∀ p, QuasiIso
      (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f p))
    (p n : ℤ) : IsIso (M.map 1 p n) := by
  let q := n-p
  have := h p
  have heq := DoubleComplexFirstPages.rowFirstIsoAt_naturality K F hF G hG D E
    f g hg M p q n (by dsimp [q]; omega)
  have hm : M.map 1 p n =
      (DoubleComplexFirstPages.rowFirstIsoAt K F hF D p q n (by dsimp [q]; omega)).hom ≫
      HomologicalComplex.homologyMap
        (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f p) q ≫
      (DoubleComplexFirstPages.rowFirstIsoAt L G hG E p q n (by dsimp [q]; omega)).inv := by
    rw [← Category.assoc, ← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hm]
  infer_instance

/-- Finite comparison turns a first-page isomorphism into the actual total
cohomology isomorphism. -/
theorem total_quasiIso_of_page (K L : Bicomplex A)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (sumTotal K)) (G : Filtration (sumTotal L))
    (hF : FiniteFiltrationConvergence.DegreewiseFinite F)
    (hG : FiniteFiltrationConvergence.DegreewiseFinite G) (f : K ⟶ L)
    (g : FilteredMap ⟨sumTotal K,F⟩ ⟨sumTotal L,G⟩)
    (hg : g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
    (D : F03Specs.PageData F) (E : F03Specs.PageData G)
    (M : FilteredPageFunctoriality.MapData g D E)
    (h : ∀ p n, IsIso (M.map 1 p n)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) := by
  have ht := FiniteTargetComparison.target_isomorphisms g hF hG D E M 1 (by omega) h
  rw [quasiIso_iff]
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).2
  obtain ⟨e,he,_⟩ := ht n
  rw [← hg, ← he]
  infer_instance

/-- HA-B04 comparison under either of the two alternative hypotheses. -/
theorem double_complex_comparison : Specs.Comparison.{v,u} := by
  intro A _ _ K L hK hL _ _ f h
  obtain ⟨Fc,Fr,hc,hr,hfc,hfr⟩ := FiniteDiagonalFiltrations.filtrations K hK
  obtain ⟨Gc,Gr,hgc,hgr,hgcfin,hgrfin⟩ := FiniteDiagonalFiltrations.filtrations L hL
  rcases h with h | h
  · obtain ⟨g,hg⟩ := formula_filteredMap K L Prod.fst Fc Gc hc hgc f
    let D := FilteredPage.pageData Fc
    let E := FilteredPage.pageData Gc
    let M := FilteredPageFunctoriality.mapData g D E
    exact total_quasiIso_of_page K L Fc Gc
      (formula_finite K hK _ (Or.inl rfl) Fc hc)
      (formula_finite L hL _ (Or.inl rfl) Gc hgc) f g hg D E M
      (column_page_isIso K L Fc Gc hc hgc D E f g hg M h)
  · obtain ⟨g,hg⟩ := formula_filteredMap K L Prod.snd Fr Gr hr hgr f
    let D := FilteredPage.pageData Fr
    let E := FilteredPage.pageData Gr
    let M := FilteredPageFunctoriality.mapData g D E
    exact total_quasiIso_of_page K L Fr Gr
      (formula_finite K hK _ (Or.inr rfl) Fr hr)
      (formula_finite L hL _ (Or.inr rfl) Gr hgr) f g hg D E M
      (row_page_isIso K L Fr Gr hr hgr D E f g hg M h)

/-- Totalization preserves the zero morphism even though only the individual
required diagonal coproducts, rather than arbitrary coproducts, are assumed. -/
theorem total_map_zero (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)] :
    HomologicalComplex₂.total.map (0 : K ⟶ K) (ComplexShape.up ℤ) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simpa only [sumInjection, comp_zero, HomologicalComplex.zero_f_apply,
    zero_comp] using
    HomologicalComplex₂.ιTotal_map K K (0 : K ⟶ K) (ComplexShape.up ℤ) p q n hpq

/-- An invertible zero endomorphism on every cohomology object forces exactness. -/
theorem acyclic_of_quasiIso_zero (T : CochainComplex A ℤ) (h : QuasiIso (0 : T ⟶ T)) :
    T.Acyclic := by
  have := h
  intro n
  apply (HomologicalComplex.exactAt_iff_isZero_homology T n).2
  apply (IsZero.iff_id_eq_zero _).2
  have hi := (quasiIsoAt_iff_isIso_homologyMap (0 : T ⟶ T) n).1 inferInstance
  have hz : HomologicalComplex.homologyMap (0 : T ⟶ T) n = 0 := by simp
  rw [hz] at hi
  have := hi
  have hh := IsIso.hom_inv_id (0 : T.homology n ⟶ T.homology n)
  simpa only [zero_comp] using hh.symm

/-- HA-B04 acyclicity, by applying comparison to the zero endomorphism. -/
theorem double_complex_acyclicity : Specs.Acyclicity.{v,u} := by
  intro A _ _ K hK _ h
  have hi : QuasiIso (HomologicalComplex₂.total.map (0 : K ⟶ K) (ComplexShape.up ℤ)) := by
    apply double_complex_comparison K K hK hK (0 : K ⟶ K)
    rcases h with h | h
    · left
      intro p
      rw [quasiIso_iff]
      intro q
      exact (quasiIsoAt_iff_exactAt _ q (h p q)).2 (h p q)
    · right
      intro p
      rw [quasiIso_iff]
      intro q
      exact (quasiIsoAt_iff_exactAt _ q (h p q)).2 (h p q)
  rw [total_map_zero] at hi
  exact acyclic_of_quasiIso_zero (sumTotal K) hi

section DistinctFiltrations

open Specs (singleBicomplex)

local instance : singleBicomplex.HasTotal (ComplexShape.up ℤ) := by
  intro n
  infer_instance

private theorem singleBicomplex_isZero (p q : ℤ) (h : (p, q) ≠ (0, 1)) :
    IsZero ((singleBicomplex.X p).X q) := by
  have hz : IsZero (ModuleCat.of ℚ PUnit) :=
    ModuleCat.isZero_iff_subsingleton.2 inferInstance
  simpa only [singleBicomplex, HomologicalComplex₂.ofGradedObject_X_X, ite_eq_right h] using hz

private theorem singleBicomplex_finite : FiniteDiagonals singleBicomplex := by
  intro n
  have hf : ((Subtype.val : Diagonal n → ℤ × ℤ) ⁻¹' {((0 : ℤ), (1 : ℤ))}).Finite :=
    (Set.finite_singleton _).preimage Subtype.val_injective.injOn
  apply hf.subset
  intro i hi
  by_contra h
  exact hi (singleBicomplex_isZero i.val.1 i.val.2 h)

private def singleDegreeOneIso :
    (singleBicomplex.X 0).X 1 ≅ (sumTotal singleBicomplex).X 1 := by
  letI : ∀ n, HasBiproduct (diagonalFamily singleBicomplex n) :=
    diagonalBiproducts singleBicomplex singleBicomplex_finite
  refine ⟨sumInjection singleBicomplex 0 1 1 (by simp),
    sumProjection singleBicomplex 0 1 1 (by simp), injection_sumProjection_self _ _ _ _ _, ?_⟩
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  by_cases h : (p, q) = (0, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp only [sumInjection, ← Category.assoc]
    change (sumInjection singleBicomplex 0 1 1 hpq ≫
      sumProjection singleBicomplex 0 1 1 hpq) ≫
      sumInjection singleBicomplex 0 1 1 hpq = _
    simp
  · exact (singleBicomplex_isZero p q h).eq_of_src _ _

private theorem singleTotal_d (n m : ℤ) : (sumTotal singleBicomplex).d n m = 0 := by
  by_cases h : (ComplexShape.up ℤ).Rel n m
  · change n + 1 = m at h
    subst m
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p + q = n at hpq
    change sumInjection singleBicomplex p q n hpq ≫
      (sumTotal singleBicomplex).d n (n + 1) = _
    rw [sumDifferential singleBicomplex p (p + 1) q (q + 1) n (n + 1)
      rfl rfl hpq (by omega) (by omega)]
    simp [singleBicomplex]
  · exact (sumTotal singleBicomplex).shape n m h

private def singleTotalHomologyIso :
    (sumTotal singleBicomplex).homology 1 ≅ ModuleCat.of ℚ ℚ := by
  let T := sumTotal singleBicomplex
  let data := ShortComplex.LeftHomologyData.ofZeros (T.sc 1)
    (singleTotal_d _ _) (singleTotal_d _ _)
  exact data.homologyIso ≪≫ singleDegreeOneIso.symm ≪≫
    eqToIso (by simp [singleBicomplex])

/-- At step one only the row filtration contains the lone nonzero summand. -/
theorem row_column_filtrations_differ : Specs.DistinctCohomologyFiltrations := by
  change FiniteDiagonals singleBicomplex ∧ _
  obtain ⟨Fc, Fr, hc, hr, -, -⟩ :=
    FiniteDiagonalFiltrations.filtrations singleBicomplex singleBicomplex_finite
  have hc₁ : Fc.piece 1 1 = ⊥ := by
    obtain ⟨b, hb, ι, hι, eι, _⟩ := hc 1 1
    rw [← eι]
    apply Subobject.mk_eq_bot_iff_zero.mpr
    apply hb.isColimit.hom_ext
    rintro ⟨i⟩
    apply (singleBicomplex_isZero _ _ ?_).eq_of_src
    intro h
    have hi := i.property
    change 1 ≤ i.val.val.1 at hi
    rw [congrArg Prod.fst h] at hi
    omega
  have hr₁ : Fr.piece 1 1 = ⊤ := by
    obtain ⟨b, _, ι, hι, eι, hbi⟩ := hr 1 1
    let i : {i : Diagonal 1 // (1 : ℤ) ≤ i.val.2} := ⟨⟨(0, 1), by simp⟩, le_rfl⟩
    have hcomp : b.ι i ≫ ι = singleDegreeOneIso.hom := hbi i
    have : Epi ι := epi_of_epi_fac hcomp
    rw [← eι]
    have : IsIso ι := isIso_of_mono_of_epi ι
    exact Subobject.mk_eq_top_of_isIso ι
  have hcH := cohomologyPiece_eq_bot Fc 1 1 hc₁
  have hrH := cohomologyPiece_eq_top Fr 1 1 hr₁
  refine ⟨singleBicomplex_finite, ⟨singleTotalHomologyIso⟩, Fc, Fr, hc, hr, hcH, hrH, ?_⟩
  rw [hcH, hrH]
  intro h
  have := (Subobject.isIso_arrow_iff_eq_top _).2 h
  have hz : IsZero ((sumTotal singleBicomplex).homology 1) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi (⊥ : Subobject ((sumTotal singleBicomplex).homology 1)).arrow).1
    simp only [Subobject.bot_arrow, zero_comp]
  have hs := ModuleCat.isZero_iff_subsingleton.1 (hz.of_iso singleTotalHomologyIso.symm)
  exact zero_ne_one (hs.elim (0 : ℚ) 1)

end DistinctFiltrations

end AdvancedHomologicalAlgebra.DoubleComplexConvergence
