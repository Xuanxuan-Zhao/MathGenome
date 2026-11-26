import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.KoszulTower
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.AugmentedCechComplex
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Finset.CastCard

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped BigOperators TensorProduct

namespace CommutativeAlgebraNotes.KoszulTower

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R]

open Specs.CommutativeAlgebraNotes.KoszulTower
open Specs.CommutativeAlgebraNotes.AugmentedCechComplex (Selection product selected localizationMap preceding)
local notation "upZ" => ComplexShape.up ℤ

/-- The Koszul complex on the list of positive powers, with coefficients in `M`. -/
abbrev complex (rs : List R) (M : Coeff R) (n : ℕ) : Complex R := stage rs M n

/-- The maps in the tower multiply each summand by its product of listed generators. -/
abbrev diagram (rs : List R) (M : Coeff R) : ℕ ⥤ Complex R := tower rs M

private theorem fraction_transition (M : Coeff R) (p : R) {n m : ℕ} (h : n ≤ m) :
    scalar M (p ^ (m - n)) ≫ fraction M p m = fraction M p n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change fraction M p m (p ^ (m - n) • x) = fraction M p n x
  rw [fraction_apply M p m (p ^ (m - n) • x), fraction_apply M p n x]
  have hden : denominator p (m + 1) = denominator p (m - n) * denominator p (n + 1) := by
    apply Subtype.ext
    change p ^ (m+1) = p ^ (m-n) * p ^ (n+1)
    rw [← pow_add, show m - n + (n + 1) = m + 1 by omega]
  rw [hden]
  exact LocalizedModule.mk_cancel_common_left (denominator p (m - n)) _ x

private def scalarDiagram (M : Coeff R) (p : R) : ℕ ⥤ Coeff R where
  obj _ := M
  map {n m} _ := scalar M (p ^ (m - n))
  map_id _ := by simp
  map_comp {n m l} f g := by
    have hf := f.le
    have hg := g.le
    ext x
    change p ^ (l - n) • x = p ^ (l - m) • (p ^ (m - n) • x)
    rw [smul_smul, ← pow_add, show l - m + (m - n) = l - n by omega]

private def fractionCocone (M : Coeff R) (p : R) : Cocone (scalarDiagram M p) where
  pt := ModuleCat.of R (LocalizedModule.Away p M)
  ι.app := fraction M p
  ι.naturality {n m} f := by
    change scalar M (p ^ (m-n)) ≫ fraction M p m = fraction M p n ≫ 𝟙 _
    rw [Category.comp_id]
    exact fraction_transition M p f.le

private theorem fractionCocone_jointly_surjective (M : Coeff R) (p : R)
    (x : LocalizedModule.Away p M) :
    ∃ n : ℕ, ∃ y : M, x = fraction M p n y := by
  induction x using LocalizedModule.induction_on with
  | _ x s =>
    obtain ⟨k, hk⟩ := s.property
    have hs : s = denominator p k := Subtype.ext hk.symm
    refine ⟨k, p • x, ?_⟩
    rw [fraction_apply, hs]
    have h : denominator p (k + 1) = denominator p k * denominator p 1 := by
      apply Subtype.ext
      change p ^ (k + 1) = p ^ k * p ^ 1
      rw [pow_add]
    rw [h, ← LocalizedModule.mk_cancel_common_right (denominator p k) (denominator p 1) x]
    congr 1
    change p ^ 1 • x = p • x
    rw [pow_one]

private def fractionCoconeIsColimit (M : Coeff R) (p : R) :
    IsColimit (fractionCocone M p) := by
  letI : PreservesFilteredColimitsOfSize.{0,0} (forget (Coeff R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits.{u,u} _
  letI := reflectsColimit_of_reflectsIsomorphisms (scalarDiagram M p) (forget (Coeff R))
  apply isColimitOfReflects (forget (Coeff R))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    exact fractionCocone_jointly_surjective M p x
  · intro n x y h
    change fraction M p n x = fraction M p n y at h
    rw [fraction_apply M p n (x : M), fraction_apply M p n (y : M), LocalizedModule.mk_eq] at h
    obtain ⟨s, hs⟩ := h
    obtain ⟨k, hk⟩ := s.property
    change p ^ k = (s : R) at hk
    have heq : p ^ (k + (n+1)) • x = p ^ (k + (n+1)) • y := by
      simpa [Submonoid.smul_def, ← hk, denominator, pow_add, mul_smul] using hs
    refine ⟨n + (k + (n+1)), homOfLE (by omega), ?_⟩
    change p ^ (n + (k + (n+1)) - n) • x = p ^ (n + (k + (n+1)) - n) • y
    simpa using heq


open private rowFunctor rowIso from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison

private def selection (rs : List R) (q : ℤ) (J : Positions rs.length q) :
    Selection rs.length q := (Cech.selectionEquiv rs.length q).symm J

omit [CommRing R] in
private theorem selection_positions (rs : List R) (q : ℤ) (J : Positions rs.length q) :
    (Finset.univ.filter fun a => selected (selection rs q J) a = true) = J.val :=
  congrArg Subtype.val ((Cech.selectionEquiv rs.length q).apply_symm_apply J)

private theorem selection_product (rs : List R) (q : ℤ) (J : Positions rs.length q) :
    product R rs (selection rs q J) = positionProduct rs J := by
  rw [Cech.product_eq, selection_positions]
  rfl

private def ringFractionTensor (M : Coeff R) (p : R) (n : ℕ) :
    M ⟶ ModuleCat.of R (Localization.Away p) ⊗ M :=
  fraction M p n ≫ (localizationTensorIso M p).hom

@[simp]
private theorem ringFractionTensor_apply (M : Coeff R) (p : R) (n : ℕ) (x : M) :
    ringFractionTensor M p n x = Localization.mk (1 : R) (denominator p (n+1)) ⊗ₜ[R] x := by
  change (LocalizedModule.equivTensorProduct _ M) (fraction M p n x) = _
  rw [fraction_apply, LocalizedModule.equivTensorProduct_apply_mk]

private theorem localizationMap_fraction (p a q : R) (hq : q = a * p) (hp : p ∣ q) (e : ℕ) :
    localizationMap R p q hp (Localization.mk 1 (denominator p e)) =
      a ^ e • Localization.mk 1 (denominator q e) := by
  have hu : IsUnit (algebraMap R (Localization.Away q) (p ^ e)) :=
    by rw [map_pow]; exact (IsLocalization.Away.isUnit_of_dvd q hp).pow e
  apply (IsUnit.mul_left_inj hu).mp
  have hleft : localizationMap R p q hp (Localization.mk 1 (denominator p e)) *
      algebraMap R (Localization.Away q) (p ^ e) = 1 := by
    rw [← (localizationMap R p q hp).commutes, ← map_mul, Localization.mk_eq_mk']
    have hs := IsLocalization.mk'_spec (Localization.Away p) (1 : R) (denominator p e)
    change _ * algebraMap R (Localization.Away p) (p ^ e) = _ at hs
    rw [hs, map_one, map_one]
  rw [hleft, Algebra.smul_def, mul_right_comm, ← map_mul, ← mul_pow, ← hq, mul_comm,
    Localization.mk_eq_mk']
  have hs := IsLocalization.mk'_spec (Localization.Away q) (1 : R) (denominator q e)
  change _ * algebraMap R (Localization.Away q) (q ^ e) = _ at hs
  rw [hs, map_one]

private def rowInclusion (rs : List R) (M : Coeff R) (q : ℤ) (s : Selection rs.length q) :
    ModuleCat.of R (LocalizedModule.Away (product R rs s) M) ⟶
      ((rowFunctor (CechComplex rs)).obj M).X q :=
  (localizationTensorIso M (product R rs s)).hom ≫ (Cech.summandι rs q s ▷ M)

private def rowTermMap (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ) :
    term rs M q ⟶ ((rowFunctor (CechComplex rs)).obj M).X q :=
  Sigma.desc (fun J : Positions rs.length q =>
    fraction M (product R rs (selection rs q J)) n ≫ rowInclusion rs M q (selection rs q J))

@[reassoc (attr := simp)]
private theorem ι_rowTermMap (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ)
    (J : Positions rs.length q) :
    Sigma.ι (fun _ : Positions rs.length q => M) J ≫ rowTermMap rs M n q =
      ringFractionTensor M (product R rs (selection rs q J)) n ≫
        (Cech.summandι rs q (selection rs q J) ▷ M) := by
  rw [rowTermMap, Sigma.ι_comp_desc]
  exact (Category.assoc _ _ _).symm

omit [CommRing R] in
private theorem selection_insert (rs : List R) (q : ℤ) (J : Positions rs.length q)
    (a : Fin rs.length) (ha : a ∉ J.val) (t : Selection rs.length (q+1))
    (ht : ∀ j, selected t j = (decide (j = a) || selected (selection rs q J) j)) :
    t = selection rs (q+1) (insertPosition J a ha) := by
  apply (Cech.selectionEquiv rs.length (q+1)).injective
  apply Subtype.ext
  change (Finset.univ.filter fun j => selected t j = true) =
    (Finset.univ.filter fun j => selected (selection rs (q+1) (insertPosition J a ha)) j = true)
  rw [selection_positions]
  have hset : (Finset.univ.filter fun j => selected t j = true) =
      insert a (Finset.univ.filter fun j => selected (selection rs q J) j = true) := by
    ext j
    simp [ht]
  rw [hset, selection_positions]
  rfl

private theorem rowTerm_comm (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ) :
    rowTermMap rs M n q ≫ ((rowFunctor (CechComplex rs)).obj M).d q (q+1) =
      differential rs M n q ≫ rowTermMap rs M n (q+1) := by
  apply Sigma.hom_ext
  intro J
  rw [ι_rowTermMap_assoc, ι_differential_assoc, Preadditive.sum_comp]
  let s := selection rs q J
  change ringFractionTensor M (product R rs s) n ≫
    (Cech.summandι rs q s ▷ M) ≫ ((CechComplex rs).d q (q+1) ▷ M) = _
  rw [← comp_whiskerRight, Cech.summandι_differential]
  change ringFractionTensor M (product R rs s) n ≫
    (tensorRight M).map (∑ _, _) = _
  rw [Functor.map_sum, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hsign : preceding s a = countBefore J.val a := by
    rw [Cech.preceding_card]
    unfold countBefore
    have hs : (Finset.univ.filter fun j => selected s j = true ∧ j < a) =
        J.val.filter (· < a) := by
      rw [← selection_positions rs q J]
      ext j
      simp [s]
    rw [hs]
  rw [hsign]
  by_cases ha : a ∉ J.val
  · have hsa : selected s a = false := by
      have hh : a ∉ (Finset.univ.filter fun j => selected s j = true) := by
        rwa [selection_positions]
      simpa using hh
    obtain ⟨t, hp, ht, hpt, hloc⟩ := Cech.summandι_insert_localization rs q s a hsa
    have he := selection_insert rs q J a ha t ht
    subst t
    rw [hloc]
    have hz {X Y : Coeff R} (g : X ⟶ Y) (z : ℤˣ) :
        (tensorRight M).map (z • g) = z • (tensorRight M).map g :=
      (tensorRight M).map_zsmul
    rw [hz, Functor.map_comp]
    simp only [component, dite_eq_left ha]
    have hl {X Y : Coeff R} (f : M ⟶ X) (g : X ⟶ Y) (z : ℤˣ) :
        f ≫ (z • g) = z • (f ≫ g) := Preadditive.comp_zsmul f g z
    have hr {Y : Coeff R} (f : M ⟶ term rs M (q+1)) (g : term rs M (q+1) ⟶ Y) (z : ℤˣ) :
        (z • f) ≫ g = z • (f ≫ g) := Preadditive.zsmul_comp f g z
    rw [hl, hr, Category.assoc, ι_rowTermMap, ← Category.assoc, ← Category.assoc]
    congr 2
    ext x
    change (_ ▷ M) (ringFractionTensor M (product R rs s) n x) =
      ringFractionTensor M (product R rs (selection rs (q+1) (insertPosition J a ha))) n
        (rs.get a ^ (n+1) • x)
    rw [ringFractionTensor_apply, ringFractionTensor_apply, ModuleCat.MonoidalCategory.whiskerRight_apply]
    change localizationMap R _ _ hp (Localization.mk 1 _) ⊗ₜ[R] x = _
    rw [localizationMap_fraction _ _ _ hpt hp, TensorProduct.smul_tmul]
  · have hsa : selected s a = true := by
      have hh : a ∈ (Finset.univ.filter fun j => selected s j = true) := by
        rw [selection_positions]
        exact not_not.mp ha
      simpa using hh
    rw [Cech.summandι_insert_eq_zero false rs q s a hsa]
    simp [component, ha]

private def rowLeg (rs : List R) (M : Coeff R) (n : ℕ) :
    complex rs M n ⟶ (rowFunctor (CechComplex rs)).obj M where
  f := rowTermMap rs M n
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    rw [stage_d]
    exact rowTerm_comm rs M n i

private def rowCocone (rs : List R) (M : Coeff R) : Cocone (diagram rs M) where
  pt := (rowFunctor (CechComplex rs)).obj M
  ι.app := rowLeg rs M
  ι.naturality {n m} f := by
    change transition rs M f.le ≫ rowLeg rs M m = rowLeg rs M n ≫ 𝟙 _
    rw [Category.comp_id]
    apply HomologicalComplex.hom_ext
    intro q
    apply Sigma.hom_ext
    intro J
    change Sigma.ι (fun _ : Positions rs.length q => M) J ≫
      transitionTerm rs M n m q ≫ rowTermMap rs M m q = _ ≫ rowTermMap rs M n q
    rw [ι_transitionTerm_assoc, ι_rowTermMap, ι_rowTermMap]
    have hfrac : scalar M (positionProduct rs J ^ (m - n)) ≫
        ringFractionTensor M (product R rs (selection rs q J)) m =
        ringFractionTensor M (product R rs (selection rs q J)) n := by
      unfold ringFractionTensor
      rw [← Category.assoc, ← selection_product, fraction_transition M _ f.le]
    exact congrArg (fun g => g ≫ (Cech.summandι rs q (selection rs q J) ▷ M)) hfrac


open private precomposeCofanIsColimit from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.AugmentedCechComplex

private def rowCofanIsColimit (rs : List R) (M : Coeff R) (q : ℤ) :
    IsColimit (Cofan.mk (((rowFunctor (CechComplex rs)).obj M).X q) (rowInclusion rs M q)) := by
  let t := tensorRight M
  let c := Cofan.mk (t.obj ((CechComplex rs).X q)) (fun s => t.map (Cech.summandι rs q s))
  exact precomposeCofanIsColimit c
    (isColimitCofanMkObjOfIsColimit t _ _ (Cech.summandCofanIsColimit rs q))
    (fun s => localizationTensorIso M (product R rs s))

private def evalRowCoconeIsColimit (rs : List R) (M : Coeff R) (q : ℤ) :
    IsColimit ((HomologicalComplex.eval (Coeff R) upZ q).mapCocone (rowCocone rs M)) := by
  let F := diagram rs M ⋙ HomologicalComplex.eval (Coeff R) upZ q
  let leg (s : Selection rs.length q) :=
    Sigma.ι (fun _ : Positions rs.length q => M) (Cech.selectionEquiv rs.length q s)
  let app (t : Cocone F) (n : ℕ) : term rs M q ⟶ t.pt := t.ι.app n
  have hApp (t : Cocone F) {n m : ℕ} (f : n ⟶ m) :
      transitionTerm rs M n m q ≫ app t m = app t n := t.w f
  let D (t : Cocone F) (s : Selection rs.length q) :
      Cocone (scalarDiagram M (product R rs s)) :=
    { pt := t.pt
      ι.app n := leg s ≫ app t n
      ι.naturality {n m} f := by
        change scalar M (product R rs s ^ (m-n)) ≫ leg s ≫ app t m =
          (leg s ≫ app t n) ≫ 𝟙 t.pt
        rw [Category.comp_id, ← hApp t f]
        change _ = leg s ≫ transitionTerm rs M n m q ≫ t.ι.app m
        dsimp only [leg]
        rw [ι_transitionTerm_assoc]
        congr 2
        have h := selection_product rs q (Cech.selectionEquiv rs.length q s)
        rw [selection, Equiv.symm_apply_apply] at h
        rw [h] }
  let L (s : Selection rs.length q) := fractionCoconeIsColimit M (product R rs s)
  let H := rowCofanIsColimit rs M q
  have hleg (n : ℕ) (s : Selection rs.length q) :
      leg s ≫ rowTermMap rs M n q = fraction M (product R rs s) n ≫ rowInclusion rs M q s := by
    dsimp only [leg]
    rw [rowTermMap, Sigma.ι_comp_desc, selection, Equiv.symm_apply_apply]
  have hdesc (t : Cocone F) (s : Selection rs.length q) :
      rowInclusion rs M q s ≫ Cofan.IsColimit.desc H (fun s => (L s).desc (D t s)) =
        (L s).desc (D t s) := Cofan.IsColimit.fac H _ s
  refine
    { desc t := Cofan.IsColimit.desc H (fun s => (L s).desc (D t s))
      fac t n := by
        apply Sigma.hom_ext
        intro J
        obtain ⟨s, rfl⟩ := (Cech.selectionEquiv rs.length q).surjective J
        change leg s ≫ rowTermMap rs M n q ≫ _ = leg s ≫ app t n
        rw [← Category.assoc, hleg, Category.assoc, hdesc]
        exact (L s).fac (D t s) n
      uniq t g hg := by
        apply Cofan.IsColimit.hom_ext H
        intro s
        change rowInclusion rs M q s ≫ g =
          rowInclusion rs M q s ≫ Cofan.IsColimit.desc H (fun s => (L s).desc (D t s))
        rw [hdesc]
        apply (L s).hom_ext
        intro n
        rw [IsColimit.fac]
        change fraction M (product R rs s) n ≫ rowInclusion rs M q s ≫ g = leg s ≫ app t n
        rw [← Category.assoc, ← hleg, Category.assoc]
        have hh : rowTermMap rs M n q ≫ g = app t n := hg n
        exact congrArg (fun z => leg s ≫ z) hh }

/-- The canonical maps from the Koszul stages into the augmented Čech complex. -/
def cechCocone (rs : List R) (M : Coeff R) : Cocone (diagram rs M) where
  pt := cechCoefficients rs M
  ι := (rowCocone rs M).ι ≫ (Functor.const ℕ).map ((rowIso (CechComplex rs)).hom.app M)

/-- The Čech complex with module coefficients is the colimit of the Koszul tower. -/
def cechIsColimit (rs : List R) (M : Coeff R) : IsColimit (cechCocone rs M) :=
  IsColimit.ofIsoColimit
    (HomologicalComplex.isColimitOfEval _ (rowCocone rs M) (evalRowCoconeIsColimit rs M))
    (Cocone.ext ((rowIso (CechComplex rs)).app M) (fun _ => rfl))


private def topFold (rs : List R) (M : Coeff R) (q : ℤ) : term rs M q ⟶ M :=
  Sigma.desc (fun _ => 𝟙 M)

@[reassoc (attr := simp)]
private theorem ι_topFold (rs : List R) (M : Coeff R) (q : ℤ) (J : Positions rs.length q) :
    Sigma.ι (fun _ : Positions rs.length q => M) J ≫ topFold rs M q = 𝟙 M :=
  Sigma.ι_comp_desc _ _

omit [CommRing R] in
private theorem topPositions_eq_univ (rs : List R) (q : ℤ) (hq : q = rs.length)
    (J : Positions rs.length q) : J.val = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Fintype.card_fin]
  exact Int.ofNat_inj.mp (J.property.trans hq)

omit [CommRing R] in
private theorem exists_missing (rs : List R) (q : ℤ) (hq : q + 1 = rs.length)
    (J : Positions rs.length q) : ∃ a, a ∉ J.val := by
  by_contra! h
  have hh : J.val = Finset.univ := Finset.eq_univ_of_forall h
  have hc := J.property
  rw [hh, Finset.card_univ, Fintype.card_fin] at hc
  omega

private theorem topDifferential_column (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ)
    (hq : q + 1 = rs.length) (J : Positions rs.length q) (a : Fin rs.length) (ha : a ∉ J.val) :
    Sigma.ι (fun _ : Positions rs.length q => M) J ≫
      (stage rs M n).d q (q+1) ≫ topFold rs M (q+1) =
      (countBefore J.val a).negOnePow • scalar M (rs.get a ^ (n+1)) := by
  rw [stage_d, ι_differential_assoc, Preadditive.sum_comp, Finset.sum_eq_single a]
  · simp only [component, dite_eq_left ha]
    rw [show ∀ (f : M ⟶ term rs M (q+1)) (z : ℤˣ),
        (z • f) ≫ topFold rs M (q+1) = z • (f ≫ topFold rs M (q+1)) from
      fun f z => Preadditive.zsmul_comp f _ z, Category.assoc, ι_topFold, Category.comp_id]
  · intro b _ hb
    have ht := topPositions_eq_univ rs (q+1) hq (insertPosition J a ha)
    have hm : b ∈ J.val := by
      have : b ∈ (insertPosition J a ha).val := by rw [ht]; exact Finset.mem_univ b
      exact (Finset.mem_insert.mp this).resolve_left hb
    simp [component, hm]
  · simp

private theorem topDifferential_range (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ)
    (hq : q + 1 = rs.length) :
    (((stage rs M n).d q (q+1)) ≫ topFold rs M (q+1)).hom.range = powersSubmodule rs M n := by
  let D := (stage rs M n).d q (q+1) ≫ topFold rs M (q+1)
  apply le_antisymm
  · rw [← Submodule.ker_mkQ (powersSubmodule rs M n), LinearMap.range_le_ker_iff]
    change (D ≫ quotientProjection rs M n).hom =
      (0 : (stage rs M n).X q ⟶ QuotientTerm rs M n).hom
    apply ModuleCat.hom_ext_iff.mp
    apply Sigma.hom_ext
    intro J
    obtain ⟨a, ha⟩ := exists_missing rs q hq J
    have hcol : Sigma.ι (fun _ : Positions rs.length q => M) J ≫ D =
        (countBefore J.val a).negOnePow • scalar M (rs.get a ^ (n+1)) :=
      topDifferential_column rs M n q hq J a ha
    rw [← Category.assoc, hcol, Limits.comp_zero]
    have hz : scalar M (rs.get a ^ (n+1)) ≫ quotientProjection rs M n = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (powersSubmodule rs M n).mkQ (rs.get a ^ (n+1) • x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, powersSubmodule_eq_iSup]
      exact Submodule.mem_iSup_of_mem a ⟨x, rfl⟩
    rw [show ∀ (z : ℤˣ), (z • scalar M (rs.get a ^ (n+1))) ≫ quotientProjection rs M n =
        z • (scalar M (rs.get a ^ (n+1)) ≫ quotientProjection rs M n) from
      fun z => Preadditive.zsmul_comp _ _ z, hz, smul_zero]
  · rw [powersSubmodule_eq_iSup]
    apply iSup_le
    intro a x hx
    obtain ⟨y, rfl⟩ := hx
    let J : Positions rs.length q := ⟨Finset.univ.erase a, by
      rw [Finset.cast_card_erase_of_mem (R := ℤ) (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      omega⟩
    have ha : a ∉ J.val := Finset.notMem_erase _ _
    let z := (countBefore J.val a).negOnePow
    have hcol : Sigma.ι (fun _ : Positions rs.length q => M) J ≫ D =
        z • scalar M (rs.get a ^ (n+1)) := topDifferential_column rs M n q hq J a ha
    refine ⟨(Sigma.ι (fun _ : Positions rs.length q => M) J) (z⁻¹ • y), ?_⟩
    have hh := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hcol) (z⁻¹ • y)
    change _ = z • (scalar M (rs.get a ^ (n+1))).hom (z⁻¹ • y) at hh
    rw [show (scalar M (rs.get a ^ (n+1))).hom (z⁻¹ • y) =
        z⁻¹ • (scalar M (rs.get a ^ (n+1))).hom y from map_zsmul _ _ _,
      smul_inv_smul] at hh
    exact hh

local notation "topDegree" rs:arg => (List.length rs : ℤ)

private def stageTopProjection (rs : List R) (M : Coeff R) (n : ℕ) :
    (stage rs M n).X (topDegree rs) ⟶ QuotientTerm rs M n :=
  topFold rs M (topDegree rs) ≫ quotientProjection rs M n

private theorem stageTop_exact (rs : List R) (M : Coeff R) (n : ℕ) :
    Function.Exact ((stage rs M n).d (topDegree rs - 1) (topDegree rs)).hom
      (stageTopProjection rs M n).hom := by
  let D := (stage rs M n).d (topDegree rs - 1) (topDegree rs)
  have hD : (D ≫ topFold rs M (topDegree rs)).hom.range = powersSubmodule rs M n := by
    have hq : topDegree rs - 1 + 1 = topDegree rs := by omega
    have hh := topDifferential_range rs M n (topDegree rs - 1) hq
    rw [hq] at hh
    exact hh
  have hf : Mono (topFold rs M (topDegree rs)) := by
    let J : Positions rs.length (topDegree rs) := ⟨Finset.univ, by simp⟩
    have h : ∀ J' : Positions rs.length (topDegree rs), J' = J :=
      fun J' => Subtype.ext (topPositions_eq_univ rs _ rfl J')
    have hι : topFold rs M (topDegree rs) ≫ Sigma.ι (fun _ : Positions rs.length (topDegree rs) => M) J =
        𝟙 _ := by
      apply Sigma.hom_ext
      intro J'
      rw [h J']
      simp
    exact mono_of_mono_fac hι
  have hi := (ModuleCat.mono_iff_injective (topFold rs M (topDegree rs))).mp hf
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    change (powersSubmodule rs M n).mkQ ((topFold rs M _).hom x) = 0 at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← hD] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hi hy⟩
  · rintro ⟨y, rfl⟩
    change (powersSubmodule rs M n).mkQ ((D ≫ topFold rs M _).hom y) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← hD]
    exact LinearMap.mem_range_self _ _

instance (rs : List R) (M : Coeff R) (n : ℕ) : Epi (stageTopProjection rs M n) := by
  have h : Epi (topFold rs M (topDegree rs)) := by
    let J : Positions rs.length (topDegree rs) := ⟨Finset.univ, by simp⟩
    exact epi_of_epi_fac (ι_topFold rs M _ J)
  unfold stageTopProjection
  infer_instance

private theorem stageTop_condition (rs : List R) (M : Coeff R) (n : ℕ) :
    (stage rs M n).d (topDegree rs - 1) (topDegree rs) ≫ stageTopProjection rs M n = 0 :=
  ModuleCat.hom_ext (LinearMap.ext (stageTop_exact rs M n).apply_apply_eq_zero)

private def stageTopIsCokernel (rs : List R) (M : Coeff R) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (stageTopProjection rs M n) (stageTop_condition rs M n)) :=
  ModuleCat.isColimitCokernelCofork _ _ (stageTop_exact rs M n)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

private theorem stageTop_comm (rs : List R) (M : Coeff R) {n m : ℕ} (h : n ≤ m) :
    (transition rs M h).f (topDegree rs) ≫ stageTopProjection rs M m =
      stageTopProjection rs M n ≫ quotientTransition rs M h := by
  apply Sigma.hom_ext
  intro J
  change Sigma.ι (fun _ : Positions rs.length (topDegree rs) => M) J ≫
    transitionTerm rs M n m (topDegree rs) ≫ stageTopProjection rs M m =
    Sigma.ι (fun _ : Positions rs.length (topDegree rs) => M) J ≫
      stageTopProjection rs M n ≫ quotientTransition rs M h
  have hprod : positionProduct rs J = totalProduct rs := by
    unfold positionProduct totalProduct
    rw [topPositions_eq_univ rs _ rfl J]
  simp only [ι_transitionTerm_assoc, stageTopProjection, Category.assoc, ι_topFold_assoc,
    hprod, quotientProjection_transition]


private theorem up_next (q : ℤ) : (upZ).next q = q + 1 :=
  (upZ).next_eq' (show (upZ).Rel q (q+1) from rfl)

private theorem up_prev (q : ℤ) : (upZ).prev q = q - 1 :=
  (upZ).prev_eq' (show (q-1)+1 = q by omega)

private def topHomologyProjection (K : Complex R) (q : ℤ) (h : K.d q (q+1) = 0) :
    K.X q ⟶ K.homology q :=
  K.pOpcycles q ≫ (K.isoHomologyι q (q+1) (up_next q) h).inv

private theorem topHomology_condition (K : Complex R) (q : ℤ) (h : K.d q (q+1) = 0) :
    K.d (q-1) q ≫ topHomologyProjection K q h = 0 := by
  simp [topHomologyProjection]

private def topHomologyIsCokernel (K : Complex R) (q : ℤ) (h : K.d q (q+1) = 0) :
    IsColimit (CokernelCofork.ofπ (topHomologyProjection K q h) (topHomology_condition K q h)) :=
  IsColimit.ofIsoColimit (K.opcyclesIsCokernel (i := q-1) (j := q) (up_prev q))
    (Cocone.ext (K.isoHomologyι q (q+1) (up_next q) h).symm (by
      rintro (_ | _)
      · simp [topHomology_condition]
      · rfl))

private theorem topHomologyProjection_naturality {K L : Complex R} (f : K ⟶ L) (q : ℤ)
    (hK : K.d q (q+1) = 0) (hL : L.d q (q+1) = 0) :
    topHomologyProjection K q hK ≫ HomologicalComplex.homologyMap f q =
      f.f q ≫ topHomologyProjection L q hL := by
  let := L.isIso_homologyι q (q+1) (up_next q) hL
  apply (cancel_mono (L.homologyι q)).mp
  simp [topHomologyProjection]

private abbrev cechModuleFunctor (rs : List R) : Coeff R ⥤ Complex R :=
  HomologicalComplex.single (Coeff R) upZ 0 ⋙ cechTensorFunctor rs

private theorem cechTop_zero (rs : List R) (M : Coeff R) :
    (cechCoefficients rs M).d (topDegree rs) (topDegree rs + 1) = 0 := by
  have hz := (tensorRight M).map_isZero
    (Cech.isZero_X rs (topDegree rs + 1) (.inr (by omega)))
  let e := (HomologicalComplex.eval (Coeff R) upZ (topDegree rs + 1)).mapIso
    ((rowIso (CechComplex rs)).app M)
  exact (hz.of_iso e.symm).eq_of_tgt _ _

private def cechTopProjection (rs : List R) (M : Coeff R) :
    (cechCoefficients rs M).X (topDegree rs) ⟶ (cechCoefficients rs M).homology (topDegree rs) :=
  topHomologyProjection _ _ (cechTop_zero rs M)

private abbrev cechLeg (rs : List R) (M : Coeff R) (n : ℕ) :
    stage rs M n ⟶ cechCoefficients rs M := (cechCocone rs M).ι.app n

private def topLeg (rs : List R) (M : Coeff R) (n : ℕ) :
    QuotientTerm rs M n ⟶ (cechCoefficients rs M).homology (topDegree rs) :=
  (CokernelCofork.IsColimit.desc' (stageTopIsCokernel rs M n)
    ((cechLeg rs M n).f (topDegree rs) ≫ cechTopProjection rs M)
    (by
      have hf := (cechLeg rs M n).comm (topDegree rs - 1) (topDegree rs)
      change _ ≫ _ ≫ topHomologyProjection _ _ (cechTop_zero rs M) = _
      rw [← Category.assoc, ← hf, Category.assoc, topHomology_condition, comp_zero])).val

@[reassoc (attr := simp)]
private theorem stageTopProjection_topLeg (rs : List R) (M : Coeff R) (n : ℕ) :
    stageTopProjection rs M n ≫ topLeg rs M n =
      (cechLeg rs M n).f (topDegree rs) ≫ cechTopProjection rs M :=
  (CokernelCofork.IsColimit.desc' (stageTopIsCokernel rs M n) _ _).property

private def topCocone (rs : List R) (M : Coeff R) : Cocone (quotientDiagram rs M) where
  pt := (cechCoefficients rs M).homology (topDegree rs)
  ι.app := topLeg rs M
  ι.naturality {n m} f := by
    change quotientTransition rs M f.le ≫ topLeg rs M m = topLeg rs M n ≫ 𝟙 _
    rw [Category.comp_id]
    apply (cancel_epi (stageTopProjection rs M n)).mp
    rw [← Category.assoc, ← stageTop_comm, Category.assoc,
      stageTopProjection_topLeg, stageTopProjection_topLeg, ← Category.assoc]
    have hh := congrArg (fun z : (stage rs M n) ⟶ cechCoefficients rs M => z.f (topDegree rs))
      ((cechCocone rs M).w f)
    exact congrArg (fun z => z ≫ cechTopProjection rs M) hh

private def evalCechIsColimit (rs : List R) (M : Coeff R) (q : ℤ) :
    IsColimit ((HomologicalComplex.eval (Coeff R) upZ q).mapCocone (cechCocone rs M)) :=
  isColimitOfPreserves _ (cechIsColimit rs M)

private def topCoconeIsColimit (rs : List R) (M : Coeff R) :
    IsColimit (topCocone rs M) := by
  let K := cechCoefficients rs M
  let q : ℤ := topDegree rs
  let H (i : ℤ) := evalCechIsColimit rs M i
  let B := topHomologyIsCokernel K q (cechTop_zero rs M)
  let T (s : Cocone (quotientDiagram rs M)) :
      Cocone (diagram rs M ⋙ HomologicalComplex.eval (Coeff R) upZ q) :=
    { pt := s.pt
      ι.app n := stageTopProjection rs M n ≫ s.ι.app n
      ι.naturality {n m} f := by
        change (transition rs M f.le).f q ≫ stageTopProjection rs M m ≫ s.ι.app m =
          (stageTopProjection rs M n ≫ s.ι.app n) ≫ 𝟙 _
        have hw : quotientTransition rs M f.le ≫ s.ι.app m = s.ι.app n := s.w f
        rw [Category.comp_id, ← Category.assoc, stageTop_comm, Category.assoc, hw] }
  have ht (s : Cocone (quotientDiagram rs M)) :
      K.d (q-1) q ≫ (H q).desc (T s) = 0 := by
    apply (H (q-1)).hom_ext
    intro n
    change (cechLeg rs M n).f (q-1) ≫ K.d (q-1) q ≫ (H q).desc (T s) = _
    have hf := (cechLeg rs M n).comm (q-1) q
    change (cechLeg rs M n).f (q-1) ≫ K.d (q-1) q =
      (stage rs M n).d (q-1) q ≫ (cechLeg rs M n).f q at hf
    rw [← Category.assoc, hf, Category.assoc]
    have hh : (cechLeg rs M n).f q ≫ (H q).desc (T s) =
        stageTopProjection rs M n ≫ s.ι.app n := (H q).fac (T s) n
    rw [hh, ← Category.assoc, stageTop_condition, zero_comp, comp_zero]
  let desc (s : Cocone (quotientDiagram rs M)) :=
    CokernelCofork.IsColimit.desc' B ((H q).desc (T s)) (ht s)
  have hdesc (s : Cocone (quotientDiagram rs M)) :
      cechTopProjection rs M ≫ (desc s).val = (H q).desc (T s) := (desc s).property
  refine
    { desc s := (desc s).val
      fac s n := by
        change topLeg rs M n ≫ (desc s).val = s.ι.app n
        apply (cancel_epi (stageTopProjection rs M n)).mp
        rw [stageTopProjection_topLeg_assoc, hdesc]
        exact (H q).fac (T s) n
      uniq s g hg := by
        have : Epi (cechTopProjection rs M) := by
          unfold cechTopProjection topHomologyProjection
          infer_instance
        apply (cancel_epi (cechTopProjection rs M)).mp
        rw [hdesc]
        apply (H q).hom_ext
        intro n
        change (cechLeg rs M n).f q ≫ cechTopProjection rs M ≫ g =
          (cechLeg rs M n).f q ≫ (H q).desc (T s)
        rw [← stageTopProjection_topLeg_assoc]
        have hh : topLeg rs M n ≫ g = s.ι.app n := hg n
        rw [hh]
        exact ((H q).fac (T s) n).symm }


private theorem ringFractionTensor_naturality {M N : Coeff R} (f : M ⟶ N) (p : R) (n : ℕ) :
    ringFractionTensor M p n ≫ (ModuleCat.of R (Localization.Away p) ◁ f) =
      f ≫ ringFractionTensor N p n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (ModuleCat.of R (Localization.Away p) ◁ f) (ringFractionTensor M p n x) =
    ringFractionTensor N p n (f x)
  rw [ringFractionTensor_apply, ringFractionTensor_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]

private theorem topLeg_naturality (rs : List R) {M N : Coeff R} (f : M ⟶ N) (n : ℕ) :
    quotientMap rs f n ≫ topLeg rs N n =
      topLeg rs M n ≫ HomologicalComplex.homologyMap ((cechModuleFunctor rs).map f) (topDegree rs) := by
  apply (cancel_epi (quotientProjection rs M n)).mp
  let q : ℤ := topDegree rs
  let J : Positions rs.length q := ⟨Finset.univ, by simp [q]⟩
  let includeM (M : Coeff R) := Sigma.ι (fun _ : Positions rs.length q => M) J
  have hπ (M : Coeff R) : includeM M ≫ stageTopProjection rs M n = quotientProjection rs M n := by
    change Sigma.ι (fun _ : Positions rs.length q => M) J ≫
      topFold rs M q ≫ quotientProjection rs M n = quotientProjection rs M n
    rw [ι_topFold_assoc]
  have hleg (M : Coeff R) : quotientProjection rs M n ≫ topLeg rs M n =
      includeM M ≫ (cechLeg rs M n).f q ≫ cechTopProjection rs M := by
    rw [← hπ, Category.assoc, stageTopProjection_topLeg]
  rw [quotientProjection_map_assoc, hleg N,
    ← Category.assoc (quotientProjection rs M n), hleg M]
  simp only [Category.assoc]
  have hH : cechTopProjection rs M ≫
      HomologicalComplex.homologyMap ((cechModuleFunctor rs).map f) q =
      ((cechModuleFunctor rs).map f).f q ≫ cechTopProjection rs N :=
    topHomologyProjection_naturality _ _ (cechTop_zero rs M) (cechTop_zero rs N)
  rw [hH]
  have hc : f ≫ includeM N ≫ (cechLeg rs N n).f q =
      includeM M ≫ (cechLeg rs M n).f q ≫ ((cechModuleFunctor rs).map f).f q := by
    let F := CechComplex rs
    let e := rowIso F
    have hn := congrArg (fun g : (rowFunctor F).obj M ⟶ cechCoefficients rs N => g.f q)
      (e.hom.naturality f)
    change (F.X q ◁ f) ≫ (e.hom.app N).f q =
      (e.hom.app M).f q ≫ ((cechModuleFunctor rs).map f).f q at hn
    change f ≫ includeM N ≫ rowTermMap rs N n q ≫ (e.hom.app N).f q =
      includeM M ≫ (rowTermMap rs M n q ≫ (e.hom.app M).f q) ≫ ((cechModuleFunctor rs).map f).f q
    simp only [includeM, ι_rowTermMap_assoc, Category.assoc, ← hn]
    let s := selection rs q J
    change f ≫ ringFractionTensor N (product R rs s) n ≫
      (Cech.summandι rs q s ▷ N) ≫ (e.hom.app N).f q =
      ringFractionTensor M (product R rs s) n ≫
        (Cech.summandι rs q s ▷ M) ≫ (F.X q ◁ f) ≫ (e.hom.app N).f q
    rw [← Category.assoc (Cech.summandι rs q s ▷ M), ← whisker_exchange,
      Category.assoc, ← Category.assoc (ringFractionTensor M _ _), ringFractionTensor_naturality,
      Category.assoc]
  simpa only [Category.assoc] using congrArg (fun g => g ≫ cechTopProjection rs N) hc

private def cechTopQuotientIso (rs : List R) :
    quotientColimit rs ≅ cechModuleFunctor rs ⋙
      HomologicalComplex.homologyFunctor (Coeff R) upZ (topDegree rs) :=
  NatIso.ofComponents
    (fun M => (colimit.isColimit (quotientDiagram rs M)).coconePointUniqueUpToIso
      (topCoconeIsColimit rs M))
    (fun {M N} f => by
      apply colimit.hom_ext
      intro n
      change colimit.ι (quotientDiagram rs M) n ≫ colimMap (quotientDiagramMap rs f) ≫ _ =
        colimit.ι (quotientDiagram rs M) n ≫ _ ≫
          HomologicalComplex.homologyMap ((cechModuleFunctor rs).map f) (topDegree rs)
      rw [ι_colimMap_assoc]
      have hι (P : Coeff R) :
          colimit.ι (quotientDiagram rs P) n ≫
            ((colimit.isColimit (quotientDiagram rs P)).coconePointUniqueUpToIso
              (topCoconeIsColimit rs P)).hom = topLeg rs P n :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n
      rw [hι N, ← Category.assoc, hι M]
      exact topLeg_naturality rs f n)

/-- In top degree the natural Čech computation is the colimit of the quotients
by the powers of the listed generators. -/
theorem localCohomologyComparison : TopComparison.{u} := by
  intro R _ _ I rs hI
  obtain ⟨e⟩ := localCohomologyCechComparison I rs hI (topDegree rs)
  exact ⟨e ≪≫ (cechTopQuotientIso rs).symm⟩


/-- The colimit legs are the localization fractions in the ordered-subset coordinates. -/
theorem cechColimitComparison : CechColimitComparison.{u} := by
  intro R _ rs
  refine ⟨Cech.selectionEquiv rs.length, Cech.summandι rs, (fun _ _ => rfl),
    (fun q s => ?_), (fun q => ⟨Cech.summandCofanIsColimit rs q⟩), ?_⟩
  · have h := selection_product rs q (Cech.selectionEquiv rs.length q s)
    rwa [selection, Equiv.symm_apply_apply] at h
  intro M
  refine ⟨(cechCocone rs M).ι, ⟨cechIsColimit rs M⟩, ?_⟩
  intro n q s
  change Sigma.ι (fun _ : Positions rs.length q => M) (Cech.selectionEquiv rs.length q s) ≫
    rowTermMap rs M n q ≫ ((rowIso (CechComplex rs)).hom.app M).f q = _
  rw [ι_rowTermMap_assoc, selection, Equiv.symm_apply_apply]
  simp only [ringFractionTensor, Category.assoc]
  rfl

private theorem stageTop_zero (rs : List R) (M : Coeff R) (n : ℕ) :
    (stage rs M n).d (topDegree rs) (topDegree rs + 1) = 0 := by
  apply Sigma.hom_ext
  intro J
  rw [stage_d, ι_differential, Limits.comp_zero]
  apply Finset.sum_eq_zero
  intro a _
  have ha : a ∈ J.val := by
    rw [topPositions_eq_univ rs _ rfl J]
    exact Finset.mem_univ _
  simp [component, ha]

private def stageTopIso (rs : List R) (M : Coeff R) (n : ℕ) :
    (stage rs M n).homology (topDegree rs) ≅ QuotientTerm rs M n :=
  (topHomologyIsCokernel _ _ (stageTop_zero rs M n)).coconePointUniqueUpToIso (stageTopIsCokernel rs M n)

private theorem stageTopIso_fac (rs : List R) (M : Coeff R) (n : ℕ) :
    topHomologyProjection (stage rs M n) (topDegree rs) (stageTop_zero rs M n) ≫
      (stageTopIso rs M n).hom = stageTopProjection rs M n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (topHomologyIsCokernel _ _ (stageTop_zero rs M n)) (stageTopIsCokernel rs M n)
    WalkingParallelPair.one

/-- In top degree the stage homology maps identify with the stated quotient tower. -/
theorem stageTopComparison : StageTopComparison.{u} := by
  intro R _ rs M
  refine ⟨NatIso.ofComponents (stageTopIso rs M) ?_⟩
  intro n m f
  let p := topHomologyProjection (stage rs M n) (topDegree rs) (stageTop_zero rs M n)
  have : Epi p := by
    dsimp [p, topHomologyProjection]
    infer_instance
  apply (cancel_epi p).mp
  change p ≫ HomologicalComplex.homologyMap (transition rs M f.le) (topDegree rs) ≫
    (stageTopIso rs M m).hom = p ≫ (stageTopIso rs M n).hom ≫ quotientTransition rs M f.le
  have hnat : p ≫ HomologicalComplex.homologyMap (transition rs M f.le) (topDegree rs) =
      (transition rs M f.le).f (topDegree rs) ≫
        topHomologyProjection (stage rs M m) (topDegree rs) (stageTop_zero rs M m) :=
    topHomologyProjection_naturality _ _ _ _
  rw [← Category.assoc, hnat, Category.assoc, stageTopIso_fac, ← Category.assoc p]
  change _ = (topHomologyProjection _ _ (stageTop_zero rs M n) ≫ (stageTopIso rs M n).hom) ≫ _
  rw [stageTopIso_fac]
  exact stageTop_comm rs M f.le

end
end CommutativeAlgebraNotes.KoszulTower
