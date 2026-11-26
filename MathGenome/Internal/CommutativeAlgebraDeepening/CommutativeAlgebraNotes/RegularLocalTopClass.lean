import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularLocalTopClass
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.KoszulTower
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.ProductsAndPowers

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open RingTheory.Sequence
open scoped Pointwise

namespace CommutativeAlgebraNotes.RegularLocalTopClass

universe u

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Specs.CommutativeAlgebraNotes.KoszulTower
open Specs.CommutativeAlgebraNotes.RegularLocalTopClass

private theorem ideal_smul_top {R : Type u} [CommRing R] (I : Ideal R) :
    I • (⊤ : Submodule R R) = I := Ideal.mul_top I

private theorem mapIdx_const {R S : Type*} (f : R → S) (rs : List R) :
    rs.mapIdx (fun _ x => f x) = rs.map f := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [List.mapIdx_cons, List.map_cons, ih]

/-- Cancel a power of the parameter product against powers one degree higher. -/
private theorem mem_of_product_pow_mul_mem (n k : ℕ) :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (rs : List R), rs.length = k → IsRegular R rs →
      ∀ z : R, rs.prod ^ n * z ∈ Ideal.ofList (rs.map (· ^ (n + 1))) →
        z ∈ Ideal.ofList rs := by
  induction k with
  | zero =>
    intro R _ _ _ rs hlen _ z hz
    have hr : rs = [] := List.length_eq_zero_iff.mp hlen
    simpa [hr] using hz
  | succ k ih =>
    intro R _ _ _ rs hlen hreg z hz
    cases rs with
    | nil => simp at hlen
    | cons x xs =>
      have hlen' : xs.length = k := by simpa using hlen
      let J : Ideal R := Ideal.ofList (xs.map (· ^ (n + 1)))
      let I : Ideal R := Ideal.span {x}
      have hp := AdvCommAlg.RegularSequence.regular_powers R (xs ++ [x])
        (fun i => if i < xs.length then n + 1 else 1)
        (by intro i _; split <;> omega)
        (IsLocalRing.isRegular_of_perm hreg (by simpa using List.perm_append_comm (l₁ := [x]) (l₂ := xs)))
      have hmap : xs.mapIdx (fun i a => a ^ (if i < xs.length then n + 1 else 1)) =
          xs.map (· ^ (n + 1)) := by
        rw [← mapIdx_const]
        exact List.mapIdx_eq_mapIdx_iff.mpr fun i hi => by simp [hi]
      rw [List.mapIdx_append, hmap, List.mapIdx_singleton] at hp
      simp only [Nat.zero_add, lt_self_iff_false, ite_false, pow_one] at hp
      have hx := ((isWeaklyRegular_append_iff R
        (xs.map (· ^ (n + 1))) [x]).mp hp.toIsWeaklyRegular).2
      rw [isWeaklyRegular_singleton_iff, ideal_smul_top] at hx
      change IsSMulRegular (R ⧸ J) x at hx
      rw [List.map_cons, Ideal.ofList_cons, List.prod_cons, mul_pow, mul_assoc] at hz
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      have hc : x ^ n * (xs.prod ^ n * z - x * c) ∈ J := by
        have he : x ^ n * (xs.prod ^ n * z - x * c) = b := by
          rw [mul_sub, ← mul_assoc (x ^ n) x c, ← pow_succ, ← hab, add_sub_cancel_left]
        exact he ▸ hb
      have hc' : xs.prod ^ n * z - x * c ∈ J := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        apply (hx.pow n)
        change Ideal.Quotient.mk J (x ^ n * (xs.prod ^ n * z - x * c)) = x ^ n • 0
        rw [smul_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem).mpr hc
      have htail : IsRegular (R ⧸ I) (xs.map (Ideal.Quotient.mk I)) := by
        have h := ((isRegular_cons_iff R x xs).mp hreg).2
        have he : (x • (⊤ : Submodule R R)) = I := by
          rw [← Submodule.ideal_span_singleton_smul, ideal_smul_top]
        let e : QuotSMulTop x R ≃ₗ[R] (R ⧸ I) := Submodule.quotEquivOfEq _ _ he
        apply (e.toAddEquiv.isRegular_congr ?_).mp h
        apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro a _ m
        exact (e.map_smul a m).trans (algebraMap_smul (R ⧸ I) a (e m)).symm
      let : Nontrivial (R ⧸ I) := htail.nontrivial
      let : IsLocalRing (R ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      have hmod : Ideal.Quotient.mk I (xs.prod ^ n * z) ∈ J.map (Ideal.Quotient.mk I) := by
        have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hc'
        have hx0 : Ideal.Quotient.mk I x = 0 :=
          (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
        simpa [map_sub, map_mul, hx0] using hm
      have hpow : (xs.map (· ^ (n + 1))).map (Ideal.Quotient.mk I) =
          (xs.map (Ideal.Quotient.mk I)).map (· ^ (n + 1)) := by simp [List.map_map, Function.comp_def]
      have hmod' : (xs.map (Ideal.Quotient.mk I)).prod ^ n * Ideal.Quotient.mk I z ∈
          Ideal.ofList ((xs.map (Ideal.Quotient.mk I)).map (· ^ (n + 1))) := by
        simpa only [J, Ideal.map_ofList, hpow, map_mul, map_pow, map_list_prod] using hmod
      have h := ih (xs.map (Ideal.Quotient.mk I)) (by simpa using hlen') htail _ hmod'
      rw [← Ideal.map_ofList, Ideal.mem_quotient_iff_mem_sup] at h
      simpa only [Ideal.ofList_cons, I, sup_comm] using h

open Specs.CommutativeAlgebraNotes.AugmentedCechComplex (Selection product selected coefficients)
open private stageTopProjection ι_topFold
  topLeg stageTopProjection_topLeg topCocone topCoconeIsColimit
  cechTop_zero cechTopProjection selection rowTermMap ι_rowTermMap_assoc ringFractionTensor
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.KoszulTower
open private rowIso from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison

variable {R : Type u} [CommRing R]

private theorem powersSubmodule_self (rs : List R) (n : ℕ) :
    powersSubmodule rs (ModuleCat.of R R) n = Ideal.ofList (rs.map (· ^ (n + 1))) := by
  rw [powersSubmodule, ideal_smul_top]
  apply congrArg Ideal.span
  ext x
  change (∃ i : Fin rs.length, rs.get i ^ (n + 1) = x) ↔ x ∈ rs.map (· ^ (n + 1))
  rw [List.mem_map]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨rs.get i, List.get_mem _ _, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨i, rfl⟩

private theorem firstClass_ne_zero [IsLocalRing R] [IsNoetherianRing R] (rs : List R)
    (hreg : IsRegular R rs) :
    topLeg rs (ModuleCat.of R R) 0 (quotientProjection rs (ModuleCat.of R R) 0 (1 : R)) ≠ 0 := by
  let M := ModuleCat.of R R
  let F := quotientDiagram rs M
  let c := topCocone rs M
  let : PreservesFilteredColimitsOfSize.{0,0} (CategoryTheory.forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits.{u,u} _
  let hc := isColimitOfPreserves (CategoryTheory.forget (ModuleCat.{u} R)) (topCoconeIsColimit rs M)
  let a : F.obj 0 := quotientProjection rs M 0 (1 : R)
  intro h
  have he : ((CategoryTheory.forget (ModuleCat.{u} R)).mapCocone c).ι.app 0 a =
      ((CategoryTheory.forget (ModuleCat.{u} R)).mapCocone c).ι.app 0 0 := by
    change topLeg rs M 0 a = topLeg rs M 0 0
    rw [map_zero]
    exact h
  obtain ⟨n, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc a 0).mp he
  change quotientTransition rs M f.le a = quotientTransition rs M f.le 0 at hf
  rw [map_zero] at hf
  have hmap := congrArg (fun g : M ⟶ F.obj n => g (1 : R))
    (quotientProjection_transition rs M f.le)
  change quotientTransition rs M f.le a =
    quotientProjection rs M n ((totalProduct rs ^ (n - 0)) • (1 : R)) at hmap
  rw [Nat.sub_zero, smul_eq_mul, mul_one] at hmap
  have hz : (Submodule.Quotient.mk (totalProduct rs ^ n) : QuotientTerm rs M n) = 0 :=
    hmap.symm.trans hf
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  change totalProduct rs ^ n ∈ powersSubmodule rs (ModuleCat.of R R) n at hm
  have hprod : totalProduct rs = rs.prod := Fin.prod_univ_getElem rs
  rw [powersSubmodule_self, hprod] at hm
  have hone : (1 : R) ∈ Ideal.ofList rs :=
    mem_of_product_pow_mul_mem n rs.length rs rfl hreg 1 (by simpa using hm)
  exact hreg.top_ne_smul (by rw [ideal_smul_top, Ideal.eq_top_of_isUnit_mem _ hone isUnit_one])

private theorem selected_fullSelection (n : ℕ) (q : ℤ) (h : q = n) (i : Fin n) :
    selected (fullSelection n q h) i = true := by
  induction n generalizing q with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih _ _ _

private theorem topLocalizationInclusion_eq (rs : List R) (q : ℤ) (h : q = rs.length) :
    topLocalizationInclusion rs q h = Cech.summandι rs q (fullSelection rs.length q h) := by
  induction rs generalizing q with
  | nil => rfl
  | cons r rs ih =>
    rw [topLocalizationInclusion, ih]
    rfl

private theorem fractionClass_eq_firstClass (rs : List R) :
    cechFractionClass rs (cechTop_zero rs (ModuleCat.of R R)) =
      topLeg rs (ModuleCat.of R R) 0 (quotientProjection rs (ModuleCat.of R R) 0 (1 : R)) := by
  let M := ModuleCat.of R R
  let q : ℤ := rs.length
  let J : Positions rs.length q := ⟨Finset.univ, by simp [q]⟩
  let s : Selection rs.length q := fullSelection rs.length q rfl
  have hs : selection rs q J = s := by
    apply (Cech.selectionEquiv rs.length q).injective
    rw [show (Cech.selectionEquiv rs.length q) (selection rs q J) = J from
      (Cech.selectionEquiv rs.length q).apply_symm_apply J]
    apply Subtype.ext
    change Finset.univ = Finset.univ.filter (fun i => selected s i = true)
    simp [s, selected_fullSelection]
  have hstage : Sigma.ι (fun _ : Positions rs.length q => M) J ≫
      stageTopProjection rs M 0 = quotientProjection rs M 0 := by
    change Sigma.ι (fun _ : Positions rs.length q => M) J ≫
      _ ≫ quotientProjection rs M 0 = _
    rw [← Category.assoc, ι_topFold, Category.id_comp]
  have h := calc
    quotientProjection rs M 0 ≫ topLeg rs M 0 =
        Sigma.ι (fun _ : Positions rs.length q => M) J ≫
          ((KoszulTower.cechCocone rs M).ι.app 0).f q ≫ cechTopProjection rs M := by
      rw [← hstage, Category.assoc, stageTopProjection_topLeg]
    _ = fraction M (product R rs s) 0 ≫
        (Specs.CommutativeAlgebraNotes.KoszulTower.localizationTensorIso M (product R rs s)).hom ≫
        (Cech.summandι rs q s ▷ M) ≫
        ιTensorObj (CechComplex rs) ((single (ModuleCat R) (.up ℤ) 0).obj M) q 0 q (add_zero q) ≫
        cechTopProjection rs M := by
      change Sigma.ι (fun _ : Positions rs.length q => M) J ≫
        (rowTermMap rs M 0 q ≫ ((rowIso (CechComplex rs)).hom.app M).f q) ≫ _ = _
      rw [Category.assoc, ι_rowTermMap_assoc, hs]
      simp only [ringFractionTensor, Category.assoc]
      rfl
  rw [← topLocalizationInclusion_eq rs q rfl] at h
  exact (congrArg (fun g : M ⟶ _ => g (1 : R)) h).symm

/-- The top Čech class of the reciprocal of the parameter product is nonzero
in the local cohomology of a regular local ring. -/
theorem topClass_nonzero : TopClassNonzero.{u} := by
  intro R _ _ rs hd hgen
  have hreg : IsRegular R rs :=
    AdvCommAlg.CohenMacaulay.regular_generatingList R rs.length rs hd rfl hgen
  obtain ⟨e⟩ := localCohomologyCechComparison (IsLocalRing.maximalIdeal R) rs hgen (rs.length : ℤ)
  let M := ModuleCat.of R R
  let h := cechTop_zero rs M
  refine ⟨e, h, ?_⟩
  intro hz
  let f : (coefficients R rs M).homology (rs.length : ℤ) ⟶
      (Specs.CommutativeAlgebraNotes.IdealTorsion.localCohomology (IsLocalRing.maximalIdeal R)
        (rs.length : ℤ)).obj M := e.inv.app M
  change f (cechFractionClass rs h) = 0 at hz
  have hinj := (ModuleCat.mono_iff_injective f).mp (by change Mono (e.inv.app M); infer_instance)
  apply firstClass_ne_zero rs hreg
  rw [← fractionClass_eq_firstClass]
  exact hinj (hz.trans f.hom.map_zero.symm)

end

end CommutativeAlgebraNotes.RegularLocalTopClass
