import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.NoncompleteDVRLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.EndomorphismsOfResidueHull
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularAndCompleteIntersection
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Polynomial.Quotient

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex IsLocalRing
open Specs.CommutativeAlgebraNotes.NoncompleteDVRLocalCohomology
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
  (Completion IsPowerTorsion completionModule completionScalarTower scalar)
open AdvCommAlg.Gorenstein
open scoped MonoidalCategory

namespace CommutativeAlgebraNotes

universe u

variable (k : Type u) [Field k]

local notation "T" => LocalLine k
local notation "t" => parameter k
local notation "𝔪" => maximalIdeal T
local notation "K" => RationalFunctions k

private theorem localLine_maximalIdeal : 𝔪 = Ideal.span {t} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (origin k) T]
  exact Ideal.map_span _ _ |>.trans (by simp [parameter])

private theorem localLine_parameter_ne_zero : t ≠ 0 := by
  simpa only [map_zero] using
    (IsLocalization.injective T (origin k).primeCompl_le_nonZeroDivisors).ne
      (Polynomial.X_ne_zero (R := k))

private theorem localLine_isDVR : IsDiscreteValuationRing T where
  not_a_field' := by
    rw [localLine_maximalIdeal]
    exact fun h => localLine_parameter_ne_zero k (Ideal.span_singleton_eq_bot.mp h)

/-- Localization at the origin preserves the residue field obtained by evaluation at zero. -/
private def localLine_residueField : ResidueField T ≃+* k := by
  have h : origin k = Ideal.span {Polynomial.X - Polynomial.C 0} := by simp [origin]
  let e := (Ideal.quotientEquivAlgOfEq k h).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : k))
  exact (IsLocalization.AtPrime.equivQuotMaximalIdeal (origin k) T).symm.toRingEquiv.trans
    e.toRingEquiv

private theorem localLine_profile : IsDiscreteValuationRing T ∧
    𝔪 = Ideal.span {t} ∧ ringKrullDim T = 1 ∧ LocalGorenstein T ∧
      Nonempty (ResidueField T ≃+* k) := by
  let := localLine_isDVR k
  have hd := IsDiscreteValuationRing.ringKrullDim_eq_one T
  let : IsRegularLocalRing T := by
    rw [isRegularLocalRing_iff, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      IsLocalRing.finrank_CotangentSpace_eq_one, hd]
    simp
  exact ⟨inferInstance, localLine_maximalIdeal k, hd, regularLocal_gorenstein T,
    ⟨localLine_residueField k⟩⟩

theorem localLine_dvr : DVRProfile.{u} := fun k _ => localLine_profile k

private theorem rationalFunctions_isAway : IsLocalization.Away t K := by
  let := localLine_isDVR k
  have ht := localLine_parameter_ne_zero k
  have hi := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal t ht
    (localLine_maximalIdeal k)
  have hsub : Submonoid.powers t ≤ nonZeroDivisors T :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ht)
  have hdvd : ∀ x ∈ nonZeroDivisors T, ∃ y ∈ Submonoid.powers t, x ∣ y := by
    intro x hx
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hx) hi
    exact ⟨t ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact (IsLocalization.iff_of_le_of_exists_dvd (S := K) _ _ hsub hdvd).mpr inferInstance

private def cechOneFactor (R : Type u) [CommRing R] (x : R) :
    cechCoefficients [x] (ModuleCat.of R R) ≅
      Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor R x := by
  change tensorObj (tensorObj _ (tensorUnit (ModuleCat R) (.up ℤ)))
    (tensorUnit (ModuleCat R) (.up ℤ)) ≅ _
  exact (ρ_ _ : _) ≪≫ (ρ_ _ : _)

private def factorHomology (R : Type u) [CommRing R] (x : R) :
    (Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor R x).homology 1 ≅
      cokernel (ModuleCat.ofHom (Algebra.linearMap R (Localization.Away x))) := by
  let A := Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor R x
  let S := A.sc' 0 1 2
  have hf : S.f = ModuleCat.ofHom (Algebra.linearMap R (Localization.Away x)) := rfl
  have hg : S.g = 0 := by
    simp [S, A, HomologicalComplex.sc', Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor]
  exact A.homologyIsoSc' 0 1 2 (ComplexShape.prev_eq' _ (by rfl))
      (ComplexShape.next_eq' _ (by rfl)) ≪≫
    (ShortComplex.LeftHomologyData.ofHasCokernel S hg).homologyIso ≪≫
      cokernelIsoOfEq hf

private theorem cohomology_fractionQuotient :
    Nonempty (TopCohomology k ≃ₗ[T] FractionQuotient k) := by
  let := rationalFunctions_isAway k
  let e := IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t) K
  let H := homologyFunctor (ModuleCat T) (.up ℤ) 1
  let f : ModuleCat.of T T ⟶ ModuleCat.of T (Localization.Away t) :=
    ModuleCat.ofHom (Algebra.linearMap T (Localization.Away t))
  let g : ModuleCat.of T T ⟶ ModuleCat.of T K :=
    ModuleCat.ofHom (Algebra.linearMap T K)
  have hg : f ≫ e.toLinearEquiv.toModuleIso.hom = g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact e.commutes x
  have hgen : Ideal.span {x : T | x ∈ [t]} = Ideal.span {t} := by simp
  obtain ⟨c⟩ := localCohomologyCechComparison (Ideal.span {t}) [t] hgen 1
  exact ⟨(c.app (ModuleCat.of T T) ≪≫ H.mapIso (cechOneFactor T t) ≪≫
    factorHomology T t ≪≫ cokernel.mapIso f g (Iso.refl _) e.toLinearEquiv.toModuleIso
      (by simpa using hg) ≪≫ ModuleCat.cokernelIsoRangeQuotient g).toLinearEquiv⟩

theorem dvrLocalCohomologyFractionQuotient : FractionQuotientComparison.{u} :=
  fun k _ => cohomology_fractionQuotient k

set_option maxHeartbeats 600000 in
private theorem cohomology_residueHull (E : ResidueFieldEnvelope T) :
    Nonempty (TopCohomology k ≃ₗ[T] E.carrier) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} T)
  obtain ⟨_, hm, hd, hG, _⟩ := localLine_dvr k
  obtain ⟨e⟩ := gorenstein_top_localCohomology hG 1 hd E
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} T) 1
  let A := ModuleCat.of T E.carrier
  let shiftIso := (DerivedCategory.singleFunctors (ModuleCat.{u} T)).shiftIso
    (-1 : ℤ) 1 0 (by decide)
  change Nonempty ((localCohomology (Ideal.span {t}) 1).obj (ModuleCat.of T T) ≃ₗ[T] E.carrier)
  rw [← hm]
  let cmp := AdvancedHomologicalAlgebra.CechToCohomology.natRightDerivedIso
    (idealTorsionFunctor 𝔪) 1
  exact ⟨((cmp.app (ModuleCat.of T T)).symm ≪≫ H.mapIso (e ≪≫ shiftIso.app A) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 1).app A).toLinearEquiv⟩

theorem dvrLocalCohomologyResidueHull : ResidueHullComparison.{u} :=
  fun k _ E => cohomology_residueHull k E

private theorem completion_eval_compatible {R : Type*} [CommRing R]
    (I : Ideal R) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  simpa only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk] using
    AdicCompletion.Ideal.mk_eq_mk I h a

private theorem variableIdeal_map :
    (MvPolynomial.idealOfVars Unit k).map (MvPolynomial.uniqueAlgEquiv k Unit).toRingHom =
      origin k := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span]
  congr 1
  ext q
  simp only [Set.mem_singleton_iff]
  have hX (i : Unit) :
      MvPolynomial.uniqueAlgEquiv k Unit (MvPolynomial.X i) = Polynomial.X :=
    MvPolynomial.eval₂_X _ _ _
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hX i
  · rintro rfl
    exact ⟨MvPolynomial.X (), ⟨(), rfl⟩, hX ()⟩

local notation "P" => MvPolynomial Unit k
local notation "J" => MvPolynomial.idealOfVars Unit k

private def quotientStage (n : ℕ) :
    (P ⧸ J ^ n) ≃+* (T ⧸ 𝔪 ^ n) :=
  (Ideal.quotientEquiv (J ^ n) (origin k ^ n)
    (MvPolynomial.uniqueAlgEquiv k Unit).toRingEquiv
    (by
      rw [Ideal.map_pow]
      exact congrArg (fun I : Ideal (Polynomial k) => I ^ n) (variableIdeal_map k).symm)).trans
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow (origin k) T n).toRingEquiv

private theorem quotientStage_mk (n : ℕ) (p : P) :
    quotientStage k n (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (algebraMap (Polynomial k) T (MvPolynomial.uniqueAlgEquiv k Unit p)) :=
  rfl

private theorem quotientStage_compatible {m n : ℕ} (h : m ≤ n) (x : P ⧸ J ^ n) :
    Ideal.Quotient.factorPow 𝔪 h (quotientStage k n x) =
      quotientStage k m (Ideal.Quotient.factorPow J h x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private def polynomialCompletionStage (n : ℕ) :
    AdicCompletion J P →+* (T ⧸ 𝔪 ^ n) :=
  (quotientStage k n).toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom

private theorem polynomialCompletionStage_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow 𝔪 h).comp (polynomialCompletionStage k n) =
      polynomialCompletionStage k m :=
  RingHom.ext fun x => (quotientStage_compatible k h _).trans
    (congrArg (quotientStage k m) (completion_eval_compatible J h x))

/-- The map of completions induced by the polynomial map into the local ring. -/
private def completionOfPolynomial : AdicCompletion J P →+* Completion T :=
  AdicCompletion.liftRingHom 𝔪 (polynomialCompletionStage k)
    (polynomialCompletionStage_compatible k)

private theorem completionOfPolynomial_eval (n : ℕ) (x : AdicCompletion J P) :
    AdicCompletion.evalₐ 𝔪 n (completionOfPolynomial k x) =
      quotientStage k n (AdicCompletion.evalₐ J n x) :=
  AdicCompletion.evalₐ_liftRingHom 𝔪 (polynomialCompletionStage k)
    (polynomialCompletionStage_compatible k) n x

private def completionOfPolynomialEquiv : AdicCompletion J P ≃+* Completion T := by
  let F := completionOfPolynomial k
  let G := AdicCompletion.liftRingHom J
    (fun n => (quotientStage k n).symm.toRingHom.comp (AdicCompletion.evalₐ 𝔪 n).toRingHom)
    (fun h => RingHom.ext fun x => (quotientStage k _).injective (by
      change quotientStage k _ (Ideal.Quotient.factorPow J h
        ((quotientStage k _).symm (AdicCompletion.evalₐ 𝔪 _ x))) =
          quotientStage k _ ((quotientStage k _).symm (AdicCompletion.evalₐ 𝔪 _ x))
      rw [← quotientStage_compatible, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
        completion_eval_compatible]))
  have hG (n : ℕ) (x : Completion T) :
      AdicCompletion.evalₐ J n (G x) = (quotientStage k n).symm (AdicCompletion.evalₐ 𝔪 n x) :=
    AdicCompletion.evalₐ_liftRingHom _ _ _ _ _
  exact RingEquiv.ofRingHom F G
    (RingHom.ext fun x => AdicCompletion.ext_evalₐ (fun n => by
      change AdicCompletion.evalₐ 𝔪 n (F (G x)) = AdicCompletion.evalₐ 𝔪 n x
      rw [show F = completionOfPolynomial k from rfl, completionOfPolynomial_eval, hG,
        RingEquiv.apply_symm_apply]))
    (RingHom.ext fun x => AdicCompletion.ext_evalₐ (fun n => by
      change AdicCompletion.evalₐ J n (G (F x)) = AdicCompletion.evalₐ J n x
      rw [hG, show F = completionOfPolynomial k from rfl, completionOfPolynomial_eval,
        RingEquiv.symm_apply_apply]))

private theorem completionOfPolynomialEquiv_of (p : P) :
    completionOfPolynomialEquiv k (AdicCompletion.of J P p) =
      AdicCompletion.of 𝔪 T (algebraMap (Polynomial k) T (MvPolynomial.uniqueAlgEquiv k Unit p)) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ 𝔪 n (completionOfPolynomial k (AdicCompletion.of J P p)) = _
  rw [completionOfPolynomial_eval, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of,
    quotientStage_mk]

private def completionPowerSeriesEquiv : Completion T ≃ₐ[T] PowerSeries k := by
  let e : PowerSeries k ≃+* Completion T :=
    (MvPowerSeries.toAdicCompletionAlgEquiv Unit k).toRingEquiv.trans
      (completionOfPolynomialEquiv k)
  refine { e.symm with commutes' := ?_ }
  have h : e.toRingHom.comp (seriesMap k) = algebraMap T (Completion T) := by
    apply IsLocalization.ringHom_ext (M := (origin k).primeCompl)
    apply RingHom.ext
    intro p
    change e (seriesMap k (algebraMap (Polynomial k) T p)) =
      algebraMap T (Completion T) (algebraMap (Polynomial k) T p)
    rw [seriesMap, IsLocalization.lift_eq]
    let q := (MvPolynomial.uniqueAlgEquiv k Unit).symm p
    have hq : MvPolynomial.uniqueAlgEquiv k Unit q = p := AlgEquiv.apply_symm_apply _ _
    change e (p : PowerSeries k) = _
    rw [Polynomial.pUnitAlgEquiv_symm_toPowerSeries]
    change completionOfPolynomialEquiv k (MvPowerSeries.toAdicCompletion Unit k
      (q : MvPowerSeries Unit k)) = _
    rw [MvPowerSeries.toAdicCompletion_coe, completionOfPolynomialEquiv_of, hq]
    rfl
  intro a
  change e.symm (algebraMap T (Completion T) a) = seriesMap k a
  apply e.injective
  rw [RingEquiv.apply_symm_apply]
  exact (congrArg (fun f : T →+* Completion T => f a) h).symm

theorem dvrCompletionPowerSeries : CompletionComparison.{u} := by
  intro k _
  exact ⟨completionPowerSeriesEquiv k⟩

private theorem seriesMap_not_surjective : ¬ Function.Surjective (seriesMap k) := by
  classical
  let f : PowerSeries k := PowerSeries.mk fun j =>
    if ∃ a : ℕ, j = 2 ^ a then 1 else 0
  intro surj
  obtain ⟨x, hx⟩ := surj f
  obtain ⟨⟨p, q⟩, hfrac⟩ := IsLocalization.surj (origin k).primeCompl x
  have hq₀ : (q : Polynomial k).coeff 0 ≠ 0 := by
    intro h
    exact q.property (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h))
  have hpoly (r : Polynomial k) :
      seriesMap k (algebraMap (Polynomial k) T r) = (r : PowerSeries k) := by
    rw [seriesMap, IsLocalization.lift_eq, Polynomial.coeToPowerSeries.ringHom_apply]
  have hproduct : (q.val : PowerSeries k) * f = (p : PowerSeries k) := by
    have h := congrArg (seriesMap k) hfrac
    rw [map_mul, hx, hpoly, hpoly, mul_comm] at h
    exact h
  let m := max p.natDegree q.val.natDegree
  let n := 2 ^ (m + 1)
  have hgap : m < 2 ^ m := Nat.lt_two_pow_self
  have hn : n = 2 ^ m + 2 ^ m := Nat.two_pow_succ m
  have hm : m < n := by omega
  have hp : p.natDegree < n := (le_max_left _ _).trans_lt hm
  -- At degree n, the constant coefficient of q supplies the only nonzero term.
  have hcoeff : PowerSeries.coeff n ((q.val : PowerSeries k) * f) = q.val.coeff 0 := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · change PowerSeries.coeff 0 (q.val : PowerSeries k) * PowerSeries.coeff n f = _
      rw [Polynomial.coeff_coe, PowerSeries.coeff_mk, ite_eq_left ⟨m + 1, rfl⟩, mul_one]
    · rintro ⟨i, j⟩ hij hne
      have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
      rw [Polynomial.coeff_coe]
      by_cases hi : q.val.natDegree < i
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      · have hi' : i ≤ m := (Nat.le_of_not_gt hi).trans (le_max_right _ _)
        have hi₀ : i ≠ 0 := by
          intro he
          subst i
          exact hne (Prod.ext rfl (by simpa using hij'))
        have hj : ¬ ∃ a : ℕ, j = 2 ^ a := by
          rintro ⟨a, ha⟩
          by_cases ham : a ≤ m
          · have hle := Nat.pow_le_pow_right (by decide : 0 < 2) ham
            omega
          · have hle := Nat.pow_le_pow_right (by decide : 0 < 2)
              (show m + 1 ≤ a by omega)
            omega
        rw [PowerSeries.coeff_mk, ite_eq_right hj, mul_zero]
    · intro h
      exact (h (Finset.mem_antidiagonal.mpr (zero_add n))).elim
  exact hq₀ (by
    rw [← hcoeff, hproduct, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hp])

theorem localLine_not_isAdicComplete : Noncomplete.{u} := by
  intro k _ h
  apply seriesMap_not_surjective k
  intro f
  let e := completionPowerSeriesEquiv k
  obtain ⟨x, hx⟩ := (AdicCompletion.of_bijective_iff.mpr h).2 (e.symm f)
  refine ⟨x, ?_⟩
  rw [← e.apply_symm_apply f, ← hx]
  exact (e.commutes x).symm

private theorem cohomology_matlisDual (E : ResidueFieldEnvelope T) :
    ∃ (h : IsPowerTorsion T E.carrier)
      (e : Completion T ≃ₐ[T] PowerSeries k),
      let := completionModule h
      let := completionScalarTower h
      let : Module (Completion T) (PowerSeries k) := Module.compHom _ e.toRingHom
      Nonempty ((TopCohomology k →ₗ[T] E.carrier) ≃ₗ[Completion T] PowerSeries k) := by
  obtain ⟨f⟩ := dvrLocalCohomologyResidueHull k E
  let h := residueHull_powerTorsion E
  let e := completionPowerSeriesEquiv k
  refine ⟨h, e, ?_⟩
  let := completionModule h
  let := completionScalarTower h
  let : Module (Completion T) (PowerSeries k) := Module.compHom _ e.toRingHom
  let a := residueHullEndomorphismEquiv E
  let l : Completion T →ₗ[Completion T] (TopCohomology k →ₗ[T] E.carrier) :=
    { toFun := fun s => (a s).comp f.toLinearMap
      map_add' := by
        intro s r
        ext x
        simp
      map_smul' := by
        intro s r
        ext x
        change a (s * r) (f x) = scalar h s (a r (f x))
        rw [map_mul, Module.End.mul_apply, residueHullEndomorphismEquiv_apply] }
  have hl : Function.Bijective l := by
    constructor
    · intro s r hsr
      apply a.injective
      ext x
      obtain ⟨y, rfl⟩ := f.surjective x
      exact congrArg (fun g : TopCohomology k →ₗ[T] E.carrier => g y) hsr
    · intro g
      refine ⟨a.symm (g.comp f.symm.toLinearMap), ?_⟩
      ext x
      change (a (a.symm (g.comp f.symm.toLinearMap))) (f x) = g x
      simp
  let e' : Completion T ≃ₗ[Completion T] PowerSeries k :=
    { e.toAddEquiv with
      map_smul' := fun s r => e.map_mul s r }
  exact ⟨(LinearEquiv.ofBijective l hl).symm.trans e'⟩

theorem dvrLocalCohomologyMatlisDual : MatlisDualComparison.{u} :=
  fun k _ E => cohomology_matlisDual k E

end CommutativeAlgebraNotes
