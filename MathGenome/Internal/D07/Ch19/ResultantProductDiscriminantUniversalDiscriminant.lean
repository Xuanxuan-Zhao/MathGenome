import MathGenome.Internal.Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant
import MathGenome.Internal.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
The notes' discriminant is first related to the fixed-bound resultant by
factoring off one indexed linear factor before differentiation, then pairing
oppositely directed root differences. This works for repeated roots and in
all characteristics. Cancellation of the nonzero leading coefficient identifies
it with the modified Sylvester determinant. Over the universal integer coefficient
ring this determinant is already a polynomial, and its specialization is proved
by mapping the modified matrix at a fixed size.
-/

universe u v
noncomputable section
namespace D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant
open Polynomial Finset
open Specs.D07.Ch19.ResultantDefinition
open Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant

/-- The modified derivative matrix with its size given independently of the polynomial. -/
private def derivativeMatrix {R : Type*} [CommRing R] (f : R[X]) (n : ℕ) :
    Matrix (Fin (n - 1 + n)) (Fin (n - 1 + n)) R :=
  if hn : n = 0 then 0
  else (f.derivative.sylvester f (n - 1) n).updateRow ⟨2 * n - 2, by omega⟩
    (fun j => if ↑j = n - 2 then 1 else if ↑j = 2 * n - 2 then n else 0)

private lemma derivativeMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X]) (n : ℕ) :
    derivativeMatrix (f.map φ) n = φ.mapMatrix (derivativeMatrix f n) := by
  unfold derivativeMatrix
  split_ifs with hn
  · ext i j; simp
  · rw [Polynomial.derivative_map, Polynomial.sylvester_map_map]
    ext i j
    simp only [Matrix.updateRow_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      apply_ite φ, map_one, map_natCast, map_zero]

lemma discr_map_of_natDegree_eq {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X]) (h : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  change (derivativeMatrix (f.map φ) (f.map φ).natDegree).det * _ =
    φ ((derivativeMatrix f f.natDegree).det * _)
  rw [h, derivativeMatrix_map, ← RingHom.map_det, map_mul, map_pow, map_neg, map_one]

lemma universalPolynomial_degree (n : ℕ) : (universalPolynomial n).natDegree = n := by
  apply le_antisymm
  · exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
  · apply Polynomial.le_natDegree_of_ne_zero
    change ((Polynomial.ofFn (n + 1)) (fun i => MvPolynomial.X i)).coeff n ≠ 0
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self n)]
    exact MvPolynomial.X_ne_zero _

lemma universalPolynomial_map {R : Type*} [CommRing R] (f : R[X]) (n : ℕ)
    (h : f.natDegree ≤ n) :
    (universalPolynomial n).map
      (MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin (n + 1) => f.coeff i)) = f := by
  classical
  ext k
  rw [Polynomial.coeff_map]
  by_cases hk : k < n + 1
  · simp [universalPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
  · rw [show f.coeff k = 0 from Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp only [universalPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk), map_zero]

theorem universalSpecialization : UniversalSpecialization.{u} := by
  intro R _ f n hn
  have hm := discr_map_of_natDegree_eq
    (MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin (n + 1) => f.coeff i))
    (universalPolynomial n) (by rw [universalPolynomial_map f n hn.le,
      universalPolynomial_degree, hn])
  rw [universalPolynomial_map f n hn.le] at hm
  exact hm.symm

theorem universalResultantDivision : UniversalResultantDivision := by
  intro n hn
  have hd := universalPolynomial_degree n
  rw [D07.Ch19.ResultantDefinition.resultantBridge _ _ _ _ _ hd.le
    (by simpa [hd] using (Polynomial.natDegree_derivative_le (universalPolynomial n)))]
  have hr := Polynomial.resultant_deriv (f := universalPolynomial n)
    (by rw [← Polynomial.natDegree_pos_iff_degree_pos, hd]; omega)
  have hl : (universalPolynomial n).leadingCoeff = MvPolynomial.X (Fin.last n) := by
    rw [Polynomial.leadingCoeff, hd]
    simp only [universalPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self n)]
    rfl
  simpa only [hd, hl, universalDiscriminant] using hr

theorem degreeOne : DegreeOne.{u} := by
  intro L _ a α
  simp [rootDiscriminant, rootDifferenceProduct]

theorem zeroDerivative : ZeroDerivative.{u} := by
  intro F _ f n hf hn hp hz
  have hres : fixedResultant f f.derivative n (n - 1) = 0 := by
    rw [D07.Ch19.ResultantDefinition.resultantBridge _ _ _ _ _ hn.le
      (by simp [hz]), hz, Polynomial.resultant_zero_right]
    simp [show n ≠ 0 by omega]
  refine ⟨hres, ?_⟩
  rw [D07.Ch19.ResultantDefinition.resultantBridge _ _ _ _ _ hn.le
    (by simp [hz]), ← hn,
    Polynomial.resultant_deriv (by rw [← Polynomial.natDegree_pos_iff_degree_pos, hn]; omega)] at hres
  exact (mul_eq_zero.mp hres).resolve_left
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Polynomial.leadingCoeff_ne_zero.mpr hf))

lemma permutationInvariance : PermutationInvariance.{u} := by
  intro R _ n α σ
  simp only [rootDifferenceProduct, Function.comp_apply, Finset.prod_pow]
  rw [σ.prod_Ioi_comp_eq_sign_mul_prod (f := fun i j => α i - α j) (fun i j => (neg_sub _ _).symm), mul_pow]
  have hr : ((σ.sign : ℤ) : R) ^ 2 = 1 := by
    rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one, Int.cast_one]
  rw [hr, one_mul]

lemma vanishingIffRepeatedEntries : VanishingIffRepeatedEntries.{u} := by
  intro L _ n a α ha
  simp only [rootDiscriminant, mul_eq_zero, pow_ne_zero _ ha, false_or,
    rootDifferenceProduct, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    Finset.mem_Ioi, pow_eq_zero_iff (by decide : 2 ≠ 0), sub_eq_zero]

lemma repeatedEntries_iff_not_injective {L : Type*} {n : ℕ} (α : Fin n → L) :
    (∃ i j, i < j ∧ α i = α j) ↔ ¬ Function.Injective α := by
  constructor
  · rintro ⟨i,j,hij,he⟩ hi; exact hij.ne (hi he)
  · intro h
    obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp h
    rcases lt_or_gt_of_ne hne with hij | hij
    · exact ⟨i,j,hij,he⟩
    · exact ⟨j,i,hij,he.symm⟩

lemma vanishingIffRepeatedRoot : VanishingIffRepeatedRoot.{u,v} := by
  classical
  intro F L _ _ _ f n α hf hn hnpos hs hα
  rw [vanishingIffRepeatedEntries L n _ α
    (by simpa using (algebraMap F L).injective.ne (Polynomial.leadingCoeff_ne_zero.mpr hf)),
    repeatedEntries_iff_not_injective, ← List.nodup_ofFn, ← Multiset.coe_nodup, hα,
    Multiset.nodup_iff_count_le_one]
  simp only [Polynomial.count_roots, not_forall, not_le]
  exact exists_congr (fun x => by omega)

lemma pairCount (n : ℕ) : (∑ i : Fin n, #(Finset.Ioi i)) = n * (n-1) / 2 := by
  calc
    _ = ∑ i : Fin n, (i.rev : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Fin.val_rev, Nat.sub_sub, Nat.add_comm]
    _ = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp Fin.revPerm _
    _ = _ := (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n).trans (Finset.sum_range_id n)

lemma directedDifferenceProduct {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) :
    (∏ i, ∏ j ∈ ({i}ᶜ : Finset (Fin n)), (α i - α j)) =
      (-1 : R) ^ (n*(n-1)/2) * rootDifferenceProduct α := by
  rw [← Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j => α j - α i)]
  have he : ∀ i j : Fin n, (α i - α j) * (α j - α i) = (-1 : R) * (α i - α j)^2 := by
    intros; ring
  simp_rw [he, Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum, pairCount]
  rfl

lemma evalDerivativeAtIndex {L : Type*} [Field L] (f : L[X]) {n : ℕ}
    (α : Fin n → L) (hs : f.Splits) (hα : (List.ofFn α : Multiset L) = f.roots)
    (i : Fin n) :
    f.derivative.eval (α i) = f.leadingCoeff * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), (α i - α j) := by
  classical
  have hfac := hs.eq_prod_roots
  rw [← hα] at hfac
  simp only [Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, List.prod_ofFn, Function.comp_def] at hfac
  rw [← Finset.mul_prod_erase univ (fun j => (X - C (α j) : L[X])) (mem_univ i)] at hfac
  conv_lhs => rw [hfac]
  simp [derivative_mul, Polynomial.eval_prod, ← Finset.compl_singleton]

lemma derivativeProduct {L : Type*} [Field L] (f : L[X]) {n : ℕ}
    (α : Fin n → L) (hs : f.Splits) (hα : (List.ofFn α : Multiset L) = f.roots) :
    (∏ i, f.derivative.eval (α i)) =
      (-1 : L) ^ (n * (n-1)/2) * f.leadingCoeff^n * rootDifferenceProduct α := by
  simp_rw [evalDerivativeAtIndex f α hs hα]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, directedDifferenceProduct]
  ring

lemma resultantDiscriminant {R : Type*} [CommRing R] (f : R[X]) (n : ℕ)
    (hn : f.natDegree = n) (hp : 1 ≤ n) :
    fixedResultant f f.derivative n (n-1) =
      (-1 : R)^(n*(n-1)/2) * f.leadingCoeff * f.discr := by
  rw [D07.Ch19.ResultantDefinition.resultantBridge _ _ _ _ _ hn.le
    (by simpa [hn] using Polynomial.natDegree_derivative_le f)]
  simpa only [hn] using Polynomial.resultant_deriv (f := f)
    (by rw [← Polynomial.natDegree_pos_iff_degree_pos, hn]; omega)

lemma resultantRootDiscriminant {F L : Type*} [Field F] [Field L] [Algebra F L]
    (f : F[X]) (n : ℕ) (α : Fin n → L) (hf : f ≠ 0) (hn : f.natDegree = n)
    (hnpos : 1 ≤ n) (hs : (f.map (algebraMap F L)).Splits)
    (hα : (List.ofFn α : Multiset L) = (f.map (algebraMap F L)).roots) :
    algebraMap F L (fixedResultant f f.derivative n (n-1)) =
      (-1 : L)^(n*(n-1)/2) * algebraMap F L f.leadingCoeff *
        rootDiscriminant (algebraMap F L f.leadingCoeff) α := by
  have hr := D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.indexedRootProduct F L f f.derivative n (n-1) α hf hn hnpos
    (by simpa [hn] using Polynomial.natDegree_derivative_le f) hs hα
  have hd := derivativeProduct (f.map (algebraMap F L)) α hs hα
  simp only [Polynomial.derivative_map, Polynomial.eval_map_algebraMap,
    Polynomial.leadingCoeff_map] at hd
  rw [hr, hd]
  unfold rootDiscriminant
  have hexp : n - 1 + n = 1 + (2 * n - 2) := by omega
  calc
    _ = (-1 : L)^(n*(n-1)/2) * algebraMap F L f.leadingCoeff ^ (n-1+n) *
        rootDifferenceProduct α := by rw [pow_add]; ring
    _ = _ := by rw [hexp, pow_add, pow_one]; ring

lemma rootProductEqualsDiscriminant : RootProductEqualsDiscriminant.{u,v} := by
  intro F L _ _ _ f n α hf hn hp hs hα
  have h1 := resultantRootDiscriminant f n α hf hn hp hs hα
  rw [resultantDiscriminant f n hn hp, map_mul, map_mul, map_pow, map_neg, map_one] at h1
  have ha : algebraMap F L f.leadingCoeff ≠ 0 := by
    simpa using (algebraMap F L).injective.ne (Polynomial.leadingCoeff_ne_zero.mpr hf)
  exact (mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ha) h1).symm

lemma numberingIndependence : NumberingIndependence.{u,v} := by
  intro F L _ _ _ f n α β hf hn hp hs hα hβ
  rw [rootProductEqualsDiscriminant F L f n α hf hn hp hs hα,
    rootProductEqualsDiscriminant F L f n β hf hn hp hs hβ]

lemma discriminantResultantIdentity : DiscriminantResultantIdentity.{u,v} := by
  intro F L _ _ _ f n α hf hn hp hs hα
  rw [rootProductEqualsDiscriminant F L f n α hf hn hp hs hα,
    resultantDiscriminant f n hn hp, map_mul, map_mul, map_pow, map_neg, map_one]
  have ha : algebraMap F L f.leadingCoeff ≠ 0 := by
    simpa using (algebraMap F L).injective.ne (Polynomial.leadingCoeff_ne_zero.mpr hf)
  have hsquare : ((-1 : L)^(n*(n-1)/2))^2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul]; simp
  calc
    _ = ((-1 : L)^(n*(n-1)/2))^2 * algebraMap F L f.discr := by rw [hsquare, one_mul]
    _ = _ := by field_simp

theorem universalRootSpecialization : UniversalRootSpecialization.{u,v} := by
  intro F L _ _ _ f n α hf hn hp hs hα
  rw [universalSpecialization F f n hn]
  exact (rootProductEqualsDiscriminant F L f n α hf hn hp hs hα).symm

end D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant
