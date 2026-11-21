import MathGenome.Internal.Specs.D07.Ch14.QuarticSplittingExample
import MathGenome.Internal.D07.Ch11.Eisenstein
import MathGenome.Internal.D07.Ch14.DegreeIndex
import MathGenome.Internal.D07.Ch14.NormalQuotient
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
K07.14.quartic_splitting_example, paper.tex:4272–4281.

The positive fourth root is sqrt(sqrt(2)). Eisenstein and the realness of
ℚ(a) give the tower degrees 4 and 2. Explicit linear factors prove splitting
and field generation. Over ℚ(i), the degree-four minimal polynomial supplies
the rotation; complex conjugation supplies the reflection. Their action on
the two generators constructs an explicit equivalence with DihedralGroup 4.
The degree/index theorem identifies the two actual fixed fields, and the
normal-subgroup criterion yields their different normality behavior.
-/

noncomputable section
namespace D07.Ch14.QuarticSplittingExample
open Polynomial IntermediateField
open Specs.D07.Ch14.QuarticSplittingExample

lemma aReal_pos : 0 < aReal := by
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by norm_num))

lemma aReal_four : aReal ^ 4 = 2 := by
  have h : aReal ^ 2 = Real.sqrt 2 := Real.sq_sqrt (Real.sqrt_nonneg _)
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, Real.sq_sqrt (by norm_num)]

lemma aComplex_four : aComplex ^ 4 = 2 := by
  change (aReal : ℂ) ^ 4 = 2
  exact_mod_cast aReal_four

lemma a_four : a ^ 4 = 2 := by
  apply Subtype.val_injective
  exact aComplex_four

lemma i_sq : i ^ 2 = -1 := by
  apply Subtype.val_injective
  exact Complex.I_sq

lemma a_ne_zero : a ≠ 0 := by
  intro h
  have := a_four
  rw [h, zero_pow (by decide)] at this
  norm_num at this

lemma i_ne_zero : i ≠ 0 := by
  intro h
  have := i_sq
  rw [h, zero_pow (by decide)] at this
  norm_num at this

lemma root_data : RootData := ⟨aReal_pos, aReal_four, rfl, rfl⟩

lemma field_eq_adjoin_pair : splittingField = adjoin ℚ {aComplex, Complex.I} :=
  adjoin_simple_adjoin_simple ℚ aComplex Complex.I

lemma irreducible_polynomial : Irreducible polynomial := by
  exact (D07.Ch11.Eisenstein.xPowSubPrime 2 4 (by decide) (by decide)).2

lemma minpoly_aComplex : minpoly ℚ aComplex = polynomial := by
  symm
  apply minpoly.eq_of_irreducible_of_monic irreducible_polynomial
  · simpa [polynomial] using sub_eq_zero.mpr aComplex_four
  · exact monic_X_pow_sub_C _ (by decide)

lemma aComplex_integral : IsIntegral ℚ aComplex := by
  exact ⟨polynomial, monic_X_pow_sub_C _ (by decide), by simp [polynomial, aComplex_four]⟩

instance realRootField_finite : FiniteDimensional ℚ realRootField :=
  adjoin.finiteDimensional aComplex_integral

lemma realRootField_degree : Module.finrank ℚ realRootField = 4 := by
  rw [realRootField, adjoin.finrank aComplex_integral, minpoly_aComplex]
  exact natDegree_X_pow_sub_C

lemma realRootField_conj (x : ℂ) (hx : x ∈ realRootField) : (starRingEnd ℂ) x = x := by
  refine adjoin_induction ℚ (motive := fun x _ => (starRingEnd ℂ) x = x)
    ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Complex.conj_ofReal _
  · intro q
    simp
  · intro y z _ _ hy hz
    rw [map_add, hy, hz]
  · intro y _ hy
    rw [map_inv₀, hy]
  · intro y z _ _ hy hz
    rw [map_mul, hy, hz]

lemma realRootField_im (x : realRootField) : (x : ℂ).im = 0 :=
  Complex.conj_eq_iff_im.mp (realRootField_conj x x.property)

lemma i_minpoly_over_realRootField :
    minpoly realRootField Complex.I = (X ^ 2 + 1 : realRootField[X]) := by
  have hdeg : (X ^ 2 + (1 : realRootField[X])).natDegree = 2 := by
    compute_degree!
  have hirr : Irreducible (X ^ 2 + (1 : realRootField[X])) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · simp [hdeg]
    · intro x hx
      have he : x ^ 2 + 1 = 0 := by simpa using hx
      have he' := congrArg (fun y : realRootField => (y : ℂ).re) he
      have hxim := realRootField_im x
      change (((x : ℂ) ^ 2 + 1).re) = 0 at he'
      simp [pow_two, Complex.mul_re, hxim] at he'
      nlinarith [sq_nonneg (x : ℂ).re]
  symm
  apply minpoly.eq_of_irreducible_of_monic hirr
  · simp [Complex.I_sq]
  · exact (monic_X_pow_add_C _ (by decide))

lemma i_integral_over_realRootField : IsIntegral realRootField Complex.I := by
  refine ⟨X ^ 2 + 1, monic_X_pow_add_C _ (by decide), ?_⟩
  simp [Complex.I_sq]

instance splittingField_algebra_over_realRootField : Algebra realRootField L :=
  inferInstanceAs (Algebra realRootField (adjoin realRootField ({Complex.I} : Set ℂ)))

instance splittingField_tower : IsScalarTower ℚ realRootField L :=
  inferInstanceAs (IsScalarTower ℚ realRootField (adjoin realRootField ({Complex.I} : Set ℂ)))

instance splittingField_finite_over_realRootField : FiniteDimensional realRootField L :=
  adjoin.finiteDimensional i_integral_over_realRootField

instance splittingField_finite : FiniteDimensional ℚ L :=
  Module.Finite.trans realRootField L

lemma splittingField_degree_over_realRootField : Module.finrank realRootField L = 2 := by
  change Module.finrank realRootField (adjoin realRootField {Complex.I}) = 2
  rw [adjoin.finrank i_integral_over_realRootField, i_minpoly_over_realRootField]
  compute_degree!

lemma splittingField_degree : Module.finrank ℚ L = 8 := by
  rw [← Module.finrank_mul_finrank ℚ realRootField L,
    realRootField_degree, splittingField_degree_over_realRootField]


lemma adjoin_generators : adjoin ℚ ({a, i} : Set L) = ⊤ := by
  apply map_injective splittingField.val
  rw [adjoin_map, Set.image_pair]
  rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  exact field_eq_adjoin_pair.symm

lemma polynomial_factorization :
    polynomial.map (algebraMap ℚ L) =
    (X - C a) * (X + C a) * (X - C (i * a)) * (X + C (i * a)) := by
  have hi : (C i : L[X]) ^ 2 = -1 := by rw [← C_pow, i_sq]; simp
  have ha : (C a : L[X]) ^ 4 = 2 := by rw [← C_pow, a_four, C_ofNat]
  simp only [polynomial, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, C_mul, C_ofNat]
  linear_combination ha + ((C a) ^ 2 * (X ^ 2 - (C a) ^ 2)) * hi

lemma polynomial_splits : (polynomial.map (algebraMap ℚ L)).Splits := by
  rw [polynomial_factorization]
  have hplus (x : L) : (X + C x).Splits := by
    simpa only [C_neg, sub_neg_eq_add] using (Splits.X_sub_C (-x))
  exact (((Splits.X_sub_C a).mul (hplus a)).mul (Splits.X_sub_C (i * a))).mul (hplus (i * a))

lemma polynomial_eval_a : aeval a polynomial = 0 := by simp [polynomial, a_four]
lemma polynomial_eval_ia : aeval (i * a) polynomial = 0 := by
  have hi4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, i_sq]; norm_num
  simp [polynomial, mul_pow, hi4, a_four]

lemma roots_generate : adjoin ℚ (polynomial.rootSet L) = ⊤ := by
  apply top_unique
  rw [← adjoin_generators]
  apply adjoin_le_iff.mpr
  intro x hx
  rcases hx with rfl | hx
  · exact subset_adjoin ℚ _ (mem_rootSet.mpr ⟨irreducible_polynomial.ne_zero, polynomial_eval_a⟩)
  · have hx : x = i := Set.mem_singleton_iff.mp hx
    subst x
    have ha : a ∈ adjoin ℚ (polynomial.rootSet L) :=
      subset_adjoin ℚ _ (mem_rootSet.mpr ⟨irreducible_polynomial.ne_zero, polynomial_eval_a⟩)
    have hia : i * a ∈ adjoin ℚ (polynomial.rootSet L) :=
      subset_adjoin ℚ _ (mem_rootSet.mpr ⟨irreducible_polynomial.ne_zero, polynomial_eval_ia⟩)
    simpa [a_ne_zero] using (adjoin ℚ (polynomial.rootSet L)).div_mem hia ha

instance splittingField_splits : Polynomial.IsSplittingField ℚ L polynomial :=
  isSplittingField_iff_intermediateField.mpr ⟨polynomial_splits, roots_generate⟩

instance splittingField_galois : IsGalois ℚ L := by
  exact IsGalois.of_separable_splitting_field irreducible_polynomial.separable


lemma minpoly_a : minpoly ℚ a = polynomial := by
  symm
  exact minpoly.eq_of_irreducible_of_monic irreducible_polynomial polynomial_eval_a
    (monic_X_pow_sub_C _ (by decide))

lemma rationalA_degree : Module.finrank ℚ rationalA = 4 := by
  rw [rationalA, adjoin.finrank (IsIntegral.of_finite ℚ a), minpoly_a]
  exact natDegree_X_pow_sub_C

lemma irreducible_i_polynomial : Irreducible (X ^ 2 + (1 : ℚ[X])) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (X ^ 2 + (1 : ℚ[X])).natDegree = 2 := by compute_degree!
    simp [hd]
  · intro x hx
    have he : x ^ 2 + 1 = 0 := by simpa using hx
    nlinarith [sq_nonneg x]

lemma minpoly_i : minpoly ℚ i = X ^ 2 + 1 := by
  symm
  exact minpoly.eq_of_irreducible_of_monic irreducible_i_polynomial
    (by simp [i_sq]) (monic_X_pow_add_C _ (by decide))

lemma rationalI_degree : Module.finrank ℚ rationalI = 2 := by
  rw [rationalI, adjoin.finrank (IsIntegral.of_finite ℚ i), minpoly_i]
  compute_degree!

lemma field_data : FieldData :=
  ⟨field_eq_adjoin_pair, inferInstance, splittingField_degree, inferInstance,
    inferInstance, rationalA_degree, rationalI_degree⟩

lemma automorphism_ext {σ τ : L ≃ₐ[ℚ] L} (ha : σ a = τ a) (hi : σ i = τ i) : σ = τ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext_of_eq_adjoin ℚ field_eq_adjoin_pair
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ha
  · rcases Set.mem_singleton_iff.mp hx with rfl
    exact hi

lemma conj_mem (x : L) : (starRingEnd ℂ) (x : ℂ) ∈ splittingField := by
  have hx : (x : ℂ) ∈ adjoin ℚ ({aComplex, Complex.I} : Set ℂ) := by
    rw [← field_eq_adjoin_pair]
    exact x.property
  refine adjoin_induction ℚ (motive := fun x _ => (starRingEnd ℂ) x ∈ splittingField)
    ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · rw [show (starRingEnd ℂ) aComplex = aComplex from Complex.conj_ofReal _]
      exact a.property
    · rcases Set.mem_singleton_iff.mp hy with rfl
      rw [Complex.conj_I]
      exact splittingField.neg_mem i.property
  · intro q
    simp
  · intro y z _ _ hy hz
    rw [map_add]
    exact splittingField.add_mem hy hz
  · intro y _ hy
    rw [map_inv₀]
    exact splittingField.inv_mem hy
  · intro y z _ _ hy hz
    rw [map_mul]
    exact splittingField.mul_mem hy hz

def conjugation : L ≃ₐ[ℚ] L where
  toFun x := ⟨(starRingEnd ℂ) (x : ℂ), conj_mem x⟩
  invFun x := ⟨(starRingEnd ℂ) (x : ℂ), conj_mem x⟩
  left_inv x := by apply Subtype.ext; exact star_star _
  right_inv x := by apply Subtype.ext; exact star_star _
  map_mul' x y := by apply Subtype.ext; exact map_mul (starRingEnd ℂ) _ _
  map_add' x y := by apply Subtype.ext; exact map_add (starRingEnd ℂ) _ _
  commutes' q := by apply Subtype.ext; simp

lemma conjugation_a : conjugation a = a := by
  apply Subtype.ext
  exact Complex.conj_ofReal _

lemma conjugation_i : conjugation i = -i := by
  apply Subtype.ext
  exact Complex.conj_I

lemma conjugation_sq : conjugation ^ 2 = 1 := by
  apply automorphism_ext
  · simp [pow_two, AlgEquiv.mul_apply, conjugation_a]
  · simp [pow_two, AlgEquiv.mul_apply, conjugation_i]

lemma adjoin_a_over_rationalI : adjoin rationalI {a} = ⊤ := by
  apply restrictScalars_injective ℚ
  rw [restrictScalars_top, restrictScalars_adjoin_eq_sup, rationalI,
    sup_comm, ← adjoin_union]
  simpa only [Set.singleton_union] using adjoin_generators

lemma degree_over_rationalI : Module.finrank rationalI L = 4 := by
  have h := Module.finrank_mul_finrank ℚ rationalI L
  rw [rationalI_degree, splittingField_degree] at h
  omega

lemma minpoly_a_over_rationalI : minpoly rationalI a = X ^ 4 - C 2 := by
  have hdegree : (minpoly rationalI a).natDegree = 4 := by
    have h := (PowerBasis.ofAdjoinSimpleEqTop (IsIntegral.of_finite rationalI a)
      adjoin_a_over_rationalI).finrank
    simpa only [PowerBasis.ofAdjoinSimpleEqTop_dim, degree_over_rationalI] using h.symm
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsIntegral.of_finite rationalI a))
    (monic_X_pow_sub_C _ (by decide))
  · apply minpoly.dvd
    simp only [map_sub, aeval_X_pow, aeval_C, a_four]
    exact sub_eq_zero.mpr (map_ofNat rationalI.val 2).symm
  · rw [hdegree, natDegree_X_pow_sub_C]

lemma rotation_exists : ∃ r : L ≃ₐ[ℚ] L, r a = i * a ∧ r i = i := by
  have hirr : Irreducible (X ^ 4 - C (2 : rationalI)) := by
    rw [← minpoly_a_over_rationalI]
    exact minpoly.irreducible (IsIntegral.of_finite rationalI a)
  have hroot : aeval (i * a) (X ^ 4 - C (2 : rationalI)) = 0 := by
    have hi4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, i_sq]; norm_num
    simp only [map_sub, aeval_X_pow, aeval_C, mul_pow, a_four, hi4, one_mul]
    exact sub_eq_zero.mpr (map_ofNat rationalI.val 2).symm
  have heq : minpoly rationalI (i * a) = minpoly rationalI a := by
    rw [minpoly_a_over_rationalI]
    exact (minpoly.eq_of_irreducible_of_monic hirr hroot
      (monic_X_pow_sub_C _ (by decide))).symm
  obtain ⟨r, hr⟩ := (Normal.minpoly_eq_iff_mem_orbit L).mp heq
  refine ⟨r.restrictScalars ℚ, hr, ?_⟩
  exact r.commutes (AdjoinSimple.gen ℚ i)

def rotation : L ≃ₐ[ℚ] L := Classical.choose rotation_exists
lemma rotation_a : rotation a = i * a := (Classical.choose_spec rotation_exists).1
lemma rotation_i : rotation i = i := (Classical.choose_spec rotation_exists).2


lemma i_four : i ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, i_sq]
  norm_num

lemma i_six : i ^ 6 = -1 := by
  rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, i_four, i_sq, one_mul]

lemma i_cube : i ^ 3 = -i := by rw [pow_succ, i_sq]; ring

lemma i_ne_neg_i : i ≠ -i := by
  intro h
  have hc := congrArg (fun x : L => (x : ℂ).im) h
  norm_num [i] at hc

lemma a_ne_neg_a : a ≠ -a := by
  intro h
  have h2 : (2 : L) * a = 0 := by linear_combination h
  exact a_ne_zero ((mul_eq_zero.mp h2).resolve_left (by norm_num))

lemma rotation_pow_a (n : ℕ) : (rotation ^ n) a = i ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, rotation_i, rotation_a, pow_succ]
    ring

lemma rotation_pow_i (n : ℕ) : (rotation ^ n) i = i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, rotation_i]

lemma rotation_four : rotation ^ 4 = 1 := by
  apply automorphism_ext
  · simp [rotation_pow_a, i_four]
  · simp [rotation_pow_i]

lemma rotation_sq_ne_one : rotation ^ 2 ≠ 1 := by
  intro h
  have ha := AlgEquiv.congr_fun h a
  simp only [rotation_pow_a, i_sq, neg_one_mul, AlgEquiv.one_apply] at ha
  exact a_ne_neg_a ha.symm

lemma rotation_order : orderOf rotation = 4 := by
  exact orderOf_eq_prime_pow (p := 2) (n := 1)
    (by simpa using rotation_sq_ne_one) (by simpa using rotation_four)

lemma conjugation_order : orderOf conjugation = 2 := by
  apply orderOf_eq_prime conjugation_sq
  intro h
  have hi := AlgEquiv.congr_fun h i
  simp only [conjugation_i, AlgEquiv.one_apply] at hi
  exact i_ne_neg_i hi.symm

lemma dihedral_relation : conjugation * rotation * conjugation = rotation⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  apply automorphism_ext
  · simp only [AlgEquiv.mul_apply, rotation_a, conjugation_a, conjugation_i,
      rotation_i, map_mul, map_neg, AlgEquiv.one_apply]
    calc
      - -i * (-i * a) = -(i ^ 2) * a := by ring
      _ = a := by rw [i_sq]; ring
  · simp [AlgEquiv.mul_apply, rotation_i, conjugation_i]

lemma automorphism_card : Nat.card (L ≃ₐ[ℚ] L) = 8 :=
  (IsGalois.card_aut_eq_finrank ℚ L).trans splittingField_degree

/-- In Mathlib, sr j means s*r^j. -/
def dihedralMapFun : DihedralGroup 4 → (L ≃ₐ[ℚ] L)
  | .r j => rotation ^ j.val
  | .sr j => conjugation * rotation ^ j.val

lemma zmod_four_cases (j : ZMod 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
  revert j
  decide

lemma dihedralMapFun_mul (x y : DihedralGroup 4) :
    dihedralMapFun (x * y) = dihedralMapFun x * dihedralMapFun y := by
  rcases x with ⟨j⟩ | ⟨j⟩ <;> rcases y with ⟨k⟩ | ⟨k⟩ <;>
    simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;>
    rcases zmod_four_cases j with rfl | rfl | rfl | rfl <;>
    rcases zmod_four_cases k with rfl | rfl | rfl | rfl <;>
    simp only [dihedralMapFun] <;>
    norm_num only [sub_eq_add_neg, ZMod.val_add (n := 4), ZMod.neg_val (n := 4),
      ZMod.val_zero (n := 4), ZMod.val_one_eq_one_mod 4, ZMod.val_ofNat 4,
      show (1 : ZMod 4) ≠ 0 from by decide,
      show (2 : ZMod 4) ≠ 0 from by decide,
      show (3 : ZMod 4) ≠ 0 from by decide] <;>
    apply automorphism_ext <;>
    simp only [AlgEquiv.mul_apply, rotation_pow_a, rotation_pow_i,
      conjugation_a, conjugation_i, map_mul, map_pow, map_neg,
      AlgEquiv.one_apply, pow_zero, pow_one, one_mul] <;>
    norm_num [rotation_a, rotation_i, conjugation_a, conjugation_i, i_sq, i_cube, i_four] <;>
    (try ring_nf) <;> (try simp [i_sq, i_cube, i_four, i_six])


def dihedralHom : DihedralGroup 4 →* (L ≃ₐ[ℚ] L) where
  toFun := dihedralMapFun
  map_one' := by
    change rotation ^ (0 : ZMod 4).val = 1
    rfl
  map_mul' := dihedralMapFun_mul

lemma dihedralHom_injective : Function.Injective dihedralHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  change x = 1
  change dihedralMapFun x = 1 at hx
  cases x with
  | r j =>
    rcases zmod_four_cases j with rfl | rfl | rfl | rfl
    · rfl
    all_goals
      have ha := congrArg (fun σ : L ≃ₐ[ℚ] L => σ a) hx
      simp only [dihedralMapFun, rotation_pow_a, AlgEquiv.one_apply] at ha
      norm_num only [ZMod.val_one_eq_one_mod 4, ZMod.val_ofNat 4] at ha
      have hre := congrArg (fun x : L => (x : ℂ).re) ha
      norm_num [a, i, aComplex, Complex.mul_re, Complex.mul_im, pow_succ] at hre
      nlinarith [aReal_pos]
  | sr j =>
    have hi := congrArg (fun σ : L ≃ₐ[ℚ] L => σ i) hx
    simp only [dihedralMapFun, AlgEquiv.mul_apply, rotation_pow_i, conjugation_i,
      AlgEquiv.one_apply] at hi
    exact (i_ne_neg_i hi.symm).elim

def dihedralEquiv : DihedralGroup 4 ≃* (L ≃ₐ[ℚ] L) :=
  MulEquiv.ofBijective dihedralHom (dihedralHom_injective.bijective_of_nat_card_le (by
    rw [automorphism_card, DihedralGroup.nat_card]))

lemma dihedralEquiv_rotation : dihedralEquiv (.r 1) = rotation := by
  change rotation ^ (1 : ZMod 4).val = rotation
  rfl

lemma dihedralEquiv_conjugation : dihedralEquiv (.sr 0) = conjugation := by
  change conjugation * rotation ^ (0 : ZMod 4).val = conjugation
  simp

lemma generators_generate :
    Subgroup.closure ({rotation, conjugation} : Set (L ≃ₐ[ℚ] L)) = ⊤ := by
  let H := Subgroup.closure ({rotation, conjugation} : Set (L ≃ₐ[ℚ] L))
  have hr : rotation ∈ H := Subgroup.subset_closure (by simp)
  have hs : conjugation ∈ H := Subgroup.subset_closure (by simp)
  apply (Subgroup.eq_top_iff' _).mpr
  intro σ
  obtain ⟨x, rfl⟩ := dihedralEquiv.surjective σ
  cases x with
  | r j =>
    change rotation ^ j.val ∈ H
    exact H.pow_mem hr _
  | sr j =>
    change conjugation * rotation ^ j.val ∈ H
    exact H.mul_mem hs (H.pow_mem hr _)

lemma automorphism_data : AutomorphismData rotation conjugation :=
  ⟨rotation_a, rotation_i, conjugation_a, conjugation_i, rotation_four, conjugation_sq,
    dihedral_relation, generators_generate, automorphism_card, dihedralEquiv,
    dihedralEquiv_rotation, dihedralEquiv_conjugation⟩


lemma rotations_card : Nat.card (rotations rotation) = 4 :=
  (Nat.card_zpowers rotation).trans rotation_order
lemma reflection_card : Nat.card (reflection conjugation) = 2 :=
  (Nat.card_zpowers conjugation).trans conjugation_order

lemma rotations_index : (rotations rotation).index = 2 := by
  have h := (rotations rotation).card_mul_index
  rw [rotations_card, automorphism_card] at h
  omega

lemma reflection_index : (reflection conjugation).index = 4 := by
  have h := (reflection conjugation).card_mul_index
  rw [reflection_card, automorphism_card] at h
  omega

lemma fixes_adjoin_simple (σ : L ≃ₐ[ℚ] L) (x : L) (hx : σ x = x) :
    σ ∈ (adjoin ℚ {x}).fixingSubgroup := by
  apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
  intro y hy
  refine adjoin_induction ℚ (motive := fun y _ => σ y = y) ?_ ?_ ?_ ?_ ?_ hy
  · intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hx
  · intro q
    exact σ.commutes q
  · intro y z _ _ hy hz
    rw [map_add, hy, hz]
  · intro y _ hy
    rw [map_inv₀, hy]
  · intro y z _ _ hy hz
    rw [map_mul, hy, hz]

lemma rotations_fix_rationalI : rotations rotation ≤ rationalI.fixingSubgroup :=
  Subgroup.zpowers_le.mpr (fixes_adjoin_simple rotation i rotation_i)

lemma reflection_fixes_rationalA : reflection conjugation ≤ rationalA.fixingSubgroup :=
  Subgroup.zpowers_le.mpr (fixes_adjoin_simple conjugation a conjugation_a)

lemma rotations_fixedField : fixedField (rotations rotation) = rationalI := by
  have hle : rationalI ≤ fixedField (rotations rotation) :=
    (le_iff_le _ _).mpr rotations_fix_rationalI
  have hdeg : Module.finrank ℚ (fixedField (rotations rotation)) = 2 := by
    exact (D07.Ch14.DegreeIndex.degree_index ℚ L (rotations rotation)).2.1.trans rotations_index
  exact (eq_of_le_of_finrank_eq hle (rationalI_degree.trans hdeg.symm)).symm

lemma reflection_fixedField : fixedField (reflection conjugation) = rationalA := by
  have hle : rationalA ≤ fixedField (reflection conjugation) :=
    (le_iff_le _ _).mpr reflection_fixes_rationalA
  have hdeg : Module.finrank ℚ (fixedField (reflection conjugation)) = 4 := by
    exact (D07.Ch14.DegreeIndex.degree_index ℚ L (reflection conjugation)).2.1.trans reflection_index
  exact (eq_of_le_of_finrank_eq hle (rationalA_degree.trans hdeg.symm)).symm

lemma rotations_normal : (rotations rotation).Normal :=
  Subgroup.normal_of_index_eq_two rotations_index

lemma rotation_inv_a : rotation⁻¹ a = -i * a := by
  apply rotation.injective
  change rotation (rotation.symm a) = rotation (-i * a)
  rw [rotation.apply_symm_apply, map_mul, map_neg, rotation_i, rotation_a]
  calc
    a = -(i ^ 2) * a := by rw [i_sq]; ring
    _ = -i * (i * a) := by ring

lemma reflection_not_normal : ¬ (reflection conjugation).Normal := by
  intro hn
  have hmem := hn.conj_mem conjugation (Subgroup.mem_zpowers conjugation) rotation
  have hfix := (mem_fixingSubgroup_iff _ _).mp (reflection_fixes_rationalA hmem)
    a (mem_adjoin_simple_self ℚ a)
  simp only [AlgEquiv.mul_apply, rotation_inv_a, map_mul, map_neg,
    conjugation_i, conjugation_a, rotation_i, rotation_a] at hfix
  have hneg : -a = a := by
    calc
      -a = i ^ 2 * a := by rw [i_sq]; ring
      _ = i * (i * a) := by ring
      _ = a := by simpa only [neg_neg] using hfix
  exact a_ne_neg_a hneg.symm

lemma rationalI_galois : IsGalois ℚ rationalI := by
  rw [← rotations_fixedField]
  exact (D07.Ch14.NormalQuotient.galois_iff_normal ℚ L (rotations rotation)).mpr rotations_normal

lemma rationalA_not_normal : ¬ Normal ℚ rationalA := by
  intro hn
  have hgal : IsGalois ℚ rationalA :=
    { to_normal := hn, to_isSeparable := inferInstance }
  apply reflection_not_normal
  apply (D07.Ch14.NormalQuotient.galois_iff_normal ℚ L (reflection conjugation)).mp
  change IsGalois ℚ (fixedField (reflection conjugation))
  rw [reflection_fixedField]
  exact hgal

lemma subgroup_data : SubgroupData rotation conjugation :=
  ⟨rotations_card, rotations_index, reflection_card, reflection_index,
    rotations_fixedField, reflection_fixedField, rotations_normal, reflection_not_normal,
    rationalI_galois, rationalA_not_normal⟩

theorem quartic_splitting_example : Example :=
  ⟨root_data, field_data, rotation, conjugation, automorphism_data, subgroup_data⟩

end D07.Ch14.QuarticSplittingExample
