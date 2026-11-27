import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.LaurentCechCohomology
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwists

noncomputable section

open CategoryTheory
open scoped BigOperators DirectSum

namespace DerivedFormalization.LaurentCechCohomology

open ProjectiveTwists (Index Polynomials ChartLocalization DegreePiece chartProduct chartDenominator
  variablePolynomial grading localizationRestriction)

universe u

variable (k : Type u) [Field k] {n : ℕ}

private theorem sign_sq (J : Finset (Index n)) (i : Index n) :
    sign k J i * sign k J i = 1 := by
  simp [sign, ← mul_pow]

private theorem sign_erase (J : Finset (Index n)) {i j : Index n} (hi : i ∈ J) :
    sign k J j = if i < j then -sign k (J.erase i) j else sign k (J.erase i) j := by
  classical
  by_cases h : i < j
  · have hmem : i ∈ J.filter (· < j) := Finset.mem_filter.mpr ⟨hi, h⟩
    simp only [sign, h, ite_true, Finset.filter_erase]
    rw [← Finset.card_erase_add_one hmem, pow_succ, mul_neg_one]
  · have hmem : i ∉ J.filter (· < j) := by simp [h]
    simp [sign, h, Finset.filter_erase]

private theorem sign_erase_self (J : Finset (Index n)) {i : Index n} (hi : i ∈ J) :
    sign k J i = sign k (J.erase i) i := by
  rw [sign_erase k J (j := i) hi, ite_eq_right (lt_irrefl _)]

private theorem sign_erase_swap (J : Finset (Index n)) {i j : Index n}
    (hi : i ∈ J) (hj : j ∈ J) (hne : i ≠ j) :
    sign k J i * sign k (J.erase i) j = -(sign k J j * sign k (J.erase j) i) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [sign_erase k J hj, ite_eq_right (not_lt_of_ge h.le), sign_erase k J (j := j) hi, ite_eq_left h]
    ring
  · rw [sign_erase k J hj, ite_eq_left h, sign_erase k J (j := j) hi, ite_eq_right (not_lt_of_ge h.le)]
    ring

private theorem deleteSum_square (x : Finset (Index n) → k) (J : Finset (Index n)) :
    deleteSum k (deleteSum k x) J = 0 := by
  classical
  let D := (J ×ˢ J).filter fun ij ↦ ij.1 ≠ ij.2
  let f : Index n × Index n → k := fun ij ↦
    (sign k J ij.1 * sign k (J.erase ij.1) ij.2) * x ((J.erase ij.1).erase ij.2)
  have hD (ij : Index n × Index n) :
      ij ∈ D ↔ ij.1 ∈ J ∧ ij.2 ∈ J ∧ ij.1 ≠ ij.2 := by
    simp [D, and_assoc]
  have hz : ∑ ij ∈ D, f ij = 0 := by
    refine Finset.sum_involution (fun ij _ ↦ ij.swap) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ hij
      obtain ⟨hi, hj, hne⟩ := (hD _).mp hij
      change (sign k J i * sign k (J.erase i) j) * x ((J.erase i).erase j) +
        (sign k J j * sign k (J.erase j) i) * x ((J.erase j).erase i) = 0
      have he : (J.erase i).erase j = (J.erase j).erase i := by
        ext t; simp [Finset.mem_erase, and_left_comm]
      rw [sign_erase_swap k J hi hj hne, he]
      ring
    · rintro ⟨i, j⟩ hij _ heq
      exact ((hD _).mp hij).2.2 (congrArg Prod.snd heq)
    · intro ij hij
      obtain ⟨hi, hj, hne⟩ := (hD _).mp hij
      exact (hD _).mpr ⟨hj, hi, Ne.symm hne⟩
    · rintro ⟨i, j⟩ hij
      rfl
  rw [← hz]
  dsimp only [D]
  rw [Finset.sum_filter, Finset.sum_product]
  unfold deleteSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, ← Finset.sum_filter]
  have he : J.erase i = J.filter (fun j ↦ i ≠ j) := by ext j; simp [ne_comm, and_comm]
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [f, he, mul_assoc]

theorem fixedSquareZero : Expected.fixedSquareZero.{u} := by
  intro k _ n augmented a p
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext J
  exact deleteSum_square k x.val J

theorem differentialSquareZero : Expected.differentialSquareZero.{u} := by
  intro k _ n m p
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro a
  change fixedD k false a.val (p + 1) (fixedD k false a.val p (x a)) = 0
  exact DFunLike.congr_fun (fixedSquareZero k n false a.val p) (x a)

private theorem delete_insert_identity (j : Index n) (x : Finset (Index n) → k)
    (J : Finset (Index n)) :
    deleteSum k (insertAt k j x) J + insertAt k j (deleteSum k x) J = x J := by
  classical
  by_cases hj : j ∈ J
  · rw [insertAt, ite_eq_left hj, add_zero, deleteSum, ← Finset.sum_erase_add _ _ hj]
    have hz : ∑ i ∈ J.erase j, sign k J i * insertAt k j x (J.erase i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hh := Finset.mem_erase.mp hi
      simp [insertAt, Finset.mem_erase, hj, Ne.symm hh.1]
    rw [hz, zero_add, insertAt, ite_eq_right (Finset.notMem_erase _ _), Finset.insert_erase hj,
      ← mul_assoc, ← sign_erase_self k J hj, sign_sq, one_mul]
  · rw [insertAt, ite_eq_right hj]
    change (∑ i ∈ J, sign k J i * insertAt k j x (J.erase i)) +
      sign k J j * (∑ i ∈ insert j J, sign k (insert j J) i * x ((insert j J).erase i)) = x J
    rw [Finset.sum_insert hj, mul_add, ← mul_assoc, sign_erase_self k _ (Finset.mem_insert_self _ _),
      Finset.erase_insert hj, sign_sq, one_mul, Finset.mul_sum]
    have he : (∑ i ∈ J, sign k J i * insertAt k j x (J.erase i)) =
        -(∑ i ∈ J, sign k J j * (sign k (insert j J) i * x ((insert j J).erase i))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
      rw [insertAt, ite_eq_right (fun h ↦ hj (Finset.erase_subset _ _ h))]
      have hins := sign_erase k (insert j J) (i := j) (j := i)
        (Finset.mem_insert_self j J)
      rw [Finset.erase_insert hj] at hins
      rw [Finset.erase_insert_of_ne (Ne.symm hij)]
      rcases lt_or_gt_of_ne hij with h | h
      · rw [hins, ite_eq_right (not_lt_of_ge h.le), sign_erase k J (j := j) hi, ite_eq_left h]
        ring
      · rw [hins, ite_eq_left h, sign_erase k J (j := j) hi, ite_eq_right (not_lt_of_ge h.le)]
        ring
    rw [he]
    ring

theorem insertionContraction : Expected.insertionContraction.{u} := by
  intro k _ n augmented a j hj haug p x
  refine ⟨?_, delete_insert_identity k j x.val⟩
  intro J hJ
  by_cases hjJ : j ∈ J
  · simp [insertAt, hjJ]
  · rw [insertAt, ite_eq_right hjJ, x.property _ (fun h ↦ hJ ?_), mul_zero]
    refine ⟨?_, ?_, ?_⟩
    · have hcard := Finset.card_insert_of_notMem hjJ
      have := h.1
      omega
    · intro i hi
      exact (Finset.mem_insert.mp (h.2.1 hi)).resolve_left (fun e ↦ hj (e ▸ hi))
    · refine haug.imp_right (fun ⟨i, hi⟩ ↦ ⟨i, ?_⟩)
      exact (Finset.mem_insert.mp (h.2.1 hi)).resolve_left (fun e ↦ hj (e ▸ hi))

theorem polynomialGrading : Expected.polynomialGrading.{u} := by
  intro k _ n
  constructor
  · intro d
    ext p
    change (∀ a : Index n →₀ ℕ, p.coeff a ≠ 0 → (∑ i, (a i : ℤ)) = d) ↔
      p ∈ MvPolynomial.homogeneousSubmodule (Index n) k d
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    rw [AddMonoidAlgebra.mem_supported, Set.subset_def]
    simp only [SetLike.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq, Finsupp.degree_eq_sum]
    norm_cast
  · intro m hm
    apply eq_bot_iff.mpr
    intro p hp
    rw [Submodule.mem_bot]
    apply MvPolynomial.ext
    intro a
    by_contra h
    have he := hp a (by simpa using h)
    have hsum : 0 ≤ ∑ i, (a i : ℤ) := Finset.sum_nonneg fun i _ ↦ Int.natCast_nonneg (a i)
    omega


private theorem naturalExponent_injective (n : ℕ) : Function.Injective (naturalExponent n) := by
  intro a b h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

private theorem naturalExponent_exists {a : ExponentVector n} (h : ∀ i, 0 ≤ a i) :
    ∃ b : Index n →₀ ℕ, naturalExponent n b = a := by
  classical
  refine ⟨Finsupp.equivFunOnFinite.symm (fun i ↦ (a i).toNat), ?_⟩
  funext i
  change ((Finsupp.equivFunOnFinite.symm (fun i ↦ (a i).toNat) : Index n →₀ ℕ) i : ℤ) = a i
  simp [Int.toNat_of_nonneg (h i)]

private theorem polynomialToLaurent_coeff (f : Polynomials k n) (a : Index n →₀ ℕ) :
    (polynomialToLaurent k n f).coeff (naturalExponent n a) = f.coeff a :=
  Finsupp.mapDomain_apply_of_injective (naturalExponent_injective n) f.coeff a

private theorem polynomialToLaurent_coeff_zero (f : Polynomials k n) {a : ExponentVector n}
    (h : a ∉ Set.range (naturalExponent n)) :
    (polynomialToLaurent k n f).coeff a = 0 :=
  Finsupp.mapDomain_of_notMem_range f.coeff a h

private theorem polynomialToLaurent_injective (n : ℕ) :
    Function.Injective (polynomialToLaurent k n) :=
  AddMonoidAlgebra.mapDomain_injective (naturalExponent_injective n)

private theorem chartToLaurent_injective (J : Finset (Index n)) :
    Function.Injective (chartToLaurent k n J) := by
  change Function.Injective (IsLocalization.lift (S := ChartLocalization k n J)
    (chartProduct_maps_to_unit k n J))
  rw [IsLocalization.lift_injective_iff]
  intro a b
  constructor
  · intro h
    have he := congrArg (chartToLaurent k n J) h
    simpa [chartToLaurent, IsLocalization.liftAlgHom_apply] using he
  · intro h
    congr 1
    exact polynomialToLaurent_injective k n h

private theorem chartToLaurent_restrict {J K : Finset (Index n)} (h : J ⊆ K)
    (s : ChartLocalization k n J) :
    chartToLaurent k n K (localizationRestriction k n h s) = chartToLaurent k n J s := by
  have he : (chartToLaurent k n K).toRingHom.comp (localizationRestriction k n h) =
      (chartToLaurent k n J).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (chartProduct k n J))
    apply RingHom.ext
    intro f
    change chartToLaurent k n K (localizationRestriction k n h (algebraMap _ _ f)) =
      chartToLaurent k n J (algebraMap _ _ f)
    rw [localizationRestriction, IsLocalization.Away.lift_eq]
    simp [chartToLaurent, IsLocalization.liftAlgHom_apply]
  exact DFunLike.congr_fun he s

private abbrev denominatorShift (J : Finset (Index n)) (t : ℕ) : ExponentVector n :=
  t • characteristic n J

private theorem denominatorShift_apply (J : Finset (Index n)) (t : ℕ) (i : Index n) :
    denominatorShift J t i = if i ∈ J then (t : ℤ) else 0 := by
  simp [denominatorShift, characteristic]

private theorem denominatorShift_sum (J : Finset (Index n)) (t : ℕ) :
    ∑ i, denominatorShift J t i = (t : ℤ) * J.card := by
  classical
  simp_rw [denominatorShift_apply]
  rw [← Finset.sum_filter]
  simp [mul_comm]

private theorem polynomialToLaurent_denominator (J : Finset (Index n)) (t : ℕ) :
    polynomialToLaurent k n (chartProduct k n J ^ t) =
      AddMonoidAlgebra.single (denominatorShift J t) 1 := by
  rw [map_pow, polynomialToLaurent_chartProduct]
  induction t with
  | zero => simp [AddMonoidAlgebra.one_def]
  | succ t ih => simp [pow_succ, ih, add_mul]

private theorem chartToLaurent_mk (J : Finset (Index n)) (f : Polynomials k n) (t : ℕ) :
    chartToLaurent k n J (Localization.mk f (chartDenominator k n J t)) =
      polynomialToLaurent k n f * AddMonoidAlgebra.single (-denominatorShift J t) 1 := by
  rw [Localization.mk_eq_mk']
  change IsLocalization.lift (chartProduct_maps_to_unit k n J) _ = _
  apply (IsLocalization.lift_mk'_spec (chartProduct_maps_to_unit k n J) _ _ _).mpr
  change polynomialToLaurent k n f =
    polynomialToLaurent k n (chartProduct k n J ^ t) *
      (polynomialToLaurent k n f * AddMonoidAlgebra.single (-denominatorShift J t) 1)
  rw [polynomialToLaurent_denominator]
  rw [mul_left_comm, AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul,
    ← AddMonoidAlgebra.one_def, mul_one]

private theorem chartToLaurent_mk_coeff (J : Finset (Index n)) (f : Polynomials k n) (t : ℕ)
    (a : ExponentVector n) :
    (chartToLaurent k n J (Localization.mk f (chartDenominator k n J t))).coeff a =
      (polynomialToLaurent k n f).coeff (a + denominatorShift J t) := by
  rw [chartToLaurent_mk]
  conv_lhs => rw [show a = (a + denominatorShift J t) + -denominatorShift J t by abel]
  rw [AddMonoidAlgebra.coeff_mul_single_add, mul_one]

private theorem shiftedNatural_mem (J : Finset (Index n)) (t : ℕ) (b : Index n →₀ ℕ) (m : ℤ) :
    naturalExponent n b - denominatorShift J t ∈ exponentSet n m J ↔
      (∑ i, (b i : ℤ)) - (t : ℤ) * J.card = m := by
  have hsub : negativeSupport n (naturalExponent n b - denominatorShift J t) ⊆ J := by
    intro i hi
    by_contra h
    have hn := (Finset.mem_filter.mp hi).2
    change (b i : ℤ) - denominatorShift J t i < 0 at hn
    rw [denominatorShift_apply, ite_eq_right h] at hn
    omega
  change ((∑ i, (naturalExponent n b - denominatorShift J t) i) = m ∧ _) ↔ _
  rw [and_iff_left hsub]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, denominatorShift_sum]
  rfl

private theorem chartPiece_mk_iff (J : Finset (Index n)) (f : Polynomials k n) (t : ℕ) (m : ℤ) :
    Localization.mk f (chartDenominator k n J t) ∈ chartPiece k n m J ↔
      f ∈ polynomialDegree k n (m + (t : ℤ) * J.card) := by
  change chartToLaurent k n J (Localization.mk f (chartDenominator k n J t)) ∈
    AddMonoidAlgebra.supported k k (exponentSet n m J) ↔ _
  rw [AddMonoidAlgebra.mem_supported, Set.subset_def]
  simp only [SetLike.mem_coe, Finsupp.mem_support_iff, chartToLaurent_mk_coeff]
  constructor
  · intro h b hb
    have ha := h (naturalExponent n b - denominatorShift J t)
      (by simpa [polynomialToLaurent_coeff] using hb)
    have hs := (shiftedNatural_mem J t b m).mp ha
    omega
  · intro h a ha
    have hmem : a + denominatorShift J t ∈ Set.range (naturalExponent n) :=
      by_contra fun hn ↦ ha (polynomialToLaurent_coeff_zero k f hn)
    obtain ⟨b, hb⟩ := hmem
    have ha' : a = naturalExponent n b - denominatorShift J t := eq_sub_of_add_eq hb.symm
    rw [← hb, polynomialToLaurent_coeff] at ha
    rw [ha', shiftedNatural_mem]
    have hs := h b ha
    omega


private theorem chartPiece_iff_degreePiece (J : Finset (Index n)) (hJ : J.Nonempty)
    (m : ℤ) (s : ChartLocalization k n J) :
    s ∈ chartPiece k n m J ↔ ∃ a : DegreePiece k n J m, a.val = s := by
  constructor
  · intro hs
    by_cases hz : s = 0
    · let t := (-m).toNat
      have ht : -m ≤ (t : ℤ) := by
        dsimp [t]
        omega
      have hcard : 1 ≤ (J.card : ℤ) := by exact_mod_cast Finset.card_pos.mpr hJ
      have hmul : (t : ℤ) ≤ (t : ℤ) * J.card := by
        simpa using mul_le_mul_of_nonneg_left hcard (Int.natCast_nonneg t)
      have hd : 0 ≤ m + (t : ℤ) * J.card := by omega
      refine ⟨⟨s, 0, t, (m + (t : ℤ) * J.card).toNat, Submodule.zero_mem _, ?_, ?_⟩, rfl⟩
      · rw [Int.toNat_of_nonneg hd, Nat.cast_mul]
        omega
      · simp [hz, Localization.mk_eq_mk']
    obtain ⟨f, y, hy⟩ := IsLocalization.exists_mk'_eq
      (M := Submonoid.powers (chartProduct k n J)) s
    obtain ⟨t, ht⟩ := y.property
    have he : y = chartDenominator k n J t := Subtype.ext ht.symm
    rw [he, ← Localization.mk_eq_mk'] at hy
    have hf := (chartPiece_mk_iff k J f t m).mp (by simpa only [hy] using hs)
    have hfne : f ≠ 0 := by
      intro h
      rw [h, Localization.mk_eq_mk', IsLocalization.mk'_zero] at hy
      exact hz hy.symm
    obtain ⟨b, hb⟩ := MvPolynomial.exists_coeff_ne_zero hfne
    have hsum := hf b hb
    have hh : 0 ≤ m + (t : ℤ) * J.card := by
      rw [← hsum]
      positivity
    let d := (m + (t : ℤ) * J.card).toNat
    have hd : (d : ℤ) = m + (t : ℤ) * J.card := Int.toNat_of_nonneg hh
    refine ⟨⟨s, f, t, d, ?_, ?_, hy.symm⟩, rfl⟩
    · rw [← (polynomialGrading k n).1 d, hd]
      exact hf
    · rw [hd, Nat.cast_mul]
      omega
  · rintro ⟨⟨s, f, t, d, hf, hm, rfl⟩, rfl⟩
    apply (chartPiece_mk_iff k J f t m).mpr
    rw [← (polynomialGrading k n).1 d] at hf
    rwa [show m + (t : ℤ) * J.card = (d : ℤ) by push_cast at hm; omega]

private theorem laurentSingle_in_chartRange (J : Finset (Index n)) (a : ExponentVector n)
    (ha : negativeSupport n a ⊆ J) :
    AddMonoidAlgebra.single a (1 : k) ∈ LinearMap.range (chartToLaurent k n J).toLinearMap := by
  classical
  let t := ∑ i, (a i).natAbs
  have hpos (i : Index n) : 0 ≤ (a + denominatorShift J t) i := by
    change 0 ≤ a i + denominatorShift J t i
    rw [denominatorShift_apply]
    by_cases hi : i ∈ J
    · rw [ite_eq_left hi]
      have ht : (a i).natAbs ≤ t :=
        Finset.single_le_sum (f := fun i ↦ (a i).natAbs) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      have habs : -a i ≤ ((a i).natAbs : ℤ) := by omega
      omega
    · rw [ite_eq_right hi, add_zero]
      exact le_of_not_gt (fun h ↦ hi (ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
  obtain ⟨b, hb⟩ := naturalExponent_exists hpos
  refine ⟨Localization.mk (MvPolynomial.monomial b 1) (chartDenominator k n J t), ?_⟩
  change chartToLaurent k n J _ = _
  rw [chartToLaurent_mk]
  change AddMonoidAlgebra.mapDomain (naturalExponent n) (AddMonoidAlgebra.single b (1 : k)) *
    AddMonoidAlgebra.single (-denominatorShift J t) 1 = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, hb]
  simp

private def chartLaurentEquiv (J : Finset (Index n)) (m : ℤ) :
    chartPiece k n m J ≃ₗ[k] laurentPiece k n m J := by
  let f := ((chartToLaurent k n J).toLinearMap.comp (chartPiece k n m J).subtype).codRestrict
    (laurentPiece k n m J) (fun x ↦ x.property)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact chartToLaurent_injective k J (congrArg Subtype.val h)
  · intro y
    have hrange : laurentPiece k n m J ≤ LinearMap.range (chartToLaurent k n J).toLinearMap := by
      unfold laurentPiece
      rw [AddMonoidAlgebra.supported_eq_span_single]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      exact laurentSingle_in_chartRange k J a ha.2
    obtain ⟨x, hx⟩ := hrange y.property
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change (chartToLaurent k n J) x ∈ laurentPiece k n m J
    exact hx.symm ▸ y.property

private theorem chartLaurentEquiv_apply (J : Finset (Index n)) (m : ℤ)
    (x : chartPiece k n m J) :
    (chartLaurentEquiv k J m x).val = chartToLaurent k n J x.val := rfl

theorem chartCoefficientComparison : Expected.chartCoefficientComparison.{u} := by
  intro k _ n
  refine ⟨chartPiece_iff_degreePiece k, fun _ _ ↦ chartToLaurent_restrict k, ?_⟩
  intro J m
  let e : laurentPiece k n m J ≃ₗ[k] (exponentSet n m J →₀ k) :=
    AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k) (exponentSet n m J)
  refine ⟨e.symm.trans (chartLaurentEquiv k J m).symm, fun f ↦ ?_⟩
  have he := chartLaurentEquiv_apply k J m ((chartLaurentEquiv k J m).symm (e.symm f))
  rw [LinearEquiv.apply_symm_apply] at he
  change chartToLaurent k n J ((chartLaurentEquiv k J m).symm (e.symm f)).val = _
  rw [← he]
  apply AddMonoidAlgebra.coeff_injective
  change ((Finsupp.supportedEquivFinsupp (R := k) (exponentSet n m J)).symm f).val =
    Finsupp.mapDomain Subtype.val f
  classical
  rw [Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_eq_embDomain_subtype]
  exact Finsupp.embDomain_eq_mapDomain (Function.Embedding.subtype _) f


private theorem chartLaurentEquiv_symm_apply (J : Finset (Index n)) (m : ℤ)
    (x : laurentPiece k n m J) :
    chartToLaurent k n J ((chartLaurentEquiv k J m).symm x).val = x.val := by
  rw [← chartLaurentEquiv_apply, LinearEquiv.apply_symm_apply]

private theorem laurentPiece_coeff_zero {J : Finset (Index n)} {m : ℤ}
    (x : laurentPiece k n m J) {a : ExponentVector n} (ha : a ∉ exponentSet n m J) :
    x.val.coeff a = 0 :=
  (AddMonoidAlgebra.mem_supported'.mp x.property) a ha

private def termCoeff {m p : ℤ} (x : Term k n m p) (J : Faces n p) (a : ExponentVector n) :
    k := if h : (∑ i, a i) = m then (x ⟨a, h⟩).val J.val else 0

private theorem termCoeff_zero {m p : ℤ} (x : Term k n m p) (J : Faces n p)
    (a : ExponentVector n) (ha : a ∉ exponentSet n m J.val) :
    termCoeff k x J a = 0 := by
  unfold termCoeff
  split
  · rename_i h
    exact (x ⟨a, h⟩).property _ (fun hh ↦ ha ⟨h, hh.2.1⟩)
  · rfl

private def termLaurent {m p : ℤ} (x : Term k n m p) (J : Faces n p) :
    laurentPiece k n m J.val := by
  classical
  let c := termCoeff k x J
  have hs : ∀ a, a ∈ (x.support.image Subtype.val).filter (fun b ↦ c b ≠ 0) ↔ c a ≠ 0 := by
    intro a
    rw [Finset.mem_filter]
    refine and_iff_right_of_imp fun ha ↦ ?_
    have hh : (∑ i, a i) = m := by
      by_contra h
      exact ha (by simp [c, termCoeff, h])
    apply Finset.mem_image.mpr
    refine ⟨⟨a, hh⟩, DFinsupp.mem_support_iff.mpr ?_, rfl⟩
    intro hz
    apply ha
    simp [c, termCoeff, hh, hz]
  refine ⟨AddMonoidAlgebra.ofCoeff ⟨_, c, hs⟩, AddMonoidAlgebra.mem_supported'.mpr ?_⟩
  exact termCoeff_zero k x J

private def transposeTerm (m p : ℤ) :
    Term k n m p →ₗ[k] (∀ J : Faces n p, laurentPiece k n m J.val) where
  toFun x J := termLaurent k x J
  map_add' x y := by
    funext J
    apply Subtype.ext
    apply AddMonoidAlgebra.ext
    ext a
    change termCoeff k (x + y) J a = termCoeff k x J a + termCoeff k y J a
    by_cases h : (∑ i, a i) = m <;> simp [termCoeff, h]
  map_smul' r x := by
    funext J
    apply Subtype.ext
    apply AddMonoidAlgebra.ext
    ext a
    change termCoeff k (r • x) J a = r * termCoeff k x J a
    by_cases h : (∑ i, a i) = m
    · simp only [termCoeff, h, dite_true]
      rfl
    · simp [termCoeff, h]

private theorem transposeTerm_coeff {m p : ℤ} (x : Term k n m p) (J : Faces n p)
    (a : Exponents n m) :
    (transposeTerm k m p x J).val.coeff a.val = (x a).val J.val := by
  change termCoeff k x J a.val = _
  simp [termCoeff, a.property]

private theorem transposeTerm_bijective (m p : ℤ) :
    Function.Bijective (transposeTerm k (n := n) m p) := by
  classical
  constructor
  · intro x y h
    apply DFinsupp.ext
    intro a
    apply Subtype.ext
    funext J
    by_cases hJ : J ∈ (Finset.univ : Finset (Finset (Index n))) ∧
      (J.card : ℤ) = p + 1 ∧ J.Nonempty
    · let F : Faces n p := ⟨J, hJ.2⟩
      rw [← transposeTerm_coeff k x F a, ← transposeTerm_coeff k y F a, h]
    · have hbad : ¬ admissible false a.val p J := by
        intro hh
        exact hJ ⟨Finset.mem_univ _, hh.1, hh.2.2.resolve_left (by decide)⟩
      rw [(x a).property J hbad, (y a).property J hbad]
  · intro y
    let : Fintype (Faces n p) := Fintype.ofFinite _
    let S : Finset (ExponentVector n) := Finset.univ.biUnion (fun J : Faces n p ↦ (y J).val.coeff.support)
    let T : Finset (Exponents n m) := S.preimage Subtype.val Subtype.val_injective.injOn
    let col (a : Exponents n m) : Fixed k false a.val p :=
      ⟨fun J ↦ if h : (J.card : ℤ) = p + 1 ∧ J.Nonempty then (y ⟨J, h⟩).val.coeff a.val else 0,
        by
          intro J hJ
          dsimp only
          split
          · rename_i h
            exact laurentPiece_coeff_zero k (y ⟨J, h⟩)
              (fun ha ↦ hJ ⟨h.1, ha.2, Or.inr h.2⟩)
          · rfl⟩
    let x : Term k n m p := DFinsupp.mk T (fun a ↦ col a.val)
    refine ⟨x, ?_⟩
    funext J
    apply Subtype.ext
    apply AddMonoidAlgebra.ext
    ext a
    by_cases ha : (∑ i, a i) = m
    · rw [transposeTerm_coeff k x J (⟨a, ha⟩ : Exponents n m)]
      change ((DFinsupp.mk T (fun a ↦ col a.val) : Term k n m p) ⟨a, ha⟩).val J.val = _
      rw [DFinsupp.mk_apply]
      split
      · change (if h : (J.val.card : ℤ) = p + 1 ∧ J.val.Nonempty then
            (y ⟨J.val, h⟩).val.coeff a else 0) = _
        rw [dite_eq_left J.property]
      · rename_i ht
        change 0 = (y J).val.coeff a
        symm
        apply Finsupp.notMem_support_iff.mp
        intro h
        apply ht
        rw [Finset.mem_preimage]
        exact Finset.mem_biUnion.mpr ⟨J, Finset.mem_univ _, h⟩
    · change termCoeff k x J a = (y J).val.coeff a
      rw [termCoeff, dite_eq_right ha, laurentPiece_coeff_zero k (y J) (fun h ↦ ha h.1)]

private def termLocalizedEquiv (n : ℕ) (m p : ℤ) :
    Term k n m p ≃ₗ[k] LocalizedTerm k n m p :=
  (LinearEquiv.ofBijective (transposeTerm k (n := n) m p) (transposeTerm_bijective k m p)).trans
    (LinearEquiv.piCongrRight fun J ↦ (chartLaurentEquiv k J.val m).symm)

private theorem termLocalizedEquiv_coeff {m p : ℤ} (x : Term k n m p) (J : Faces n p)
    (a : Exponents n m) :
    (chartToLaurent k n J.val (termLocalizedEquiv k n m p x J).val).coeff a.val =
      (x a).val J.val := by
  change (chartToLaurent k n J.val ((chartLaurentEquiv k J.val m).symm (transposeTerm k m p x J)).val).coeff a.val = _
  rw [chartLaurentEquiv_symm_apply, transposeTerm_coeff]

theorem localizedComplexComparison : Expected.localizedComplexComparison.{u} := by
  classical
  intro k _ n m
  refine ⟨termLocalizedEquiv k n m, fun _ ↦ termLocalizedEquiv_coeff k, ?_⟩
  intro p x J
  apply chartToLaurent_injective k J.val
  apply AddMonoidAlgebra.ext
  ext a
  rw [localizedDeleteSum, map_sum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  by_cases ha : (∑ i, a i) = m
  · let a' : Exponents n m := ⟨a, ha⟩
    change (chartToLaurent k n J.val _).coeff a'.val = _
    rw [termLocalizedEquiv_coeff]
    change (∑ i ∈ J.val, sign k J.val i * (x a').val (J.val.erase i)) = _
    apply Finset.sum_congr rfl
    intro i hi
    have hcard : (↑(J.val.erase i).card : ℤ) = p + 1 := by
      have := Finset.card_erase_add_one hi
      have := J.property.1
      omega
    by_cases he : (J.val.erase i).Nonempty
    · rw [dite_eq_left ⟨hcard, he⟩]
      rw [show chartToLaurent k n J.val (_ • _) = sign k J.val i •
        chartToLaurent k n J.val (localizationRestriction k n (Finset.erase_subset i J.val)
          (termLocalizedEquiv k n m p x ⟨J.val.erase i, ⟨hcard, he⟩⟩).val)
        from (chartToLaurent k n J.val).toLinearMap.map_smul _ _]
      rw [chartToLaurent_restrict, AddMonoidAlgebra.coeff_smul]
      change _ = sign k J.val i * (chartToLaurent k n (J.val.erase i) _).coeff a'.val
      exact congrArg (sign k J.val i * ·)
        (termLocalizedEquiv_coeff k x (⟨J.val.erase i, ⟨hcard, he⟩⟩ : Faces n p) a').symm
    · rw [dite_eq_right (fun h ↦ he h.2), map_zero]
      rw [(x a').property _ (fun h ↦ he (h.2.2.resolve_left (by decide)))]
      simp
  · have hz {F : Finset (Index n)} (f : chartPiece k n m F) :
        (chartToLaurent k n F f.val).coeff a = 0 :=
      laurentPiece_coeff_zero k (chartLaurentEquiv k F m f) (fun h ↦ ha h.1)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    split
    · rename_i h
      rw [show chartToLaurent k n J.val (_ • _) = sign k J.val i •
        chartToLaurent k n J.val (localizationRestriction k n (Finset.erase_subset i J.val)
          (termLocalizedEquiv k n m p x ⟨J.val.erase i, h⟩).val)
        from (chartToLaurent k n J.val).toLinearMap.map_smul _ _,
        chartToLaurent_restrict, AddMonoidAlgebra.coeff_smul]
      change sign k J.val i * (chartToLaurent k n (J.val.erase i) _).coeff a = 0
      rw [hz, mul_zero]
    · simp


private theorem fixed_zero_at {aug : Bool} {a : ExponentVector n} {p : ℤ}
    (x : Fixed k aug a p) (h : ∀ J, ¬ admissible aug a p J) :
    x = 0 := by
  apply Subtype.ext
  funext J
  exact x.property J (h J)

private theorem fixed_nonempty_of_card {p : ℤ} {J : Finset (Index n)} (hp : 0 ≤ p)
    (h : (J.card : ℤ) = p + 1) : J.Nonempty := by
  rw [← Finset.card_pos]
  omega

private theorem fixed_full_support_zero {a : ExponentVector n} {p : ℤ}
    (ha : negativeSupport n a = Finset.univ) (hp : p ≠ n)
    (x : Fixed k false a p) : x = 0 := by
  apply fixed_zero_at k x
  intro J hJ
  have he : J = Finset.univ := Finset.eq_univ_of_forall (fun j ↦ (ha ▸ hJ.2.1) (Finset.mem_univ j))
  have hc : J.card = n + 1 := by simp [he]
  have hh := hJ.1
  omega

private theorem term_zero_outside {m p : ℤ} (hp : p < 0 ∨ (n : ℤ) < p)
    (x : Term k n m p) : x = 0 := by
  apply DFinsupp.ext
  intro a
  apply fixed_zero_at k (x a)
  intro J hJ
  have hpos := Finset.card_pos.mpr (hJ.2.2.resolve_left (by decide))
  have hle : J.card ≤ n + 1 := by simpa using Finset.card_le_univ J
  have hc := hJ.1
  omega

private theorem exists_not_in_negativeSupport {a : ExponentVector n}
    (h : negativeSupport n a ≠ Finset.univ) : ∃ j, j ∉ negativeSupport n a := by
  by_contra! h'
  exact h (Finset.eq_univ_of_forall h')

private def insertedPrimitive (a : ExponentVector n) (p : ℤ) (hp : 0 < p)
    (j : Index n) (hj : j ∉ negativeSupport n a) :
    Fixed k false a p →ₗ[k] Fixed k false a (p - 1) where
  toFun x := ⟨insertAt k j x.val, by
    let x' : Fixed k true a p :=
      ⟨x.val, fun J hJ ↦ x.property J (fun h ↦ hJ ⟨h.1, h.2.1, Or.inl rfl⟩)⟩
    intro J hJ
    exact (insertionContraction k n true a j hj (Or.inl rfl) p x').1 J
      (fun h ↦ hJ ⟨h.1, h.2.1, Or.inr (fixed_nonempty_of_card (by omega) h.1)⟩)⟩
  map_add' x y := by
    apply Subtype.ext
    funext J
    by_cases h : j ∈ J <;> simp [insertAt, h, mul_add]
  map_smul' r x := by
    apply Subtype.ext
    funext J
    by_cases h : j ∈ J
    · change insertAt k j (r • x).val J = r * insertAt k j x.val J
      simp [insertAt, h]
    · change insertAt k j (r • x).val J = r * insertAt k j x.val J
      simp only [insertAt, ite_eq_right h]
      exact mul_left_comm _ _ _

private def previousCochain (m p : ℤ) (hp : 0 < p) :
    Term k n m p →ₗ[k] Term k n m (p - 1) := by
  classical
  exact DirectSum.lmap fun a ↦
    if h : negativeSupport n a.val = Finset.univ then 0
    else insertedPrimitive k a.val p hp (exists_not_in_negativeSupport h).choose
      (exists_not_in_negativeSupport h).choose_spec

private theorem previousCochain_delete {m p : ℤ} (hp : 0 < p)
    (x : Term k n m p) (hx : differential k n m p x = 0) (a : Exponents n m)
    (ha : negativeSupport n a.val ≠ Finset.univ) (J : Finset (Index n)) :
    deleteSum k (previousCochain k m p hp x a).val J = (x a).val J := by
  classical
  have h := delete_insert_identity k (exists_not_in_negativeSupport ha).choose (x a).val J
  have hz : deleteSum k (x a).val = 0 := by
    exact congrArg Subtype.val (DFunLike.congr_fun hx a)
  rw [hz] at h
  unfold previousCochain
  rw [DirectSum.lmap_apply, dite_eq_right ha]
  change deleteSum k (insertAt k (exists_not_in_negativeSupport ha).choose (x a).val) J = _
  simpa [insertAt] using h

private theorem previousCochain_full {m p : ℤ} (hp : 0 < p)
    (x : Term k n m p) (a : Exponents n m) (ha : negativeSupport n a.val = Finset.univ) :
    previousCochain k m p hp x a = 0 := by
  classical
  simp [previousCochain, ha]

private theorem degreeZero_column {a : ExponentVector n} (hn : 1 ≤ n)
    (x : Fixed k false a 0) (hx : deleteSum k x.val = 0) (i : Index n) :
    x.val {i} = if negativeSupport n a = ∅ then x.val {(0 : Index n)} else 0 := by
  classical
  by_cases he : negativeSupport n a = ∅
  · rw [ite_eq_left he]
    have h J := delete_insert_identity k (0 : Index n) x.val J
    simp only [hx, show ∀ J, insertAt k (0 : Index n) 0 J = 0 by simp [insertAt], add_zero] at h
    have hs (v : Index n) : deleteSum k (insertAt k (0 : Index n) x.val) {v} =
        x.val {(0 : Index n)} := by
      have hf : ({v} : Finset (Index n)).filter (· < v) = ∅ := by
        ext j
        simp +contextual
      simp [deleteSum, insertAt, sign, hf]
    rw [← h {i}, ← h {(0 : Index n)}, hs, hs]
  · rw [ite_eq_right he]
    by_cases hf : negativeSupport n a = Finset.univ
    · rw [fixed_full_support_zero k hf (by omega) x]
      rfl
    · let j := (exists_not_in_negativeSupport hf).choose
      have h := insertionContraction k n false a j (exists_not_in_negativeSupport hf).choose_spec
        (Or.inr (Finset.nonempty_iff_ne_empty.mpr he)) 0 x
      have hzero : insertAt k j x.val ∅ = 0 :=
        h.1 ∅ (by simp [admissible])
      have hh := h.2 {i}
      rw [hx, show insertAt k j 0 {i} = 0 by simp [insertAt], add_zero] at hh
      simpa [deleteSum, hzero] using hh.symm


private theorem negativeSupport_empty_iff (a : ExponentVector n) :
    negativeSupport n a = ∅ ↔ ∀ i, 0 ≤ a i := by
  constructor
  · intro h i
    apply le_of_not_gt
    intro hi
    have : i ∈ negativeSupport n a := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    simp [h] at this
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact (not_lt_of_ge (h i)) (Finset.mem_filter.mp hi).2

private theorem negativeSupport_full_iff (a : ExponentVector n) :
    negativeSupport n a = Finset.univ ↔ ∀ i, a i < 0 := by
  constructor
  · intro h i
    exact (Finset.mem_filter.mp (h ▸ Finset.mem_univ i : i ∈ negativeSupport n a)).2
  · intro h
    exact Finset.eq_univ_of_forall (fun i ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ i, h i⟩)

private theorem naturalExponent_support (b : Index n →₀ ℕ) :
    negativeSupport n (naturalExponent n b) = ∅ :=
  (negativeSupport_empty_iff _).mpr fun i ↦ Int.natCast_nonneg (b i)

private theorem polynomial_coeff_allowed {m : ℤ} (f : polynomialDegree k n m)
    {a : ExponentVector n} (ha : (polynomialToLaurent k n f.val).coeff a ≠ 0) :
    a ∈ exponentSet n m ∅ := by
  have hmem : a ∈ Set.range (naturalExponent n) :=
    by_contra fun h ↦ ha (polynomialToLaurent_coeff_zero k f.val h)
  obtain ⟨b, rfl⟩ := hmem
  rw [polynomialToLaurent_coeff] at ha
  exact ⟨f.property b ha, (naturalExponent_support b).le⟩

private theorem laurentPiece_empty_range (m : ℤ) :
    laurentPiece k n m ∅ ≤ LinearMap.range (polynomialToLaurent k n).toLinearMap := by
  unfold laurentPiece
  rw [AddMonoidAlgebra.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb⟩ := naturalExponent_exists ((negativeSupport_empty_iff a).mp
    (Finset.subset_empty.mp ha.2))
  refine ⟨MvPolynomial.monomial b 1, ?_⟩
  change AddMonoidAlgebra.mapDomain (naturalExponent n) (AddMonoidAlgebra.single b (1 : k)) = _
  rw [AddMonoidAlgebra.mapDomain_single, hb]

private def assembleTerm {A : Type u} [AddCommGroup A] [Module k A] {m p : ℤ}
    (f : ∀ a : Exponents n m, A →ₗ[k] Fixed k false a.val p)
    (hf : ∀ v, ∃ s : Finset (Exponents n m), ∀ a ∉ s, f a v = 0) :
    A →ₗ[k] Term k n m p where
  toFun v := ⟨fun a ↦ f a v, Trunc.mk ⟨(hf v).choose.val, fun a ↦ by
    classical
    by_cases h : a ∈ (hf v).choose
    · exact Or.inl h
    · exact Or.inr ((hf v).choose_spec a h)⟩⟩
  map_add' x y := DFinsupp.ext fun a ↦ (f a).map_add x y
  map_smul' r x := DFinsupp.ext fun a ↦ (f a).map_smul r x

private theorem assembleTerm_apply {A : Type u} [AddCommGroup A] [Module k A] {m p : ℤ}
    (f : ∀ a : Exponents n m, A →ₗ[k] Fixed k false a.val p)
    (hf : ∀ v, ∃ s : Finset (Exponents n m), ∀ a ∉ s, f a v = 0) (v : A) (a : Exponents n m) :
    assembleTerm k f hf v a = f a v := rfl

private def indicatorColumn (a : ExponentVector n) (p : ℤ) (P : Finset (Index n) → Prop)
    [DecidablePred P] (h : ∀ J, P J → admissible false a p J) :
    k →ₗ[k] Fixed k false a p where
  toFun c := ⟨fun J ↦ if P J then c else 0, fun J hJ ↦ ite_eq_right (fun hh ↦ hJ (h J hh))⟩
  map_add' x y := by
    apply Subtype.ext
    funext J
    change (if P J then x + y else 0) = (if P J then x else 0) + (if P J then y else 0)
    by_cases hJ : P J <;> simp [hJ]
  map_smul' r x := by
    apply Subtype.ext
    funext J
    change (if P J then r * x else 0) = r * (if P J then x else 0)
    by_cases hJ : P J <;> simp [hJ]

private def polynomialColumn (m : ℤ) (a : Exponents n m) :
    polynomialDegree k n m →ₗ[k] Fixed k false a.val 0 := by
  let v := ((Finsupp.lapply a.val).comp (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap).comp
    ((polynomialToLaurent k n).toLinearMap.comp (polynomialDegree k n m).subtype)
  refine (indicatorColumn k a.val 0 (fun J ↦ J.card = 1 ∧ negativeSupport n a.val = ∅) ?_).comp v
  rintro J ⟨hJ, ha⟩
  exact ⟨by exact_mod_cast hJ, by simp [ha], Or.inr (Finset.card_pos.mp (by omega))⟩

private theorem polynomialColumn_apply {m : ℤ} (f : polynomialDegree k n m) (a : Exponents n m)
    (J : Finset (Index n)) :
    (polynomialColumn k m a f).val J =
      if J.card = 1 then (polynomialToLaurent k n f.val).coeff a.val else 0 := by
  change (if J.card = 1 ∧ negativeSupport n a.val = ∅ then
    (polynomialToLaurent k n f.val).coeff a.val else 0) = _
  by_cases hj : J.card = 1
  · simp only [hj, true_and, ite_true]
    split
    · rfl
    · rename_i h
      symm
      by_contra hn
      exact h (Finset.subset_empty.mp (polynomial_coeff_allowed k f hn).2)
  · simp [hj]

private def polynomialCochain (n : ℕ) (m : ℤ) : polynomialDegree k n m →ₗ[k] Term k n m 0 := by
  classical
  refine assembleTerm k (polynomialColumn k m) fun f ↦ ?_
  let s := (polynomialToLaurent k n f.val).coeff.support
  refine ⟨s.preimage Subtype.val Subtype.val_injective.injOn, fun a ha ↦ ?_⟩
  apply Subtype.ext
  funext J
  have hn : (polynomialToLaurent k n f.val).coeff a.val = 0 :=
    Finsupp.notMem_support_iff.mp fun h ↦ ha (Finset.mem_preimage.mpr h)
  simp [polynomialColumn_apply, hn]

private theorem polynomialCochain_apply {m : ℤ} (f : polynomialDegree k n m) (a : Exponents n m)
    (J : Finset (Index n)) :
    (polynomialCochain k n m f a).val J =
      if J.card = 1 then (polynomialToLaurent k n f.val).coeff a.val else 0 := by
  rw [polynomialCochain, assembleTerm_apply, polynomialColumn_apply]

private theorem deleteSum_emptyIndicator (c : k) (J : Finset (Index n)) :
    deleteSum k (fun I ↦ if I = ∅ then c else 0) J = if J.card = 1 then c else 0 := by
  classical
  by_cases h : J.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    have hf : ({i} : Finset (Index n)).filter (· < i) = ∅ := by
      ext j
      simp +contextual
    simp [deleteSum, sign, hf]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro i hi
    have he : J.erase i ≠ ∅ := by
      intro he
      have hc := Finset.card_erase_add_one hi
      simp [he] at hc
      exact h hc.symm
    simp [he]

private theorem polynomialCochain_closed {m : ℤ} (f : polynomialDegree k n m) :
    differential k n m 0 (polynomialCochain k n m f) = 0 := by
  apply DFinsupp.ext
  intro a
  apply Subtype.ext
  funext J
  change deleteSum k (polynomialCochain k n m f a).val J = 0
  have he : (polynomialCochain k n m f a).val =
      deleteSum k (fun I : Finset (Index n) ↦
        if I = ∅ then (polynomialToLaurent k n f.val).coeff a.val else 0) := by
    funext I
    rw [polynomialCochain_apply, deleteSum_emptyIndicator]
  rw [he, deleteSum_square]


private theorem polynomialCochain_injective (n : ℕ) (m : ℤ) :
    Function.Injective (polynomialCochain k n m) := by
  intro f g h
  apply Subtype.ext
  apply polynomialToLaurent_injective k n
  apply AddMonoidAlgebra.ext
  ext a
  by_cases ha : (∑ i, a i) = m
  · have he := congrArg (fun x : Term k n m 0 ↦ (x ⟨a, ha⟩).val {(0 : Index n)}) h
    change (polynomialCochain k n m f ⟨a, ha⟩).val {(0 : Index n)} =
      (polynomialCochain k n m g ⟨a, ha⟩).val {(0 : Index n)} at he
    simpa [polynomialCochain_apply] using he
  · have hz (f : polynomialDegree k n m) :
        (polynomialToLaurent k n f.val).coeff a = 0 :=
      by_contra fun h ↦ ha (polynomial_coeff_allowed k f h).1
    rw [hz, hz]

private theorem polynomialCochain_surjective_cycles {m : ℤ} (hn : 1 ≤ n) (x : Term k n m 0)
    (hx : differential k n m 0 x = 0) : ∃ f, polynomialCochain k n m f = x := by
  classical
  let J₀ : Faces n 0 := ⟨{0}, by simp⟩
  let z := (transposeTerm k m 0 x J₀).val
  have hc (a : Exponents n m) : deleteSum k (x a).val = 0 :=
    congrArg Subtype.val (DFunLike.congr_fun hx a)
  have hz : z ∈ laurentPiece k n m ∅ := by
    apply AddMonoidAlgebra.mem_supported'.mpr
    intro a ha
    by_cases he : (∑ i, a i) = m
    · let b : Exponents n m := ⟨a, he⟩
      have hh : negativeSupport n a ≠ ∅ := fun h ↦ ha ⟨he, h.le⟩
      change (transposeTerm k m 0 x J₀).val.coeff b.val = 0
      rw [transposeTerm_coeff]
      have h := degreeZero_column k hn (x b) (hc b) 0
      exact h.trans (ite_eq_right hh)
    · exact laurentPiece_coeff_zero k (transposeTerm k m 0 x J₀) (fun h ↦ he h.1)
  obtain ⟨f, hf⟩ := laurentPiece_empty_range k m hz
  change polynomialToLaurent k n f = z at hf
  have hf' : f ∈ polynomialDegree k n m := by
    intro b hb
    have he : z.coeff (naturalExponent n b) ≠ 0 := by
      rwa [← hf, polynomialToLaurent_coeff]
    exact ((AddMonoidAlgebra.mem_supported.mp hz) (Finsupp.mem_support_iff.mpr he)).1
  refine ⟨⟨f, hf'⟩, ?_⟩
  apply DFinsupp.ext
  intro a
  apply Subtype.ext
  funext J
  rw [polynomialCochain_apply, hf]
  by_cases hJ : J.card = 1
  · rw [ite_eq_left hJ]
    change (transposeTerm k m 0 x J₀).val.coeff a.val = _
    rw [transposeTerm_coeff]
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hJ
    by_cases he : negativeSupport n a.val = ∅
    · symm
      exact (degreeZero_column k hn (x a) (hc a) i).trans (ite_eq_left he)
    · have he₀ := (degreeZero_column k hn (x a) (hc a) 0).trans (ite_eq_right he)
      have hei := (degreeZero_column k hn (x a) (hc a) i).trans (ite_eq_right he)
      exact he₀.trans hei.symm
  · rw [ite_eq_right hJ]
    exact ((x a).property J (fun h ↦ hJ (by exact_mod_cast h.1))).symm

private def topColumn (m : ℤ) (a : Exponents n m) :
    (TopExponents n m →₀ k) →ₗ[k] Fixed k false a.val (n : ℤ) := by
  classical
  by_cases ha : ∀ i, a.val i < 0
  · refine (indicatorColumn k a.val (n : ℤ) (· = Finset.univ) ?_).comp (Finsupp.lapply ⟨a, ha⟩)
    intro J hJ
    subst J
    exact ⟨by simp, Finset.subset_univ _, Or.inr Finset.univ_nonempty⟩
  · exact 0

private theorem topColumn_apply {m : ℤ} (f : TopExponents n m →₀ k) (a : Exponents n m)
    (J : Finset (Index n)) :
    (topColumn k m a f).val J =
      if h : ∀ i, a.val i < 0 then if J = Finset.univ then f ⟨a, h⟩ else 0 else 0 := by
  classical
  by_cases ha : ∀ i, a.val i < 0
  · simp only [topColumn, dite_eq_left ha]
    rfl
  · simp [topColumn, ha]

private def topCochain (n : ℕ) (m : ℤ) :
    (TopExponents n m →₀ k) →ₗ[k] Term k n m (n : ℤ) := by
  classical
  refine assembleTerm k (topColumn k m) (fun f ↦ ⟨f.support.image Subtype.val, fun a ha ↦ ?_⟩)
  apply Subtype.ext
  funext J
  rw [topColumn_apply]
  split
  · rename_i h
    have hz : f ⟨a, h⟩ = 0 := Finsupp.notMem_support_iff.mp fun hf ↦
      ha (Finset.mem_image.mpr ⟨⟨a, h⟩, hf, rfl⟩)
    simp [hz]
  · rfl

private theorem topCochain_apply {m : ℤ} (f : TopExponents n m →₀ k) (a : Exponents n m)
    (J : Finset (Index n)) :
    (topCochain k n m f a).val J =
      if h : ∀ i, a.val i < 0 then if J = Finset.univ then f ⟨a, h⟩ else 0 else 0 := by
  rw [topCochain, assembleTerm_apply, topColumn_apply]

private def topCoefficients {m : ℤ} (x : Term k n m (n : ℤ)) : TopExponents n m →₀ k := by
  classical
  apply Finsupp.onFinset (x.support.preimage Subtype.val Subtype.val_injective.injOn)
    (fun b ↦ (x b.val).val Finset.univ)
  intro b hb
  exact Finset.mem_preimage.mpr (DFinsupp.mem_support_iff.mpr (fun h ↦ hb (by simp [h])))

private theorem topCoefficients_apply {m : ℤ} (x : Term k n m (n : ℤ)) (b : TopExponents n m) :
    topCoefficients k x b = (x b.val).val Finset.univ := rfl

private theorem topResidual_full_zero {m : ℤ} (x : Term k n m (n : ℤ)) (a : Exponents n m)
    (ha : negativeSupport n a.val = Finset.univ) :
    (x - topCochain k n m (topCoefficients k x)) a = 0 := by
  classical
  have hall := (negativeSupport_full_iff a.val).mp ha
  apply Subtype.ext
  funext J
  change (x a).val J - (topCochain k n m (topCoefficients k x) a).val J = 0
  rw [topCochain_apply, dite_eq_left hall]
  by_cases hJ : J = Finset.univ
  · subst J
    simp [topCoefficients_apply]
  · rw [ite_eq_right hJ, sub_zero]
    exact (x a).property J (fun h ↦ hJ (Finset.eq_univ_of_forall
      (fun i ↦ (ha ▸ h.2.1) (Finset.mem_univ i))))


private abbrev cech (n : ℕ) (m : ℤ) :=
  orderedComplex k n m (differentialSquareZero k n m)

private abbrev cechShort (n : ℕ) (m p : ℤ) :=
  (cech k n m).sc' (p - 1) p (p + 1)

private theorem cechShort_g_eq (n : ℕ) (m p : ℤ) :
    (cechShort k n m p).g = ModuleCat.ofHom (differential k n m p) := by
  exact CochainComplex.of_d (fun q : ℤ ↦ ModuleCat.of k (Term k n m q))
    (fun q ↦ ModuleCat.ofHom (differential k n m q)) p

private theorem cech_d_apply {m p q : ℤ} (h : p + 1 = q) (x : Term k n m p)
    (a : Exponents n m) (J : Finset (Index n)) :
    ((show Term k n m q from (cech k n m).d p q x) a).val J = deleteSum k (x a).val J := by
  subst q
  have hh : (cech k n m).d p (p + 1) = ModuleCat.ofHom (differential k n m p) :=
    cechShort_g_eq k n m p
  exact congrArg (fun f : (cech k n m).X p ⟶ (cech k n m).X (p + 1) ↦
    ((show Term k n m (p + 1) from f x) a).val J) hh

private theorem previousCochain_is_preimage {m p : ℤ} (hp : 0 < p) (x : Term k n m p)
    (hx : differential k n m p x = 0)
    (hfull : ∀ a : Exponents n m, negativeSupport n a.val = Finset.univ → x a = 0) :
    (cechShort k n m p).f (previousCochain k m p hp x) = x := by
  apply DFinsupp.ext
  intro a
  apply Subtype.ext
  funext J
  change ((show Term k n m p from (cech k n m).d (p - 1) p (previousCochain k m p hp x)) a).val J =
    (x a).val J
  rw [cech_d_apply k (sub_add_cancel p 1)]
  by_cases ha : negativeSupport n a.val = Finset.univ
  · rw [previousCochain_full k hp x a ha, hfull a ha]
    simp [deleteSum]
  · exact previousCochain_delete k hp x hx a ha J

private theorem homologyClass_zero_iff {S : ShortComplex (ModuleCat.{u} k)} (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ y : S.X₁, S.f y = S.iCycles z := by
  have hπ := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f z)
    S.π_moduleCatCyclesIso_hom
  change S.moduleCatHomologyIso.hom (S.homologyπ z) =
    (LinearMap.range S.moduleCatToCycles).mkQ (S.moduleCatCyclesIso.hom z) at hπ
  have hcyc := congrArg (fun f : S.cycles ⟶ S.X₂ ↦ f z) S.moduleCatCyclesIso_hom_i
  change (S.moduleCatCyclesIso.hom z).val = S.iCycles z at hcyc
  have hz : S.homologyπ z = 0 ↔ S.moduleCatHomologyIso.hom (S.homologyπ z) = 0 := by
    exact S.moduleCatHomologyIso.toLinearEquiv.map_eq_zero_iff.symm
  rw [hz, hπ]
  let c : LinearMap.ker S.g.hom := S.moduleCatCyclesIso.hom z
  change (Submodule.Quotient.mk c : LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (congrArg Subtype.val hy).trans hcyc⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext (hy.trans hcyc.symm)⟩

private def representativesToCycles {S : ShortComplex (ModuleCat.{u} k)}
    {A : Type u} [AddCommGroup A] [Module k A] (r : A →ₗ[k] S.X₂)
    (h : ∀ a, S.g (r a) = 0) : A →ₗ[k] S.cycles :=
  S.moduleCatCyclesIso.inv.hom.comp (r.codRestrict (LinearMap.ker S.g.hom) h)

private theorem representativesToCycles_apply {S : ShortComplex (ModuleCat.{u} k)}
    {A : Type u} [AddCommGroup A] [Module k A] (r : A →ₗ[k] S.X₂)
    (h : ∀ a, S.g (r a) = 0) (a : A) :
    S.iCycles (representativesToCycles k r h a) = r a := by
  exact congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ ↦ f ⟨r a, h a⟩)
    S.moduleCatCyclesIso_inv_iCycles

private theorem classEquivalence {S : ShortComplex (ModuleCat.{u} k)}
    {A : Type u} [AddCommGroup A] [Module k A]
    (r : A →ₗ[k] S.X₂) (h : ∀ a, S.g (r a) = 0)
    (hinj : ∀ a, (∃ y : S.X₁, S.f y = r a) → a = 0)
    (hsurj : ∀ x : S.X₂, S.g x = 0 → ∃ (a : A) (y : S.X₁), S.f y = x - r a) :
    ∃ e : A ≃ₗ[k] S.homology, ∀ a, ∃ z : S.cycles,
      S.homologyπ z = e a ∧ S.iCycles z = r a := by
  let l := representativesToCycles k r h
  let g := S.homologyπ.hom.comp l
  have hb : Function.Bijective g := by
    constructor
    · apply (LinearMap.ker_eq_bot).mp
      apply eq_bot_iff.mpr
      intro a ha
      change S.homologyπ (l a) = 0 at ha
      have hr := (homologyClass_zero_iff k (l a)).mp ha
      rw [representativesToCycles_apply] at hr
      exact (Submodule.mem_bot k).mpr (hinj a hr)
    · intro z
      obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance z
      have hw : S.g (S.iCycles w) = 0 :=
        congrArg (fun f : S.cycles ⟶ S.X₃ ↦ f w) S.iCycles_g
      obtain ⟨a, y, hy⟩ := hsurj (S.iCycles w) hw
      have hz : S.homologyπ (w - l a) = 0 := by
        apply (homologyClass_zero_iff k _).mpr
        refine ⟨y, ?_⟩
        change S.f y = S.iCycles.hom (w - l a)
        rw [map_sub]
        simpa only [representativesToCycles_apply, l] using hy
      have he := sub_eq_zero.mp (by simpa only [← map_sub] using hz :
        S.homologyπ.hom w - S.homologyπ.hom (l a) = 0)
      exact ⟨a, he.symm⟩
  exact ⟨LinearEquiv.ofBijective g hb,
    fun a ↦ ⟨l a, rfl, representativesToCycles_apply k r h a⟩⟩

private theorem cohomologyClassEquivalence (n : ℕ) (m p : ℤ)
    {A : Type u} [AddCommGroup A] [Module k A]
    (r : A →ₗ[k] Term k n m p) (h : ∀ a, differential k n m p (r a) = 0)
    (hinj : ∀ a, (∃ y : Term k n m (p - 1), (cechShort k n m p).f y = r a) → a = 0)
    (hsurj : ∀ x : Term k n m p, differential k n m p x = 0 →
      ∃ (a : A) (y : Term k n m (p - 1)), (cechShort k n m p).f y = x - r a) :
    ∃ e : A ≃ₗ[k] (cech k n m).homology p, ∀ a, ∃ z : (cech k n m).cycles p,
      (cech k n m).homologyπ p z = e a ∧ (cech k n m).iCycles p z = r a := by
  let C := cech k n m
  let S := cechShort k n m p
  have hprev := CochainComplex.prev ℤ p
  have hnext := CochainComplex.next ℤ p
  let iH := C.homologyIsoSc' (p - 1) p (p + 1) hprev hnext
  let iZ := C.cyclesIsoSc' (p - 1) p (p + 1) hprev hnext
  have hg : ∀ x : S.X₂, S.g x = 0 ↔ differential k n m p x = 0 := by
    intro x
    change (cechShort k n m p).g x = 0 ↔ _
    rw [cechShort_g_eq]
    rfl
  obtain ⟨e, he⟩ := classEquivalence k (S := S) r
    (fun a ↦ (hg (r a)).mpr (h a)) hinj (fun x hx ↦ hsurj x ((hg x).mp hx))
  refine ⟨e.trans iH.symm.toLinearEquiv, fun a ↦ ?_⟩
  obtain ⟨z, hz, hr⟩ := he a
  refine ⟨iZ.inv z, ?_, ?_⟩
  · change C.homologyπ p (iZ.inv z) = iH.inv (e a)
    rw [← hz]
    exact (congrArg (fun f : S.cycles ⟶ C.homology p ↦ f z)
      (C.π_homologyIsoSc'_inv (p - 1) p (p + 1) hprev hnext)).symm
  · have hh := congrArg (fun f : S.cycles ⟶ C.X p ↦ f z)
      (C.cyclesIsoSc'_inv_iCycles (p - 1) p (p + 1) hprev hnext)
    change C.iCycles p (iZ.inv z) = S.iCycles z at hh
    exact hh.trans hr


theorem cohomologyComputation : Expected.cohomologyComputation.{u} := by
  classical
  intro k _ n hn m
  refine ⟨differentialSquareZero k n m, ?_, ?_, ?_⟩
  · have hinj (f : polynomialDegree k n m)
        (hf : ∃ y : Term k n m (0 - 1), (cechShort k n m 0).f y = polynomialCochain k n m f) :
        f = 0 := by
      obtain ⟨y, hy⟩ := hf
      rw [term_zero_outside k (Or.inl (by decide)) y] at hy
      have hz : polynomialCochain k n m f = (0 : Term k n m 0) :=
        hy.symm.trans (map_zero (cechShort k n m 0).f.hom)
      exact polynomialCochain_injective k n m (hz.trans (map_zero (polynomialCochain k n m)).symm)
    have hsurj (x : Term k n m 0) (hx : differential k n m 0 x = 0) :
        ∃ (f : polynomialDegree k n m) (y : Term k n m (0 - 1)),
          (cechShort k n m 0).f y = x - polynomialCochain k n m f := by
      obtain ⟨f, hf⟩ := polynomialCochain_surjective_cycles k hn x hx
      refine ⟨f, 0, ?_⟩
      rw [hf, sub_self]
      exact map_zero (cechShort k n m 0).f.hom
    obtain ⟨e, he⟩ := cohomologyClassEquivalence k n m 0 (polynomialCochain k n m)
      (polynomialCochain_closed k) hinj hsurj
    refine ⟨e, fun f ↦ ?_⟩
    obtain ⟨z, hz, hr⟩ := he f
    refine ⟨z, hz, fun J a hJ ↦ ?_⟩
    rw [hr, polynomialCochain_apply, ite_eq_left hJ]
  · have hn' : 0 < (n : ℤ) := by omega
    have hclose (x : Term k n m (n : ℤ)) : differential k n m (n : ℤ) x = 0 :=
      term_zero_outside k (Or.inr (by omega)) _
    have hinj (f : TopExponents n m →₀ k)
        (hf : ∃ y : Term k n m ((n : ℤ) - 1),
          (cechShort k n m (n : ℤ)).f y = topCochain k n m f) : f = 0 := by
      obtain ⟨y, hy⟩ := hf
      ext a
      have hy' := congrArg (fun x : Term k n m (n : ℤ) ↦ (x a.val).val Finset.univ) hy
      change ((show Term k n m (n : ℤ) from (cech k n m).d ((n : ℤ) - 1) (n : ℤ) y)
        a.val).val Finset.univ = (topCochain k n m f a.val).val Finset.univ at hy'
      rw [cech_d_apply k (sub_add_cancel (n : ℤ) 1), topCochain_apply,
        dite_eq_left a.property, ite_eq_left rfl] at hy'
      have hfull := (negativeSupport_full_iff a.val.val).mpr a.property
      rw [fixed_full_support_zero k hfull (by omega) (y a.val)] at hy'
      simpa [deleteSum] using hy'.symm
    have hsurj (x : Term k n m (n : ℤ)) (_hx : differential k n m (n : ℤ) x = 0) :
        ∃ (f : TopExponents n m →₀ k) (y : Term k n m ((n : ℤ) - 1)),
          (cechShort k n m (n : ℤ)).f y = x - topCochain k n m f := by
      let f := topCoefficients k x
      let z := x - topCochain k n m f
      exact ⟨f, previousCochain k m (n : ℤ) hn' z,
        previousCochain_is_preimage k hn' z (hclose z) (topResidual_full_zero k x)⟩
    obtain ⟨e, he⟩ := cohomologyClassEquivalence k n m (n : ℤ) (topCochain k n m)
      (fun f ↦ hclose (topCochain k n m f)) hinj hsurj
    refine ⟨e, fun f ↦ ?_⟩
    obtain ⟨z, hz, hr⟩ := he f
    refine ⟨z, hz, fun a ↦ ?_⟩
    rw [hr, topCochain_apply]
    split <;> simp
  · intro p hp hp'
    let C := cech k n m
    apply (C.exactAt_iff' (p - 1) p (p + 1) (CochainComplex.prev ℤ p)
      (CochainComplex.next ℤ p)).mpr
    apply (cechShort k n m p).moduleCat_exact_iff.mpr
    intro x hx
    have hx' : differential k n m p x = 0 := by
      rw [cechShort_g_eq k n m p] at hx
      exact hx
    exact ⟨previousCochain k m p hp x,
      previousCochain_is_preimage k hp x hx' (fun a ha ↦
        fixed_full_support_zero k ha hp' ((show Term k n m p from x) a))⟩

end DerivedFormalization.LaurentCechCohomology
