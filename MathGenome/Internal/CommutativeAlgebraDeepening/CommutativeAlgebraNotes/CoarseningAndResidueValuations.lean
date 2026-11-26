import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoarseningAndResidueValuations
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Quotient
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace CommutativeAlgebraNotes.CoarseningAndResidueValuations

open Function
open Additive (ofMul toMul)
open OrderedValuationGroups
open ValuationPrimesAndConvexSubgroups
open Specs.CommutativeAlgebraNotes.CoarseningAndResidueValuations
open Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups (ringValue)

open private coe_ne_zero dvd_of_ringValue_le
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups

private theorem orderedEquivOfSurjective {A B C : Type*} [AddGroup A]
    [AddGroup B] [LinearOrder B] [AddGroup C] [LinearOrder C]
    (f : A →+ B) (g : A →+ C) (hf : Surjective f) (hg : Surjective g)
    (hle : ∀ a b, g a ≤ g b ↔ f a ≤ f b) :
    ∃ e : B ≃+o C, ∀ a, e (f a) = g a := by
  have hker : f.ker ≤ g.ker := by
    intro a ha
    rw [AddMonoidHom.mem_ker] at ha ⊢
    have he : f a = f 0 := ha.trans (map_zero f).symm
    exact (le_antisymm ((hle a 0).mpr he.le) ((hle 0 a).mpr he.ge)).trans (map_zero g)
  let t := f.liftOfSurjective hf ⟨g, hker⟩
  have ht (a : A) : t (f a) = g a := f.liftOfRightInverse_comp_apply _ _ _ a
  have ht_le (x y : B) : t x ≤ t y ↔ x ≤ y := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [ht, ht, hle]
  have ht_inj : Injective t := fun a b h ↦
    le_antisymm ((ht_le a b).mp h.le) ((ht_le b a).mp h.ge)
  have ht_surj : Surjective t := by
    intro c
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨f a, ht a⟩
  exact ⟨{ AddEquiv.ofBijective t ⟨ht_inj, ht_surj⟩ with map_le_map_iff' := ht_le _ _ }, ht⟩

universe u

variable {K : Type u} [Field K] (V : ValuationSubring K) (P : PrimeSpectrum V)
  (H : ConvexAddSubgroup (ValueGroup V))

private theorem mem_localization_iff (hH : Associated V P H) (a : Kˣ) :
    (a : K) ∈ V.ofPrime P.asIdeal ↔ ∃ h ∈ H.1, 0 ≤ value V (ofMul a) + h := by
  constructor
  · rintro ⟨x, s, hs, he⟩
    have hs₀ : s ≠ 0 := fun h ↦ hs (h.symm ▸ P.asIdeal.zero_mem)
    let b := Units.mk0 (s : K) (coe_ne_zero V hs₀)
    have hab : (↑(a * b) : K) = (x : K) := by
      change (a : K) * (s : K) = (x : K)
      apply (eq_div_iff (coe_ne_zero V hs₀)).mp
      exact he.trans (div_eq_mul_inv _ _).symm
    refine ⟨ringValue V s hs₀, (hH _ (ringValue_nonneg V s hs₀)).mpr ⟨s, hs₀, hs, rfl⟩, ?_⟩
    have h := (value_nonneg_iff V (a * b)).mpr (hab.symm ▸ x.property)
    change 0 ≤ value V (ofMul a + ofMul b) at h
    rw [map_add] at h
    exact h
  · rintro ⟨h, hh, ha⟩
    by_cases h₀ : 0 ≤ h
    · obtain ⟨s, hs₀, hs, rfl⟩ := (hH _ h₀).mp hh
      let b := Units.mk0 (s : K) (coe_ne_zero V hs₀)
      change 0 ≤ value V (ofMul a) + value V (ofMul b) at ha
      rw [← map_add] at ha
      let x : V := ⟨(↑(a * b) : K), (value_nonneg_iff V (a * b)).mp ha⟩
      refine ⟨x, s, hs, ?_⟩
      change (a : K) = ((a : K) * (s : K)) * (s : K)⁻¹
      rw [mul_assoc, mul_inv_cancel₀ (coe_ne_zero V hs₀), mul_one]
    · apply V.le_ofPrime P.asIdeal
      apply (value_nonneg_iff V a).mp
      exact ha.trans (add_le_of_nonpos_right (le_of_not_ge h₀))

/-- Localization at a prime coarsens the original valuation by the corresponding convex subgroup. -/
theorem coarsening (hH : Associated V P H) : IsCoarsening V P H := by
  let f := value (V.ofPrime P.asIdeal)
  let g := (quotientMap H).comp (value V)
  have hg : Surjective g := (quotientMap_surjective H).comp (value_surjective V)
  have hnonneg (a : Additive Kˣ) : 0 ≤ g a ↔ 0 ≤ f a := by
    change 0 ≤ quotientMap H (value V a) ↔ 0 ≤ value (V.ofPrime P.asIdeal) (ofMul (toMul a))
    rw [← map_zero (quotientMap H), quotientMap_le_iff, value_nonneg_iff]
    exact (mem_localization_iff V P H hH (toMul a)).symm
  exact orderedEquivOfSurjective f g (value_surjective _) hg fun a b ↦ by
    rw [← sub_nonneg, ← map_sub, hnonneg, map_sub, sub_nonneg]

private theorem valuation_add_of_mem_prime {x y : V} (hx : x ∈ P.asIdeal) (hy : y ∉ P.asIdeal)
    (hxy : x + y ∉ P.asIdeal) :
    V.valuation ((x + y : V) : K) = V.valuation (y : K) := by
  by_cases hx₀ : x = 0
  · simp [hx₀]
  have hy₀ := notMem_ne_zero V P hy
  have hxy₀ := notMem_ne_zero V P hxy
  have hlt : ringValue V y hy₀ < ringValue V x hx₀ :=
    lt_of_not_ge (fun h ↦ hy (P.asIdeal.mem_of_dvd (dvd_of_ringValue_le V hx₀ hy₀ h) hx))
  have he := value_add_eq_min V (Units.mk0 (x : K) (coe_ne_zero V hx₀))
    (Units.mk0 (y : K) (coe_ne_zero V hy₀)) (coe_ne_zero V hxy₀) (ne_of_gt hlt)
  change ringValue V (x + y) hxy₀ = min (ringValue V x hx₀) (ringValue V y hy₀) at he
  rw [min_eq_right hlt.le] at he
  exact congrArg (fun g : ValueGroup V ↦ ((toMul g : V.ValueGroupˣ) : V.ValueGroup)) he

/-- On the original ring, the residue valuation vanishes precisely on the prime. -/
private def truncatedValue (x : V) : V.ValueGroup := by
  classical
  exact if x ∈ P.asIdeal then 0 else V.valuation (x : K)

private theorem truncatedValue_of_mem {x : V} (hx : x ∈ P.asIdeal) :
    truncatedValue V P x = 0 := by simp [truncatedValue, hx]

private theorem truncatedValue_of_notMem {x : V} (hx : x ∉ P.asIdeal) :
    truncatedValue V P x = V.valuation (x : K) := by simp [truncatedValue, hx]

private def truncatedValuation : Valuation V V.ValueGroup where
  toFun := truncatedValue V P
  map_zero' := truncatedValue_of_mem V P P.asIdeal.zero_mem
  map_one' := (truncatedValue_of_notMem V P P.isPrime.one_notMem).trans (map_one V.valuation)
  map_mul' x y := by
    by_cases hx : x ∈ P.asIdeal
    · rw [truncatedValue_of_mem V P (P.asIdeal.mul_mem_right _ hx),
        truncatedValue_of_mem V P hx, zero_mul]
    by_cases hy : y ∈ P.asIdeal
    · rw [truncatedValue_of_mem V P (P.asIdeal.mul_mem_left _ hy),
        truncatedValue_of_mem V P hy, mul_zero]
    rw [truncatedValue_of_notMem V P (P.isPrime.mul_notMem hx hy),
      truncatedValue_of_notMem V P hx, truncatedValue_of_notMem V P hy]
    exact map_mul V.valuation _ _
  map_add_le_max' x y := by
    by_cases hxy : x + y ∈ P.asIdeal
    · rw [truncatedValue_of_mem V P hxy]
      exact zero_le
    rw [truncatedValue_of_notMem V P hxy]
    by_cases hx : x ∈ P.asIdeal
    · have hy : y ∉ P.asIdeal := fun hy ↦ hxy (P.asIdeal.add_mem hx hy)
      rw [valuation_add_of_mem_prime V P hx hy hxy, truncatedValue_of_notMem V P hy]
      exact le_max_right _ _
    by_cases hy : y ∈ P.asIdeal
    · have h' : y + x ∉ P.asIdeal := by rwa [add_comm]
      rw [add_comm x y, valuation_add_of_mem_prime V P hy hx h',
        truncatedValue_of_notMem V P hx]
      exact le_max_left _ _
    rw [truncatedValue_of_notMem V P hx, truncatedValue_of_notMem V P hy]
    exact V.valuation.map_add _ _

private def quotientValuation : Valuation (V ⧸ P.asIdeal) V.ValueGroup :=
  (truncatedValuation V P).onQuot (fun _ hx ↦ truncatedValue_of_mem V P hx)

private theorem quotientValuation_mk (x : V) :
    quotientValuation V P (Ideal.Quotient.mk P.asIdeal x) = truncatedValue V P x := rfl

private def extendedResidueValuation : Valuation P.asIdeal.ResidueField V.ValueGroup :=
  (quotientValuation V P).extendToLocalization
    (S := nonZeroDivisors (V ⧸ P.asIdeal)) (by
      intro q hq
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      have hx : x ∉ P.asIdeal := fun h ↦ mem_nonZeroDivisors_iff_ne_zero.mp hq
        (Ideal.Quotient.eq_zero_iff_mem.mpr h)
      change quotientValuation V P (Ideal.Quotient.mk P.asIdeal x) ≠ 0
      rw [quotientValuation_mk, truncatedValue_of_notMem V P hx]
      exact V.valuation.ne_zero_iff.mpr (coe_ne_zero V (notMem_ne_zero V P hx)))
    P.asIdeal.ResidueField

private theorem extendedResidueValuation_apply (x : V) :
    extendedResidueValuation V P (residueMap V P x) = truncatedValue V P x := by
  unfold extendedResidueValuation residueMap
  rw [RingHom.comp_apply, Valuation.extendToLocalization_apply_map_apply]
  exact quotientValuation_mk V P x

private theorem residueMap_eq_zero {x : V} (hx : x ∈ P.asIdeal) : residueMap V P x = 0 := by
  change algebraMap (V ⧸ P.asIdeal) P.asIdeal.ResidueField
    (Ideal.Quotient.mk P.asIdeal x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem exists_residue_fraction (z : P.asIdeal.ResidueField) :
    ∃ a b : V, b ∉ P.asIdeal ∧ residueMap V P a / residueMap V P b = z := by
  obtain ⟨x, y, hy, hz⟩ := IsFractionRing.div_surjective (V ⧸ P.asIdeal) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨a, b, fun h ↦ mem_nonZeroDivisors_iff_ne_zero.mp hy (Ideal.Quotient.eq_zero_iff_mem.mpr h), hz⟩

private theorem mem_residue_valuationSubring (z : P.asIdeal.ResidueField) :
    z ∈ (extendedResidueValuation V P).valuationSubring ↔ z ∈ (residueMap V P).range := by
  let w := extendedResidueValuation V P
  change w z ≤ 1 ↔ _
  constructor
  · intro hz
    obtain ⟨a, b, hb, rfl⟩ := exists_residue_fraction V P z
    by_cases ha : a ∈ P.asIdeal
    · exact ⟨0, by rw [map_zero, residueMap_eq_zero V P ha, zero_div]⟩
    have ha₀ := notMem_ne_zero V P ha
    have hb₀ := notMem_ne_zero V P hb
    have hz' : V.valuation (a : K) ≤ V.valuation (b : K) := by
      rw [w.map_div, extendedResidueValuation_apply, extendedResidueValuation_apply,
        truncatedValue_of_notMem V P ha, truncatedValue_of_notMem V P hb] at hz
      exact (div_le_one₀ (V.valuation.pos_iff.mpr (coe_ne_zero V hb₀))).mp hz
    have hab : ringValue V b hb₀ ≤ ringValue V a ha₀ := by
      change (toMul (ringValue V a ha₀) : V.ValueGroupˣ) ≤ toMul (ringValue V b hb₀)
      rw [← Units.val_le_val]
      exact hz'
    obtain ⟨c, hc⟩ := dvd_of_ringValue_le V hb₀ ha₀ hab
    exact ⟨c, by rw [hc, map_mul, mul_comm, mul_div_cancel_right₀ _ (residueMap_ne_zero V P hb)]⟩
  · rintro ⟨a, rfl⟩
    rw [extendedResidueValuation_apply]
    by_cases ha : a ∈ P.asIdeal
    · rw [truncatedValue_of_mem V P ha]
      exact zero_le
    · rw [truncatedValue_of_notMem V P ha]
      exact (V.valuation_le_one_iff _).mpr a.property

/-- The additive value of a nonzero element of the residue fraction field, in the original group. -/
private def residueValue : Additive P.asIdeal.ResidueFieldˣ →+ ValueGroup V :=
  MonoidHom.toAdditive
    (Units.map (extendedResidueValuation V P).toMonoidWithZeroHom.toMonoidHom)

private theorem residueValue_apply (a : V) (ha : a ∉ P.asIdeal) :
    residueValue V P (ofMul (residueUnit V P a ha)) =
      ringValue V a (notMem_ne_zero V P ha) := by
  apply Units.ext
  exact (extendedResidueValuation_apply V P a).trans (truncatedValue_of_notMem V P ha)

private theorem residueValue_mem (hH : Associated V P H) (a : Additive P.asIdeal.ResidueFieldˣ) :
    residueValue V P a ∈ H.1 := by
  obtain ⟨x, y, hy, hxy⟩ :=
    exists_residue_fraction V P (↑(toMul a : P.asIdeal.ResidueFieldˣ))
  have hx : x ∉ P.asIdeal := by
    intro hx
    rw [residueMap_eq_zero V P hx, zero_div] at hxy
    exact (toMul a).ne_zero hxy.symm
  let numerator := residueUnit V P x hx
  let denominator := residueUnit V P y hy
  have ha : a = ofMul numerator - ofMul denominator := (Units.ext hxy).symm
  rw [ha, map_sub, residueValue_apply V P x hx, residueValue_apply V P y hy]
  exact H.1.sub_mem
    ((hH _ (ringValue_nonneg V x _)).mpr ⟨x, _, hx, rfl⟩)
    ((hH _ (ringValue_nonneg V y _)).mpr ⟨y, _, hy, rfl⟩)

/-- The residue valuation has the ordered value group of the corresponding convex subgroup. -/
theorem residue_valuation (hH : Associated V P H) : HasResidueValuation V P H := by
  let w := extendedResidueValuation V P
  let f := value w.valuationSubring
  let g := (residueValue V P).codRestrict H.1 (residueValue_mem V P H hH)
  refine ⟨w.valuationSubring, mem_residue_valuationSubring V P, ?_⟩
  have hnonneg (z : H.1) (hz : 0 ≤ z.val) : ∃ a, g a = z := by
    obtain ⟨x, hx₀, hx, hval⟩ := (hH z.val hz).mp z.property
    exact ⟨ofMul (residueUnit V P x hx),
      Subtype.ext ((residueValue_apply V P x hx).trans hval)⟩
  have hg : Surjective g := by
    intro z
    obtain hz | hz := le_total 0 z.val
    · exact hnonneg z hz
    · obtain ⟨a, ha⟩ := hnonneg (-z) (neg_nonneg.mpr hz)
      exact ⟨-a, by rw [map_neg, ha, neg_neg]⟩
  have hle (a b : Additive P.asIdeal.ResidueFieldˣ) : g a ≤ g b ↔ f a ≤ f b := by
    let x : P.asIdeal.ResidueFieldˣ := toMul a
    let y : P.asIdeal.ResidueFieldˣ := toMul b
    change w y ≤ w x ↔ w.valuationSubring.valuation y ≤ w.valuationSubring.valuation x
    exact w.isEquiv_valuation_valuationSubring _ _
  obtain ⟨e, he⟩ := orderedEquivOfSurjective f g (value_surjective _) hg hle
  have he_residue (a : V) (ha : a ∉ P.asIdeal) :
      (e (f (ofMul (residueUnit V P a ha))) : ValueGroup V) =
        ringValue V a (notMem_ne_zero V P ha) :=
    (congrArg Subtype.val (he _)).trans (residueValue_apply V P a ha)
  refine ⟨e, he_residue, fun a b ha hb ↦ ?_⟩
  change (e (f (ofMul (residueUnit V P a ha) - ofMul (residueUnit V P b hb))) :
    ValueGroup V) = _
  rw [map_sub, map_sub]
  change (e (f (ofMul (residueUnit V P a ha))) : ValueGroup V) -
    (e (f (ofMul (residueUnit V P b hb))) : ValueGroup V) = _
  rw [he_residue, he_residue]

/-- Both value-group identifications for the subgroup from the prime correspondence. -/
theorem coarsening_and_residue :
    ∃ J : ConvexAddSubgroup (ValueGroup V),
      Associated V P J ∧ IsCoarsening V P J ∧ HasResidueValuation V P J := by
  let J := primeToConvex V P
  have hJ : Associated V P J := fun _ hg ↦ mem_primeToConvex_iff V P hg
  exact ⟨J, hJ, coarsening V P J hJ, residue_valuation V P J hJ⟩

/-- The localization and residue descriptions specialize to both extreme primes. -/
theorem extreme_primes (V : ValuationSubring K) :
    let O : PrimeSpectrum V := ⊥
    let M : PrimeSpectrum V := ⟨IsLocalRing.maximalIdeal V, inferInstance⟩
    (V.ofPrime O.asIdeal = ⊤ ∧
      ∃ H : ConvexAddSubgroup (ValueGroup V),
        Associated V O H ∧ H.1 = ⊤ ∧ IsCoarsening V O H ∧ HasResidueValuation V O H) ∧
    (V.ofPrime M.asIdeal = V ∧ Surjective (residueMap V M) ∧
      ∃ H : ConvexAddSubgroup (ValueGroup V),
        Associated V M H ∧ H.1 = ⊥ ∧ IsCoarsening V M H ∧ HasResidueValuation V M H) := by
  dsimp only
  let M : PrimeSpectrum V := ⟨IsLocalRing.maximalIdeal V, inferInstance⟩
  have hM : M.asIdeal.IsMaximal := inferInstanceAs ((IsLocalRing.maximalIdeal V).IsMaximal)
  have hsurj : Surjective (residueMap V M) := by
    have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient M.asIdeal).mp hM
    exact (IsFractionRing.surjective_iff_isField.mpr hfield).comp Ideal.Quotient.mk_surjective
  have hassoc (Q : PrimeSpectrum V) : Associated V Q (primeToConvex V Q) :=
    fun _ hg ↦ mem_primeToConvex_iff V Q hg
  refine ⟨⟨ValuationSubring.ofPrime_bot V, primeToConvex V ⊥, hassoc ⊥,
    primeToConvex_bot V, coarsening V _ _ (hassoc _), residue_valuation V _ _ (hassoc _)⟩,
    ⟨ValuationSubring.ofPrime_top V, hsurj, primeToConvex V M, hassoc M,
      primeToConvex_maximalIdeal V, coarsening V _ _ (hassoc _), residue_valuation V _ _ (hassoc _)⟩⟩

end CommutativeAlgebraNotes.CoarseningAndResidueValuations
