import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.CyclicFourier
import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ComplexConjugate ENNReal

namespace P102.Periodic.Cyclic

abbrev counting := CyclicData.counting
abbrev character := CyclicData.character
abbrev coefficient := CyclicData.coefficient
abbrev convolution := CyclicData.convolution
abbrev sample := CyclicData.sample

variable (m : ℕ) [NeZero m]

lemma character_conj (k j : ZMod m) : conj (character m k j) =
    ZMod.stdAddChar (-(k * j)) := by
  change conj (↑(ZMod.toCircle (k * j)) : ℂ) =
    (↑(ZMod.toCircle (-(k * j))) : ℂ)
  rw [AddChar.map_neg_eq_inv, _root_.Circle.coe_inv_eq_conj]

lemma character_add (k j l : ZMod m) :
    character m k (j + l) = character m k j * character m k l := by
  simp only [character, CyclicData.character, mul_add, AddChar.map_add_eq_mul]

lemma characterFormula (k j : ℤ) :
    character m (k : ZMod m) (j : ZMod m) =
      Complex.exp (2 * Real.pi * Complex.I * k * j / m) := by
  unfold character CyclicData.character
  rw [← Int.cast_mul, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

lemma countingProbability : counting m Set.univ = 1 := by
  simp [counting, CyclicData.counting, Measure.count_apply_finite, ZMod.card,
    ENNReal.inv_mul_cancel, NeZero.ne m]

lemma countingSingleton (j : ZMod m) : counting m {j} = (m : ℝ≥0∞)⁻¹ := by
  simp [counting, CyclicData.counting]

lemma averageIntegral (f : ZMod m → ℂ) :
    (∫ j, f j ∂counting m) = (m : ℂ)⁻¹ * ∑ j, f j := by
  simp [counting, CyclicData.counting, integral_smul_measure, integral_fintype,
    ENNReal.toReal_inv]

lemma characterOrthonormal (k l : ZMod m) :
    (m : ℂ)⁻¹ * ∑ j, character m k j * conj (character m l j) =
      if k = l then 1 else 0 := by
  simp_rw [character_conj, character, CyclicData.character,
    ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  have hs : (∑ j : ZMod m, ZMod.stdAddChar ((k - l) * j)) =
      if k - l = 0 then (m : ℂ) else 0 := by
    simpa only [mul_comm, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      (AddChar.sum_mulShift (b := k - l) (ZMod.isPrimitive_stdAddChar m))
  rw [hs]
  by_cases h : k = l
  · simp [h, NeZero.ne (m : ℂ)]
  · simp [sub_ne_zero.mpr h, h]

lemma coefficient_eq_dft (f : ZMod m → ℂ) (k : ZMod m) :
    coefficient m f k = (m : ℂ)⁻¹ * ZMod.dft f k := by
  simp only [coefficient, CyclicData.coefficient, character_conj, ZMod.dft_apply,
    smul_eq_mul, mul_comm k, mul_comm (f _)]

lemma inversion (f : ZMod m → ℂ) (j : ZMod m) :
    f j = ∑ k, coefficient m f k * character m k j := by
  have h := congrFun (ZMod.dft.symm_apply_apply f) j
  rw [ZMod.invDFT_apply, smul_eq_mul] at h
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coefficient_eq_dft]
  simp only [character, CyclicData.character, smul_eq_mul]
  ring

lemma conjugate_coefficient (f : ZMod m → ℂ) (k : ZMod m) :
    conj (coefficient m f k) = (m : ℂ)⁻¹ * ∑ j, character m k j * conj (f j) := by
  simp [coefficient, CyclicData.coefficient, map_sum, mul_comm]

/-- The inner-product identity, linear in the first argument. -/
lemma pairing (f g : ZMod m → ℂ) :
    (m : ℂ)⁻¹ * ∑ j, f j * conj (g j) =
      ∑ k, coefficient m f k * conj (coefficient m g k) := by
  calc
    _ = (m : ℂ)⁻¹ * ∑ j, (∑ k, coefficient m f k * character m k j) * conj (g j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [← inversion]
    _ = ∑ k, coefficient m f k * ((m : ℂ)⁻¹ * ∑ j, character m k j * conj (g j)) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp_rw [conjugate_coefficient]

lemma parseval (f : ZMod m → ℂ) :
    (m : ℝ)⁻¹ * ∑ j, ‖f j‖ ^ 2 = ∑ k, ‖coefficient m f k‖ ^ 2 := by
  have h := pairing m f f
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.ofReal_pow] using h

lemma sampleInjective (T : ℝ) [hT : Fact (0 < T)] :
    Function.Injective (sample m T) :=
  (AddCircle.equivAddCircle (1 : ℝ) T one_ne_zero hT.out.ne').injective.comp
    (ZMod.toAddCircle_injective m)

lemma sampleFormula (T : ℝ) [hT : Fact (0 < T)] (j : ℤ) :
    sample m T (j : ZMod m) = ((T * j / m : ℝ) : AddCircle T) := by
  change (AddCircle.equivAddCircle (1 : ℝ) T one_ne_zero hT.out.ne')
    (ZMod.toAddCircle (j : ZMod m)) = _
  rw [ZMod.toAddCircle_intCast, AddCircle.equivAddCircle_apply_mk]
  congr 1
  ring

lemma modeRestriction (T : ℝ) [hT : Fact (0 < T)] (k : ℤ) (j : ZMod m) :
    mode T k (sample m T j) = character m (k : ZMod m) j := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective j
  rw [sampleFormula, mode_formula, characterFormula]
  congr 1
  push_cast
  field_simp [show (T : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hT.out.ne']

lemma trivialGroup :
    (∀ k j : ZMod 1, character 1 k j = 1) ∧
    (∀ (f : ZMod 1 → ℂ) k, coefficient 1 f k = f 0) ∧
    (∀ (f g : ZMod 1 → ℂ) j, convolution 1 f g j = f 0 * g 0) := by
  have hz (j : ZMod 1) : j = 0 := Subsingleton.elim _ _
  simp [character, CyclicData.character, coefficient, CyclicData.coefficient,
    convolution, CyclicData.convolution, hz]

lemma shifted_pairing (f g : ZMod m → ℂ) (k l : ZMod m) :
    (∑ j, f (j - l) * g l * conj (character m k j)) =
      (∑ u, f u * conj (character m k u)) * g l * conj (character m k l) := by
  simp only [Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.subRight l) _ _ ?_
  intro j
  have hc : character m k j = character m k (j - l) * character m k l := by
    rw [← character_add, sub_add_cancel]
  change f (j - l) * g l * conj (character m k j) =
    f (j - l) * conj (character m k (j - l)) * g l * conj (character m k l)
  rw [hc, map_mul]
  ring

lemma convolutionProduct (f g : ZMod m → ℂ) (k : ZMod m) :
    coefficient m (convolution m f g) k = coefficient m f k * coefficient m g k := by
  unfold coefficient CyclicData.coefficient convolution CyclicData.convolution
  calc
    _ = (m : ℂ)⁻¹ * ((m : ℂ)⁻¹ * ∑ l, ∑ j,
        f (j - l) * g l * conj (character m k j)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [shifted_pairing]
      have hs : (∑ l, (∑ u, f u * conj (character m k u)) * g l * conj (character m k l)) =
          (∑ u, f u * conj (character m k u)) * ∑ l, g l * conj (character m k l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      rw [hs]
      ring

end P102.Periodic.Cyclic
