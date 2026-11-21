import MathGenome.Internal.Specs.D07.Ch23.FrobeniusAnticommutingDecomposition
import MathGenome.Internal.D07.Ch23.FrobeniusComplexSubfieldCentralizer
import MathGenome.Internal.D07.Ch23.QuaternionAlgebra
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

noncomputable section
universe u
namespace D07.Ch23.FrobeniusAnticommutingDecomposition
open Specs.D07.Ch23.FrobeniusAnticommutingDecomposition
variable {D : Type u} [DivisionRing D] [Algebra ℝ D]

lemma imaginary_square (φ : ℂ →ₐ[ℝ] D) : φ Complex.I * φ Complex.I = -1 := by
  rw [← map_mul, Complex.I_mul_I, map_neg, map_one]

lemma imaginary_ne_zero (φ : ℂ →ₐ[ℝ] D) : φ Complex.I ≠ 0 :=
  (map_ne_zero φ).mpr Complex.I_ne_zero

lemma imaginary_inv (φ : ℂ →ₐ[ℝ] D) : (φ Complex.I)⁻¹ = -φ Complex.I := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_neg, imaginary_square, neg_neg]

lemma conjugation_formula (φ : ℂ →ₐ[ℝ] D) (y : D) :
    conjugation φ y = -(φ Complex.I * y * φ Complex.I) := by
  simp [conjugation, imaginary_inv]

lemma conjugation_involutive (φ : ℂ →ₐ[ℝ] D) :
    Function.Involutive (conjugation φ) := by
  intro y
  simp only [conjugation_formula, mul_neg, neg_mul, neg_neg]
  calc
    φ Complex.I * (φ Complex.I * y * φ Complex.I) * φ Complex.I =
        (φ Complex.I * φ Complex.I) * y * (φ Complex.I * φ Complex.I) := by
          noncomm_ring
    _ = y := by simp [imaginary_square]

lemma negative_iff (φ : ℂ →ₐ[ℝ] D) (y : D) :
    y ∈ negative φ ↔ φ Complex.I * y = -(y * φ Complex.I) := Iff.rfl

lemma positive_iff (φ : ℂ →ₐ[ℝ] D) (y : D) :
    y ∈ positive φ ↔ y ∈ Set.range φ := Iff.rfl

lemma conjugation_linear (φ : ℂ →ₐ[ℝ] D) :
    ∃ T : D →ₗ[ℝ] D, (∀ y, T y = conjugation φ y) ∧ Function.Involutive T := by
  let T : D →ₗ[ℝ] D :=
    { toFun := conjugation φ
      map_add' := fun a b => by simp [conjugation, mul_add, add_mul]
      map_smul' := fun r y => by simp [conjugation] }
  exact ⟨T, fun _ => rfl, conjugation_involutive φ⟩

lemma conjugation_mul_I (φ : ℂ →ₐ[ℝ] D) (y : D) :
    conjugation φ y * φ Complex.I = φ Complex.I * y := by
  simp [conjugation, mul_assoc]

lemma fixed_iff (φ : ℂ →ₐ[ℝ] D) (y : D) :
    conjugation φ y = y ↔ y * φ Complex.I = φ Complex.I * y := by
  constructor
  · intro h
    calc
      y * φ Complex.I = conjugation φ y * φ Complex.I := congrArg (· * φ Complex.I) h.symm
      _ = φ Complex.I * y := conjugation_mul_I φ y
  · intro h
    apply mul_right_cancel₀ (imaginary_ne_zero φ)
    rw [conjugation_mul_I, h]

lemma negated_iff (φ : ℂ →ₐ[ℝ] D) (y : D) :
    conjugation φ y = -y ↔ y ∈ negative φ := by
  rw [negative_iff]
  constructor
  · intro h
    rw [← conjugation_mul_I φ y, h, neg_mul]
  · intro h
    apply mul_right_cancel₀ (imaginary_ne_zero φ)
    rw [conjugation_mul_I, h, neg_mul]

lemma projection_properties (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) (y : D) :
    positivePart φ y ∈ positive φ ∧ negativePart φ y ∈ negative φ ∧
      positivePart φ y + negativePart φ y = y := by
  obtain ⟨T, hT, hTT⟩ := conjugation_linear φ
  have hp : positivePart φ y = (1 / 2 : ℝ) • (y + T y) := by
    simp only [positivePart, hT]
  have hn : negativePart φ y = (1 / 2 : ℝ) • (y - T y) := by
    simp only [negativePart, hT]
  refine ⟨?_, ?_, ?_⟩
  · rw [positive_iff, ← hc, ← fixed_iff, hp, ← hT, map_smul, map_add, hTT]
    congr 1
    abel
  · rw [← negated_iff, hn, ← hT, map_smul, map_sub, hTT]
    module
  · rw [hp, hn]
    module

theorem decomposition (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    Decomposition φ := by
  refine ⟨conjugation_linear φ, ?_, projection_properties φ hc⟩
  rw [isCompl_iff]
  constructor
  · rw [Submodule.disjoint_def]
    intro y hp hn
    have hp' := (fixed_iff φ y).mpr ((hc y).mpr hp)
    have hn' := (negated_iff φ y).mpr hn
    have he : y = -y := hp'.symm.trans hn'
    have hz : (2 : ℝ) • y = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr he
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  · rw [codisjoint_iff, Submodule.sup_eq_top_iff]
    intro y
    obtain ⟨hp, hn, he⟩ := projection_properties φ hc y
    exact ⟨positivePart φ y, hp, negativePart φ y, hn, he.symm⟩

lemma complex_coordinates (φ : ℂ →ₐ[ℝ] D) (z : ℂ) :
    φ z = algebraMap ℝ D z.re + z.im • φ Complex.I := by
  conv_lhs => rw [← Complex.re_add_im z]
  simp only [map_add, map_mul, AlgHom.map_coe_real_complex, Algebra.smul_def]

lemma reverse_anticommute (φ : ℂ →ₐ[ℝ] D) {j : D} (hj : j ∈ negative φ) :
    j * φ Complex.I = -(φ Complex.I * j) := by
  have h := (negative_iff φ j).mp hj
  rw [h, neg_neg]

theorem conjugateAction (φ : ℂ →ₐ[ℝ] D) : ConjugateAction φ := by
  intro j hj z
  rw [complex_coordinates φ z, complex_coordinates φ (star z)]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, mul_add, add_mul,
    mul_smul_comm, reverse_anticommute φ hj, smul_neg, neg_smul]
  rw [← Algebra.commutes z.re j, neg_mul, smul_mul_assoc]

lemma negative_complex_mul (φ : ℂ →ₐ[ℝ] D) (z : ℂ) {j : D}
    (hj : j ∈ negative φ) : φ z * j ∈ negative φ := by
  rw [negative_iff] at hj ⊢
  calc
    φ Complex.I * (φ z * j) = φ z * (φ Complex.I * j) := by
      rw [← mul_assoc, ← map_mul, mul_comm Complex.I z, map_mul, mul_assoc]
    _ = -(φ z * j * φ Complex.I) := by rw [hj]; noncomm_ring

lemma negative_ratio_commutes (φ : ℂ →ₐ[ℝ] D) {y j : D}
    (hy : y ∈ negative φ) (hj : j ∈ negative φ) (hjn : j ≠ 0) :
    (y * j⁻¹) * φ Complex.I = φ Complex.I * (y * j⁻¹) := by
  apply mul_right_cancel₀ hjn
  calc
    (y * j⁻¹) * φ Complex.I * j = -(y * φ Complex.I) := by
      rw [mul_assoc (y * j⁻¹), (negative_iff φ j).mp hj]
      simp [mul_assoc, hjn]
    _ = φ Complex.I * y := ((negative_iff φ y).mp hy).symm
    _ = (φ Complex.I * (y * j⁻¹)) * j := by simp [mul_assoc, hjn]

theorem negativeLine (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    NegativeLine φ := by
  intro j hj hjn y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := (hc _).mp (negative_ratio_commutes φ hy hj hjn)
    refine ⟨z, ?_⟩
    rw [hz]
    simp [hjn]
  · rintro ⟨z, rfl⟩
    exact negative_complex_mul φ z hj

lemma square_commutes (φ : ℂ →ₐ[ℝ] D) {j : D} (hj : j ∈ negative φ) :
    j ^ 2 * φ Complex.I = φ Complex.I * j ^ 2 := by
  rw [pow_two]
  calc
    (j * j) * φ Complex.I = j * (j * φ Complex.I) := mul_assoc _ _ _
    _ = j * (-(φ Complex.I * j)) := by rw [reverse_anticommute φ hj]
    _ = -(j * φ Complex.I) * j := by noncomm_ring
    _ = φ Complex.I * (j * j) := by rw [reverse_anticommute φ hj]; noncomm_ring

lemma square_real (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ)
    {j : D} (hj : j ∈ negative φ) (hjn : j ≠ 0) :
    ∃ r : ℝ, j ^ 2 = algebraMap ℝ D r := by
  obtain ⟨z, hz⟩ := (hc _).mp (square_commutes φ hj)
  have hstar : z = star z := by
    apply φ.injective
    apply mul_right_cancel₀ hjn
    calc
      φ z * j = j * φ z := by rw [hz]; simp [pow_two, mul_assoc]
      _ = φ (star z) * j := conjugateAction φ j hj z
  have hi : z.im = 0 := by
    have he := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at he
    linarith
  refine ⟨z.re, ?_⟩
  rw [← hz, complex_coordinates, hi, zero_smul, add_zero]

lemma negative_real_zero (φ : ℂ →ₐ[ℝ] D) {r : ℝ}
    (h : algebraMap ℝ D r ∈ negative φ) : r = 0 := by
  have hcomm := Algebra.commutes r (φ Complex.I)
  have ha := (negative_iff φ _).mp h
  have hz : φ Complex.I * algebraMap ℝ D r = 0 := by
    rw [hcomm] at ha
    have he : (2 : ℝ) • (φ Complex.I * algebraMap ℝ D r) = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr ha
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  exact (map_eq_zero (algebraMap ℝ D)).mp ((mul_eq_zero.mp hz).resolve_left (imaginary_ne_zero φ))

theorem negativeSquare (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    NegativeSquare φ := by
  intro j hj hjn
  obtain ⟨r, hr⟩ := square_real φ hc hj hjn
  have hrn : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hr
    exact (pow_ne_zero 2 hjn) hr
  have hrneg : r < 0 := by
    by_contra hn
    have hrpos : 0 < r := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hrn)
    let s : ℝ := Real.sqrt r
    have hs : s ^ 2 = r := Real.sq_sqrt hrpos.le
    have hsD : (algebraMap ℝ D s) ^ 2 = algebraMap ℝ D r := by
      rw [← map_pow, hs]
    have hprod : (j - algebraMap ℝ D s) * (j + algebraMap ℝ D s) = 0 := by
      have hcomm := Algebra.commutes s j
      calc
        (j - algebraMap ℝ D s) * (j + algebraMap ℝ D s) =
          j ^ 2 - (algebraMap ℝ D s) ^ 2 := by
            noncomm_ring [hcomm]
        _ = 0 := by rw [hr, hsD, sub_self]
    rcases mul_eq_zero.mp hprod with he | he
    · have hjreal : j = algebraMap ℝ D s := sub_eq_zero.mp he
      have hz := negative_real_zero φ (hjreal ▸ hj)
      apply hjn
      rw [hjreal, hz, map_zero]
    · have hjreal : j = algebraMap ℝ D (-s) := by
        rw [map_neg]; exact eq_neg_of_add_eq_zero_left he
      have hz := negative_real_zero φ (hjreal ▸ hj)
      apply hjn
      rw [hjreal, hz, map_zero]
  exact ⟨r, hrneg, hrn, hr⟩

theorem normalization (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    Normalization φ := by
  intro j hj hjn
  obtain ⟨r, hrneg, hrn, hr⟩ := negativeSquare φ hc j hj hjn
  let t : ℝ := Real.sqrt (-r)
  have ht : 0 < t := Real.sqrt_pos.mpr (neg_pos.mpr hrneg)
  have htn : t ≠ 0 := ne_of_gt ht
  have ht2 : t ^ 2 = -r := Real.sq_sqrt (neg_nonneg.mpr hrneg.le)
  let s : ℝ := t⁻¹
  let j₀ : D := s • j
  have hs : 0 < s := inv_pos.mpr ht
  have hscale : s ^ 2 * r = -1 := by
    dsimp [s]
    rw [inv_pow, ht2]
    field_simp
  have hj₀ : j₀ ∈ negative φ := (negative φ).smul_mem s hj
  have hj₀n : j₀ ≠ 0 := smul_ne_zero (ne_of_gt hs) hjn
  have hj₀2 : j₀ ^ 2 = -1 := by
    change (s • j) ^ 2 = -1
    calc
      (s • j) ^ 2 = (s * s) • (j * j) := by
        simp only [pow_two, smul_mul_smul_comm]
      _ = algebraMap ℝ D (s ^ 2 * r) := by
        rw [← pow_two, ← pow_two, hr, Algebra.smul_def, ← map_mul]
      _ = -1 := by rw [hscale, map_neg, map_one]
  refine ⟨s, j₀, hs, rfl, hj₀, hj₀n, hj₀2, ?_⟩
  intro y
  exact ((negativeLine φ hc j₀ hj₀ hj₀n y).symm).trans (negativeLine φ hc j hj hjn y)

lemma quaternion_hom (φ : ℂ →ₐ[ℝ] D) {j : D}
    (hj : j ∈ negative φ) (hj2 : j ^ 2 = -1) :
    ∃ f : Quaternion ℝ →ₐ[ℝ] D,
      ∀ z w : ℂ, f (Specs.D07.Ch23.QuaternionAlgebra.toH (z, w)) = φ z + φ w * j := by
  let B : _root_.QuaternionAlgebra.Basis D (-1 : ℝ) 0 (-1) :=
    { i := φ Complex.I
      j := j
      k := φ Complex.I * j
      i_mul_i := by simpa using imaginary_square φ
      j_mul_j := by simpa only [neg_smul, one_smul, pow_two] using hj2
      i_mul_j := rfl
      j_mul_i := by simpa using reverse_anticommute φ hj }
  refine ⟨B.liftHom, ?_⟩
  intro z w
  change algebraMap ℝ D z.re + z.im • φ Complex.I + w.re • j +
    w.im • (φ Complex.I * j) = φ z + φ w * j
  rw [complex_coordinates φ z, complex_coordinates φ w, add_mul, ← smul_mul_assoc,
    ← Algebra.smul_def]
  abel

theorem quaternionEquivalence (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    QuaternionEquivalence φ := by
  intro j hj hj2
  have hjn : j ≠ 0 := by
    intro h
    simp [h] at hj2
  obtain ⟨f, hf⟩ := quaternion_hom φ hj hj2
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨hp, hn, he⟩ := projection_properties φ hc y
    obtain ⟨z, hz⟩ := hp
    change φ z = positivePart φ y at hz
    obtain ⟨w, hw⟩ := (negativeLine φ hc j hj hjn _).mp hn
    refine ⟨Specs.D07.Ch23.QuaternionAlgebra.toH (z, w), ?_⟩
    rw [hf, hz, ← hw, he]
  exact ⟨AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩, hf⟩

theorem uniqueCoordinates (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    UniqueCoordinates φ := by
  intro j hj hj2 y
  obtain ⟨e, he⟩ := quaternionEquivalence φ hc j hj hj2
  have hfun : (fun u : ℂ × ℂ => φ u.1 + φ u.2 * j) =
      e ∘ D07.Ch23.QuaternionAlgebra.pairEquiv := by
    funext u
    exact (he u.1 u.2).symm
  have hbij : Function.Bijective (fun u : ℂ × ℂ => φ u.1 + φ u.2 * j) := by
    rw [hfun]
    exact e.bijective.comp D07.Ch23.QuaternionAlgebra.pairEquiv.bijective
  exact hbij.existsUnique y

theorem complexCase (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    ComplexCase φ := by
  intro hn
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨hp, hm, he⟩ := projection_properties φ hc y
    have hz : negativePart φ y = 0 := by simpa only [hn, Submodule.mem_bot] using hm
    obtain ⟨z, hz'⟩ := hp
    refine ⟨z, ?_⟩
    change φ z = positivePart φ y at hz'
    simpa only [hz', hz, add_zero] using he
  exact ⟨AlgEquiv.ofBijective φ ⟨φ.injective, hsurj⟩, fun _ => rfl⟩

theorem quaternionCase (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    QuaternionCase φ := by
  intro hn
  obtain ⟨j, hj, hjn⟩ := (negative φ).ne_bot_iff.mp hn
  obtain ⟨s, j₀, hs, hj₀eq, hj₀, hj₀n, hj₀2, hline⟩ := normalization φ hc j hj hjn
  exact ⟨j₀, hj₀, hj₀2, quaternionEquivalence φ hc j₀ hj₀ hj₀2⟩

theorem anticommutingResults (φ : ℂ →ₐ[ℝ] D) (hc : CentralizerCondition φ) :
    AnticommutingResults φ :=
  ⟨decomposition φ hc, conjugateAction φ, negativeLine φ hc,
    negativeSquare φ hc, normalization φ hc, quaternionEquivalence φ hc, uniqueCoordinates φ hc,
    complexCase φ hc, quaternionCase φ hc⟩

theorem centralizerAnticommutingResults : CentralizerAnticommutingResults.{u} := by
  intro D _ _ φ hc
  exact anticommutingResults φ hc

theorem algebraicAnticommutingResults : AlgebraicAnticommutingResults.{u} := by
  intro D _ _ h φ
  exact anticommutingResults φ
    (FrobeniusComplexSubfieldCentralizer.complexCentralizerImage D h φ)

end D07.Ch23.FrobeniusAnticommutingDecomposition
