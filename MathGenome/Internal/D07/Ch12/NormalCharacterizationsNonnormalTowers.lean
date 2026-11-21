import MathGenome.Internal.Specs.D07.Ch12.NormalCharacterizationsNonnormalTowers
import MathGenome.Internal.D07.Ch11.Eisenstein
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree

/-!
The cubic and quartic polynomials are irreducible by the accepted Eisenstein
criterion at 2. A splitting of either real polynomial would split its quadratic
factor: X²+aX+a² in the cubic case and X²+a² in the quartic case. Positivity
rules out real roots of these factors. Normality of the generated fields would
force precisely these impossible splittings after mapping coefficients into ℝ.

The middle field of the tower is generated inside the top field by the square
of the fourth-root generator. Its image in ℝ is ℚ(√2). Eisenstein gives degrees
2 and 4 over ℚ, and the finite tower law gives upper degree 2. Both steps are
therefore normal. The explicit complex root i·fourthRoot witnesses the missing
nonreal roots; no algebraic closedness of ℂ is used.
-/

noncomputable section
namespace D07.Ch12.NormalCharacterizationsNonnormalTowers
open Polynomial IntermediateField
open Specs.D07.Ch12.NormalCharacterizationsNonnormalTowers

lemma cubeRoot_cube : cubeRoot ^ 3 = 2 :=
  Real.rpow_inv_natCast_pow (by norm_num) (by decide)

lemma fourthRoot_square : fourthRoot ^ 2 = Real.sqrt 2 :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

lemma fourthRoot_fourth : fourthRoot ^ 4 = 2 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, fourthRoot_square]
  exact Real.sq_sqrt (by norm_num)

lemma radical_irreducible (n : ℕ) (hn : 0 < n) :
    Irreducible (X ^ n - C (2 : ℚ)) :=
  (Ch11.Eisenstein.xPowSubPrime 2 n Nat.prime_two hn).2

lemma radical_integral {F : Type*} [Field F] [Algebra ℚ F]
    (a : F) (n : ℕ) (hn : n ≠ 0) (ha : a ^ n = 2) : IsIntegral ℚ a := by
  refine ⟨X ^ n - C 2, monic_X_pow_sub_C _ hn, ?_⟩
  simpa using (sub_eq_zero.mpr ha : a ^ n - 2 = 0)

lemma radical_minpoly {F : Type*} [Field F] [Algebra ℚ F]
    (a : F) (n : ℕ) (hn : 0 < n) (ha : a ^ n = 2) :
    minpoly ℚ a = X ^ n - C 2 := by
  symm
  apply minpoly.eq_of_irreducible_of_monic (radical_irreducible n hn)
  · simpa using (sub_eq_zero.mpr ha : a ^ n - 2 = 0)
  · exact monic_X_pow_sub_C _ (Nat.ne_zero_of_lt hn)

lemma radical_finrank {F : Type*} [Field F] [Algebra ℚ F] (a : F) (n : ℕ) (hn : 0 < n) (ha : a ^ n = 2) :
    Module.finrank ℚ (adjoin ℚ {a}) = n := by
  rw [adjoin.finrank (radical_integral a n (Nat.ne_zero_of_lt hn) ha),
    radical_minpoly a n hn ha, natDegree_X_pow_sub_C]

lemma cubic_not_splits_real (a : ℝ) (ha : a ^ 3 = 2) :
    ¬ (X ^ 3 - C (2 : ℝ)).Splits := by
  intro hs
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let q : ℝ[X] := X ^ 2 + C a * X + C (a ^ 2)
  have hq : q ∣ X ^ 3 - C (2 : ℝ) := by
    refine ⟨X - C a, ?_⟩
    rw [← ha]
    dsimp [q]
    simp only [map_pow]
    ring
  have hqs : q.Splits := hs.of_dvd (by
    exact (monic_X_pow_sub_C _ (by decide)).ne_zero) hq
  have hd : q.degree ≠ 0 := by
    have he : q.natDegree = 2 := by
      dsimp [q]
      compute_degree!
    exact degree_ne_of_natDegree_ne (n := 0) (by omega)
  obtain ⟨x, hx⟩ := hqs.exists_eval_eq_zero hd
  have he : x ^ 2 + a * x + a ^ 2 = 0 := by simpa [q] using hx
  have hp := sq_pos_of_ne_zero ha0
  nlinarith [sq_nonneg (2 * x + a)]

lemma quartic_not_splits_real (a : ℝ) (ha : a ^ 4 = 2) :
    ¬ (X ^ 4 - C (2 : ℝ)).Splits := by
  intro hs
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let q : ℝ[X] := X ^ 2 + C (a ^ 2)
  have hq : q ∣ X ^ 4 - C (2 : ℝ) := by
    refine ⟨X ^ 2 - C (a ^ 2), ?_⟩
    rw [← ha]
    dsimp [q]
    simp only [map_pow]
    ring
  have hqs : q.Splits := hs.of_dvd (monic_X_pow_sub_C _ (by decide)).ne_zero hq
  have hd : q.degree ≠ 0 := by
    have he : q.natDegree = 2 := by
      exact natDegree_X_pow_add_C
    exact degree_ne_of_natDegree_ne (n := 0) (by omega)
  obtain ⟨x, hx⟩ := hqs.exists_eval_eq_zero hd
  have he : x ^ 2 + a ^ 2 = 0 := by simpa [q] using hx
  nlinarith [sq_nonneg x, sq_pos_of_ne_zero ha0]

lemma radical_not_normal (a : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : a ^ n = 2) (hs : ¬ (X ^ n - C (2 : ℝ)).Splits) :
    ¬ Normal ℚ (adjoin ℚ {a}) := by
  intro h
  have hm := h.splits (AdjoinSimple.gen ℚ a)
  rw [minpoly_gen, radical_minpoly a n hn ha] at hm
  have hr := hm.map (algebraMap (adjoin ℚ {a}) ℝ)
  have he : ((X ^ n - C (2 : ℚ)).map (algebraMap ℚ (adjoin ℚ {a}))).map
      (algebraMap (adjoin ℚ {a}) ℝ) = X ^ n - C (2 : ℝ) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, map_ofNat]
  exact hs (he ▸ hr)

theorem cubicCounterexample : CubicCounterexample := by
  have hi := radical_integral cubeRoot 3 (by decide) cubeRoot_cube
  have hm : minpoly ℚ cubeRoot = cubicPolynomial :=
    radical_minpoly cubeRoot 3 (by decide) cubeRoot_cube
  have hs := SplittingField.splits cubicPolynomial
  have hd : (cubicPolynomial.map (algebraMap ℚ CubicSplittingField)).degree ≠ 0 := by
    rw [degree_map]
    exact degree_ne_of_natDegree_ne (by
      simp [cubicPolynomial])
  obtain ⟨b, hb⟩ := hs.exists_eval_eq_zero hd
  have hroot : b ∈ (minpoly ℚ cubeRoot).aroots CubicSplittingField := by
    rw [hm, mem_aroots]
    exact ⟨(radical_irreducible 3 (by decide)).ne_zero,
      (eval_map_algebraMap cubicPolynomial b).symm.trans hb⟩
  refine ⟨cubeRoot_cube, radical_finrank cubeRoot 3 (by decide) cubeRoot_cube,
    radical_not_normal cubeRoot 3 (by decide) cubeRoot_cube
      (cubic_not_splits_real cubeRoot cubeRoot_cube), inferInstance,
    Normal.of_isSplittingField cubicPolynomial, ?_⟩
  exact ⟨(algHomAdjoinIntegralEquiv ℚ hi).symm ⟨b, hroot⟩⟩

lemma middle_image : Middle.map Quartic.val = Square := by
  rw [Middle, adjoin_map, Set.image_singleton]
  have he : Quartic.val (fourthGenerator ^ 2) = Real.sqrt 2 := fourthRoot_square
  rw [he]
  rfl

lemma fourthGenerator_fourth : fourthGenerator ^ 4 = 2 := by
  apply Subtype.ext
  exact fourthRoot_fourth

lemma middle_finrank : Module.finrank ℚ Middle = 2 := by
  apply radical_finrank (fourthGenerator ^ 2) 2 (by decide)
  simpa only [← pow_mul] using fourthGenerator_fourth

lemma quartic_finrank : Module.finrank ℚ Quartic = 4 :=
  radical_finrank fourthRoot 4 (by decide) fourthRoot_fourth

lemma quartic_missing_nonreal_root :
    ∃ z : ℂ, aeval z quarticPolynomial = 0 ∧ z.im ≠ 0 ∧
      ∀ x : Quartic, ((x : ℝ) : ℂ) ≠ z := by
  refine ⟨(fourthRoot : ℂ) * Complex.I, ?_, ?_, ?_⟩
  · have hp : (fourthRoot : ℂ) ^ 4 = 2 := by
      exact_mod_cast fourthRoot_fourth
    simp [quarticPolynomial, mul_pow, hp]
  · have h0 : fourthRoot ≠ 0 := by
      intro h
      have hp := fourthRoot_fourth
      simp [h] at hp
    simpa using h0
  · intro x hx
    have hh := congrArg Complex.im hx
    have h0 : fourthRoot ≠ 0 := by
      intro h
      have hp := fourthRoot_fourth
      simp [h] at hp
    exact h0 (by simpa using hh.symm)

theorem towerCounterexample : TowerCounterexample := by
  let : FiniteDimensional ℚ Quartic :=
    adjoin.finiteDimensional (radical_integral fourthRoot 4 (by decide) fourthRoot_fourth)
  have ht := Module.finrank_mul_finrank ℚ Middle Quartic
  have hu : Module.finrank Middle Quartic = 2 := by
    rw [middle_finrank, quartic_finrank] at ht
    omega
  let : Algebra.IsQuadraticExtension ℚ Middle := ⟨middle_finrank⟩
  let : Algebra.IsQuadraticExtension Middle Quartic := ⟨hu⟩
  exact ⟨fourthRoot_square, fourthRoot_fourth, middle_image, middle_finrank,
    hu, quartic_finrank, inferInstance, inferInstance,
    radical_not_normal fourthRoot 4 (by decide) fourthRoot_fourth
      (quartic_not_splits_real fourthRoot fourthRoot_fourth),
    quartic_missing_nonreal_root⟩

end D07.Ch12.NormalCharacterizationsNonnormalTowers
