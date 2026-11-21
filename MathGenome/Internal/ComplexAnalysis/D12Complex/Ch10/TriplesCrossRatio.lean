import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.TriplesCrossRatio
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.Mobius

noncomputable section

/- Candidate-owned exports of the canonical objects shared with the independent Specs. -/
namespace D12Complex.TriplesCrossRatioDefinitions
abbrev IsMobiusTransformation := D12Complex.Mobius.IsMobiusTransformation
abbrev normalizedCoefficients := D12Complex.Mobius.normalizedCoefficients
abbrev crossRatio := D12Complex.Mobius.crossRatio
end D12Complex.TriplesCrossRatioDefinitions

namespace D12Complex.Mobius

private theorem finite_ne {p q : ℂ} (h : sphereFinite p ≠ sphereFinite q) : p ≠ q :=
  fun he => h (congrArg sphereFinite he)

private theorem normalized_finite (p q r : ℂ) :
    normalizedCoefficients (sphereFinite p) (sphereFinite q) (sphereFinite r) =
      !![q-r, -p*(q-r); q-p, -r*(q-p)] := by
  simp [normalizedCoefficients, finiteCoordinate, sphereFinite, sphereInfty]

private theorem normalized_r_infty (p q : ℂ) :
    normalizedCoefficients (sphereFinite p) (sphereFinite q) sphereInfty =
      !![1, -p; 0, q-p] := by
  simp [normalizedCoefficients, finiteCoordinate, sphereFinite, sphereInfty]

private theorem normalized_p_infty (q r : ℂ) :
    normalizedCoefficients sphereInfty (sphereFinite q) (sphereFinite r) =
      !![0, q-r; 1, -r] := by
  simp [normalizedCoefficients, finiteCoordinate, sphereFinite, sphereInfty]

private theorem normalized_q_infty (p r : ℂ) :
    normalizedCoefficients (sphereFinite p) sphereInfty (sphereFinite r) =
      !![1, -p; 1, -r] := by
  simp [normalizedCoefficients, finiteCoordinate, sphereFinite, sphereInfty]

theorem normalizedCoefficients_regular (p q r : RiemannSphere)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Regular (normalizedCoefficients p q r) := by
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => exact (hpq rfl).elim
    | coe q =>
      induction r using OnePoint.rec with
      | infty => exact (hpr rfl).elim
      | coe r =>
        change Regular (normalizedCoefficients sphereInfty (sphereFinite q) (sphereFinite r))
        rw [normalized_p_infty]
        simpa [Regular, Matrix.det_fin_two] using sub_ne_zero.mpr (finite_ne hqr).symm
  | coe p =>
    induction q using OnePoint.rec with
    | infty =>
      induction r using OnePoint.rec with
      | infty => exact (hqr rfl).elim
      | coe r =>
        change Regular (normalizedCoefficients (sphereFinite p) sphereInfty (sphereFinite r))
        rw [normalized_q_infty]
        simpa [Regular, Matrix.det_fin_two, sub_eq_add_neg, add_comm] using sub_ne_zero.mpr (finite_ne hpr)
    | coe q =>
      induction r using OnePoint.rec with
      | infty =>
        change Regular (normalizedCoefficients (sphereFinite p) (sphereFinite q) sphereInfty)
        rw [normalized_r_infty]
        simpa [Regular, Matrix.det_fin_two] using sub_ne_zero.mpr (finite_ne hpq).symm
      | coe r =>
        change Regular (normalizedCoefficients (sphereFinite p) (sphereFinite q) (sphereFinite r))
        rw [normalized_finite]
        have hd : (!![q-r, -p*(q-r); q-p, -r*(q-p)] : Coefficients).det =
            (q-r)*(q-p)*(p-r) := by simp [Matrix.det_fin_two]; ring
        rw [Regular, hd]
        exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (finite_ne hqr))
          (sub_ne_zero.mpr (finite_ne hpq).symm)) (sub_ne_zero.mpr (finite_ne hpr))

theorem crossRatio_finite (z p q r : ℂ) (_hpq : p ≠ q) (_hpr : p ≠ r) (_hqr : q ≠ r) :
    crossRatio (sphereFinite z) (sphereFinite p) (sphereFinite q) (sphereFinite r) =
      spherePair ((z-p)*(q-r)) ((z-r)*(q-p)) := by
  rw [crossRatio, normalized_finite]
  change spherePair ((q-r)*z + -p*(q-r)) ((q-p)*z + -r*(q-p)) = _
  congr 1 <;> ring

theorem crossRatio_finite_quotient (z p q r : ℂ)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hzr : z ≠ r) :
    crossRatio (sphereFinite z) (sphereFinite p) (sphereFinite q) (sphereFinite r) =
      sphereFinite (((z-p)*(q-r))/((z-r)*(q-p))) := by
  rw [crossRatio_finite z p q r hpq hpr hqr]
  exact ite_eq_right (mul_ne_zero (sub_ne_zero.mpr hzr) (sub_ne_zero.mpr hpq.symm))

theorem crossRatio_infinity_entries (z p q : ℂ) (_hpq : p ≠ q) :
    (crossRatio (sphereFinite z) (sphereFinite p) (sphereFinite q) sphereInfty =
      spherePair (z-p) (q-p)) ∧
    (crossRatio (sphereFinite z) sphereInfty (sphereFinite p) (sphereFinite q) =
      spherePair (p-q) (z-q)) ∧
    (crossRatio (sphereFinite z) (sphereFinite p) sphereInfty (sphereFinite q) =
      spherePair (z-p) (z-q)) := by
  simp only [crossRatio, normalized_r_infty, normalized_p_infty, normalized_q_infty]
  simp [mobiusMap, sphereFinite, sub_eq_add_neg]

theorem crossRatio_infty (p q r : ℂ) (hpq : p ≠ q) (_hpr : p ≠ r) (_hqr : q ≠ r) :
    crossRatio sphereInfty (sphereFinite p) (sphereFinite q) (sphereFinite r) =
      sphereFinite ((q-r)/(q-p)) := by
  rw [crossRatio, normalized_finite]
  change spherePair (q-r) (q-p) = _
  exact ite_eq_right (sub_ne_zero.mpr hpq.symm)


private theorem crossRatio_normalizes_finite (p q r : ℂ)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    crossRatio (sphereFinite p) (sphereFinite p) (sphereFinite q) (sphereFinite r) = sphereFinite 0 ∧
    crossRatio (sphereFinite q) (sphereFinite p) (sphereFinite q) (sphereFinite r) = sphereFinite 1 ∧
    crossRatio (sphereFinite r) (sphereFinite p) (sphereFinite q) (sphereFinite r) = sphereInfty := by
  rw [crossRatio_finite p p q r hpq hpr hqr, crossRatio_finite q p q r hpq hpr hqr,
    crossRatio_finite r p q r hpq hpr hqr]
  simp [spherePair, sub_ne_zero.mpr hpr, sub_ne_zero.mpr hpq.symm,
    sub_ne_zero.mpr hqr, mul_comm]

theorem crossRatio_normalizes (p q r : RiemannSphere)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    crossRatio p p q r = sphereFinite 0 ∧
    crossRatio q p q r = sphereFinite 1 ∧
    crossRatio r p q r = sphereInfty := by
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => exact (hpq rfl).elim
    | coe q =>
      induction r using OnePoint.rec with
      | infty => exact (hpr rfl).elim
      | coe r =>
        have h := finite_ne hqr
        change crossRatio sphereInfty sphereInfty (sphereFinite q) (sphereFinite r) = _ ∧ _
        refine ⟨?_, ?_, ?_⟩
        · erw [crossRatio, normalized_p_infty]
          change spherePair 0 1 = sphereFinite 0
          simp [spherePair]
        · erw [(crossRatio_infinity_entries q q r h).2.1]
          simp [spherePair, sub_ne_zero.mpr h]
        · erw [(crossRatio_infinity_entries r q r h).2.1]
          simp [spherePair]
  | coe p =>
    induction q using OnePoint.rec with
    | infty =>
      induction r using OnePoint.rec with
      | infty => exact (hqr rfl).elim
      | coe r =>
        have h := finite_ne hpr
        change crossRatio (sphereFinite p) (sphereFinite p) sphereInfty (sphereFinite r) = _ ∧ _
        refine ⟨?_, ?_, ?_⟩
        · erw [(crossRatio_infinity_entries p p r h).2.2]
          simp [spherePair, sub_ne_zero.mpr h]
        · erw [crossRatio, normalized_q_infty]
          change spherePair 1 1 = sphereFinite 1
          simp [spherePair]
        · erw [(crossRatio_infinity_entries r p r h).2.2]
          simp [spherePair]
    | coe q =>
      induction r using OnePoint.rec with
      | infty =>
        have h := finite_ne hpq
        change crossRatio (sphereFinite p) (sphereFinite p) (sphereFinite q) sphereInfty = _ ∧ _
        refine ⟨?_, ?_, ?_⟩
        · erw [(crossRatio_infinity_entries p p q h).1]
          simp [spherePair, sub_ne_zero.mpr h.symm]
        · erw [(crossRatio_infinity_entries q p q h).1]
          simp [spherePair, sub_ne_zero.mpr h.symm]
        · erw [crossRatio, normalized_r_infty]
          change spherePair 1 0 = sphereInfty
          simp [spherePair]
      | coe r =>
        exact crossRatio_normalizes_finite p q r (finite_ne hpq) (finite_ne hpr) (finite_ne hqr)


/-- Fixing the three standard points forces the identity sphere map. -/
theorem mobiusMap_eq_id_of_fix_standard (M : Coefficients) (hM : Regular M)
    (h0 : mobiusMap M (sphereFinite 0) = sphereFinite 0)
    (h1 : mobiusMap M (sphereFinite 1) = sphereFinite 1)
    (hi : mobiusMap M sphereInfty = sphereInfty) : mobiusMap M = id := by
  have hc : M 1 0 = 0 := (spherePair_eq_infty_iff _ _).mp hi
  have hd : M 1 1 ≠ 0 := by
    intro hd
    apply hM
    simp [Matrix.det_fin_two, hc, hd]
  have hb : M 0 1 = 0 := by
    have he : sphereFinite (M 0 1 / M 1 1) = sphereFinite 0 := by
      simpa [mobiusMap, spherePair, sphereFinite, hc, hd] using h0
    exact (div_eq_zero_iff.mp (sphereFinite_injective he)).resolve_right hd
  have ha : M 0 0 = M 1 1 := by
    have he : sphereFinite (M 0 0 / M 1 1) = sphereFinite 1 := by
      simpa [mobiusMap, spherePair, sphereFinite, hc, hb, hd] using h1
    exact (div_eq_one_iff_eq hd).mp (sphereFinite_injective he)
  have hmat : M = M 1 1 • (1 : Coefficients) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
  rw [hmat, mobiusMap_smul _ _ hd, mobiusMap_one]

private theorem mobiusMap_eq_of_standard (M N : Coefficients) (hM : Regular M) (hN : Regular N)
    (h0 : mobiusMap M (sphereFinite 0) = mobiusMap N (sphereFinite 0))
    (h1 : mobiusMap M (sphereFinite 1) = mobiusMap N (sphereFinite 1))
    (hi : mobiusMap M sphereInfty = mobiusMap N sphereInfty) : mobiusMap M = mobiusMap N := by
  have hI := regular_inverseCoefficients N hN
  have hfix (p : RiemannSphere) (hp : mobiusMap M p = mobiusMap N p) :
      mobiusMap (inverseCoefficients N * M) p = p := by
    rw [mobiusMap_mul _ _ hI hM, Function.comp_apply, hp]
    exact (mobiusMap_inverse N hN).1 p
  have hid := mobiusMap_eq_id_of_fix_standard _ (regular_mul _ _ hI hM)
    (hfix _ h0) (hfix _ h1) (hfix _ hi)
  funext p
  apply (mobiusMap_bijective (inverseCoefficients N) hI).1
  have hp := congrFun hid p
  rw [mobiusMap_mul _ _ hI hM] at hp
  exact hp.trans ((mobiusMap_inverse N hN).1 p).symm

/-- Two nonsingular fractional linear maps agreeing on a distinct triple agree everywhere. -/
theorem mobiusMap_eq_of_triple (M N : Coefficients) (hM : Regular M) (hN : Regular N)
    (p q r : RiemannSphere) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : mobiusMap M p = mobiusMap N p)
    (hq : mobiusMap M q = mobiusMap N q)
    (hr : mobiusMap M r = mobiusMap N r) : mobiusMap M = mobiusMap N := by
  let A := normalizedCoefficients p q r
  let B := inverseCoefficients A
  have hA : Regular A := normalizedCoefficients_regular p q r hpq hpr hqr
  have hB : Regular B := regular_inverseCoefficients A hA
  obtain ⟨hAp, hAq, hAr⟩ := crossRatio_normalizes p q r hpq hpr hqr
  have hBp : mobiusMap B (sphereFinite 0) = p := by
    rw [← hAp]
    exact (mobiusMap_inverse A hA).1 p
  have hBq : mobiusMap B (sphereFinite 1) = q := by
    rw [← hAq]
    exact (mobiusMap_inverse A hA).1 q
  have hBr : mobiusMap B sphereInfty = r := by
    rw [← hAr]
    exact (mobiusMap_inverse A hA).1 r
  have he : mobiusMap (M * B) = mobiusMap (N * B) := by
    apply mobiusMap_eq_of_standard _ _ (regular_mul _ _ hM hB) (regular_mul _ _ hN hB)
    · simpa only [mobiusMap_mul _ _ hM hB, mobiusMap_mul _ _ hN hB,
        Function.comp_apply, hBp] using hp
    · simpa only [mobiusMap_mul _ _ hM hB, mobiusMap_mul _ _ hN hB,
        Function.comp_apply, hBq] using hq
    · simpa only [mobiusMap_mul _ _ hM hB, mobiusMap_mul _ _ hN hB,
        Function.comp_apply, hBr] using hr
  funext z
  have hz := congrFun he (mobiusMap A z)
  have hBA : mobiusMap B (mobiusMap A z) = z := (mobiusMap_inverse A hA).1 z
  simpa only [mobiusMap_mul _ _ hM hB, mobiusMap_mul _ _ hN hB,
    Function.comp_apply, hBA] using hz

theorem mobius_triples_existsUnique (p q r P Q R : RiemannSphere)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    ∃! F : RiemannSphere → RiemannSphere,
      IsMobiusTransformation F ∧ F p = P ∧ F q = Q ∧ F r = R := by
  let A := normalizedCoefficients p q r
  let C := normalizedCoefficients P Q R
  let D := inverseCoefficients C
  have hA : Regular A := normalizedCoefficients_regular p q r hpq hpr hqr
  have hC : Regular C := normalizedCoefficients_regular P Q R hPQ hPR hQR
  have hD : Regular D := regular_inverseCoefficients C hC
  have hT : Regular (D * A) := regular_mul _ _ hD hA
  obtain ⟨hAp, hAq, hAr⟩ := crossRatio_normalizes p q r hpq hpr hqr
  obtain ⟨hCP, hCQ, hCR⟩ := crossRatio_normalizes P Q R hPQ hPR hQR
  have hTp : mobiusMap (D * A) p = P := by
    rw [mobiusMap_mul _ _ hD hA, Function.comp_apply]
    change mobiusMap D (crossRatio p p q r) = P
    rw [hAp, ← hCP]
    exact (mobiusMap_inverse C hC).1 P
  have hTq : mobiusMap (D * A) q = Q := by
    rw [mobiusMap_mul _ _ hD hA, Function.comp_apply]
    change mobiusMap D (crossRatio q p q r) = Q
    rw [hAq, ← hCQ]
    exact (mobiusMap_inverse C hC).1 Q
  have hTr : mobiusMap (D * A) r = R := by
    rw [mobiusMap_mul _ _ hD hA, Function.comp_apply]
    change mobiusMap D (crossRatio r p q r) = R
    rw [hAr, ← hCR]
    exact (mobiusMap_inverse C hC).1 R
  refine ⟨mobiusMap (D * A), ⟨⟨D * A, hT, rfl⟩, hTp, hTq, hTr⟩, ?_⟩
  rintro F ⟨⟨M, hM, rfl⟩, hp, hq, hr⟩
  exact mobiusMap_eq_of_triple M (D * A) hM hT p q r hpq hpr hqr
    (hp.trans hTp.symm) (hq.trans hTq.symm) (hr.trans hTr.symm)

theorem crossRatio_invariant (M : Coefficients) (z p q r : RiemannSphere)
    (hM : Regular M) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    crossRatio (mobiusMap M z) (mobiusMap M p) (mobiusMap M q) (mobiusMap M r) =
      crossRatio z p q r := by
  have hinj := (mobiusMap_bijective M hM).1
  let A := normalizedCoefficients p q r
  let B := normalizedCoefficients (mobiusMap M p) (mobiusMap M q) (mobiusMap M r)
  have hA : Regular A := normalizedCoefficients_regular p q r hpq hpr hqr
  have hB : Regular B := normalizedCoefficients_regular _ _ _
    (hinj.ne hpq) (hinj.ne hpr) (hinj.ne hqr)
  obtain ⟨hAp, hAq, hAr⟩ := crossRatio_normalizes p q r hpq hpr hqr
  obtain ⟨hBp, hBq, hBr⟩ := crossRatio_normalizes _ _ _
    (hinj.ne hpq) (hinj.ne hpr) (hinj.ne hqr)
  have he : mobiusMap (B * M) = mobiusMap A := by
    apply mobiusMap_eq_of_triple _ _ (regular_mul _ _ hB hM) hA p q r hpq hpr hqr
    · rw [mobiusMap_mul _ _ hB hM, Function.comp_apply]
      exact hBp.trans hAp.symm
    · rw [mobiusMap_mul _ _ hB hM, Function.comp_apply]
      exact hBq.trans hAq.symm
    · rw [mobiusMap_mul _ _ hB hM, Function.comp_apply]
      exact hBr.trans hAr.symm
  have hz := congrFun he z
  rw [mobiusMap_mul _ _ hB hM] at hz
  exact hz

theorem crossRatio_continuous (p q r : RiemannSphere)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Continuous (fun z => crossRatio z p q r) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((mobiusMap_holomorphic _ (normalizedCoefficients_regular p q r hpq hpr hqr)).2
    z (Set.mem_univ _)).1

theorem crossRatio_reciprocal_source (p q r : RiemannSphere) (w : ℂ) :
    crossRatio (infinityParametrization w) p q r =
      spherePair
        (normalizedCoefficients p q r 0 0 + normalizedCoefficients p q r 0 1 * w)
        (normalizedCoefficients p q r 1 0 + normalizedCoefficients p q r 1 1 * w) :=
  mobiusMap_infinityParametrization (normalizedCoefficients p q r) w

end D12Complex.Mobius
