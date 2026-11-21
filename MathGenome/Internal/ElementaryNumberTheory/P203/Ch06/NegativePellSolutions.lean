import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.NegativePellSolutions
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch06.FundamentalPellSolution
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch06.PellSigns

namespace P203.Ch06.NegativePellSolutions
open P203Specs.Ch06.PellUnits
open P203Specs.Ch06.FundamentalPellSolution
open P203Specs.Ch06.NegativePellSolutions

lemma norm_pair (D x y : ℤ) :
    norm (⟨x, y⟩ : IntegralQuadratic D) = x ^ 2 - D * y ^ 2 :=
  (P203.Ch06.PellUnits.coefficient_formulas D x y).2.2

lemma value_mul (D : ℤ) (hD : 0 < D) (u v : IntegralQuadratic D) :
    realValue D (u * v) = realValue D u * realValue D v :=
  (realEmbedding D hD).map_mul u v

lemma value_pow (D : ℤ) (hD : 0 < D) (u : IntegralQuadratic D) (j : ℕ) :
    realValue D (u ^ j) = realValue D u ^ j :=
  (realEmbedding D hD).map_pow u j

/-- The integral inverse given by the signed conjugate. -/
def integralInverse {D : ℤ} (u : IntegralQuadratic D) : IntegralQuadratic D :=
  (norm u : IntegralQuadratic D) * conjugate u

lemma inverse_norm {D : ℤ} (u : IntegralQuadratic D)
    (hu : norm u = 1 ∨ norm u = -1) : norm (integralInverse u) = norm u := by
  simp only [integralInverse, norm, conjugate, Zsqrtd.norm_mul, Zsqrtd.norm_intCast,
    Zsqrtd.norm_conj]
  rcases hu with hu | hu <;> change Zsqrtd.norm u = _ at hu <;> rw [hu] <;> norm_num

lemma inverse_value (D : ℤ) (hD : 0 < D) (u : IntegralQuadratic D)
    (hu : norm u = 1 ∨ norm u = -1) :
    realValue D (integralInverse u) = (realValue D u)⁻¹ := by
  have hi := (P203.Ch06.PellUnits.signed_inverse D u (norm u) hu rfl).1
  have hv := congrArg (realEmbedding D hD) hi
  change realValue D (u * integralInverse u) = realValue D 1 at hv
  rw [value_mul D hD] at hv
  have hone : realValue D (1 : IntegralQuadratic D) = 1 := (realEmbedding D hD).map_one
  rw [hone] at hv
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hv)

lemma quotient_value (D : ℤ) (hD : 0 < D) (v u : IntegralQuadratic D)
    (hu : norm u = 1 ∨ norm u = -1) :
    realValue D (v * integralInverse u) = realValue D v / realValue D u := by
  rw [value_mul D hD, inverse_value D hD u hu, div_eq_mul_inv]

theorem even_nonexistence : EvenNonexistence := by
  intro D hD hns he hn
  have ho := (P203.pell_fundamental_signs D hD hns).2.2.1.mp hn
  exact (Nat.not_even_iff_odd.mpr ho) he

theorem negative_coordinates : NegativeCoordinates := by
  intro D hD u hu
  have hi := (P203.Ch06.PellUnits.unit_criterion D u).mpr (Or.inr hu.1)
  exact ⟨hi, (P203.Ch06.PellUnits.positive_coordinates D hD u hi).mp hu.2.1⟩

theorem negative_exists : NegativeExists := by
  intro D hD hns ho
  have hl := (P203.pell_fundamental_signs D hD hns).2.2.2 ho
  let m : IntegralQuadratic D := ⟨P203Specs.pellPeriodNumerator D 1,
    P203Specs.pellPeriodDenominator D 1⟩
  have hn : norm m = -1 := (norm_pair _ _ _).trans hl.1.2.2
  have hi := (P203.Ch06.PellUnits.unit_criterion D m).mpr (Or.inr hn)
  have hm : LeastNegative D m := by
    refine ⟨hn, (P203.Ch06.PellUnits.positive_coordinates D hD m hi).mpr
      ⟨hl.1.1, hl.1.2.1⟩, ?_⟩
    intro v hv hvpos
    have hvi := (P203.Ch06.PellUnits.unit_criterion D v).mpr (Or.inr hv)
    have hc := (P203.Ch06.PellUnits.positive_coordinates D hD v hvi).mp hvpos
    exact hl.2 v.re v.im ⟨hc.1, hc.2, by
      simpa only [norm, Zsqrtd.norm_def, pow_two, mul_assoc] using hv⟩
  refine ⟨m, hm, ?_⟩
  intro v hv
  apply (P203.Ch06.PellUnits.real_model D hD hns).1
  exact le_antisymm (hv.2.2 m hm.1 hm.2.1) (hm.2.2 v hv.1 hv.2.1)

/-- Dividing a smaller norm-one element by the least negative unit (in one
of the two orders) would contradict the latter's minimality. -/
lemma least_negative_square (D : ℤ) (hD : 0 < D) (hns : ¬IsSquare D)
    (m : IntegralQuadratic D) (hm : LeastNegative D m) : LeastPositive D (m ^ 2) := by
  have hn : norm (m ^ 2) = 1 := by
    change Zsqrtd.normMonoidHom (m ^ 2) = 1
    rw [map_pow]
    change norm m ^ 2 = 1
    rw [hm.1]
    norm_num
  have ha : 0 < realValue D m := lt_trans zero_lt_one hm.2.1
  refine ⟨hn, ?_, ?_⟩
  · rw [value_pow D hD]
    nlinarith [hm.2.1]
  · intro v hv hvpos
    rw [value_pow D hD]
    by_contra hle
    have hlt : realValue D v < realValue D m ^ 2 := lt_of_not_ge hle
    have hb : 0 < realValue D v := lt_trans zero_lt_one hvpos
    rcases lt_trichotomy (realValue D v) (realValue D m) with hvm | heq | hmv
    · let w := m * integralInverse v
      have hwn : norm w = -1 := by
        change norm (m * integralInverse v) = -1
        rw [(P203.Ch06.PellUnits.norm_laws D hD _ _).2.1,
          inverse_norm v (Or.inl hv), hv, hm.1]
        norm_num
      have hw : realValue D w = realValue D m / realValue D v :=
        quotient_value D hD m v (Or.inl hv)
      have hwpos : 1 < realValue D w := by
        rw [hw]
        exact (one_lt_div hb).mpr hvm
      have hwlt : realValue D w < realValue D m := by
        rw [hw, div_lt_iff₀ hb]
        nlinarith
      have := hm.2.2 w hwn hwpos
      linarith
    · have he := (P203.Ch06.PellUnits.real_model D hD hns).1 heq
      have hh := congrArg norm he
      rw [hv, hm.1] at hh
      norm_num at hh
    · let w := v * integralInverse m
      have hwn : norm w = -1 := by
        change norm (v * integralInverse m) = -1
        rw [(P203.Ch06.PellUnits.norm_laws D hD _ _).2.1,
          inverse_norm m (Or.inr hm.1), hv, hm.1]
        norm_num
      have hw : realValue D w = realValue D v / realValue D m :=
        quotient_value D hD v m (Or.inr hm.1)
      have hwpos : 1 < realValue D w := by
        rw [hw]
        exact (one_lt_div ha).mpr hmv
      have hwlt : realValue D w < realValue D m := by
        rw [hw, div_lt_iff₀ ha]
        nlinarith
      have := hm.2.2 w hwn hwpos
      linarith

theorem fundamental_square : FundamentalSquare := by
  intro D hD hns m p hm hp
  exact P203.Ch06.FundamentalPellSolution.least_unique hD hns hp
    (least_negative_square D hD hns m hm)

theorem negative_parametrization : NegativeParametrization := by
  intro D hD hns m p hm hp x y hx hy hxy
  let v : IntegralQuadratic D := ⟨x, y⟩
  have hv : norm v = -1 := (norm_pair D x y).trans hxy
  have hvi := (P203.Ch06.PellUnits.unit_criterion D v).mpr (Or.inr hv)
  have hvpos : 1 < realValue D v :=
    (P203.Ch06.PellUnits.positive_coordinates D hD v hvi).mpr ⟨hx, hy⟩
  have hmv := hm.2.2 v hv hvpos
  have hmpos : 0 < realValue D m := lt_trans zero_lt_one hm.2.1
  let w := v * integralInverse m
  have hwn : norm w = 1 := by
    change norm (v * integralInverse m) = 1
    rw [(P203.Ch06.PellUnits.norm_laws D hD _ _).2.1,
      inverse_norm m (Or.inr hm.1), hv, hm.1]
    norm_num
  have hw : realValue D w = realValue D v / realValue D m :=
    quotient_value D hD v m (Or.inr hm.1)
  have hwge : 1 ≤ realValue D w := by
    rw [hw]
    exact (one_le_div hmpos).mpr hmv
  have hex : ∃ j : ℕ, realValue D v = realValue D m * realValue D p ^ j := by
    rcases hwge.eq_or_lt with heq | hlt
    · refine ⟨0, ?_⟩
      have hh : realValue D v / realValue D m = 1 := hw.symm.trans heq.symm
      have hh' := (div_eq_iff (ne_of_gt hmpos)).mp hh
      simpa using hh'
    · have hwi := (P203.Ch06.PellUnits.unit_criterion D w).mpr (Or.inl hwn)
      have hc := (P203.Ch06.PellUnits.positive_coordinates D hD w hwi).mp hlt
      have hweq : w.re ^ 2 - D * w.im ^ 2 = 1 := by
        simpa only [norm, Zsqrtd.norm_def, pow_two, mul_assoc] using hwn
      obtain ⟨j, hj, _⟩ := P203.Ch06.FundamentalPellSolution.positive_parametrization
        D hD hns p hp w.re w.im hc.1 hc.2 hweq
      have hj' : realValue D w = realValue D p ^ j := hj.2
      rw [hw] at hj'
      refine ⟨j, ?_⟩
      have hh := (div_eq_iff (ne_of_gt hmpos)).mp hj'
      simpa only [mul_comm] using hh
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, ?_⟩
  intro k hk
  apply (pow_right_strictMono₀ hp.2.1).injective
  exact mul_left_cancel₀ (ne_of_gt hmpos) (hk.symm.trans hj)

theorem negative_products : NegativeProducts := by
  intro D hD hns m p hm hp j
  have hn : norm (m * p ^ j) = -1 := by
    change Zsqrtd.normMonoidHom (m * p ^ j) = -1
    rw [map_mul, map_pow]
    change norm m * norm p ^ j = -1
    rw [hm.1, hp.1, one_pow, mul_one]
  have he : realValue D (m * p ^ j) = realValue D m * realValue D p ^ j := by
    rw [value_mul D hD, value_pow D hD]
  have hv : 1 < realValue D (m * p ^ j) := by
    rw [he]
    have hj : 1 ≤ realValue D p ^ j := one_le_pow₀ hp.2.1.le
    nlinarith [hm.2.1]
  have hi := (P203.Ch06.PellUnits.unit_criterion D _).mpr (Or.inr hn)
  have hc := (P203.Ch06.PellUnits.positive_coordinates D hD _ hi).mp hv
  exact ⟨hn, hc.1, hc.2, he⟩

theorem negative_solution_set : NegativeSolutionSet := by
  intro D hD hns m p hm hp
  ext r
  constructor
  · rintro ⟨x, y, hx, hy, hn, rfl⟩
    obtain ⟨j, hj, _⟩ := negative_parametrization D hD hns m p hm hp x y hx hy hn
    exact ⟨j, hj⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨hn, hx, hy, he⟩ := negative_products D hD hns m p hm hp j
    refine ⟨(m * p ^ j).re, (m * p ^ j).im, hx, hy, ?_, he.symm⟩
    simpa only [norm, Zsqrtd.norm_def, pow_two, mul_assoc] using hn

end P203.Ch06.NegativePellSolutions
