import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.PositiveRoots
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Archimedean
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Nonnegative roots and rational powers

The root is the supremum construction of K03.01.positive_roots. Existence
of a nonnegative power preimage is obtained from `NNReal.powOrderIso`, whose
surjectivity proof uses continuity and the intermediate value theorem, without
logarithms. The least-upper-bound characterization then identifies the preimage
with the constructed supremum. Rational powers are defined using these roots
and integer powers, including reciprocals. Their comparison with Mathlib's
`Real.rpow` is proved, then used to transport its algebraic laws. This last
library proof route uses the existing analytic power API, rather than the
manuscript's common-denominator proof. No downstream project goal is imported.
-/

namespace SingleVariableAnalysis

/-- The source's supremum construction; its root properties require `0 < m`
and `0 ≤ a`. Values outside this domain carry no root assertion. -/
noncomputable def nonnegativeRoot (m : ℕ) (a : ℝ) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ t ^ m ≤ a}

/-- Rational powers from the nonnegative root of the reduced positive
denominator and the integer numerator. Laws at nonpositive bases are only
asserted below for base zero and strictly positive exponents. -/
noncomputable def rationalPower (a : ℝ) (q : ℚ) : ℝ :=
  nonnegativeRoot q.den a ^ q.num

private theorem nonnegative_power_preimage (m : ℕ) (hm : 0 < m)
    (a : ℝ) (ha : 0 ≤ a) : ∃ r : ℝ, 0 ≤ r ∧ r ^ m = a := by
  obtain ⟨r, hr⟩ := (NNReal.powOrderIso m (Nat.ne_of_gt hm)).surjective ⟨a, ha⟩
  exact ⟨r, r.property, congrArg (fun x : NNReal => (x : ℝ)) hr⟩

/-- Any nonnegative power preimage is the supremum of the defining set. -/
private theorem root_eq_of_power (m : ℕ) (hm : 0 < m) (a r : ℝ)
    (hr : 0 ≤ r) (hpow : r ^ m = a) : nonnegativeRoot m a = r := by
  apply (isLUB_csSup ?_ ?_).unique ?_
  · exact ⟨r, hr, hpow.le⟩
  · refine ⟨r, ?_⟩
    intro t ht
    exact (pow_le_pow_iff_left₀ ht.1 hr (Nat.ne_of_gt hm)).mp (ht.2.trans_eq hpow.symm)
  · constructor
    · intro t ht
      exact (pow_le_pow_iff_left₀ ht.1 hr (Nat.ne_of_gt hm)).mp
        (ht.2.trans_eq hpow.symm)
    · intro b hb
      exact hb ⟨hr, hpow.le⟩

theorem nonnegativeRoot_nonneg (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ nonnegativeRoot m a := by
  obtain ⟨r, hr, hp⟩ := nonnegative_power_preimage m hm a ha
  rw [root_eq_of_power m hm a r hr hp]
  exact hr

theorem nonnegativeRoot_pow (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a) :
    nonnegativeRoot m a ^ m = a := by
  obtain ⟨r, hr, hp⟩ := nonnegative_power_preimage m hm a ha
  rw [root_eq_of_power m hm a r hr hp]
  exact hp

theorem nonnegativeRoot_isLUB (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a) :
    IsLUB {t : ℝ | 0 ≤ t ∧ t ^ m ≤ a} (nonnegativeRoot m a) := by
  constructor
  · intro t ht
    exact (pow_le_pow_iff_left₀ ht.1 (nonnegativeRoot_nonneg m hm a ha)
      (Nat.ne_of_gt hm)).mp (ht.2.trans_eq (nonnegativeRoot_pow m hm a ha).symm)
  · intro b hb
    exact hb ⟨nonnegativeRoot_nonneg m hm a ha, (nonnegativeRoot_pow m hm a ha).le⟩

theorem nonnegativeRoot_unique (m : ℕ) (hm : 0 < m) (a : ℝ) (_ha : 0 ≤ a)
    (r : ℝ) (hr : 0 ≤ r) (hp : r ^ m = a) : r = nonnegativeRoot m a :=
  (root_eq_of_power m hm a r hr hp).symm

theorem nonnegativeRoot_existsUnique (a : ℝ) (ha : 0 ≤ a) (m : ℕ) (hm : 0 < m) :
    ∃! r : ℝ, 0 ≤ r ∧ r ^ m = a := by
  exact ⟨nonnegativeRoot m a, ⟨nonnegativeRoot_nonneg m hm a ha,
    nonnegativeRoot_pow m hm a ha⟩,
    fun r hr => nonnegativeRoot_unique m hm a ha r hr.1 hr.2⟩

theorem nonnegativeRoot_pos (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) :
    0 < nonnegativeRoot m a := by
  have hn := nonnegativeRoot_nonneg m hm a ha.le
  have hp := nonnegativeRoot_pow m hm a ha.le
  apply lt_of_le_of_ne hn
  intro hz
  rw [← hz, zero_pow (Nat.ne_of_gt hm)] at hp
  exact ha.ne hp

theorem nonnegativeRoot_zero (m : ℕ) (hm : 0 < m) : nonnegativeRoot m 0 = 0 := by
  exact root_eq_of_power m hm 0 0 le_rfl (zero_pow (Nat.ne_of_gt hm))

theorem nonnegativeRoot_sqrt (a : ℝ) (ha : 0 ≤ a) :
    nonnegativeRoot 2 a = Real.sqrt a :=
  root_eq_of_power 2 (by decide) a (Real.sqrt a) (Real.sqrt_nonneg a) (Real.sq_sqrt ha)

/-- Comparison used to transport the library's algebraic power laws. -/
theorem nonnegativeRoot_eq_rpow (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a) :
    nonnegativeRoot m a = a ^ ((m : ℝ)⁻¹) :=
  root_eq_of_power m hm a _ (Real.rpow_nonneg ha _)
    (Real.rpow_inv_natCast_pow ha (Nat.ne_of_gt hm))

theorem rationalPower_eq_rpow (a : ℝ) (ha : 0 < a) (q : ℚ) :
    rationalPower a q = a ^ (q : ℝ) := by
  rw [rationalPower, nonnegativeRoot_eq_rpow q.den q.den_pos a ha.le,
    ← Real.rpow_intCast, ← Real.rpow_mul ha.le]
  congr 1
  rw [Rat.cast_def, div_eq_mul_inv, mul_comm]

/-- Any fraction representation with positive denominator gives the same
value, whether or not the fraction is reduced. -/
theorem rationalPower_fraction (a : ℝ) (ha : 0 < a) (p : ℤ) (d : ℕ) (hd : 0 < d) :
    rationalPower a ((p : ℚ) / (d : ℚ)) = nonnegativeRoot d a ^ p := by
  rw [rationalPower_eq_rpow a ha, nonnegativeRoot_eq_rpow d hd a ha.le,
    ← Real.rpow_intCast, ← Real.rpow_mul ha.le]
  congr 1
  push_cast
  ring

theorem rationalPower_fraction_independent (a : ℝ) (ha : 0 < a)
    (p s : ℤ) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (h : (p : ℚ) / d = (s : ℚ) / e) :
    nonnegativeRoot d a ^ p = nonnegativeRoot e a ^ s := by
  rw [← rationalPower_fraction a ha p d hd, ← rationalPower_fraction a ha s e he, h]

theorem rationalPower_pos (a : ℝ) (ha : 0 < a) (q : ℚ) : 0 < rationalPower a q := by
  rw [rationalPower_eq_rpow a ha]
  exact Real.rpow_pos_of_pos ha _

theorem rationalPower_int (a : ℝ) (ha : 0 < a) (p : ℤ) :
    rationalPower a (p : ℚ) = a ^ p := by
  rw [rationalPower_eq_rpow a ha]
  simp [Real.rpow_intCast]

theorem rationalPower_zero_exponent (a : ℝ) (ha : 0 < a) : rationalPower a 0 = 1 := by
  simpa using rationalPower_int a ha 0

theorem rationalPower_one_exponent (a : ℝ) (ha : 0 < a) : rationalPower a 1 = a := by
  simpa using rationalPower_int a ha 1

theorem rationalPower_add (a : ℝ) (ha : 0 < a) (q r : ℚ) :
    rationalPower a (q + r) = rationalPower a q * rationalPower a r := by
  simp only [rationalPower_eq_rpow a ha, Rat.cast_add]
  exact Real.rpow_add ha _ _

theorem rationalPower_neg (a : ℝ) (ha : 0 < a) (q : ℚ) :
    rationalPower a (-q) = (rationalPower a q)⁻¹ := by
  simp only [rationalPower_eq_rpow a ha, Rat.cast_neg]
  exact Real.rpow_neg ha.le _

theorem rationalPower_sub (a : ℝ) (ha : 0 < a) (q r : ℚ) :
    rationalPower a (q - r) = rationalPower a q / rationalPower a r := by
  simp only [rationalPower_eq_rpow a ha, Rat.cast_sub]
  exact Real.rpow_sub ha _ _

theorem rationalPower_mul_base (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (q : ℚ) :
    rationalPower (a * b) q = rationalPower a q * rationalPower b q := by
  rw [rationalPower_eq_rpow _ (mul_pos ha hb), rationalPower_eq_rpow a ha,
    rationalPower_eq_rpow b hb]
  exact Real.mul_rpow ha.le hb.le

theorem rationalPower_div_base (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (q : ℚ) :
    rationalPower (a / b) q = rationalPower a q / rationalPower b q := by
  rw [rationalPower_eq_rpow _ (div_pos ha hb), rationalPower_eq_rpow a ha,
    rationalPower_eq_rpow b hb]
  exact Real.div_rpow ha.le hb.le _

theorem rationalPower_mul_exponent (a : ℝ) (ha : 0 < a) (q r : ℚ) :
    rationalPower (rationalPower a q) r = rationalPower a (q * r) := by
  rw [rationalPower_eq_rpow _ (rationalPower_pos a ha q),
    rationalPower_eq_rpow a ha, rationalPower_eq_rpow a ha, Rat.cast_mul]
  exact (Real.rpow_mul ha.le _ _).symm

theorem rationalPower_zero_base (q : ℚ) (hq : 0 < q) : rationalPower 0 q = 0 := by
  rw [rationalPower, nonnegativeRoot_zero q.den q.den_pos]
  exact zero_zpow q.num (ne_of_gt (Rat.num_pos.mpr hq))

end SingleVariableAnalysis
