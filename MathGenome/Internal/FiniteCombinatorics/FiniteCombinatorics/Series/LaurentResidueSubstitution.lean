import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.LaurentResidueSubstitution
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.Substitution
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Laurent residue substitution

The Laurent series and derivative are Mathlib's integer Hahn series and Hasse
first derivative. Every construction is valid over a commutative ring; only the
monomial residue argument requires a ℚ-algebra. In particular neither a domain
nor a nontrivial coefficient ring is assumed.

For `g = X U`, `power U k` is `X^k U^k`. Its support starts at least at `k`.
Thus the summands `L[k] g^k` have a common lower bound and finite coefficient
support. The formal sum agrees with ordinary substitution on power series.
The change of variable theorem then follows from the integer power rule and
zero residue of a derivative, with the exponent -1 treated separately.

Source: paper.tex, p204:W18, the formal Laurent substitution paragraph.
-/

noncomputable section
universe u
namespace FiniteCombinatorics.Series.Laurent
open scoped BigOperators
namespace Expected
export Specs.FiniteCombinatorics.Series.LaurentResidueSubstitution
  (residueValue powerValue composeValue)
end Expected

/-- Coefficient of exponent -1, for Laurent series with finitely many negative terms. -/
def residue {R : Type u} [CommRing R] : LaurentSeries R → R := Expected.residueValue
/-- Integer powers of the admissible inner series `X U`. -/
def power {R : Type u} [CommRing R] : (PowerSeries R)ˣ → ℤ → LaurentSeries R :=
  Expected.powerValue
/-- Formal Laurent substitution; each coefficient is a finite sum. -/
def compose {R : Type u} [CommRing R] : LaurentSeries R → (PowerSeries R)ˣ → LaurentSeries R :=
  Expected.composeValue

variable {R : Type u} [CommRing R]

@[simp] theorem residue_derivative (L : LaurentSeries R) :
    residue (LaurentSeries.derivative R L) = 0 := by
  simp [residue, Expected.residueValue, LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff]

theorem unit_parameterization (U : PowerSeries R) :
    IsUnit (PowerSeries.constantCoeff U) ↔ ∃ v : (PowerSeries R)ˣ, (v : PowerSeries R) = U := by
  rw [← PowerSeries.isUnit_iff_constantCoeff]
  rfl

theorem coeff_power (U : (PowerSeries R)ˣ) (k n : ℤ) :
    (power U k).coeff n =
      if n-k < 0 then 0 else PowerSeries.coeff (n-k).natAbs (↑(U^k) : PowerSeries R) := by
  simp [power, Expected.powerValue, HahnSeries.coeff_single_mul, PowerSeries.coeff_coe]

theorem coeff_power_eq_zero (U : (PowerSeries R)ˣ) (k n : ℤ) (h : n < k) :
    (power U k).coeff n = 0 := by
  rw [coeff_power, ite_eq_left (by omega)]

@[simp] theorem power_zero (U : (PowerSeries R)ˣ) : power U 0 = 1 := by
  simp [power, Expected.powerValue, ← HahnSeries.C_apply]

theorem power_add (U : (PowerSeries R)ˣ) (k l : ℤ) :
    power U (k+l) = power U k * power U l := by
  simp only [power, Expected.powerValue, zpow_add, Units.val_mul, PowerSeries.coe_mul]
  rw [mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul]

theorem power_one (U : (PowerSeries R)ˣ) :
    power U 1 = ((PowerSeries.X * (U : PowerSeries R) : PowerSeries R) : LaurentSeries R) := by
  simp [power, Expected.powerValue, PowerSeries.coe_mul]

theorem coeff_compose (L : LaurentSeries R) (U : (PowerSeries R)ˣ) (n : ℤ) :
    (compose L U).coeff n =
      ∑ k ∈ Finset.Icc L.order n, L.coeff k * (power U k).coeff n := rfl

/-- A power series unit's logarithmic derivative, valid also for negative powers. -/
theorem derivative_unit_zpow_mul (U : (PowerSeries R)ˣ) (k : ℤ) :
    PowerSeries.derivative (↑(U^k) : PowerSeries R) * (U : PowerSeries R) =
      PowerSeries.C (k : R) * (↑(U^k) : PowerSeries R) * PowerSeries.derivative (U : PowerSeries R) := by
  let T : ℤ → Prop := fun k =>
    PowerSeries.derivative (↑(U^k) : PowerSeries R) * (U : PowerSeries R) =
      PowerSeries.C (k : R) * (↑(U^k) : PowerSeries R) * PowerSeries.derivative (U : PowerSeries R)
  have step (j : ℤ) : T (j+1) ↔ T j := by
    dsimp [T]
    have he : (↑(U^(j+1)) : PowerSeries R) = (↑(U^j) : PowerSeries R) * (U : PowerSeries R) := by
      simp [zpow_add]
    rw [he, PowerSeries.derivative.leibniz, smul_eq_mul, smul_eq_mul,
      Int.cast_add, Int.cast_one, map_add, map_one]
    constructor
    · intro h
      apply (Units.mul_left_inj U).mp
      linear_combination h
    · intro h
      linear_combination (U : PowerSeries R) * h
  change T k
  induction k using Int.induction_on with
  | zero => simp [T]
  | succ n ih => exact (step n).mpr ih
  | pred n ih =>
    have h := (step (-(n : ℤ)-1)).mp
    exact h (by simpa using ih)

/-- The integer power rule for the unit part in the ordinary power series ring. -/
theorem derivative_unit_zpow (U : (PowerSeries R)ˣ) (k : ℤ) :
    PowerSeries.derivative (↑(U^k) : PowerSeries R) =
      PowerSeries.C (k : R) * (↑(U^(k-1)) : PowerSeries R) *
        PowerSeries.derivative (U : PowerSeries R) := by
  apply (Units.mul_left_inj U).mp
  have he : (↑(U^(k-1)) : PowerSeries R) * (U : PowerSeries R) = (↑(U^k) : PowerSeries R) := by
    have h := congrArg (fun v : (PowerSeries R)ˣ => (v : PowerSeries R)) (zpow_add U (k-1) 1)
    simpa using h.symm
  rw [derivative_unit_zpow_mul]
  rw [show PowerSeries.C (k : R) * (↑(U^(k-1)) : PowerSeries R) *
      PowerSeries.derivative (U : PowerSeries R) * (U : PowerSeries R) =
      PowerSeries.C (k : R) * ((↑(U^(k-1)) : PowerSeries R) * (U : PowerSeries R)) *
      PowerSeries.derivative (U : PowerSeries R) by ring, he]

/-- Euler differentiation preserves the exponent, including degree zero. -/
theorem coeff_euler (A : PowerSeries R) (k m : ℤ) :
    (((PowerSeries.C (k : R) * A + PowerSeries.X * PowerSeries.derivative A : PowerSeries R) :
      LaurentSeries R)).coeff m = (k + m : ℤ) • (A : LaurentSeries R).coeff m := by
  cases m with
  | negSucc n =>
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    simp
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, LaurentSeries.coeff_coe_powerSeries]
    cases n with
    | zero => simp [
        PowerSeries.coeff_zero_eq_constantCoeff_apply, ← Int.cast_smul_eq_zsmul R,
        smul_eq_mul]
    | succ n =>
      simp only [map_add, PowerSeries.coeff_C_mul]
      have hx : PowerSeries.coeff (n+1) (PowerSeries.X * PowerSeries.derivative A) =
          PowerSeries.coeff (n+1) A * (n+1 : R) := by
        simpa only [pow_one, mul_comm] using
          (PowerSeries.coeff_mul_X_pow (PowerSeries.derivative A) 1 n).trans
            (PowerSeries.coeff_derivative A n)
      rw [hx, ← Int.cast_smul_eq_zsmul R, smul_eq_mul]
      push_cast
      ring

/-- Differentiation of a shifted ordinary power series, for every integer shift. -/
theorem derivative_shift (A : PowerSeries R) (k : ℤ) :
    LaurentSeries.derivative R (HahnSeries.single k 1 * (A : LaurentSeries R)) =
      HahnSeries.single (k-1) 1 *
        (((PowerSeries.C (k : R) * A + PowerSeries.X * PowerSeries.derivative A : PowerSeries R) :
          LaurentSeries R)) := by
  ext n
  simp only [LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff,
    Ring.choose_one_right, HahnSeries.coeff_single_mul, one_mul, coeff_euler]
  have h : n - (k-1) = n+1-k := by omega
  simp only [h]
  congr 1
  omega

/-- Formal differentiation obeys the power rule for every integer exponent. -/
theorem derivative_power (U : (PowerSeries R)ˣ) (k : ℤ) :
    LaurentSeries.derivative R (power U k) =
      k • (power U (k-1) *
        ((PowerSeries.derivative (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R)) := by
  unfold power Expected.powerValue
  rw [derivative_shift, mul_assoc, ← PowerSeries.coe_mul, ← mul_smul_comm,
    ← map_zsmul (HahnSeries.ofPowerSeries ℤ R)]
  rw [← Int.cast_smul_eq_zsmul R, PowerSeries.smul_eq_C_mul]
  congr 2
  have he : (↑(U^(k-1)) : PowerSeries R) * (U : PowerSeries R) = (↑(U^k) : PowerSeries R) := by
    have h := congrArg (fun v : (PowerSeries R)ˣ => (v : PowerSeries R)) (zpow_add U (k-1) 1)
    simpa using h.symm
  rw [derivative_unit_zpow, FiniteCombinatorics.Series.derivative_mul, PowerSeries.derivative_X,
    one_mul, ← he]
  ring

/-- The exceptional exponent has residue one, without any field hypothesis. -/
theorem residue_power_neg_one (U : (PowerSeries R)ˣ) :
    residue (power U (-1) *
      ((PowerSeries.derivative (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R)) = 1 := by
  unfold residue Expected.residueValue power Expected.powerValue
  rw [mul_assoc, ← PowerSeries.coe_mul, HahnSeries.coeff_single_mul]
  simp only [sub_self, one_mul]
  have hzero (A : PowerSeries R) : (A : LaurentSeries R).coeff 0 = PowerSeries.constantCoeff A := by
    simpa only [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) A 0)
  rw [hzero]
  rw [FiniteCombinatorics.Series.derivative_mul, PowerSeries.derivative_X, one_mul]
  simp only [map_mul, map_add, PowerSeries.constantCoeff_X, zero_mul, add_zero]
  rw [← map_mul]
  simp

/-- All nonexceptional integer monomials give zero residue. Division is only
by a nonzero rational integer, so the coefficient algebra may have zero divisors. -/
theorem residue_power_mul_derivative [Algebra ℚ R] (U : (PowerSeries R)ˣ) (k : ℤ) :
    residue (power U k *
      ((PowerSeries.derivative (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R)) =
      if k = -1 then 1 else 0 := by
  split_ifs with hk
  · subst k
    exact residue_power_neg_one U
  · have hd := residue_derivative (power U (k+1))
    rw [derivative_power, show k+1-1 = k by omega] at hd
    have hd' : (k+1) • residue (power U k *
        ((PowerSeries.derivative (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R)) = 0 :=
      by simpa only [residue, Expected.residueValue, HahnSeries.coeff_smul] using hd
    rw [← Int.cast_smul_eq_zsmul ℚ] at hd' 
    have hq : (k+1 : ℚ) ≠ 0 := by exact_mod_cast (show k+1 ≠ 0 by omega)
    exact (smul_eq_zero.mp hd').resolve_left (by simpa only [Int.cast_add, Int.cast_one] using hq)

/-- The monomial summands of Laurent substitution form a genuinely summable
family: their supports are uniformly bounded below and locally finite. -/
def substitutionFamily (L : LaurentSeries R) (U : (PowerSeries R)ˣ) :
    HahnSeries.SummableFamily ℤ R ℤ where
  toFun k := L.coeff k • power U k
  isPWO_iUnion_support' := by
    have hb : BddBelow (⋃ k : ℤ, (L.coeff k • power U k).support) := by
      refine ⟨L.order, ?_⟩
      intro n hn
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hn
      change (L.coeff k • power U k).coeff n ≠ 0 at hk
      simp only [HahnSeries.coeff_smul, smul_eq_mul] at hk
      have hL : L.coeff k ≠ 0 := left_ne_zero_of_mul hk
      have hkn : k ≤ n := by
        by_contra h
        exact hk (by rw [coeff_power_eq_zero U k n (by omega), mul_zero])
      exact (HahnSeries.order_le_of_coeff_ne_zero hL).trans hkn
    exact hb.isWF.isPWO
  finite_co_support' n := by
    apply (Finset.Icc L.order n).finite_toSet.subset
    intro k hk
    simp only [Set.mem_ofPred_eq, HahnSeries.coeff_smul, smul_eq_mul] at hk
    simp only [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨HahnSeries.order_le_of_coeff_ne_zero (left_ne_zero_of_mul hk), ?_⟩
    by_contra h
    exact hk (by rw [coeff_power_eq_zero U k n (by omega), mul_zero])

/-- The finite formula agrees with the formal sum of all integer monomials. -/
theorem compose_eq_hsum (L : LaurentSeries R) (U : (PowerSeries R)ˣ) :
    compose L U = (substitutionFamily L U).hsum := by
  ext n
  rw [coeff_compose]
  symm
  have hs : {k | ((substitutionFamily L U) k).coeff n ≠ 0} ⊆
      (Finset.Icc L.order n : Set ℤ) := by
    intro k hk
    change (L.coeff k • power U k).coeff n ≠ 0 at hk
    simp only [HahnSeries.coeff_smul, smul_eq_mul] at hk
    simp only [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨HahnSeries.order_le_of_coeff_ne_zero (left_ne_zero_of_mul hk), ?_⟩
    by_contra h
    exact hk (by rw [coeff_power_eq_zero U k n (by omega), mul_zero])
  rw [HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset hs]
  apply Finset.sum_congr rfl
  intro k hk
  exact HahnSeries.coeff_smul

theorem compose_monomial (U : (PowerSeries R)ˣ) (k : ℤ) (r : R) :
    compose (HahnSeries.single k r) U = r • power U k := by
  ext n
  rw [compose_eq_hsum, HahnSeries.SummableFamily.coeff_hsum]
  change (∑ᶠ j : ℤ, ((HahnSeries.single k r).coeff j • power U j).coeff n) = _
  rw [finsum_eq_single _ k (fun j hj => by simp [HahnSeries.coeff_single_of_ne hj])]
  simp

/-- Nonnegative powers agree with multiplication in the shared power series ring. -/
theorem power_nat (U : (PowerSeries R)ˣ) (n : ℕ) :
    power U (n : ℤ) =
      (((PowerSeries.X * (U : PowerSeries R)) ^ n : PowerSeries R) : LaurentSeries R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, power_add, ih, power_one, pow_succ]
    simp only [PowerSeries.coe_mul]

/-- Laurent substitution extends the accepted ordinary power series substitution. -/
theorem compose_powerSeries (A : PowerSeries R) (U : (PowerSeries R)ˣ) :
    compose (A : LaurentSeries R) U =
      ((FiniteCombinatorics.Series.compose A (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R) := by
  ext n
  rw [compose_eq_hsum, HahnSeries.SummableFamily.coeff_hsum]
  change (∑ᶠ j : ℤ, (A : LaurentSeries R).coeff j * (power U j).coeff n) = _
  cases n with
  | negSucc n =>
    rw [PowerSeries.coeff_coe, ite_eq_left (Int.negSucc_lt_zero n)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    by_cases hj : j < 0
    · rw [PowerSeries.coeff_coe, ite_eq_left hj, zero_mul]
    · rw [coeff_power_eq_zero U j (Int.negSucc n) (by omega), mul_zero]
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, LaurentSeries.coeff_coe_powerSeries]
    rw [FiniteCombinatorics.Series.coeff_compose A _ (by simp) n]
    rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (n+1)).map Nat.castEmbedding)]
    · rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Nat.castEmbedding_apply, LaurentSeries.coeff_coe_powerSeries, power_nat]
    · intro j hj
      change (A : LaurentSeries R).coeff j * (power U j).coeff (n : ℤ) ≠ 0 at hj
      have hj0 : 0 ≤ j := by
        by_contra h
        exact hj (by rw [PowerSeries.coeff_coe, ite_eq_left (by omega), zero_mul])
      have hjn : j ≤ n := by
        by_contra h
        exact hj (by rw [coeff_power_eq_zero U j n (by omega), mul_zero])
      simp only [Finset.mem_coe, Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply]
      exact ⟨j.toNat, by omega, by omega⟩

/-- Substitution of a shifted Laurent series, including a negative shift. -/
theorem compose_shift (L : LaurentSeries R) (U : (PowerSeries R)ˣ) (j : ℤ) :
    compose (HahnSeries.single j 1 * L) U = power U j * compose L U := by
  rw [compose_eq_hsum, compose_eq_hsum, ← HahnSeries.SummableFamily.hsum_smul]
  ext n
  simp only [HahnSeries.SummableFamily.coeff_hsum]
  rw [← finsum_comp_equiv (Equiv.addLeft j)]
  apply finsum_congr
  intro k
  change (((HahnSeries.single j 1 * L).coeff (j+k)) • power U (j+k)).coeff n =
    (power U j * (L.coeff k • power U k)).coeff n
  rw [HahnSeries.coeff_single_mul, one_mul, add_sub_cancel_left, power_add]
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul]
  congr 1
  ring

/-- Laurent substitution respects products. -/
theorem compose_mul (L M : LaurentSeries R) (U : (PowerSeries R)ˣ) :
    compose (L*M) U = compose L U * compose M U := by
  have hp (A B : PowerSeries R) (j k : ℤ) :
      compose ((HahnSeries.single j 1 * (A : LaurentSeries R)) *
        (HahnSeries.single k 1 * (B : LaurentSeries R))) U =
      compose (HahnSeries.single j 1 * (A : LaurentSeries R)) U *
        compose (HahnSeries.single k 1 * (B : LaurentSeries R)) U := by
    rw [mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul, ← PowerSeries.coe_mul,
      compose_shift, compose_powerSeries, FiniteCombinatorics.Series.compose_mul A B _ (by simp)]
    rw [compose_shift, compose_shift, compose_powerSeries, compose_powerSeries, power_add,
      PowerSeries.coe_mul]
    ring
  have h := hp L.powerSeriesPart M.powerSeriesPart L.order M.order
  simpa only [LaurentSeries.single_order_mul_powerSeriesPart] using h

/-- The formal Laurent change of variable formula of p204:W18. -/
theorem residue_substitution [Algebra ℚ R] (L : LaurentSeries R) (U : (PowerSeries R)ˣ) :
    residue (compose L U *
      ((PowerSeries.derivative (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R)) =
      residue L := by
  let dg : LaurentSeries R :=
    ((PowerSeries.derivative (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R)
  have hf : residue (compose L U * dg) =
      ∑ᶠ k : ℤ, L.coeff k * residue (power U k * dg) := by
    rw [compose_eq_hsum, mul_comm, ← HahnSeries.SummableFamily.hsum_smul]
    unfold residue Expected.residueValue
    rw [HahnSeries.SummableFamily.coeff_hsum]
    apply finsum_congr
    intro k
    change (dg * (L.coeff k • power U k)).coeff (-1) = _
    rw [← HahnSeries.C_mul_eq_smul, mul_left_comm dg, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul, mul_comm dg]
  change residue (compose L U * dg) = _
  rw [hf]
  have hm (k : ℤ) : residue (power U k * dg) = if k = -1 then 1 else 0 :=
    residue_power_mul_derivative U k
  simp_rw [hm]
  rw [finsum_eq_single _ (-1) (fun k hk => by simp [hk])]
  simp [residue, Expected.residueValue]

/-- Coefficient formula for the canonical Laurent derivative. -/
theorem derivative_coeff (L : LaurentSeries R) (n : ℤ) :
    (LaurentSeries.derivative R L).coeff n = (n+1) • L.coeff (n+1) := by
  simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff]

/-- The negative exponent denotes the two-sided inverse of the positive one. -/
theorem power_inverse (U : (PowerSeries R)ˣ) (k : ℤ) :
    power U k * power U (-k) = 1 ∧ power U (-k) * power U k = 1 := by
  constructor <;> simp [← power_add]

/-- Coefficients can be computed using any supplied lower support bound. -/
theorem coeff_compose_of_lower_bound (L : LaurentSeries R) (U : (PowerSeries R)ˣ)
    (b : ℤ) (hb : ∀ k : ℤ, k < b → L.coeff k = 0) (n : ℤ) :
    (compose L U).coeff n = ∑ k ∈ Finset.Icc b n, L.coeff k * (power U k).coeff n := by
  rw [compose_eq_hsum, HahnSeries.SummableFamily.coeff_hsum]
  change (∑ᶠ k : ℤ, L.coeff k * (power U k).coeff n) = _
  apply finsum_eq_sum_of_support_subset
  intro k hk
  change L.coeff k * (power U k).coeff n ≠ 0 at hk
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · by_contra h
    exact hk (by rw [hb k (by omega), zero_mul])
  · by_contra h
    exact hk (by rw [coeff_power_eq_zero U k n (by omega), mul_zero])

/-- Each coefficient depends only on a finite interval of outer coefficients. -/
theorem compose_finite_dependence (L M : LaurentSeries R) (U : (PowerSeries R)ˣ)
    (b n : ℤ) (hL : ∀ k : ℤ, k < b → L.coeff k = 0)
    (hM : ∀ k : ℤ, k < b → M.coeff k = 0)
    (he : ∀ k : ℤ, b ≤ k → k ≤ n → L.coeff k = M.coeff k) :
    (compose L U).coeff n = (compose M U).coeff n := by
  rw [coeff_compose_of_lower_bound L U b hL, coeff_compose_of_lower_bound M U b hM]
  apply Finset.sum_congr rfl
  intro k hk
  rw [he k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2]

/-- The change of variable theorem under the source's unit constant term
hypothesis, specialized from the unit parameterization. -/
theorem residue_substitution_of_unit_constant [Algebra ℚ R]
    (L : LaurentSeries R) (U : PowerSeries R) (hU : IsUnit (PowerSeries.constantCoeff U)) :
    residue (compose L (PowerSeries.isUnit_iff_constantCoeff.mpr hU).unit *
      ((PowerSeries.derivative (PowerSeries.X * U)) : LaurentSeries R)) = residue L := by
  have hv := (PowerSeries.isUnit_iff_constantCoeff.mpr hU).unit_spec
  simpa only [hv] using
    (residue_substitution L (PowerSeries.isUnit_iff_constantCoeff.mpr hU).unit)

end FiniteCombinatorics.Series.Laurent
