import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.FiniteGeometricMixing
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.EventualPositivity
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.TotalVariation
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.FinitePositiveRecurrence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StationaryReturnTimes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped ENNReal Classical
universe u
namespace P207.Markov
noncomputable section

variable {S : Type u} [Fintype S] [Nonempty S]

theorem finite_positive_power : FiniteGeometricMixingSpec.positive_power.{u} := by
  intro S _ _ P hI hA
  choose N hN using eventual_power_pos P hI hA
  let m := max 1 (Finset.univ.sup fun i => Finset.univ.sup (N i))
  refine ⟨m, le_max_left _ _, fun i j => hN i j m ?_⟩
  exact (Finset.le_sup (f := N i) (Finset.mem_univ j)).trans
    ((Finset.le_sup (f := fun i => Finset.univ.sup (N i)) (Finset.mem_univ i)).trans
      (le_max_right _ _))

lemma blockCommonMass_le (P : StochasticMatrix S) (m : ℕ) (i j : S) :
    blockCommonMass P m j ≤ realMatrix (power P m) i j :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma blockCommonMass_nonneg (P : StochasticMatrix S) (m : ℕ) (j : S) :
    0 ≤ blockCommonMass P m j := by
  apply Finset.le_inf'
  intro i _
  exact ENNReal.toReal_nonneg

lemma blockMinorization_nonneg (P : StochasticMatrix S) (m : ℕ) :
    0 ≤ blockMinorization P m := Finset.sum_nonneg fun j _ => blockCommonMass_nonneg P m j

lemma blockMinorization_le_one (P : StochasticMatrix S) (m : ℕ) :
    blockMinorization P m ≤ 1 := by
  let i : S := Classical.arbitrary S
  calc
    _ ≤ ∑ j, realMatrix (power P m) i j :=
      Finset.sum_le_sum fun j _ => blockCommonMass_le P m i j
    _ = 1 := realMatrix_finite_rowsum _ _

theorem finite_minorization_bounds : FiniteGeometricMixingSpec.minorization_bounds.{u} := by
  intro S _ _ P m hpos
  refine ⟨?_, blockMinorization_le_one P m⟩
  apply Finset.sum_pos
  · intro j _
    apply (Finset.lt_inf'_iff _).mpr
    intro i _
    exact (ENNReal.toReal_pos_iff).mpr ⟨hpos i j, lt_top_iff_ne_top.mpr ((power P m i).apply_ne_top j)⟩
  · exact Finset.univ_nonempty

omit [Nonempty S] in
lemma bind_toReal (μ : ProbabilityLaw S) (K : StochasticMatrix S) (j : S) :
    (μ.bind K j).toReal = ∑ i, (μ i).toReal * realMatrix K i j := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul, tsum_fintype, realMatrix]
  · intro i
    exact ENNReal.mul_ne_top (μ.apply_ne_top i) ((K i).apply_ne_top j)

omit [Nonempty S] in
lemma sum_mass (μ : ProbabilityLaw S) : ∑ i, (μ i).toReal = 1 := by
  simpa only [tsum_fintype] using tsum_mass μ

/-- Subtracting the common column masses removes a zero-sum term. The residual
matrix has nonnegative entries and every row sums to `1 - ε`. -/
lemma block_contraction (P : StochasticMatrix S) (m : ℕ) (μ ν : ProbabilityLaw S) :
    totalVariation (evolve μ P m) (evolve ν P m) ≤
      (1 - blockMinorization P m) * totalVariation μ ν := by
  let K := power P m
  let d : S → ℝ := fun i => (μ i).toReal - (ν i).toReal
  let R : S → S → ℝ := fun i j => realMatrix K i j - blockCommonMass P m j
  have hR (i j : S) : 0 ≤ R i j := sub_nonneg.mpr (blockCommonMass_le P m i j)
  have hd : ∑ i, d i = 0 := by simp [d, Finset.sum_sub_distrib, sum_mass]
  have hrow (i : S) : ∑ j, R i j = 1 - blockMinorization P m := by
    simp only [R, Finset.sum_sub_distrib, realMatrix_finite_rowsum, blockMinorization]
  have hdiff (j : S) :
      (evolve μ P m j).toReal - (evolve ν P m j).toReal = ∑ i, d i * R i j := by
    simp only [evolve, bind_toReal, R, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hd, zero_mul, sub_zero]
    simp only [d, sub_mul, Finset.sum_sub_distrib, K]
  rw [totalVariation_eq_half_tsum, totalVariation_eq_half_tsum, tsum_fintype, tsum_fintype]
  have hh : (∑ j, |(evolve μ P m j).toReal - (evolve ν P m j).toReal|) ≤
      (1 - blockMinorization P m) * ∑ i, |d i| := by
    calc
      _ = ∑ j, |∑ i, d i * R i j| := by simp_rw [hdiff]
      _ ≤ ∑ j, ∑ i, |d i| * R i j := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [abs_mul, abs_of_nonneg (hR _ _)] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => d i * R i j))
      _ = ∑ i, ∑ j, |d i| * R i j := Finset.sum_comm
      _ = _ := by simp_rw [← Finset.mul_sum, hrow]; rw [← Finset.sum_mul, mul_comm]
  dsimp only [d] at hh
  nlinarith

/-- Iterate the block contraction and contract through the remaining steps. -/
theorem finite_geometric_bound : FiniteGeometricMixingSpec.geometric_bound.{u} := by
  intro S _ _ P m hm n μ ν
  have hq : 0 ≤ 1 - blockMinorization P m := sub_nonneg.mpr (blockMinorization_le_one P m)
  have hblocks (k : ℕ) :
      totalVariation (evolve μ P (k * m)) (evolve ν P (k * m)) ≤
        (1 - blockMinorization P m) ^ k * totalVariation μ ν := by
    induction k with
    | zero => simp only [Nat.zero_mul, evolve_zero, pow_zero, one_mul]; exact le_rfl
    | succ k ih =>
      rw [Nat.succ_mul, evolve_add, evolve_add]
      calc
        _ ≤ (1 - blockMinorization P m) *
            totalVariation (evolve μ P (k * m)) (evolve ν P (k * m)) :=
          block_contraction P m _ _
        _ ≤ (1 - blockMinorization P m) *
            ((1 - blockMinorization P m) ^ k * totalVariation μ ν) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = _ := by rw [pow_succ]; ring
  calc
    _ = totalVariation
        (evolve (evolve μ P ((n / m) * m)) P (n % m))
        (evolve (evolve ν P ((n / m) * m)) P (n % m)) := by
      rw [← evolve_add, ← evolve_add, Nat.div_add_mod']
    _ ≤ totalVariation (evolve μ P ((n / m) * m)) (evolve ν P ((n / m) * m)) :=
      totalVariation_bind_le _ _ (power P (n % m))
    _ ≤ _ := hblocks (n / m)

theorem finite_mass_one_rows : FiniteGeometricMixingSpec.mass_one_rows.{u} := by
  intro S _ _ P m he i j
  have hnonneg (k : S) : 0 ≤ realMatrix (power P m) i k - blockCommonMass P m k :=
    sub_nonneg.mpr (blockCommonMass_le P m i k)
  have hsum : (∑ k, (realMatrix (power P m) i k - blockCommonMass P m k)) = 0 := by
    rw [Finset.sum_sub_distrib, realMatrix_finite_rowsum]
    change 1 - blockMinorization P m = 0
    rw [he, sub_self]
  have hle := Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
  rw [hsum] at hle
  exact le_antisymm (by linarith) (blockCommonMass_le P m i j)

theorem finite_mass_one_stationarity : FiniteGeometricMixingSpec.mass_one_stationarity.{u} := by
  intro S _ _ P m he μ π hπ n hn
  have heq : evolve μ P m = evolve π P m := by
    apply PMF.ext
    intro j
    apply (ENNReal.toReal_eq_toReal_iff' ((evolve μ P m).apply_ne_top j)
      ((evolve π P m).apply_ne_top j)).mp
    simp only [evolve, bind_toReal, finite_mass_one_rows P m he,
      ← Finset.sum_mul, sum_mass, one_mul]
  have hn' : m + (n - m) = n := Nat.add_sub_of_le hn
  rw [← hn', evolve_add, heq, stationary_evolve P π hπ m,
    stationary_evolve P π hπ (n - m)]

omit [Nonempty S] in
lemma totalVariation_le_one_finite (μ ν : ProbabilityLaw S) : totalVariation μ ν ≤ 1 := by
  rw [totalVariation_eq_one_sub_overlap]
  exact sub_le_self _ (tsum_nonneg fun _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- The logarithmic certificate, valid at every time after the stated threshold. -/
theorem finite_mixing_time_bound : FiniteGeometricMixingSpec.mixing_time_bound.{u} := by
  intro S _ _ P m hm he0 he1 μ π hπ δ hδ hδ1 n hn
  let q := 1 - blockMinorization P m
  have hq : 0 < q := sub_pos.mpr he1
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  have hden : 0 < -Real.log q := neg_pos.mpr hlog
  have hk : ⌈Real.log (1 / δ) / (-Real.log q)⌉₊ ≤ n / m :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [Nat.mul_comm] using hn)
  have hratio : Real.log (1 / δ) / (-Real.log q) ≤ (n / m : ℕ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hk)
  have hprod := (div_le_iff₀ hden).mp hratio
  have hpow : q ^ (n / m) ≤ δ := by
    apply (Real.log_le_log_iff (pow_pos hq _) hδ).mp
    rw [Real.log_pow]
    rw [one_div, Real.log_inv] at hprod
    nlinarith
  calc
    totalVariation (evolve μ P n) π =
        totalVariation (evolve μ P n) (evolve π P n) := by rw [stationary_evolve P π hπ n]
    _ ≤ q ^ (n / m) * totalVariation μ π := finite_geometric_bound P m hm n μ π
    _ ≤ q ^ (n / m) * 1 :=
      mul_le_mul_of_nonneg_left (totalVariation_le_one_finite μ π) (pow_nonneg hq.le _)
    _ ≤ δ := by simpa only [mul_one] using hpow

/-- The stationary law invoked in the mixing certificate exists under the
original finite irreducibility assumptions. -/
theorem finite_mixing_stationary_exists : FiniteGeometricMixingSpec.stationary_exists.{u} := by
  intro S _ _ P hI
  let : MeasurableSpace S := ⊤
  let i : S := Classical.arbitrary S
  exact exists_stationary_of_positiveRecurrent P i (finite_irreducible_positiveRecurrent P hI i)

/-- The finite minorization bound and its mixing-time certificate, with the
positive power and the stationary law both constructed. -/
theorem finite_geometric_mixing : FiniteGeometricMixingSpec.finite_geometric_mixing.{u} := by
  intro S _ _ P hI hA
  obtain ⟨m, hm, hpos⟩ := finite_positive_power P hI hA
  obtain ⟨he0, he1⟩ := finite_minorization_bounds P m hpos
  obtain ⟨π, hπ⟩ := finite_mixing_stationary_exists P hI
  refine ⟨m, hm, hpos, he0, he1, finite_geometric_bound P m hm, π, hπ, ?_, ?_⟩
  · intro he
    exact ⟨finite_mass_one_rows P m he,
      fun μ n hn => finite_mass_one_stationarity P m he μ π hπ n hn⟩
  · intro he μ δ hδ hδ1 n hn
    exact finite_mixing_time_bound P m hm he0 he μ π hπ δ hδ hδ1 n hn

end
end P207.Markov
