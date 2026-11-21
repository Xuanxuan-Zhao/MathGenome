import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ReturnGeneratingFunctions
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.RecurrenceInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StrongMarkov
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.DeterministicTransitions

open MeasureTheory Filter
open scoped ENNReal Topology
universe u
namespace P207.Markov.ReturnGeneratingFunctions
noncomputable section

namespace Objects
abbrev diagonalMass : ReturnGeneratingFunctionsSpec.diagonalMassType := @P207.Markov.ReturnGeneratingFunctions.diagonalMass
abbrev firstReturnMass : ReturnGeneratingFunctionsSpec.firstReturnMassType := @P207.Markov.ReturnGeneratingFunctions.firstReturnMass
abbrev greenFunction : ReturnGeneratingFunctionsSpec.greenFunctionType := @P207.Markov.ReturnGeneratingFunctions.greenFunction
abbrev firstReturnFunction : ReturnGeneratingFunctionsSpec.generatingFunctionType := @P207.Markov.ReturnGeneratingFunctions.firstReturnFunction
end Objects

variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

local instance stateLaw_probability (P : StochasticMatrix S) (i : S) :
    IsProbabilityMeasure (statePathLaw P i) := by
  unfold statePathLaw
  infer_instance

theorem diagonal_zero (P : StochasticMatrix S) (i : S) : diagonalMass P i 0 = 1 := by
  classical
  simp [diagonalMass, power_zero, identity_apply]

theorem firstReturn_zero (P : StochasticMatrix S) (i : S) : firstReturnMass P i 0 = 0 := by
  have he : {ω : ℕ → S | returnTime i ω = (0 : WithTop ℕ)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω h
    obtain ⟨k, hk, hk0, _⟩ := (positiveReturnTime_le_iff coordinate i ω 0).mp
      (le_of_eq h)
    omega
  simp [firstReturnMass, he]

theorem measurableSet_return_layer (i : S) (n : ℕ) :
    MeasurableSet {ω : ℕ → S | returnTime i ω = n} :=
  (measurable_returnTime i) (measurableSet_singleton _)

theorem firstReturn_total (P : StochasticMatrix S) (i : S) :
    (∑' n : ℕ, firstReturnMass P i (n + 1)) = returnProbability P i := by
  have hu : {ω : ℕ → S | returnTime i ω < ⊤} =
      ⋃ n : ℕ, {ω | returnTime i ω = (n + 1 : ℕ)} := by
    ext ω
    constructor
    · intro hω
      change returnTime i ω < ⊤ at hω
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hω)
      have hle := (positiveReturnTime_le_iff coordinate i ω k).mp (le_of_eq hk.symm)
      have hkpos : 0 < k := by obtain ⟨j, hj, hjk, _⟩ := hle; omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
      exact Set.mem_iUnion.mpr ⟨n, hk.symm⟩
    · intro hω
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
      simp only [Set.mem_ofPred_eq] at hn
      change returnTime i ω < ⊤
      rw [hn]
      exact WithTop.coe_lt_top _
  have hd : Pairwise (fun n k : ℕ => Disjoint
      {ω : ℕ → S | returnTime i ω = (n + 1 : ℕ)}
      {ω : ℕ → S | returnTime i ω = (k + 1 : ℕ)}) := by
    intro n k hnk
    apply Set.disjoint_left.mpr
    intro ω hn hk
    exact hnk (by exact Nat.add_right_cancel (WithTop.coe_injective (hn.symm.trans hk)))
  unfold firstReturnMass returnProbability
  rw [hu, measure_iUnion hd (fun n => measurableSet_return_layer i (n + 1))]

theorem diagonal_le_one (P : StochasticMatrix S) (i : S) (n : ℕ) :
    diagonalMass P i n ≤ 1 := (power P n i).coe_le_one i

theorem firstReturn_le_one (P : StochasticMatrix S) (i : S) (n : ℕ) :
    firstReturnMass P i n ≤ 1 := prob_le_one

theorem summable_green (P : StochasticMatrix S) (i : S) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun n : ℕ => (diagonalMass P i n).toReal * z ^ n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz n))
    (fun n => ?_) (summable_geometric_of_lt_one hz hz1)
  exact mul_le_of_le_one_left (pow_nonneg hz n)
    (by simpa using ENNReal.toReal_mono (by simp) (diagonal_le_one P i n))

theorem summable_firstReturn (P : StochasticMatrix S) (i : S) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun n : ℕ => (firstReturnMass P i (n + 1)).toReal * z ^ (n + 1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz (n + 1)))
    (fun n => ?_) ((summable_geometric_of_lt_one hz hz1).comp_injective Nat.succ_injective)
  exact mul_le_of_le_one_left (pow_nonneg hz (n + 1))
    (by simpa using ENNReal.toReal_mono (by simp) (firstReturn_le_one P i (n + 1)))

theorem green_le (P : StochasticMatrix S) (i : S) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z < 1) : greenFunction P i z ≤ 1 / (1 - z) := by
  unfold greenFunction
  rw [one_div, ← tsum_geometric_of_lt_one hz hz1]
  apply (summable_green P i z hz hz1).tsum_le_tsum _ (summable_geometric_of_lt_one hz hz1)
  intro n
  exact mul_le_of_le_one_left (pow_nonneg hz n)
    (by simpa using ENNReal.toReal_mono (by simp) (diagonal_le_one P i n))

theorem firstReturn_le (P : StochasticMatrix S) (i : S) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z < 1) : firstReturnFunction P i z ≤ z := by
  have hfin : (∑' n : ℕ, firstReturnMass P i (n + 1)) ≠ ⊤ := by
    rw [firstReturn_total]
    exact ne_top_of_le_ne_top (by simp) (returnProbability_le_one P i)
  have hs := ENNReal.summable_toReal hfin
  have hsum : (∑' n : ℕ, (firstReturnMass P i (n + 1)).toReal) =
      (returnProbability P i).toReal := by
    rw [← ENNReal.tsum_toReal_eq (fun n => ne_top_of_le_ne_top ENNReal.one_ne_top (firstReturn_le_one P i (n + 1))), firstReturn_total]
  calc
    firstReturnFunction P i z ≤ ∑' n : ℕ, (firstReturnMass P i (n + 1)).toReal * z := by
      apply (summable_firstReturn P i z hz hz1).tsum_le_tsum _ (hs.mul_right z)
      intro n
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      rw [pow_succ]
      exact mul_le_of_le_one_left hz (pow_le_one₀ hz hz1.le)
    _ = (returnProbability P i).toReal * z := by rw [tsum_mul_right, hsum]
    _ ≤ z := mul_le_of_le_one_left hz (by
      simpa using ENNReal.toReal_mono (by simp) (returnProbability_le_one P i))

theorem firstReturn_lt_one (P : StochasticMatrix S) (i : S) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z < 1) : firstReturnFunction P i z < 1 :=
  (firstReturn_le P i z hz hz1).trans_lt hz1

/-- The mass of a coordinate under the canonical point-started law. -/
theorem diagonalMass_eq_measure (P : StochasticMatrix S) (i : S) (n : ℕ) :
    diagonalMass P i n = statePathLaw P i {ω | ω n = i} := by
  let : Nonempty S := ⟨i⟩
  have h := DeterministicTransitions.marginal_mass
    (coordinate_isMarkovChain P (PMF.pure i)) n i
  simpa [coordinate, statePathLaw, evolve, diagonalMass] using h.symm

theorem return_layer_state (i : S) (k : ℕ) (ω : ℕ → S)
    (hk : returnTime i ω = k) : ω k = i := by
  have hne : hittingAfter coordinate {i} 1 ω ≠ ⊤ := by
    change returnTime i ω ≠ ⊤
    rw [hk]
    simp
  have hm := hittingAfter_mem_set_of_ne_top hne
  change coordinate (returnTime i ω).untopA ω ∈ ({i} : Set S) at hm
  rw [hk] at hm
  exact hm

/-- On each finite first-return layer, the fixed-time future law restarts at i. -/
theorem return_layer_factor (P : StochasticMatrix S) (i : S) (k m : ℕ) :
    statePathLaw P i ({ω | returnTime i ω = k} ∩ {ω | ω (k + m) = i}) =
      firstReturnMass P i k * diagonalMass P i m := by
  classical
  let : Nonempty S := ⟨i⟩
  let B : Set (ℕ → S) := {p | p m = i}
  have hB : MeasurableSet B := by
    exact measurableSet_eq_fun (measurable_pi_apply m) measurable_const
  have hA := MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable
    (returnTime_isStoppingTime i) k
  have he := StrongMarkov.fixed_future_lintegral
    (coordinate_isMarkovChain P (PMF.pure i))
    (B.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hB) k
    {ω | returnTime i ω = k} hA
  have hleft : (fun ω : ℕ → S => B.indicator (fun _ => (1 : ℝ≥0∞))
      (fun j => coordinate (k + j) ω)) =
      {ω : ℕ → S | ω (k + m) = i}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    simp only [B, coordinate, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hleft, lintegral_indicator
    (measurableSet_eq_fun (measurable_pi_apply (k + m)) measurable_const), setLIntegral_const,
    one_mul, Measure.restrict_apply
      (measurableSet_eq_fun (measurable_pi_apply (k + m)) measurable_const), Set.inter_comm] at he
  change pathLaw P (PMF.pure i) _ = _
  rw [he]
  calc
    _ = ∫⁻ _ in {ω : ℕ → S | returnTime i ω = k},
        statePathLaw P i B ∂statePathLaw P i := by
      apply setLIntegral_congr_fun (measurableSet_return_layer i k)
      intro ω hω
      dsimp only
      rw [lintegral_indicator hB, setLIntegral_const, one_mul]
      rw [show coordinate k ω = i from return_layer_state i k ω hω]
    _ = firstReturnMass P i k * diagonalMass P i m := by
      rw [setLIntegral_const, ← diagonalMass_eq_measure P i m, mul_comm]
      rfl

theorem convolution (P : StochasticMatrix S) (i : S) (n : ℕ) (hn : 1 ≤ n) :
    diagonalMass P i n = ∑ k ∈ Finset.Icc 1 n,
      firstReturnMass P i k * diagonalMass P i (n - k) := by
  classical
  let A := fun k : ℕ => {ω : ℕ → S | returnTime i ω = k} ∩ {ω | ω n = i}
  have hm (k : ℕ) : MeasurableSet (A k) :=
    (measurableSet_return_layer i k).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)
  have hd : Set.PairwiseDisjoint (↑(Finset.Icc 1 n) : Set ℕ) A := by
    intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro ω hωk hωl
    exact hkl (WithTop.coe_injective (hωk.1.symm.trans hωl.1))
  have hu : {ω : ℕ → S | ω n = i} = ⋃ k ∈ Finset.Icc 1 n, A k := by
    ext ω
    constructor
    · intro hω
      have hle : returnTime i ω ≤ n := by
        apply (positiveReturnTime_le_iff coordinate i ω n).mpr
        exact ⟨n, hn, le_rfl, hω⟩
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hle)
      have hkn : k ≤ n := WithTop.coe_le_coe.mp (hk.symm ▸ hle)
      have hk1 : 1 ≤ k := by
        have hp := (positiveReturnTime_le_iff coordinate i ω k).mp (le_of_eq hk.symm)
        obtain ⟨j, hj, hjk, _⟩ := hp
        omega
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
        ⟨Finset.mem_Icc.mpr ⟨hk1, hkn⟩, hk.symm, hω⟩⟩
    · intro hω
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hω
      obtain ⟨_, hk⟩ := Set.mem_iUnion.mp hk
      exact hk.2
  rw [diagonalMass_eq_measure, hu, measure_biUnion_finset hd (fun k _ => hm k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := (Finset.mem_Icc.mp hk).2
  simpa only [Nat.add_sub_of_le hkn] using return_layer_factor P i k (n - k)


/-- Solve the renewal identity using the absolutely convergent Cauchy product. -/
theorem reciprocal (P : StochasticMatrix S) (i : S) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z < 1) :
    greenFunction P i z = 1 / (1 - firstReturnFunction P i z) := by
  let f : ℕ → ℝ := fun n => (firstReturnMass P i n).toReal * z ^ n
  let g : ℕ → ℝ := fun n => (diagonalMass P i n).toReal * z ^ n
  have hf : Summable f :=
    (summable_nat_add_iff (f := f) 1).mp (summable_firstReturn P i z hz hz1)
  have hg : Summable g := summable_green P i z hz hz1
  have hf0 : f 0 = 0 := by simp [f, firstReturn_zero]
  have hg0 : g 0 = 1 := by simp [g, diagonal_zero]
  have hfval : (∑' n, f n) = firstReturnFunction P i z := by
    calc
      _ = f 0 + ∑' n, f (n + 1) := hf.tsum_eq_zero_add
      _ = _ := by rw [hf0, zero_add]; rfl
  have hfg := hf.tsum_mul_tsum_eq_tsum_sum_range hg (Summable.mul_of_nonneg hf hg
    (fun n => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz n))
    (fun n => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz n)))
  have hterm (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1), f k * g (n - k)) = if n = 0 then 0 else g n := by
    by_cases hn : n = 0
    · simp [hn, hf0]
    · rw [ite_eq_right hn]
      have hc := congrArg ENNReal.toReal (convolution P i n (by omega))
      rw [ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top
        (ne_top_of_le_ne_top ENNReal.one_ne_top (firstReturn_le_one P i k))
        (ne_top_of_le_ne_top ENNReal.one_ne_top (diagonal_le_one P i (n - k))))] at hc
      simp only [ENNReal.toReal_mul] at hc
      have hsubset : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
        intro k hk
        exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hk).2; omega)
      calc
        _ = ∑ k ∈ Finset.Icc 1 n, f k * g (n - k) := by
          symm
          apply Finset.sum_subset hsubset
          intro k hk hkn
          have hk0 : k = 0 := by
            have hkr := Finset.mem_range.mp hk
            have hkcc : ¬ (1 ≤ k ∧ k ≤ n) := by simpa only [Finset.mem_Icc] using hkn
            omega
          simp [hk0, hf0]
        _ = (∑ k ∈ Finset.Icc 1 n,
            (firstReturnMass P i k).toReal * (diagonalMass P i (n - k)).toReal) * z ^ n := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          have hp : z ^ k * z ^ (n - k) = z ^ n := by
            rw [← pow_add, Nat.add_sub_of_le (Finset.mem_Icc.mp hk).2]
          dsimp only [f, g]
          calc
            _ = ((firstReturnMass P i k).toReal * (diagonalMass P i (n - k)).toReal) *
                (z ^ k * z ^ (n - k)) := by ring
            _ = _ := by rw [hp]
        _ = g n := by rw [← hc]
  simp_rw [hterm] at hfg
  have htail : (∑' n : ℕ, if n = 0 then (0 : ℝ) else g n) = greenFunction P i z - 1 := by
    have hs : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else g n) := by
      apply (summable_nat_add_iff 1).mp
      simpa using (summable_nat_add_iff (f := g) 1).mpr hg
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_add]
    have hgval := hg.tsum_eq_zero_add
    change greenFunction P i z = _ at hgval
    rw [hg0] at hgval
    linarith
  rw [hfval, htail] at hfg
  change firstReturnFunction P i z * greenFunction P i z = greenFunction P i z - 1 at hfg
  apply (eq_div_iff (sub_ne_zero.mpr (ne_of_gt (firstReturn_lt_one P i z hz hz1)))).mpr
  nlinarith

omit [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Abel convergence for nonnegative series, including an infinite total.
Finite partial sums give every lower bound; the full mass is an upper bound. -/
theorem tendsto_ennreal_powerSeries (a : ℕ → ℝ≥0∞) (e : ℕ → ℕ)
    (ha : ∀ n, a n ≠ ⊤) :
    Tendsto (fun z : ℝ => ∑' n : ℕ, a n * ENNReal.ofReal z ^ e n)
      (𝓝[<] 1) (𝓝 (∑' n : ℕ, a n)) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    rw [ENNReal.tsum_eq_iSup_sum] at hc
    obtain ⟨s, hs⟩ := lt_iSup_iff.mp hc
    have ht : Tendsto (fun z : ℝ => ∑ n ∈ s, a n * ENNReal.ofReal z ^ e n)
        (𝓝[<] 1) (𝓝 (∑ n ∈ s, a n)) := by
      apply tendsto_finsetSum
      intro n _
      have hn : Continuous (fun z : ℝ => a n * ENNReal.ofReal z ^ e n) :=
        (ENNReal.continuous_const_mul (ha n)).comp ((ENNReal.continuous_pow (e n)).comp ENNReal.continuous_ofReal)
      simpa using hn.tendsto 1 |>.mono_left nhdsWithin_le_nhds
    filter_upwards [(tendsto_order.mp ht).1 c hs] with z hz
    exact hz.trans_le (ENNReal.sum_le_tsum s)
  · intro c hc
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with z hz
    apply lt_of_le_of_lt _ hc
    apply ENNReal.tsum_le_tsum
    intro n
    apply mul_le_of_le_one_right' _
    exact pow_le_one₀ (by positivity) (by simpa using ENNReal.ofReal_le_ofReal hz.2.le)

theorem limit_firstReturn (P : StochasticMatrix S) (i : S) :
    Tendsto (fun z : ℝ => ENNReal.ofReal (firstReturnFunction P i z))
      (𝓝[<] 1) (𝓝 (returnProbability P i)) := by
  have ht := tendsto_ennreal_powerSeries (fun n => firstReturnMass P i (n + 1))
    (fun n => n + 1) (fun n => ne_top_of_le_ne_top ENNReal.one_ne_top
      (firstReturn_le_one P i (n + 1)))
  rw [firstReturn_total] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with z hz
  unfold firstReturnFunction
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz.1.le _))
    (summable_firstReturn P i z hz.1.le hz.2)]
  apply tsum_congr
  intro n
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (firstReturn_le_one P i (n + 1))),
    ENNReal.ofReal_pow hz.1.le]

theorem limit_green (P : StochasticMatrix S) (i : S) :
    Tendsto (fun z : ℝ => ENNReal.ofReal (greenFunction P i z))
      (𝓝[<] 1) (𝓝 (∑' n : ℕ, diagonalMass P i n)) := by
  have ht := tendsto_ennreal_powerSeries (diagonalMass P i) (fun n => n)
    (fun n => ne_top_of_le_ne_top ENNReal.one_ne_top (diagonal_le_one P i n))
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with z hz
  unfold greenFunction
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz.1.le _))
    (summable_green P i z hz.1.le hz.2)]
  apply tsum_congr
  intro n
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (diagonal_le_one P i n)),
    ENNReal.ofReal_pow hz.1.le]

end
end P207.Markov.ReturnGeneratingFunctions
