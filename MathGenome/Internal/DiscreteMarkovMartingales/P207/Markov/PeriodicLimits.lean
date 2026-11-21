import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.PeriodicLimits
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.CyclicStructure
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.AperiodicMixing
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter
open scoped Topology ENNReal Classical
universe u
namespace P207.Markov
noncomputable section

namespace PeriodicLimits
abbrev cesaroLaw : PeriodicLimitsSpec.cesaroLawType.{u} := @P207.Markov.cesaroLaw
abbrev alternatingKernel : PeriodicLimitsSpec.alternatingKernelType := P207.Markov.alternatingKernel
abbrev alternatingLaw : PeriodicLimitsSpec.alternatingLawType := P207.Markov.alternatingLaw
end PeriodicLimits

lemma lawEvent_mass_le_one {S : Type u} (μ : ProbabilityLaw S) (A : Set S) :
    lawEvent μ A ≤ 1 := by
  calc
    lawEvent μ A ≤ ∑' i, μ i := ENNReal.tsum_le_tsum (fun i => by
      by_cases hi : i ∈ A <;> simp [hi])
    _ = 1 := μ.tsum_coe

/-- Evaluation at any event is bounded by the paper-normalized TV distance. -/
lemma event_abs_le_totalVariation {S : Type u} [Countable S]
    (μ ν : ProbabilityLaw S) (A : Set S) :
    |(lawEvent μ A).toReal - (lawEvent ν A).toReal| ≤ totalVariation μ ν := by
  have hb : BddAbove (Set.range (fun A : Set S =>
      |(lawEvent μ A).toReal - (lawEvent ν A).toReal|)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨B, rfl⟩
    have hm := ENNReal.toReal_mono ENNReal.one_ne_top (lawEvent_mass_le_one μ B)
    have hn := ENNReal.toReal_mono ENNReal.one_ne_top (lawEvent_mass_le_one ν B)
    simp only [ENNReal.toReal_one] at hm hn
    exact abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := lawEvent μ B)],
      by linarith [ENNReal.toReal_nonneg (a := lawEvent ν B)]⟩
  exact le_csSup hb (Set.mem_range_self A)

lemma totalVariation_nonneg {S : Type u} [Countable S] (μ ν : ProbabilityLaw S) :
    0 ≤ totalVariation μ ν :=
  (abs_nonneg _).trans (event_abs_le_totalVariation μ ν ∅)

lemma lawEvent_singleton {S : Type u} (μ : ProbabilityLaw S) (j : S) :
    lawEvent μ {j} = μ j := by
  simp [lawEvent, Set.indicator_singleton]

lemma tendsto_mass_of_totalVariation {S : Type u} [Countable S]
    (μ : ℕ → ProbabilityLaw S) (ν : ProbabilityLaw S)
    (h : Tendsto (fun n => totalVariation (μ n) ν) atTop (𝓝 0)) (j : S) :
    Tendsto (fun n => (μ n j).toReal) atTop (𝓝 (ν j).toReal) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ h
  intro n
  simpa only [Real.norm_eq_abs, lawEvent_singleton] using
    event_abs_le_totalVariation (μ n) ν {j}

namespace CyclicPartition
variable {S : Type u} {P : StochasticMatrix S} {d : ℕ}

/-- Residue reached from l after n steps. -/
def advance (c : CyclicPartition P d) (l : Fin d) (n : ℕ) : Fin d :=
  ⟨(l.val + n) % d, Nat.mod_lt _ c.period_pos⟩

lemma advance_injective (c : CyclicPartition P d) (n : ℕ) :
    Function.Injective (fun l => c.advance l n) := by
  intro l k h
  apply Fin.ext
  have hh : l.val + n ≡ k.val + n [MOD d] := congrArg Fin.val h
  have he := Nat.ModEq.add_right_cancel' n hh
  change l.val % d = k.val % d at he
  simpa only [Nat.mod_eq_of_lt l.isLt, Nat.mod_eq_of_lt k.isLt] using he

lemma classLaw_evolve_any (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) (n : ℕ) :
    evolve (c.classLaw π hπ l) P n = c.classLaw π hπ (c.advance l n) := by
  apply c.classLaw_bind π hπ (power P n) (stationary_evolve P π hπ n)
    (fun l => c.advance l n) (c.advance_injective n)
  intro i j h
  exact Fin.ext (c.power_label n h)

/-- P^(md) cannot leave the starting class. -/
lemma power_mul_zero (c : CyclicPartition P d) (i j : S) (m : ℕ)
    (hj : c.label j ≠ c.label i) : power P (m * d) i j = 0 := by
  apply le_antisymm (not_lt.mp ?_) bot_le
  intro hp
  apply hj
  apply Fin.ext
  simpa [Nat.add_mod, Nat.mod_eq_of_lt (c.label i).isLt] using c.power_label (m*d) hp

/-- Lift the skeleton mixing limit from its class subtype to the full space. -/
lemma tendsto_classLaw [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (c : CyclicPartition P d) (π : ProbabilityLaw S) (hP : Irreducible P)
    (hπ : IsStationary P π) (hd : ∀ i, period P i = d) (i : S) :
    Tendsto (fun m => totalVariation (power P (m * d) i)
      (c.classLaw π hπ (c.label i))) atTop (𝓝 0) := by
  have hmix := aperiodic_tendsto_totalVariation (c.skeleton (c.label i))
    (c.skeletonLaw π hπ (c.label i)) (c.skeleton_irreducible hP _)
    (c.skeleton_aperiodic hd _) (c.skeleton_stationary π hπ _) (⟨i, rfl⟩)
  apply tendsto_totalVariation_of_pointwise
  intro j
  by_cases hj : c.label j = c.label i
  · have ht := tendsto_mass_of_totalVariation _ _ hmix (⟨j, hj⟩)
    simpa only [skeleton_power, skeletonLaw_apply, classLaw_apply, ite_eq_left hj,
      Nat.mul_comm d] using ht
  · simpa only [c.power_mul_zero i j _ hj, classLaw_apply, ite_eq_right hj,
      ENNReal.toReal_zero] using (tendsto_const_nhds (x := (0 : ℝ)))

lemma tendsto_residue [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (c : CyclicPartition P d) (π : ProbabilityLaw S) (hP : Irreducible P)
    (hπ : IsStationary P π) (hd : ∀ i, period P i = d) (i : S) (r : ℕ) :
    Tendsto (fun m => totalVariation (power P (m * d + r) i)
      (c.classLaw π hπ (c.advance (c.label i) r))) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => totalVariation_nonneg _ _) _ (c.tendsto_classLaw π hP hπ hd i)
  intro m
  have h := totalVariation_bind_le (power P (m*d) i)
    (c.classLaw π hπ (c.label i)) (power P r)
  rw [show (power P (m*d) i).bind (power P r) = power P (m*d+r) i from
    congrFun (power_add P (m*d) r).symm i,
    ← evolve, c.classLaw_evolve_any] at h
  exact h

end CyclicPartition

theorem cyclic_residue_limit : PeriodicLimitsSpec.cyclic_residue_limit.{u} := by
  intro S _ _ _ P π d c hP hπ hd
  exact ⟨c.classLaw π hπ, (fun _ _ => rfl), fun i r => c.tendsto_residue π hP hπ hd i r.val⟩

theorem stationary_marginals : PeriodicLimitsSpec.stationary_marginals.{u} :=
  stationary_evolve

/-- The entire time-n row is carried by the prescribed cyclic class. -/
lemma CyclicPartition.power_class {S : Type u} {P : StochasticMatrix S} {d : ℕ}
    (c : CyclicPartition P d) (i : S) (n : ℕ) :
    lawEvent (power P n i) (c.classSet (c.advance (c.label i) n)) = 1 := by
  rw [lawEvent]
  calc
    (∑' j, (c.classSet (c.advance (c.label i) n)).indicator (power P n i) j) =
        ∑' j, power P n i j := by
      apply tsum_congr
      intro j
      by_cases hj : c.label j = c.advance (c.label i) n
      · simp [CyclicPartition.classSet, hj]
      · have hz : power P n i j = 0 := by
          apply le_antisymm (not_lt.mp ?_) bot_le
          intro hp
          exact hj (Fin.ext (c.power_label n hp))
        simp [CyclicPartition.classSet, hj, hz]
    _ = 1 := power_row_sum P n i

theorem periodic_obstruction : PeriodicLimitsSpec.periodic_obstruction.{u} := by
  intro S _ P π d c hπ _ i n
  have h := event_abs_le_totalVariation (power P n i) π
    (c.classSet (c.advance (c.label i) n))
  rw [c.power_class, c.class_mass π hπ, ENNReal.toReal_one,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] at h
  exact (le_abs_self _).trans h

theorem cesaroLaw_apply : PeriodicLimitsSpec.cesaroLaw_apply.{u} := by
  intro S ν P n j
  rw [cesaroLaw, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [PMF.ofFintype_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ← Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun k => (evolve ν P k j).toReal) (n + 1)
  · intro k _
    exact ENNReal.mul_ne_top (by simp) ((evolve ν P k.val).apply_ne_top j)

namespace PeriodicLimits

/-- Finitely many residue subsequences determine the limit of a sequence. -/
lemma tendsto_of_residues {E : Type*} [TopologicalSpace E] {f : ℕ → E} {a : E}
    {d : ℕ} (hd : 0 < d)
    (h : ∀ r : Fin d, Tendsto (fun m => f (m*d+r.val)) atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  apply tendsto_def.mpr
  intro U hU
  have hh : ∀ r : Fin d, ∃ N, ∀ m ≥ N, f (m*d+r.val) ∈ U := by
    intro r
    exact eventually_atTop.mp ((tendsto_def.mp (h r)) U hU)
  choose N hN using hh
  let M := Finset.univ.sup N
  apply eventually_atTop.mpr
  refine ⟨M*d, ?_⟩
  intro n hn
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hMN : N r ≤ M := Finset.le_sup (Finset.mem_univ r)
  have hMd : M ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr hn
  have he : n / d * d + r.val = n := by simpa [r, Nat.mul_comm] using Nat.div_add_mod n d
  simpa only [he] using hN r (n / d) (hMN.trans hMd)

/-- Decompose a sum over complete blocks, including the empty block. -/
lemma sum_blocks (a : ℕ → ℝ) (d m : ℕ) :
    ∑ k ∈ Finset.range (m*d), a k =
      ∑ k ∈ Finset.range m, ∑ r ∈ Finset.range d, a (k*d+r) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A bounded nonnegative sequence with residue limits has the expected
Cesàro limit. No assertion about its ordinary limit is used. -/
lemma cesaro_of_residue_limits (a : ℕ → ℝ) {d : ℕ} (hd : 0 < d)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1) (L : Fin d → ℝ)
    (h : ∀ r : Fin d, Tendsto (fun m => a (m*d+r.val)) atTop (𝓝 (L r))) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k)
      atTop (𝓝 ((d : ℝ)⁻¹ * ∑ r, L r)) := by
  let mean := fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k
  let b := fun m => ∑ r : Fin d, a (m*d+r.val)
  have hb : Tendsto b atTop (𝓝 (∑ r, L r)) :=
    tendsto_finsetSum _ (fun r _ => h r)
  have hblock : Tendsto (fun m => mean (m*d)) atTop
      (𝓝 ((d : ℝ)⁻¹ * ∑ r, L r)) := by
    have ht := hb.cesaro.const_mul ((d : ℝ)⁻¹)
    convert ht using 1
    funext m
    simp only [mean, Nat.cast_mul, mul_inv_rev, mul_assoc]
    rw [sum_blocks]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    exact (Fin.sum_univ_eq_sum_range (fun r => a (k*d+r)) d).symm
  have hmul : Tendsto (fun m : ℕ => m*d) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    exact eventually_atTop.mpr ⟨B, fun m hm => hm.trans (Nat.le_mul_of_pos_right m hd)⟩
  apply tendsto_of_residues hd
  intro r
  have hratio := (tendsto_natCast_div_add_atTop (r.val : ℝ)).comp hmul
  have hlow : Tendsto (fun m => ((m*d+r.val : ℕ) : ℝ)⁻¹ *
      ∑ k ∈ Finset.range (m*d), a k) atTop
      (𝓝 ((d : ℝ)⁻¹ * ∑ r, L r)) := by
    have ht := hratio.mul hblock
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : ((m*d : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp [mean]
    push_cast
    field_simp
  have htime : Tendsto (fun m : ℕ => m*d+r.val) atTop atTop := by
    exact tendsto_atTop_mono (fun m => Nat.le_add_right (m*d) r.val) hmul
  have htail := (tendsto_const_div_atTop_nhds_zero_nat (r.val : ℝ)).comp htime
  have hupp := hlow.add htail
  simp only [add_zero] at hupp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro m
    have htail0 : 0 ≤ ∑ k ∈ Finset.range r.val, a (m*d+k) :=
      Finset.sum_nonneg (fun k _ => (ha _).1)
    dsimp [mean]
    rw [Finset.sum_range_add]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right htail0) (inv_nonneg.mpr (by positivity))
  · intro m
    have htail1 : (∑ k ∈ Finset.range r.val, a (m*d+k)) ≤ r.val := by
      calc
        _ ≤ ∑ _k ∈ Finset.range r.val, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => (ha _).2)
        _ = r.val := by simp
    dsimp [mean]
    rw [Finset.sum_range_add, mul_add, div_eq_mul_inv, mul_comm (r.val : ℝ)]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left htail1
      (inv_nonneg.mpr (Nat.cast_nonneg (m*d+r.val))))

end PeriodicLimits

namespace CyclicPartition
variable {S : Type u} {P : StochasticMatrix S} {d : ℕ}

/-- Adding a fixed class label permutes all residue labels. -/
def residueEquiv (c : CyclicPartition P d) (l : Fin d) : Fin d ≃ Fin d :=
  Equiv.ofBijective (fun r => c.advance l r.val) (by
    have hinj : Function.Injective (fun r : Fin d => c.advance l r.val) := by
      intro r s h
      apply Fin.ext
      have hh : l.val + r.val ≡ l.val + s.val [MOD d] := congrArg Fin.val h
      have he := Nat.ModEq.add_left_cancel' l.val hh
      change r.val % d = s.val % d at he
      simpa only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt s.isLt] using he
    exact ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩)

lemma mean_classLaw (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) (j : S) :
    (d : ℝ)⁻¹ * ∑ r : Fin d, (c.classLaw π hπ (c.advance l r.val) j).toReal =
      (π j).toReal := by
  rw [show (∑ r : Fin d, (c.classLaw π hπ (c.advance l r.val) j).toReal) =
      ∑ k : Fin d, (c.classLaw π hπ k j).toReal from
    (c.residueEquiv l).sum_comp (fun k => (c.classLaw π hπ k j).toReal)]
  have he : (∑ k : Fin d, (c.classLaw π hπ k j).toReal) =
      (d : ℝ) * (π j).toReal := by
    rw [Finset.sum_eq_single (c.label j)]
    · simp [classLaw_apply, ENNReal.toReal_mul]
    · intro k _ hk
      simp [classLaw_apply, Ne.symm hk]
    · simp
  rw [he, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast c.period_pos.ne'), one_mul]

/-- Coordinatewise convergence of the Cesàro laws, first for point starts. -/
lemma tendsto_cesaro_pure_mass [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (c : CyclicPartition P d) (π : ProbabilityLaw S) (hP : Irreducible P)
    (hπ : IsStationary P π) (hd : ∀ i, period P i = d) (i j : S) :
    Tendsto (fun n => (cesaroLaw (PMF.pure i) P n j).toReal) atTop (𝓝 (π j).toReal) := by
  have ht := PeriodicLimits.cesaro_of_residue_limits
    (fun n => (power P n i j).toReal) c.period_pos
    (fun n => ⟨ENNReal.toReal_nonneg,
      by simpa using ENNReal.toReal_mono ENNReal.one_ne_top ((power P n i).coe_le_one j)⟩)
    (fun r => (c.classLaw π hπ (c.advance (c.label i) r.val) j).toReal)
    (fun r => tendsto_mass_of_totalVariation _ _ (c.tendsto_residue π hP hπ hd i r.val) j)
  rw [c.mean_classLaw π hπ] at ht
  have ht' := ht.comp (tendsto_add_atTop_nat 1)
  apply ht'.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only [Function.comp_def]
    rw [cesaroLaw_apply]
    simp only [evolve, PMF.pure_bind])

end CyclicPartition

/-- Initial mixing commutes with the finite time average. -/
lemma cesaroLaw_bind {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) (n : ℕ) :
    cesaroLaw ν P n = ν.bind (fun i => cesaroLaw (PMF.pure i) P n) := by
  unfold cesaroLaw evolve
  simp only [PMF.pure_bind]
  exact PMF.bind_comm _ _ _

lemma bind_real {S T : Type u} (ν : ProbabilityLaw S) (Q : S → ProbabilityLaw T) (j : T) :
    (ν.bind Q j).toReal = ∑' i, (ν i).toReal * (Q i j).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul]
  · intro i
    exact ENNReal.mul_ne_top (ν.apply_ne_top i) ((Q i).apply_ne_top j)

theorem cesaro_tendsto : PeriodicLimitsSpec.cesaro_tendsto.{u} := by
  intro S _ _ _ P π hP hπ ν
  obtain ⟨a, _⟩ := π.support_nonempty
  obtain ⟨c⟩ := exists_cyclicPartition P a hP
  have hd (i : S) : period P i = period P a := period_eq_of_communicate P (hP i a)
  apply tendsto_totalVariation_of_pointwise
  intro j
  have ht : Tendsto (fun n => ∑' i, (ν i).toReal *
      (cesaroLaw (PMF.pure i) P n j).toReal) atTop
      (𝓝 (∑' i, (ν i).toReal * (π j).toReal)) := by
    apply tendsto_tsum_of_dominated_convergence (summable_mass ν)
    · intro i
      exact tendsto_const_nhds.mul (c.tendsto_cesaro_pure_mass π hP hπ hd i j)
    · apply Eventually.of_forall
      intro n i
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
      have hb : (cesaroLaw (PMF.pure i) P n j).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top
          ((cesaroLaw (PMF.pure i) P n).coe_le_one j)
      exact (mul_le_mul_of_nonneg_left hb ENNReal.toReal_nonneg).trans_eq (mul_one _)
  simpa only [cesaroLaw_bind ν P, bind_real, tsum_mul_right, tsum_mass, one_mul] using ht

theorem periodic_limits : PeriodicLimitsSpec.periodic_limits.{u} := by
  intro S _ _ _ P d hP hpr hd
  obtain ⟨π, hπ, c, hc⟩ := cyclic_structure P d hP hpr hd
  obtain ⟨μ, hμ, ht⟩ := cyclic_residue_limit P π d c hP hπ hd
  exact ⟨π, hπ, c, μ, hc, hμ, ht, cesaro_tendsto P π hP hπ,
    periodic_obstruction P π d c hπ, stationary_evolve P π hπ⟩

/-- The uniform law is invariant under swapping the two states. -/
lemma alternating_stationary : IsStationary alternatingKernel alternatingLaw := by
  apply (stationary_iff_masses _ _).mpr
  intro j
  cases j <;> simp [alternatingKernel, alternatingLaw, tsum_fintype, PMF.pure_apply]

lemma alternating_irreducible : Irreducible alternatingKernel := by
  have hacc (i j : Bool) : Accessible alternatingKernel i j := by
    by_cases hij : i = j
    · subst j
      exact ⟨0, by simp [power_zero, identity_apply]⟩
    · refine ⟨1, ?_⟩
      cases i <;> cases j <;>
        simp_all [power_one, alternatingKernel, PMF.pure_apply]
  exact fun i j => ⟨hacc i j, hacc j i⟩

lemma alternating_power_two : power alternatingKernel 2 = identity := by
  funext i
  simp [power_succ, power_zero, comp, identity, alternatingKernel]

/-- Exact even/odd laws establish the corresponding cyclic subsequence limits. -/
lemma alternating_powers (i : Bool) (m : ℕ) :
    power alternatingKernel (m*2) i = PMF.pure i ∧
      power alternatingKernel (m*2+1) i = PMF.pure (!i) := by
  have he (m : ℕ) : power alternatingKernel (m*2) = identity := by
    induction m with
    | zero => exact power_zero _
    | succ m ih =>
      rw [Nat.succ_mul, power_add, ih, alternating_power_two, comp_identity]
  constructor
  · exact congrFun (he m) i
  · rw [power_add, he m, power_one, identity_comp]
    rfl

lemma totalVariation_pure_alternating (i : Bool) :
    totalVariation (PMF.pure i) alternatingLaw = (1/2 : ℝ) := by
  rw [totalVariation_eq_half_tsum, tsum_fintype]
  cases i <;> norm_num [Fintype.sum_bool, alternatingLaw, PMF.ofFintype_apply,
    PMF.pure_apply, ENNReal.toReal_inv]

lemma alternating_distance (i : Bool) (n : ℕ) :
    totalVariation (power alternatingKernel n i) alternatingLaw = (1/2 : ℝ) := by
  have he : n = n/2*2+n%2 := by omega
  have hr : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hr with hr | hr
  · rw [he, hr, add_zero, (alternating_powers i (n/2)).1]
    exact totalVariation_pure_alternating i
  · rw [he, hr, (alternating_powers i (n/2)).2]
    exact totalVariation_pure_alternating (!i)

theorem alternating_example : PeriodicLimitsSpec.alternating_example := by
  refine ⟨by simp [alternatingKernel], by simp [alternatingKernel],
    fun _ => rfl, alternating_stationary, alternating_distance, alternating_powers,
    ?_, stationary_evolve _ _ alternating_stationary⟩
  exact cesaro_tendsto _ _ alternating_irreducible alternating_stationary

theorem alternating_cyclic_limits : PeriodicLimitsSpec.alternating_cyclic_limits := by
  intro i
  have hzero (j : Bool) : totalVariation (PMF.pure j) (PMF.pure j) = 0 := by
    simp [totalVariation_eq_half_tsum]
  constructor
  · simpa only [(alternating_powers i _).1, hzero] using
      (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop (α := ℕ)))
  · simpa only [(alternating_powers i _).2, hzero] using
      (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop (α := ℕ)))

end
end P207.Markov
