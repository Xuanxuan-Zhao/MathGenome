import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.GraphPeriodMixing
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.GraphStationarity
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.AperiodicMixing
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.PeriodicLimits

open Filter
open scoped ENNReal Topology Classical
universe u
namespace P207.Walk.GraphPeriodMixing
open P207.Markov
noncomputable section

abbrev lazyKernel : GraphPeriodMixingSpec.lazyKernelType.{u} := @P207.Walk.lazyKernel

theorem lazyKernel_apply : GraphPeriodMixingSpec.lazyKernel_apply.{u} := by
  intro S P α h₀ h₁ i j
  simp only [P207.Walk.lazyKernel, PMF.pure_apply]
  rfl

section Graph
variable {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)

/-- Traversing an edge and its reverse gives a two-step return. -/
theorem two_step_return (v : V) : 0 < power (neighborKernel G hG) 2 v v := by
  obtain ⟨w, hw⟩ := hG.preconnected.exists_adj_of_nontrivial v
  exact power_pos_add (neighborKernel G hG) (m := 1) (n := 1)
    (by simpa only [power_one] using (GraphStationarity.neighborKernel_pos_iff G hG v w).mpr hw)
    (by simpa only [power_one] using (GraphStationarity.neighborKernel_pos_iff G hG w v).mpr hw.symm)

theorem period_dvd_two (v : V) : period (neighborKernel G hG) v ∣ 2 :=
  period_dvd_returnLength _ _ 2 ⟨by decide, two_step_return G hG v⟩

/-- The graph's given bipartition is a cyclic partition of its actual kernel. -/
def colorPartition (c : G.Coloring (Fin 2)) : CyclicPartition (neighborKernel G hG) 2 where
  period_pos := by decide
  label := c
  onto := by
    intro l
    let v : V := Classical.arbitrary V
    obtain ⟨w, hw⟩ := hG.preconnected.exists_adj_of_nontrivial v
    by_cases hv : c v = l
    · exact ⟨v, hv⟩
    · refine ⟨w, Fin.ext ?_⟩
      have hne : (c v).val ≠ (c w).val := fun h => c.valid hw (Fin.ext h)
      have hnl : (c v).val ≠ l.val := fun h => hv (Fin.ext h)
      have := (c v).isLt
      have := (c w).isLt
      have := l.isLt
      omega
  step := by
    intro i j hij
    have hne : (c i).val ≠ (c j).val := fun h =>
      c.valid ((GraphStationarity.neighborKernel_pos_iff G hG i j).mp hij) (Fin.ext h)
    have := (c i).isLt
    have := (c j).isLt
    omega

end Graph

theorem period_two_iff_bipartite : GraphPeriodMixingSpec.period_two_iff_bipartite.{u} := by
  intro V _ _ G _ hG v
  constructor
  · intro hv
    obtain ⟨c⟩ := exists_cyclicPartition (neighborKernel G hG) v
      (GraphStationarity.neighborKernel_irreducible G hG)
    rw [hv] at c
    refine ⟨SimpleGraph.Coloring.mk c.label ?_⟩
    intro i j hij heq
    have hs := c.step i j ((GraphStationarity.neighborKernel_pos_iff G hG i j).mpr hij)
    have hv := congrArg Fin.val heq
    have := (c.label i).isLt
    omega
  · rintro ⟨c⟩
    apply Nat.dvd_antisymm (period_dvd_two G hG v)
    apply (dvd_period_iff _ _ 2).mpr
    intro n hn
    exact (colorPartition G hG c).dvd_length rfl hn.2

theorem period_one_of_nonbipartite : GraphPeriodMixingSpec.period_one_of_nonbipartite.{u} := by
  intro V _ _ G _ hG hGnb v
  exact (Nat.prime_two.eq_one_or_self_of_dvd _ (period_dvd_two G hG v)).resolve_right
    (fun hv => hGnb ((period_two_iff_bipartite G hG v).mp hv))

theorem nonbipartite_mixing : GraphPeriodMixingSpec.nonbipartite_mixing.{u} := by
  intro V _ _ G _ hG hGnb ν
  letI : MeasurableSpace V := ⊤
  exact aperiodic_tendsto_totalVariation_evolve _ _
    (GraphStationarity.neighborKernel_irreducible G hG)
    (period_one_of_nonbipartite G hG hGnb) (GraphStationarity.stationary G hG) ν

theorem bipartite_limits : GraphPeriodMixingSpec.bipartite_limits.{u} := by
  intro V _ _ G _ hG c
  letI : MeasurableSpace V := ⊤
  let C := colorPartition G hG c
  refine ⟨?_, ?_, ?_⟩
  · exact C.class_mass _ (GraphStationarity.stationary G hG)
  · intro i n
    convert C.power_class i n using 1
    congr 1
    ext v
    simp only [CyclicPartition.classSet, CyclicPartition.advance, Set.mem_ofPred_eq,
      Fin.ext_iff]
    rfl
  · exact cyclic_residue_limit _ _ 2 C
      (GraphStationarity.neighborKernel_irreducible G hG)
      (GraphStationarity.stationary G hG)
      (fun v => (period_two_iff_bipartite G hG v).mpr ⟨c⟩)

theorem cesaro_mixing : GraphPeriodMixingSpec.cesaro_mixing.{u} := by
  intro V _ _ G _ hG ν
  letI : MeasurableSpace V := ⊤
  exact cesaro_tendsto _ _ (GraphStationarity.neighborKernel_irreducible G hG)
    (GraphStationarity.stationary G hG) ν

/-- Positive transitions remain positive after adding a holding probability. -/
theorem lazyKernel_pos {S : Type u} (P : StochasticMatrix S)
    (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1) {i j : S} (hij : 0 < P i j) :
    0 < lazyKernel P α h₀ h₁ i j := by
  rw [lazyKernel_apply]
  exact (ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (by linarith), hij⟩).trans_le
    le_add_self

/-- An arbitrary positive transition path survives lazification. -/
theorem lazyKernel_power_pos {S : Type u} (P : StochasticMatrix S)
    (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1) (n : ℕ) {i j : S}
    (hij : 0 < power P n i j) : 0 < power (lazyKernel P α h₀ h₁) n i j := by
  induction n generalizing j with
  | zero => simpa only [power_zero] using hij
  | succ n ih =>
    obtain ⟨k, hk, hkj⟩ := power_pos_split P n 1 hij
    apply power_pos_add (lazyKernel P α h₀ h₁) (ih hk)
    simpa only [power_one] using lazyKernel_pos P α h₀ h₁ (by simpa only [power_one] using hkj)

/-- Holding preserves every detailed balance identity. -/
theorem lazyKernel_detailedBalance {S : Type u} (P : StochasticMatrix S)
    (π : ProbabilityLaw S) (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1)
    (hπ : DetailedBalance P π) : DetailedBalance (lazyKernel P α h₀ h₁) π := by
  intro i j
  rw [lazyKernel_apply, lazyKernel_apply]
  have hdelta : π i * (if j = i then (1 : ℝ≥0∞) else 0) =
      π j * (if i = j then (1 : ℝ≥0∞) else 0) := by
    by_cases h : j = i
    · subst j
      simp
    · simp [h, Ne.symm h]
  calc
    _ = ENNReal.ofReal α * (π i * (if j = i then 1 else 0)) +
        ENNReal.ofReal (1-α) * (π i * P i j) := by ring
    _ = ENNReal.ofReal α * (π j * (if i = j then 1 else 0)) +
        ENNReal.ofReal (1-α) * (π j * P j i) := by rw [hdelta, hπ i j]
    _ = _ := by ring

theorem lazy_stationary : GraphPeriodMixingSpec.lazy_stationary.{u} := by
  intro V _ _ G _ hG α h₀ h₁
  exact detailedBalance_stationary _ _ (lazyKernel_detailedBalance _ _ α h₀ h₁
    (GraphStationarity.detailed_balance G hG))

theorem lazy_irreducible : GraphPeriodMixingSpec.lazy_irreducible.{u} := by
  intro V _ _ G _ hG α h₀ h₁ i j
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := GraphStationarity.neighborKernel_irreducible G hG i j
  exact ⟨⟨m, lazyKernel_power_pos _ α h₀ h₁ m hm⟩,
    ⟨n, lazyKernel_power_pos _ α h₀ h₁ n hn⟩⟩

theorem lazy_aperiodic : GraphPeriodMixingSpec.lazy_aperiodic.{u} := by
  intro V _ _ G _ hG α h₀ h₁ v
  apply Nat.eq_one_of_dvd_one
  apply period_dvd_returnLength _ _ 1
  refine ⟨by decide, ?_⟩
  rw [power_one, lazyKernel_apply, ite_eq_left rfl, mul_one]
  exact (ENNReal.ofReal_pos.mpr h₀).trans_le le_self_add

theorem lazy_mixing : GraphPeriodMixingSpec.lazy_mixing.{u} := by
  intro V _ _ G _ hG α h₀ h₁ ν
  letI : MeasurableSpace V := ⊤
  exact aperiodic_tendsto_totalVariation_evolve _ _ (lazy_irreducible G hG α h₀ h₁)
    (lazy_aperiodic G hG α h₀ h₁) (lazy_stationary G hG α h₀ h₁) ν

end
end P207.Walk.GraphPeriodMixing
