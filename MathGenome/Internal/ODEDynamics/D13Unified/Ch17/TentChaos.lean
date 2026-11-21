import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.TentChaos
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.LogisticTent
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.ConjugacyTransport
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ChaosDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ShiftCompactness
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra

noncomputable section
namespace D13Unified.Ch17.TentChaos
open Set Topology
open D13Unified.Ch15.LogisticTent
open D13Unified.Ch17.ChaosDefinitions

local notation "τ" => (fun x : Interval => tentMap x)

abbrev leftBranch := Specs.D13Unified.Ch17.TentChaos.leftBranch
abbrev rightBranch := Specs.D13Unified.Ch17.TentChaos.rightBranch

lemma left_inverse (y : Interval) : tentMap (leftBranch y) = y := by
  apply Subtype.ext
  rw [tentBranches.1 _ (by change (y : ℝ) / 2 ≤ 1 / 2; linarith [y.property.2])]
  change 2 * ((y : ℝ) / 2) = (y : ℝ)
  ring

lemma right_inverse (y : Interval) : tentMap (rightBranch y) = y := by
  apply Subtype.ext
  rw [tentBranches.2 _ (by change 1 / 2 ≤ 1 - (y : ℝ) / 2; linarith [y.property.2])]
  change 2 - 2 * (1 - (y : ℝ) / 2) = (y : ℝ)
  ring

/-- Choose a branch containing the specified point. The turning point belongs
to both branches; choosing the left one there does not assert unique coding. -/
def inverseAt (x : Interval) : Interval → Interval :=
  if (x : ℝ) ≤ 1 / 2 then leftBranch else rightBranch

lemma inverseAt_rightInverse (x y : Interval) : tentMap (inverseAt x y) = y := by
  unfold inverseAt
  split_ifs <;> [exact left_inverse y; exact right_inverse y]

lemma inverseAt_orbit (x : Interval) : inverseAt x (tentMap x) = x := by
  apply Subtype.ext
  unfold inverseAt
  split_ifs with hx
  · change (tentMap x : ℝ) / 2 = (x : ℝ)
    rw [tentBranches.1 x hx]
    ring
  · change 1 - (tentMap x : ℝ) / 2 = (x : ℝ)
    rw [tentBranches.2 x (by linarith)]
    ring

lemma inverseAt_continuous (x : Interval) : Continuous (inverseAt x) := by
  unfold inverseAt
  split_ifs
  · exact Continuous.subtype_mk (continuous_subtype_val.div_const 2) _
  · exact Continuous.subtype_mk
      (continuous_const.sub (continuous_subtype_val.div_const 2)) _

lemma inverseAt_dist (x y z : Interval) :
    dist (inverseAt x y) (inverseAt x z) = (1 / 2 : ℝ) * dist y z := by
  unfold inverseAt
  split_ifs
  · change |(y : ℝ) / 2 - (z : ℝ) / 2| = (1 / 2 : ℝ) * |(y : ℝ) - (z : ℝ)|
    rw [← sub_div, abs_div]
    norm_num
    ring
  · change |(1 - (y : ℝ) / 2) - (1 - (z : ℝ) / 2)| =
      (1 / 2 : ℝ) * |(y : ℝ) - (z : ℝ)|
    rw [show (1 - (y : ℝ) / 2) - (1 - (z : ℝ) / 2) =
      -((y : ℝ) - (z : ℝ)) / 2 by ring, abs_div, abs_neg]
    norm_num
    ring

/-- A full inverse branch of the nth iterate containing x. -/
def inverseIterate : ℕ → Interval → Interval → Interval
  | 0, _, y => y
  | n + 1, x, y => inverseAt x (inverseIterate n (tentMap x) y)

lemma inverseIterate_rightInverse (n : ℕ) (x y : Interval) :
    τ^[n] (inverseIterate n x y) = y := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, inverseIterate, inverseAt_rightInverse, ih]

lemma inverseIterate_orbit (n : ℕ) (x : Interval) :
    inverseIterate n x (τ^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, inverseIterate, ih, inverseAt_orbit]

lemma inverseIterate_continuous (n : ℕ) (x : Interval) :
    Continuous (inverseIterate n x) := by
  induction n generalizing x with
  | zero => exact continuous_id
  | succ n ih => exact (inverseAt_continuous x).comp (ih (tentMap x))

lemma inverseIterate_dist (n : ℕ) (x y z : Interval) :
    dist (inverseIterate n x y) (inverseIterate n x z) =
      (1 / 2 : ℝ) ^ n * dist y z := by
  induction n generalizing x with
  | zero => simp [inverseIterate]
  | succ n ih =>
    rw [inverseIterate, inverseIterate, inverseAt_dist, ih, pow_succ]
    ring

lemma interval_dist_le_one (x y : Interval) : dist x y ≤ 1 := by
  change |(x : ℝ) - (y : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]

lemma inverseIterate_dist_center (n : ℕ) (x y : Interval) :
    dist (inverseIterate n x y) x ≤ (1 / 2 : ℝ) ^ n := by
  calc
    _ = dist (inverseIterate n x y) (inverseIterate n x (τ^[n] x)) := by
      rw [inverseIterate_orbit]
    _ = (1 / 2 : ℝ) ^ n * dist y (τ^[n] x) := inverseIterate_dist _ _ _ _
    _ ≤ (1 / 2 : ℝ) ^ n * 1 :=
      mul_le_mul_of_nonneg_left (interval_dist_le_one _ _) (by positivity)
    _ = _ := mul_one _

/-- Every neighborhood contains a complete inverse branch of positive depth. -/
lemma small_inverse_branch (x : Interval) (U : Set Interval) (hU : U ∈ 𝓝 x) :
    ∃ n : ℕ, 0 < n ∧ ∀ y, inverseIterate n x y ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨m + 1, by omega, fun y => hball ?_⟩
  apply lt_of_le_of_lt (inverseIterate_dist_center _ _ _) (lt_of_le_of_lt ?_ hm)
  rw [pow_succ]
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) m]

theorem exactness : Specs.D13Unified.Ch17.TentChaos.exactness := by
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨n, _, hn⟩ := small_inverse_branch x U (hU.mem_nhds hx)
  refine ⟨n, Set.eq_univ_of_forall fun y => ?_⟩
  exact ⟨inverseIterate n x y, hn y, inverseIterate_rightInverse n x y⟩

theorem transitivity : Specs.D13Unified.Ch17.TentChaos.transitivity := by
  intro U V hU hUne _ hVne
  obtain ⟨n, hn⟩ := exactness U hU hUne
  refine ⟨n, ?_⟩
  change ((τ^[n] '' U) ∩ V).Nonempty
  rw [show τ^[n] '' U = univ from hn, univ_inter]
  exact hVne

lemma interval_fixed_point (b : Interval → Interval) (hb : Continuous b) :
    ∃ y, b y = y := by
  have h : ∃ y, (b y : ℝ) = (y : ℝ) :=
    intermediate_value_univ₂ (continuous_subtype_val.comp hb) continuous_subtype_val
      (a := ⟨1, by norm_num⟩) (b := ⟨0, by norm_num⟩)
      (b ⟨1, by norm_num⟩).property.2 (b ⟨0, by norm_num⟩).property.1
  exact h.imp fun y hy => Subtype.ext hy

theorem periodicDensity : Specs.D13Unified.Ch17.TentChaos.periodicDensity := by
  apply (densePeriodicPoints_iff_open (fun x : Interval => tentMap x)).mpr
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨n, hn, hbranch⟩ := small_inverse_branch x U (hU.mem_nhds hx)
  obtain ⟨y, hy⟩ := interval_fixed_point _ (inverseIterate_continuous n x)
  refine ⟨y, ?_, n, hn, ?_⟩
  · rw [← hy]
    exact hbranch y
  · calc
      τ^[n] y = τ^[n] (inverseIterate n x y) := by rw [hy]
      _ = y := inverseIterate_rightInverse n x y

theorem sensitivityConstants : Specs.D13Unified.Ch17.TentChaos.sensitivityConstants := by
  intro δ hδ hδhalf x U hU
  obtain ⟨n, _, hn⟩ := small_inverse_branch x U hU
  let z := τ^[n] x
  have hz : dist z (⟨0, by norm_num⟩ : Interval) ≥ 1 / 2 ∨
      dist z (⟨1, by norm_num⟩ : Interval) ≥ 1 / 2 := by
    change |(z : ℝ) - 0| ≥ 1 / 2 ∨ |(z : ℝ) - 1| ≥ 1 / 2
    rw [sub_zero, abs_of_nonneg z.property.1, abs_of_nonpos (by linarith [z.property.2])]
    by_cases h : 1 / 2 ≤ (z : ℝ)
    · exact Or.inl h
    · right; linarith
  rcases hz with hz | hz
  · refine ⟨inverseIterate n x ⟨0, by norm_num⟩, hn _, n, ?_⟩
    change δ < dist z (τ^[n] (inverseIterate n x _))
    rw [inverseIterate_rightInverse]
    exact lt_of_lt_of_le hδhalf hz
  · refine ⟨inverseIterate n x ⟨1, by norm_num⟩, hn _, n, ?_⟩
    change δ < dist z (τ^[n] (inverseIterate n x _))
    rw [inverseIterate_rightInverse]
    exact lt_of_lt_of_le hδhalf hz

theorem tentChaos : Specs.D13Unified.Ch17.TentChaos.tentChaos := by
  refine ⟨transitivity, periodicDensity, (1 / 4 : ℝ), by norm_num, ?_⟩
  exact sensitivityConstants _ (by norm_num) (by norm_num)

/-- Sensitivity transports through the inverse uniform continuity estimate.
Using half the transported separation retains a strict inequality. -/
theorem compactSensitivityTransport :
    Specs.D13Unified.Ch17.TentChaos.compactSensitivityTransport := by
  intro X Y _ _ _ F G h hh hs
  obtain ⟨δ, hδ, hs⟩ := hs
  obtain ⟨ε, hε, hmod⟩ :=
    Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous h.symm.continuous) δ hδ
  refine ⟨ε / 2, by positivity, ?_⟩
  intro y U hU
  obtain ⟨x, rfl⟩ := h.surjective y
  obtain ⟨x', hx', n, hn⟩ := hs x (h ⁻¹' U)
    (h.continuous.continuousAt.preimage_mem_nhds hU)
  refine ⟨h x', hx', n, ?_⟩
  change ε / 2 < dist (G^[n] (h x)) (G^[n] (h x'))
  change δ < dist (F^[n] x) (F^[n] x') at hn
  rw [← hh.iterate_right n x, ← hh.iterate_right n x']
  have hsep : ε ≤ dist (h (F^[n] x)) (h (F^[n] x')) := by
    by_contra! hlt
    have hsmall := hmod hlt
    simp only [h.symm_apply_apply] at hsmall
    exact (not_lt_of_ge hn.le) hsmall
  linarith

lemma transitivity_transport {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y) (hh : Function.Semiconj h F G)
    (ht : TopologicallyTransitive F) : TopologicallyTransitive G := by
  apply (topologicallyTransitive_iff_exists_mem G).mpr
  intro U V hU hUne hV hVne
  have hpull (A : Set Y) (hne : A.Nonempty) : (h ⁻¹' A).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨h.symm y, by simpa using hy⟩
  obtain ⟨x, hx, n, hn⟩ := (topologicallyTransitive_iff_exists_mem F).mp ht
    (h ⁻¹' U) (h ⁻¹' V) (hU.preimage h.continuous) (hpull U hUne)
    (hV.preimage h.continuous) (hpull V hVne)
  refine ⟨h x, hx, n, ?_⟩
  rw [← hh.iterate_right n x]
  exact hn

lemma periodicDensity_transport {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y) (hh : Function.Semiconj h F G)
    (hp : DensePeriodicPoints F) : DensePeriodicPoints G := by
  apply (densePeriodicPoints_iff_open G).mpr
  intro U hU hUne
  obtain ⟨y, hy⟩ := hUne
  have hne : (h ⁻¹' U).Nonempty := ⟨h.symm y, by simpa using hy⟩
  obtain ⟨x, hx, n, hn, hfix⟩ := (densePeriodicPoints_iff_open F).mp hp
    (h ⁻¹' U) (hU.preimage h.continuous) hne
  refine ⟨h x, hx, n, hn, ?_⟩
  rw [← hh.iterate_right n x, hfix]

theorem logisticChaos : Specs.D13Unified.Ch17.TentChaos.logisticChaos := by
  obtain ⟨h, _, _, hh⟩ := conjugacy
  exact ⟨transitivity_transport _ _ h hh tentChaos.1,
    periodicDensity_transport _ _ h hh tentChaos.2.1,
    compactSensitivityTransport _ _ h hh tentChaos.2.2⟩

theorem noSymbolicHomeomorph : Specs.D13Unified.Ch17.TentChaos.noSymbolicHomeomorph := by
  rintro ⟨h⟩
  have hc : IsConnected (h '' (univ : Set Interval)) :=
    isConnected_univ.image h h.continuous.continuousOn
  have hsub := D13Unified.Ch17.ShiftCompactness.connected_subsingletonPlus _ hc
  have heq := hsub (mem_image_of_mem h (mem_univ (⟨0, by norm_num⟩ : Interval)))
    (mem_image_of_mem h (mem_univ (⟨1, by norm_num⟩ : Interval)))
  have h01 := congrArg Subtype.val (h.injective heq)
  norm_num at h01

theorem codingNotInjective : Specs.D13Unified.Ch17.TentChaos.codingNotInjective := by
  intro π hπ hsur hinj
  let h := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective π ⟨hinj, hsur⟩) hπ
  exact noSymbolicHomeomorph ⟨h.symm⟩

theorem branchProperties : Specs.D13Unified.Ch17.TentChaos.branchProperties := by
  refine ⟨?_, ?_, left_inverse, right_inverse, ?_⟩
  · intro x y hxy
    have hv := congrArg Subtype.val hxy
    apply Subtype.ext
    change (x : ℝ) / 2 = (y : ℝ) / 2 at hv
    linarith
  · intro x y hxy
    have hv := congrArg Subtype.val hxy
    apply Subtype.ext
    change 1 - (x : ℝ) / 2 = 1 - (y : ℝ) / 2 at hv
    linarith
  · intro hdis
    have hl : (⟨1 / 2, by norm_num⟩ : Interval) ∈ range leftBranch :=
      ⟨⟨1, by norm_num⟩, by apply Subtype.ext; norm_num [leftBranch,
        Specs.D13Unified.Ch17.TentChaos.leftBranch]⟩
    have hr : (⟨1 / 2, by norm_num⟩ : Interval) ∈ range rightBranch :=
      ⟨⟨1, by norm_num⟩, by apply Subtype.ext; norm_num [rightBranch,
        Specs.D13Unified.Ch17.TentChaos.rightBranch]⟩
    exact Set.disjoint_left.mp hdis hl hr

end D13Unified.Ch17.TentChaos
