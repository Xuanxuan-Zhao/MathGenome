import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.WeakContinuityImpliesStrong
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PettisMeasurability
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.RealVectorSpace

/-!
Weak continuity at zero implies strong continuity, paper.tex:16474–16522.

Two uniform-boundedness arguments first bound the operators near zero. Grid
samples approaching each time from above show that each orbit is weakly
measurable and lies in a separable closed subspace. The accepted countable
separating-family construction and Lusin–Souslin then give actual strong
measurability, hence Bochner integrability on compact intervals.

Integrated orbit vectors have continuous translated endpoints. Their scaled
averages converge weakly to the original vectors by scalar FTC. Since the
subspace of strong continuity vectors is norm closed and therefore weakly
closed, it is the whole space. Local bounds then give continuity at every time.
All duals are scalar-linear; no ambient separability is assumed.
-/

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology NNReal
universe u v

namespace ExpandedFA.Semigroups
open WeakContinuitySpec
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Adding the known value T(0)=I turns the punctured right limit in the
source hypothesis into a limit along the whole half-line neighborhood. -/
theorem weakAtZero_of_right {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakRightAtZero T) : WeakAtZero T := by
  have hset : Ioi (0 : ℝ≥0) = {0}ᶜ := by
    ext t
    simp only [mem_Ioi, mem_compl_iff, mem_singleton_iff, pos_iff_ne_zero]
  intro x ℓ
  have hp := hw x ℓ
  rw [hset] at hp
  have hc : ContinuousAt (fun t => ℓ (T t x)) 0 :=
    continuousAt_iff_punctured_nhds.mpr (by simpa only [hl.1, ContinuousLinearMap.id_apply] using hp)
  simpa only [hl.1, ContinuousLinearMap.id_apply] using hc.tendsto

/-- Uniform boundedness on the dual turns weak sequential convergence into
norm boundedness; no separability or completeness of E is required. -/
theorem weakly_convergent_sequence_bounded (f : ℕ → E) (x : E)
    (hf : ∀ ℓ : E →L[𝕜] 𝕜, Tendsto (fun n => ℓ (f n)) atTop (𝓝 (ℓ x))) :
    ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C := by
  have hb (ℓ : E →L[𝕜] 𝕜) : ∃ C : ℝ, ∀ n, ‖ℓ (f n)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (hf ℓ)).exists_norm_le
    exact ⟨C, fun n => hC _ (mem_range_self n)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun n => NormedSpace.inclusionInDoubleDual 𝕜 E (f n)) hb
  refine ⟨C, fun n => ?_⟩
  rw [← (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).norm_map (f n)]
  exact hC n

/-- A sequence of times approaching zero has uniformly bounded operator norms. -/
theorem operator_sequence_bounded [CompleteSpace E]
    {T : ℝ≥0 → E →L[𝕜] E} (hw : WeakAtZero T)
    (t : ℕ → ℝ≥0) (ht : Tendsto t atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ n, ‖T (t n)‖ ≤ C := by
  apply banach_steinhaus
  intro x
  exact weakly_convergent_sequence_bounded _ x (fun ℓ => (hw x ℓ).comp ht)

/-- Weak convergence at zero forces a uniform bound on a whole interval.
The contradiction sequence does not require any initial time regularity. -/
theorem bounded_near_zero [CompleteSpace E]
    {T : ℝ≥0 → E →L[𝕜] E} (hw : WeakAtZero T) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≤ δ, ‖T t‖ ≤ C := by
  by_contra h
  push Not at h
  have hex (n : ℕ) : ∃ t : ℝ≥0, t ≤ (n + 1 : ℝ≥0)⁻¹ ∧ (n : ℝ) < ‖T t‖ := by
    exact h _ (by positivity) (n : ℝ) (by positivity)
  choose t ht hnorm using hex
  have ht0 : Tendsto t atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_add_atTop_iff_nat 1).2 tendsto_inv_atTop_nhds_zero_nat)
      (fun _ => bot_le) (fun n => by simpa only [Nat.cast_add, Nat.cast_one] using ht n)
  obtain ⟨C, hC⟩ := operator_sequence_bounded hw t ht0
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact (hn.trans (hnorm n)).not_ge (hC n)

/-- Scalar orbits are right continuous at every time. The functional in the
hypothesis is precomposed with the fixed bounded operator T(t). -/
theorem scalar_right_limit {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakAtZero T)
    (x : E) (ℓ : E →L[𝕜] 𝕜) (t : ℝ≥0) :
    Tendsto (fun h => ℓ (T (t + h) x)) (𝓝 0) (𝓝 (ℓ (T t x))) := by
  simpa only [hl.2, ContinuousLinearMap.comp_apply] using hw x (ℓ.comp (T t))

/-- The semigroup law propagates a near-zero bound to any finite interval. -/
theorem locallyBounded_of_bounded_near_zero
    {T : ℝ≥0 → E →L[𝕜] E} (hl : SemigroupLaws T)
    (hb : ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≤ δ, ‖T t‖ ≤ C) :
    LocallyBounded T := by
  obtain ⟨δ, hδ, C, _, hC⟩ := hb
  let B : ℝ := max C 1
  have hB : 1 ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hCB : C ≤ B := le_max_left _ _
  have hn : ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ n * δ → ‖T t‖ ≤ B ^ n := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have ht0 : t = 0 := by simpa using ht
      simpa [ht0, hl.1] using (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E))
    | succ n ih =>
      intro t ht
      by_cases hs : t ≤ n * δ
      · exact (ih t hs).trans (by
          rw [pow_succ]
          exact le_mul_of_one_le_right (pow_nonneg hB0 _) hB)
      · have hs' : (n : ℝ≥0) * δ ≤ t := le_of_lt (lt_of_not_ge hs)
        have hrem : t - n * δ ≤ δ := by
          apply (tsub_le_iff_right).2
          calc
            t ≤ (↑(n + 1) : ℝ≥0) * δ := ht
            _ = δ + ↑n * δ := by simp only [Nat.cast_add, Nat.cast_one]; ring
        have heq : t = ↑n * δ + (t - ↑n * δ) :=
          (add_tsub_cancel_of_le hs').symm
        calc
          ‖T t‖ = ‖(T (↑n * δ)).comp (T (t - ↑n * δ))‖ := by
            conv_lhs => rw [heq, hl.2]
          _ ≤ ‖T (↑n * δ)‖ * ‖T (t - ↑n * δ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ B ^ n * B := mul_le_mul (ih _ le_rfl) ((hC _ hrem).trans hCB)
            (norm_nonneg _) (pow_nonneg hB0 _)
          _ = B ^ (n + 1) := (pow_succ _ _).symm
  intro a
  obtain ⟨n, hn'⟩ := exists_nat_gt (a / δ)
  have ha : a ≤ (n : ℝ≥0) * δ := by
    exact ((div_lt_iff₀ hδ).mp hn').le
  exact ⟨B ^ n, pow_nonneg hB0 _, fun t ht => hn n t (ht.trans ha)⟩

/-- All compact time intervals have uniformly bounded operator norms. -/
theorem locallyBounded_of_weak [CompleteSpace E]
    {T : ℝ≥0 → E →L[𝕜] E} (hl : SemigroupLaws T) (hw : WeakAtZero T) :
    LocallyBounded T :=
  locallyBounded_of_bounded_near_zero hl (bounded_near_zero hw)

/-- The quantitative estimate used to pass from zero to arbitrary times. -/
theorem orbit_distance_le {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (x : E) {s t : ℝ≥0} (hst : s ≤ t)
    {C : ℝ} (hsC : ‖T s‖ ≤ C) :
    dist (T t x) (T s x) ≤ C * ‖T (t - s) x - x‖ := by
  have heq : T t x - T s x = T s (T (t - s) x - x) := by
    rw [map_sub, ← ContinuousLinearMap.comp_apply, ← hl.2, add_tsub_cancel_of_le hst]
  rw [dist_eq_norm, heq]
  exact ((T s).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hsC (norm_nonneg _))

/-- Local boundedness and strong convergence at zero give norm continuity
on the entire closed half-line, including left continuity at positive times. -/
theorem continuous_orbits_of_strongAtZero {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hb : LocallyBounded T) (hs : StrongAtZero T)
    (x : E) : Continuous (fun t => T t x) := by
  apply continuous_iff_continuousAt.2
  intro t
  obtain ⟨C, hC, hbound⟩ := hb (t + 1)
  have hright : Tendsto (fun s : ℝ≥0 => ‖T (s - t) x - x‖) (𝓝 t) (𝓝 0) := by
    have htime : Tendsto (fun s : ℝ≥0 => s - t) (𝓝 t) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ≥0 => s - t) := by fun_prop
      simpa only [tsub_self] using hc.continuousAt.tendsto (x := t)
    simpa using ((hs x).comp htime).sub_const x |>.norm
  have hleft : Tendsto (fun s : ℝ≥0 => ‖T (t - s) x - x‖) (𝓝 t) (𝓝 0) := by
    have htime : Tendsto (fun s : ℝ≥0 => t - s) (𝓝 t) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ≥0 => t - s) := by fun_prop
      simpa only [tsub_self] using hc.continuousAt.tendsto (x := t)
    simpa using ((hs x).comp htime).sub_const x |>.norm
  apply tendsto_iff_dist_tendsto_zero.2
  have hlim : Tendsto (fun s : ℝ≥0 => C *
      (‖T (s - t) x - x‖ + ‖T (t - s) x - x‖)) (𝓝 t) (𝓝 0) := by
    simpa using (hright.add hleft).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
  have hnear : ∀ᶠ s : ℝ≥0 in 𝓝 t, s < t + 1 :=
    Iio_mem_nhds (lt_add_one t)
  filter_upwards [hnear] with s hs'
  rcases le_total s t with hst | hts
  · calc
      dist (T s x) (T t x) = dist (T t x) (T s x) := dist_comm _ _
      _ ≤ C * ‖T (t - s) x - x‖ := orbit_distance_le hl x hst (hbound s hs'.le)
      _ ≤ C * (‖T (s - t) x - x‖ + ‖T (t - s) x - x‖) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hC
  · exact (orbit_distance_le hl x hts (hbound t (by simp))).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hC)

/-- Once continuity is known, the orbit is strongly measurable without a
separability assumption on its ambient space. -/
theorem orbit_stronglyMeasurable_of_continuous {T : ℝ≥0 → E →L[𝕜] E}
    (hc : ∀ x, Continuous (fun t => T t x)) (x : E) :
    StronglyMeasurable (fun t : ℝ => T (Real.toNNReal t) x) :=
  ((hc x).comp continuous_real_toNNReal).stronglyMeasurable

/-- This compact-interval statement includes a=0 and empty intervals a<0. -/
theorem orbit_integrableOn_of_continuous {T : ℝ≥0 → E →L[𝕜] E}
    (hc : ∀ x, Continuous (fun t => T t x)) (x : E) (a : ℝ) :
    IntegrableOn (fun t : ℝ => T (Real.toNNReal t) x) (Icc 0 a) :=
  ((hc x).comp continuous_real_toNNReal).integrableOn_Icc

/-- Countable grids, rounded upward. They approach each point from its right. -/
def upperGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌈t * (n + 1 : ℝ≥0)⌉₊ : ℝ≥0) / (n + 1 : ℝ≥0)

theorem upperGrid_ge (n : ℕ) (t : ℝ≥0) : t ≤ upperGrid n t := by
  apply (le_div_iff₀ (by positivity : 0 < (n + 1 : ℝ≥0))).2
  exact Nat.le_ceil _

theorem upperGrid_le (n : ℕ) (t : ℝ≥0) :
    upperGrid n t ≤ t + (n + 1 : ℝ≥0)⁻¹ := by
  calc
    upperGrid n t ≤ (t * (n + 1 : ℝ≥0) + 1) / (n + 1 : ℝ≥0) := by
      exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le (by positivity)
    _ = t + (n + 1 : ℝ≥0)⁻¹ := by
      rw [add_div, mul_div_cancel_right₀ _ (by positivity), one_div]

theorem upperGrid_sub_tendsto (t : ℝ≥0) :
    Tendsto (fun n => upperGrid n t - t) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((tendsto_add_atTop_iff_nat 1).2 tendsto_inv_atTop_nhds_zero_nat)
    (fun _ => bot_le)
  intro n
  apply tsub_le_iff_right.2
  simpa only [Nat.cast_add, Nat.cast_one, add_comm] using upperGrid_le n t

/-- Scalar measurability is proved by measurable grid samples and their weak
limits, rather than assuming two-sided weak continuity. -/
theorem scalar_orbit_measurable {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakAtZero T) (x : E) (ℓ : E →L[𝕜] 𝕜) :
    @Measurable ℝ≥0 𝕜 _ (borel 𝕜) (fun t => ℓ (T t x)) := by
  letI : MeasurableSpace 𝕜 := borel 𝕜
  have hm (n : ℕ) : Measurable (fun t => ℓ (T (upperGrid n t) x)) := by
    exact (measurable_of_countable (fun k : ℕ => ℓ (T (k / (n + 1 : ℝ≥0)) x))).comp
      (measurable_id.mul_const (n + 1 : ℝ≥0)).nat_ceil
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro t
  have ht := (scalar_right_limit hl hw x ℓ t).comp (upperGrid_sub_tendsto t)
  simpa only [Function.comp_def, add_tsub_cancel_of_le (upperGrid_ge _ _)] using ht

/-- Closed linear subspaces contain all weak limits of their sequences.
This is the real-convex weak closure theorem for either scalar field. -/
theorem mem_closed_submodule_of_weak_tendsto (S : Submodule 𝕜 E)
    (hS : IsClosed (S : Set E)) (f : ℕ → E) (x : E)
    (hm : ∀ n, f n ∈ S)
    (hf : ∀ ℓ : E →L[𝕜] 𝕜, Tendsto (fun n => ℓ (f n)) atTop (𝓝 (ℓ x))) :
    x ∈ S := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hconv : Convex ℝ (S : Set E) := (S.restrictScalars ℝ).convex
  have heq : toWeakSpace 𝕜 E '' (S : Set E) =
      closure (toWeakSpace 𝕜 E '' (S : Set E)) := by
    simpa only [hS.closure_eq] using hconv.toWeakSpace_closure 𝕜
  have hclosed : IsClosed (toWeakSpace 𝕜 E '' (S : Set E)) := by
    rw [heq]
    exact isClosed_closure
  have hinj : Function.Injective (topDualPairing 𝕜 E).flip := by
    intro x y h
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
    intro ℓ
    exact DFunLike.congr_fun h ℓ
  have ht : Tendsto (fun n => toWeakSpace 𝕜 E (f n)) atTop
      (𝓝 (toWeakSpace 𝕜 E x)) :=
    (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing 𝕜 E).flip hinj).2 hf
  obtain ⟨y, hy, hyx⟩ := hclosed.mem_of_tendsto ht
    (Eventually.of_forall (fun n => mem_image_of_mem _ (hm n)))
  exact (toWeakSpace 𝕜 E).injective hyx ▸ hy

/-- Each orbit is contained in a separable closed linear subspace, even when
E itself is nonseparable. The generators are the countable grid values. -/
theorem orbit_separable_subspace {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakAtZero T) (x : E) :
    ∃ S : Submodule 𝕜 E, IsClosed (S : Set E) ∧
      TopologicalSpace.IsSeparable (S : Set E) ∧ ∀ t, T t x ∈ S := by
  let A : Set E := range (fun p : ℕ × ℕ => T (p.2 / (p.1 + 1 : ℝ≥0)) x)
  let S := (Submodule.span 𝕜 A).topologicalClosure
  have hclosed : IsClosed (S : Set E) := Submodule.isClosed_topologicalClosure _
  have hsep : TopologicalSpace.IsSeparable (S : Set E) :=
    ((countable_range _).isSeparable.span (R := 𝕜)).closure
  refine ⟨S, hclosed, hsep, fun t => ?_⟩
  apply mem_closed_submodule_of_weak_tendsto S hclosed
    (fun n => T (upperGrid n t) x) (T t x)
  · intro n
    apply (Submodule.span 𝕜 A).le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨(n, ⌈t * (n + 1 : ℝ≥0)⌉₊), rfl⟩
  · intro ℓ
    have ht := (scalar_right_limit hl hw x ℓ t).comp (upperGrid_sub_tendsto t)
    simpa only [Function.comp_def, add_tsub_cancel_of_le (upperGrid_ge _ _)] using ht

/-- Actual strong measurability of orbits follows from their separable
closed span and the accepted countable separating family construction.
No completion of the Borel measure, or separability of E, is assumed. -/
theorem orbit_stronglyMeasurable [CompleteSpace E]
    {T : ℝ≥0 → E →L[𝕜] E} (hl : SemigroupLaws T) (hw : WeakAtZero T) (x : E) :
    StronglyMeasurable (fun t => T t x) := by
  classical
  letI : MeasurableSpace 𝕜 := borel 𝕜
  obtain ⟨S, hclosed, hsep, hmem⟩ := orbit_separable_subspace hl hw x
  letI : SeparableSpace S := hsep.separableSpace
  letI : CompleteSpace S := hclosed.isComplete.completeSpace_coe
  letI : MeasurableSpace S := borel S
  letI : BorelSpace S := ⟨rfl⟩
  let g : ℝ≥0 → S := fun t => ⟨T t x, hmem t⟩
  obtain ⟨ℓ, hℓ⟩ := FunctionSpaces.exists_countable_separating_on_submodule 𝕜 S
  let J : S → ℕ → 𝕜 := fun y n => ℓ n (y : E)
  have hJ : Continuous J :=
    continuous_pi fun n => (ℓ n).continuous.comp continuous_subtype_val
  have hJi : Function.Injective J := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hℓ (a - b)
    intro n
    have hn := congrFun hab n
    simpa only [Submodule.coe_sub, map_sub, sub_eq_zero] using hn
  have hJg : Measurable (J ∘ g) := by
    apply Measurable.of_eval
    intro n
    exact scalar_orbit_measurable hl hw x (ℓ n)
  have hg : StronglyMeasurable g :=
    ((hJ.measurableEmbedding hJi).measurable_comp_iff.mp hJg).stronglyMeasurable
  exact continuous_subtype_val.comp_stronglyMeasurable hg

/-- The real-time extension is strongly measurable before any strong
continuity has been proved. -/
theorem real_orbit_stronglyMeasurable [CompleteSpace E]
    {T : ℝ≥0 → E →L[𝕜] E} (hl : SemigroupLaws T) (hw : WeakAtZero T) (x : E) :
    StronglyMeasurable (fun t : ℝ => T (Real.toNNReal t) x) :=
  (orbit_stronglyMeasurable hl hw x).comp_measurable continuous_real_toNNReal.measurable

/-- Measurability and the uniform interval bound supply Bochner integrability
on every compact interval, without assuming the ambient space separable. -/
theorem real_orbit_integrableOn [CompleteSpace E]
    {T : ℝ≥0 → E →L[𝕜] E} (hl : SemigroupLaws T) (hw : WeakAtZero T)
    (x : E) (a b : ℝ) :
    IntegrableOn (fun t : ℝ => T (Real.toNNReal t) x) (Icc a b) := by
  obtain ⟨C, _, hC⟩ := locallyBounded_of_weak hl hw (Real.toNNReal b)
  refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top
    (real_orbit_stronglyMeasurable hl hw x).aestronglyMeasurable
    (C * ‖x‖) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact ((T (Real.toNNReal t)).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hC _ (Real.toNNReal_mono ht.2)) (norm_nonneg _))

/-- The vectors at which the orbit converges strongly form a linear subspace. -/
def continuitySubmodule (T : ℝ≥0 → E →L[𝕜] E) : Submodule 𝕜 E where
  carrier := {x | Tendsto (fun t => T t x) (𝓝 0) (𝓝 x)}
  zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using (tendsto_const_nhds :
    Tendsto (fun _ : ℝ≥0 => (0 : E)) (𝓝 0) (𝓝 0))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq, map_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_ofPred_eq, map_smul] using hx.const_smul c

/-- Uniform operator bounds make the subspace of strong continuity vectors
norm closed. This uses no weak continuity and no completeness. -/
theorem continuitySubmodule_isClosed {T : ℝ≥0 → E →L[𝕜] E}
    (hb : LocallyBounded T) : IsClosed (continuitySubmodule T : Set E) := by
  let F : ℝ≥0 → E →L[𝕜] E := fun t => T (min t 1)
  obtain ⟨C, _, hC⟩ := hb 1
  have hnorm : ∃ C : ℝ, ∀ t, ‖F t‖ ≤ C := ⟨C, fun t => hC _ (min_le_right _ _)⟩
  have hF : Equicontinuous (fun t x => F t x) :=
    ((NormedSpace.equicontinuous_TFAE F).out 6 2).mp hnorm
  have heq : (continuitySubmodule T : Set E) =
      {x | Tendsto (fun t => F t x) (𝓝 0) (𝓝 x)} := by
    ext x
    apply tendsto_congr'
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ≥0) < 1)] with t ht
    dsimp [F]
    rw [min_eq_left ht.le]
  rw [heq]
  exact hF.isClosed_setOfPred_tendsto continuous_id

section Integration
variable [CompleteSpace E]
-- Private, explicitly named instances have module-qualified internal names,
-- so they cannot clash with instances in other semigroup modules.
private local instance weakContinuityNormedSpaceReal : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ 𝕜 E
private local instance weakContinuityIsScalarTower : IsScalarTower ℝ 𝕜 E :=
  IsScalarTower.restrictScalars ℝ 𝕜 E

/-- All intervals, even reversed ones, are integrable for the real orbit extension. -/
theorem real_orbit_intervalIntegrable {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakAtZero T) (x : E) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => T (Real.toNNReal t) x) volume a b := by
  apply (real_orbit_integrableOn hl hw x (min a b) (max a b)).intervalIntegrable

/-- Integrated orbit vectors. Only vector integrals are used: T need not be
Bochner measurable as a function into the operator space. -/
def integratedOrbit (T : ℝ≥0 → E →L[𝕜] E) (a : ℝ≥0) (x : E) : E :=
  ∫ s in (0 : ℝ)..(a : ℝ), T (Real.toNNReal s) x

/-- Translating an integrated orbit vector only moves the two endpoints. -/
theorem integratedOrbit_translate {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakAtZero T) (a h : ℝ≥0) (x : E) :
    T h (integratedOrbit T a x) =
      ∫ s in (h : ℝ)..((a : ℝ) + h), T (Real.toNNReal s) x := by
  rw [integratedOrbit, ← (T h).intervalIntegral_comp_comm
    (real_orbit_intervalIntegrable hl hw x 0 a)]
  have heq : (∫ s in (0 : ℝ)..(a : ℝ), T h (T (Real.toNNReal s) x)) =
      ∫ s in (0 : ℝ)..(a : ℝ), T (Real.toNNReal (s + h)) x := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := by simpa only [min_eq_left a.coe_nonneg] using hs.1
    change T h (T (Real.toNNReal s) x) = T (Real.toNNReal (s + h)) x
    rw [Real.toNNReal_add hs0 h.coe_nonneg, Real.toNNReal_coe, add_comm, hl.2,
      ContinuousLinearMap.comp_apply]
  rw [heq]
  simpa only [zero_add] using
    intervalIntegral.integral_comp_add_right (fun s : ℝ => T (Real.toNNReal s) x)
      (a := 0) (b := (a : ℝ)) (h : ℝ)

/-- The indefinite vector integral is continuous. Hence translating both
endpoints proves that every integrated orbit vector is a continuity vector. -/
theorem integratedOrbit_mem_continuitySubmodule {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakAtZero T) (a : ℝ≥0) (x : E) :
    integratedOrbit T a x ∈ continuitySubmodule T := by
  let f : ℝ → E := fun s => T (Real.toNNReal s) x
  let P : ℝ → E := fun b => ∫ s in (0 : ℝ)..b, f s
  have hP : Continuous P :=
    intervalIntegral.continuous_primitive (real_orbit_intervalIntegrable hl hw x) 0
  have hlim : Tendsto (fun h : ℝ≥0 => P (a + h) - P h) (𝓝 0)
      (𝓝 (integratedOrbit T a x)) := by
    have hc1 : Continuous (fun h : ℝ≥0 => (a : ℝ) + h) := by fun_prop
    have h1 := (hP.comp hc1).continuousAt.tendsto (x := 0)
    have h2 := (hP.comp NNReal.continuous_coe).continuousAt.tendsto (x := 0)
    simpa [P, integratedOrbit] using h1.sub h2
  change Tendsto _ _ _
  convert hlim using 1
  ext h
  rw [integratedOrbit_translate hl hw]
  exact (intervalIntegral.integral_interval_sub_left
    (real_orbit_intervalIntegrable hl hw x 0 (a + h))
    (real_orbit_intervalIntegrable hl hw x 0 h)).symm

/-- Scalar averages of the integrated orbit converge to the scalar value at
zero. The scalar fundamental theorem of calculus supplies the limit. -/
theorem integratedOrbit_scalar_average {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakAtZero T) (x : E) (ℓ : E →L[𝕜] 𝕜)
    (a : ℕ → ℝ≥0) (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => ℓ (((a n : ℝ)⁻¹) • integratedOrbit T (a n) x))
      atTop (𝓝 (ℓ x)) := by
  let f : ℝ → 𝕜 := fun s => ℓ (T (Real.toNNReal s) x)
  have hm : StronglyMeasurable f :=
    ℓ.continuous.comp_stronglyMeasurable (real_orbit_stronglyMeasurable hl hw x)
  have hf0 : f 0 = ℓ x := by simp [f, hl.1]
  have hc : ContinuousAt f 0 := by
    change Tendsto _ _ (𝓝 (f 0))
    rw [hf0]
    have ht : Tendsto Real.toNNReal (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.toNNReal_zero] using
        continuous_real_toNNReal.continuousAt.tendsto (x := 0)
    exact (hw x ℓ).comp ht
  have hd : HasDerivAt (fun b => ∫ s in (0 : ℝ)..b, f s) (f 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (by simp)
      hm.stronglyMeasurableAtFilter hc
  have hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [Function.comp_def, NNReal.coe_zero] using NNReal.continuous_coe.continuousAt.tendsto.comp ha,
      Eventually.of_forall (fun n => ha0 n)⟩
  have hlim := hd.tendsto_slope_zero_right.comp hat
  rw [hf0] at hlim
  convert hlim using 1
  ext n
  dsimp only [Function.comp_def]
  rw [zero_add, intervalIntegral.integral_same, sub_zero, integratedOrbit]
  rw [map_real_smul ℓ ℓ.continuous,
    ← ℓ.intervalIntegral_comp_comm (real_orbit_intervalIntegrable hl hw x 0 (a n))]

/-- The norm-closed subspace of strong continuity vectors contains every
vector, since the scaled integrals in that subspace converge weakly to it. -/
theorem strongAtZero_of_weak {T : ℝ≥0 → E →L[𝕜] E}
    (hl : SemigroupLaws T) (hw : WeakAtZero T) : StrongAtZero T := by
  intro x
  let a : ℕ → ℝ≥0 := fun n => (n + 1 : ℝ≥0)⁻¹
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, Nat.cast_add, Nat.cast_one] using
      ((tendsto_add_atTop_iff_nat 1).2
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0)))
  have ha0 (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  apply mem_closed_submodule_of_weak_tendsto (continuitySubmodule T)
    (continuitySubmodule_isClosed (locallyBounded_of_weak hl hw))
    (fun n => ((a n : ℝ)⁻¹) • integratedOrbit T (a n) x) x
  · intro n
    exact (continuitySubmodule T).restrictScalars ℝ |>.smul_mem _
      (integratedOrbit_mem_continuitySubmodule hl hw (a n) x)
  · intro ℓ
    exact integratedOrbit_scalar_average hl hw x ℓ a ha ha0

end Integration
/-- Weak continuity at zero implies a strongly continuous semigroup, together
with the local bounds and orbit Bochner measurability and integrability needed
in the proof, for arbitrary real or complex Banach spaces. -/
theorem weakContinuityImpliesStrong : WeakContinuitySpec.WeakContinuityImpliesStrong.{u,v} := by
  intro 𝕜 _ E _ _ _ T hl hw'
  have hw := weakAtZero_of_right hl hw'
  have hb := locallyBounded_of_weak hl hw
  have hc := continuous_orbits_of_strongAtZero hl hb (strongAtZero_of_weak hl hw)
  exact ⟨hc, hb, real_orbit_stronglyMeasurable hl hw,
    fun x a => real_orbit_integrableOn hl hw x 0 a⟩

end ExpandedFA.Semigroups
