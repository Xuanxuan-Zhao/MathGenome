import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.KoopmanGroups
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.StoneTheorem
import Mathlib.MeasureTheory.Function.ContinuousMapDense

noncomputable section
open MeasureTheory Filter Topology
namespace ExpandedFA.Models.KoopmanGroups
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- Pointwise flow laws also hold as equalities of maps. -/
theorem maps_add (Φ : MeasurePreservingFlow X μ) (t s : ℝ) :
    Φ.maps (t + s) = Φ.maps t ∘ Φ.maps s := funext (Φ.add_time t s)

@[simp] theorem pullback_zero (Φ : MeasurePreservingFlow X μ) (f : Lp ℂ 2 μ) :
    pullback Φ 0 f = f := by
  have h : Φ.maps 0 = id := funext Φ.zero_time
  simp [pullback, Lp.compMeasurePreservingₗᵢ, Lp.compMeasurePreservingₗ, h]

/-- Pullbacks reverse composition; real times commute, giving the group law. -/
theorem pullback_add (Φ : MeasurePreservingFlow X μ) (t s : ℝ) (f : Lp ℂ 2 μ) :
    pullback Φ (t + s) f = pullback Φ t (pullback Φ s f) := by
  change Lp.compMeasurePreserving _ _ f =
    Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
  simpa only [← maps_add, add_comm s t] using
    Lp.compMeasurePreserving_comp_apply f (Φ.measure_preserving s) (Φ.measure_preserving t)

@[simp] theorem pullback_neg_cancel (Φ : MeasurePreservingFlow X μ) (t : ℝ)
    (f : Lp ℂ 2 μ) : pullback Φ (-t) (pullback Φ t f) = f := by
  rw [← pullback_add, neg_add_cancel, pullback_zero]

/-- Inverse time makes the norm-preserving linear pullback surjective. -/
def pullbackUnitary (Φ : MeasurePreservingFlow X μ) (t : ℝ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearEquiv :=
    { (pullback Φ t).toLinearMap with
      invFun := pullback Φ (-t)
      left_inv := pullback_neg_cancel Φ t
      right_inv := by intro f; simpa using pullback_neg_cancel Φ (-t) f }
  norm_map' := (pullback Φ t).norm_map

/-- This construction requires the independent strong-continuity hypothesis. -/
def unitaryGroup (Φ : MeasurePreservingFlow X μ) (hΦ : StronglyContinuous Φ) :
    Semigroups.Stone.UnitaryGroup (Lp ℂ 2 μ) where
  operators := pullbackUnitary Φ
  at_zero := pullback_zero Φ
  add_time := pullback_add Φ
  continuous_orbit := hΦ

/-- Measure preservation, inverse time, and strong continuity imply Stone's theorem. -/
theorem koopman_group : Spec.KoopmanTheorem.{u} := by
  intro X _ μ Φ hΦ
  let U := unitaryGroup Φ hΦ
  exact ⟨U, (fun _ _ => rfl), Semigroups.Stone.stone_forward (Lp ℂ 2 μ) U⟩

/-- Isometries allow extension of continuous orbits from a dense range. -/
theorem stronglyContinuous_of_denseRange {D : Type*} (j : D → Lp ℂ 2 μ)
    (hj : DenseRange j) (Φ : MeasurePreservingFlow X μ)
    (hc : ∀ d, Continuous (fun t : ℝ => pullback Φ t (j d))) : StronglyContinuous Φ := by
  intro f
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d, hd⟩ := hj.exists_dist_lt f (show 0 < ε / 3 by positivity)
  have ht := Metric.tendsto_nhds.mp ((hc d).tendsto a) (ε / 3) (by positivity)
  filter_upwards [ht] with t ht
  have hb := dist_triangle4 (pullback Φ t f) (pullback Φ t (j d))
    (pullback Φ a (j d)) (pullback Φ a f)
  rw [(pullback Φ t).isometry.dist_eq, (pullback Φ a).isometry.dist_eq,
    dist_comm (j d) f] at hb
  linarith

section Compact
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
variable [IsFiniteMeasure μ]

/-- Compatibility of continuous representatives and quotient-space pullbacks. -/
theorem pullback_toLp (Φ : MeasurePreservingFlow X μ) (t : ℝ) (c : C(X, ℂ))
    (h : Continuous (Φ.maps t)) :
    pullback Φ t (ContinuousMap.toLp 2 μ ℂ c) =
      ContinuousMap.toLp 2 μ ℂ (c.comp ⟨Φ.maps t, h⟩) := by
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving _ (Φ.measure_preserving t)).trans
    (((Φ.measure_preserving t).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℂ) c)).trans
        (ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℂ) (c.comp ⟨Φ.maps t, h⟩)).symm)

/-- Joint continuity on a compact space gives uniform-norm continuous orbits,
which remain continuous after the continuous map into L². -/
theorem continuous_pullback_toLp (Φ : MeasurePreservingFlow X μ)
    (hΦ : Continuous (fun p : ℝ × X => Φ.maps p.1 p.2)) (c : C(X, ℂ)) :
    Continuous (fun t : ℝ => pullback Φ t (ContinuousMap.toLp 2 μ ℂ c)) := by
  have hc (t : ℝ) : Continuous (Φ.maps t) :=
    hΦ.comp (continuous_const.prodMk continuous_id)
  let ψ : ℝ → C(X, ℂ) := fun t => c.comp ⟨Φ.maps t, hc t⟩
  have hψ : Continuous ψ :=
    ContinuousMap.continuous_of_continuous_uncurry ψ (c.continuous.comp hΦ)
  have hLp := (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).continuous.comp hψ
  exact hLp.congr (fun t => (pullback_toLp Φ t c (hc t)).symm)

end Compact

/-- The regular-measure density theorem completes the compact-flow argument. -/
theorem compact_strong_continuity : Spec.CompactStrongContinuity.{u} := by
  intro X _ _ _ _ _ μ _ _ Φ hΦ
  apply stronglyContinuous_of_denseRange (ContinuousMap.toLp 2 μ ℂ)
    (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)) Φ
  exact continuous_pullback_toLp Φ hΦ

/-- Every continuous compact measure-preserving flow therefore has its Stone generator. -/
theorem compact_koopman_group : Spec.CompactKoopmanTheorem.{u} := by
  intro X _ _ _ _ _ μ _ _ Φ hΦ
  exact koopman_group X μ Φ (compact_strong_continuity X μ Φ hΦ)

@[simp] theorem realPullback_zero (Φ : MeasurePreservingFlow X μ) (f : Lp ℝ 2 μ) :
    realPullback Φ 0 f = f := by
  have h : Φ.maps 0 = id := funext Φ.zero_time
  simp [realPullback, Lp.compMeasurePreservingₗᵢ, Lp.compMeasurePreservingₗ, h]

/-- Pullbacks reverse composition; real times commute, giving the group law. -/
theorem realPullback_add (Φ : MeasurePreservingFlow X μ) (t s : ℝ) (f : Lp ℝ 2 μ) :
    realPullback Φ (t + s) f = realPullback Φ t (realPullback Φ s f) := by
  change Lp.compMeasurePreserving _ _ f =
    Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
  simpa only [← maps_add, add_comm s t] using
    Lp.compMeasurePreserving_comp_apply f (Φ.measure_preserving s) (Φ.measure_preserving t)

@[simp] theorem realPullback_neg_cancel (Φ : MeasurePreservingFlow X μ) (t : ℝ)
    (f : Lp ℝ 2 μ) : realPullback Φ (-t) (realPullback Φ t f) = f := by
  rw [← realPullback_add, neg_add_cancel, realPullback_zero]

/-- Inverse time makes the norm-preserving linear pullback surjective. -/
def pullbackOrthogonal (Φ : MeasurePreservingFlow X μ) (t : ℝ) : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ where
  toLinearEquiv :=
    { (realPullback Φ t).toLinearMap with
      invFun := realPullback Φ (-t)
      left_inv := realPullback_neg_cancel Φ t
      right_inv := by intro f; simpa using realPullback_neg_cancel Φ (-t) f }
  norm_map' := (realPullback Φ t).norm_map

/-- A continuous real pullback group on genuine real-valued L². -/
def orthogonalGroup (Φ : MeasurePreservingFlow X μ) (hΦ : RealStronglyContinuous Φ) :
    OrthogonalGroup (Lp ℝ 2 μ) where
  operators := pullbackOrthogonal Φ
  at_zero := realPullback_zero Φ
  add_time := realPullback_add Φ
  continuous_orbit := hΦ

/-- The real pullbacks are surjective real-linear isometries at every time. -/
theorem real_koopman_group : Spec.RealKoopmanGroup.{u} := by
  intro X _ μ Φ hΦ
  exact ⟨orthogonalGroup Φ hΦ, fun _ _ => rfl⟩

/-- Isometries allow extension of continuous orbits from a dense range. -/
theorem realStronglyContinuous_of_denseRange {D : Type*} (j : D → Lp ℝ 2 μ)
    (hj : DenseRange j) (Φ : MeasurePreservingFlow X μ)
    (hc : ∀ d, Continuous (fun t : ℝ => realPullback Φ t (j d))) : RealStronglyContinuous Φ := by
  intro f
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d, hd⟩ := hj.exists_dist_lt f (show 0 < ε / 3 by positivity)
  have ht := Metric.tendsto_nhds.mp ((hc d).tendsto a) (ε / 3) (by positivity)
  filter_upwards [ht] with t ht
  have hb := dist_triangle4 (realPullback Φ t f) (realPullback Φ t (j d))
    (realPullback Φ a (j d)) (realPullback Φ a f)
  rw [(realPullback Φ t).isometry.dist_eq, (realPullback Φ a).isometry.dist_eq,
    dist_comm (j d) f] at hb
  linarith

section RealCompact
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
variable [IsFiniteMeasure μ]

/-- Compatibility of continuous representatives and quotient-space pullbacks. -/
theorem realPullback_toLp (Φ : MeasurePreservingFlow X μ) (t : ℝ) (c : C(X, ℝ))
    (h : Continuous (Φ.maps t)) :
    realPullback Φ t (ContinuousMap.toLp 2 μ ℝ c) =
      ContinuousMap.toLp 2 μ ℝ (c.comp ⟨Φ.maps t, h⟩) := by
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving _ (Φ.measure_preserving t)).trans
    (((Φ.measure_preserving t).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℝ) c)).trans
        (ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℝ) (c.comp ⟨Φ.maps t, h⟩)).symm)

/-- Joint continuity on a compact space gives uniform-norm continuous orbits,
which remain continuous after the continuous map into L². -/
theorem continuous_realPullback_toLp (Φ : MeasurePreservingFlow X μ)
    (hΦ : Continuous (fun p : ℝ × X => Φ.maps p.1 p.2)) (c : C(X, ℝ)) :
    Continuous (fun t : ℝ => realPullback Φ t (ContinuousMap.toLp 2 μ ℝ c)) := by
  have hc (t : ℝ) : Continuous (Φ.maps t) :=
    hΦ.comp (continuous_const.prodMk continuous_id)
  let ψ : ℝ → C(X, ℝ) := fun t => c.comp ⟨Φ.maps t, hc t⟩
  have hψ : Continuous ψ :=
    ContinuousMap.continuous_of_continuous_uncurry ψ (c.continuous.comp hΦ)
  have hLp := (ContinuousMap.toLp 2 μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ).continuous.comp hψ
  exact hLp.congr (fun t => (realPullback_toLp Φ t c (hc t)).symm)

end RealCompact

/-- The regular-measure density theorem completes the compact-flow argument. -/
theorem compact_real_strong_continuity : Spec.CompactRealStrongContinuity.{u} := by
  intro X _ _ _ _ _ μ _ _ Φ hΦ
  apply realStronglyContinuous_of_denseRange (ContinuousMap.toLp 2 μ ℝ)
    (ContinuousMap.toLp_denseRange ℝ μ ℝ (by norm_num)) Φ
  exact continuous_realPullback_toLp Φ hΦ

/-- Compact continuous flows give strongly continuous orthogonal groups. -/
theorem compact_real_koopman_group : Spec.CompactRealKoopmanGroup.{u} := by
  intro X _ _ _ _ _ μ _ _ Φ hΦ
  exact real_koopman_group X μ Φ (compact_real_strong_continuity X μ Φ hΦ)

end ExpandedFA.Models.KoopmanGroups
