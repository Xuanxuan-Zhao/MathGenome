import MathGenome.Internal.LinearPDE.P201Specs.Potential.HarnackConvergence
import MathGenome.Internal.LinearPDE.P201.Potential.Harnack
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology
namespace P201.HarnackConvergence
open P201Specs

/-- The sharp bounds, retained as part of the full source corollary. -/
theorem ball_bounds : P201Specs.Harnack.BallBoundsStatement := P201.Harnack.ball_bounds

/-- Uniform positive comparison constants on compact subsets. -/
theorem compact_bounds : P201Specs.Harnack.CompactBoundsStatement := P201.Harnack.compact_bounds

/-- Subtraction preserves the actual shared notion of harmonicity. -/
theorem harmonic_sub {n : ℕ} (Ω : Domain n) {f g : Space n → ℝ}
    (hf : MeanValues.IsHarmonic Ω f) (hg : MeanValues.IsHarmonic Ω g) :
    MeanValues.IsHarmonic Ω (fun x => f x - g x) :=
  (P201.MeanValues.harmonic_bridge Ω _).mpr
    (((P201.MeanValues.harmonic_bridge Ω f).mp hf).sub
      ((P201.MeanValues.harmonic_bridge Ω g).mp hg))

/-- A bound at one point propagates to every point, by comparing u_j - u_0. -/
theorem bounded_at_every_point {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hΩ : IsConnected (Ω : Set (Space n))) (u : ℕ → Space n → ℝ)
    (hu : ∀ j, MeanValues.IsHarmonic Ω (u j))
    (hmono : ∀ x ∈ Ω, Monotone (fun j => u j x))
    (a : Space n) (ha : a ∈ Ω) (hb : BddAbove (range (fun j => u j a))) :
    ∀ x ∈ Ω, BddAbove (range (fun j => u j x)) := by
  obtain ⟨M, hM⟩ := hb
  intro x hx
  obtain ⟨c, C, hc, hC, hcomp⟩ := compact_bounds hn Ω hΩ {x}
    (isCompact_singleton) (singleton_subset_iff.mpr hx) a ha
  refine ⟨u 0 x + C * (M - u 0 a), ?_⟩
  rintro _ ⟨j, rfl⟩
  have h := (hcomp (fun y => u j y - u 0 y) (harmonic_sub Ω (hu j) (hu 0))
    (fun y hy => sub_nonneg.mpr (hmono y hy (Nat.zero_le j))) x (mem_singleton x)).2
  have hj : u j a ≤ M := hM (mem_range_self j)
  nlinarith

/-- Once the scalar limits exist, Harnack controls the entire compact-set
error by the error at one reference point. -/
theorem uniform_of_pointwise {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hΩ : IsConnected (Ω : Set (Space n))) (u : ℕ → Space n → ℝ)
    (hu : ∀ j, MeanValues.IsHarmonic Ω (u j))
    (hmono : ∀ x ∈ Ω, Monotone (fun j => u j x))
    (a : Space n) (ha : a ∈ Ω) (f : Space n → ℝ)
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => u j x) atTop (𝓝 (f x))) :
    ∀ K : Set (Space n), IsCompact K → K ⊆ (Ω : Set _) →
      TendstoUniformlyOn u f atTop K := by
  intro K hK hKΩ
  obtain ⟨c, C, hc, hC, hcomp⟩ := compact_bounds hn Ω hΩ K hK hKΩ a ha
  have hle : ∀ x ∈ Ω, ∀ j, u j x ≤ f x := by
    intro x hx j
    exact (hmono x hx).ge_of_tendsto (hlim x hx) j
  have herr : ∀ j, ∀ x ∈ K, f x - u j x ≤ C * (f a - u j a) := by
    intro j x hx
    apply le_of_tendsto ((hlim x (hKΩ hx)).sub_const (u j x))
    filter_upwards [eventually_ge_atTop j] with m hm
    have h := (hcomp (fun y => u m y - u j y) (harmonic_sub Ω (hu m) (hu j))
      (fun y hy => sub_nonneg.mpr (hmono y hy hm)) x hx).2
    exact h.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right (hle a ha m) _) hC.le)
  have hscalar : Tendsto (fun j => C * (f a - u j a)) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.sub (hlim a ha)).const_mul C using 1 <;> simp
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hscalar.eventually (gt_mem_nhds hε)] with j hj x hx
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hle x (hKΩ hx) j))]
  exact (herr j x hx).trans_lt hj

/-- The locally uniform limit retains the ball mean identities. Monotone
convergence for the Bochner integral applies also to signed integrands. -/
theorem harmonic_of_monotone_uniform_limit {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (u : ℕ → Space n → ℝ) (hu : ∀ j, MeanValues.IsHarmonic Ω (u j))
    (hmono : ∀ x ∈ Ω, Monotone (fun j => u j x)) (f : Space n → ℝ)
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => u j x) atTop (𝓝 (f x)))
    (hunif : ∀ K : Set (Space n), IsCompact K → K ⊆ (Ω : Set _) →
      TendstoUniformlyOn u f atTop K) : MeanValues.IsHarmonic Ω f := by
  have hlocal : TendstoLocallyUniformlyOn u f atTop (Ω : Set _) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact Ω.isOpen).mpr
      (fun K hKΩ hK => hunif K hK hKΩ)
  have hf : ContinuousOn f Ω := hlocal.continuousOn
    (Eventually.of_forall (fun j => (hu j).1.continuousOn)).frequently
  apply (P201.MeanValues.ball_converse hn Ω f hf ?_).2
  intro a r hr hb
  have hint : ∀ j, IntegrableOn (u j) (ball a r) := fun j =>
    (((hu j).1.continuousOn.mono hb).integrableOn_compact
      (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have hfint : IntegrableOn f (ball a r) :=
    ((hf.mono hb).integrableOn_compact (isCompact_closedBall a r)).mono_set
      ball_subset_closedBall
  have hae : ∀ᵐ x ∂volume.restrict (ball a r), x ∈ (Ω : Set _) := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    exact hb (ball_subset_closedBall hx)
  have hi : Tendsto (fun j => ∫ x in ball a r, u j x) atTop
      (𝓝 (∫ x in ball a r, f x)) :=
    integral_tendsto_of_tendsto_of_monotone hint hfint
      (hae.mono fun x hx => hmono x hx) (hae.mono fun x hx => hlim x hx)
  have hav : Tendsto (fun j => ballAverage (u j) a r) atTop
      (𝓝 (ballAverage f a r)) := tendsto_const_nhds.smul hi
  have hcenter : Tendsto (fun j => u j a) atTop (𝓝 (ballAverage f a r)) := by
    convert hav using 1
    funext j
    exact (P201.MeanValues.mean_values hn Ω (u j) (hu j) a r hr hb).2
  exact tendsto_nhds_unique (hlim a (hb (mem_closedBall_self hr.le))) hcenter

/-- Boundedness at one point yields a finite harmonic limit, with uniform
convergence on every compact subset of the domain. -/
theorem bounded_convergence : P201Specs.HarnackConvergence.BoundedConvergenceStatement := by
  intro n hn Ω hΩ u hu hmono a ha hb
  have hbAll := bounded_at_every_point hn Ω hΩ u hu hmono a ha hb
  let f : Space n → ℝ := fun x => ⨆ j, u j x
  have hlim : ∀ x ∈ Ω, Tendsto (fun j => u j x) atTop (𝓝 (f x)) :=
    fun x hx => tendsto_atTop_ciSup (hmono x hx) (hbAll x hx)
  have hunif := uniform_of_pointwise hn Ω hΩ u hu hmono a ha f hlim
  exact ⟨f, harmonic_of_monotone_uniform_limit hn Ω u hu hmono f hlim hunif, hunif⟩

/-- Harnack's monotone sequence alternative, without a sign restriction on
any sequence member, and in every dimension n ≥ 1. -/
theorem monotone_alternative : P201Specs.HarnackConvergence.MonotoneAlternativeStatement := by
  classical
  intro n hn Ω hΩ u hu hmono
  by_cases hb : ∃ a ∈ Ω, BddAbove (range (fun j => u j a))
  · obtain ⟨a, ha, hb⟩ := hb
    exact Or.inr (bounded_convergence hn Ω hΩ u hu hmono a ha hb)
  · left
    intro x hx
    exact tendsto_atTop_atTop_of_monotone' (hmono x hx)
      (fun h => hb ⟨x, hx, h⟩)

end P201.HarnackConvergence
