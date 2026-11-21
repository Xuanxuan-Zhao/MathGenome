import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.ExtremalUnivalent
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch12.BoundedUnivalent
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.Montel
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.HolomorphicLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.UnivalentLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.StrongModulus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.IsLUB

/-! The extremal construction from D12.12.03 up to, and including,
attainment of the positive finite derivative supremum. Cauchy bounds the
class, rotations align its derivatives, and Montel supplies a limit.
Nonzero derivative excludes the constant alternative in the univalent-limit
theorem and the boundary equality case in the maximum principle. -/

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.ExtremalUnivalent

/-- The entire normalized univalent class, with conditions only on Ω. -/
def normalizedFamily (Ω : Set ℂ) (z₀ : ℂ) : Set (ℂ → ℂ) :=
  {f | HolomorphicOn Ω f ∧ Set.InjOn f Ω ∧
    Set.MapsTo f Ω (Metric.ball 0 1) ∧ f z₀ = 0}

/-- The actual norms of the derivatives in the class. -/
def derivativeNorms (Ω : Set ℂ) (z₀ : ℂ) : Set ℝ :=
  (fun f : ℂ → ℂ => ‖deriv f z₀‖) '' normalizedFamily Ω z₀

/-- The derivative extremum. Its finiteness and positivity are proved below. -/
def derivativeSupremum (Ω : Set ℂ) (z₀ : ℂ) : ℝ :=
  sSup (derivativeNorms Ω z₀)

/-- Cauchy's estimate on a closed disk inside the domain gives a common bound. -/
theorem derivativeNorms_bddAbove {Ω : Set ℂ} {z₀ : ℂ}
    (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω) : BddAbove (derivativeNorms Ω z₀) := by
  obtain ⟨r, hr, hclosed⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall z₀ r ⊆ Ω :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz₀)
  refine ⟨1 / r, ?_⟩
  rintro t ⟨f, hf, rfl⟩
  have hM : ∀ w ∈ Metric.sphere z₀ r, ‖f w‖ ≤ (1 : ℝ) := by
    intro w hw
    have hm := hf.2.2.1 (hclosed (Metric.sphere_subset_closedBall hw))
    have hm' : ‖f w‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hm
    exact hm'.le
  have he := DiskCauchyDerivatives.disk_cauchy_estimate
    z₀ r Ω f 1 hr hf.1 hclosed hM 1
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul,
    pow_one] using he
/-- A unit-modulus rotation makes the derivative real and nonnegative,
while preserving the full normalized univalent class. -/
theorem phase_normalize {Ω : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {f : ℂ → ℂ} (hf : f ∈ normalizedFamily Ω z₀) :
    ∃ g : ℂ → ℂ, g ∈ normalizedFamily Ω z₀ ∧
      deriv g z₀ = (‖deriv f z₀‖ : ℂ) := by
  by_cases hd : deriv f z₀ = 0
  · exact ⟨f, hf, by simp [hd]⟩
  let c : ℂ := (‖deriv f z₀‖ : ℂ) / deriv f z₀
  have hc : ‖c‖ = 1 := by
    simp [c, Complex.norm_real, hd]
  have hcn : c ≠ 0 := by
    intro hzero
    simp [hzero] at hc
  refine ⟨fun z => c * f z, ?_, ?_⟩
  · refine ⟨⟨hf.1.1, fun z hz => (hf.1.2 z hz).const_mul c⟩,
      ?_, ?_, ?_⟩
    · intro z hz w hw heq
      exact hf.2.1 hz hw (mul_left_cancel₀ hcn heq)
    · intro z hz
      have hnorm : ‖f z‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hf.2.2.1 hz
      simpa only [Metric.mem_ball, dist_zero_right, norm_mul, hc, one_mul] using hnorm
    · simp [hf.2.2.2]
  · calc
      deriv (fun z => c * f z) z₀ = c * deriv f z₀ :=
        ((hf.1.2 z₀ hz₀).hasDerivAt.const_mul c).deriv
      _ = (‖deriv f z₀‖ : ℂ) := div_mul_cancel₀ _ hd

/-- Choose members approaching the real supremum and rotate their derivatives
without changing their norms. -/
theorem approximating_sequence {Ω : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hF : (normalizedFamily Ω z₀).Nonempty)
    (hbd : BddAbove (derivativeNorms Ω z₀)) :
    ∃ f : ℕ → ℂ → ℂ, (∀ n, f n ∈ normalizedFamily Ω z₀) ∧
      Tendsto (fun n => deriv (f n) z₀) atTop
        (𝓝 (derivativeSupremum Ω z₀ : ℂ)) := by
  have hn : (derivativeNorms Ω z₀).Nonempty := hF.image _
  obtain ⟨u, _hu, hlim, hmem⟩ := exists_seq_tendsto_sSup hn hbd
  have hex : ∀ n, ∃ f : ℂ → ℂ, f ∈ normalizedFamily Ω z₀ ∧ ‖deriv f z₀‖ = u n := by
    intro n
    exact hmem n
  choose f hf heq using hex
  choose g hg hder using fun n => phase_normalize hz₀ (hf n)
  refine ⟨g, hg, ?_⟩
  have hc : Tendsto (fun n => (u n : ℂ)) atTop
      (𝓝 (derivativeSupremum Ω z₀ : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hlim
  convert hc using 1
  ext n
  rw [hder n, heq n]
/-- Montel's limit has the prescribed nonzero derivative. This excludes the
constant alternative and, by the maximum principle, all unit-circle values. -/
lemma normalizedFamily_limit (Ω : Set ℂ) (z₀ : ℂ) (hΩ : IsDomain Ω) (hz₀ : z₀ ∈ Ω)
    (F : ℕ → ℂ → ℂ) (hF : ∀ n, F n ∈ normalizedFamily Ω z₀)
    (s : ℝ) (hs : 0 < s)
    (hd : Tendsto (fun n => deriv (F n) z₀) atTop (𝓝 (s : ℂ))) :
    ∃ f ∈ normalizedFamily Ω z₀, deriv f z₀ = (s : ℂ) := by
  have hfamily : ∀ f ∈ normalizedFamily Ω z₀, HolomorphicOn Ω f :=
    fun f hf => hf.1
  have hb : HolomorphicCompactness.LocallyBounded Ω (normalizedFamily Ω z₀) := by
    intro K _ hK
    refine ⟨1, zero_le_one, ?_⟩
    intro f hf z hz
    exact (show ‖f z‖ < 1 by simpa using hf.2.2.1 (hK hz)).le
  have hn := (Ch11.Montel.locallyBounded_iff_finiteNormal Ω (normalizedFamily Ω z₀)
    hΩ.2.1 hfamily).mp hb
  obtain ⟨φ, f, hφ, hf, hlim⟩ := hn F hF
  have hdz : Tendsto (fun n => deriv (F (φ n)) z₀) atTop (𝓝 (deriv f z₀)) := by
    simpa only [iteratedDeriv_one] using
      (HolomorphicLimits.iteratedDeriv_locallyUniform_limit Ω (fun n => F (φ n)) f
        hΩ.2.1 (fun n => (hF (φ n)).1) hlim 1).tendsto_at hz₀
  have hder : deriv f z₀ = (s : ℂ) :=
    tendsto_nhds_unique hdz (hd.comp hφ.tendsto_atTop)
  have hfzero : f z₀ = 0 := by
    apply tendsto_nhds_unique (hlim.tendsto_at hz₀)
    have heq : (fun n => F (φ n) z₀) = (fun _ : ℕ => (0 : ℂ)) := by
      funext n
      exact (hF (φ n)).2.2.2
    rw [heq]
    exact tendsto_const_nhds
  have hnonconstant : ¬ ∃ c : ℂ, Set.EqOn f (fun _ => c) Ω := by
    rintro ⟨c, hc⟩
    have hlocal : f =ᶠ[𝓝 z₀] (fun _ => c) :=
      Filter.eventually_of_mem (hΩ.2.1.mem_nhds hz₀) (fun z hz => hc hz)
    have hzero : deriv f z₀ = 0 := by rw [hlocal.deriv_eq]; simp
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    exact hs0 (hder.symm.trans hzero)
  have hinj : Set.InjOn f Ω :=
    (UnivalentLimits.injective_or_constant Ω (fun n => F (φ n)) f hΩ
      (fun n => (hF (φ n)).1) hf
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ.2.1).mp hlim)
      (fun n => (hF (φ n)).2.1)).resolve_right hnonconstant
  have hbound : ∀ z ∈ Ω, ‖f z‖ ≤ 1 := by
    intro z hz
    apply le_of_tendsto (hlim.tendsto_at hz).norm
    exact Eventually.of_forall fun n =>
      (show ‖F (φ n) z‖ < 1 by simpa using (hF (φ n)).2.2.1 hz).le
  have hmaps : Set.MapsTo f Ω (Metric.ball 0 1) := by
    intro a ha
    have hlt : ‖f a‖ < 1 := by
      by_contra hnot
      have heq : ‖f a‖ = 1 := le_antisymm (hbound a ha) (not_lt.mp hnot)
      have hmax : IsLocalMaxOn (fun z => ‖f z‖) Ω a := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hbound z hz).trans_eq heq.symm
      have hc := StrongModulus.constant_of_local_maximum_modulus Ω f a hΩ hf ha hmax
      exact hnonconstant ⟨f a, fun z hz => hc z hz⟩
    simpa using hlt
  exact ⟨f, ⟨hf, hinj, hmaps, hfzero⟩, hder⟩
/-- The derivative supremum over the full normalized univalent family is
positive, finite, and attained with positive real derivative. -/
theorem extremal_univalent :
    Specs.D12Complex.Ch12.ExtremalUnivalent.extremal_univalent_type := by
  intro Ω hΩ hproper hroot z₀ hz₀
  obtain ⟨g, hg, hginj, hgmaps, hgzero, t, ht, hgd⟩ :=
    BoundedUnivalent.bounded_univalent Ω hΩ hproper hroot z₀ hz₀
  have hgf : g ∈ normalizedFamily Ω z₀ := ⟨hg, hginj, hgmaps, hgzero⟩
  have hn : (derivativeNorms Ω z₀).Nonempty := ⟨_, g, hgf, rfl⟩
  have hb := derivativeNorms_bddAbove hΩ.2.1 hz₀
  have hnorm : ‖deriv g z₀‖ = t := by
    rw [hgd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hs : 0 < derivativeSupremum Ω z₀ :=
    (ht.trans_eq hnorm.symm).trans_le (le_csSup hb ⟨g, hgf, rfl⟩)
  obtain ⟨F, hF, hFd⟩ := approximating_sequence hz₀ ⟨g, hgf⟩ hb
  obtain ⟨f, hf, hfd⟩ := normalizedFamily_limit Ω z₀ hΩ hz₀ F hF
    (derivativeSupremum Ω z₀) hs hFd
  exact ⟨hn, hb, hs, f, hf, hfd⟩

end D12Complex.ExtremalUnivalent
