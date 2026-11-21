import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.Hurwitz
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.Rouche
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Hurwitz's theorem (paper.tex:2303–2308).
A positive minimum of the limit's norm on the compact circle makes the
uniform boundary error satisfy the strict Rouché estimate. The Rouché
circle theorem then supplies exact finite zero sets with equal multiplicity
counts. For the zero-free alternative, local factorization gives a small
circle around a putative finite-order zero, and the count cannot be zero.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace D12Complex.Hurwitz
open LocalZeroFactorization

/-- Uniform convergence eventually satisfies the strict Rouché estimate on
any compact set where the continuous limit does not vanish. -/
theorem eventual_strict_compact_bound
    {Ω K : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hf : ContinuousOn f Ω) (hn : ∀ z ∈ K, f z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) :
    ∀ᶠ n in atTop, ∀ z ∈ K, ‖F n z - f z‖ < ‖f z‖ := by
  obtain ⟨ε, hε, hlower⟩ := hK.exists_forall_le' (hf.mono hKΩ).norm
    (fun z hz => norm_pos_iff.mpr (hn z hz))
  have hu : TendstoUniformlyOn F f atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      (hconv.mono hKΩ)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with n hnconv
  intro z hz
  have hdist := hnconv z hz
  rw [dist_comm, dist_eq_norm] at hdist
  exact hdist.trans_le (hlower z hz)


/-- Disk zero counts for a locally uniform holomorphic limit. This stronger
form needs only an open ambient set and nonvanishing on the chosen circle. -/
theorem eventually_same_zero_count_on_circle
    (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ n, HolomorphicOn Ω (F n)) (hf : HolomorphicOn Ω f)
    (hlim : TendstoLocallyUniformlyOn F f atTop Ω)
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hclosed : Metric.closedBall c r ⊆ Ω)
    (hboundary : ∀ z ∈ Metric.sphere c r, f z ≠ 0) :
    ∀ᶠ n in atTop,
      (∀ a ∈ Metric.ball c r,
        HasFiniteOrder f a (analyticOrderNatAt f a) ∧
        HasFiniteOrder (F n) a (analyticOrderNatAt (F n) a)) ∧
      ∃ s t : Finset ℂ,
        (∀ a, a ∈ s ↔ a ∈ Metric.ball c r ∧ f a = 0) ∧
        (∀ a, a ∈ t ↔ a ∈ Metric.ball c r ∧ F n a = 0) ∧
        (∑ a ∈ s, analyticOrderNatAt f a) = ∑ a ∈ t, analyticOrderNatAt (F n) a := by
  have hcont : ContinuousOn f Ω := fun z hz =>
    (hf.2 z hz).continuousAt.continuousWithinAt
  have hstrict := eventual_strict_compact_bound (isCompact_sphere c r)
    (Metric.sphere_subset_closedBall.trans hclosed) hcont hboundary hlim
  filter_upwards [hstrict] with n hn
  exact Rouche.circle Ω c r f (F n) hr hf (hF n) hclosed hn

/-- Hurwitz zero-count stability, with the source hypotheses and convergence
on every compact subset. -/
theorem circle : Specs.D12Complex.Ch09.Hurwitz.circle_type := by
  intro Ω F f _hΩ hF hf hlim _hnonzero c r hr hclosed hboundary
  exact eventually_same_zero_count_on_circle Ω F f hF hf
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hf.1).mpr hlim)
    c r hr hclosed hboundary

/-- A zero-free sequence has a zero-free or identically zero holomorphic
limit. The second alternative applies on the whole original domain. -/
theorem zero_free_or_identically_zero
    (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hΩ : IsDomain Ω) (hF : ∀ n, HolomorphicOn Ω (F n))
    (hf : HolomorphicOn Ω f) (hlim : TendstoLocallyUniformlyOn F f atTop Ω)
    (hfree : ∀ n z, z ∈ Ω → F n z ≠ 0) :
    (∀ z ∈ Ω, f z ≠ 0) ∨ EqOn f (fun _ => 0) Ω := by
  classical
  by_cases hzero : EqOn f (fun _ => 0) Ω
  · exact Or.inr hzero
  left
  intro a ha hfa
  have hfaNear : HolomorphicNear f a := ⟨Ω, ha, hf⟩
  have hAn : AnalyticOnNhd ℂ f Ω := fun z hz =>
    (holomorphicNear_iff_analyticAt f z).mp ⟨Ω, hz, hf⟩
  have hnotgerm : ¬ ZeroGerm f a := by
    intro hgerm
    exact hzero (hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩ.2.2 ha hgerm)
  obtain ⟨m, hm, _⟩ := ((local_zero_factorization f a hfaNear).resolve_left
    (fun h => hnotgerm h.1)).2
  have hiso := eventually_nhdsWithin_iff.mp (finiteOrder_isolated f a m hm)
  have hnhds : {z | z ∈ Ω ∧ (z ≠ a → f z ≠ 0)} ∈ 𝓝 a :=
    Filter.inter_mem (hΩ.2.1.mem_nhds ha) hiso
  obtain ⟨r, hr, hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhds
  have hclosedΩ : Metric.closedBall a r ⊆ Ω := fun z hz => (hclosed hz).1
  have hboundary : ∀ z ∈ Metric.sphere a r, f z ≠ 0 := by
    intro z hz
    apply (hclosed (Metric.sphere_subset_closedBall hz)).2
    intro he
    subst z
    have heq : (0 : ℝ) = r := by simpa only [Metric.mem_sphere, dist_self] using hz
    exact hr.ne' heq.symm
  obtain ⟨n, horders, s, t, hs, ht, heq⟩ :=
    (eventually_same_zero_count_on_circle Ω F f hF hf hlim a r hr hclosedΩ hboundary).exists
  have htEmpty : t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz' := (ht z).mp hz
    exact hfree n z (hclosedΩ (Metric.ball_subset_closedBall hz'.1)) hz'.2
  have hsum : ∑ z ∈ s, analyticOrderNatAt f z = 0 := by
    simpa only [htEmpty, Finset.sum_empty] using heq
  have haS : a ∈ s := (hs a).mpr ⟨Metric.mem_ball_self hr, hfa⟩
  have horderzero : analyticOrderNatAt f a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hsum a haS
  have hpos : 0 < analyticOrderNatAt f a :=
    (finiteOrder_zero_iff f a (analyticOrderNatAt f a)
      (horders a (Metric.mem_ball_self hr)).1).mp hfa
  exact Nat.ne_of_gt hpos horderzero

/-- The zero-free alternative under exactly compact-uniform convergence. -/
theorem zero_free : Specs.D12Complex.Ch09.Hurwitz.zero_free_type := by
  intro Ω F f hΩ hF hf hlim hfree
  exact zero_free_or_identically_zero Ω F f hΩ hF hf
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hf.1).mpr hlim) hfree

end D12Complex.Hurwitz
