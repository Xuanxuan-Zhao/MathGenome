import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.UnivalentLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.Hurwitz
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Limits of univalent functions, paper.tex:2311–2316.
For a collision f(a)=f(b), a≠b, the translated approximants
F n - F n a are zero-free on a small disk about b missing a.
Hurwitz forces f-f(a) to vanish on that disk; the identity theorem
then makes f constant throughout the original connected domain.
The final example proves that this alternative is necessary.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.UnivalentLimits

/-- The source theorem on every plane domain, with compact-uniform convergence. -/
theorem injective_or_constant :
    Specs.D12Complex.Ch09.UnivalentLimits.injective_or_constant_type := by
  intro Ω F f hΩ hF hf hlim hinj
  classical
  by_cases hc : ∃ c : ℂ, Set.EqOn f (fun _ => c) Ω
  · exact Or.inr hc
  left
  intro a ha b hb hab
  by_contra hne
  have hopen : IsOpen (Ω \ {a}) := hΩ.2.1.sdiff isClosed_singleton
  have hb' : b ∈ Ω \ {a} := ⟨hb, by simpa only [Set.mem_singleton_iff] using Ne.symm hne⟩
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hopen b hb'
  have hsub : Metric.ball b r ⊆ Ω := fun z hz => (hrs hz).1
  have havoid : ∀ z ∈ Metric.ball b r, z ≠ a := fun z hz => (hrs hz).2
  have hdomain : IsDomain (Metric.ball b r) :=
    ⟨⟨b, Metric.mem_ball_self hr⟩, Metric.isOpen_ball, Metric.isPreconnected_ball⟩
  let G : ℕ → ℂ → ℂ := fun n z => F n z - F n a
  let g : ℂ → ℂ := fun z => f z - f a
  have hgΩ : HolomorphicOn Ω g :=
    ⟨hf.1, fun z hz => (hf.2 z hz).sub_const (f a)⟩
  have hG : ∀ n, HolomorphicOn (Metric.ball b r) (G n) :=
    fun n => ⟨Metric.isOpen_ball, fun z hz => ((hF n).2 z (hsub hz)).sub_const (F n a)⟩
  have hg : HolomorphicOn (Metric.ball b r) g :=
    ⟨Metric.isOpen_ball, fun z hz => hgΩ.2 z (hsub hz)⟩
  have hloc : TendstoLocallyUniformlyOn F f atTop Ω :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hf.1).mpr hlim
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => F n a)
      (fun _ => f a) atTop Ω :=
    ((hloc.tendsto_at ha).tendstoUniformlyOn_const Ω).tendstoLocallyUniformlyOn
  have hGlim : TendstoLocallyUniformlyOn G g atTop (Metric.ball b r) :=
    (hloc.sub hconst).mono hsub
  have hfree : ∀ n z, z ∈ Metric.ball b r → G n z ≠ 0 := by
    intro n z hz he
    exact havoid z hz (hinj n (hsub hz) ha (sub_eq_zero.mp he))
  rcases Hurwitz.zero_free_or_identically_zero (Metric.ball b r) G g hdomain
      hG hg hGlim hfree with hn | hz
  · exact hn b (Metric.mem_ball_self hr) (sub_eq_zero.mpr hab.symm)
  have hgerm : g =ᶠ[𝓝 b] (fun _ => 0) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds b hr) fun z hz' => hz hz'
  have hAn : AnalyticOnNhd ℂ g Ω := fun z hz' =>
    (LocalZeroFactorization.holomorphicNear_iff_analyticAt g z).mp ⟨Ω, hz', hgΩ⟩
  have hglobal : EqOn g (fun _ => 0) Ω :=
    hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩ.2.2 hb hgerm
  exact hc ⟨f a, fun z hz' => sub_eq_zero.mp (hglobal hz')⟩

/-- The injective holomorphic functions z/(n+1) tend uniformly to zero on
any disk; their constant limit is not injective on a positive-radius disk. -/
theorem scaling_example :
    Specs.D12Complex.Ch09.UnivalentLimits.scaling_example_type := by
  intro a r hr
  have huniform : TendstoUniformlyOn (fun (n : ℕ) z => z / (↑(n+1):ℂ))
      (fun _ => (0 : ℂ)) atTop (Metric.ball a r) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((‖a‖ + r) / ε)
    filter_upwards [eventually_ge_atTop N] with n hn
    intro z hz
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hzbound : ‖z‖ < ‖a‖ + r := by
      calc ‖z‖ = ‖z - a + a‖ := by rw [sub_add_cancel]
           _ ≤ ‖z - a‖ + ‖a‖ := norm_add_le _ _
           _ < r + ‖a‖ := by
             have h : ‖z - a‖ < r := by simpa [dist_eq_norm] using hz
             linarith
           _ = ‖a‖ + r := add_comm _ _
    have hN' : (‖a‖ + r) < ε * ((n : ℝ) + 1) := by
      have h := (div_lt_iff₀ hε).mp hN
      have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    simp only [dist_eq_norm, zero_sub, norm_neg, norm_div]
    have hnorm : ‖(↑(n+1):ℂ)‖ = (n : ℝ) + 1 := by norm_cast
    rw [hnorm]
    exact (div_lt_iff₀ hn0).mpr (hzbound.trans hN')
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · refine ⟨Metric.isOpen_ball, ?_⟩
      intro z hz
      exact differentiableAt_id.div_const _
    · intro z hz w hw he
      have hn : (↑(n+1):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      exact (div_left_inj' hn).mp he
  · intro K hK _hcompact
    exact huniform.mono hK
  · exact ⟨0, fun _ _ => rfl⟩
  · intro hinj
    have hp : a + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball a r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      linarith
    have heq : a = a + ((r / 2 : ℝ) : ℂ) :=
      hinj (Metric.mem_ball_self hr) hp rfl
    have hzero : ((r / 2 : ℝ) : ℂ) = 0 :=
      add_left_cancel (show a + ((r / 2 : ℝ) : ℂ) = a + 0 by simpa using heq.symm)
    have : r / 2 = 0 := by exact_mod_cast hzero
    linarith

end D12Complex.UnivalentLimits
