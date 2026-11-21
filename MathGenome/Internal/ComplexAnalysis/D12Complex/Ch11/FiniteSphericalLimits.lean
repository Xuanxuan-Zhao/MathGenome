import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.FiniteSphericalLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.SphericalLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.Hurwitz
import Mathlib.Analysis.Normed.Module.Connected

/-!
A finite holomorphic sequence cannot acquire an isolated pole under locally
uniform chordal convergence. In the reciprocal chart, Hurwitz turns any
infinite value into a whole infinite germ; the sphere identity theorem then
propagates that germ across the connected domain. In the other case the finite
chart gives holomorphy and ordinary uniform convergence on every compact set.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D12Complex.FiniteSphericalLimits

/-- A finite holomorphic function is a holomorphic map into the sphere in
the canonical finite coordinate. -/
lemma finite_holomorphic_lift {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) :
    PlaneSphereHolomorphicOn Ω (fun z => sphereFinite (f z)) := by
  refine ⟨hf.1, fun a ha => ?_⟩
  apply planeSphereHolomorphicAt_of_finite_germ
  · exact ⟨Ω, ha, hf⟩
  · exact Eventually.of_forall fun z => OnePoint.coe_ne_infty (f z)

/-- Hurwitz in the reciprocal coordinate turns an infinite value into an
infinite germ, because the approximating functions take only finite values. -/
lemma infinite_value_has_infinite_germ
    {Ω : Set ℂ} {f : ℕ → ℂ → ℂ} {F : ℂ → RiemannSphere}
    (hΩ : IsOpen Ω)
    (hfSphere : ∀ n, PlaneSphereHolomorphicOn Ω (fun z => sphereFinite (f n z)))
    (hF : PlaneSphereHolomorphicOn Ω F)
    (hlim : SphericalLimits.SphericalLocallyUniformOn
      (fun n z => sphereFinite (f n z)) F Ω)
    {a : ℂ} (ha : a ∈ Ω) (hinf : F a = sphereInfty) :
    ∀ᶠ z in 𝓝 a, F z = sphereInfty := by
  have hc : F a ∈ (sphereCoordinate .reciprocal).source := by
    rw [hinf]
    exact OnePoint.infty_ne_coe 0
  obtain ⟨r, hr, hclosed, himage, ⟨M, hM, hbound, hevent⟩, hord⟩ :=
    SphericalLimits.chart_neighborhood_convergence Ω
      (fun n z => sphereFinite (f n z)) F hΩ hfSphere hlim a ha .reciprocal hc
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hballDomain : IsDomain (ball a r) :=
    ⟨⟨a, mem_ball_self hr⟩, isOpen_ball, isPreconnected_ball⟩
  let g : ℕ → ℂ → ℂ := fun n z => infinityCoordinate (sphereFinite (f (n + N) z))
  let G : ℂ → ℂ := fun z => infinityCoordinate (F z)
  have hg : ∀ n, HolomorphicOn (ball a r) (g n) := by
    intro n
    exact (hN (n + N) (Nat.le_add_left N n)).1
  have hG : HolomorphicOn (ball a r) G := by
    refine ⟨isOpen_ball, fun z hz => ?_⟩
    exact ((planeSphereHolomorphicAt_iff_chart F z .reciprocal
      (himage (ball_subset_closedBall hz))).mp
        (hF.2 z (hclosed (ball_subset_closedBall hz)))).2.differentiableAt
  have hconv : TendstoLocallyUniformlyOn g G atTop (ball a r) := by
    exact ((hord.seq_tendstoUniformlyOn (fun n => n + N)
      (tendsto_add_atTop_nat N)).tendstoLocallyUniformlyOn).mono ball_subset_closedBall
  have hfree : ∀ n z, z ∈ ball a r → g n z ≠ 0 := by
    intro n z hz hzero
    have hp := (hN (n + N) (Nat.le_add_left N n)).2 z (ball_subset_closedBall hz)
    have hi : sphereFinite (f (n + N) z) = sphereInfty :=
      (infinityCoordinate_eq_zero_iff hp.1).mp hzero
    exact OnePoint.coe_ne_infty _ hi
  have hzero : EqOn G (fun _ => 0) (ball a r) := by
    rcases Hurwitz.zero_free_or_identically_zero (ball a r) g G
      hballDomain hg hG hconv hfree with h | h
    · exact False.elim ((h a (mem_ball_self hr)) (by
        change infinityCoordinate (F a) = 0
        rw [hinf, infinityCoordinate_sphereInfty]))
    · exact h
  filter_upwards [ball_mem_nhds a hr] with z hz
  exact (infinityCoordinate_eq_zero_iff (himage (ball_subset_closedBall hz))).mp (hzero hz)


/-- The finite-sequence conclusion of the spherical limit theorem, including
ordinary locally uniform convergence in the finite case. -/
theorem finite_spherical_limit :
    Specs.D12Complex.Ch11.FiniteSphericalLimits.finite_spherical_limit_type := by
  intro Ω f F hΩ hf hlim
  have hfSphere : ∀ n, PlaneSphereHolomorphicOn Ω (fun z => sphereFinite (f n z)) :=
    fun n => finite_holomorphic_lift (hf n)
  have hF : PlaneSphereHolomorphicOn Ω F :=
    SphericalLimits.sphere_holomorphic_limit Ω
      (fun n z => sphereFinite (f n z)) F hΩ.2.1 hfSphere hlim
  by_cases hconst : EqOn F (fun _ => sphereInfty) Ω
  · exact Or.inr hconst
  left
  have hfin : ∀ z ∈ Ω, F z ≠ sphereInfty := by
    intro z hz hinf
    exact plane_no_infty_germ hΩ hF hconst z hz
      (infinite_value_has_infinite_germ hΩ.2.1 hfSphere hF hlim hz hinf)
  refine ⟨hfin, ⟨hΩ.2.1, fun z hz => ?_⟩, ?_⟩
  · exact (planeSphereHolomorphicAt_finite (hF.2 z hz) (hfin z hz)).differentiableAt
  · intro K hK hKΩ
    exact (SphericalLimits.chart_compact_convergence Ω
      (fun n z => sphereFinite (f n z)) F hΩ.2.1 hfSphere hlim
      .finite K hK hKΩ (fun z hz => hfin z (hKΩ hz))).2

end D12Complex.FiniteSphericalLimits
