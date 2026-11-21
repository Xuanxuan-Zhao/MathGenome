import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.Marty
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.SphericalDerivative
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.CompactTargetAscoli
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.SphericalLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Metric
open scoped Topology
open private coordinate_open coordinate_exists from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic

namespace D12Complex.Marty
open Chordal SphericalDerivative SphericalLimits SphericalCompleteness

/-- Local boundedness, expressed on every compact subset of the domain. -/
def LocallyBoundedSphericalDerivatives (Ω : Set ℂ)
    (𝓕 : Set (ℂ → RiemannSphere)) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ M : ℝ,
    ∀ F ∈ 𝓕, ∀ z ∈ K, SphericalDerivative.sphericalDeriv F z ≤ M


/-- The line element gives the norm of the real differential in every direction. -/
lemma norm_fderiv_finiteStereographic (w v : ℂ) :
    ‖fderiv ℝ finiteStereographic w v‖ = 2 * ‖v‖ / (1 + ‖w‖ ^ 2) := by
  obtain ⟨V, hV, hnorm⟩ := stereographic_line_element w v
  have ha : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w using 1 <;> simp
  have hd := (differentiable_finiteStereographic (w + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 ha
  simp only [zero_smul, add_zero] at hd
  have he : fderiv ℝ finiteStereographic w v = V := hd.unique hV
  rwa [he]

lemma norm_fderiv_reciprocalStereographic (w v : ℂ) :
    ‖fderiv ℝ (fun w => stereographic (infinityParametrization w)) w v‖ =
      2 * ‖v‖ / (1 + ‖w‖ ^ 2) := by
  obtain ⟨V, hV, hnorm⟩ := reciprocal_line_element w v
  have ha : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w using 1 <;> simp
  have hd := (differentiable_reciprocalStereographic (w + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 ha
  simp only [zero_smul, add_zero] at hd
  rw [hd.unique hV]
  exact hnorm

/-- Holomorphic sphere maps are real differentiable after stereographic embedding,
and the norm of their differential is controlled by the spherical derivative. -/
lemma stereographic_differential (F : ℂ → RiemannSphere) (a : ℂ)
    (hf : PlaneSphereHolomorphicAt F a) :
    DifferentiableAt ℝ (stereographic ∘ F) a ∧
      ∀ v : ℂ, ‖fderiv ℝ (stereographic ∘ F) a v‖ =
        2 * sphericalDeriv F a * ‖v‖ := by
  obtain ⟨hcont, c, hc, hg⟩ := hf
  let g : ℂ → ℂ := fun z => sphereCoordinate c (F z)
  let e : ℂ → Euclidean3 := fun w => stereographic ((sphereCoordinate c).symm w)
  have he : DifferentiableAt ℝ e (g a) := by
    cases c
    · exact differentiable_finiteStereographic (g a)
    · exact differentiable_reciprocalStereographic (g a)
  have he_norm : ∀ w v : ℂ, ‖fderiv ℝ e w v‖ =
      2 * ‖v‖ / (1 + ‖w‖ ^ 2) := by
    cases c
    · exact norm_fderiv_finiteStereographic
    · exact norm_fderiv_reciprocalStereographic
  have hdg := hg.differentiableAt.hasDerivAt
  have heq : (stereographic ∘ F) =ᶠ[𝓝 a] e ∘ g := by
    filter_upwards [hcont ((coordinate_open c).mem_nhds hc)] with z hz
    exact congrArg stereographic ((sphereCoordinate c).left_inv hz).symm
  have hd := (he.hasFDerivAt.comp a (hdg.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq heq
  refine ⟨hd.differentiableAt, fun v => ?_⟩
  rw [hd.fderiv]
  change ‖fderiv ℝ e (g a) (v * deriv g a)‖ = _
  rw [he_norm, norm_mul,
    sphericalDeriv_in_chart F a c ⟨hcont, c, hc, hg⟩ hc]
  change 2 * (‖v‖ * ‖deriv g a‖) / (1 + ‖g a‖ ^ 2) =
    2 * (‖deriv g a‖ / (1 + ‖g a‖ ^ 2)) * ‖v‖
  ring

/-- A bound on a convex set gives a chordal Lipschitz bound, including poles. -/
lemma chordal_le_of_sphericalDeriv_le {U : Set ℂ} {F : ℂ → RiemannSphere} {M : ℝ}
    (hU : Convex ℝ U) (hf : ∀ a ∈ U, PlaneSphereHolomorphicAt F a)
    (hM : 0 ≤ M) (hbound : ∀ a ∈ U, sphericalDeriv F a ≤ M)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    chordal (F z) (F w) ≤ M * dist z w := by
  have hd := fun a ha => stereographic_differential F a (hf a ha)
  have hb : ∀ a ∈ U, ‖fderiv ℝ (stereographic ∘ F) a‖ ≤ 2 * M := by
    intro a ha
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [(hd a ha).2 v]
    exact mul_le_mul_of_nonneg_right (by linarith [hbound a ha]) (norm_nonneg v)
  have hh := hU.norm_image_sub_le_of_norm_fderiv_le
    (fun a ha => (hd a ha).1) hb hz hw
  rw [chordal_half_chord, dist_eq_norm]
  change ‖stereographic (F z) - stereographic (F w)‖ / 2 ≤ _
  rw [norm_sub_rev, dist_eq_norm, norm_sub_rev z w]
  dsimp [Function.comp_def] at hh
  linarith

@[instance_reducible] private def sphereMetric : MetricSpace RiemannSphere :=
  (Classical.choose Chordal.chordal_metric).replaceTopology
    (Classical.choose_spec Chordal.chordal_metric).1.symm
local instance : MetricSpace RiemannSphere := sphereMetric
local instance : CompactSpace RiemannSphere := sphere_compact

private lemma dist_chordal (p q : RiemannSphere) : dist p q = chordal p q :=
  (Classical.choose_spec Chordal.chordal_metric).2.1 p q

/-- Local derivative bounds give equicontinuity with one radius for all members. -/
lemma equicontinuity_of_sphericalDeriv_bound {Ω : Set ℂ}
    {𝓕 : Set (ℂ → RiemannSphere)} (hΩ : IsOpen Ω)
    (hf : ∀ F ∈ 𝓕, PlaneSphereHolomorphicOn Ω F)
    (hb : LocallyBoundedSphericalDerivatives Ω 𝓕) :
    ∀ z : Ω, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ w : Ω, dist w z < δ → ∀ F ∈ 𝓕, chordal (F z) (F w) < ε := by
  intro z ε hε
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ z z.property
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hclosed : closedBall (z : ℂ) R ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hr)).trans hsub
  obtain ⟨M₀, hM₀⟩ := hb _ (isCompact_closedBall (z : ℂ) R) hclosed
  let M := max M₀ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨min R (ε / M), lt_min hR (div_pos hε hM), ?_⟩
  intro w hw F hF
  change dist (w : ℂ) (z : ℂ) < min R (ε / M) at hw
  have hwR : (w : ℂ) ∈ closedBall (z : ℂ) R :=
    (lt_of_lt_of_le hw (min_le_left _ _)).le
  have hh := chordal_le_of_sphericalDeriv_le (convex_closedBall (z : ℂ) R)
    (fun a ha => (hf F hF).2 a (hclosed ha)) hM.le
    (fun a ha => (hM₀ F hF a ha).trans (le_max_left _ _))
    (mem_closedBall_self hR.le) hwR
  have hwε : M * dist (w : ℂ) (z : ℂ) < ε := by
    simpa only [mul_comm] using
      (lt_div_iff₀ hM).mp (lt_of_lt_of_le hw (min_le_right _ _))
  exact hh.trans_lt (by simpa only [dist_comm, mul_comm] using hwε)

/-- The bounded-derivative direction of Marty’s criterion. -/
theorem normal_of_sphericalDeriv_bound (Ω : Set ℂ)
    (𝓕 : Set (ℂ → RiemannSphere)) (hΩ : IsDomain Ω)
    (hf : ∀ F ∈ 𝓕, ScalarMeromorphicOn Ω F)
    (hb : LocallyBoundedSphericalDerivatives Ω 𝓕) : SphericallyNormal Ω 𝓕 := by
  classical
  have hhol : ∀ F ∈ 𝓕, PlaneSphereHolomorphicOn Ω F :=
    fun F hF => scalarMeromorphic_planeSphereHolomorphic (hf F hF)
  refine ⟨fun F hF => Or.inl (hf F hF), ?_⟩
  intro f hfn
  let FC : 𝓕 → C(Ω, RiemannSphere) := fun F =>
    ⟨fun z => F.val z,
      continuousOn_iff_continuous_domRestrict.mp
        (planeSphereHolomorphicOn_continuousOn Ω F.val (hhol F.val F.property))⟩
  have heq : ∀ z : Ω, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ w : Ω, dist w z < δ → ∀ i : 𝓕, dist (FC i z) (FC i w) < ε := by
    intro z ε hε
    obtain ⟨δ, hδ, hh⟩ := equicontinuity_of_sphericalDeriv_bound hΩ.2.1 hhol hb z ε hε
    refine ⟨δ, hδ, fun w hw i => ?_⟩
    rw [dist_chordal]
    exact hh w hw i.val i.property
  obtain ⟨φ, hφ, g, hg⟩ := Ch11.CompactTargetAscoli.subsequence Ω hΩ.2.1
    RiemannSphere 𝓕 FC heq (fun n => ⟨f n, hfn n⟩)
  let G := extend Ω g
  have hlim : SphericalLocallyUniformOn (f ∘ φ) G Ω := by
    intro K hK hKΩ ε hε
    have hK' : IsCompact ((Subtype.val : Ω → ℂ) ⁻¹' K) :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
        (by simpa only [Subtype.range_coe] using hKΩ)
    have hh := Metric.tendstoUniformlyOn_iff.mp (hg _ hK') ε hε
    filter_upwards [hh] with n hn z hz
    have := hn ⟨z, hKΩ hz⟩ hz
    rw [dist_chordal] at this
    change chordal (g ⟨z, hKΩ hz⟩) (f (φ n) z) < ε at this
    change chordal (extend Ω g z) (f (φ n) z) < ε
    simpa only [extend, dite_eq_left (hKΩ hz)] using this
  exact ⟨φ, G, hφ, (scalar_meromorphic_limit Ω (f ∘ φ) G hΩ
    (fun n => hf _ (hfn _)) hlim).2, hlim⟩

/-- Cauchy’s estimate in either canonical target coordinate. -/
lemma sphericalDeriv_le_on_half_disk (F : ℂ → RiemannSphere) (a : ℂ)
    (r M : ℝ) (c : SphereCoordinate) (hr : 0 < r)
    (hf : ∀ z ∈ ball a r, PlaneSphereHolomorphicAt F z)
    (hg : HolomorphicOn (ball a r) (fun z => sphereCoordinate c (F z)))
    (hb : ∀ z ∈ closedBall a r,
      F z ∈ (sphereCoordinate c).source ∧ ‖sphereCoordinate c (F z)‖ ≤ M)
    (z : ℂ) (hz : z ∈ ball a (r / 2)) : sphericalDeriv F z ≤ M / (r / 4) := by
  have hsub : closedBall z (r / 4) ⊆ ball a r :=
    closedBall_subset_ball' (by have := mem_ball.mp hz; linarith)
  have hz' : z ∈ ball a r := ball_subset_ball (by linarith) hz
  have hd := DiskCauchyDerivatives.disk_cauchy_estimate z (r / 4) (ball a r)
    (fun w => sphereCoordinate c (F w)) M (by linarith) hg hsub
    (fun w hw => (hb w (ball_subset_closedBall (hsub (sphere_subset_closedBall hw)))).2) 1
  have hd' : ‖deriv (fun w => sphereCoordinate c (F w)) z‖ ≤ M / (r / 4) := by
    simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using hd
  rw [sphericalDeriv_in_chart F z c (hf z hz') (hb z (ball_subset_closedBall hz')).1]
  exact (div_le_self (norm_nonneg _) (by nlinarith [sq_nonneg ‖sphereCoordinate c (F z)‖])).trans hd'

/-- Spherical compact convergence bounds the derivatives at any convergent
sequence of source points. This works also at an infinite limiting value. -/
lemma sphericalDeriv_eventually_bounded {Ω : Set ℂ}
    {f : ℕ → ℂ → RiemannSphere} {F : ℂ → RiemannSphere}
    (hΩ : IsOpen Ω) (hf : ∀ n, PlaneSphereHolomorphicOn Ω (f n))
    (hlim : SphericalLocallyUniformOn f F Ω)
    {a : ℂ} (ha : a ∈ Ω) {z : ℕ → ℂ} (hz : Tendsto z atTop (𝓝 a)) :
    ∃ C : ℝ, ∀ᶠ n in atTop, sphericalDeriv (f n) (z n) ≤ C := by
  obtain ⟨c, hc⟩ := coordinate_exists (F a)
  obtain ⟨r, hr, hsub, _, ⟨M, _, _, hevent⟩, _⟩ :=
    chart_neighborhood_convergence Ω f F hΩ hf hlim a ha c hc
  refine ⟨M / (r / 4), ?_⟩
  filter_upwards [hevent, hz (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))] with n hn hzn
  exact sphericalDeriv_le_on_half_disk (f n) a r M c hr
    (fun w hw => (hf n).2 w (hsub (ball_subset_closedBall hw))) hn.1 hn.2 (z n) hzn

/-- The normal-family direction of Marty’s criterion. -/
theorem sphericalDeriv_bound_of_normal (Ω : Set ℂ)
    (𝓕 : Set (ℂ → RiemannSphere)) (hΩ : IsDomain Ω)
    (hf : ∀ F ∈ 𝓕, ScalarMeromorphicOn Ω F)
    (hnormal : SphericallyNormal Ω 𝓕) : LocallyBoundedSphericalDerivatives Ω 𝓕 := by
  classical
  intro K hK hKΩ
  by_contra hbad
  push Not at hbad
  have hex : ∀ n : ℕ, ∃ F ∈ 𝓕, ∃ z ∈ K, (n : ℝ) < sphericalDeriv F z :=
    fun n => hbad n
  choose f hfn z hzn hlarge using hex
  obtain ⟨a, ha, φ, hφ, hza⟩ := hK.tendsto_subseq hzn
  obtain ⟨ψ, F, hψ, _, hlim⟩ := hnormal.2 (f ∘ φ) (fun n => hfn _)
  have hzlim : Tendsto (z ∘ φ ∘ ψ) atTop (𝓝 a) := hza.comp hψ.tendsto_atTop
  obtain ⟨C, hC⟩ := sphericalDeriv_eventually_bounded hΩ.2.1
    (fun n => scalarMeromorphic_planeSphereHolomorphic (hf _ (hfn (φ (ψ n)))))
    hlim (hKΩ ha) hzlim
  obtain ⟨N, hN⟩ := exists_nat_gt C
  obtain ⟨n, hn, hnN⟩ := (hC.and (eventually_ge_atTop N)).exists
  have hind : N ≤ φ (ψ n) := hnN.trans ((hφ.comp hψ).id_le n)
  have hreal : C < (φ (ψ n) : ℝ) := hN.trans_le (Nat.cast_le.mpr hind)
  have hl := hlarge (φ (ψ n))
  dsimp [Function.comp_def] at hn
  linarith

/-- Marty’s criterion for every family of scalar meromorphic maps on a domain. -/
theorem marty : Specs.D12Complex.Ch11.Marty.marty_type := by
  intro Ω 𝓕 hΩ hf
  exact ⟨sphericalDeriv_bound_of_normal Ω 𝓕 hΩ hf,
    normal_of_sphericalDeriv_bound Ω 𝓕 hΩ hf⟩

end D12Complex.Marty
