import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.OpenRunge
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.CompatibleExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.RungeAllowedPoles
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PiecewiseC1Length
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology

namespace D12Complex.OpenRunge
open Ch15
open Specs.D12Complex.Ch07.RationalInfinity.Objects

/-- Transfer the allowed-pole condition from the complement of Ω to each
compatible compact. The whole smaller complementary component stays in
the larger one. -/
theorem allowed_poles_on_compact (Ω K : Set ℂ) (A : Set RiemannSphere)
    (hKΩ : K ⊆ Ω) (hrel : HasRelativeHoleProperty Ω K)
    (hA : A ⊆ (sphereFinite '' Ω)ᶜ)
    (hmeet : ∀ p ∈ (sphereFinite '' Ω)ᶜ,
      (connectedComponentIn (sphereFinite '' Ω)ᶜ p ∩ A).Nonempty) :
    A ⊆ (sphereFinite '' K)ᶜ ∧
    ∀ p ∈ (sphereFinite '' K)ᶜ,
      (connectedComponentIn (sphereFinite '' K)ᶜ p ∩ A).Nonempty := by
  have hsub : (sphereFinite '' Ω)ᶜ ⊆ (sphereFinite '' K)ᶜ :=
    compl_subset_compl.mpr (image_mono hKΩ)
  refine ⟨hA.trans hsub, ?_⟩
  intro p hp
  obtain ⟨q, hqp, hq⟩ := hrel p hp
  obtain ⟨a, haq, ha⟩ := hmeet q hq
  refine ⟨a, ?_, ha⟩
  rw [connectedComponentIn_eq hqp]
  exact connectedComponentIn_mono q hsub haq

/-- Poles outside Ω make the finite coordinate holomorphic everywhere in Ω,
including at all removable cancellations of the chosen presentation. -/
theorem holomorphic_of_allowed_poles (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) (A : Set RiemannSphere)
    (hA : A ⊆ (sphereFinite '' Ω)ᶜ)
    (hp : ∀ p, extension P Q p = sphereInfty → p ∈ A) :
    (∀ z ∈ Ω, extension P Q (sphereFinite z) =
      sphereFinite (finiteCoordinate (extension P Q (sphereFinite z)))) ∧
    HolomorphicOn Ω (fun z => finiteCoordinate (extension P Q (sphereFinite z))) := by
  have hn (z : ℂ) (hz : z ∈ Ω) : extension P Q (sphereFinite z) ≠ sphereInfty := by
    intro he
    exact hA (hp _ he) ⟨z, hz, rfl⟩
  have hm := (RationalInfinity.meromorphic_extension P Q hQ).1.2.1
  have hd (z : ℂ) (hz : z ∈ Ω) :
      DifferentiableAt ℂ (fun z => finiteCoordinate (extension P Q (sphereFinite z))) z :=
    hm.2.2.2.1.2 z ⟨mem_univ _, hn z hz⟩
  refine ⟨?_, hΩ, hd⟩
  intro z hz
  rcases sphere_eq_infty_or_finite (extension P Q (sphereFinite z)) with he | ⟨c, he⟩
  · exact (hn z hz he).elim
  · rw [he]
    rfl

/-- Pointwise errors on a cofinal compact exhaustion imply ordinary compact
uniform convergence. No nonempty-set convention for a supremum is needed. -/
theorem uniform_of_exhaustion (Ω : Set ℂ) (K : ℕ → Set ℂ)
    (hcofinal : ∀ S : Set ℂ, IsCompact S → S ⊆ Ω →
      ∃ N, ∀ n, N ≤ n → S ⊆ K n)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (herr : ∀ n z, z ∈ K n → ‖f z - F n z‖ < (1 / 2 : ℝ) ^ n) :
    ∀ S : Set ℂ, IsCompact S → S ⊆ Ω → TendstoUniformlyOn F f atTop S := by
  intro S hS hSΩ
  obtain ⟨N, hN⟩ := hcofinal S hS hSΩ
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop N, ht.eventually (gt_mem_nhds hε)] with n hn he z hz
  rw [dist_eq_norm]
  exact (herr n z (hN n hn hz)).trans he

theorem open_runge : Specs.D12Complex.Ch15.OpenRunge.open_runge_type := by
  intro Ω A f hΩ hA hmeet hf
  obtain ⟨K, _, hK⟩ := compatible_exhaustion Ω hΩ
  have happ (n : ℕ) : ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      (∀ p, extension P Q p = sphereInfty → p ∈ A) ∧
      ∀ z ∈ K n, ‖f z - finiteCoordinate (extension P Q (sphereFinite z))‖ <
        (1 / 2 : ℝ) ^ n := by
    obtain ⟨hAK, hmeetK⟩ := allowed_poles_on_compact Ω (K n) A
      (hK.1 n).2.1 (hK.1 n).2.2.1 hA hmeet
    obtain ⟨P, Q, hQ, hp, _, he, _⟩ := RungeAllowedPoles.runge_allowed_poles
      (K n) Ω f A (hK.1 n).1 hΩ (hK.1 n).2.1 hf hAK hmeetK
      ((1 / 2 : ℝ) ^ n) (by positivity)
    exact ⟨P, Q, hQ, hp, he⟩
  choose P Q hQ hp he using happ
  have hh (n : ℕ) := holomorphic_of_allowed_poles Ω hΩ (P n) (Q n) (hQ n) A hA (hp n)
  exact ⟨P, Q, hQ, hp, fun n => (hh n).1, fun n => (hh n).2,
    uniform_of_exhaustion Ω K hK.2.2 _ f he⟩

open PoleMovement RationalRiemannSums
open private cycle_sum_in_algebra from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.RungeAllowedPoles

/-- Cauchy polygon sums put every holomorphic restriction in any closed
complex algebra which contains all resolvents off the compact. -/
theorem holomorphic_mem_closed_algebra (K : Compacts ℂ) (U : Set ℂ)
    (f : ℂ → ℂ) (hU : IsOpen U) (hKU : (K : Set ℂ) ⊆ U)
    (hf : HolomorphicOn U f) (F : C(K, ℂ)) (hF : ∀ z : K, F z = f z)
    (S : Subalgebra ℂ C(K, ℂ)) (hc : IsClosed (S : Set C(K, ℂ)))
    (hres : ∀ a (ha : a ∉ (K : Set ℂ)), resolvent K a ha ∈ S) : F ∈ S := by
  change F ∈ (S : Set C(K, ℂ))
  rw [← hc.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨Γ, s, P, Q, _, ht, _, _, _, _, heq, hb, _⟩ :=
    rational_riemann_approximation (K : Set ℂ) U f K.isCompact hU hKU hf ε hε
  have hd : Disjoint (K : Set ℂ) Γ.trace :=
    disjoint_left.mpr (fun z hz ht' => (ht ht').2 hz)
  obtain ⟨g, hg, heg⟩ := cycle_sum_in_algebra K S Γ s f hd hres
  refine ⟨g, hg, ?_⟩
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_lt_iff (F - g) hε).mpr
  intro z
  change ‖F z - g z‖ < ε
  rw [hF, heg, heq z (fun hz => disjoint_left.mp hd z.2 hz)]
  exact (hb z z.2).trans_lt (by linarith)

/-- Only the component represented by infinity is needed in the polynomial
algebra. This avoids making any assumption about a denominator presentation. -/
theorem polynomial_approximation (K : Compacts ℂ) (U : Set ℂ) (f : ℂ → ℂ)
    (hU : IsOpen U) (hKU : (K : Set ℂ) ⊆ U) (hf : HolomorphicOn U f)
    (hInf : ∀ p ∈ (sphereFinite '' (K : Set ℂ))ᶜ,
      sphereInfty ∈ connectedComponentIn (sphereFinite '' (K : Set ℂ))ᶜ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ z ∈ (K : Set ℂ), ‖f z - P.eval z‖ < ε := by
  let T : Subalgebra ℂ C(K, ℂ) := (Polynomial.aeval (coordinate K)).range
  let S := T.topologicalClosure
  have hc : IsClosed (S : Set C(K, ℂ)) := T.isClosed_topologicalClosure
  have hx : coordinate K ∈ S := T.le_topologicalClosure
    ⟨Polynomial.X, Polynomial.aeval_X (coordinate K)⟩
  have hres (a : ℂ) (ha : a ∉ (K : Set ℂ)) : resolvent K a ha ∈ S := by
    have hi : sphereFinite a ∈ connectedComponentIn (sphericalComplement K) sphereInfty := by
      change sphereFinite a ∈ connectedComponentIn (sphereFinite '' (K : Set ℂ))ᶜ sphereInfty
      rw [← connectedComponentIn_eq (hInf (sphereFinite a)
        ((finite_mem_sphericalComplement_iff K a).mpr ha))]
      exact mem_connectedComponentIn ((finite_mem_sphericalComplement_iff K a).mpr ha)
    have hun := ((unbounded_component K).2.2 a ha).mpr hi
    obtain ⟨b, hbcomp, hbR⟩ := exists_norm_gt_of_unbounded hun ‖coordinate K‖
    have hb : b ∉ (K : Set ℂ) := connectedComponentIn_subset _ _ hbcomp
    have hba : a ∈ connectedComponentIn (K : Set ℂ)ᶜ b := by
      rw [← connectedComponentIn_eq hbcomp]
      exact mem_connectedComponentIn ha
    exact closedAlgebra_resolvent_component K S hc b a hb ha hba
      (closedAlgebra_resolvent_far K S hc hx b hb hbR)
  let F : C(K, ℂ) := ⟨fun z => f z,
    continuous_iff_continuousAt.mpr (fun z =>
      (hf.2 z (hKU z.2)).continuousAt.comp continuous_subtype_val.continuousAt)⟩
  have hm := holomorphic_mem_closed_algebra K U f hU hKU hf F (fun _ => rfl) S hc hres
  change F ∈ closure (T : Set C(K, ℂ)) at hm
  obtain ⟨g, ⟨P, rfl⟩, hg⟩ := Metric.mem_closure_iff.mp hm ε hε
  refine ⟨P, ?_⟩
  rw [dist_eq_norm] at hg
  have hb := (ContinuousMap.norm_lt_iff (F - Polynomial.aeval (coordinate K) P) hε).mp hg
  intro z hz
  have he : (Polynomial.aeval (coordinate K) P) ⟨z, hz⟩ = P.eval z := by
    have h := Polynomial.aeval_algHom_apply (ContinuousMap.evalAlgHom ℂ ℂ ⟨z, hz⟩)
      (coordinate K) P
    simpa only [ContinuousMap.evalAlgHom_apply, coordinate, ContinuousMap.coe_mk,
      Polynomial.coe_aeval_eq_eval] using h.symm
  simpa only [ContinuousMap.sub_apply, F, ContinuousMap.coe_mk, he] using hb ⟨z, hz⟩

theorem polynomial_runge : Specs.D12Complex.Ch15.OpenRunge.polynomial_runge_type := by
  intro Ω f hΩ hconn hf
  have hInfty : sphereInfty ∈ (sphereFinite '' Ω)ᶜ := by
    rintro ⟨z, _, he⟩
    exact OnePoint.coe_ne_infty z he
  have hA : ({sphereInfty} : Set RiemannSphere) ⊆ (sphereFinite '' Ω)ᶜ :=
    singleton_subset_iff.mpr hInfty
  have hmeet : ∀ p ∈ (sphereFinite '' Ω)ᶜ,
      (connectedComponentIn (sphereFinite '' Ω)ᶜ p ∩ {sphereInfty}).Nonempty := by
    intro p hp
    exact ⟨sphereInfty, by rw [hconn.isPreconnected.connectedComponentIn hp]; exact hInfty,
      mem_singleton _⟩
  obtain ⟨K, _, hK⟩ := compatible_exhaustion Ω hΩ
  have happ (n : ℕ) : ∃ P : Polynomial ℂ,
      ∀ z ∈ K n, ‖f z - P.eval z‖ < (1 / 2 : ℝ) ^ n := by
    have hm := (allowed_poles_on_compact Ω (K n) {sphereInfty}
      (hK.1 n).2.1 (hK.1 n).2.2.1 hA hmeet).2
    apply polynomial_approximation ⟨K n, (hK.1 n).1⟩ Ω f hΩ (hK.1 n).2.1 hf
      (fun p hp => ?_) _ (by positivity)
    obtain ⟨q, hq, hqInf⟩ := hm p hp
    change sphereInfty ∈ connectedComponentIn (sphereFinite '' K n)ᶜ p
    rw [← mem_singleton_iff.mp hqInf]
    exact hq
  choose P hP using happ
  exact ⟨P, uniform_of_exhaustion Ω K hK.2.2 (fun n z => (P n).eval z) f hP⟩

theorem circle_integrals : Specs.D12Complex.Ch15.OpenRunge.circle_integrals_type := by
  intro c ρ hρ hc
  refine ⟨?_, ?_⟩
  · simpa only [sub_zero] using DiskCauchyFormula.circle_integral_sub_inv c 0 ρ hρ
      (by simpa only [zero_sub, norm_neg] using hc)
  · intro P
    rw [DiskCauchyFormula.integral_eq_circleIntegral c ρ (fun z => P.eval z) hρ.le
      P.continuous.continuousOn]
    exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le
      (s := ∅) countable_empty P.continuous.continuousOn
      (fun z _ => P.differentiableAt)

theorem circle_obstruction : Specs.D12Complex.Ch15.OpenRunge.circle_obstruction_type := by
  intro c ρ hρ hc
  rintro ⟨P, hP⟩
  let γ := DiskCauchyFormula.circlePath c ρ
  have ht : γ.trace = Metric.sphere c ρ :=
    DiskCauchyFormula.circlePath_trace c ρ hρ.le
  have htend : Tendsto (fun n => γ.integral (fun z => (P n).eval z)) atTop
      (𝓝 (γ.integral (fun z : ℂ => z⁻¹))) := by
    apply PiecewiseC1Length.integral_tendsto_uniform γ _ _
      (fun n => (P n).continuous.continuousOn)
    rwa [ht]
  have he := tendsto_nhds_unique htend (show Tendsto
      (fun n => γ.integral (fun z => (P n).eval z)) atTop (𝓝 0) from by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)).congr
    intro n
    exact ((circle_integrals c ρ hρ hc).2 (P n)).symm)
  rw [(circle_integrals c ρ hρ hc).1] at he
  exact mul_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero he

theorem annulus_obstruction : Specs.D12Complex.Ch15.OpenRunge.annulus_obstruction_type := by
  intro r R ρ hr hrρ hρR
  have hρ : 0 < ρ := hr.trans_lt hrρ
  refine ⟨?_, circle_obstruction 0 ρ hρ (by simpa using hρ)⟩
  intro z hz
  have he : ‖z‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  exact ⟨he ▸ hrρ, he ▸ hρR⟩

end D12Complex.OpenRunge
