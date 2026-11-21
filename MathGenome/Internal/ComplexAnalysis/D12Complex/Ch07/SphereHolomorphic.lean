import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereHolomorphic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereTopology
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Inv

open scoped Topology
open Filter
noncomputable section

namespace D12Complex.SphereHolomorphic

abbrev SphereCoordinate := D12Complex.SphereCoordinate
abbrev sphereCoordinate := D12Complex.sphereCoordinate
abbrev HolomorphicGermAt := D12Complex.HolomorphicGermAt
abbrev PlaneSphereHolomorphicAt := D12Complex.PlaneSphereHolomorphicAt
abbrev SphereHolomorphicAt := D12Complex.SphereHolomorphicAt
abbrev PlaneSphereHolomorphicOn := D12Complex.PlaneSphereHolomorphicOn
abbrev SphereHolomorphicOn := D12Complex.SphereHolomorphicOn

end D12Complex.SphereHolomorphic

namespace D12Complex

theorem holomorphicGermAt_iff_eventually (f : ℂ → ℂ) (a : ℂ) :
    HolomorphicGermAt f a ↔ ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ f z := by
  constructor
  · rintro ⟨V, ha, hV, hf⟩
    exact Filter.mem_of_superset (hV.mem_nhds ha) hf
  · intro h
    obtain ⟨V, hV, hVo, ha⟩ := mem_nhds_iff.mp h
    exact ⟨V, ha, hVo, fun z hz => hV hz⟩

theorem HolomorphicGermAt.differentiableAt {f : ℂ → ℂ} {a : ℂ}
    (h : HolomorphicGermAt f a) : DifferentiableAt ℂ f a :=
  (holomorphicGermAt_iff_eventually f a).mp h |>.self_of_nhds

theorem HolomorphicGermAt.congr {f g : ℂ → ℂ} {a : ℂ}
    (h : HolomorphicGermAt f a) (he : f =ᶠ[𝓝 a] g) : HolomorphicGermAt g a := by
  rw [holomorphicGermAt_iff_eventually] at h ⊢
  filter_upwards [h, eventually_eventually_nhds.mpr he] with z hz hez
  exact (show f =ᶠ[𝓝 z] g from hez).differentiableAt_iff.mp hz

theorem HolomorphicGermAt.comp {f g : ℂ → ℂ} {a : ℂ}
    (hg : HolomorphicGermAt g (f a)) (hf : HolomorphicGermAt f a) :
    HolomorphicGermAt (fun z => g (f z)) a := by
  have ht := hf.differentiableAt.continuousAt
  rw [holomorphicGermAt_iff_eventually] at hg hf ⊢
  filter_upwards [hf, ht hg] with z hz hgz
  exact hgz.comp z hz

private theorem germ_id (a : ℂ) : HolomorphicGermAt (fun z : ℂ => z) a :=
  ⟨Set.univ, Set.mem_univ _, isOpen_univ, fun _ _ => differentiableAt_id⟩

private theorem germ_const (a b : ℂ) : HolomorphicGermAt (fun _ : ℂ => b) a :=
  ⟨Set.univ, Set.mem_univ _, isOpen_univ, fun _ _ => differentiableAt_const _⟩

private theorem germ_inv (a : ℂ) (ha : a ≠ 0) :
    HolomorphicGermAt (fun z : ℂ => z⁻¹) a :=
  ⟨{0}ᶜ, ha, isClosed_singleton.isOpen_compl,
    fun _ hz => differentiableAt_inv_iff.mpr hz⟩

private theorem coordinate_open (c : SphereCoordinate) :
    IsOpen (sphereCoordinate c).source := by
  cases c
  · exact finiteChart_homeomorph.1
  · exact infinityChart_homeomorph.1

private theorem coordinate_inverse_continuous (c : SphereCoordinate) :
    Continuous (sphereCoordinate c).symm := by
  cases c
  · exact continuous_sphereFinite
  · exact continuous_infinityParametrization

private theorem coordinate_continuousAt (c : SphereCoordinate) (p : RiemannSphere)
    (hp : p ∈ (sphereCoordinate c).source) : ContinuousAt (sphereCoordinate c) p := by
  apply ContinuousWithinAt.continuousAt _ ((coordinate_open c).mem_nhds hp)
  cases c
  · exact continuousOn_finiteCoordinate p hp
  · exact continuousOn_infinityCoordinate p hp

private theorem coordinate_exists (p : RiemannSphere) :
    ∃ c : SphereCoordinate, p ∈ (sphereCoordinate c).source := by
  by_cases hp : p = sphereInfty
  · refine ⟨.reciprocal, ?_⟩
    subst p
    exact OnePoint.infty_ne_coe 0
  · exact ⟨.finite, hp⟩

private theorem finiteCoordinate_infinityParametrization (z : ℂ) :
    finiteCoordinate (infinityParametrization z) = z⁻¹ := by
  by_cases hz : z = 0
  · simp [hz, infinityParametrization, finiteCoordinate, sphereInfty]
  · simp [infinityParametrization, hz]

private theorem coordinate_nonzero (p : RiemannSphere)
    (hf : p ∈ finiteChart.source) (hi : p ∈ infinityChart.source) :
    finiteCoordinate p ≠ 0 ∧ infinityCoordinate p ≠ 0 := by
  induction p using OnePoint.rec with
  | infty => exact False.elim (hf rfl)
  | coe z =>
    have hz : z ≠ 0 := fun h => hi (congrArg sphereFinite h)
    exact ⟨hz, inv_ne_zero hz⟩

theorem sphereCoordinate_transition (c d : SphereCoordinate) (p : RiemannSphere)
    (hc : p ∈ (sphereCoordinate c).source) (hd : p ∈ (sphereCoordinate d).source) :
    HolomorphicGermAt
      (fun z => sphereCoordinate d ((sphereCoordinate c).symm z))
      (sphereCoordinate c p) := by
  cases c <;> cases d
  · exact germ_id _
  · exact germ_inv _ (coordinate_nonzero p hc hd).1
  · change HolomorphicGermAt (fun z => finiteCoordinate (infinityParametrization z))
      (infinityCoordinate p)
    simp_rw [finiteCoordinate_infinityParametrization]
    exact germ_inv _ (coordinate_nonzero p hd hc).2
  · have he : (fun z => infinityChart (infinityChart.symm z)) = (fun z : ℂ => z) := by
      funext z
      exact infinityChart.right_inv (Set.mem_univ z)
    change HolomorphicGermAt (fun z => infinityChart (infinityChart.symm z)) _
    rw [he]
    exact germ_id _

/-- Target coordinate replacement, using the holomorphic transition and local inverse law. -/
private theorem plane_target_change (F : ℂ → RiemannSphere) (a : ℂ)
    (c d : SphereCoordinate) (hF : ContinuousAt F a)
    (hc : F a ∈ (sphereCoordinate c).source) (hd : F a ∈ (sphereCoordinate d).source)
    (h : HolomorphicGermAt (fun z => sphereCoordinate c (F z)) a) :
    HolomorphicGermAt (fun z => sphereCoordinate d (F z)) a := by
  have ht := (sphereCoordinate_transition c d (F a) hc hd).comp h
  apply ht.congr
  filter_upwards [hF ((coordinate_open c).mem_nhds hc)] with z hz
  rw [(sphereCoordinate c).left_inv hz]

theorem plane_target_chart_independent (F : ℂ → RiemannSphere) (a : ℂ)
    (c d : SphereCoordinate) (hF : ContinuousAt F a)
    (hc : F a ∈ (sphereCoordinate c).source) (hd : F a ∈ (sphereCoordinate d).source) :
    HolomorphicGermAt (fun z => sphereCoordinate c (F z)) a ↔
      HolomorphicGermAt (fun z => sphereCoordinate d (F z)) a :=
  ⟨plane_target_change F a c d hF hc hd, plane_target_change F a d c hF hd hc⟩

private theorem sphere_charts_change (F : RiemannSphere → RiemannSphere)
    (p : RiemannSphere) (c c' d d' : SphereCoordinate) (hF : ContinuousAt F p)
    (hc : p ∈ (sphereCoordinate c).source) (hc' : p ∈ (sphereCoordinate c').source)
    (hd : F p ∈ (sphereCoordinate d).source) (hd' : F p ∈ (sphereCoordinate d').source)
    (h : HolomorphicGermAt
      (fun z => sphereCoordinate d (F ((sphereCoordinate c).symm z)))
      (sphereCoordinate c p)) :
    HolomorphicGermAt
      (fun z => sphereCoordinate d' (F ((sphereCoordinate c').symm z)))
      (sphereCoordinate c' p) := by
  have hs := sphereCoordinate_transition c' c p hc' hc
  have hc'i := (sphereCoordinate c').left_inv hc'
  have hpre : HolomorphicGermAt
      (fun z => sphereCoordinate d (F ((sphereCoordinate c').symm z)))
      (sphereCoordinate c' p) := by
    have hh := (show HolomorphicGermAt
      (fun z => sphereCoordinate d (F ((sphereCoordinate c).symm z)))
      (sphereCoordinate c ((sphereCoordinate c').symm (sphereCoordinate c' p))) by
        simpa only [hc'i] using h).comp hs
    apply hh.congr
    have ht : Tendsto (sphereCoordinate c').symm (𝓝 (sphereCoordinate c' p)) (𝓝 p) := by
      have ht := (coordinate_inverse_continuous c').continuousAt (x := sphereCoordinate c' p)
      change Tendsto _ _ (𝓝 ((sphereCoordinate c').symm (sphereCoordinate c' p))) at ht
      rw [hc'i] at ht
      exact ht
    filter_upwards [ht ((coordinate_open c).mem_nhds hc)] with z hz
    rw [(sphereCoordinate c).left_inv hz]
  have hcont : ContinuousAt (fun z => F ((sphereCoordinate c').symm z))
      (sphereCoordinate c' p) := by
    apply ContinuousAt.comp _ (coordinate_inverse_continuous c').continuousAt
    simpa only [hc'i] using hF
  apply plane_target_change (fun z => F ((sphereCoordinate c').symm z))
    (sphereCoordinate c' p) d d' hcont
  · simpa only [hc'i] using hd
  · simpa only [hc'i] using hd'
  · exact hpre

theorem sphere_charts_independent (F : RiemannSphere → RiemannSphere)
    (p : RiemannSphere) (c c' d d' : SphereCoordinate) (hF : ContinuousAt F p)
    (hc : p ∈ (sphereCoordinate c).source) (hc' : p ∈ (sphereCoordinate c').source)
    (hd : F p ∈ (sphereCoordinate d).source) (hd' : F p ∈ (sphereCoordinate d').source) :
    HolomorphicGermAt
      (fun z => sphereCoordinate d (F ((sphereCoordinate c).symm z)))
      (sphereCoordinate c p) ↔
    HolomorphicGermAt
      (fun z => sphereCoordinate d' (F ((sphereCoordinate c').symm z)))
      (sphereCoordinate c' p) :=
  ⟨sphere_charts_change F p c c' d d' hF hc hc' hd hd',
    sphere_charts_change F p c' c d' d hF hc' hc hd' hd⟩

theorem planeSphereHolomorphicAt_iff_chart (F : ℂ → RiemannSphere) (a : ℂ)
    (d : SphereCoordinate) (hd : F a ∈ (sphereCoordinate d).source) :
    PlaneSphereHolomorphicAt F a ↔ ContinuousAt F a ∧
      HolomorphicGermAt (fun z => sphereCoordinate d (F z)) a := by
  constructor
  · rintro ⟨hF, c, hc, h⟩
    exact ⟨hF, (plane_target_chart_independent F a c d hF hc hd).mp h⟩
  · rintro ⟨hF, h⟩
    exact ⟨hF, d, hd, h⟩

theorem sphereHolomorphicAt_iff_charts (F : RiemannSphere → RiemannSphere)
    (p : RiemannSphere) (c d : SphereCoordinate)
    (hc : p ∈ (sphereCoordinate c).source) (hd : F p ∈ (sphereCoordinate d).source) :
    SphereHolomorphicAt F p ↔ ContinuousAt F p ∧
      HolomorphicGermAt
        (fun z => sphereCoordinate d (F ((sphereCoordinate c).symm z)))
        (sphereCoordinate c p) := by
  constructor
  · rintro ⟨hF, c', d', hc', hd', h⟩
    exact ⟨hF, (sphere_charts_independent F p c' c d' d hF hc' hc hd' hd).mp h⟩
  · rintro ⟨hF, h⟩
    exact ⟨hF, c, d, hc, hd, h⟩

theorem planeSphereHolomorphicAt_infty (F : ℂ → RiemannSphere) (a : ℂ)
    (hF : F a = sphereInfty) :
    (PlaneSphereHolomorphicAt F a ↔ ContinuousAt F a ∧
      HolomorphicGermAt (fun z => infinityCoordinate (F z)) a) ∧
      infinityCoordinate (F a) = 0 := by
  constructor
  · apply planeSphereHolomorphicAt_iff_chart F a .reciprocal
    rw [hF]
    exact OnePoint.infty_ne_coe 0
  · rw [hF, infinityCoordinate_sphereInfty]

theorem sphereHolomorphicAt_infty_target (F : RiemannSphere → RiemannSphere)
    (p : RiemannSphere) (c : SphereCoordinate)
    (hc : p ∈ (sphereCoordinate c).source) (hF : F p = sphereInfty) :
    (SphereHolomorphicAt F p ↔ ContinuousAt F p ∧
      HolomorphicGermAt
        (fun z => infinityCoordinate (F ((sphereCoordinate c).symm z)))
        (sphereCoordinate c p)) ∧ infinityCoordinate (F p) = 0 := by
  constructor
  · apply sphereHolomorphicAt_iff_charts F p c .reciprocal hc
    rw [hF]
    exact OnePoint.infty_ne_coe 0
  · rw [hF, infinityCoordinate_sphereInfty]

theorem planeSphereHolomorphicOn_const (Ω : Set ℂ) (q : RiemannSphere)
    (hΩ : IsOpen Ω) : PlaneSphereHolomorphicOn Ω (fun _ => q) := by
  obtain ⟨d, hd⟩ := coordinate_exists q
  exact ⟨hΩ, fun a _ => ⟨continuousAt_const, d, hd, germ_const a _⟩⟩

theorem sphereHolomorphicOn_const (Ω : Set RiemannSphere) (q : RiemannSphere)
    (hΩ : IsOpen Ω) : SphereHolomorphicOn Ω (fun _ => q) := by
  obtain ⟨d, hd⟩ := coordinate_exists q
  refine ⟨hΩ, fun p _ => ?_⟩
  obtain ⟨c, hc⟩ := coordinate_exists p
  exact ⟨continuousAt_const, c, d, hc, hd, germ_const _ _⟩

theorem planeSphereHolomorphicOn_continuousOn (Ω : Set ℂ) (F : ℂ → RiemannSphere)
    (h : PlaneSphereHolomorphicOn Ω F) : ContinuousOn F Ω :=
  fun a ha => (h.2 a ha).1.continuousWithinAt

theorem sphereHolomorphicOn_continuousOn (Ω : Set RiemannSphere)
    (F : RiemannSphere → RiemannSphere) (h : SphereHolomorphicOn Ω F) :
    ContinuousOn F Ω := fun p hp => (h.2 p hp).1.continuousWithinAt

end D12Complex
