import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.ThreeOmissionsPunctureExtension
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.TwoOmissionsPunctureExtension
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.TriplesCrossRatio
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.ScalarSphereBridge
import Batteries.Tactic.OpenPrivate

/-!
Three omitted sphere values exclude an essential puncture, paper.tex:4340–4345.
We normalize the omitted triple, extend the scalar finite part using the proved
two-omissions result, fill the puncture in the appropriate target chart, and
compose with the holomorphic inverse normalization. Patching away from the
center retains agreement on the entire original punctured disk.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.ThreeOmissionsPunctureExtension
open private coordinate_open from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic

lemma planeSphereHolomorphicAt_comp {F : ℂ → RiemannSphere}
    {G : RiemannSphere → RiemannSphere} {a : ℂ}
    (hF : PlaneSphereHolomorphicAt F a)
    (hG : SphereHolomorphicAt G (F a)) :
    PlaneSphereHolomorphicAt (fun z => G (F z)) a := by
  obtain ⟨hFc, c, hc, hf⟩ := hF
  obtain ⟨hGc, c', d, hc', hd, hg'⟩ := hG
  have hg : HolomorphicGermAt
      (fun z => sphereCoordinate d (G ((sphereCoordinate c).symm z)))
      (sphereCoordinate c (F a)) :=
    (sphere_charts_independent G (F a) c' c d d hGc hc' hc hd hd).mp hg'
  refine ⟨hGc.comp hFc, d, hd, ?_⟩
  apply (hg.comp hf).congr
  filter_upwards [hFc ((coordinate_open c).mem_nhds hc)] with z hz
  rw [(sphereCoordinate c).left_inv hz]

lemma planeSphereHolomorphicOn_comp {Ω : Set ℂ}
    {F : ℂ → RiemannSphere} {G : RiemannSphere → RiemannSphere}
    (hF : PlaneSphereHolomorphicOn Ω F)
    (hG : SphereHolomorphicOn univ G) :
    PlaneSphereHolomorphicOn Ω (fun z => G (F z)) := by
  exact ⟨hF.1, fun a ha => planeSphereHolomorphicAt_comp (hF.2 a ha) (hG.2 _ (mem_univ _))⟩

/-- Both directions use actual holomorphic sphere maps, including at poles. -/
theorem mobius_puncture_extension_iff :
    Specs.D12Complex.Ch23.ThreeOmissionsPunctureExtension.mobius_puncture_extension_iff_type := by
  intro a R f M hM
  constructor
  · rintro ⟨F, hF, he⟩
    refine ⟨fun z => Mobius.mobiusMap M (F z),
      planeSphereHolomorphicOn_comp hF (Mobius.mobiusMap_holomorphic M hM), ?_⟩
    intro z hz
    exact congrArg (Mobius.mobiusMap M) (he hz)
  · rintro ⟨G, hG, he⟩
    refine ⟨fun z => Mobius.mobiusMap (Mobius.inverseCoefficients M) (G z),
      planeSphereHolomorphicOn_comp hG (Mobius.mobiusMap_holomorphic _
        (Mobius.regular_inverseCoefficients M hM)), ?_⟩
    intro z hz
    change Mobius.mobiusMap (Mobius.inverseCoefficients M) (G z) = f z
    rw [he hz]
    exact (Mobius.mobiusMap_inverse M hM).1 (f z)


private lemma finite_germ {f : ℂ → ℂ} {a : ℂ} (hf : HolomorphicGermAt f a) :
    PlaneSphereHolomorphicAt (sphereFinite ∘ f) a := by
  refine ⟨continuous_sphereFinite.continuousAt.comp hf.differentiableAt.continuousAt,
    .finite, OnePoint.coe_ne_infty _, ?_⟩
  simpa only [sphereCoordinate, finiteChart, Function.comp_apply, PartialEquiv.coe_mk,
    finiteCoordinate_sphereFinite] using hf

private lemma patch_away {f : ℂ → ℂ} {a z : ℂ} {p : RiemannSphere}
    (hf : HolomorphicGermAt f z) (hza : z ≠ a) :
    PlaneSphereHolomorphicAt (fun w => if w = a then p else sphereFinite (f w)) z := by
  apply (finite_germ hf).congr
  filter_upwards [eventually_ne_nhds hza] with w hw
  simp only [ite_eq_right hw, Function.comp_apply]

lemma scalar_sphere_puncture_extension {a : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (_hR : 0 < R) (hf : HolomorphicOn (puncturedDisk a R) f)
    (hs : RemovableSingularityAt f a ∨ PoleAt f a) :
    ∃ F : ℂ → RiemannSphere, PlaneSphereHolomorphicOn (Metric.ball a R) F ∧
      Set.EqOn F (sphereFinite ∘ f) (puncturedDisk a R) := by
  classical
  rcases hs with hrem | hpole
  · obtain ⟨_, r, hr, g, hg, he⟩ := hrem
    let F : ℂ → RiemannSphere := fun z => if z = a then sphereFinite (g a)
      else sphereFinite (f z)
    refine ⟨F, ⟨Metric.isOpen_ball, fun z hz => ?_⟩, ?_⟩
    · by_cases hza : z = a
      · subst z
        apply (finite_germ (show HolomorphicGermAt g a from
          ⟨Metric.ball a r, Metric.mem_ball_self hr, hg⟩)).congr
        filter_upwards [Metric.ball_mem_nhds a hr] with z hz
        by_cases hza : z = a
        · simp [F, hza]
        · have hzpun : z ∈ puncturedDisk a r :=
            ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), by
              simpa only [Metric.mem_ball, dist_eq_norm] using hz⟩
          simp only [Function.comp_apply, F, ite_eq_right hza, he z hzpun]
      · apply patch_away (show HolomorphicGermAt f z from
          ⟨puncturedDisk a R, ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz⟩, hf⟩) hza
    · intro z hz
      have hza : z ≠ a := by
        intro h; simpa [h] using hz.1
      simp only [F, ite_eq_right hza, Function.comp_apply]
  · obtain ⟨m, hmpos, _, r, hr, u, hu, hu0, he⟩ := hpole
    let F : ℂ → RiemannSphere := fun z => if z = a then sphereInfty
      else sphereFinite (f z)
    refine ⟨F, ⟨Metric.isOpen_ball, fun z hz => ?_⟩, ?_⟩
    · by_cases hza : z = a
      · subst z
        have hune : ∀ᶠ z in 𝓝 a, u z ≠ 0 :=
          (hu.2 a (Metric.mem_ball_self hr)).continuousAt.eventually_ne hu0
        let g : ℂ → ℂ := fun z => (z - a)^m * (u z)⁻¹
        have hg : HolomorphicGermAt g a := by
          rw [holomorphicGermAt_iff_eventually]
          filter_upwards [Metric.ball_mem_nhds a hr, hune] with z hz hzne
          exact (((differentiableAt_id.sub_const a).pow m).mul ((hu.2 z hz).inv hzne))
        have hg0 : g a = 0 := by simp [g, zero_pow (by omega : m ≠ 0)]
        apply planeSphereHolomorphicAt_of_reciprocal_lift hg hg0
        filter_upwards [Metric.ball_mem_nhds a hr, hune] with z hz hzu
        by_cases hza : z = a
        · simp [F, hza, hg0, infinityParametrization_zero]
        · have hpow : (z - a)^m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hza)
          have hgn : g z ≠ 0 := mul_ne_zero hpow (inv_ne_zero hzu)
          rw [infinityParametrization_ne_zero _ hgn]
          have hzp : z ∈ puncturedDisk a r :=
            ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), by
              simpa only [Metric.mem_ball, dist_eq_norm] using hz⟩
          have hgeq : (g z)⁻¹ = f z := by
            simp only [g, mul_inv_rev, inv_inv]
            rw [he z hzp, mul_comm]
          simp only [F, ite_eq_right hza, hgeq]
      · apply patch_away (show HolomorphicGermAt f z from
          ⟨puncturedDisk a R, ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz⟩, hf⟩) hza
    · intro z hz
      have hza : z ≠ a := by
        intro h; simpa [h] using hz.1
      simp only [F, ite_eq_right hza, Function.comp_apply]


/-- Normalize the omitted triple, extend the scalar finite part, and compose
with the inverse normalization on the entire disk. -/
theorem three_omissions_puncture_extension :
    Specs.D12Complex.Ch23.ThreeOmissionsPunctureExtension.three_omissions_puncture_extension_type := by
  intro a R f p q r hR hf hpq hpr hqr hp hq hr
  let M := Mobius.normalizedCoefficients p q r
  have hM : Mobius.Regular M :=
    Mobius.normalizedCoefficients_regular p q r hpq hpr hqr
  have hinj := (Mobius.mobiusMap_bijective M hM).1
  have hn := Mobius.crossRatio_normalizes p q r hpq hpr hqr
  have hnp : Mobius.mobiusMap M p = sphereFinite 0 := hn.1
  have hnq : Mobius.mobiusMap M q = sphereFinite 1 := hn.2.1
  have hnr : Mobius.mobiusMap M r = sphereInfty := hn.2.2
  let T : ℂ → RiemannSphere := fun z => Mobius.mobiusMap M (f z)
  have hT : PlaneSphereHolomorphicOn (puncturedDisk a R) T :=
    planeSphereHolomorphicOn_comp hf (Mobius.mobiusMap_holomorphic M hM)
  have hfin : ∀ z ∈ puncturedDisk a R, T z ≠ sphereInfty := by
    intro z hz he
    exact hr z hz (hinj (he.trans hnr.symm))
  let g := scalarFinitePart T
  have hrep : ∀ z ∈ puncturedDisk a R, T z = sphereFinite (g z) :=
    fun z hz => sphere_eq_finiteCoordinate_of_ne_infty (hfin z hz)
  have hg : HolomorphicOn (puncturedDisk a R) g :=
    ⟨hf.1, fun z hz => (planeSphereHolomorphicAt_finite (hT.2 z hz) (hfin z hz)).differentiableAt⟩
  have hg0 : ∀ z ∈ puncturedDisk a R, g z ≠ 0 := by
    intro z hz he
    apply hp z hz
    apply hinj
    change T z = Mobius.mobiusMap M p
    rw [hrep z hz, he, hnp]
  have hg1 : ∀ z ∈ puncturedDisk a R, g z ≠ 1 := by
    intro z hz he
    apply hq z hz
    apply hinj
    change T z = Mobius.mobiusMap M q
    rw [hrep z hz, he, hnq]
  obtain ⟨G, hG, heG⟩ := scalar_sphere_puncture_extension hR hg
    (TwoOmissionsPunctureExtension.zero_one_puncture_extension a R g hR hg hg0 hg1)
  refine ⟨fun z => Mobius.mobiusMap (Mobius.inverseCoefficients M) (G z),
    planeSphereHolomorphicOn_comp hG (Mobius.mobiusMap_holomorphic _
      (Mobius.regular_inverseCoefficients M hM)), ?_⟩
  intro z hz
  change Mobius.mobiusMap (Mobius.inverseCoefficients M) (G z) = f z
  rw [heG hz, Function.comp_apply, ← hrep z hz]
  exact (Mobius.mobiusMap_inverse M hM).1 (f z)

/-- Specialization to the canonical scalar meromorphic predicate, with its
actual infinite values at the poles. -/
theorem meromorphic_three_omissions_puncture_extension :
    Specs.D12Complex.Ch23.ThreeOmissionsPunctureExtension.meromorphic_three_omissions_puncture_extension_type := by
  intro a R f p q r hR hf hpq hpr hqr hp hq hr
  exact three_omissions_puncture_extension a R f p q r hR
    (scalarMeromorphic_planeSphereHolomorphic hf) hpq hpr hqr hp hq hr

end D12Complex.ThreeOmissionsPunctureExtension
