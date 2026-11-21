import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.MeromorphicLittlePicard
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.LittlePicard
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.TriplesCrossRatio
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.ScalarSphereBridge
import Batteries.Tactic.OpenPrivate

/-!
Meromorphic Little Picard on the whole plane, paper.tex:4320–4339.

The normalized cross ratio is a single sphere biholomorphism taking the
three omitted values to 0, 1 and infinity. Its composition with the map is
holomorphic in charts, and omission of infinity makes its finite coordinate
entire. Scalar Little Picard makes that coordinate constant. Injectivity of
the Möbius map then makes the original sphere map constant. Scalar meromorphy
excludes the constant infinity map and therefore gives a finite constant.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace D12Complex.MeromorphicLittlePicard
open Mobius
open private coordinate_open from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic

/-- Composition uses a common intermediate chart and its local inverse law. -/
theorem planeSphereHolomorphicAt_comp {F : ℂ → RiemannSphere}
    {G : RiemannSphere → RiemannSphere} {a : ℂ}
    (hF : PlaneSphereHolomorphicAt F a) (hG : SphereHolomorphicAt G (F a)) :
    PlaneSphereHolomorphicAt (G ∘ F) a := by
  obtain ⟨hFc, c, hc, hf⟩ := hF
  obtain ⟨hGc, c', d, hc', hd, hg'⟩ := hG
  have hg := ((sphereHolomorphicAt_iff_charts G (F a) c d hc hd).mp
    ⟨hGc, c', d, hc', hd, hg'⟩).2
  refine ⟨hGc.comp hFc, d, hd, ?_⟩
  apply (hg.comp hf).congr
  filter_upwards [hFc ((coordinate_open c).mem_nhds hc)] with z hz
  exact congrArg (fun p => sphereCoordinate d (G p)) ((sphereCoordinate c).left_inv hz)

/-- Normalize the three fixed omitted values, including triples containing infinity. -/
theorem normalized_entire :
    Specs.D12Complex.Ch23.MeromorphicLittlePicard.normalized_entire_type := by
  intro F p q r hF hpq hpr hqr hp hq hr
  let M := normalizedCoefficients p q r
  let G : ℂ → RiemannSphere := fun z => crossRatio (F z) p q r
  have hM : Regular M := normalizedCoefficients_regular p q r hpq hpr hqr
  have hinj := (mobiusMap_bijective M hM).1
  obtain ⟨hMp, hMq, hMr⟩ := crossRatio_normalizes p q r hpq hpr hqr
  have hnoInfty : ∀ z : ℂ, G z ≠ sphereInfty := by
    intro z hz
    apply hr z
    apply hinj
    exact hz.trans hMr.symm
  have hG : PlaneSphereHolomorphicOn univ G := by
    refine ⟨isOpen_univ, fun z hz => ?_⟩
    exact planeSphereHolomorphicAt_comp (hF.2 z hz)
      ((mobiusMap_holomorphic M hM).2 (F z) (mem_univ _))
  have hlift : ∀ z : ℂ, G z = sphereFinite (scalarFinitePart G z) :=
    fun z => sphere_eq_finiteCoordinate_of_ne_infty (hnoInfty z)
  refine ⟨⟨isOpen_univ, fun z hz =>
    (planeSphereHolomorphicAt_finite (hG.2 z hz) (hnoInfty z)).differentiableAt⟩,
    hlift, ?_, ?_⟩
  · intro z hz
    apply hp z
    apply hinj
    change G z = crossRatio p p q r
    rw [hlift z, hz, hMp]
  · intro z hz
    apply hq z
    apply hinj
    change G z = crossRatio q p q r
    rw [hlift z, hz, hMq]

/-- The sphere-map formulation includes every sphere constant. -/
theorem sphere_little_picard :
    Specs.D12Complex.Ch23.MeromorphicLittlePicard.sphere_little_picard_type := by
  intro F p q r hF hpq hpr hqr hp hq hr
  obtain ⟨hg, hlift, hzero, hone⟩ :=
    normalized_entire F p q r hF hpq hpr hqr hp hq hr
  obtain ⟨c, hc⟩ := LittlePicard.omits_zero_one_constant _ hg hzero hone
  have hinj := (mobiusMap_bijective (normalizedCoefficients p q r)
    (normalizedCoefficients_regular p q r hpq hpr hqr)).1
  refine ⟨F 0, fun z => hinj ?_⟩
  change crossRatio (F z) p q r = crossRatio (F 0) p q r
  exact (hlift z).trans
    ((congrArg sphereFinite ((hc z).trans (hc 0).symm)).trans (hlift 0).symm)

/-- Under scalar meromorphy, a sphere constant cannot be infinity. -/
theorem scalar_little_picard :
    Specs.D12Complex.Ch23.MeromorphicLittlePicard.scalar_little_picard_type := by
  intro F p q r hF hpq hpr hqr hp hq hr
  obtain ⟨c, hc⟩ := sphere_little_picard F p q r
    (scalarMeromorphic_planeSphereHolomorphic hF) hpq hpr hqr hp hq hr
  have hfinite : c ≠ sphereInfty := by
    obtain ⟨b, _, hb⟩ := hF.2.2.2.2.2 0 (mem_univ _)
    intro h
    exact hb ((hc b).trans h)
  refine ⟨finiteCoordinate c, fun z => ?_⟩
  exact (hc z).trans (sphere_eq_finiteCoordinate_of_ne_infty hfinite)

end D12Complex.MeromorphicLittlePicard
