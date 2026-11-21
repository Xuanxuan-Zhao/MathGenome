import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.MeromorphicOmittedNormality
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.OmittedValueNormality
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.TriplesCrossRatio
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.ScalarSphereBridge
import Batteries.Tactic.OpenPrivate

/-! Three omitted sphere values give a spherically normal meromorphic family.
A single fixed Möbius transformation reduces to Montel–Carathéodory.
Its inverse transports both finite and infinite limits in the chordal metric.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.MeromorphicOmittedNormality
open Mobius
open private coordinate_open from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic

lemma planeSphereHolomorphicAt_comp {F : ℂ → RiemannSphere}
    {G : RiemannSphere → RiemannSphere} {a : ℂ}
    (hG : SphereHolomorphicAt G (F a)) (hF : PlaneSphereHolomorphicAt F a) :
    PlaneSphereHolomorphicAt (G ∘ F) a := by
  obtain ⟨hcF, d, hd, hgF⟩ := hF
  obtain ⟨hcG, c, e, hc, he, hgG⟩ := hG
  have hgc := (plane_target_chart_independent F a d c hcF hd hc).mp hgF
  have ht := hgG.comp hgc
  refine ⟨hcG.comp hcF, e, he, ht.congr ?_⟩
  filter_upwards [hcF ((coordinate_open c).mem_nhds hc)] with z hz
  rw [(sphereCoordinate c).left_inv hz]
  rfl

lemma planeSphereHolomorphicOn_comp {Ω : Set ℂ}
    {F : ℂ → RiemannSphere} {G : RiemannSphere → RiemannSphere}
    (hG : SphereHolomorphicOn univ G) (hF : PlaneSphereHolomorphicOn Ω F) :
    PlaneSphereHolomorphicOn Ω (G ∘ F) :=
  ⟨hF.1, fun z hz => planeSphereHolomorphicAt_comp (hG.2 _ (mem_univ _)) (hF.2 z hz)⟩

lemma scalar_transform {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    {T : RiemannSphere → RiemannSphere} {a b c : RiemannSphere}
    (hT : SphereHolomorphicOn univ T) (hinj : Function.Injective T)
    (hTa : T a = sphereFinite 0) (hTb : T b = sphereFinite 1) (hTc : T c = sphereInfty)
    (hF : PlaneSphereHolomorphicOn Ω F)
    (ha : ∀ z ∈ Ω, F z ≠ a) (hb : ∀ z ∈ Ω, F z ≠ b) (hc : ∀ z ∈ Ω, F z ≠ c) :
    HolomorphicOn Ω (fun z => finiteCoordinate (T (F z))) ∧
      (∀ z ∈ Ω, finiteCoordinate (T (F z)) ≠ 0) ∧
      (∀ z ∈ Ω, finiteCoordinate (T (F z)) ≠ 1) ∧
      EqOn (fun z => T (F z)) (fun z => sphereFinite (finiteCoordinate (T (F z)))) Ω := by
  have hcomp := planeSphereHolomorphicOn_comp hT hF
  have hfin : ∀ z ∈ Ω, T (F z) ≠ sphereInfty := by
    intro z hz h
    exact hc z hz (hinj (h.trans hTc.symm))
  have heq : EqOn (fun z => T (F z)) (fun z => sphereFinite (finiteCoordinate (T (F z)))) Ω :=
    fun z hz => sphere_eq_finiteCoordinate_of_ne_infty (hfin z hz)
  refine ⟨⟨hF.1, fun z hz => (planeSphereHolomorphicAt_finite (hcomp.2 z hz) (hfin z hz)).differentiableAt⟩,
    ?_, ?_, heq⟩
  · intro z hz he
    apply ha z hz
    apply hinj
    exact (heq hz).trans ((congrArg sphereFinite he).trans hTa.symm)
  · intro z hz he
    apply hb z hz
    apply hinj
    exact (heq hz).trans ((congrArg sphereFinite he).trans hTb.symm)

@[instance_reducible] private def sphereMetric : MetricSpace RiemannSphere :=
  (Classical.choose Chordal.chordal_metric).replaceTopology
    (Classical.choose_spec Chordal.chordal_metric).1.symm

local instance : MetricSpace RiemannSphere := sphereMetric
local instance : CompactSpace RiemannSphere := sphere_compact

private lemma dist_chordal (p q : RiemannSphere) : dist p q = Chordal.chordal p q :=
  (Classical.choose_spec Chordal.chordal_metric).2.1 p q

/-- Compact-sphere uniform continuity transports the explicit chordal
compact-convergence estimate through every continuous sphere map. -/
theorem continuous_comp_spherical :
    Specs.D12Complex.Ch23.MeromorphicOmittedNormality.continuous_comp_spherical_type := by
  intro Ω f F T hT hlim
  have hu : UniformContinuous T := CompactSpace.uniformContinuous_of_continuous hT
  intro K hK hKΩ ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  filter_upwards [hlim K hK hKΩ δ hδ] with n hn z hz
  rw [← dist_chordal]
  apply hcontrol
  simpa only [dist_chordal] using hn z hz

/-- The normalizer is chosen once from the omitted triple. -/
theorem normalizing_biholomorphism :
    Specs.D12Complex.Ch23.MeromorphicOmittedNormality.normalizing_biholomorphism_type := by
  intro a b c hab hac hbc
  have hM := normalizedCoefficients_regular a b c hab hac hbc
  obtain ⟨h0, h1, hinfty⟩ := crossRatio_normalizes a b c hab hac hbc
  exact ⟨hM, mobiusMap_biholomorphic _ hM, h0, h1, hinfty⟩

/-- Avoiding the preimage of infinity removes every pole of the normalized
map, even when the original scalar meromorphic function has poles. -/
theorem normalized_holomorphic :
    Specs.D12Complex.Ch23.MeromorphicOmittedNormality.normalized_holomorphic_type := by
  intro Ω F a b c _hΩ hab hac hbc hF ha hb hc
  obtain ⟨hM, hpair, h0, h1, hinfty⟩ := normalizing_biholomorphism a b c hab hac hbc
  obtain ⟨hg, hg0, hg1, he⟩ := scalar_transform hpair.1
    (mobiusMap_bijective _ hM).1 h0 h1 hinfty
    (scalarMeromorphic_planeSphereHolomorphic hF) ha hb hc
  exact ⟨hg, he, hg0, hg1⟩

/-- Apply two omitted values normality after the fixed change of target,
then use its holomorphic inverse to transport the subsequential sphere limit. -/
theorem subsequence :
    Specs.D12Complex.Ch23.MeromorphicOmittedNormality.subsequence_type := by
  intro Ω a b c hΩ hab hac hbc f hf ha hb hc
  let M := normalizedCoefficients a b c
  let T := mobiusMap M
  let I := mobiusMap (inverseCoefficients M)
  let G : ℕ → ℂ → RiemannSphere := fun n => T ∘ f n
  obtain ⟨_hM, hpair, _h0, _h1, _hinfty⟩ := normalizing_biholomorphism a b c hab hac hbc
  have hG (n : ℕ) : ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧
      (∀ z ∈ Ω, g z ≠ 0) ∧ (∀ z ∈ Ω, g z ≠ 1) ∧
      EqOn (G n) (fun z => sphereFinite (g z)) Ω := by
    obtain ⟨hg, he, hg0, hg1⟩ :=
      normalized_holomorphic Ω (f n) a b c hΩ hab hac hbc (hf n) (ha n) (hb n) (hc n)
    exact ⟨scalarFinitePart (T ∘ f n), hg, hg0, hg1, he⟩
  obtain ⟨φ, H, hφ, hH, hlim⟩ :=
    (OmittedValueNormality.spherically_normal Ω hΩ).2 G hG
  have hI : SphereHolomorphicOn univ I := hpair.2.1
  have hIcont : Continuous I := continuousOn_univ.mp
    (sphereHolomorphicOn_continuousOn univ I hI)
  have hHhol : PlaneSphereHolomorphicOn Ω H :=
    (plane_scalar_sphere_bridge Ω H hΩ).mpr hH
  have hback := continuous_comp_spherical Ω (G ∘ φ) H I hIcont hlim
  refine ⟨φ, I ∘ H, hφ,
    (plane_scalar_sphere_bridge Ω (I ∘ H) hΩ).mp
      (planeSphereHolomorphicOn_comp hI hHhol), ?_⟩
  have hleft (p : RiemannSphere) : I (T p) = p := hpair.2.2.1 p
  intro K hK hKΩ ε hε
  filter_upwards [hback K hK hKΩ ε hε] with n hn z hz
  simpa only [G, Function.comp_apply, hleft] using hn z hz

/-- Normality for all scalar meromorphic functions omitting the fixed triple;
limits include every finite sphere constant and the constant infinity. -/
theorem spherically_normal :
    Specs.D12Complex.Ch23.MeromorphicOmittedNormality.spherically_normal_type := by
  intro Ω a b c hΩ hab hac hbc
  constructor
  · intro F hF
    exact Or.inl hF.1
  · intro f hf
    exact subsequence Ω a b c hΩ hab hac hbc f (fun n => (hf n).1)
      (fun n => (hf n).2.1) (fun n => (hf n).2.2.1) (fun n => (hf n).2.2.2)

end D12Complex.MeromorphicOmittedNormality
