import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.PushforwardComposition
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction

open Set MeasureTheory
open scoped ENNReal
universe u v w
noncomputable section
namespace D11.Ch09.PushforwardComposition
open D11.Ch09.Pushforward D11.Ch06.ScalarIntegral
open Specs.D11.Ch10.QuotientConstruction

/-- Functoriality needs only the two measurable maps. -/
theorem functoriality : Specs.D11.Ch09.PushforwardComposition.functoriality := by
  intro X Y Z _ _ _ u v hu hv μ
  exact (Measure.map_map hv hu).symm

theorem preserves_nonnegative : Specs.D11.Ch09.PushforwardComposition.preserves_nonnegative := by
  intro X Y _ _ u hu μ ν hmap h hh
  subst ν
  exact D11.Ch09.TransportNonnegative.transport_nonnegative u hu μ h hh

theorem preserves_scalar : Specs.D11.Ch09.PushforwardComposition.preserves_scalar := by
  intro X Y 𝕜 _ _ _ _ _ u hu μ ν hmap h hh
  subst ν
  exact ⟨D11.Ch09.TransportIntegrable.transport_integrable_iff u hu μ h hh,
    D11.Ch09.TransportIntegrable.transport_integral u hu μ h⟩

variable {X : Type u} {Y : Type v} {𝕜 : Type}
  [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Pullback of ordinary a.e. classes along a map with the given pushforward. -/
def pullback (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (hmap : pushforward u hu μ = ν) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p ν →ₗᵢ[𝕜] Lp 𝕜 p μ :=
  Lp.compMeasurePreservingₗᵢ 𝕜 u ⟨hu, hmap⟩

theorem pullback_rep (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (hmap : pushforward u hu μ = ν) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : Y → 𝕜) (hm : MemLp h p ν) :
    ∃ hc : MemLp (h ∘ u) p μ, pullback u hu μ ν hmap p (hm.toLp h) = hc.toLp (h ∘ u) := by
  exact ⟨hm.comp_measurePreserving ⟨hu, hmap⟩,
    Lp.toLp_compMeasurePreserving hm ⟨hu, hmap⟩⟩

theorem pullback_isometry : Specs.D11.Ch09.PushforwardComposition.pullback_isometry := by
  intro X Y 𝕜 _ _ _ _ _ u hu μ ν hmap p _
  exact ⟨pullback u hu μ ν hmap p, fun h _ hm => pullback_rep u hu μ ν hmap p h hm⟩

/-- Conjugation by the accepted representative equivalences gives the map
on the actual raw-function quotient, including its ordinary infinity endpoint. -/
def quotientPullback (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (hmap : pushforward u hu μ = ν) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    QuotientLp (𝕜 := 𝕜) ν p →ₗᵢ[𝕜] QuotientLp (𝕜 := 𝕜) μ p :=
  (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p).symm.toLinearIsometry.comp
    ((pullback u hu μ ν hmap p).comp
      (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv ν p).toLinearIsometry)

theorem quotientPullback_rep (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (hmap : pushforward u hu μ = ν) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : Raw (𝕜 := 𝕜) ν p) :
    ∃ hc : MemLp (h.val ∘ u) p μ,
      quotientPullback u hu μ ν hmap p (classOf h) =
        classOf ⟨h.val ∘ u, h.property.1.comp hu, hc⟩ := by
  obtain ⟨hc, he⟩ := pullback_rep u hu μ ν hmap p h.val h.property.2
  refine ⟨hc, ?_⟩
  apply (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p).injective
  simpa [quotientPullback] using he

theorem quotient_pullback : Specs.D11.Ch09.PushforwardComposition.quotient_pullback := by
  intro X Y 𝕜 _ _ _ _ _ u hu μ ν hmap p _
  exact ⟨D11.Ch10.QuotientConstruction.quotientNormedAddCommGroup μ p,
    D11.Ch10.QuotientConstruction.quotientNormedSpace μ p,
    D11.Ch10.QuotientConstruction.quotientNormedAddCommGroup ν p,
    D11.Ch10.QuotientConstruction.quotientNormedSpace ν p,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv ν p,
    quotientPullback u hu μ ν hmap p,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv_classOf μ p,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv_classOf ν p,
    quotientPullback_rep u hu μ ν hmap p⟩

open Specs.D11.Ch09.PushforwardComposition (twoPointMeasure)

/-- Both points have positive mass, so a.e. assertions hold at both points. -/
theorem ae_twoPoint_iff (P : Bool → Prop) :
    (∀ᵐ b ∂twoPointMeasure, P b) ↔ P false ∧ P true := by
  simp [twoPointMeasure, ae_add_measure_iff, Measure.ae_ennreal_smul_measure_iff,
    ae_dirac_eq]

theorem twoPoint_mass : twoPointMeasure Set.univ = 1 := by
  simp only [twoPointMeasure, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

theorem twoPoint_pushforward :
    pushforward (fun _ : Bool => ()) measurable_const twoPointMeasure = Measure.dirac () := by
  change Measure.map (fun _ : Bool => ()) twoPointMeasure = _
  rw [Measure.map_const, twoPoint_mass, one_smul]

/-- The displayed probability example, for either scalar field and every p,
including infinity. Its range is exactly the constant classes, and the
zero/one function is a concrete missing class. -/
theorem two_point_not_onto : Specs.D11.Ch09.PushforwardComposition.two_point_not_onto := by
  intro 𝕜 _ _ _ p _
  letI : IsProbabilityMeasure twoPointMeasure := ⟨twoPoint_mass⟩
  refine ⟨?_, ?_, twoPoint_mass, twoPoint_pushforward, ?_⟩
  · norm_num [twoPointMeasure, Measure.add_apply, Measure.smul_apply]
  · norm_num [twoPointMeasure, Measure.add_apply, Measure.smul_apply]
  let T : Lp 𝕜 p (Measure.dirac ()) →ₗᵢ[𝕜] Lp 𝕜 p twoPointMeasure :=
    pullback (fun _ : Bool => ()) measurable_const twoPointMeasure (Measure.dirac ())
      twoPoint_pushforward p
  have hrep (h : Lp 𝕜 p (Measure.dirac ())) :
      (T h : Bool → 𝕜) =ᵐ[twoPointMeasure] (fun _ => h ()) :=
    Lp.coeFn_compMeasurePreserving h ⟨measurable_const, twoPoint_pushforward⟩
  have hrange (f : Lp 𝕜 p twoPointMeasure) :
      f ∈ Set.range T ↔ ∃ c : 𝕜, (f : Bool → 𝕜) =ᵐ[twoPointMeasure] (fun _ => c) := by
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h (), hrep h⟩
    · rintro ⟨c, hc⟩
      let hm : MemLp (fun _ : Unit => c) p (Measure.dirac ()) := memLp_const c
      refine ⟨hm.toLp (fun _ => c), ?_⟩
      apply Lp.ext
      have hval : (hm.toLp (fun _ => c) : Unit → 𝕜) () = c := by
        simpa [ae_dirac_eq] using hm.coeFn_toLp
      filter_upwards [hrep (hm.toLp (fun _ => c)), hc] with b hb hcb
      exact hb.trans (hval.trans hcb.symm)
  refine ⟨T, hrep, hrange, ?_⟩
  let step : Bool → 𝕜 := fun b => if b then 1 else 0
  have hs : Measurable step := measurable_of_finite step
  have hm : MemLp step p twoPointMeasure :=
    MemLp.of_bound hs.aestronglyMeasurable 1 (Filter.Eventually.of_forall (by
      intro b
      cases b <;> simp [step]))
  refine ⟨hm, ?_⟩
  intro hin
  obtain ⟨c, hc⟩ := (hrange (hm.toLp step)).mp hin
  have he : step =ᵐ[twoPointMeasure] (fun _ => c) := hm.coeFn_toLp.symm.trans hc
  obtain ⟨h0, h1⟩ := (ae_twoPoint_iff _).mp he
  have h01 : (0 : 𝕜) = 1 := by simpa [step] using h0.trans h1.symm
  exact zero_ne_one h01

end D11.Ch09.PushforwardComposition
