import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeMeasurability
import MathGenome.Internal.RealAnalysis.D11.Ch04.AeCommonException
import MathGenome.Internal.RealAnalysis.D11.Ch04.ScalarOperationsLimits

/-!
A.e. changes and limits, in the given sigma-algebra. A measurable version
is obtained by resetting a sequence and its limit to zero on a measurable
null exceptional set. Only the conclusions concerning the given function
require measure completeness. The construction includes infinite extended-real
limits and finite real and complex limits, and works on an empty source.
-/

open Set Filter MeasureTheory MeasurableSpace
open scoped Topology
universe u v

namespace D11.Ch04.AeMeasurability

open D11.Ch01.MeasureDefinitions
open D11.Ch04.AeCommonException

private theorem measurable_of_ae_eq_complete {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (f g : X → Y) (hμ : isComplete μ) (hf : Measurable f) (heq : aeEq μ f g) :
    Measurable g := by
  let : μ.IsComplete := (complete_iff μ).mp hμ
  exact hf.congr_ae ((aeEq_iff_native μ f g).mp heq)

/-- The closure law is applied to an everywhere convergent sequence after
resetting on the measurable exceptional envelope; it is supplied below by
proved pointwise-limit results for each scalar target. -/
private theorem version_of_pointwise_limit {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y] [Zero Y]
    (pointwise_limit : ∀ (F : ℕ → X → Y) (h : X → Y),
      (∀ n, Measurable (F n)) →
      (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (h x))) → Measurable h)
    (μ : Measure X) (f : ℕ → X → Y) (g : X → Y)
    (hf : ∀ n, Measurable (f n))
    (hg : almostEverywhere μ (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x)))) :
    ∃ h : X → Y, Measurable h ∧ aeEq μ h g := by
  classical
  obtain ⟨N, hN, hlim⟩ := hg
  let F : ℕ → X → Y := fun n x => if x ∈ N then 0 else f n x
  let h : X → Y := fun x => if x ∈ N then 0 else g x
  have hF : ∀ n, Measurable (F n) := fun n =>
    measurable_const.piecewise hN.1 (hf n)
  have hconv : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (h x)) := by
    intro x
    by_cases hx : x ∈ N
    · simpa only [F, h, ite_eq_left hx] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Y)) atTop (𝓝 0))
    · simpa only [F, h, ite_eq_right hx] using hlim x hx
  exact ⟨h, pointwise_limit F h hF hconv,
    N, hN, fun x hx => ite_eq_right hx⟩

private theorem ereal_pointwise_limit {X : Type u} [MeasurableSpace X]
    (f : ℕ → X → EReal) (g : X → EReal) (hf : ∀ n, Measurable (f n))
    (hg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Measurable g := by
  have heq : (fun x => limsup (fun n => f n x) atTop) = g :=
    funext fun x => (hg x).limsup_eq
  rw [← heq]
  exact ScalarOperationsLimits.countable_limsup _ f hf

theorem ereal_ae_change : Specs.D11.Ch04.AeMeasurability.ereal_ae_change := by
  intro X m μ f g hμ hf heq
  exact measurable_of_ae_eq_complete μ f g hμ hf heq

theorem ereal_ae_limit_version :
    Specs.D11.Ch04.AeMeasurability.ereal_ae_limit_version := by
  intro X m μ f g hf hg
  exact version_of_pointwise_limit ereal_pointwise_limit μ f g hf hg

theorem ereal_ae_limit_complete :
    Specs.D11.Ch04.AeMeasurability.ereal_ae_limit_complete := by
  intro X m μ f g hμ hf hg
  obtain ⟨h, hh, heq⟩ := ereal_ae_limit_version μ f g hf hg
  exact ereal_ae_change μ h g hμ hh heq

theorem real_ae_change : Specs.D11.Ch04.AeMeasurability.real_ae_change := by
  intro X m μ f g hμ hf heq
  exact measurable_of_ae_eq_complete μ f g hμ hf heq

theorem real_ae_limit_version :
    Specs.D11.Ch04.AeMeasurability.real_ae_limit_version := by
  intro X m μ f g hf hg
  exact version_of_pointwise_limit (ScalarOperationsLimits.real_pointwise_limit _) μ f g hf hg

theorem real_ae_limit_complete :
    Specs.D11.Ch04.AeMeasurability.real_ae_limit_complete := by
  intro X m μ f g hμ hf hg
  obtain ⟨h, hh, heq⟩ := real_ae_limit_version μ f g hf hg
  exact real_ae_change μ h g hμ hh heq

theorem complex_ae_change : Specs.D11.Ch04.AeMeasurability.complex_ae_change := by
  intro X m μ f g hμ hf heq
  exact measurable_of_ae_eq_complete μ f g hμ hf heq

theorem complex_ae_limit_version :
    Specs.D11.Ch04.AeMeasurability.complex_ae_limit_version := by
  intro X m μ f g hf hg
  exact version_of_pointwise_limit (ScalarOperationsLimits.complex_pointwise_limit _) μ f g hf hg

theorem complex_ae_limit_complete :
    Specs.D11.Ch04.AeMeasurability.complex_ae_limit_complete := by
  intro X m μ f g hμ hf hg
  obtain ⟨h, hh, heq⟩ := complex_ae_limit_version μ f g hf hg
  exact complex_ae_change μ h g hμ hh heq

end D11.Ch04.AeMeasurability
