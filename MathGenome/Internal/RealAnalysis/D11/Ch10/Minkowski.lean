import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.Minkowski
import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Minkowski and the norm identities on the shared measurable raw spaces.
The proved upstream bridges identify the finite power norm and the ordinary
essential supremum with `eLpNorm`. Applying its triangle inequality and
homogeneity therefore preserves both the source objects and the exponent
range. Measurability of sums and scalar multiples is proved separately.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch10.Minkowski

open LpDefinition
open D11.Ch04.EssentialBounds D11.Ch04.AeCommonException

-- Give the proved bridges types using the implementation names so that
-- rewriting does not depend on unfolding the independently defined Specs.
private theorem powerNorm_bridge {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p : ℝ) (f : X → 𝕜) (hp : 1 ≤ p) (hf : Measurable f) :
    powerNorm μ p f = eLpNorm f (ENNReal.ofReal p) μ :=
  powerNorm_eq_eLpNorm μ p f hp hf

private theorem essentialSupNorm_bridge {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : X → 𝕜) (hf : Measurable f) :
    essentialSupNorm μ f = eLpNorm f ∞ μ :=
  essentialSupNorm_eq_eLpNorm μ f hf

theorem minkowski_finite : Specs.D11.Ch10.Minkowski.minkowski_finite := by
  intro X 𝕜 _ _ _ _ μ p f g hp hf hg
  change f ∈ rawLp μ p at hf
  change g ∈ rawLp μ p at hg
  have hfg : Measurable (fun x => f x + g x) := hf.1.add hg.1
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hle : powerNorm μ p (fun x => f x + g x) ≤
      powerNorm μ p f + powerNorm μ p g := by
    rw [powerNorm_bridge μ p _ hp hfg,
      powerNorm_bridge μ p f hp hf.1, powerNorm_bridge μ p g hp hg.1]
    exact eLpNorm_add_le hp'
  exact ⟨⟨hfg, hle.trans_lt (ENNReal.add_lt_top.mpr ⟨hf.2, hg.2⟩)⟩, hle⟩

theorem minkowski_top : Specs.D11.Ch10.Minkowski.minkowski_top := by
  intro X 𝕜 _ _ _ _ μ f g hf hg
  change f ∈ rawLInfinity μ at hf
  change g ∈ rawLInfinity μ at hg
  have hfg : Measurable (fun x => f x + g x) := hf.1.add hg.1
  have hle : essentialSupNorm μ (fun x => f x + g x) ≤
      essentialSupNorm μ f + essentialSupNorm μ g := by
    rw [essentialSupNorm_bridge μ _ hfg,
      essentialSupNorm_bridge μ f hf.1, essentialSupNorm_bridge μ g hg.1]
    exact eLpNorm_add_le le_top
  exact ⟨⟨hfg, hle.trans_lt (ENNReal.add_lt_top.mpr ⟨hf.2, hg.2⟩)⟩, hle⟩

theorem homogeneity_finite : Specs.D11.Ch10.Minkowski.homogeneity_finite := by
  intro X 𝕜 _ _ _ _ μ p f c hp hf
  change f ∈ rawLp μ p at hf
  have hcf : Measurable (fun x => c * f x) := measurable_const.mul hf.1
  have heq : powerNorm μ p (fun x => c * f x) =
      ENNReal.ofReal ‖c‖ * powerNorm μ p f := by
    rw [powerNorm_bridge μ p _ hp hcf, powerNorm_bridge μ p f hp hf.1]
    simpa only [ofReal_norm, Pi.smul_def, smul_eq_mul] using
      eLpNorm_const_smul c f (ENNReal.ofReal p) μ
  refine ⟨⟨hcf, ?_⟩, heq⟩
  change powerNorm μ p (fun x => c * f x) < ∞
  rw [heq]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2

theorem homogeneity_top : Specs.D11.Ch10.Minkowski.homogeneity_top := by
  intro X 𝕜 _ _ _ _ μ f c hf
  change f ∈ rawLInfinity μ at hf
  have hcf : Measurable (fun x => c * f x) := measurable_const.mul hf.1
  have heq : essentialSupNorm μ (fun x => c * f x) =
      ENNReal.ofReal ‖c‖ * essentialSupNorm μ f := by
    rw [essentialSupNorm_bridge μ _ hcf, essentialSupNorm_bridge μ f hf.1]
    simpa only [ofReal_norm, Pi.smul_def, smul_eq_mul] using
      eLpNorm_const_smul c f ∞ μ
  refine ⟨⟨hcf, ?_⟩, heq⟩
  change essentialSupNorm μ (fun x => c * f x) < ∞
  rw [heq]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2

theorem zero_iff_finite : Specs.D11.Ch10.Minkowski.zero_iff_finite := by
  intro X 𝕜 _ _ _ _ μ p f hp hf
  change f ∈ rawLp μ p at hf
  change powerNorm μ p f = 0 ↔ aeEq μ f (fun _ => 0)
  rw [powerNorm_bridge μ p f hp hf.1]
  exact (eLpNorm_eq_zero_iff
    (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one hp))).trans
      (aeEq_iff_native μ f (fun _ => 0)).symm

theorem zero_iff_top : Specs.D11.Ch10.Minkowski.zero_iff_top := by
  intro X 𝕜 _ _ _ _ μ f _hf
  exact essentialSupNorm_eq_zero_iff μ f

end D11.Ch10.Minkowski
