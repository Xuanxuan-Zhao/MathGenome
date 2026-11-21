import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.FiniteMeasureInclusion
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Finite-measure inclusions for the shared raw spaces and ordinary a.e.
quotients, including the infinite upper exponent and zero total mass. -/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch10.FiniteMeasureInclusion

open Specs.D11.Ch10.QuotientConstruction
open D11.Ch10.QuotientConstruction

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Lowering the exponent keeps the same ordinary measurable function. -/
def lowerRaw (μ : Measure X) (p q : ℝ≥0∞) (hμ : μ univ < ∞) (hpq : p ≤ q)
    (f : Raw (𝕜 := 𝕜) μ q) : Raw (𝕜 := 𝕜) μ p := by
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  exact ⟨f.val, f.property.1, f.property.2.mono_exponent hpq⟩

theorem raw_inclusion : Specs.D11.Ch10.FiniteMeasureInclusion.raw_inclusion := by
  intro X 𝕜 _ _ _ _ μ p q _ hpq hμ f hf
  exact (lowerRaw μ p q hμ hpq.le ⟨f, hf⟩).property

theorem raw_norm_estimate : Specs.D11.Ch10.FiniteMeasureInclusion.raw_norm_estimate := by
  intro X 𝕜 _ _ _ _ μ p q hp hpq hμ _ f
  have hq : 1 ≤ q := hp.trans hpq.le
  change sourceNorm μ p (lowerRaw μ p q hμ hpq.le f).val ≤
    μ univ ^ (1 / p.toReal - 1 / q.toReal) * sourceNorm μ q f.val
  rw [sourceNorm_bridge μ p hp (lowerRaw μ p q hμ hpq.le f),
    sourceNorm_bridge μ q hq f]
  change eLpNorm f.val p μ ≤
    μ univ ^ (1 / p.toReal - 1 / q.toReal) * eLpNorm f.val q μ
  simpa only [mul_comm] using
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq.le f.property.2.aestronglyMeasurable

/-- The representative identity descends to an injection of ordinary quotients. -/
def inclusion (μ : Measure X) (p q : ℝ≥0∞) (hμ : μ univ < ∞) (hpq : p ≤ q) :
    QuotientLp (𝕜 := 𝕜) μ q ↪ QuotientLp (𝕜 := 𝕜) μ p where
  toFun := Quotient.map (lowerRaw μ p q hμ hpq) (fun _ _ h => h)
  inj' := by
    intro a b h
    induction a using Quotient.inductionOn with
    | _ f =>
      induction b using Quotient.inductionOn with
      | _ g =>
        change classOf (lowerRaw μ p q hμ hpq f) =
          classOf (lowerRaw μ p q hμ hpq g) at h
        have h' : nullRelation μ p (lowerRaw μ p q hμ hpq f)
            (lowerRaw μ p q hμ hpq g) := Quotient.exact h
        exact Quotient.sound h'

theorem finite_measure_inclusion :
    Specs.D11.Ch10.FiniteMeasureInclusion.finite_measure_inclusion := by
  intro X 𝕜 _ _ _ _ μ p q hp hpq hμ h0
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : Fact (1 ≤ q) := ⟨hp.trans hpq.le⟩
  refine ⟨quotientNormedAddCommGroup μ p, quotientNormedAddCommGroup μ q,
    norm_classOf μ p, norm_classOf μ q, inclusion μ p q hμ hpq.le, ?_, ?_⟩
  · intro f
    exact ⟨(lowerRaw μ p q hμ hpq.le f).property, rfl⟩
  · intro a
    induction a using Quotient.inductionOn with
    | _ f =>
      change ‖classOf (lowerRaw μ p q hμ hpq.le f)‖ ≤
        (μ univ).toReal ^ (1 / p.toReal - 1 / q.toReal) * ‖classOf f‖
      rw [norm_classOf μ p, norm_classOf μ q]
      change (sourceNorm μ p f.val).toReal ≤
        (μ univ).toReal ^ (1 / p.toReal - 1 / q.toReal) * (sourceNorm μ q f.val).toReal
      have hn : sourceNorm μ q f.val ≠ ∞ := by
        rw [sourceNorm_bridge μ q (hp.trans hpq.le) f]
        exact f.property.2.eLpNorm_lt_top.ne
      have h := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero h0 hμ.ne) hn)
        (raw_norm_estimate μ p q hp hpq hμ h0 f)
      simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using h

theorem zero_measure_quotient : Specs.D11.Ch10.FiniteMeasureInclusion.zero_measure_quotient := by
  intro X 𝕜 _ _ _ _ μ hμ p hp
  have hz : μ = 0 := by
    ext s hs
    exact le_antisymm ((measure_mono (subset_univ s)).trans_eq hμ) bot_le
  subst μ
  constructor
  · intro a
    induction a using Quotient.inductionOn with
    | _ f =>
      apply Quotient.sound
      change (0 : Measure X) {x | f.val x ≠ (0 : Raw (𝕜 := 𝕜) 0 p).val x} = 0
      simp
  · intro f
    rw [sourceNorm_bridge 0 p hp f]
    simp

end D11.Ch10.FiniteMeasureInclusion
