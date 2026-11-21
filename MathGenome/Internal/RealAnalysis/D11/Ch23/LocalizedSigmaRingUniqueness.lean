import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.LocalizedSigmaRingUniqueness
import MathGenome.Internal.RealAnalysis.D11.Ch23.ElementaryIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch23.GeneratedRingAlgebra
import MathGenome.Internal.RealAnalysis.D11.Ch01.GeneratorUniqueness
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith

/-! Uniqueness on the positive-level generated sigma-ring.
Stone ramps determine the masses of the positive levels. These levels are
already closed under intersections, by positive rescaling and lattice min.
Finite-measure uniqueness gives equality of restrictions to each level.
The sets on which the restrictions agree form a sigma-ring, using downward
closure and countable-union gluing. This packages the source's localization
and countable coverage argument without a whole-space finiteness assumption. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section

namespace D11.Ch23.LocalizedSigmaRingUniqueness

private def stoneRamp {X : Type u} (f : X → ℝ) (b : ℝ) (n : ℕ) : X → ℝ :=
  fun x => min ((n : ℝ) * (f x - min (f x) b)) 1

private lemma stoneRamp_mem {X : Type u} {V : Submodule ℝ (X → ℝ)}
    (hStone : IsStone V) (f : X → ℝ) (hf : f ∈ V) (b : ℝ) (hb : 0 < b) (n : ℕ) :
    stoneRamp f b n ∈ V := by
  exact hStone _ (V.smul_mem (n : ℝ) (V.sub_mem hf (min_const_mem V hStone f hf b hb)))

private lemma stoneRamp_nonneg {X : Type u} (f : X → ℝ) (b : ℝ) (n : ℕ) (x : X) :
    0 ≤ stoneRamp f b n x :=
  le_min (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (min_le_left _ _))) zero_le_one

private lemma stoneRamp_mono {X : Type u} (f : X → ℝ) (b : ℝ) (x : X) :
    Monotone (fun n => stoneRamp f b n x) := by
  intro i j hij
  exact min_le_min (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij)
    (sub_nonneg.mpr (min_le_left _ _))) le_rfl

private lemma stoneRamp_tendsto {X : Type u} (f : X → ℝ) (b : ℝ) (x : X) :
    Tendsto (fun n => stoneRamp f b n x) atTop
      (𝓝 ({x | b < f x}.indicator (fun _ => (1 : ℝ)) x)) := by
  classical
  by_cases hx : b < f x
  · rw [Set.indicator_of_mem (show x ∈ {x | b < f x} from hx)]
    obtain ⟨N, hN⟩ := exists_nat_gt ((f x - b)⁻¹)
    have hd : 0 < f x - b := sub_pos.mpr hx
    have hinv : (f x - b)⁻¹ * (f x - b) = 1 := inv_mul_cancel₀ hd.ne'
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    dsimp [stoneRamp]
    rw [min_eq_right hx.le]
    apply (min_eq_right _).symm
    have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    nlinarith
  · have hx' : f x ≤ b := le_of_not_gt hx
    simp [stoneRamp, min_eq_left hx', hx]

/-- Positive rescaling makes every binary intersection another positive level. -/
lemma positiveLevel_inter {X : Type u} {V : Submodule ℝ (X → ℝ)}
    (hV : IsVectorLattice V) {A B : Set X}
    (hA : A ∈ positiveLevelFamily V) (hB : B ∈ positiveLevelFamily V) :
    A ∩ B ∈ positiveLevelFamily V := by
  rcases hA with ⟨f, hf, b, hb, rfl⟩
  rcases hB with ⟨g, hg, c, hc, rfl⟩
  refine ⟨fun x => min (c * f x) (b * g x),
    hV.min_mem (V.smul_mem c hf) (V.smul_mem b hg), b * c, mul_pos hb hc, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, lt_min_iff]
  constructor
  · rintro ⟨hx, hy⟩
    constructor <;> nlinarith
  · rintro ⟨hx, hy⟩
    constructor <;> nlinarith

private lemma positiveLevel_mass_eq {X : Type u} {V : Submodule ℝ (X → ℝ)}
    (hV : IsVectorLattice V) (hStone : IsStone V) (L : V →ₗ[ℝ] ℝ) :
    letI : MeasurableSpace X := positiveLevelMeasurableSpace V
    ∀ μ ν : Measure X,
      (∀ f : V, Integrable (f : X → ℝ) μ ∧ ∫ x, (f : X → ℝ) x ∂μ = L f) →
      (∀ f : V, Integrable (f : X → ℝ) ν ∧ ∫ x, (f : X → ℝ) x ∂ν = L f) →
      ∀ A ∈ positiveLevelFamily V, μ A = ν A := by
  letI : MeasurableSpace X := positiveLevelMeasurableSpace V
  intro μ ν hμ hν A hA
  rcases hA with ⟨f, hf, b, hb, rfl⟩
  let u : ℕ → V := fun n => ⟨stoneRamp f b n, stoneRamp_mem hStone f hf b hb n⟩
  have hE : MeasurableSet {x | b < f x} := positiveLevel_measurableSet V f hf b hb
  have hind : (fun x => ENNReal.ofReal ({x | b < f x}.indicator (fun _ => (1 : ℝ)) x)) =
      {x | b < f x}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    classical
    funext x
    by_cases hx : b < f x <;> simp [hx]
  have hlim (ρ : Measure X)
      (hρ : ∀ g : V, Integrable (g : X → ℝ) ρ ∧ ∫ x, (g : X → ℝ) x ∂ρ = L g) :
      Tendsto (fun n => ENNReal.ofReal (L (u n))) atTop (𝓝 (ρ {x | b < f x})) := by
    have hm : ∀ n, Measurable (fun x => ENNReal.ofReal (stoneRamp f b n x)) :=
      fun n => (measurable_of_mem V hV _ (u n).property).ennreal_ofReal
    have ht := lintegral_tendsto_of_tendsto_of_monotone
      (μ := ρ) (fun n => (hm n).aemeasurable)
      (Eventually.of_forall fun x i j hij =>
        ENNReal.ofReal_le_ofReal (stoneRamp_mono f b x hij))
      (Eventually.of_forall fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (stoneRamp_tendsto f b x))
    have heq (n : ℕ) : (∫⁻ x, ENNReal.ofReal (stoneRamp f b n x) ∂ρ) =
        ENNReal.ofReal (L (u n)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hρ (u n)).1
        (Eventually.of_forall (stoneRamp_nonneg f b n)), (hρ (u n)).2]
    simpa only [heq, hind, lintegral_indicator hE, lintegral_one,
      Measure.restrict_apply_univ] using ht
  exact tendsto_nhds_unique (hlim μ hμ) (hlim ν hν)

/-- Any two absolutely integrable representations of the elementary integral
agree on R_V, for an arbitrary (possibly empty) underlying type. -/
theorem localized_sigma_ring_uniqueness :
    _root_.Specs.D11.Ch23.LocalizedSigmaRingUniqueness.localized_sigma_ring_uniqueness := by
  intro X V hV hStone L _hL
  letI : MeasurableSpace X := positiveLevelMeasurableSpace V
  intro μ ν hμ hν A hA
  have heq := positiveLevel_mass_eq hV hStone L μ ν hμ hν
  have hlocal (H : Set X) (hH : H ∈ positiveLevelFamily V) :
      μ.restrict H = ν.restrict H := by
    have hfinite (ρ : Measure X)
        (hρ : ∀ f : V, Integrable (f : X → ℝ) ρ ∧ ∫ x, (f : X → ℝ) x ∂ρ = L f) :
        ρ H < ∞ := by
      rcases hH with ⟨f, hf, b, hb, rfl⟩
      exact (hρ ⟨f, hf⟩).1.measure_gt_lt_top hb
    apply D11.Ch01.GeneratorUniqueness.finite_generator_uniqueness
      (μ.restrict H) (ν.restrict H) (positiveLevelFamily V) rfl
      (fun _ hs _ ht => positiveLevel_inter hV hs ht)
    · simpa only [Measure.restrict_apply_univ] using hfinite μ hμ
    · simpa only [Measure.restrict_apply_univ] using hfinite ν hν
    · intro B hB
      rw [Measure.restrict_apply (MeasurableSpace.measurableSet_generateFrom hB),
        Measure.restrict_apply (MeasurableSpace.measurableSet_generateFrom hB)]
      exact heq _ (positiveLevel_inter hV hB hH)
    · simpa only [Measure.restrict_apply_univ] using heq H hH
  let R : SigmaRing X :=
    { sets := {B | μ.restrict B = ν.restrict B}
      empty_mem := by simp
      diff_mem := fun {_ _} hB _ => Measure.restrict_congr_mono sdiff_subset hB
      iUnion_mem := fun B hB => Measure.restrict_iUnion_congr.mpr hB }
  have hRA : A ∈ R := positiveLevelSigmaRing_le V R hlocal hA
  have hrestrict : μ.restrict A = ν.restrict A := hRA
  simpa only [Measure.restrict_apply_self] using congrArg (fun ρ : Measure X => ρ A) hrestrict

end D11.Ch23.LocalizedSigmaRingUniqueness
