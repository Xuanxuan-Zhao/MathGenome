import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.MonotoneSeries
import MathGenome.Internal.RealAnalysis.D11.Ch05.AlgebraNull
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Monotone convergence, nonnegative series, and disjoint-domain additivity
(paper.tex:1594–1635). The bridge to the library lower integral is already
proved for the canonical integral. The series statement follows by applying
our a.e. monotone convergence to finite partial sums. Domain additivity
then follows by applying the series statement to indicators. No size or
completeness hypothesis on the measure is used.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace D11.Ch05.MonotoneSeries

open NonnegativeIntegral
open D11.Ch04.AeCommonException
open D11.Ch01.ExhaustionRestriction

theorem monotone_convergence : Specs.D11.Ch05.MonotoneSeries.monotone_convergence := by
  intro X _ μ f F hf _hF h
  have ha := (almostEverywhere_iff_native μ _).mp h
  have hm : ∀ᵐ x ∂μ, Monotone (fun n => f n x) :=
    ha.mono fun x hx => monotone_nat_of_le_succ hx.1
  have hl : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x)) :=
    ha.mono fun _ hx => hx.2
  change Monotone (fun n => nonnegativeIntegral μ (f n)) ∧
    nonnegativeIntegral μ F = ⨆ n, nonnegativeIntegral μ (f n) ∧
    Tendsto (fun n => nonnegativeIntegral μ (f n)) atTop
      (𝓝 (nonnegativeIntegral μ F))
  simp only [integral_eq_lintegral]
  have hmono : Monotone (fun n => ∫⁻ x, f n x ∂μ) := by
    intro i j hij
    exact lintegral_mono_ae (hm.mono fun _ hx => hx hij)
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hf n).aemeasurable) hm hl
  exact ⟨hmono, tendsto_nhds_unique hlim (tendsto_atTop_iSup hmono), hlim⟩

theorem nonnegative_series : Specs.D11.Ch05.MonotoneSeries.nonnegative_series := by
  intro X _ μ f hf
  let s : ℕ → X → ℝ≥0∞ := fun N x => ∑ n ∈ Finset.range N, f n x
  have hs : ∀ N, Measurable (s N) := fun N =>
    Finset.measurable_sum _ (fun n _ => hf n)
  have hsum : Measurable (fun x => ∑' n, f n x) := by
    simpa only [ENNReal.tsum_eq_iSup_nat] using Measurable.iSup hs
  have hconv := monotone_convergence μ s (fun x => ∑' n, f n x) hs hsum
    (almostEverywhere_of_forall μ _ (fun x => ⟨
      fun N => Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ N)),
      ENNReal.tendsto_nat_tsum (fun n => f n x)⟩))
  have hfinite (N : ℕ) : nonnegativeIntegral μ (s N) =
      ∑ n ∈ Finset.range N, nonnegativeIntegral μ (f n) := by
    simp only [integral_eq_lintegral]
    exact lintegral_finsetSum _ (fun n _ => hf n)
  change nonnegativeIntegral μ (fun x => ∑' n, f n x) =
    ∑' n, nonnegativeIntegral μ (f n)
  calc
    _ = ⨆ N, nonnegativeIntegral μ (s N) := hconv.2.1
    _ = ⨆ N, ∑ n ∈ Finset.range N, nonnegativeIntegral μ (f n) := by
      simp_rw [hfinite]
    _ = _ := ENNReal.tsum_eq_iSup_nat.symm

theorem disjoint_domain_additivity :
    Specs.D11.Ch05.MonotoneSeries.disjoint_domain_additivity := by
  intro X _ μ f E hf hE hd
  classical
  have hpoint : (fun x => ∑' n, (E n).indicator f x) = (⋃ n, E n).indicator f := by
    funext x
    by_cases hx : x ∈ ⋃ n, E n
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hz : ∀ j, j ≠ i → (E j).indicator f x = 0 := by
        intro j hji
        have hj : x ∉ E j := fun hj => Set.disjoint_left.mp (hd hji) hj hi
        simp [hj]
      rw [tsum_eq_single i hz]
      simp [hi, hx]
    · have hn : ∀ n, x ∉ E n := fun n hn => hx (mem_iUnion.mpr ⟨n, hn⟩)
      simp [hn, hx]
  have hseries := nonnegative_series μ (fun n => (E n).indicator f)
    (fun n => hf.indicator (hE n))
  change nonnegativeIntegral (restrictOnSpace μ (⋃ n, E n)) f =
    ∑' n, nonnegativeIntegral (restrictOnSpace μ (E n)) f
  calc
    _ = nonnegativeIntegral μ ((⋃ n, E n).indicator f) :=
      AlgebraNull.restriction_indicator μ f _ hf (MeasurableSet.iUnion hE)
    _ = nonnegativeIntegral μ (fun x => ∑' n, (E n).indicator f x) := by rw [hpoint]
    _ = ∑' n, nonnegativeIntegral μ ((E n).indicator f) := hseries
    _ = _ := tsum_congr (fun n => (AlgebraNull.restriction_indicator μ f (E n) hf (hE n)).symm)

end D11.Ch05.MonotoneSeries
