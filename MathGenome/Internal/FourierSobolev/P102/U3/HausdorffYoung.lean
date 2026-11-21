import MathGenome.Internal.FourierSobolev.Specs.P102.U3.HausdorffYoung
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HausdorffYoung

set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal

namespace P102.U3.HausdorffYoung
open ExpandedFA.PartIV.HausdorffYoung
open P102.Specs.U3 (Euclidean Test WeakTempered)
open P102.Specs.U3.HausdorffYoung

/-- Convert the library integral normalization to the native negative-sign
Fourier transform, preserving the entire compatible family. -/
lemma exists_family (d : ℕ) : Nonempty (Family d) := by
  obtain ⟨F⟩ := euclidean_hausdorff_young d
  refine ⟨⟨F.operator, F.norm_le, ?_, F.compatible⟩⟩
  intro a f hf
  exact (F.agreement a f hf).trans (Filter.Eventually.of_forall fun x =>
    ExpandedFA.Fourier.integralFourier_eq_native _ x)

/-- Agreement with Schwartz Fourier at every exponent, including q=∞. -/
lemma schwartz_agreement {d : ℕ} (F : Family d) (a : ExponentPair) (φ : Test d) :
    F.operator a (φ.toLp a.p) = (𝓕 φ).toLp a.q := by
  apply Lp.ext
  have h1 : MemLp (φ.toLp a.p : Euclidean d → ℂ) 1 volume :=
    (φ.memLp 1).ae_eq (φ.coeFn_toLp a.p).symm
  exact ((F.agreement a _ h1).trans
    (Filter.Eventually.of_forall (Real.fourier_congr_ae (φ.coeFn_toLp a.p)))).trans
      ((𝓕 φ).coeFn_toLp a.q).symm

/-- Continuity into the weak dual suffices for passing from the dense Schwartz
class. The resulting equality is equality of functionals, hence also of strong
tempered distributions. No ordinary integral of an arbitrary Lp input is used. -/
lemma distribution_agreement {d : ℕ} (F : Family d) (a : ExponentPair)
    (f : Lp (α := Euclidean d) ℂ a.p volume) :
    P102.Specs.U3.TemperedFourier.fourierStrong_value d
      (P102.Specs.U3.TemperedFourier.regularLp_value f) =
    P102.Specs.U3.TemperedFourier.regularLp_value (F.operator a f) := by
  let A := (FourierTransform.fourierCLM ℂ (WeakTempered d)).comp
    (Lp.toTemperedDistributionCLM ℂ volume a.p)
  let B := (Lp.toTemperedDistributionCLM ℂ volume a.q).comp (F.operator a)
  have he : ∀ φ : Test d, A (φ.toLp a.p) = B (φ.toLp a.p) := by
    intro φ
    dsimp only [A, B, ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply]
    rw [schwartz_agreement F a φ]
    rw [Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
    exact TemperedDistribution.fourier_toTemperedDistributionCLM_eq φ
  have hp : a.p ≠ ∞ := ne_top_of_le_ne_top (by norm_num) a.upper
  have heq : (A : _ → WeakTempered d) = B :=
    (SchwartzMap.denseRange_toLpCLM (E := Euclidean d) (F := ℂ) hp).equalizer
      A.continuous B.continuous (funext he)
  have hf := congrFun heq f
  ext φ
  exact congrArg (fun U : WeakTempered d => U φ) hf

/-- The p=2 member is exactly the shared Plancherel operator. -/
lemma two_agreement {d : ℕ} (F : Family d)
    (f : Lp (α := Euclidean d) ℂ 2 volume) :
    F.operator two f = P102.Specs.U3.Plancherel.fourierL2_value (Euclidean d) ℂ f := by
  let A := F.operator two
  let B := (P102.Specs.U3.Plancherel.fourierL2_value (Euclidean d) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have he : ∀ φ : Test d, A (φ.toLp 2) = B (φ.toLp 2) := by
    intro φ
    exact (schwartz_agreement F two φ).trans (SchwartzMap.toLp_fourier_eq φ).symm
  have heq : (A : _ → Lp (α := Euclidean d) ℂ 2 volume) = B :=
    (SchwartzMap.denseRange_toLpCLM (E := Euclidean d) (F := ℂ) (by norm_num : (2 : ENNReal) ≠ ∞)).equalizer
      A.continuous B.continuous (funext he)
  exact congrFun heq f

/-- Hausdorff–Young with both endpoints, arbitrary-intersection compatibility,
and the distributional interpretation for every Lp input in every dimension. -/
theorem hausdorff_young : P102.Specs.U3.HausdorffYoung.Statement := by
  intro d
  obtain ⟨F⟩ := exists_family d
  exact ⟨F, distribution_agreement F, two_agreement F⟩

end P102.U3.HausdorffYoung
