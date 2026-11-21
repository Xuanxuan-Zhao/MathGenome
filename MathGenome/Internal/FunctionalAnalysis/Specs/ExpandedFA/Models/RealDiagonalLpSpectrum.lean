import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.DiagonalLpSpectrum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Complex.Basic

/-! Real scalar companion to `fa2:p3:fourier-four-points` (paper.tex:15473–15500),
with the scalar convention at lines 67–73. These are the actual sequence spaces,
not counting-measure Lp models. Every exponent below includes both endpoints. -/
noncomputable section
open scoped ENNReal
namespace ExpandedFA.Models.RealDiagonalLpSpectrumSpec

abbrev RSequence (p : ℝ≥0∞) := lp (fun _ : ℕ => ℝ) p
abbrev CSequence (p : ℝ≥0∞) := DiagonalLpSpectrumSpec.Sequence p

/-- Coordinatewise scalar inclusion. -/
def embedValue (p : ℝ≥0∞) [Fact (1 ≤ p)] : RSequence p →L[ℝ] CSequence p :=
  lp.mapCLM p (fun _ : ℕ => Complex.ofRealCLM) zero_le_one (fun _ =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp))

/-- Coordinatewise real and imaginary parts, with membership proved by `mapCLM`. -/
def reValue (p : ℝ≥0∞) [Fact (1 ≤ p)] : CSequence p →L[ℝ] RSequence p :=
  lp.mapCLM p (fun _ : ℕ => Complex.reCLM) zero_le_one (fun _ =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
      intro z; simpa using Complex.abs_re_le_norm z))

def imValue (p : ℝ≥0∞) [Fact (1 ≤ p)] : CSequence p →L[ℝ] RSequence p :=
  lp.mapCLM p (fun _ : ℕ => Complex.imCLM) zero_le_one (fun _ =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
      intro z; simpa using Complex.abs_im_le_norm z))

def synthValue (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    RSequence p × RSequence p →L[ℝ] CSequence p :=
  (embedValue p).comp (ContinuousLinearMap.fst ℝ _ _) +
    Complex.I • (embedValue p).comp (ContinuousLinearMap.snd ℝ _ _)

/-- A real diagonal, including its exact coordinate action. -/
def realDiagonalLinear (p : ℝ≥0∞) (a : RSequence ∞) :
    RSequence p →ₗ[ℝ] RSequence p where
  toFun x := ⟨fun n => a n * x n, by
    apply ((lp.memℓp x).norm.const_smul ‖a‖).mono
    intro n
    change ‖a n * x n‖ ≤ ‖a‖ * ‖x n‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (lp.norm_apply_le_norm ENNReal.top_ne_zero a n) (norm_nonneg _)⟩
  map_add' x y := lp.ext (funext fun n => mul_add _ _ _)
  map_smul' c x := lp.ext (funext fun n => mul_left_comm _ _ _)

theorem realDiagonalLinear_bound (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : RSequence ∞) (x : RSequence p) :
    ‖realDiagonalLinear p a x‖ ≤ ‖a‖ * ‖x‖ := by
  calc
    _ ≤ ‖‖a‖ • x‖ := by
      apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      intro n
      change ‖a n * x n‖ ≤ ‖‖a‖ • x n‖
      rw [norm_mul, norm_smul, norm_norm]
      exact mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm ENNReal.top_ne_zero a n) (norm_nonneg _)
    _ = ‖a‖ * ‖x‖ := by rw [norm_smul, norm_norm]

def realDiagonalValue (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞) :
    RSequence p →L[ℝ] RSequence p :=
  (realDiagonalLinear p a).mkContinuous ‖a‖ (realDiagonalLinear_bound p a)

/-- The extension uses the fixed upstream complex diagonal, with real entries. -/
def complexifiedValue (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞) :
    CSequence p →L[ℂ] CSequence p :=
  DiagonalLpSpectrumSpec.diagonalValue p (embedValue ∞ a)

def EmbedType := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], RSequence p →L[ℝ] CSequence p
def ReType := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], CSequence p →L[ℝ] RSequence p
def SynthType := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
  RSequence p × RSequence p →L[ℝ] CSequence p
def RealDiagonalType := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (_ : RSequence ∞),
  RSequence p →L[ℝ] RSequence p
def ComplexifiedType := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (_ : RSequence ∞),
  CSequence p →L[ℂ] CSequence p

def Coordinates : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
  (∀ (x : RSequence p) n, embedValue p x n = (x n : ℂ)) ∧
  (∀ (z : CSequence p) n, reValue p z n = (z n).re) ∧
  (∀ (z : CSequence p) n, imValue p z n = (z n).im) ∧
  (∀ (x y : RSequence p) n,
    synthValue p (x,y) n = (x n : ℂ) + Complex.I * (y n : ℂ))

def EmbeddingIsometric : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
  Isometry (embedValue p)

def PartBounds : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (z : CSequence p),
  ‖reValue p z‖ ≤ ‖z‖ ∧ ‖imValue p z‖ ≤ ‖z‖

def SynthesisBounds : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (x y : RSequence p),
  max ‖x‖ ‖y‖ ≤ ‖synthValue p (x,y)‖ ∧
    ‖synthValue p (x,y)‖ ≤ ‖x‖ + ‖y‖

/-- Actual bounded real-linear equivalence and its two inverse identities. -/
def Complexification : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
  ∃ e : CSequence p ≃L[ℝ] (RSequence p × RSequence p),
    (∀ z, e z = (reValue p z, imValue p z)) ∧
    (∀ w, e.symm w = synthValue p w) ∧
    (∀ z, synthValue p (reValue p z, imValue p z) = z) ∧
    (∀ x y, (reValue p (synthValue p (x,y)),
      imValue p (synthValue p (x,y))) = (x,y)) ∧
    (∀ (c : ℂ) z, e (c • z) =
      (c.re • (e z).1 - c.im • (e z).2,
       c.im • (e z).1 + c.re • (e z).2))

/-- Completeness of the coordinate complexification in its given complex norm. -/
def ComplexComplete : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
  ∀ s : ℕ → CSequence p, CauchySeq s → ∃ z, Filter.Tendsto s Filter.atTop (nhds z)

def RealDiagonalLaws : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞),
  (∀ (x : RSequence p) n, realDiagonalValue p a x n = a n * x n) ∧
  ‖realDiagonalValue p a‖ ≤ ‖a‖ ∧
  ‖realDiagonalValue p a‖ ≤ ⨆ n, |a n|

def ExtensionLaws : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞),
  (∀ x, complexifiedValue p a (embedValue p x) =
    embedValue p (realDiagonalValue p a x)) ∧
  (∀ x y, complexifiedValue p a (synthValue p (x,y)) =
    synthValue p (realDiagonalValue p a x, realDiagonalValue p a y)) ∧
  (∀ T : CSequence p →ₗ[ℂ] CSequence p,
    (∀ x, T (embedValue p x) = embedValue p (realDiagonalValue p a x)) →
      T = (complexifiedValue p a).toLinearMap)

def ComplexSpectrumLaw : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞),
  spectrum ℂ (complexifiedValue p a) = closure (Set.range fun n => (a n : ℂ))

def RealSpectrumLaw : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞),
  spectrum ℝ (realDiagonalValue p a) = closure (Set.range fun n => a n)

/-- `IsUnit` in this operator algebra means an everywhere bounded real-linear
inverse on both sides, not merely algebraic bijectivity on coordinate expressions. -/
def RealResolventLaw : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞) (r : ℝ),
  IsUnit (algebraMap ℝ (RSequence p →L[ℝ] RSequence p) r - realDiagonalValue p a) ↔
    r ∉ closure (Set.range fun n => a n)

/-- Raw bounded sequences are included without any extra hypothesis. -/
def BoundedRealSequenceLaw : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : ℕ → ℝ) (ha : BddAbove (Set.range fun n => |a n|)),
  let A : RSequence ∞ := ⟨a, memℓp_infty (by simpa only [Real.norm_eq_abs] using ha)⟩
  spectrum ℂ (complexifiedValue p A) = closure (Set.range fun n => (a n : ℂ)) ∧
  spectrum ℝ (realDiagonalValue p A) = closure (Set.range a)

end ExpandedFA.Models.RealDiagonalLpSpectrumSpec
