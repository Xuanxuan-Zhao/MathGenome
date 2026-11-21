import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.LaplaceL2

/-! Independent statements for the interior-p and sharp-norm clauses of
`fa2:p4:laplace-hankel`, paper.tex:19598–19640. Endpoint failures are allocated
separately. Scalars are real or complex, and both Lp spaces use ordinary a.e.
equality. No condition is imposed outside the positive half-line. -/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace ExpandedFA.PartIV.CarlemanNormSpec
open LaplaceL2Spec

/-- The actual convolution kernel after logarithmic coordinates. -/
def kernel (p x : ℝ) : ℝ := Real.exp (x / p) / (1 + Real.exp x)

def eulerKernel (a t : ℝ) : ℝ := t ^ (a - 1) / (1 + t)

def sharpConstant (p : ℝ) : ℝ := Real.pi / Real.sin (Real.pi / p)

def logTransform {𝕜 : Type} [RCLike 𝕜] (p : ℝ) (f : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  Real.exp (x / p) • f (Real.exp x)

def inverseLogTransform {𝕜 : Type} [RCLike 𝕜] (p : ℝ) (g : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  if 0 < t then t ^ (-1 / p) • g (Real.log t) else 0

/-- The order of the factors agrees with h_p * g in the manuscript. -/
def convolution {𝕜 : Type} [RCLike 𝕜] (p : ℝ) (g : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  ∫ y, kernel p (x - y) • g y

abbrev PositiveLp (𝕜 : Type) [RCLike 𝕜] (p : ℝ) := Lp 𝕜 (ENNReal.ofReal p) halfLine
abbrev LineLp (𝕜 : Type) [RCLike 𝕜] (p : ℝ) := Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ)

def KernelMass : Prop :=
  ∀ p : ℝ, 1 < p →
    Integrable (kernel p) ∧ Integrable (eulerKernel (1 / p)) halfLine ∧
    (∫ x, kernel p x) = ∫ t, eulerKernel (1 / p) t ∂halfLine ∧
    (∫ x, kernel p x) = sharpConstant p

/-- Surjectivity, and compatibility on all measurable Lp representatives, are
part of the isometry assertion. -/
def LogarithmicIsometry : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp.le⟩
    ∃ U : PositiveLp 𝕜 p ≃ₗᵢ[𝕜] LineLp 𝕜 p,
      (∀ (f : ℝ → 𝕜) (hf : MemLp f (ENNReal.ofReal p) halfLine),
        (U (hf.toLp f) : ℝ → 𝕜) =ᵐ[volume] logTransform p f) ∧
      (∀ (g : ℝ → 𝕜) (hg : MemLp g (ENNReal.ofReal p) volume),
        (U.symm (hg.toLp g) : ℝ → 𝕜) =ᵐ[halfLine] inverseLogTransform p g)

/-- This equality of the actual integrals implies the conjugation assertion
on Lp classes once the logarithmic isometry is established. -/
def LogarithmicConjugation : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (p : ℝ) (f : ℝ → 𝕜),
    logTransform p (carlemanIntegral f) = convolution p (logTransform p f)

/-- The reverse estimate is for every bounded operator representing the
Carleman integral, so cannot be satisfied by merely naming a norm constant. -/
def ReverseBound : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp.le⟩
    ∀ H : PositiveLp 𝕜 p →L[𝕜] PositiveLp 𝕜 p,
      (∀ f : PositiveLp 𝕜 p, (H f : ℝ → 𝕜) =ᵐ[halfLine] carlemanIntegral f) →
      (∫ x, kernel p x) ≤ ‖H‖

/-- Exponent-parametric compatibility, kept separate so equality of Lp
exponents can be transported together with its norm instance. -/
def CarlemanAtExponent (𝕜 : Type) [RCLike 𝕜] (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (C : ℝ) : Prop :=
  ∃ H : Lp 𝕜 q halfLine →L[𝕜] Lp 𝕜 q halfLine,
    ‖H‖ = C ∧
    ∀ (f : ℝ → 𝕜) (hf : MemLp f q halfLine),
      (∀ᵐ s ∂halfLine, Integrable (fun t => f t / RCLike.ofReal (s + t)) halfLine) ∧
      (H (hf.toLp f) : ℝ → 𝕜) =ᵐ[halfLine] carlemanIntegral f

def CarlemanTheorem : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp.le⟩
    CarlemanAtExponent 𝕜 (ENNReal.ofReal p) (sharpConstant p)

/-- The sharp Laplace norm concerns a bounded self-adjoint operator with the
original integral formula and its Carleman square. -/
def SharpLaplaceTheorem : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    ∃ L H : Space 𝕜 →L[𝕜] Space 𝕜,
      ‖L‖ = Real.sqrt Real.pi ∧ ‖H‖ = Real.pi ∧
      (∀ f g, inner 𝕜 (L f) g = inner 𝕜 f (L g)) ∧ H = L.comp L ∧
      ∀ (f : ℝ → 𝕜) (hf : MemLp f 2 halfLine),
        (L (hf.toLp f) : ℝ → 𝕜) =ᵐ[halfLine] laplaceIntegral f ∧
        (H (hf.toLp f) : ℝ → 𝕜) =ᵐ[halfLine] carlemanIntegral f

/-- A partial assembly target, distinct from the unconditional sharp theorem. -/
def SharpLaplaceFromCarleman : Prop := CarlemanTheorem → SharpLaplaceTheorem

end ExpandedFA.PartIV.CarlemanNormSpec
