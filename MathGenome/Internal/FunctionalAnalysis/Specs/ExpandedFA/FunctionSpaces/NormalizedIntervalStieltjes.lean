import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BVMeasureBridge

/-! Literal standard tagged sums for the normalized integrator of
`paper.tex`, Corollary `fa2:p4:riemann-stieltjes-endpoint`.
The strict partition convention is the usual a=t₀<⋯<tₙ=b convention.
The ambient integrator is extended constantly on either side; only its values
on [a,b] enter the variation or the sums. -/
namespace ExpandedFA.FunctionSpaces.NormalizedIntervalStieltjesSpec
open Set MeasureTheory Filter
open scoped Topology ENNReal
open BVMeasureBridgeSpec ScalarRieszMarkovSpec

noncomputable def normalizedIntegrator {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    (ν : VectorMeasure (Icc a b) 𝕜) (t : ℝ) : 𝕜 :=
  if t ≤ a then 0 else ν {x | (x : ℝ) ≤ t}

structure IntervalPartition (a b : ℝ) extends TaggedPartition a b where
  strict : StrictMonoOn point (Iic n)

/-- Ordinary sums, with no separate atom term. -/
noncomputable def standardSum {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    (p : IntervalPartition a b) (w f : ℝ → 𝕜) : 𝕜 :=
  ∑ i ∈ Finset.range p.n, f (p.tag i) * (w (p.point (i+1)) - w (p.point i))

def MeasureProperties : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ), a < b →
    ∀ ν : VectorMeasure (Icc a b) 𝕜, IsFiniteMeasure ν.variation →
    let w := normalizedIntegrator ν
    w a = 0 ∧
    (∀ t, t ∈ Ioc a b → w t = ν {x | (x : ℝ) ≤ t}) ∧
    BoundedVariationOn w (Icc a b) ∧
    eVariationOn w (Icc a b) = ν.variation univ ∧
    (∀ t ∈ Ioo a b, ContinuousWithinAt w (Ici t) t) ∧
    Tendsto w (𝓝[>] a) (𝓝 (ν {x | (x : ℝ) = a})) ∧
    w.rightLim a - w a = ν {x | (x : ℝ) = a}

/-- Convergence for every continuous interval function, every sufficiently fine
strict partition, and arbitrary tags in its closed cells. -/
def TaggedConvergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ), a < b →
    ∀ ν : VectorMeasure (Icc a b) 𝕜, IsFiniteMeasure ν.variation →
    ∀ f : C(Icc a b, 𝕜), Integrable f ν.variation ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ p : IntervalPartition a b,
          (∀ i < p.n, p.point (i+1) - p.point i < δ) →
          ‖standardSum p (normalizedIntegrator ν) (intervalIntegrand f) -
            scalarIntegral ν f‖ < ε

/-- All continuous scalar-linear functionals have the literal normalized
representation, with variation equal to their operator norm. -/
def FunctionalRepresentation (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (a b : ℝ), a < b → ∀ L : C(Icc a b, 𝕜) →L[𝕜] 𝕜,
    ∃ ν : VectorMeasure (Icc a b) 𝕜,
      FiniteScalarRadon ν ∧
      (normalizedIntegrator ν a = 0) ∧
      BoundedVariationOn (normalizedIntegrator ν) (Icc a b) ∧
      (eVariationOn (normalizedIntegrator ν) (Icc a b)).toReal = ‖L‖ ∧
      (∀ f : C(Icc a b, 𝕜), Integrable f ν.variation ∧ L f = scalarIntegral ν f) ∧
      (∀ f : C(Icc a b, 𝕜), ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ p : IntervalPartition a b,
          (∀ i < p.n, p.point (i+1) - p.point i < δ) →
          ‖standardSum p (normalizedIntegrator ν) (intervalIntegrand f) - L f‖ < ε) ∧
      (∀ t ∈ Ioo a b, ContinuousWithinAt (normalizedIntegrator ν) (Ici t) t) ∧
      (normalizedIntegrator ν).rightLim a - normalizedIntegrator ν a =
        ν {x | (x : ℝ) = a}

def RealFunctionalRepresentation : Prop := FunctionalRepresentation ℝ

def ComplexFunctionalRepresentation : Prop := FunctionalRepresentation ℂ

end ExpandedFA.FunctionSpaces.NormalizedIntervalStieltjesSpec
