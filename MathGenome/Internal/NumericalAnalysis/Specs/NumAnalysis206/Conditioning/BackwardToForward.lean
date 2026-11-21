import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Errors

/-! W13, local assertion and its extension to an unattained infimum.
A map on the open domain is represented by a total extension, as in W09;
backward error uses its restriction to the domain, as in W12.
The positive radius is uniform over observed outputs and admissible sets.
The strict backward-error threshold guarantees finiteness and permits
arbitrarily near feasible perturbations to remain in the local ball.
In particular the conclusion applies when the backward error is zero.
The separate finite segment assertion of W13 is outside this module. -/

universe u v w

namespace Specs.NumAnalysis206.Conditioning.BackwardToForward

noncomputable section

/-- Uniform first-order relative forward estimate, for actual perturbations. -/
def actualPerturbationStatement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (U : Set X) (hU : IsOpen U) (f : X → Y) (x : X)
    (hx : x ∈ U) (hf : DifferentiableAt 𝕜 f x) (hx0 : x ≠ 0) (hfx : f x ≠ 0),
    ∀ a : ℝ, 0 < a → ∃ r : ℝ, 0 < r ∧
      ∀ (v : X), ‖v‖ ≤ r → ∀ (hv : x + v ∈ U) (yhat : Y),
      yhat = f (x + v) →
      Errors.relativeForwardError (fun z : U => f z) ⟨x, hx⟩ yhat
        ‖f x‖₊ (nnnorm_ne_zero_iff.mpr hfx) ≤
      (relativeConditionNumberValue 𝕜 U hU f x hx hf hx0 hfx + a) * (‖v‖ / ‖x‖)

/-- The same first-order bound for the normwise relative backward infimum.
There is no feasibility or attainment hypothesis: smallness of the infimum
itself supplies the necessary near feasible perturbations, including at zero. -/
def backwardInfimumStatement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (U : Set X) (hU : IsOpen U) (f : X → Y) (x : X)
    (hx : x ∈ U) (hf : DifferentiableAt 𝕜 f x) (hx0 : x ≠ 0) (hfx : f x ≠ 0),
    ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
      ∀ (D : Set X) (yhat : Y),
      let b := Errors.relativeNormwiseBackwardError (fun z : U => f z) ⟨x, hx⟩ yhat
        D ‖x‖₊ (nnnorm_ne_zero_iff.mpr hx0)
      b < ENNReal.ofReal δ →
      Errors.relativeForwardError (fun z : U => f z) ⟨x, hx⟩ yhat
        ‖f x‖₊ (nnnorm_ne_zero_iff.mpr hfx) ≤
      (relativeConditionNumberValue 𝕜 U hU f x hx hf hx0 hfx + a) * b.toReal

end
end Specs.NumAnalysis206.Conditioning.BackwardToForward
