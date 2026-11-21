import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.VariationalFirmness

/-! Independent specifications for the nonempty-minimizer clause of
`fa2:p2:prox-large-parameter`, paper.tex:8613–8664.
The parameter ranges over all real numbers and tends to +∞; positivity is
therefore eventual. No compactness, coercivity, or separability is assumed. -/
noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.Proximal.LargeParameterSpec
open P1.ExtendedConvexFunctions
universe u

def ArgminType := ∀ (H : Type u), ExtendedFunction H → Set H

/-- Global minimizers of the original extended-valued function. -/
def ArgminValue : ArgminType.{u} := fun _ φ => {x | ∀ y, φ x ≤ φ y}

def MinimizerSetGeometry : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    (ArgminValue H φ).Nonempty →
    (ArgminValue H φ).Nonempty ∧ IsClosed (ArgminValue H φ) ∧ Convex ℝ (ArgminValue H φ)

/-- The closedness and convexity certificates are conclusions, used only to
form the already shared nearest-point projector. The limit is in the norm
topology of the original real Hilbert space, for every datum f. -/
def LargeParameterLimit : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ hne : (ArgminValue H φ).Nonempty,
      ∃ (hclosed : IsClosed (ArgminValue H φ)) (hc : Convex ℝ (ArgminValue H φ)),
        ∀ f : H, Tendsto (fun μ : ℝ => Spec.ProximalMapValue H φ μ f) atTop
          (𝓝 (Hilbert.Projection.Spec.ConvexProjectionValue ℝ H
            (ArgminValue H φ) hne hclosed hc f))

end ExpandedFA.Proximal.LargeParameterSpec
