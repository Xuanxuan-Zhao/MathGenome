import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Independent statements for the absolute/unconditional boundary in
`fa2:p1:c15:unconditional-criteria`, paper.tex 3994–3995 and 4021–4024.
The canonical space is the accepted scalar sequence space `SequenceLp 𝕜 2`.
Its existing norm is the Hilbert norm supplied by `lp.instInnerProductSpace`.
Index `n : ℕ` means manuscript index `n+1`; `harmonicTerm` is therefore
exactly `e_{n+1}/(n+1)`, not a scalar harmonic series or an abstract witness.
Unconditional convergence means norm convergence of the finite-subset net.
-/

noncomputable section
open Filter
open scoped Topology

namespace ExpandedFA.P1.AbsoluteUnconditionalBoundary

open C01SequenceSpaces

/-- The harmonic series of coordinate vectors in the canonical scalar ℓ². -/
def harmonicTerm (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) : SequenceLp 𝕜 2 :=
  lp.single 2 n (((n + 1 : ℕ) : 𝕜)⁻¹)

namespace Spec

def HarmonicTermType :=
  ∀ (𝕜 : Type*) [RCLike 𝕜], ℕ → SequenceLp 𝕜 2

def HarmonicTermValue : HarmonicTermType := @harmonicTerm

/-- The stronger additive-group form includes every real/complex Banach space,
including the zero space. -/
def AbsoluteImpliesUnconditional : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (v : ℕ → E),
    C01Banach.Spec.AbsolutelySummableValue E v →
      C15Unconditional.Spec.UnconditionallyConvergentValue v

def HarmonicCoordinates : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (n j : ℕ),
    harmonicTerm 𝕜 n j = if j = n then (((n + 1 : ℕ) : 𝕜)⁻¹) else 0

def HarmonicNorm : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (n : ℕ),
    ‖harmonicTerm 𝕜 n‖ = ((n + 1 : ℕ) : ℝ)⁻¹

/-- Unconditional norm convergence but failure of absolute norm summability,
for both scalar fields. The positive norm partial sums even tend to infinity. -/
def HarmonicBoundary : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜],
    C15Unconditional.Spec.UnconditionallyConvergentValue (harmonicTerm 𝕜) ∧
    ¬ C01Banach.Spec.AbsolutelySummableValue (SequenceLp 𝕜 2) (harmonicTerm 𝕜) ∧
    Tendsto (fun N => ∑ n ∈ Finset.range N, ‖harmonicTerm 𝕜 n‖) atTop atTop

end Spec
end ExpandedFA.P1.AbsoluteUnconditionalBoundary
