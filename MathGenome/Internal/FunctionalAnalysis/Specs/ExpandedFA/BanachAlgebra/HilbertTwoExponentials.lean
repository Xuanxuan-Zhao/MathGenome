import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Connected.PathConnected

/-! Hilbert-space assertions of `fa2:p2:exponentials`, paper.tex 10258–10281.
The topology on units is the native units topology, which for bounded operators
agrees with the norm subspace topology. No dimension or separability assumption
is imposed, and the zero Hilbert space is included. -/
noncomputable section
namespace ExpandedFA.BanachAlgebra.HilbertTwoExponentials.Spec
universe u

def TwoExponentials : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : (H →L[ℂ] H)ˣ),
    ∃ B C : H →L[ℂ] H, IsSelfAdjoint B ∧ IsSelfAdjoint C ∧
      (T : H →L[ℂ] H) = NormedSpace.exp (Complex.I • B) * NormedSpace.exp C

def InvertiblesPathConnected : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    PathConnectedSpace ((H →L[ℂ] H)ˣ)

end ExpandedFA.BanachAlgebra.HilbertTwoExponentials.Spec
