import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section
namespace NumAnalysis206.CourantFischerDefinitions
open NumAnalysis206.MatrixDefinitions

/-- Values of the real Rayleigh form on the unit sphere of a subspace. -/
def unitRayleighValues {K : Type*} [RCLike K] {n : ℕ}
    (A : Mat K n n) (S : Submodule K (Vec K n)) : Set ℝ :=
  {r | ∃ x : Vec K n, x ∈ S ∧ ‖x‖ = 1 ∧ rayleigh A x = r}

end NumAnalysis206.CourantFischerDefinitions

namespace Specs.NumAnalysis206.CourantFischer
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.CourantFischerDefinitions

/-- Courant--Fischer with attained inner and outer extrema. `i : Fin n`
represents the manuscript index `i.val + 1`; hence there is no index when n=0.
`IsLeast`/`IsGreatest` include membership, so the subspaces and unit vectors
achieving the extrema are part of the conclusion. -/
def courant_fischer : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian)
    (i : Fin n),
    (∀ S : Submodule K (Vec K n), 0 < Module.finrank K S →
      ∃ a b : ℝ, IsLeast (unitRayleighValues A S) a ∧
        IsGreatest (unitRayleighValues A S) b) ∧
    IsLeast {r | ∃ S : Submodule K (Vec K n),
      Module.finrank K S = i.val + 1 ∧ IsGreatest (unitRayleighValues A S) r}
      (eigenvalue A hA i) ∧
    IsGreatest {r | ∃ S : Submodule K (Vec K n),
      Module.finrank K S = n - i.val ∧ IsLeast (unitRayleighValues A S) r}
      (eigenvalue A hA i)

end Specs.NumAnalysis206.CourantFischer
