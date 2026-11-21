import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Independent statements for paper.tex, Lemma `d13:10:compact-spectral`.
The scalar field may be real or complex (`RCLike`). No separability,
injectivity, dimension, or nontriviality condition is imposed on the Hilbert space.
-/

namespace Specs.D13Unified.Ch10.CompactSpectral

open Module Filter
open scoped Topology

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- The algebraic span (supremum) of all eigenspaces at strictly positive real scalars. -/
def positiveSpan (K : H →L[𝕜] H) : Submodule 𝕜 H :=
  ⨆ (r : {r : ℝ // 0 < r}), Module.End.eigenspace K.toLinearMap (r.val : 𝕜)

/-- The set of distinct nonzero eigenvalues. -/
def nonzeroEigenvalues (K : H →L[𝕜] H) : Set 𝕜 :=
  {μ | μ ≠ 0 ∧ Module.End.HasEigenvalue K.toLinearMap μ}

/-- One slot for each geometric multiplicity of each nonzero eigenvalue.
Finite dimensionality of the eigenspaces is a separate required conclusion,
so `finrank` here really is the multiplicity once the theorem is established. -/
def multiplicitySlots (K : H →L[𝕜] H) :=
  Σ μ : nonzeroEigenvalues K,
    Fin (Module.finrank 𝕜 (Module.End.eigenspace K.toLinearMap μ.val))

/-- The full compact positive spectral assertion, using the equivalent finite-threshold
form of convergence with multiplicities, and also recording convergence of any enumeration. -/
def spectralTheorem : Prop :=
  ∀ {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
  ∀ (K : H →L[𝕜] H), IsCompactOperator K → K.IsSymmetric →
    (∀ x : H, 0 ≤ RCLike.re (inner 𝕜 (K x) x)) →
    (positiveSpan K).topologicalClosure = K.kerᗮ ∧
    (∀ μ : 𝕜, μ ≠ 0 →
      FiniteDimensional 𝕜 (Module.End.eigenspace K.toLinearMap μ)) ∧
    (nonzeroEigenvalues K).Countable ∧
    (∀ ε : ℝ, 0 < ε →
      {s : multiplicitySlots K | ε ≤ ‖s.1.val‖}.Finite) ∧
    (∀ e : ℕ ≃ multiplicitySlots K,
      Tendsto (fun n => (e n).1.val) atTop (𝓝 0))

end Specs.D13Unified.Ch10.CompactSpectral
