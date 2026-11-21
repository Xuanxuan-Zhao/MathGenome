import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Order.Interval.Set.InitialSeg

/-! Independent statements for the positive min--max and reciprocal clauses of
`fa2:p2:ritz-approximation` and the positive Courant--Fischer clause of
`fa2:p2:singular-system`. Index n denotes the manuscript index k=n+1.
No finrank is assigned to an infinite-dimensional ambient space. -/
noncomputable section
universe u v
namespace ExpandedFA.CompactSpectral.PositiveMinMax.Spec
open scoped InnerProductSpace
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Equivalent to n+1 ≤ dim H, also in arbitrary infinite dimension. -/
def Admissible (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (n : ℕ) : Prop :=
  ∃ f : Fin (n+1) → H, LinearIndependent 𝕜 f

def TrialSpace (L : Submodule 𝕜 H) (k : ℕ) : Prop :=
  FiniteDimensional 𝕜 L ∧ Module.finrank 𝕜 L = k

/-- The manuscript's conjugate-first Rayleigh quotient, with its nonzero
argument imposed by rayleighValues. Real part is redundant for positive T. -/
def rayleigh (T : H →L[𝕜] H) (x : H) : ℝ :=
  RCLike.re (inner 𝕜 x (T x)) / ‖x‖ ^ 2

def rayleighValues (T : H →L[𝕜] H) (L : Submodule 𝕜 H) : Set ℝ :=
  {r | ∃ x ∈ L, x ≠ 0 ∧ rayleigh T x = r}

def unitValues (T : H →L[𝕜] H) (L : Submodule 𝕜 H) : Set ℝ :=
  {r | ∃ x ∈ L, ‖x‖ = 1 ∧ RCLike.re (inner 𝕜 x (T x)) = r}

def reciprocalValues (T : H →L[𝕜] H) (L : Submodule 𝕜 H) : Set ℝ :=
  {r | ∃ x ∈ L, x ≠ 0 ∧ (rayleigh T x)⁻¹ = r}

/-- Closed subspaces with exactly the stated finite algebraic codimension. -/
def ClosedCodimension (W : Submodule 𝕜 H) (n : ℕ) : Prop :=
  IsClosed (W : Set H) ∧ FiniteDimensional 𝕜 (H ⧸ W) ∧
    Module.finrank 𝕜 (H ⧸ W) = n

/-- Complete ordered list of the positive part; distinct orthonormal vectors
retain multiplicities. Its closed span and expansion retain the whole kernel. -/
def PositiveSpectralList (T : H →L[𝕜] H) (I : Set ℕ)
    (e : I → H) (a : I → ℝ) : Prop :=
  IsLowerSet I ∧ Orthonormal 𝕜 e ∧ (∀ i, 0 < a i) ∧ Antitone a ∧
  (∀ i, T (e i) = (a i : 𝕜) • e i) ∧
  (∀ x, HasSum (fun i => ((a i : 𝕜) * inner 𝕜 (e i) x) • e i) (T x)) ∧
  (Submodule.span 𝕜 (Set.range e)).topologicalClosure = T.ker.orthogonal ∧
  (∀ ε : ℝ, 0 < ε → {i : I | ε ≤ a i}.Finite) ∧
  (∀ r : ℕ, (FiniteDimensional 𝕜 T.range ∧ Module.finrank 𝕜 T.range = r) ↔
    I = Set.Iio r) ∧
  (∀ μ : ℝ, 0 < μ → Module.End.eigenspace T.toLinearMap (μ : 𝕜) =
    Submodule.span 𝕜 (e '' {i | a i = μ}))

/-- Zero padding is outside the complete positive list, never an additional
assumption that zero has an eigenvector below an inadmissible dimension. -/
def paddedValue (I : Set ℕ) (a : I → ℝ) (n : ℕ) : ℝ :=
  by classical exact if hn : n ∈ I then a ⟨n, hn⟩ else 0

/-- Every conditional extremum has its actual nonempty bounded domain. Inner
minima on finite trial spaces are attained; the outer maximum and minimum
are expressed by IsGreatest and IsLeast, so they are attained too. -/
def CourantFischerAt (T : H →L[𝕜] H) (n : ℕ) (μ : ℝ) : Prop :=
  (∀ L, TrialSpace L (n+1) →
    (rayleighValues T L).Nonempty ∧ BddBelow (rayleighValues T L) ∧
      ∃ r, IsLeast (rayleighValues T L) r) ∧
  (∀ M, TrialSpace M n →
    (rayleighValues T M.orthogonal).Nonempty ∧
      BddAbove (rayleighValues T M.orthogonal)) ∧
  IsGreatest {r | ∃ L, TrialSpace L (n+1) ∧ sInf (rayleighValues T L) = r} μ ∧
  IsLeast {r | ∃ M, TrialSpace M n ∧ sSup (rayleighValues T M.orthogonal) = r} μ

/-- Injectivity guarantees strict positivity both of the kth value and of
every nonzero quotient, so no displayed reciprocal divides by zero.
The second extremum ranges over all closed codimension-n subspaces. -/
def ReciprocalAt (T : H →L[𝕜] H) (n : ℕ) (μ : ℝ) : Prop :=
  0 < μ ∧ (∀ x, x ≠ 0 → 0 < rayleigh T x) ∧
  (∀ L, TrialSpace L (n+1) →
    (reciprocalValues T L).Nonempty ∧ BddAbove (reciprocalValues T L)) ∧
  (∀ W, ClosedCodimension W n →
    (reciprocalValues T W).Nonempty ∧ BddBelow (reciprocalValues T W)) ∧
  IsLeast {r | ∃ L, TrialSpace L (n+1) ∧ sSup (reciprocalValues T L) = r} μ⁻¹ ∧
  IsGreatest {r | ∃ W, ClosedCodimension W n ∧ sInf (reciprocalValues T W) = r} μ⁻¹

def OrderedPositiveSpectrum : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H), T.IsPositive →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∃ (I : Set ℕ) (e : I → H) (a : I → ℝ), PositiveSpectralList T I e a

/-- Full assigned obligation on the original real or complex Hilbert space,
including zero spaces, finite spectra, and nonseparable kernels. -/
def Principle : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H), T.IsPositive →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∃ (I : Set ℕ) (e : I → H) (a : I → ℝ), PositiveSpectralList T I e a ∧
      (∀ n, Admissible 𝕜 H n → CourantFischerAt T n (paddedValue I a n)) ∧
      (Function.Injective T → ∀ n, Admissible 𝕜 H n →
        ReciprocalAt T n (paddedValue I a n))

end ExpandedFA.CompactSpectral.PositiveMinMax.Spec
