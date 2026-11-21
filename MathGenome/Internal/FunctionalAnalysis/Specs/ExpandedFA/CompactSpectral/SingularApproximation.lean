import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.SingularExpansion
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
Independent interfaces for the approximation stage of `fa2:p2:singular-system`.
The index `n` is one-based: the admissible approximants have cardinal rank < n.
Cardinal rank, rather than `finrank` alone, excludes infinite-rank approximants.
The approximation-number construction is meaningful without compactness; its
identification with the spectrally defined singular sequence is stated below.
-/
noncomputable section
universe u v w v₀ w₀
namespace ExpandedFA.CompactSpectral.SingularApproximation.Spec

section Normed
variable {𝕜 : Type u} [RCLike 𝕜]
  {H : Type v} {K : Type w} [NormedAddCommGroup H] [NormedAddCommGroup K]
  [NormedSpace 𝕜 H] [NormedSpace 𝕜 K]

def ApproximationNumberType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K], (H →L[𝕜] K) → ℕ → ℝ

def ApproximationNumberValue : ApproximationNumberType.{u, v, w} :=
  fun {𝕜} _ {H} {K} _ _ _ _ T n => sInf {r : ℝ | ∃ F : H →L[𝕜] K,
    F.toLinearMap.rank < (n : Cardinal) ∧ r = ‖T - F‖}

def Nonnegative : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K] (T : H →L[𝕜] K) (n : ℕ),
    0 < n → 0 ≤ ApproximationNumberValue T n

def LowerBound : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K] (T F : H →L[𝕜] K) (n : ℕ),
    F.toLinearMap.rank < (n : Cardinal) → ApproximationNumberValue T n ≤ ‖T - F‖

def GreatestLowerBound : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K] (T : H →L[𝕜] K) (n : ℕ),
    0 < n → ∀ c : ℝ,
    (∀ F : H →L[𝕜] K, F.toLinearMap.rank < (n : Cardinal) → c ≤ ‖T - F‖) →
    c ≤ ApproximationNumberValue T n

def IdealInequality : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    (H₀ : Type v₀) (K₀ : Type w₀)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedAddCommGroup H₀] [NormedAddCommGroup K₀]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K]
    [NormedSpace 𝕜 H₀] [NormedSpace 𝕜 K₀]
    (T : H →L[𝕜] K) (A : K →L[𝕜] K₀) (B : H₀ →L[𝕜] H) (n : ℕ),
    0 < n → ApproximationNumberValue (A.comp (T.comp B)) n ≤
      ‖A‖ * ‖B‖ * ApproximationNumberValue T n

def RankVanishing : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K] (T : H →L[𝕜] K) (n : ℕ),
    0 < n → T.toLinearMap.rank < (n : Cardinal) → ApproximationNumberValue T n = 0

end Normed

section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜]
  {H : Type v} {K : Type w} [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

def TruncationType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T), Finset S.Index → H →L[𝕜] K

/-- The original finite singular expansion, as a bounded linear operator. -/
def TruncationValue (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (s : Finset S.Index) : H →L[𝕜] K :=
  ∑ j ∈ s, (innerSL 𝕜 (S.rightVector j)).smulRight ((S.sigma j : 𝕜) • S.leftVector j)

def TruncationRank : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], ∀ (T : H →L[𝕜] K) (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    (s : Finset S.Index), (TruncationValue T S s).toLinearMap.rank ≤ (s.card : Cardinal)

def TruncationOnRight : Prop := by
  classical
  exact ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], ∀ (T : H →L[𝕜] K) (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    (s : Finset S.Index) (j : S.Index),
    TruncationValue T S s (S.rightVector j) = if j ∈ s then T (S.rightVector j) else 0

def OmittedValueLowerBound : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], ∀ (T : H →L[𝕜] K) (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    (s : Finset S.Index) (j : S.Index), j ∉ s → S.sigma j ≤ ‖T - TruncationValue T S s‖

/-- Spectral order statistic: the infimum of positive thresholds above which
fewer than `n` positive singular directions remain. Each orthonormal direction
counts once, so repeated eigenvalues retain their multiplicities. -/
def SingularValueType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], (H →L[𝕜] K) → ℕ → ℝ

def SingularValueValue (T : H →L[𝕜] K) (n : ℕ) : ℝ :=
  sInf {c : ℝ | 0 < c ∧ ∃ S : SingularExpansion.Spec.SingularSystem 𝕜 H K T,
    {j | c < S.sigma j}.ncard < n}

/-- The spectral sequence has the original rank support, including finite rank,
zero spaces and arbitrary-dimensional kernels. -/
def SequenceProperties : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    (∀ n : ℕ, 0 < n → 0 ≤ SingularValueValue T n) ∧
    Antitone (fun n : ℕ => SingularValueValue T (n + 1)) ∧
    Filter.Tendsto (SingularValueValue T) Filter.atTop (nhds 0) ∧
    (∀ n : ℕ, 0 < n → (SingularValueValue T n = 0 ↔
      T.toLinearMap.rank < (n : Cardinal))) ∧
    (∀ n : ℕ, 0 < n → (0 < SingularValueValue T n ↔
      (n : Cardinal) ≤ T.toLinearMap.rank))

/-- Explicit finite-rank, infinite-rank and zero-operator specializations. -/
def RankCases : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    (FiniteDimensional 𝕜 T.range → ∀ n : ℕ, 0 < n →
      (0 < SingularValueValue T n ↔ n ≤ Module.finrank 𝕜 T.range) ∧
      (SingularValueValue T n = 0 ↔ Module.finrank 𝕜 T.range < n)) ∧
    (¬FiniteDimensional 𝕜 T.range → ∀ n : ℕ, 0 < n → 0 < SingularValueValue T n) ∧
    (T = 0 → ∀ n : ℕ, 0 < n → SingularValueValue T n = 0)

/-- Full best-approximation identity and attainment by a top spectral prefix. -/
def BestApproximation : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ n : ℕ, 0 < n →
      SingularValueValue T n = ApproximationNumberValue T n ∧
      ∀ S : SingularExpansion.Spec.SingularSystem 𝕜 H K T,
      ∃ q : Finset S.Index, q.card < n ∧
        (q.card = n - 1 ∨ ∀ j, j ∈ q) ∧
        (∀ i ∈ q, ∀ j, j ∉ q → S.sigma j ≤ S.sigma i) ∧
        (TruncationValue T S q).toLinearMap.rank < (n : Cardinal) ∧
        ‖T - TruncationValue T S q‖ = SingularValueValue T n ∧
        ((∀ j, j ∈ q) → TruncationValue T S q = T) ∧
        (T.toLinearMap.rank < (n : Cardinal) → TruncationValue T S q = T)

/-- Exact order statistics of every singular system, including repetitions. -/
def SpectralCounting : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ S : SingularExpansion.Spec.SingularSystem 𝕜 H K T,
      (∀ (c : ℝ), 0 < c → ∀ n : ℕ, 0 < n →
        (SingularValueValue T n ≤ c ↔ {j | c < S.sigma j}.ncard < n)) ∧
      (∀ (c : ℝ), 0 < c → ∀ n : ℕ, 0 < n →
        (c ≤ SingularValueValue T n ↔ n ≤ {j | c ≤ S.sigma j}.ncard)) ∧
      (∀ n : ℕ, 0 < n → 0 < SingularValueValue T n →
        ∃ j, SingularValueValue T n = S.sigma j)

/-- Positive entries are exactly the positive square roots of Gram eigenvalues,
with finite eigenspace multiplicity, in the original source and target spaces. -/
def SpectralMultiplicity : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ a : ℝ, 0 < a →
      FiniteDimensional 𝕜 (Module.End.eigenspace
        ((ContinuousLinearMap.adjoint T).comp T).toLinearMap ((a ^ 2 : ℝ) : 𝕜)) ∧
      (Module.End.HasEigenvalue ((ContinuousLinearMap.adjoint T).comp T).toLinearMap
        ((a ^ 2 : ℝ) : 𝕜) ↔ ∃ n : ℕ, 0 < n ∧ SingularValueValue T n = a) ∧
      {n : ℕ | 0 < n ∧ SingularValueValue T n = a}.Finite ∧
      {n : ℕ | 0 < n ∧ SingularValueValue T n = a}.ncard =
        Module.finrank 𝕜 (Module.End.eigenspace
          ((ContinuousLinearMap.adjoint T).comp T).toLinearMap ((a ^ 2 : ℝ) : 𝕜))

/-- No nonzero Gram eigenvalues are omitted by the spectral sequence. -/
def GramSpectrum : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ μ : 𝕜, μ ≠ 0 →
      (Module.End.HasEigenvalue ((ContinuousLinearMap.adjoint T).comp T).toLinearMap μ ↔
        ∃ n : ℕ, 0 < n ∧ 0 < SingularValueValue T n ∧
          μ = ((SingularValueValue T n ^ 2 : ℝ) : 𝕜))

def SingularIdealInequality : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    (H₀ : Type v₀) (K₀ : Type w₀)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedAddCommGroup H₀] [NormedAddCommGroup K₀]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [InnerProductSpace 𝕜 H₀] [InnerProductSpace 𝕜 K₀]
    [CompleteSpace H] [CompleteSpace K] [CompleteSpace H₀] [CompleteSpace K₀]
    (T : H →L[𝕜] K) (A : K →L[𝕜] K₀) (B : H₀ →L[𝕜] H),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ n : ℕ, 0 < n → SingularValueValue (A.comp (T.comp B)) n ≤
      ‖A‖ * ‖B‖ * SingularValueValue T n

end Hilbert
end ExpandedFA.CompactSpectral.SingularApproximation.Spec
