import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.SingularApproximation
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.PositiveMinMax

/-! `fa2:p2:singular-system`, paper.tex 11362–11407. Lists index their strictly
positive entries by a lower subset of ℕ (manuscript index is n+1). Zero padding
belongs to the scalar sequence, not to the orthonormal families. -/
noncomputable section
universe u v w v₀ w₀
namespace ExpandedFA.CompactSpectral.CourantFischerSingularSystems.Spec
open scoped InnerProductSpace

variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

/-- The ordered vectors and the canonical singular numbers describe the same
system, including repetitions, finite lists, empty lists and arbitrary kernels. -/
def OrderedSingularList (T : H →L[𝕜] K) (I : Set ℕ)
    (v : I → H) (u : I → K) (a : I → ℝ) : Prop :=
  IsLowerSet I ∧ Orthonormal 𝕜 v ∧ Orthonormal 𝕜 u ∧
  (∀ i, 0 < a i) ∧ Antitone a ∧
  (∀ i, T (v i) = (a i : 𝕜) • u i) ∧
  (∀ i, T.adjoint (u i) = (a i : 𝕜) • v i) ∧
  (∀ x, HasSum (fun i => ((a i : 𝕜) * inner 𝕜 (v i) x) • u i) (T x)) ∧
  (Submodule.span 𝕜 (Set.range v)).topologicalClosure = T.ker.orthogonal ∧
  (∀ ε : ℝ, 0 < ε → {i : I | ε ≤ a i}.Finite) ∧
  (∀ n : ℕ, PositiveMinMax.Spec.paddedValue I a n =
    SingularApproximation.Spec.SingularValueValue T (n+1))

def OrderedSingularSystems : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∃ (I : Set ℕ) (v : I → H) (u : I → K) (a : I → ℝ),
      OrderedSingularList T I v u a

/-- All scalar sequence conclusions and the two displayed approximation/ideal
formulas, with cardinal rank excluding infinite-rank approximants. -/
def SingularNumberProperties : Prop :=
  SingularApproximation.Spec.SequenceProperties.{u,v,w} ∧
  SingularApproximation.Spec.RankCases.{u,v,w} ∧
  SingularApproximation.Spec.BestApproximation.{u,v,w} ∧
  SingularApproximation.Spec.SingularIdealInequality.{u,v,w,v₀,w₀}

/-- Unit-vector form of the two extrema. All conditional extrema have nonempty,
bounded domains at the admissible ambient dimensions. -/
def UnitCourantFischerAt (C : H →L[𝕜] H) (n : ℕ) (μ : ℝ) : Prop :=
  (∀ L, PositiveMinMax.Spec.TrialSpace L (n+1) →
    (PositiveMinMax.Spec.unitValues C L).Nonempty ∧
    BddBelow (PositiveMinMax.Spec.unitValues C L) ∧
    ∃ r, IsLeast (PositiveMinMax.Spec.unitValues C L) r) ∧
  (∀ M, PositiveMinMax.Spec.TrialSpace M n →
    (PositiveMinMax.Spec.unitValues C M.orthogonal).Nonempty ∧
    BddAbove (PositiveMinMax.Spec.unitValues C M.orthogonal)) ∧
  IsGreatest {r | ∃ L, PositiveMinMax.Spec.TrialSpace L (n+1) ∧
    sInf (PositiveMinMax.Spec.unitValues C L) = r} μ ∧
  IsLeast {r | ∃ M, PositiveMinMax.Spec.TrialSpace M n ∧
    sSup (PositiveMinMax.Spec.unitValues C M.orthogonal) = r} μ

/-- The attained-extremum formulation gives the displayed numerical equalities. -/
def UnitInfSupIdentities : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (C : H →L[𝕜] H) (n : ℕ) (μ : ℝ), UnitCourantFischerAt C n μ →
      μ = sInf {r | ∃ M, PositiveMinMax.Spec.TrialSpace M n ∧
        sSup (PositiveMinMax.Spec.unitValues C M.orthogonal) = r} ∧
      μ = sSup {r | ∃ L, PositiveMinMax.Spec.TrialSpace L (n+1) ∧
        sInf (PositiveMinMax.Spec.unitValues C L) = r}

/-- Real-part notation in the extrema retains the actual inner product for
self-adjoint (in particular positive) operators over either scalar field. -/
def QuadraticReal : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : H →L[𝕜] H), IsSelfAdjoint N → ∀ x : H,
      inner 𝕜 x (N x) = ((RCLike.re (inner 𝕜 x (N x)) : ℝ) : 𝕜)

def PositiveCourantFischer : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : H →L[𝕜] H), C.IsPositive →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue C.toLinearMap →
    ∃ (I : Set ℕ) (e : I → H) (a : I → ℝ),
      PositiveMinMax.Spec.PositiveSpectralList C I e a ∧
      ∀ n, PositiveMinMax.Spec.Admissible 𝕜 H n →
        UnitCourantFischerAt C n (PositiveMinMax.Spec.paddedValue I a n)

/-- For each sign, order precisely that sign's eigenvectors. At every listed
entry both minmax formulas hold for sign*N on the original Hilbert space.
For the negative list these give the negative eigenvalue formulas after reversing
order by negation. No claim pads past the positive spectrum of an indefinite
operator: only the positive-operator theorem pads to admissible dimensions. -/
def SignedCourantFischer : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : H →L[𝕜] H), IsSelfAdjoint N →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap →
    ∃ (J : Type u) (_ : Countable J) (e : J → H) (a : J → ℝ),
      Orthonormal 𝕜 e ∧
      (∀ j, a j ≠ 0 ∧ N (e j) = (a j : 𝕜) • e j) ∧
      (Submodule.span 𝕜 (Set.range e)).topologicalClosure = N.ker.orthogonal ∧
      (∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • e j) (N x)) ∧
      (∀ ε : ℝ, 0 < ε → {j | ε ≤ |a j|}.Finite) ∧
      ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        ∃ (I : Set ℕ) (b : I ≃ {j : J // 0 < sign * a j}),
          IsLowerSet I ∧ Antitone (fun i => sign * a (b i).val) ∧
          ∀ n (hn : n ∈ I), UnitCourantFischerAt ((sign : 𝕜) • N) n
            (sign * a (b ⟨n, hn⟩).val)

end ExpandedFA.CompactSpectral.CourantFischerSingularSystems.Spec
