import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.NormalExpansion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.HilbertCardinalityClassification
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Independent statements for the complete corrected compact normal spectral
expansion and classification, `fa2:p2:compact-spectral`, paper.tex 11266ff.
Complex eigenspaces and real eigenvalue lines/rotation planes have distinct
interfaces. The real construction takes place on the original real space.
No separability, nonzero dimension or infinite-spectrum premise is imposed.
-/

noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.CompactSpectral.CompactNormalClassification.Spec
universe u v w

/-- A canonical choice of Hilbert basis, used only to express Hilbert dimension.
This is distinct from algebraic (Hamel) dimension in infinite dimension. -/
def basisSet (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] : Set H :=
  Classical.choose (exists_hilbertBasis 𝕜 H)

def chosenBasis (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] :
    HilbertBasis (basisSet 𝕜 H) 𝕜 H :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis 𝕜 H))

def hilbertDimension (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] : Cardinal.{v} :=
  Cardinal.mk (basisSet 𝕜 H)

/-- Equality of Hilbert dimensions is equivalent to existence of a unitary,
including arbitrary infinite dimensions and empty bases. -/
def DimensionClassification : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K],
    (Nonempty (H ≃ₗᵢ[𝕜] K) ↔
      Cardinal.lift.{w} (hilbertDimension 𝕜 H) =
      Cardinal.lift.{v} (hilbertDimension 𝕜 K))

/-- Multiplicity of the zero eigenvalue is the full Hilbert dimension of the
kernel. Nonzero multiplicities are the corresponding finite dimensions. -/
def eigenMultiplicity {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (N : H →L[ℂ] H) (α : ℂ) : Cardinal.{v} :=
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) :=
    (N.isClosed_eigenspace α).completeSpace_coe
  hilbertDimension ℂ (Module.End.eigenspace N.toLinearMap α)

/-- The complete complex expansion, with the previously established exact
projection definitions and all finite/empty cases. -/
def ComplexExpansion : Prop :=
  NormalEigenspaces.Spec.OrthogonalEigenspaces.{v} ∧
  NormalEigenspaces.Spec.FiniteDimensionalEigenspaces.{v} ∧
  NormalEigenspaces.Spec.CountableNonzeroEigenvalues.{v} ∧
  NormalEigenspaces.Spec.FiniteAwayFromZero.{v} ∧
  NormalExpansion.Spec.Decomposition.{v} ∧
  NormalExpansion.Spec.VectorExpansion.{v} ∧
  NormalExpansion.Spec.OperatorExpansion.{v} ∧
  NormalExpansion.Spec.OrderedExpansion.{v} ∧
  NormalExpansion.Spec.TailNorm.{v}

def ComplexClassification : Prop :=
  ∀ (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : H →L[ℂ] H) (M : K →L[ℂ] K),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue M.toLinearMap → IsStarNormal M →
    ((∃ U : H ≃ₗᵢ[ℂ] K, ∀ x, U (N x) = M (U x)) ↔
      ∀ α : ℂ, Cardinal.lift.{w} (eigenMultiplicity N α) =
        Cardinal.lift.{v} (eigenMultiplicity M α))

/-- The real eigenvalues of a complex self-adjoint operator. -/
def SelfAdjointEigenvaluesReal : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsSelfAdjoint N →
    ∀ (α : ℂ) (x : H), x ≠ 0 → N x = α • x → α.im = 0

/-- Eigenvector expansion on the original real or complex Hilbert space,
with the whole kernel retained. Real normality alone is deliberately absent. -/
def SelfAdjointExpansion : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : H →L[𝕜] H), IsSelfAdjoint N →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap →
    ∃ (ι : Type u) (_ : Countable ι) (e : ι → H) (a : ι → ℝ),
      Orthonormal 𝕜 e ∧ (∀ i, a i ≠ 0 ∧ N (e i) = (a i : 𝕜) • e i) ∧
      (Submodule.span 𝕜 (Set.range e)).topologicalClosure = N.ker.orthogonal ∧
      IsCompl N.ker (Submodule.span 𝕜 (Set.range e)).topologicalClosure ∧
      (∀ x, HasSum (fun i => ⟪e i, x⟫_𝕜 • e i)
        (x - (letI : CompleteSpace N.ker := N.isClosed_ker.completeSpace_coe;
          N.ker.starProjection x)) ∧
        HasSum (fun i => ((a i : 𝕜) * ⟪e i, x⟫_𝕜) • e i) (N x)) ∧
      (∀ μ : 𝕜, μ ≠ 0 → FiniteDimensional 𝕜 (Module.End.eigenspace N.toLinearMap μ)) ∧
      (∀ ε : ℝ, 0 < ε → {i | ε ≤ |a i|}.Finite)

/-- A positive-speed rotation plane is impossible for a real self-adjoint
operator: this rules out every B(a,b), b>0, in a block decomposition. -/
def NoSelfAdjointRotationPlane : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsSelfAdjoint N → ∀ (a b : ℝ) (e f : H),
    ‖e‖ = 1 → ‖f‖ = 1 → ⟪e, f⟫_ℝ = 0 →
    N e = a • e + b • f → N f = (-b) • e + a • f → b = 0

/-- The positive Gram operator is defined on the original real Hilbert space. -/
def gramOperator {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (N : H →L[ℝ] H) : H →L[ℝ] H :=
  N.adjoint.comp N

/-- A direct real-space reduction to finite-dimensional reducing summands.
This is a construction stage, not the complete line/plane theorem. -/
def RealModulusDecomposition : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    let G := gramOperator N
    IsSelfAdjoint G ∧ Compactness.DefinitionsSpec.IsCompactLinearMapValue G.toLinearMap ∧
      G.ker = N.ker ∧
      OrthogonalFamily ℝ (fun r : ℝ => Module.End.eigenspace G.toLinearMap r)
        (fun r => (Module.End.eigenspace G.toLinearMap r).subtypeₗᵢ) ∧
      (∀ r : ℝ, r ≠ 0 → FiniteDimensional ℝ (Module.End.eigenspace G.toLinearMap r)) ∧
      (∀ r : ℝ, Module.End.HasEigenvalue G.toLinearMap r → r ≠ 0 → 0 < r) ∧
      (∀ r : ℝ, Hilbert.Adjoint.Spec.ReducingSubspaceValue ℝ H
        (Module.End.eigenspace G.toLinearMap r) N) ∧
      (∀ (r : ℝ) (x : H), x ∈ Module.End.eigenspace G.toLinearMap r →
        ‖N x‖ ^ 2 = r * ‖x‖ ^ 2) ∧
      (⨆ r : {r : ℝ // r ≠ 0}, Module.End.eigenspace G.toLinearMap r.val).topologicalClosure =
        N.ker.orthogonal ∧
      {r : ℝ | Module.End.HasEigenvalue G.toLinearMap r ∧ r ≠ 0}.Countable ∧
      (∀ ε : ℝ, 0 < ε →
        {r : ℝ | Module.End.HasEigenvalue G.toLinearMap r ∧ ε ≤ Real.sqrt r}.Finite)

/-- A positive-speed real rotation plane, extracted without complexifying H. -/
def RealRotationPlaneExtraction : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N → ∀ (μ a : ℝ) (e : H),
    ‖e‖ = 1 → (∀ x, N.adjoint (N x) = μ • x) →
    N e + N.adjoint e = (2 * a) • e → N e - a • e ≠ 0 →
    ∃ (b : ℝ) (f : H), 0 < b ∧ ‖f‖ = 1 ∧ ⟪e, f⟫_ℝ = 0 ∧
      N e = a • e + b • f ∧ N f = (-b) • e + a • f ∧
      N.adjoint e = a • e - b • f ∧ N.adjoint f = b • e + a • f ∧
      a ^ 2 + b ^ 2 = μ

/-- The real quadratic selecting a conjugate pair a ± ib. -/
def pairOperator {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : H →L[ℝ] H) (a b : ℝ) : H →L[ℝ] H :=
  N * N - (2 * a) • N + (a * a + b * b) • 1

def pairMultiplicity {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : H →L[ℝ] H) (a b : ℝ) : ℕ :=
  Module.finrank ℝ (pairOperator N a b).ker / 2

def realEigenMultiplicity {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (N : H →L[ℝ] H) (r : ℝ) : Cardinal.{v} :=
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap r) :=
    (N.isClosed_eigenspace r).completeSpace_coe
  hilbertDimension ℝ (Module.End.eigenspace N.toLinearMap r)

/-- Real block witnesses on the original H.
The family is countable only off the kernel. -/
structure RealBlockData {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (N : H →L[ℝ] H) where
  LineIndex : Type
  PlaneIndex : Type
  line_countable : Countable LineIndex
  plane_countable : Countable PlaneIndex
  line : LineIndex → H
  first : PlaneIndex → H
  second : PlaneIndex → H
  eigenvalue : LineIndex → ℝ
  realPart : PlaneIndex → ℝ
  speed : PlaneIndex → ℝ
  eigenvalue_ne_zero : ∀ i, eigenvalue i ≠ 0
  speed_pos : ∀ j, 0 < speed j
  orthonormal : Orthonormal ℝ
    (Sum.elim line (fun q : PlaneIndex × Bool => if q.2 then second q.1 else first q.1))
  line_action : ∀ i, N (line i) = eigenvalue i • line i
  first_action : ∀ j, N (first j) = realPart j • first j + speed j • second j
  second_action : ∀ j, N (second j) = (-speed j) • first j + realPart j • second j
  closed_span : (Submodule.span ℝ (Set.range
    (Sum.elim line (fun q : PlaneIndex × Bool => if q.2 then second q.1 else first q.1)))).topologicalClosure = N.ker.orthogonal
  line_reducing : ∀ i, Hilbert.Adjoint.Spec.ReducingSubspaceValue ℝ H
    (Submodule.span ℝ {line i}) N
  plane_reducing : ∀ j, Hilbert.Adjoint.Spec.ReducingSubspaceValue ℝ H
    (Submodule.span ℝ {first j, second j}) N

namespace RealBlockData
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {N : H →L[ℝ] H}

def modulus (D : RealBlockData N) : D.LineIndex ⊕ D.PlaneIndex → ℝ :=
  Sum.elim (fun i => |D.eigenvalue i|)
    (fun j => Real.sqrt (D.realPart j ^ 2 + D.speed j ^ 2))

def projection (D : RealBlockData N) : D.LineIndex ⊕ D.PlaneIndex → H →L[ℝ] H :=
  Sum.elim (fun i => (innerSL ℝ (D.line i)).smulRight (D.line i))
    (fun j => (innerSL ℝ (D.first j)).smulRight (D.first j) +
      (innerSL ℝ (D.second j)).smulRight (D.second j))

def truncation (D : RealBlockData N) (s : Finset (D.LineIndex ⊕ D.PlaneIndex)) :
    H →L[ℝ] H := ∑ i ∈ s, N.comp (D.projection i)

def tailModuli (D : RealBlockData N) (s : Finset (D.LineIndex ⊕ D.PlaneIndex)) : Set ℝ :=
  D.modulus '' {i | i ∉ s}
end RealBlockData

/-- Full real expansion, including empty and finite block families. -/
def RealNormalExpansion : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    ∃ D : RealBlockData N,
      (∀ ε : ℝ, 0 < ε → {i | ε ≤ D.modulus i}.Finite) ∧
      (∀ x, HasSum (fun i => D.projection i x)
        (x - (letI : CompleteSpace N.ker := N.isClosed_ker.completeSpace_coe;
          N.ker.starProjection x)) ∧ HasSum (fun i => N (D.projection i x)) (N x)) ∧
      HasSum (fun i => N.comp (D.projection i)) N ∧
      (∀ s, ‖N - D.truncation s‖ = sSup (D.tailModuli s)) ∧
      ∃ s : ℕ → Finset (D.LineIndex ⊕ D.PlaneIndex), Monotone s ∧
        (∀ i, ∃ n, i ∈ s n) ∧
        (∀ n i, i ∈ s n → ∀ j, j ∉ s n → D.modulus j ≤ D.modulus i) ∧
        Filter.Tendsto (fun n => D.truncation (s n)) Filter.atTop (nhds N)

/-- Equality of real eigenvalue multiplicities, conjugate-pair multiplicities,
and the full real kernel Hilbert dimension characterizes orthogonal equivalence. -/
def RealNormalClassification : Prop :=
  ∀ (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (N : H →L[ℝ] H) (M : K →L[ℝ] K),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue M.toLinearMap → IsStarNormal M →
    ((∃ U : H ≃ₗᵢ[ℝ] K, ∀ x, U (N x) = M (U x)) ↔
      (∀ r : ℝ, Cardinal.lift.{w} (realEigenMultiplicity N r) =
        Cardinal.lift.{v} (realEigenMultiplicity M r)) ∧
      (∀ a b : ℝ, 0 < b → pairMultiplicity N a b = pairMultiplicity M a b))

/-- Intertwining preserves the listed invariants even without compactness. -/
def RealClassificationNecessary : Prop :=
  ∀ (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (N : H →L[ℝ] H) (M : K →L[ℝ] K),
    (∃ U : H ≃ₗᵢ[ℝ] K, ∀ x, U (N x) = M (U x)) →
      (∀ r : ℝ, Cardinal.lift.{w} (realEigenMultiplicity N r) =
        Cardinal.lift.{v} (realEigenMultiplicity M r)) ∧
      (∀ a b : ℝ, 0 < b → pairMultiplicity N a b = pairMultiplicity M a b)

def RealPairKernelFinite : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap →
    ∀ a b : ℝ, 0 < b → FiniteDimensional ℝ (pairOperator N a b).ker

def SelfAdjointPairKernelZero : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsSelfAdjoint N →
    ∀ a b : ℝ, 0 < b → (pairOperator N a b).ker = ⊥

/-- The analytic part applies to every given orthogonal block decomposition;
the complete theorem must also construct those blocks from N. -/
def RealOrthogonalBlockExpansion : Prop :=
  ∀ (H : Type v) (ι : Type w) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (V : ι → Submodule ℝ H) [∀ i, (V i).HasOrthogonalProjection],
    OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ) →
    ∀ (N : H →L[ℝ] H), (∀ i, ∀ y ∈ V i, N y ∈ V i) →
    ∀ r : ι → ℝ, (∀ i, 0 < r i) → (∀ i, V i ≠ ⊥) →
    (∀ i, ∀ y ∈ V i, ‖N y‖ = r i * ‖y‖) →
    ((⨆ i, V i).topologicalClosure).orthogonal ≤ N.ker →
    (∀ ε : ℝ, 0 < ε → {i | ε ≤ r i}.Finite) →
      (∀ x, HasSum (fun i => N ((V i).starProjection x)) (N x)) ∧
      (∀ s : Finset ι, ‖N - ∑ i ∈ s, N.comp (V i).starProjection‖ =
        sSup (r '' {i | i ∉ s})) ∧
      HasSum (fun i => N.comp (V i).starProjection) N ∧
      ∃ s : ℕ → Finset ι, Monotone s ∧ (∀ i, ∃ n, i ∈ s n) ∧
        (∀ n i, i ∈ s n → ∀ j, j ∉ s n → r j ≤ r i) ∧
        Filter.Tendsto (fun n => ∑ i ∈ s n, N.comp (V i).starProjection)
          Filter.atTop (nhds N)

end ExpandedFA.CompactSpectral.CompactNormalClassification.Spec
