import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.PositiveAdjointProduct
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalSpectral

/-! The bounded-piece construction in paper.tex:13893–13920. Normality means
equality of the partial products, including their domains. No resolvent point,
separability, or nonzero-space hypothesis is present. -/
noncomputable section
open scoped InnerProductSpace
open Set Filter
namespace ExpandedFA.Unbounded.NormalBoundedSpectralPiecesSpec
open OperatorDomainsSpec HilbertAdjointSpec PositiveAdjointProductSpec
open SpectralMeasure
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- All identities refer to the same inverse B and bounded transform C = NB.
The equations on D(N) and D(N*) include domain preservation explicitly. -/
structure TransformLaws (N : Operator ℂ H H) (B C : H →L[ℂ] H) : Prop where
  inverse_right : ∀ f : H, ∃ hx : B f ∈ (adjointProduct N).domain,
    B f + adjointProduct N ⟨B f, hx⟩ = f
  inverse_left : ∀ x : (adjointProduct N).domain,
    B ((x : H) + adjointProduct N x) = (x : H)
  injective : Function.Injective B
  selfAdjoint : B.adjoint = B
  contractive : ‖B‖ ≤ 1
  nonnegative : ∀ f : H, 0 ≤ (inner ℂ f (B f)).re
  transform : ∀ f : H, ∃ hf : B f ∈ N.domain, C f = N ⟨B f, hf⟩
  adjoint_transform : ∀ f : H, ∃ hf : B f ∈ (adjointValue N).domain,
    C.adjoint f = adjointValue N ⟨B f, hf⟩
  commute_domain : ∀ x : N.domain, ∃ hx : B x ∈ N.domain,
    N ⟨B x, hx⟩ = B (N x)
  commute_adjoint_domain : ∀ x : (adjointValue N).domain,
    ∃ hx : B x ∈ (adjointValue N).domain,
      adjointValue N ⟨B x, hx⟩ = B (adjointValue N x)
  commute : Commute B C
  normal : IsStarNormal C

def BoundedTransforms : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Operator ℂ H H), Dense (N.domain : Set H) → N.IsClosed →
    productValue (adjointValue N) N = productValue N (adjointValue N) →
    ∃ B C : H →L[ℂ] H, TransformLaws N B C

/-- A reducing bounded normal restriction on the range of the specified
projection. The range is closed, so the normality assertion uses precisely
its induced Hilbert-space structure. -/
structure ReducingPiece (N : Operator ℂ H H) (Q : H →L[ℂ] H) (r : ℝ) where
  closed_range : IsClosed (Q.range : Set H)
  T : Q.range →L[ℂ] Q.range
  domain : Q.range ≤ N.domain
  adjoint_domain : Q.range ≤ (adjointValue N).domain
  evaluation : ∀ x : Q.range, (T x : H) = N ⟨x, domain x.property⟩
  adjoint_evaluation : letI : CompleteSpace Q.range :=
      closed_range.isComplete.completeSpace_coe
    ∀ x : Q.range, (T.adjoint x : H) = adjointValue N ⟨x, adjoint_domain x.property⟩
  normal : letI : CompleteSpace Q.range := closed_range.isComplete.completeSpace_coe
    IsStarNormal T
  norm_bound : ‖T‖ ≤ r
  reduces : ∀ x : N.domain, ∃ hx : Q x ∈ N.domain,
    N ⟨Q x, hx⟩ = Q (N x)
  reduces_adjoint : ∀ x : (adjointValue N).domain,
    ∃ hx : Q x ∈ (adjointValue N).domain,
      adjointValue N ⟨Q x, hx⟩ = Q (adjointValue N x)

/-- Spectral cutoffs are subsets of the actual complex spectrum of B; B is
positive, so its coordinate is real and lies in [0,1]. -/
def cutoff (B : H →L[ℂ] H) (δ : ℝ) : Set (spectrum ℂ B) :=
  {z | δ ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1}

/-- The n=0 band is (1/2,1], so the bands partition (0,1]. -/
def band (B : H →L[ℂ] H) (n : ℕ) : Set (spectrum ℂ B) :=
  {z | 1 / ((n : ℝ) + 2) < (z : ℂ).re ∧ (z : ℂ).re ≤ 1 / ((n : ℝ) + 1)}

/-- Complete construction, including the exact square-summability domain and
graph of the orthogonal sum. Neither assertion presupposes any unbounded PVM.
The maps R n are ambient extensions T_n P_n of the restrictions, allowing
the graph identity to be stated without a choice of Hilbert direct-sum model. -/
def BoundedSpectralPieces : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Operator ℂ H H), Dense (N.domain : Set H) → N.IsClosed →
    productValue (adjointValue N) N = productValue N (adjointValue N) →
    ∃ (B C : H →L[ℂ] H) (P : ProjectionValuedMeasure (spectrum ℂ B) H),
      TransformLaws N B C ∧ SpectralMeasure.NormalPVM.Spec.Resolves B P ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        Nonempty (ReducingPiece N (P (cutoff B δ)) (Real.sqrt ((1 - δ) / δ)))) ∧
      (∀ S : Set (spectrum ℂ B), MeasurableSet S → Commute C (P S)) ∧
      ∃ R : ℕ → H →L[ℂ] H,
        (∀ n, ∃ p : ReducingPiece N (P (band B n)) (Real.sqrt ((n : ℝ) + 1)),
          ∀ x : H, R n x = (p.T ⟨P (band B n) x, ⟨x, rfl⟩⟩ : H)) ∧
        (∀ n m, n ≠ m → ∀ x y : H,
          inner ℂ (P (band B n) x) (P (band B m) y) = 0) ∧
        (∀ x : H, HasSum (fun n => P (band B n) x) x) ∧
        (∀ x : H, x ∈ N.domain ↔ Summable (fun n => ‖R n x‖ ^ 2)) ∧
        (∀ x y : H, (x, y) ∈ N.graph ↔
          Summable (fun n => ‖R n x‖ ^ 2) ∧ HasSum (fun n => R n x) y)

end ExpandedFA.Unbounded.NormalBoundedSpectralPiecesSpec
