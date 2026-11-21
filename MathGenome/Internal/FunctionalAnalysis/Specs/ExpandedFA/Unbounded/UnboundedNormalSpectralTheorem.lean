import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.NormalBoundedSpectralPieces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.ArbitraryCyclicSum

/-!
Independent statements for paper.tex, `fa2:p3:normal-spectral` (13864–13932).
Normality is equality of partial products, including their domains. The
spectrum uses bounded everywhere-defined two-sided inverses in the ambient
Hilbert norm. No resolvent point, countability, separability, nonzero vector,
or common finite scalar control measure is assumed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace

namespace ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
open SpectralMeasure MeasurableSpectralCalculus
open OperatorDomainsSpec HilbertAdjointSpec
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complement of the source's bounded-inverse resolvent set. -/
def operatorSpectrum (N : Operator ℂ H H) : Set ℂ :=
  (resolventSetValue N)ᶜ

/-- Canonical integral representation; equality here includes the exact domain.
Square integrability is the nonnegative integral condition, without the
Bochner integral's totalization outside its integrability domain. -/
def Resolves (N : Operator ℂ H H) (E : ProjectionValuedMeasure ℂ H) : Prop :=
  ∃ C : BoundedRealization E,
    measurableIntegral C (fun z : ℂ => z) = N ∧
    ∀ x : H, x ∈ N.domain ↔ SquareIntegrable C (fun z : ℂ => z) x

/-- PVMs are compared on Borel sets only: their values on nonmeasurable
sets are deliberately unconstrained by the shared PVM definition. -/
def SameBorelValues (E F : ProjectionValuedMeasure ℂ H) : Prop :=
  ∀ S : Set ℂ, MeasurableSet S → E S = F S

/-- Both parts of the support assertion, for the actual unbounded spectrum. -/
def SpectralSupport (N : Operator ℂ H H) (E : ProjectionValuedMeasure ℂ H) : Prop :=
  _root_.IsClosed (operatorSpectrum N) ∧ E (operatorSpectrum N)ᶜ = 0 ∧
    ∀ U : Set ℂ, IsOpen U → (U ∩ operatorSpectrum N).Nonempty → E U ≠ 0

/-- The bounded direct-sum statement with its precise domain and graph.
The maps R n are the ambient extensions T_n Q_n. -/
structure BoundedDecomposition (N : Operator ℂ H H) where
  Q : ℕ → H →L[ℂ] H
  piece : ∀ n, NormalBoundedSpectralPiecesSpec.ReducingPiece N (Q n)
    (Real.sqrt ((n : ℝ) + 1))
  projection : ∀ n, IsSelfAdjoint (Q n) ∧ Q n * Q n = Q n
  R : ℕ → H →L[ℂ] H
  evaluation : ∀ n x, R n x = (piece n).T ⟨Q n x, ⟨x, rfl⟩⟩
  orthogonal : ∀ n m, n ≠ m → ∀ x y, inner ℂ (Q n x) (Q m y) = 0
  complete : ∀ x, HasSum (fun n => Q n x) x
  domain : ∀ x, x ∈ N.domain ↔ Summable (fun n => ‖R n x‖ ^ 2)
  graph : ∀ x y, (x, y) ∈ N.graph ↔
    Summable (fun n => ‖R n x‖ ^ 2) ∧ HasSum (fun n => R n x) y

/-- The real PVM is an actual PVM on ℝ, with the real coordinate embedded
in ℂ in its spectral integral. -/
def RealResolves (N : Operator ℂ H H) (E : ProjectionValuedMeasure ℝ H) : Prop :=
  ∃ C : BoundedRealization E,
    measurableIntegral C (fun t : ℝ => (t : ℂ)) = N ∧
    ∀ x : H, x ∈ N.domain ↔ SquareIntegrable C (fun t : ℝ => (t : ℂ)) x

/-- An actual unitary representation on native L² of a disjoint union of
finite-measure spaces. The index set may be uncountable and the symbol
unbounded. MemLp records the maximal multiplication domain. -/
def MultiplicationModel (N : Operator ℂ H H) : Prop :=
  ∃ (I : Type u) (S : I → Type) (m : ∀ i, MeasurableSpace (S i))
    (μ : ∀ i, @Measure (S i) (m i)),
    letI := m
    (∀ i, IsFiniteMeasure (μ i)) ∧
    ∃ g : Sigma S → ℂ, Measurable g ∧
    ∃ U : Lp ℂ 2 (ArbitraryCyclicSum.Spec.disjointMeasure μ) ≃ₗᵢ[ℂ] H,
      (∀ f : Lp ℂ 2 (ArbitraryCyclicSum.Spec.disjointMeasure μ),
        U f ∈ N.domain ↔ MemLp (fun s => g s * f s) 2
          (ArbitraryCyclicSum.Spec.disjointMeasure μ)) ∧
      (∀ x : N.domain, U.symm (N x) =ᵐ[ArbitraryCyclicSum.Spec.disjointMeasure μ]
        fun s => g s * (U.symm (x : H)) s)

namespace Spec

/-- Existence alone is separated from uniqueness and support for proof reuse. -/
def SpectralExistence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Operator ℂ H H), Dense (N.domain : Set H) → N.IsClosed →
    productValue (adjointValue N) N = productValue N (adjointValue N) →
    ∃ E : ProjectionValuedMeasure ℂ H, Resolves N E

/-- Every representation has the support assertion and is unique on Borel sets. -/
def SpectralUniquenessAndSupport : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Operator ℂ H H), Dense (N.domain : Set H) → N.IsClosed →
    productValue (adjointValue N) N = productValue N (adjointValue N) →
    ∀ E : ProjectionValuedMeasure ℂ H, Resolves N E →
      SpectralSupport N E ∧ ∀ F : ProjectionValuedMeasure ℂ H,
        Resolves N F → SameBorelValues E F

def BoundedDecompositionExists : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Operator ℂ H H), Dense (N.domain : Set H) → N.IsClosed →
    productValue (adjointValue N) N = productValue N (adjointValue N) →
    Nonempty (BoundedDecomposition N)

/-- Real support and the genuine real-base PVM, with its precise domain. -/
def SelfAdjointSpectralTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Operator ℂ H H), Dense (N.domain : Set H) → N.IsClosed →
    adjointValue N = N →
    (∃ E : ProjectionValuedMeasure ℝ H, RealResolves N E) ∧
    (∀ E : ProjectionValuedMeasure ℂ H, Resolves N E → E {z | z.im ≠ 0} = 0)

def MultiplicationTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Operator ℂ H H), Dense (N.domain : Set H) → N.IsClosed →
    productValue (adjointValue N) N = productValue N (adjointValue N) →
    MultiplicationModel N

/-- Complete source obligation, including all three concluding specializations. -/
def FullTheorem : Prop :=
  SpectralExistence.{u} ∧ SpectralUniquenessAndSupport.{u} ∧
  SelfAdjointSpectralTheorem.{u} ∧ BoundedDecompositionExists.{u} ∧
  MultiplicationTheorem.{u}

end Spec
end ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
