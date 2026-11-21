import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.DoubleCommutant
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.ScalarMultiplicationCommutant

/-!
Independent statements for the cyclic/separating stage of
`fa2:p2:abelian-von-neumann`, paper.tex 12082–12115.
A star subalgebra is unital. All Hilbert spaces in the existence assertions
are separable, and may be zero. The scalar measure need not have positive mass.
The normal-operator control measure and weak-star topology assertions are
allocated separately to `mid_p2_abelian_von_neumann`.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.VonNeumann.SeparableMASA.Spec
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commutativity in the original operator algebra. -/
def IsAbelian (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a * b = b * a

/-- Closedness for the shared weak operator topology, not the operator norm. -/
def IsWOTClosed (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  @IsClosed _ (OperatorTopology.Spec.WeakTopologyValue ℂ H H) (A : Set (H →L[ℂ] H))

/-- A maximal abelian algebra, among all unital star subalgebras. -/
def IsMaximalAbelian (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  IsAbelian A ∧ ∀ B : StarSubalgebra ℂ (H →L[ℂ] H), IsAbelian B → A ≤ B → B = A

/-- The source hypothesis. Maximality among WOT-closed abelian algebras is
also sufficient; the implementation proves this equivalence explicitly. -/
def IsMASA (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  IsMaximalAbelian A ∧ IsWOTClosed A

/-- The orbit is already a complex linear subspace, so this is the usual
cyclic-vector condition. -/
def IsCyclic (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H) : Prop :=
  DenseRange (fun a : A => (a : H →L[ℂ] H) e)

/-- Separating means faithful evaluation on the concrete algebra. -/
def IsSeparating (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H) : Prop :=
  ∀ T ∈ A, T e = 0 → T = 0

/-- Exact equality after unitary transport with all L∞ multiplication
operators, on the native L² of a finite positive measure. Both implications
are part of the assertion; no representation on a proper subspace suffices.
The carrier universe agrees with H, allowing arbitrary Hilbert universes. -/
def HasScalarModel (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (hμ : IsFiniteMeasure μ),
    letI := hμ
    ∃ U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ T : H →L[ℂ] H, T ∈ A ↔
        ∃ h : Lp ℂ ∞ μ, ∀ x : H,
          U (T x) = ScalarMultiplicationCommutant.Spec.multiplier μ h (U x)

/-- The full cyclic-vector existence statement, including the zero space. -/
def MASACyclic : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (A : StarSubalgebra ℂ (H →L[ℂ] H)),
    IsMASA A → ∃ e : H, IsCyclic A e

/-- The entire multiplication algebra, not just a faithful multiplication
representation of a proper subalgebra. -/
def MASAScalarRepresentation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (A : StarSubalgebra ℂ (H →L[ℂ] H)),
    IsMASA A → HasScalarModel A

/-- Separability applies to this source sentence too. -/
def AbelianSeparating : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (A : StarSubalgebra ℂ (H →L[ℂ] H)),
    IsAbelian A → IsWOTClosed A → ∃ e : H, IsSeparating A e

/-! Real cyclicity and separation take place on the original real operator
algebra. They require no scalar multiplication representation or complex
structure on the original Hilbert space. -/
section RealScalar
variable {HR : Type u} [NormedAddCommGroup HR] [InnerProductSpace ℝ HR]
  [CompleteSpace HR]

/-- Pairwise commutation of actual real bounded endomorphisms. -/
def RealIsAbelian (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a * b = b * a

/-- Closedness for the canonical real weak operator topology. -/
def RealIsWOTClosed (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) : Prop :=
  @IsClosed _ (OperatorTopology.Spec.WeakTopologyValue ℝ HR HR)
    (A : Set (HR →L[ℝ] HR))

/-- Maximality among real abelian unital star subalgebras. -/
def RealIsMaximalAbelian (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) : Prop :=
  RealIsAbelian A ∧
    ∀ B : StarSubalgebra ℝ (HR →L[ℝ] HR), RealIsAbelian B → A ≤ B → B = A

def RealIsMASA (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) : Prop :=
  RealIsMaximalAbelian A ∧ RealIsWOTClosed A

/-- The real algebra orbit is dense in the original real Hilbert space. -/
def RealIsCyclic (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) (e : HR) : Prop :=
  DenseRange (fun a : A => (a : HR →L[ℝ] HR) e)

/-- Faithful evaluation on the original real algebra. -/
def RealIsSeparating (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) (e : HR) : Prop :=
  ∀ T ∈ A, T e = 0 → T = 0

/-- The valid original-real MASA conclusion, including the zero space. -/
def RealMASACyclic : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    RealIsMASA A → ∃ e : H, RealIsCyclic A e

/-- The valid original-real abelian von Neumann algebra conclusion. -/
def RealAbelianSeparating : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    RealIsAbelian A → RealIsWOTClosed A → ∃ e : H, RealIsSeparating A e

end RealScalar

end ExpandedFA.VonNeumann.SeparableMASA.Spec
