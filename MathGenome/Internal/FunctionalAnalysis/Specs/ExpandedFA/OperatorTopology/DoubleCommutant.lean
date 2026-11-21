import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.Definitions
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Independent statements for `fa2:p2:double-commutant`.
The topologies are the canonical Part I topologies, not operator norm topology.
`StarSubalgebra` is unital. No separability or nonzero-space assumption is made.
Adjunction is in fact WOT continuous on the whole operator space, which includes
its restriction to every norm-bounded subset. -/

namespace ExpandedFA.OperatorTopology.DoubleCommutantSpec
open scoped Topology InnerProductSpace
noncomputable section
universe u v

def ConvergenceTests : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : Type v) (l : Filter ι) (f : ι → H →L[ℂ] H) (T : H →L[ℂ] H),
    (Filter.Tendsto f l (@nhds _ (Spec.StrongTopologyValue ℂ H H) T) ↔
      ∀ x, Filter.Tendsto (fun i => f i x) l (𝓝 (T x))) ∧
    (Filter.Tendsto f l (@nhds _ (Spec.WeakTopologyValue ℂ H H) T) ↔
      ∀ x y, Filter.Tendsto (fun i => ⟪y, f i x⟫_ℂ) l (𝓝 ⟪y, T x⟫_ℂ))

def AdjointContinuous : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    @Continuous (H →L[ℂ] H) (H →L[ℂ] H)
      (Spec.WeakTopologyValue ℂ H H) (Spec.WeakTopologyValue ℂ H H) star

def SeparateMultiplication : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H),
    @Continuous (H →L[ℂ] H) (H →L[ℂ] H)
      (Spec.StrongTopologyValue ℂ H H) (Spec.StrongTopologyValue ℂ H H) (fun T => A * T) ∧
    @Continuous (H →L[ℂ] H) (H →L[ℂ] H)
      (Spec.StrongTopologyValue ℂ H H) (Spec.StrongTopologyValue ℂ H H) (fun T => T * A) ∧
    @Continuous (H →L[ℂ] H) (H →L[ℂ] H)
      (Spec.WeakTopologyValue ℂ H H) (Spec.WeakTopologyValue ℂ H H) (fun T => A * T) ∧
    @Continuous (H →L[ℂ] H) (H →L[ℂ] H)
      (Spec.WeakTopologyValue ℂ H H) (Spec.WeakTopologyValue ℂ H H) (fun T => T * A)

/-- One algebra element approximates all the prescribed vectors simultaneously. -/
def FiniteApproximation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H),
    T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) →
    ∀ (s : Finset H) (ε : ℝ), 0 < ε →
      ∃ a ∈ A, ∀ x ∈ s, ‖T x - a x‖ < ε

def DoubleCommutant : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)),
    @closure _ (Spec.StrongTopologyValue ℂ H H) (A : Set (H →L[ℂ] H)) =
      @closure _ (Spec.WeakTopologyValue ℂ H H) (A : Set (H →L[ℂ] H)) ∧
    @closure _ (Spec.WeakTopologyValue ℂ H H) (A : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))

/-! The original real-Hilbert-space case. These use real continuous linear
endomorphisms and real unital star subalgebras, with the same canonical
Part I topologies. No complex structure on H is required. The unchanged
complex statements above and these real statements together cover the
scalar convention in paper.tex:67–73. -/

def RealConvergenceTests : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : Type v) (l : Filter ι) (f : ι → H →L[ℝ] H) (T : H →L[ℝ] H),
    (Filter.Tendsto f l (@nhds _ (Spec.StrongTopologyValue ℝ H H) T) ↔
      ∀ x, Filter.Tendsto (fun i => f i x) l (𝓝 (T x))) ∧
    (Filter.Tendsto f l (@nhds _ (Spec.WeakTopologyValue ℝ H H) T) ↔
      ∀ x y, Filter.Tendsto (fun i => ⟪y, f i x⟫_ℝ) l (𝓝 ⟪y, T x⟫_ℝ))

def RealAdjointContinuous : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    @Continuous (H →L[ℝ] H) (H →L[ℝ] H)
      (Spec.WeakTopologyValue ℝ H H) (Spec.WeakTopologyValue ℝ H H) star

def RealSeparateMultiplication : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H),
    @Continuous (H →L[ℝ] H) (H →L[ℝ] H)
      (Spec.StrongTopologyValue ℝ H H) (Spec.StrongTopologyValue ℝ H H) (fun T => A * T) ∧
    @Continuous (H →L[ℝ] H) (H →L[ℝ] H)
      (Spec.StrongTopologyValue ℝ H H) (Spec.StrongTopologyValue ℝ H H) (fun T => T * A) ∧
    @Continuous (H →L[ℝ] H) (H →L[ℝ] H)
      (Spec.WeakTopologyValue ℝ H H) (Spec.WeakTopologyValue ℝ H H) (fun T => A * T) ∧
    @Continuous (H →L[ℝ] H) (H →L[ℝ] H)
      (Spec.WeakTopologyValue ℝ H H) (Spec.WeakTopologyValue ℝ H H) (fun T => T * A)

/-- Simultaneous approximation on the original real Hilbert space. -/
def RealFiniteApproximation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)) (T : H →L[ℝ] H),
    T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℝ] H))) →
    ∀ (s : Finset H) (ε : ℝ), 0 < ε →
      ∃ a ∈ A, ∀ x ∈ s, ‖T x - a x‖ < ε

def RealDoubleCommutant : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    @closure _ (Spec.StrongTopologyValue ℝ H H) (A : Set (H →L[ℝ] H)) =
      @closure _ (Spec.WeakTopologyValue ℝ H H) (A : Set (H →L[ℝ] H)) ∧
    @closure _ (Spec.WeakTopologyValue ℝ H H) (A : Set (H →L[ℝ] H)) =
      Set.centralizer (Set.centralizer (A : Set (H →L[ℝ] H)))


end
end ExpandedFA.OperatorTopology.DoubleCommutantSpec
