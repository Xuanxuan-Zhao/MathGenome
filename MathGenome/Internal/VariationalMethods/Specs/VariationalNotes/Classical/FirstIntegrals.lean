import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.InnerTimeVariation

/-! Independent statements for paper.tex, Proposition `beltrami`, lines 3271–3294.
All endpoint derivatives are within derivatives of the shared closed-interval jet.
The ambient zero extensions have no prescribed derivatives outside the interval. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace VariationalNotes.Classical.FirstIntegrals

/-- The momentum, expressed as a field for differentiation in time. -/
def momentumField {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m)
    (t : ℝ) : State m :=
  (InnerProductSpace.toDual ℝ (State m)).symm
    (fderiv ℝ (fun v => L.value (t, stateField I m u t, v)) (velocityField I m u t))

def stateGradientField {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m)
    (t : ℝ) : State m :=
  (InnerProductSpace.toDual ℝ (State m)).symm
    (fderiv ℝ (fun z => L.value (t, z, velocityField I m u t)) (stateField I m u t))

/-- The classical hypothesis on p: C¹ up to the endpoints, and p′ = L_z in the interior. -/
def EulerLagrange {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m) : Prop :=
  ContDiffOn ℝ 1 (momentumField L u) (Icc I.a I.b) ∧
    ∀ t ∈ Ioo I.a I.b,
      HasDerivAt (momentumField L u) (stateGradientField L u t) t

/-- Independence of time wherever both time–state–velocity points are admissible. -/
def Autonomous {m : ℕ} (L : Lagrangian m) : Prop :=
  ∀ (t r : ℝ) (z v : State m), (t, z, v) ∈ L.domain → (r, z, v) ∈ L.domain →
    L.value (r, z, v) = L.value (t, z, v)

/-- Independence of the i-th state coordinate on the Lagrangian domain. -/
def IgnorableCoordinate {m : ℕ} (L : Lagrangian m) (i : Fin m) : Prop :=
  ∀ (t : ℝ) (z v : State m) (s : ℝ), (t, z, v) ∈ L.domain →
    (t, z + s • EuclideanSpace.single i 1, v) ∈ L.domain →
    L.value (t, z + s • EuclideanSpace.single i 1, v) = L.value (t, z, v)

end VariationalNotes.Classical.FirstIntegrals

namespace Specs.VariationalNotes.Classical.FirstIntegrals
open _root_.VariationalNotes.Classical
open _root_.VariationalNotes.Classical.InnerTime
open _root_.VariationalNotes.Classical.FirstIntegrals

def energyIdentity : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → EulerLagrange L u →
    (ContDiffOn ℝ 2 (stateField I m u) (Icc I.a I.b) ∨ innerTimeStationary L u) →
    ContDiffOn ℝ 1 (energy L u) (Icc I.a I.b) ∧
    (∀ t ∈ Icc I.a I.b,
      HasDerivWithinAt (energy L u) (timePartial L u t) (Icc I.a I.b) t) ∧
    (∀ t ∈ Ioo I.a I.b, HasDerivAt (energy L u) (timePartial L u t) t)

def autonomousEnergyConstant : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → EulerLagrange L u →
    (ContDiffOn ℝ 2 (stateField I m u) (Icc I.a I.b) ∨ innerTimeStationary L u) →
    Autonomous L → ∀ t ∈ Icc I.a I.b, energy L u t = energy L u I.a

/-- No C² or inner-time assumption is needed for the ignorable-coordinate consequence. -/
def ignorableMomentumConstant : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → EulerLagrange L u →
    ∀ i : Fin m, IgnorableCoordinate L i →
    ∀ t ∈ Icc I.a I.b, momentumField L u t i = momentumField L u I.a i

end Specs.VariationalNotes.Classical.FirstIntegrals
