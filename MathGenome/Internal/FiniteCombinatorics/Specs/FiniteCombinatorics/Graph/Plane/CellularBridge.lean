import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.Incidence
import Mathlib.LinearAlgebra.Matrix.Rank
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularDegrees
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficientsCohomology

/-! Independent statements for the cellular bridge in W62. The CW structure is
on the original sphere subspace. Cellular groups are actual skeletal relative
singular homology, and all homology/cohomology groups below use ordinary singular
chains and their unrestricted algebraic dual. -/

universe u
noncomputable section

namespace Specs.FiniteCombinatorics.Graph.Plane.CellularBridge
open _root_.FiniteCombinatorics.Graph.Trees
open Specs.FiniteCombinatorics.Graph.Trees.Incidence

/-- The actual signed incidence map on rational edge coefficients. -/
def incidenceMap {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet]
    (o : EdgeOrientation G) : (G.edgeSet → ℚ) →ₗ[ℚ] (V → ℚ) :=
  (incidenceValue G ℚ o).mulVecLin

def transposeIncidenceMap {V : Type u} [Fintype V] (G : SimpleGraph V)
    (o : EdgeOrientation G) : (V → ℚ) →ₗ[ℚ] (G.edgeSet → ℚ) :=
  (incidenceValue G ℚ o).transpose.mulVecLin

def transpose_applyType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (o : EdgeOrientation G)
    (f : V → ℚ) (e : G.edgeSet),
    transposeIncidenceMap G o f e = f (o.head e) - f (o.tail e)

def transpose_kernelType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (o : EdgeOrientation G) (f : V → ℚ),
    f ∈ LinearMap.ker (transposeIncidenceMap G o) ↔
      ∀ a b : V, G.Reachable a b → f a = f b

def transpose_kernel_equivType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (o : EdgeOrientation G),
    ∃ E : (G.ConnectedComponent → ℚ) ≃ₗ[ℚ] LinearMap.ker (transposeIncidenceMap G o),
      ∀ f v, (E f).val v = f (G.connectedComponentMk v)

def transpose_kernel_finrankType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (o : EdgeOrientation G),
    Module.finrank ℚ (LinearMap.ker (transposeIncidenceMap G o)) =
      Nat.card G.ConnectedComponent

def incidence_rankType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (o : EdgeOrientation G),
    Module.finrank ℚ (LinearMap.range (incidenceMap G o)) =
      Nat.card V - Nat.card G.ConnectedComponent

/-- Addition precedes natural subtraction to cover disconnected and empty graphs. -/
def incidence_nullityType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (o : EdgeOrientation G),
    Module.finrank ℚ (LinearMap.ker (incidenceMap G o)) =
      Nat.card G.edgeSet + Nat.card G.ConnectedComponent - Nat.card V

def incidence_kernel_dual_finrankType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (o : EdgeOrientation G),
    Module.finrank ℚ (Module.Dual ℚ (LinearMap.ker (incidenceMap G o))) =
      Nat.card G.edgeSet + Nat.card G.ConnectedComponent - Nat.card V

/-- Evaluation on the actual quotient cohomology of an arbitrary rational chain
complex. This uses unrestricted algebraic cochains, not finite-support duals. -/
def rational_quotient_evaluationType : Prop :=
  ∀ (C : ChainComplex (ModuleCat.{u} ℚ) ℤ) (n : ℤ),
    Function.Bijective
      (P202Specs.UniversalCoefficientsCohomology.quotientEvaluation ℚ ℚ C n)

/-- The rational universal-coefficient comparison, on the categorical homology
objects of the fixed complex and its actual algebraic dual complex. Applying
this to the ordinary singular chain complex includes the empty space. -/
def rational_evaluationType : Prop :=
  ∀ (C : ChainComplex (ModuleCat.{u} ℚ) ℤ) (n : ℤ),
    Function.Bijective
      (P202Specs.UniversalCoefficientsCohomology.evaluation ℚ ℚ C n)

/-- Actual singular cohomology of the sphere realization, with its canonical
evaluation on singular homology. No nonemptiness assumption is imposed. -/
def realization_universal_coefficientsType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Specs.FiniteCombinatorics.Graph.Plane.Foundations.Drawing G),
    let X := TopCat.of (Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.Realization D)
    ∃ E : P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ X 1 ≃ₗ[ℚ]
        Module.Dual ℚ (P202Specs.SingularChains.homology ℚ ℚ X 1),
      ∀ a, E a = P202Specs.UniversalCoefficientsCohomology.evaluation ℚ ℚ
        (P202Specs.SingularChains.ordinaryComplex ℚ ℚ X) 1 a

/-- Genuine finite CW cells on the original sphere subspace, with their
geometric images and the endpoints of the oriented characteristic intervals. -/
def embedded_cwType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Specs.FiniteCombinatorics.Graph.Plane.Foundations.Drawing G) (o : EdgeOrientation G),
    ∃ (C : P202.Cellular.CWStructure
        (Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.Realization D))
      (h : P202Specs.CellularDegrees.IntervalParametrization),
      letI := C
      let X := Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.Realization D
      ∃ (ev : P202.Cellular.Cell X 0 ≃ V) (ee : P202.Cellular.Cell X 1 ≃ G.edgeSet),
        Finite (Σ n, P202.Cellular.Cell X n) ∧
        (∀ n, IsEmpty (P202.Cellular.Cell X (n+2))) ∧
        (∀ c x, P202.Cellular.characteristic X 0 c x =
          Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.realizationVertex D (ev c)) ∧
        (∀ c, Subtype.val '' Set.range (P202.Cellular.characteristic X 1 c) =
          OnePoint.some '' D.edge (ee c)) ∧
        (∀ c, P202.Cellular.characteristic X 1 c (h.endpoint.{0} 0).val.down =
            Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.realizationVertex D (o.head (ee c)) ∧
          P202.Cellular.characteristic X 1 c (h.endpoint.{0} 1).val.down =
            Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.realizationVertex D (o.tail (ee c)))

open P202.Cellular P202Specs.CellularChains P202Specs.CellularDegrees
open P202Specs.RelativeSingularChains
open Specs.FiniteCombinatorics.Graph.Plane.Foundations
open Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry

/-- Coordinates preserve the actual positive point classes and the interval
class selected by h. Thus the matrix identity uses the geometric orientations. -/
def CharacteristicCoordinates (X : Type) [TopologicalSpace X] [CWStructure X]
    {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (o : EdgeOrientation G) (h : IntervalParametrization)
    (ev : Cell X 0 ≃ V) (ee : Cell X 1 ≃ G.edgeSet)
    (E0 : chainGroup X ℚ ℚ 0 ≃ₗ[ℚ] (V → ℚ))
    (E1 : chainGroup X ℚ ℚ 1 ≃ₗ[ℚ] (G.edgeSet → ℚ)) : Prop := by
  classical
  exact
    (∀ z, E0 (differential X ℚ ℚ 0 z) = incidenceMap G o (E1 z)) ∧
    (∀ c m, E0 (relativePointClass ℚ ℚ (skeletalPair X 0)
      (diskToSkeleton X CWStructure.boundary_lands 0 c ⟨0, by simp⟩) m) =
        Pi.single (ev c) m) ∧
    ∃ (g : ℚ ≃ₗ[ℚ] relativeHomology ℚ ℚ (referenceDiskPair.{0} 1) 1)
      (hz : ∀ m : ℚ, (ordinary ℚ ℚ (referenceDiskPair.{0} 1)).d 1 0
        (relativeSimplexChain ℚ ℚ (referenceDiskPair.{0} 1) 1 h.simplex m) = 0),
      (∀ m, g m = P202Specs.SpheresDisks.classOf ℚ
        (ordinary ℚ ℚ (referenceDiskPair.{0} 1)) 1
        (relativeSimplexChain ℚ ℚ (referenceDiskPair.{0} 1) 1 h.simplex m) (hz m)) ∧
      ∀ c m, E1 (cellClass X ℚ ℚ 1 c (g m)) = Pi.single (ee c) m

/-- A single geometric CW model, its absence of higher cells, and its genuine
cellular coordinates with boundary equal to the signed graph incidence map. -/
def cellular_modelType : Prop :=
  ∀ {V : Type u} [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    (D : Drawing G) (o : EdgeOrientation G),
    ∃ (C : CWStructure (Realization D)) (h : IntervalParametrization),
      letI := C
      let X := Realization D
      ∃ (ev : Cell X 0 ≃ V) (ee : Cell X 1 ≃ G.edgeSet),
        Finite (Σ n, Cell X n) ∧
        (∀ n, IsEmpty (Cell X (n+2))) ∧
        (∀ c x, characteristic X 0 c x = realizationVertex D (ev c)) ∧
        (∀ c, Subtype.val '' Set.range (characteristic X 1 c) =
          OnePoint.some '' D.edge (ee c)) ∧
        (∀ c, characteristic X 1 c (h.endpoint.{0} 0).val.down =
            realizationVertex D (o.head (ee c)) ∧
          characteristic X 1 c (h.endpoint.{0} 1).val.down =
            realizationVertex D (o.tail (ee c))) ∧
        ∃ (E0 : chainGroup X ℚ ℚ 0 ≃ₗ[ℚ] (V → ℚ))
          (E1 : chainGroup X ℚ ℚ 1 ≃ₗ[ℚ] (G.edgeSet → ℚ)),
          CharacteristicCoordinates X G o h ev ee E0 E1

/-- H₁ is actual singular homology of the original realization. -/
def realization_homologyType : Prop :=
  ∀ {V : Type u} [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    (D : Drawing G) (o : EdgeOrientation G),
    Nonempty (P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1 ≃ₗ[ℚ]
      LinearMap.ker (incidenceMap G o))

/-- The H¹ identification evaluates on the same H₁ identification. -/
def realization_cohomologyType : Prop :=
  ∀ {V : Type u} [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    (D : Drawing G) (o : EdgeOrientation G),
    ∃ (E : P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1 ≃ₗ[ℚ]
        LinearMap.ker (incidenceMap G o))
      (F : P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
        (TopCat.of (Realization D)) 1 ≃ₗ[ℚ]
          Module.Dual ℚ (LinearMap.ker (incidenceMap G o))),
      ∀ a z, F a z = P202Specs.UniversalCoefficientsCohomology.evaluation ℚ ℚ
        (P202Specs.SingularChains.ordinaryComplex ℚ ℚ (TopCat.of (Realization D))) 1
        a (E.symm z)

/-- Finite dimensionality is asserted as well as the numerical finrank. -/
def realization_homology_finrankType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G),
    FiniteDimensional ℚ (P202Specs.SingularChains.homology ℚ ℚ
      (TopCat.of (Realization D)) 1) ∧
    Module.finrank ℚ (P202Specs.SingularChains.homology ℚ ℚ
      (TopCat.of (Realization D)) 1) =
        Nat.card G.edgeSet + Nat.card G.ConnectedComponent - Nat.card V

def realization_cohomology_finrankType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G),
    FiniteDimensional ℚ (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
      (TopCat.of (Realization D)) 1) ∧
    Module.finrank ℚ (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
      (TopCat.of (Realization D)) 1) =
        Nat.card G.edgeSet + Nat.card G.ConnectedComponent - Nat.card V

/-- The empty realization is handled without a nonempty-space comparison. -/
def realization_emptyType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] {G : SimpleGraph V} (D : Drawing G),
    IsEmpty (Realization D) ∧
    Subsingleton (P202Specs.SingularChains.homology ℚ ℚ
      (TopCat.of (Realization D)) 1) ∧
    Subsingleton (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
      (TopCat.of (Realization D)) 1) ∧
    Module.finrank ℚ (P202Specs.SingularChains.homology ℚ ℚ
      (TopCat.of (Realization D)) 1) = 0 ∧
    Module.finrank ℚ (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
      (TopCat.of (Realization D)) 1) = 0

end Specs.FiniteCombinatorics.Graph.Plane.CellularBridge
