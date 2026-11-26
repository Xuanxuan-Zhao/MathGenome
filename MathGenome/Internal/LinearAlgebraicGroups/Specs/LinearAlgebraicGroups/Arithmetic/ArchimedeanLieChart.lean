import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.UniformSpace.Matrix

noncomputable section

open Filter Topology NormedSpace AlgebraicGeometry CategoryTheory
open scoped Matrix.Norms.Operator
open LinearAlgebraicGroups.Arithmetic.AdelicGroups
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)

namespace LinearAlgebraicGroups.Specs.ArchimedeanLieChart

universe u

section Units

variable {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The matrix exponential with its inverse supplied by the negative exponential. -/
def expUnit (x : A) : Aˣ :=
  (isUnit_exp_of_mem_ball (𝕂 := ℝ) (x := x)
    ((expSeries_radius_eq_top ℝ A).symm ▸ edist_lt_top x 0)).unit

/-- The directions whose entire real one-parameter group is in the subgroup. -/
def exponentialLines (H : Subgroup Aˣ) : Set A :=
  {x | ∀ t : ℝ, expUnit (t • x) ∈ H}

/-- The underlying matrix of the conjugation of a tangent vector. -/
def conjugate (g : Aˣ) (x : A) : A := (g : A) * x * (↑g⁻¹ : A)

structure ClosedSubgroupChart (H : Subgroup Aˣ) where
  tangent : Submodule ℝ A
  mem_tangent (x : A) : x ∈ tangent ↔ x ∈ exponentialLines H
  expOpen : OpenPartialHomeomorph tangent H
  zero_mem : (0 : tangent) ∈ expOpen.source
  exp_chart (x : tangent) (hx : x ∈ expOpen.source) :
    (expOpen x : Aˣ) = expUnit (x : A)
  exp_derivative :
    HasStrictFDerivAt (fun x => (expOpen x : Aˣ).val) tangent.subtypeL 0
  conjugation (g : H) (x : tangent) : conjugate (g : Aˣ) x ∈ tangent
  bracket_mem (x y : tangent) : (x : A) * (y : A) - (y : A) * (x : A) ∈ tangent
  discrete_of_zero : tangent = ⊥ → DiscreteTopology H
  open_of_full : tangent = ⊤ → IsOpen (H : Set Aˣ)

def ClosedSubgroupExponential : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [FiniteDimensional ℝ A] (H : Subgroup Aˣ),
    IsClosed (H : Set Aˣ) → Nonempty (ClosedSubgroupChart H)

end Units

section MatrixFactors

/-- The matrix coefficients of the scheme differential in the given realization. -/
abbrev tangentMatrix {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (i : MatrixRealization G) :
    Lie F G.val → Matrix (Unipotent.Index.{u} i.size) (Unipotent.Index.{u} i.size) F :=
  InfinitesimalCommutator.matrixDifferential i.embedding i.matrix

/-- The real tangent of the actual point group is the scheme tangent viewed
in matrices. Its adjoint action and infinitesimal action use the same realization. -/
def MatrixTangentComparison : Prop :=
  ∀ (F : Type u) [NormedField F] [NormedAlgebra ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ F] (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (s : IdentityLieStructure G.val),
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := Module.restrictScalars ℝ F (Lie F G.val)
    ∃ (d : Lie F G.val →ₗ[ℝ] Matrix (Unipotent.Index.{u} i.size) (Unipotent.Index.{u} i.size) F),
      Function.Injective d ∧
      (∀ x, d x = tangentMatrix i x) ∧
      (∀ X, X ∈ exponentialLines (asMatrix i F).range ↔ X ∈ d.range) ∧
      (∀ (g : PointsIn i F) x, ∃ y : Lie F G.val,
        y.toMul.val = AdjointRepresentation.conjugate (G := G.val)
          (R := CommAlgCat.of F F) g x ∧
        d y = conjugate (asMatrix i F g) (d x)) ∧
      ∀ x y, HasDerivAt (fun t : ℝ => conjugate (expUnit (t • d x)) (d y))
        (d ⁅x, y⁆) 0

end MatrixFactors

section Products

variable {J : Type u} [Fintype J]
  (F : J → Type u) [∀ j, NormedField (F j)] [∀ j, NormedAlgebra ℝ (F j)]
  [∀ j, CompleteSpace (F j)]
  (G : ∀ j, AffineAlgebraicGroup (F j)) (i : ∀ j, MatrixRealization (G j))

abbrev MatrixProduct :=
  ∀ j, Matrix (Unipotent.Index.{u} (i j).size) (Unipotent.Index.{u} (i j).size) (F j)

abbrev PointProduct := ∀ j, PointsIn (i j) (F j)

/-- Matrices of the actual points, in the units of the dependent product algebra. -/
def pointMatrices : PointProduct F G i →* (MatrixProduct F G i)ˣ where
  toFun g := {
    val := fun j => (asMatrix (i j) (F j) (g j)).val
    inv := fun j => (asMatrix (i j) (F j) (g j)).inv
    val_inv := funext fun j => (asMatrix (i j) (F j) (g j)).val_inv
    inv_val := funext fun j => (asMatrix (i j) (F j) (g j)).inv_val }
  map_one' := Units.ext (funext fun j => congrArg Units.val (map_one (asMatrix (i j) (F j))))
  map_mul' x y :=
    Units.ext (funext fun j => congrArg Units.val (map_mul (asMatrix (i j) (F j)) (x j) (y j)))

/-- The exponential chart on the product and on each closed subgroup, with the
ambient tangent identified with the product of the actual scheme tangents. -/
def ProductChart : Prop :=
  ∀ (J : Type u) [Fintype J] (F : J → Type u) [∀ j, NormedField (F j)]
    [∀ j, NormedAlgebra ℝ (F j)] [∀ j, CompleteSpace (F j)]
    [∀ j, FiniteDimensional ℝ (F j)] (G : ∀ j, AffineAlgebraicGroup (F j))
    (i : ∀ j, MatrixRealization (G j))
    (s : ∀ j, IdentityLieStructure (G j).val),
    letI : ∀ j, LieRing (Lie (F j) (G j).val) := fun j => (s j).lieRing
    letI : ∀ j, LieAlgebra (F j) (Lie (F j) (G j).val) := fun j => (s j).lieAlgebra
    letI : ∀ j, Module ℝ (Lie (F j) (G j).val) :=
      fun j => Module.restrictScalars ℝ (F j) (Lie (F j) (G j).val)
    ∃ (d : (∀ j, Lie (F j) (G j).val) →ₗ[ℝ] MatrixProduct F G i),
      Function.Injective d ∧
      (∀ x j, d x j = tangentMatrix (i j) (x j)) ∧
      (∀ x, x ∈ exponentialLines (pointMatrices F G i).range ↔ x ∈ d.range) ∧
      (∀ (H : Subgroup (PointProduct F G i)), IsClosed (H : Set (PointProduct F G i)) →
        ∃ (W : Submodule ℝ (MatrixProduct F G i))
          (e : OpenPartialHomeomorph W H),
          W ≤ d.range ∧
          (∀ x, x ∈ W ↔ ∀ t : ℝ, expUnit (t • x) ∈ H.map (pointMatrices F G i)) ∧
          (0 : W) ∈ e.source ∧
          (∀ (x : W), x ∈ e.source →
            pointMatrices F G i ((e x : H) : PointProduct F G i) = expUnit (x : MatrixProduct F G i)) ∧
          (∀ (g : H) (x : W),
            conjugate (pointMatrices F G i (g : PointProduct F G i)) x ∈ W) ∧
          (∀ x y : W,
            (x : MatrixProduct F G i) * (y : MatrixProduct F G i) -
              (y : MatrixProduct F G i) * (x : MatrixProduct F G i) ∈ W) ∧
          (W = ⊥ → DiscreteTopology H) ∧
          (W = d.range → IsOpen (H : Set (PointProduct F G i)))) ∧
      (∃ e : OpenPartialHomeomorph d.range (PointProduct F G i),
        (0 : d.range) ∈ e.source ∧
        (∀ (x : d.range), x ∈ e.source →
          pointMatrices F G i (e x) = expUnit (x : MatrixProduct F G i)) ∧
        HasStrictFDerivAt (fun x => (pointMatrices F G i (e x)).val) d.range.subtypeL 0) ∧
      (∀ x j, (expUnit (d x)).val j = (expUnit (tangentMatrix (i j) (x j))).val) ∧
      (∀ (g : PointProduct F G i) (x : ∀ j, Lie (F j) (G j).val),
        ∃ y : ∀ j, Lie (F j) (G j).val,
          (∀ j, (y j).toMul.val = AdjointRepresentation.conjugate (G := (G j).val)
            (R := CommAlgCat.of (F j) (F j)) (g j) (x j)) ∧
          d y = conjugate (pointMatrices F G i g) (d x)) ∧
      ∀ x y, HasDerivAt
        (fun t : ℝ => conjugate (expUnit (t • d x)) (d y)) (d fun j => ⁅x j, y j⁆) 0

/-- Restricting an exponential to a subproduct or inserting it with identity
coordinates gives the exponential of the correspondingly restricted or extended tangent. -/
def ProductCoordinateCompatibility : Prop :=
  ∀ (J : Type u) [Fintype J] (F : J → Type u) [∀ j, NormedField (F j)]
    [∀ j, NormedAlgebra ℝ (F j)] [∀ j, CompleteSpace (F j)]
    [∀ j, FiniteDimensional ℝ (F j)] (G : ∀ j, AffineAlgebraicGroup (F j))
    (i : ∀ j, MatrixRealization (G j))
    (P : J → Prop) [DecidablePred P],
    let F' : {j // P j} → Type u := fun j => F j
    let G' : ∀ j, AffineAlgebraicGroup (F' j) := fun j => G j
    let i' : ∀ j, MatrixRealization (G' j) := fun j => i j
    (∀ (x : MatrixProduct F G i) (g : PointProduct F G i),
      pointMatrices F G i g = expUnit x →
      pointMatrices F' G' i' (fun j => g j) = expUnit (fun j : {a // P a} => x j)) ∧
    ∀ (x : MatrixProduct F' G' i') (g : PointProduct F' G' i'),
      pointMatrices F' G' i' g = expUnit x →
      pointMatrices F G i (fun j => if h : P j then g ⟨j, h⟩ else 1) =
        expUnit (fun j => if h : P j then x ⟨j, h⟩ else 0)

end Products

/-- The specified closed realization after scalar extension gives the usual
homeomorphism between points of the base-changed group and points over the extension. -/
def BaseChangeMatrixComparison : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [TopologicalSpace F]
    (G : AffineAlgebraicGroup k) (i : MatrixRealization G),
    let G_F := (groupBaseChange k F).obj G.val
    ∃ h : IsAffine G_F.X.left ∧ LocallyOfFiniteType G_F.X.hom ∧ QuasiCompact G_F.X.hom,
      let H : AffineAlgebraicGroup F := ⟨G_F, h⟩
      ∃ (iF : MatrixRealization H) (hs : iF.size = i.size)
        (e : PointsIn iF F ≃ₜ* PointsIn i F),
        (∀ p, (show Points G.val.X (CommAlgCat.of k F) from e p).left =
          (baseChangePoint k F G.val.X (CommAlgCat.of F F) p).left) ∧
        ∀ p, cast (congrArg (fun n => Matrix.GeneralLinearGroup (Unipotent.Index.{u} n) F) hs)
          (asMatrix iF F p) = asMatrix i F (e p)

/-- The ordinary real scalar action on each actual archimedean completion,
given via the canonical real or complex model of that completion. -/
def CompletionRealStructures : Prop :=
  ∀ (K : Type u) [Field K] (w : NumberField.InfinitePlace K),
    ∃ A : NormedAlgebra ℝ w.Completion,
      letI := A
      FiniteDimensional ℝ w.Completion ∧
      (∀ (hw : w.IsReal) (r : ℝ),
        NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
          (algebraMap ℝ w.Completion r) = r) ∧
      ∀ (hw : w.IsComplex) (r : ℝ),
        NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
          (algebraMap ℝ w.Completion r) = (r : ℂ)

end LinearAlgebraicGroups.Specs.ArchimedeanLieChart
