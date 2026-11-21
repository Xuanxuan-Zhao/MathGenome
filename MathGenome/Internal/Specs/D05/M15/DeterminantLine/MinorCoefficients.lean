import MathGenome.Internal.Specs.D05.M15.ExteriorBasis
import MathGenome.Internal.Specs.D05.M15.WedgeSign
import MathGenome.Internal.Specs.D05.M05.DetDefinition
import MathGenome.Internal.Specs.D05.M04.MatrixOfMap
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
Independent statements for the minor-coefficient step of K05.15.determinant_line,
paper.tex:2966–2985. Rows index the output basis and columns the input basis.
A k-subset is enumerated in increasing order, exactly as in the accepted
`increasingWedge`. Coefficients are actual basis coordinates in the homogeneous
submodules of the exterior quotient. The determinant is the accepted column
Leibniz determinant. No characteristic, splitting, rank, or invertibility
hypothesis is imposed, and neither dimension nor the degree must be positive.
-/

noncomputable section
namespace Specs.D05.M15.DeterminantLine.MinorCoefficients

universe u v w
open scoped BigOperators

/-- The coefficient formula in arbitrary finite ordered bases. -/
def based_minor_coefficients : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {n m : ℕ} (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (f : V →ₗ[K] W) (k : ℕ)
    (I : Set.powersetCard (Fin m) k) (J : Set.powersetCard (Fin n) k),
    (c.exteriorPower k).repr
        (WedgeSign.powerMap_value k f (ExteriorBasis.increasingWedge b k J)) I =
      D05.M05.determinant ((Specs.D05.M04.MatrixOfMap.matrixOfMap_value b c f).submatrix
        (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop))

/-- Every rectangular matrix acts on coordinate columns; its exterior-map
entry from e_J to e_I is its ordered (I,J) minor, for every natural k. -/
def minor_coefficients : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (k : ℕ) (I : Set.powersetCard (Fin m) k) (J : Set.powersetCard (Fin n) k),
    ((Pi.basisFun K (Fin m)).exteriorPower k).repr
        (WedgeSign.powerMap_value k (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A)
          (ExteriorBasis.increasingWedge (Pi.basisFun K (Fin n)) k J)) I =
      D05.M05.determinant (A.submatrix
        (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop))

/-- The coefficient identity also gives the full finite expansion in the
increasing wedge basis. Above the output dimension this is an empty sum. -/
def minor_expansion : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (k : ℕ) (J : Set.powersetCard (Fin n) k),
    WedgeSign.powerMap_value k (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A)
        (ExteriorBasis.increasingWedge (Pi.basisFun K (Fin n)) k J) =
      ∑ I : Set.powersetCard (Fin m) k,
        D05.M05.determinant (A.submatrix
          (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop)) •
            ExteriorBasis.increasingWedge (Pi.basisFun K (Fin m)) k I

/-- The sole degree-zero coefficient is the empty determinant, equal to 1. -/
def degree_zero_coefficient : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (I : Set.powersetCard (Fin m) 0) (J : Set.powersetCard (Fin n) 0),
    ((Pi.basisFun K (Fin m)).exteriorPower 0).repr
        (WedgeSign.powerMap_value 0 (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A)
          (ExteriorBasis.increasingWedge (Pi.basisFun K (Fin n)) 0 J)) I = 1

/-- Under the canonical degree-zero scalar identifications, the entire map is
identity on K, including matrices with no rows or no columns. -/
def degree_zero_map : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (x : ⋀[K]^0 (Fin n → K)),
    exteriorPower.zeroEquiv K (Fin m → K)
        (WedgeSign.powerMap_value 0 (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A) x) =
      exteriorPower.zeroEquiv K (Fin n → K) x

/-- The actual exterior homogeneous submodule above the coordinate-space
dimension is zero; this applies separately to either side of a rectangle. -/
def above_dimension : Prop :=
  ∀ {K : Type u} [Field K] (d k : ℕ), d < k →
    Exterior.homogeneousPart_value K (Fin d → K) k = ⊥

/-- If k exceeds either dimension, the induced linear map is the zero map,
with its actual exterior-power domain and codomain. -/
def above_dimension_map : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (k : ℕ), (n < k ∨ m < k) →
    WedgeSign.powerMap_value k (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A) = 0

end Specs.D05.M15.DeterminantLine.MinorCoefficients
