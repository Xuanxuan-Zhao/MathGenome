import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralLattices
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.MatrixOpenCell

open scoped Matrix

universe u

namespace LinearAlgebraicGroups.Specs.IntegralRootCellOrders

open Pinning (BasedRootDatum)
open IntegralLattices (Index Positive Negative TorusCoordinatesGenerate orderedMatrix
  triangularEntries)
open MatrixOpenCell (CellCoordinates cellMatrix)
open OrderedRootProducts (Enumerates)

noncomputable section

abbrev evaluateRootMatrix {n : ℕ} {R : Type*} [CommRing R]
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) (x : R) :
    Matrix (Index.{u} n) (Index.{u} n) R :=
  (Polynomial.eval₂RingHom (Int.castRingHom R) x).mapMatrix p

abbrev torusMatrix {n : ℕ} {X R : Type u} [AddCommGroup X] [CommRing R]
    (w : Index.{u} n → X) (t : Multiplicative X →* Rˣ) :
    Matrix (Index.{u} n) (Index.{u} n) R :=
  Matrix.diagonal (fun i => (t (Multiplicative.ofAdd (w i)) : R))

/-- The marked diagonal torus acts on the parameter through the specified root character. -/
def ScalarAction {D : BasedRootDatum.{u}} {n : ℕ}
    (w : Index.{u} n → D.X)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) : Prop :=
  ∀ (a : D.I) (R : Type u) [CommRing R] (t : Multiplicative D.X →* Rˣ) (x : R),
    torusMatrix w t * evaluateRootMatrix (p a) x =
      evaluateRootMatrix (p a) ((t (Multiplicative.ofAdd (D.datum.root a)) : R) * x) *
        torusMatrix w t

/-- The integral weight vector and functional that detect the linear root coefficient. -/
def UnitCoefficientTests {D : BasedRootDatum.{u}} {n : ℕ}
    (w : Index.{u} n → D.X)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) : Prop :=
  ∀ a : D.I, ∃ (μ : D.X) (v : Index.{u} n → ℤ) (φ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ),
    (∀ j, w j ≠ μ → v j = 0) ∧
    (∀ j, w j ≠ μ + D.datum.root a → φ (Pi.single j 1) = 0) ∧
    φ ((Matrix.of (fun i j => (p a i j).coeff 1)).mulVec v) = 1

/-- Triangularity and polynomial recovery in the free entries of the triangular group. -/
def IsOrderedRootChart {n : ℕ} {σ : Type u} (upper : Bool)
    (P : Matrix (Index.{u} n) (Index.{u} n) (MvPolynomial σ ℤ)) : Prop :=
  (∀ i j, (if upper then ¬ i < j else ¬ j < i) → P i j = (1 : Matrix _ _ _) i j) ∧
  (∀ a : σ, ∃ q : MvPolynomial (triangularEntries n upper) ℤ,
    MvPolynomial.aeval (fun ij => P ij.val.1 ij.val.2) q = MvPolynomial.X a)

/-- Every enumeration uses the already marked basis and the same root polynomials. -/
def OrderedRootCells : Prop :=
  ∀ {D : BasedRootDatum.{u}} {n : ℕ}
    (w : Index.{u} n → D.X) (height : D.X →ₗ[ℤ] ℤ)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)),
    Antitone (height ∘ w) →
    (∀ a : Positive D, 0 < height (D.datum.root a.val)) →
    (∀ a : Negative D, height (D.datum.root a.val) < 0) →
    (∀ a i j, (p a i j).coeff 0 = (1 : Matrix _ _ ℤ) i j) →
    ScalarAction w p → UnitCoefficientTests w p →
    ∀ (negative : List (Negative D)) (positive : List (Positive D)),
      Enumerates negative Set.univ → Enumerates positive Set.univ →
      IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)) ∧
      IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val))

/-- Coordinates on the product of the two affine spaces of root parameters and the torus. -/
abbrev IntegralCellCoordinates (D : BasedRootDatum.{u}) :=
  MvPolynomial D.I (AddMonoidAlgebra ℤ D.X)

abbrev cellParameterMap {D : BasedRootDatum.{u}} {σ : Type u} (label : σ → D.I) :
    MvPolynomial σ ℤ →+* IntegralCellCoordinates D :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (MvPolynomial.X ∘ label)

abbrev rootMatrixOverCell {D : BasedRootDatum.{u}} {n : ℕ} {σ : Type u}
    (label : σ → D.I) (l : List σ)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) :
    Matrix (Fin n) (Fin n) (IntegralCellCoordinates D) :=
  ((cellParameterMap label).mapMatrix (orderedMatrix l (p ∘ label))).submatrix ULift.up ULift.up

/-- The actual lower–diagonal–upper matrix with the marked characters and root parameters. -/
def markedCellMatrix {D : BasedRootDatum.{u}} {n : ℕ}
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) :
    Matrix (Fin n) (Fin n) (IntegralCellCoordinates D) :=
  rootMatrixOverCell Subtype.val negative p *
    Matrix.diagonal (fun i => MvPolynomial.C (AddMonoidAlgebra.single (w (ULift.up i)) 1)) *
      rootMatrixOverCell Subtype.val positive p

/-- Pullback along the marked product is surjective on the full matrix open cell. -/
def SurjectiveCellCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} {n : ℕ}
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)),
    TorusCoordinatesGenerate w →
    IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)) →
    IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val)) →
    ∃ φ : CellCoordinates (ULift.{u} ℤ) n →+* IntegralCellCoordinates D,
      Function.Surjective φ ∧
        φ.mapMatrix (cellMatrix (ULift.{u} ℤ) n) = markedCellMatrix negative positive w p

/-- An integral chart whose rational restriction agrees with the fixed generic
matrix map is the localization of the matrix closure at the minor product.
The two injections express schematic density on the generic fibre and
injective extension of the integral chart coordinates to that fibre. -/
def LocalizedClosureCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} {n : ℕ}
    {B K : Type u} [CommRing B] [CommRing K]
    (generic : MatrixOpenCell.MatrixGroupCoordinates (ULift.{u} ℤ) n →+* B)
    (φ : CellCoordinates (ULift.{u} ℤ) n →+* IntegralCellCoordinates D)
    (restrict : B →+* K) (extend : IntegralCellCoordinates D →+* K),
    Function.Surjective φ → Function.Injective restrict → Function.Injective extend →
    restrict.comp generic = extend.comp (φ.comp (algebraMap _ _)) →
    ∃ f : (MatrixOpenCell.MatrixGroupCoordinates (ULift.{u} ℤ) n ⧸ RingHom.ker generic)
        →+* IntegralCellCoordinates D,
      f.comp (Ideal.Quotient.mk (RingHom.ker generic)) = φ.comp (algebraMap _ _) ∧
        letI := f.toAlgebra
        IsLocalization.Away (Ideal.Quotient.mk (RingHom.ker generic)
          (MatrixOpenCell.minorProduct (ULift.{u} ℤ) n)) (IntegralCellCoordinates D)

open RationalRealization (RationalField Realization)
open IntegralRootRelations (RootCoordinates)
open RootGroups (AdditiveLine)
open IntegralLattices (RationalHighestWeight dividedPower)
open MatrixOpenCell (MatrixGroupCoordinates glMatrix minorProduct)

/-- A single generic matrix representation and a comparison in one order
suffice for all orders on the same integral lattice. The changes of coordinates
preserve the torus coordinate algebra. In each order the resulting chart is the
localization of the same matrix closure at the same product of leading minors. -/
def ReorderedClosureCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}} {Q : Realization D A}
    [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
    [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
    {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
    {ω : D.base.support → D.X}
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Module.Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (height : D.X →ₗ[ℤ] ℤ)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)),
    (∀ j i, b j i ∈ (V i).weightSpace (w j)) →
    Antitone (height ∘ w) →
    (∀ a : Positive D, 0 < height (D.datum.root a.val)) →
    (∀ a : Negative D, height (D.datum.root a.val) < 0) →
    TorusCoordinatesGenerate w →
    (∀ a m j i, ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
      (dividedPower ((V i).rootOperator a) m).mulVec (b j i)) →
    UnitCoefficientTests w p →
    ∀ {B K : Type u} [CommRing B] [CommRing K]
      (generic : MatrixGroupCoordinates (ULift.{u} ℤ) n →+* B)
      (restrict : B →+* K) (extend : IntegralCellCoordinates D →+* K)
      (negative : List (Negative D)) (positive : List (Positive D)),
      Enumerates negative Set.univ → Enumerates positive Set.univ →
      Function.Injective restrict → Function.Injective extend →
      (∀ i j, restrict (generic (glMatrix (ULift.{u} ℤ) n i j)) =
        extend (markedCellMatrix negative positive w p i j)) →
      ∃ φ : CellCoordinates (ULift.{u} ℤ) n →+* IntegralCellCoordinates D,
        Function.Surjective φ ∧
        φ.mapMatrix (cellMatrix (ULift.{u} ℤ) n) = markedCellMatrix negative positive w p ∧
        ∀ (negative' : List (Negative D)) (positive' : List (Positive D)),
          Enumerates negative' Set.univ → Enumerates positive' Set.univ →
          ∃ changeOrder : IntegralCellCoordinates D ≃ₐ[AddMonoidAlgebra ℤ D.X]
              IntegralCellCoordinates D,
            let ψ := changeOrder.toRingHom.comp φ
            Function.Surjective ψ ∧
            ψ.mapMatrix (cellMatrix (ULift.{u} ℤ) n) = markedCellMatrix negative' positive' w p ∧
            ∃ f : (MatrixGroupCoordinates (ULift.{u} ℤ) n ⧸ RingHom.ker generic)
                →+* IntegralCellCoordinates D,
              f.comp (Ideal.Quotient.mk (RingHom.ker generic)) = ψ.comp (algebraMap _ _) ∧
              letI := f.toAlgebra
              IsLocalization.Away (Ideal.Quotient.mk (RingHom.ker generic)
                (minorProduct (ULift.{u} ℤ) n)) (IntegralCellCoordinates D)

end

end LinearAlgebraicGroups.Specs.IntegralRootCellOrders
