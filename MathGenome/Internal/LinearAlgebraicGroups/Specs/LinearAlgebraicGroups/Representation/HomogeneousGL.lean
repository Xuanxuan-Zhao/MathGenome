import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.PolynomialGL
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorEvaluation

open CategoryTheory
open scoped BigOperators

universe u

namespace LinearAlgebraicGroups.Specs.HomogeneousGL

open StandardGroups PolynomialGL
open Unipotent (Index)

noncomputable section

variable {k m I : Type u} [Field k] [Fintype m] [DecidableEq m]
  [Fintype I] [DecidableEq I]

/-- The scalar matrices act on this subspace through the character z ↦ z^d. -/
def degreeSpace (ρ : MatrixRepresentation k m I) (d : ℤ) : Submodule k (I → k) :=
  ⨅ (R : TestAlgebra k) (z : Rˣ),
    LinearMap.ker (((((representationAt ρ R (Matrix.GeneralLinearGroup.scalar m z)).val.mulVecLin
      - (z ^ d).val • LinearMap.id).restrictScalars k).comp
      (RootWeightAction.extendLinear R)))

theorem mem_degreeSpace {ρ : MatrixRepresentation k m I} {d : ℤ} {v : I → k} :
    v ∈ degreeSpace ρ d ↔
      ∀ (R : TestAlgebra k) (z : Rˣ),
        (representationAt ρ R (Matrix.GeneralLinearGroup.scalar m z)).val.mulVec
          (RootWeightAction.extendVector R v) =
          (z ^ d).val • RootWeightAction.extendVector R v := by
  simp [degreeSpace, sub_eq_zero, RootWeightAction.extendLinear]

/-- A vector and a covector determine a coefficient of the polynomial matrix.
Varying the covector includes the dual coordinate functions of any basis of a summand,
extended to the ambient vector space. -/
def polynomialCoefficient (P : Matrix I I (MvPolynomial (m × m) k))
    (v f : I → k) : MvPolynomial (m × m) k :=
  dotProduct (fun i => MvPolynomial.C (f i)) (P.mulVec fun i => MvPolynomial.C (v i))

/-- The central weight spaces are an internal direct sum of rational submodules. -/
def CentralDegreeDecomposition : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (n : ℕ)
    (G : AffineAlgebraicGroup k) (e : GeneralLinearStructure.MatrixPoints G (n + 1))
    (ρ : MatrixRepresentation k (Index.{u} (n + 1)) I),
    DirectSum.IsInternal (degreeSpace ρ) ∧
    ∀ d, PrimitiveLine.IsStable (e.hom ≫ ρ) (degreeSpace ρ d)

/-- On the simple of highest weight λ, the scalar exponent is the sum of its coordinates.
The polynomial criterion applies in the same coordinates. -/
def SimpleDegree : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (n : ℕ)
    (G : AffineAlgebraicGroup k) (e : GeneralLinearStructure.MatrixPoints G (n + 1))
    (ρ : MatrixRepresentation k (Index.{u} (n + 1)) I),
    PrimitiveLine.IsSimple (G := G) (e.hom ≫ ρ) →
    ∀ (lam : Index.{u} (n + 1) → ℤ) (v : I → k), IsPrimitive ρ lam v →
      degreeSpace ρ (∑ i, lam i) = ⊤ ∧ (IsPolynomial ρ ↔ 0 ≤ lam ⟨Fin.last n⟩)

/-- Every coefficient on the degree-d summand is homogeneous of degree d, over any
ground field. Polynomial representations have no negative central weights. -/
def HomogeneousCoefficients : Prop :=
  ∀ (k m I : Type u) [Field k] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
    (ρ : MatrixRepresentation k m I) (P : Matrix I I (MvPolynomial (m × m) k)),
    EvaluatesTo ρ P →
    (∀ (d : ℕ) (v : I → k), v ∈ degreeSpace ρ (d : ℤ) →
      ∀ f : I → k, (polynomialCoefficient P v f).IsHomogeneous d) ∧
    ∀ d : ℤ, d < 0 → degreeSpace ρ d = ⊥

/-- The weight of the last vector of the dual standard basis. -/
def dualWeight (n : ℕ) : Index.{u} (n + 1) → ℤ :=
  Pi.single ⟨Fin.last n⟩ (-1)

/-- The dual natural module has the inverse-transpose action, the indicated
highest-weight vector, and cofactor coefficients after twisting by det. -/
def NaturalDual : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    ∃ ρ : MatrixRepresentation k (Index.{u} (n + 1)) (Index.{u} (n + 1)),
      (∀ (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup (Index.{u} (n + 1)) R),
        (representationAt ρ R g).val = (g⁻¹).val.transpose) ∧
      IsPrimitive ρ (dualWeight n) (Pi.single ⟨Fin.last n⟩ 1) ∧
      (∀ lam v, IsPrimitive ρ lam v → lam = dualWeight n) ∧
      EvaluatesTo (determinantTwist ρ 1) (genericMatrix k (Index.{u} (n + 1))).adjugate.transpose

/-- Compare the weight tuple with the rows of a partition that labels a nonzero
multiplicity space for the tensor power of the standard complex module. -/
def IsSchurWeylLabel (n d : ℕ) (lam : Index.{u} (n + 1) → ℤ) : Prop :=
  ∃! p : Nat.Partition d,
    Nontrivial (_root_.Specs.AdvancedFiniteGroupRepresentations.TensorMultiplicity
      (Fin (n + 1) → ℂ) p) ∧
    ∀ i, lam i = (YoungDiagram.ofPartition p).rowLen i.down.val

/-- The same padded partition labels describe dominant tuples and the central
degree of polynomial simple modules. The label comparison uses the actual
complex Schur–Weyl multiplicity spaces. -/
def SchurWeylLabels : Prop :=
  (∀ (n d : ℕ) (lam : Index.{u} (n + 1) → ℤ),
    (Antitone lam ∧ 0 ≤ lam ⟨Fin.last n⟩ ∧ (∑ i, lam i) = (d : ℤ)) ↔
      IsSchurWeylLabel n d lam) ∧
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (n d : ℕ)
    (G : AffineAlgebraicGroup k) (e : GeneralLinearStructure.MatrixPoints G (n + 1))
    (ρ : MatrixRepresentation k (Index.{u} (n + 1)) I),
    PrimitiveLine.IsSimple (G := G) (e.hom ≫ ρ) →
    ∀ (lam : Index.{u} (n + 1) → ℤ) (v : I → k), Antitone lam → IsPrimitive ρ lam v →
      ((IsPolynomial ρ ∧ degreeSpace ρ (d : ℤ) = ⊤) ↔ IsSchurWeylLabel n d lam)

end

end LinearAlgebraicGroups.Specs.HomogeneousGL
