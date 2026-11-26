import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SteinbergTensorStep
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.NonsplitSymmetricPower
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Kronecker

open AlgebraicGeometry CategoryTheory
open scoped Kronecker

universe u

namespace LinearAlgebraicGroups.Specs.SteinbergTensorProduct

open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open AbstractPairing (IsAttachedCoroot)
open FlagLineBundle (OppositeBorelPair)
open RootWeightAction (SimpleRoot Representation)
open InducedNonvanishing (Dominant)
open SimpleClassification (SocleModel)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)
open AdjointRepresentation (GroupPoints)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The bound on each simple-coroot coordinate of a dominant digit. -/
def Restricted (P : OppositeBorelPair G) (p : ℕ) (χ : Character P.torus.group) : Prop :=
  Dominant P χ ∧ ∀ (a : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group),
    IsAttachedCoroot P.torus a.val c → pairing P.torus.group χ c < (p : ℤ)

/-- A little-endian list represents a sequence of weights extended by the trivial
character. The product notation for characters corresponds to weight addition. -/
def digitWeight {X : Type*} [Monoid X] (p : ℕ) : List X → X
  | [] => 1
  | a :: tail => a * digitWeight p tail ^ p

/-- Existence and uniqueness of the finite-support digit sequence, with
lists compared after extension by the trivial character. -/
def Digits : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k), IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (P : OppositeBorelPair G) (lam : Character P.torus.group), Dominant P lam →
      ∃ digits : List (Character P.torus.group),
        (∀ a ∈ digits, Restricted P p a) ∧ digitWeight p digits = lam ∧
        ∀ other : List (Character P.torus.group),
          (∀ a ∈ other, Restricted P p a) → digitWeight p other = lam →
          ∀ i : ℕ, other.getD i 1 = digits.getD i 1

/-- A finite list of the actual simple socles attached to the digits. -/
inductive Factors (P : OppositeBorelPair G) (U : ClosedSubgroup P.positive.group) :
    List (Character P.torus.group) → Type (u + 1)
  | nil : Factors P U []
  | cons {a tail} : SocleModel P U a → Factors P U tail → Factors P U (a :: tail)

namespace Factors

variable {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}

def Index {l} : Factors P U l → Type u
  | .nil => ULift.{u} Unit
  | .cons S tail => S.J × tail.Index

noncomputable instance {l} (F : Factors P U l) : Fintype F.Index := by
  induction F with
  | nil => exact inferInstanceAs (Fintype (ULift.{u} Unit))
  | cons S _ ih =>
      letI := ih
      exact inferInstanceAs (Fintype (S.J × _))

noncomputable instance {l} (F : Factors P U l) : DecidableEq F.Index := by
  induction F with
  | nil => exact inferInstanceAs (DecidableEq (ULift.{u} Unit))
  | cons S _ ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (S.J × _))

/-- The ordered tensor product matrix, with the factor in position i raised
entrywise to the power p^i. The empty tensor acts by 1 on a line.
The coefficient power is the relative Frobenius pullback in the scalar-twisted
basis, as in the one-step formula. -/
noncomputable def matrix {l} (F : Factors P U l) (p : ℕ) (R : TestAlgebra k)
    (g : GroupPoints G.val R) : Matrix F.Index F.Index R :=
  match F with
  | .nil => fun _ _ => 1
  | .cons S tail => (S.socleAction.app R g).val ⊗ₖ
      (fun i j => tail.matrix p R g i j ^ p)

/-- The ordered tensor action when the first listed factor is in position `n`. -/
noncomputable def matrixFrom {l} (F : Factors P U l) (p n : ℕ) (R : TestAlgebra k)
    (g : GroupPoints G.val R) : Matrix F.Index F.Index R :=
  match F with
  | .nil => fun _ _ => 1
  | .cons S tail => (fun i j => (S.socleAction.app R g).val i j ^ (p ^ n)) ⊗ₖ
      tail.matrixFrom p (n + 1) R g

end Factors

variable {I J : Type u}

/-- A fixed change of basis over the ground field identifies two matrix
actions over every commutative test algebra. -/
def MatrixIsomorphism [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (r : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix I I R)
    (s : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix J J R) : Prop :=
  ∃ (C : Matrix J I k) (D : Matrix I J k),
    C * D = 1 ∧ D * C = 1 ∧
    ∀ (R : TestAlgebra k) (g : GroupPoints G.val R),
      C.map (algebraMap k R) * r R g = s R g * C.map (algebraMap k R)

/-- The tensor product for every finite digit expansion and every choice of
simple socle models, including the empty tensor for the trivial weight. -/
def TensorProductFormula : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k), IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (P : OppositeBorelPair G) (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
      ∀ (l : List (Character P.torus.group)), (∀ a ∈ l, Restricted P p a) →
        Nonempty (Factors P U l) ∧ Nonempty (SocleModel P U (digitWeight p l)) ∧
        ∀ (F : Factors P U l) (L : SocleModel P U (digitWeight p l)),
          MatrixIsomorphism (G := G) (F.matrixFrom p 0)
            (fun R g => (L.socleAction.app R g).val)

open LinearAlgebraicGroups.RationalRepresentations (coefficients)
open LinearAlgebraicGroups.FiniteDistributions (twistCoordinates FrobeniusFormula)
open RelativeFrobenius (extendAlong scalarTensor)

/-- The relative Frobenius target of a group extended from the prime field
identifies with the same split model. The formula on every model coordinate
applies in particular to each coefficient of a representation of that model. -/
def SplitModelRelativeTwist : Prop :=
  ∀ {k : Type u} [Field k] (p n : ℕ) [Fact p.Prime] [CharP k p],
    let k₀ := ULift.{u} (ZMod p)
    let ι : k₀ →+* k := (ZMod.castHom (dvd_refl p) k).comp ULift.ringEquiv.toRingHom
    ∀ A₀ : HopfAlgebraCategory k₀,
      let A := extendAlong ι A₀
      ∃ e : A ≅ twistCoordinates k p n A,
        (∀ a : A₀, e.hom.hom (scalarTensor ι A₀ 1 a) =
          scalarTensor (iterateFrobenius k p n) A 1 (scalarTensor ι A₀ 1 a)) ∧
        ∀ F : twistCoordinates k p n A ⟶ A, FrobeniusFormula k p n A F →
          ∀ (R : TestAlgebra k) (g : A →ₐ[k] R) (a : A₀),
            g ((e.hom ≫ F).hom (scalarTensor ι A₀ 1 a)) =
              (g (scalarTensor ι A₀ 1 a)) ^ (p ^ n)

/-- The coefficient powers in the tensor factors come from pullback of the
scalar-twisted representation along iterated relative Frobenius, compatibly
with the identification for a split model over the prime field. -/
def RelativeTwistMatrices : Prop :=
  (∀ {k V I : Type u} [Field k] [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (A : HopfAlgebraCategory k)
    (b : Module.Basis I k V) (rho : RightComodule k A V),
    ∃ (F : twistCoordinates k p n A ⟶ A)
        (delta : RightComodule k (twistCoordinates k p n A) V) (sigma : RightComodule k A V),
      FrobeniusFormula k p n A F ∧
      (∀ i j, coefficients (twistCoordinates k p n A) b delta i j =
        scalarTensor (iterateFrobenius k p n) A 1 (coefficients A b rho i j)) ∧
      sigma.coaction = F.hom.toAlgHom.toLinearMap.lTensor V ∘ₗ delta.coaction ∧
      (∀ i j, coefficients A b sigma i j = (coefficients A b rho i j) ^ (p ^ n))) ∧
  SplitModelRelativeTwist.{u}

open GeneralLinearStructure (SpecialMatrixPoints)
open NonsplitSymmetricPower (Forms purePowers purePowerMap frobeniusMatrix)
open CharacterPairing (characterValue)

/-- The diagonal character of weight one on SL₂ is its single nontrivial
digit for the weight p. The natural module has this highest weight. Its first
Frobenius pullback is the marked simple socle of the pth symmetric power,
via the pure-power map on vectors. -/
def RankOneExample : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k) (s : SpecialMatrixPoints G 2),
    ∃ (P : OppositeBorelPair G) (chi : Character P.torus.group)
      (U : ClosedSubgroup P.positive.group) (L : SocleModel P U (chi ^ p)),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U ∧
      (∀ (R : TestAlgebra k) (t : GroupPoints P.torus.group R),
        characterValue chi R t =
          (s.hom.app R (t ≫ P.torus.inclusion.hom.hom)).val ⟨0⟩ ⟨0⟩) ∧
      chi ≠ 1 ∧
      (∀ a c, IsAttachedCoroot P.torus (a : SimpleRoot P.torus P.positive).val c →
        pairing P.torus.group chi c = 1) ∧
      (∀ a ∈ ([1, chi] : List (Character P.torus.group)), Restricted P p a) ∧
      digitWeight p [1, chi] = chi ^ p ∧
      ∃ M : SocleModel P U chi,
        MatrixIsomorphism (G := G) (fun R g => (s.hom.app R g).val)
          (fun R g => (M.socleAction.app R g).val) ∧
        ∃ (E : Forms k p ≃ₗ[k] (L.I → k)) (e : (Fin 2 → k) ≃ₗ[k] L.socle),
          (purePowers k p).map E.toLinearMap = L.socle ∧
          (∀ v, (e v : L.I → k) = E (purePowerMap k p v)) ∧
          ∀ (R : TestAlgebra k) (g : GroupPoints G.val R) (ell : R →ₗ[k] k) (v : Fin 2 → k),
            let m := (s.hom.app R g).val.submatrix ULift.up ULift.up
            let w := (frobeniusMatrix p m).mulVec (fun i => algebraMap k R (v i))
            L.socleBasis.equivFun (e (fun i => ell (w i))) =
              PrimitiveLine.orbitCoefficient L.socleAction R g ell
                (L.socleBasis.equivFun (e v))

end LinearAlgebraicGroups.Specs.SteinbergTensorProduct
