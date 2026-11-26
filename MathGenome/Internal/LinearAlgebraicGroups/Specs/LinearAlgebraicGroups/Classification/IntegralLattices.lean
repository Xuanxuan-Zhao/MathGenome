import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Data.Matrix.Mul

open CategoryTheory
open scoped BigOperators Classical Matrix

universe u

namespace LinearAlgebraicGroups.Specs.IntegralLattices

open Pinning (BasedRootDatum)
open RationalRealization (RationalField Realization)
open IntegralRootRelations (RootCoordinates IsChevalley IsRootTangent OppositeRootRelations
  IndependentRootRelations FormalBigCellProduct dualUnit)
open RootGroups (AdditiveLine)
open OrderedRootProducts (Enumerates)
open CharacterPairing (characterValue)
open AdjointRepresentation (GroupPoints)

noncomputable section

/-- The basis of characters dual to the simple coroots when the coroots
generate the entire cocharacter lattice. -/
def FundamentalWeights : Prop := by
  classical
  exact ∀ D : BasedRootDatum.{u}, RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∃ b : Module.Basis D.base.support ℤ D.X,
      ∀ i j : D.base.support, D.datum.coroot' j (b i) = if j = i then 1 else 0

abbrev Index (n : ℕ) := ULift.{u} (Fin n)

abbrev Positive (D : BasedRootDatum.{u}) := {a : D.I // D.base.IsPos a}
abbrev Negative (D : BasedRootDatum.{u}) := {a : D.I // ¬ D.base.IsPos a}

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}

section HighestWeight

variable [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]

local notation "𝔤" => Lie RationalField Q.pinned.pair.G.val
local notation "U" => UniversalEnvelopingAlgebra RationalField 𝔤

/-- The Verma relations augmented by the simple lowering powers for a
fundamental character. The left ideal acts on the cyclic highest vector. -/
def highestWeightRelations (e h : D.I → 𝔤) (lam : D.X) : Submodule U U :=
  Submodule.span U
    (Set.range (fun a : Positive D => UniversalEnvelopingAlgebra.ι RationalField (e a)) ∪
     Set.range (fun j : D.base.support =>
       UniversalEnvelopingAlgebra.ι RationalField (h j) -
         algebraMap RationalField U (D.datum.coroot' j lam : RationalField)) ∪
     Set.range (fun j : D.base.support =>
       UniversalEnvelopingAlgebra.ι RationalField (e (D.datum.reflectionPerm j j)) ^
         ((D.datum.coroot' j lam).toNat + 1)))

/-- The indicated divided power of the root operator in a rational basis. -/
def dividedPower {n : ℕ} (E : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) (m : ℕ) :
    Matrix (Index.{u} n) (Index.{u} n) RationalField.{u} :=
  (m.factorial : RationalField.{u})⁻¹ • E ^ m

/-- Polynomial exponential of a root operator that vanishes at the given power. -/
def exponentialPolynomial {n : ℕ} (E : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) (N : ℕ) :
    Matrix (Index.{u} n) (Index.{u} n) (Polynomial RationalField.{u}) :=
  ∑ m ∈ Finset.range N, ((Polynomial.X : Polynomial RationalField.{u}) ^ m) •
    (Polynomial.C : RationalField.{u} →+* Polynomial RationalField.{u}).mapMatrix (dividedPower E m)

/-- The rational highest-weight module of the actual pinned group. The kernel
of the cyclic map specifies the enveloping-algebra presentation, and the
natural group action has the prescribed root polynomials and torus weights. -/
structure RationalHighestWeight (z : RootCoordinates Q)
    (e h : D.I → 𝔤) (lam : D.X) where
  dimension : ℕ
  highest : Index.{u} dimension → RationalField.{u}
  highest_ne_zero : highest ≠ 0
  envelopingAction : U →ₐ[RationalField.{u}]
    Matrix (Index.{u} dimension) (Index.{u} dimension) RationalField.{u}
  cyclic : Function.Surjective (fun a => (envelopingAction a).mulVec highest)
  relations : ∀ a : U, (envelopingAction a).mulVec highest = 0 ↔
    a ∈ highestWeightRelations e h lam
  weight : Index.{u} dimension → D.X
  highest_support : ∀ j, weight j ≠ lam → highest j = 0
  highest_line : ∀ v : Index.{u} dimension → RationalField.{u},
    (∀ j, weight j ≠ lam → v j = 0) →
    v ∈ Submodule.span RationalField.{u} {highest}
  nilpotenceBound : ℕ
  nilpotent : ∀ a, envelopingAction (UniversalEnvelopingAlgebra.ι RationalField (e a)) ^
    nilpotenceBound = 0
  action : (groupPointsFunctor RationalField.{u}).obj Q.pinned.pair.G.val ⟶
    StandardGroups.generalLinearPoints RationalField.{u} (Index.{u} dimension)
  torus_action : ∀ (R : TestAlgebra RationalField.{u}) (t : GroupPoints Q.pinned.pair.T.group R),
    (action.app R (t ≫ Q.pinned.pair.T.inclusion.hom.hom) :
      Matrix.GeneralLinearGroup (Index.{u} dimension) R).val =
      Matrix.diagonal (fun j =>
        characterValue (Additive.toMul (Q.datumIso.val.weightEquiv (weight j))) R t)
  root_action : ∀ (a : D.I) (R : TestAlgebra RationalField.{u}) (x : R),
    (action.app R (IntegralRootRelations.root Q z a R x) :
      Matrix.GeneralLinearGroup (Index.{u} dimension) R).val =
      (Polynomial.eval₂RingHom (algebraMap RationalField.{u} R) x).mapMatrix
        (exponentialPolynomial
          (envelopingAction (UniversalEnvelopingAlgebra.ι RationalField (e a))) nilpotenceBound)

namespace RationalHighestWeight

variable {z : RootCoordinates Q}
variable {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
variable {lam : D.X}
variable (V : RationalHighestWeight z e h lam)
include e h

abbrev space := Index.{u} V.dimension → RationalField.{u}

def rootOperator (a : D.I) : Matrix (Index.{u} V.dimension) (Index.{u} V.dimension) RationalField.{u} :=
  V.envelopingAction (UniversalEnvelopingAlgebra.ι RationalField (e a))

/-- A coefficient of the ordered negative-root product on the highest vector. -/
def negativeCoefficient (negative : List (Negative D)) (m : Negative D →₀ ℕ) : V.space :=
  ((negative.map (fun a : Negative D => dividedPower (V.rootOperator a.val) (m a))).prod).mulVec V.highest

/-- The integer span of the coefficients of the big cell on the highest vector.
The positive factors fix that vector and the torus contributes integral series
with constant term one, so only the negative factors enter the generators. -/
def lattice (negative : List (Negative D)) : Submodule ℤ V.space :=
  Submodule.span ℤ (Set.range (V.negativeCoefficient negative))

/-- The weight space in the chosen rational basis. -/
def weightSpace (μ : D.X) : Submodule RationalField.{u} V.space where
  carrier := {v | ∀ j, V.weight j ≠ μ → v j = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw j hj; simp [hv j hj, hw j hj]
  smul_mem' := by intro c v hv j hj; simp [hv j hj]

def IsIntegralLattice (negative : List (Negative D)) : Prop :=
  let L := V.lattice negative
  Module.Finite ℤ L ∧ Module.Free ℤ L ∧
  Submodule.span RationalField.{u} (L : Set V.space) = ⊤ ∧
  (⨆ μ, L ⊓ (V.weightSpace μ).restrictScalars ℤ) = L ∧
  L ⊓ (V.weightSpace lam).restrictScalars ℤ = Submodule.span ℤ {V.highest} ∧
  ∀ a m v, v ∈ L → (dividedPower (V.rootOperator a) m).mulVec v ∈ L

end RationalHighestWeight

end HighestWeight

/-- The coordinate criterion for the diagonal split torus with the specified
weights to embed as a closed subgroup. Negative characters account for the
inverse diagonal entries. -/
def TorusCoordinatesGenerate {n : ℕ} (w : Index.{u} n → D.X) : Prop :=
  Algebra.adjoin ℤ
    (Set.range (fun i => (AddMonoidAlgebra.single (w i) 1 : AddMonoidAlgebra ℤ D.X)) ∪
     Set.range (fun i => (AddMonoidAlgebra.single (-w i) 1 : AddMonoidAlgebra ℤ D.X))) = ⊤

/-- Indices for the freely varying entries of the relevant unitriangular group. -/
def triangularEntries (n : ℕ) (upper : Bool) :=
  {ij : Index.{u} n × Index.{u} n // if upper then ij.1 < ij.2 else ij.2 < ij.1}

/-- The ordered product in its own root variables over the integers. -/
def orderedMatrix {n : ℕ} {σ : Type u} (l : List σ)
    (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) :
    Matrix (Index.{u} n) (Index.{u} n) (MvPolynomial σ ℤ) :=
  (l.map (fun a => (Polynomial.aeval (MvPolynomial.X a)).toRingHom.mapMatrix (p a))).prod

/-- The product lands in the specified unitriangular group. Each root
coordinate is the restriction of an integral polynomial in the available
entries, giving a surjective coordinate map. The closed image is a subgroup. -/
def ClosedRootImage {n : ℕ} {σ : Type u} (upper : Bool)
    (P : Matrix (Index.{u} n) (Index.{u} n) (MvPolynomial σ ℤ)) : Prop :=
  (∀ i j, (if upper then ¬ i < j else ¬ j < i) → P i j = (1 : Matrix _ _ _) i j) ∧
  (∀ a : σ, ∃ p : MvPolynomial (triangularEntries n upper) ℤ,
    MvPolynomial.aeval (fun ij => P ij.val.1 ij.val.2) p = MvPolynomial.X a) ∧
  ∀ (R : Type u) [CommRing R], ∃ f : (σ → R) → Matrix.GeneralLinearGroup (Index.{u} n) R,
    (∀ x, (f x).val = (MvPolynomial.eval₂Hom (Int.castRingHom R) x).mapMatrix P) ∧
    ∃ H : Subgroup (Matrix.GeneralLinearGroup (Index.{u} n) R), Set.range f = H

/-- The fundamental highest-weight lattices for the semisimple coroot-lattice
datum, together with the integral matrix realization of their ordered root
products. -/
def Statement : Prop :=
  ∀ (D : BasedRootDatum.{u}), RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∃ (A : AdditiveLine RationalField.{u}) (Q : Realization D A) (z : RootCoordinates Q)
      (s : IdentityLieStructure Q.pinned.pair.G.val),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ (e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val)
      (ω : Module.Basis D.base.support ℤ D.X),
    IsChevalley Q z ∧ OppositeRootRelations Q z ∧ IndependentRootRelations Q z ∧
    FormalBigCellProduct Q z ∧
    (∀ a, IsRootTangent Q z a (e a) ∧
      (h a).toMul.val = IntegralRootRelations.torus Q (D.datum.coroot a)
        (CommAlgCat.of _ (DualNumber RationalField.{u})) dualUnit) ∧
    (∀ i j : D.base.support, D.datum.coroot' j (ω i) = if j = i then 1 else 0) ∧
    ∀ (negative : List (Negative D)) (positive : List (Positive D)),
      Enumerates negative Set.univ → Enumerates positive Set.univ →
      ∃ (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
        (n : ℕ)
        (b : Module.Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
        (w : Index.{u} n → D.X)
        (height : D.X →ₗ[ℤ] ℤ)
        (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)),
        (∀ i, (V i).IsIntegralLattice negative) ∧
        Submodule.span ℤ (Set.range b) = Submodule.pi Set.univ
          (fun i => (V i).lattice negative) ∧
        (∀ j i, b j i ∈ (V i).weightSpace (w j)) ∧
        Antitone (height ∘ w) ∧
        (∀ a : Positive D, 0 < height (D.datum.root a)) ∧
        (∀ a : Negative D, height (D.datum.root a) < 0) ∧
        TorusCoordinatesGenerate w ∧
        (∀ (a : D.I) (m : ℕ) (j : Index.{u} n) (i : D.base.support),
          ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
            (dividedPower ((V i).rootOperator a) m).mulVec (b j i)) ∧
        (∀ a : D.I, ∃ (μ : D.X) (v : Index.{u} n → ℤ) (φ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ),
          (∀ j, w j ≠ μ → v j = 0) ∧
          (∀ j, w j ≠ μ + D.datum.root a → φ (Pi.single j 1) = 0) ∧
          φ ((Matrix.of (fun l j => (p a l j).coeff 1)).mulVec v) = 1) ∧
        ClosedRootImage false (orderedMatrix negative (fun a => p a.val)) ∧
        ClosedRootImage true (orderedMatrix positive (fun a => p a.val))

end

end LinearAlgebraicGroups.Specs.IntegralLattices
