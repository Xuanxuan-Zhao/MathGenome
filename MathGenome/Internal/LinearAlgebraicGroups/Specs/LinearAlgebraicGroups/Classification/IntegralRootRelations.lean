import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.RationalRealization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.Data.Nat.Choose.Basic
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RankTwoRootSystems

open AlgebraicGeometry CategoryTheory
open scoped Matrix TensorProduct BigOperators

universe u

namespace LinearAlgebraicGroups.Specs.IntegralRootRelations

open Pinning (BasedRootDatum RootCoordinate)
open RationalRealization (RationalField Realization)
open RootGroups (AdditiveLine rootPoint)
open OrderedRootProducts (Enumerates)
open AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

noncomputable section

section RankOne
variable {R : Type u} [CommRing R]

/-- The upper elementary matrix in the rank-one action. -/
def upper (x : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- The lower elementary matrix in the rank-one action. -/
def lower (y : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; y, 1], by simp [Matrix.det_fin_two]⟩

/-- The rank-one diagonal carrying the given unit and its inverse. -/
def diagonal (s : Rˣ) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![(s : R), 0; 0, (↑s⁻¹ : R)], by simp [Matrix.det_fin_two]⟩

/-- The opposite-root calculation on the locus where the denominator is a unit. -/
def OppositeRootMatrix : Prop :=
  ∀ {R : Type u} [CommRing R] (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
    upper x * lower y = lower (y * (↑s⁻¹ : R)) * diagonal s * upper (x * (↑s⁻¹ : R))
end RankOne

namespace RankTwo

open LieAlgebrasAndRepresentations (RankTwoKind rankTwoCoefficients)

abbrev Lattice := ℤ × ℤ

/-- The root-string coordinate of `b + i*a` in the rank-two model. -/
def step (a b : Lattice) (i : ℤ) : Lattice := (b.1 + i * a.1, b.2 + i * a.2)

def rootString (R : Finset Lattice) (a b : Lattice) : Finset ℕ :=
  (Finset.range 4).filter (fun i => step a b i ∈ R)

def backwardLength (R : Finset Lattice) (a b : Lattice) : ℕ :=
  ((Finset.range 4).filter (fun i : ℕ => step a b (-(i : ℤ)) ∈ R)).sup id

def bracketPairs (R : Finset Lattice) (a b : Lattice) : Finset (ℕ × ℕ) :=
  ((rootString R a b) ×ˢ (rootString R a b)).filter (fun ij =>
    ij.1 < ij.2 ∧ step (step a b ij.1) (step a b ij.2) 1 ∈ R)

/-- The absolute Chevalley bracket coefficient after dividing the two string terms by factorials. -/
def bracketMagnitude (R : Finset Lattice) (a b : Lattice) (ij : ℕ × ℕ) : ℕ :=
  let p := backwardLength R a b
  (p + ij.1).choose ij.1 * (p + ij.2).choose ij.2 *
    (1 + backwardLength R (step a b ij.1) (step a b ij.2))

def squaredLength (kind : RankTwoKind) (a : Lattice) : ℤ :=
  match kind with
  | .A₁A₁ => a.1 ^ 2 + a.2 ^ 2
  | .A₂ => 2 * a.1 ^ 2 - 2 * a.1 * a.2 + 2 * a.2 ^ 2
  | .B₂ => 2 * a.1 ^ 2 - 4 * a.1 * a.2 + 4 * a.2 ^ 2
  | .G₂ => 2 * a.1 ^ 2 - 6 * a.1 * a.2 + 6 * a.2 ^ 2

/-- Each central root coefficient of the signed bracket sum is even
in the shorter-first orientation of the rank-two calculation. -/
def CentralBracketCoefficientsIntegral : Prop :=
  ∀ (kind : RankTwoKind)
    (a b : Lattice), a ∈ rankTwoCoefficients kind → b ∈ rankTwoCoefficients kind →
    a.1 * b.2 - a.2 * b.1 ≠ 0 →
    (kind = .A₁A₁ ∨ squaredLength kind a ≤ squaredLength kind b) →
    ∀ c : ℕ × ℕ → ℤ,
    (∀ ij ∈ bracketPairs (rankTwoCoefficients kind) a b,
      let m := (bracketMagnitude (rankTwoCoefficients kind) a b ij : ℤ)
      c ij = m ∨ c ij = -m) →
    ∀ ij ∈ bracketPairs (rankTwoCoefficients kind) a b,
      ∃ n : ℤ, (∑ pq ∈ (bracketPairs (rankTwoCoefficients kind) a b).filter
          (fun pq => pq.1 + pq.2 = ij.1 + ij.2), c pq) = 2 * n

end RankTwo

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})} (Q : Realization D A)

/-- The actual root of the pinned rational group carrying the input label. -/
abbrev rootIndex (i : D.I) := Q.datumIso.val.indexEquiv i

/-- Root coordinates in the specified rational realization. -/
abbrev RootCoordinates :=
  ∀ i : D.I, RootCoordinate A Q.pinned.pair.T
    (Q.pinned.roots (rootIndex Q i)).val (rootIndex Q i).val

/-- Evaluate a chosen root coordinate as a point of the rational group. -/
def root (z : RootCoordinates Q) (i : D.I) (R : TestAlgebra (RationalField.{u})) (x : R) :
    GroupPoints Q.pinned.pair.G.val R :=
  rootPoint ((z i).val.hom ≫ (Q.pinned.roots (rootIndex Q i)).val.inclusion) R x

/-- Evaluate a lattice cocharacter, using the marking of the actual rational torus. -/
def torus (v : D.Y) (R : TestAlgebra (RationalField.{u})) (s : Rˣ) :
    GroupPoints Q.pinned.pair.G.val R :=
  cocharacterPoint (Additive.toMul (Q.datumIso.val.coweightEquiv.symm v)) R s ≫
    Q.pinned.pair.T.inclusion.hom.hom

/-- Endpoints of the string through j in direction i are measured
in the original character lattice. -/
def IsRootString (i j : D.I) (p q : ℕ) : Prop :=
  ∀ n : ℤ, D.datum.root j + n • D.datum.root i ∈ Set.range D.datum.root ↔
    -(p : ℤ) ≤ n ∧ n ≤ (q : ℤ)

/-- A tangent of an actual coordinate at the standard dual number. -/
def IsRootTangent (z : RootCoordinates Q) (i : D.I)
    (e : Lie (RationalField.{u}) Q.pinned.pair.G.val) : Prop :=
  e.toMul.val = root Q z i (CommAlgCat.of _ (DualNumber (RationalField.{u}))) DualNumber.eps

def dualUnit : (DualNumber (RationalField.{u}))ˣ :=
  (IsNilpotent.isUnit_one_add (show IsNilpotent (DualNumber.eps :
    DualNumber (RationalField.{u})) from ⟨2, by simp [pow_two]⟩)).unit

/-- The Chevalley basis with the specified simple pinning and marked coroots.
The constants have the root-string magnitude and the opposite-root signs of F05
in *Lie Algebras and Finite-Dimensional Representations*. -/
def IsChevalley (z : RootCoordinates Q) : Prop :=
  (∀ i : D.base.support, z i.val = Q.pinned.pin (Q.simpleRoot i)) ∧
  ∃ s : IdentityLieStructure Q.pinned.pair.G.val,
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ (e : D.I → Lie (RationalField.{u}) Q.pinned.pair.G.val)
      (h : D.I → Lie (RationalField.{u}) Q.pinned.pair.G.val)
      (B : Module.Basis (D.base.support ⊕ D.I) (RationalField.{u})
        (Lie (RationalField.{u}) Q.pinned.pair.G.val)),
      (∀ i, IsRootTangent Q z i (e i) ∧
        (h i).toMul.val = torus Q (D.datum.coroot i)
          (CommAlgCat.of _ (DualNumber (RationalField.{u}))) dualUnit.{u}) ∧
      (∀ i : D.base.support, B (.inl i) = h i) ∧
      (∀ i, B (.inr i) = e i) ∧
      (∀ i j, D.datum.root j = -D.datum.root i → ⁅e i, e j⁆ = h i) ∧
      (∀ i j k, D.datum.root i + D.datum.root j = D.datum.root k →
        ∃ (p q : ℕ) (n : ℤ), IsRootString i j p q ∧
          (n = (p : ℤ) + 1 ∨ n = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = n • e k ∧
          ⁅e (D.datum.reflectionPerm i i), e (D.datum.reflectionPerm j j)⁆ =
            (-n) • e (D.datum.reflectionPerm k k)) ∧
      (∀ i j, D.datum.root i + D.datum.root j ≠ 0 →
        D.datum.root i + D.datum.root j ∉ Set.range D.datum.root → ⁅e i, e j⁆ = 0) ∧
      (∀ i j, ⁅h i, h j⁆ = 0) ∧
      (∀ i j, ⁅h i, e j⁆ = D.datum.pairing j i • e j) ∧
      (∀ a b c, ∃ n : ℤ, B.repr ⁅B a, B b⁆ c = (n : RationalField.{u}))

/-- Opposite roots obey the rank-one factorization with the marked coroot. -/
def OppositeRootRelations (z : RootCoordinates Q) : Prop :=
  ∀ i j : D.I, D.datum.root j = -D.datum.root i →
    ∀ (R : TestAlgebra (RationalField.{u})) (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
      root Q z i R x * root Q z j R y =
        root Q z j R (y * (↑s⁻¹ : R)) * torus Q (D.datum.coroot i) R s *
          root Q z i R (x * (↑s⁻¹ : R))

/-- Independence in the rationalized character lattice. -/
def IndependentRoots (i j : D.I) : Prop :=
  LinearIndependent ℚ ![(1 : ℚ) ⊗ₜ[ℤ] D.datum.root i, (1 : ℚ) ⊗ₜ[ℤ] D.datum.root j]

/-- One labelled root of the strictly positive cone on two independent roots. -/
structure ConeRoot (i j : D.I) where
  leftDegree : ℕ+
  rightDegree : ℕ+
  index : D.I
  root_eq : D.datum.root index =
    (leftDegree : ℕ) • D.datum.root i + (rightDegree : ℕ) • D.datum.root j

/-- The commutator uses each cone root in the specified order, with an integer
coefficient of its bidegree, over every rational test algebra. -/
def IndependentRootRelations (z : RootCoordinates Q) : Prop :=
  ∀ i j : D.I, IndependentRoots i j →
    ∀ l : List (ConeRoot i j), Enumerates l Set.univ →
      ∃ c : ConeRoot i j → ℤ,
        ∀ (R : TestAlgebra (RationalField.{u})) (x y : R),
          root Q z i R x * root Q z j R y *
            (root Q z i R x)⁻¹ * (root Q z j R y)⁻¹ =
          (l.map (fun a => root Q z a.index R
            ((c a : R) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ)))).prod

/-- The ordered negative-root, torus, positive-root coordinates. -/
def cellPoint {r : ℕ} (z : RootCoordinates Q) (b : Module.Basis (Fin r) ℤ D.Y)
    (negative positive : List D.I) (R : TestAlgebra (RationalField.{u}))
    (v : D.I → R) (t : Fin r → Rˣ) : GroupPoints Q.pinned.pair.G.val R :=
  (negative.map (fun i => root Q z i R (v i))).prod *
  ((List.finRange r).map (fun i => torus Q (b i) R (t i))).prod *
  (positive.map (fun i => root Q z i R (v i))).prod

/-- Two independent copies of the root and torus variables of the big cell. -/
abbrev CellVariables (D : BasedRootDatum.{u}) (r : ℕ) := Bool × (D.I ⊕ Fin r)

/-- A series centered at the identity gives a unit by adding one. -/
def onePlusSeries {σ K : Type u} [CommRing K] (f : MvPowerSeries σ K)
    (hf : f.constantCoeff = 0) : (MvPowerSeries σ K)ˣ :=
  (MvPowerSeries.isUnit_iff_constantCoeff.mpr (show IsUnit (1 + f).constantCoeff by
    rw [map_add, map_one, hf, add_zero]; exact isUnit_one)).unit

/-- The rank-one denominator has constant coefficient one and is a unit
even in the integer formal coordinates. -/
def RankOneDenominator : Prop :=
  ∀ {σ : Type u} (x y : MvPowerSeries σ ℤ), x.constantCoeff = 0 →
    (1 + x * y).constantCoeff = 1 ∧ IsUnit (1 + x * y)

/-- A centered integral series is a root parameter or the change from one
of a multiplicative torus parameter. -/
abbrev CenteredSeries (σ : Type u) :=
  {f : MvPowerSeries σ ℤ // f.constantCoeff = 0}

abbrev CellAlgebra (D : BasedRootDatum.{u}) (r : ℕ) : TestAlgebra (RationalField.{u}) :=
  CommAlgCat.of _ (MvPowerSeries (CellVariables D r) (RationalField.{u}))

/-- One of the two universal cells at the identity, over the rational
series algebra on the full set of input variables. -/
def genericCellPoint {r : ℕ} (z : RootCoordinates Q) (b : Module.Basis (Fin r) ℤ D.Y)
    (negative positive : List D.I) (side : Bool) :
    GroupPoints Q.pinned.pair.G.val (CellAlgebra D r) :=
  cellPoint Q z b negative positive (CellAlgebra D r)
    (fun i => MvPowerSeries.X (side, .inl i))
    (fun i => onePlusSeries (MvPowerSeries.X (side, .inr i)) (MvPowerSeries.constantCoeff_X _))

/-- Evaluate centered integer series in the marked rational cell. -/
def integralCellPoint {r : ℕ} (z : RootCoordinates Q) (b : Module.Basis (Fin r) ℤ D.Y)
    (negative positive : List D.I) (f : D.I ⊕ Fin r → CenteredSeries (CellVariables D r)) :
    GroupPoints Q.pinned.pair.G.val (CellAlgebra D r) :=
  let F := fun i => MvPowerSeries.map (Int.castRingHom (RationalField.{u})) (f i).val
  cellPoint Q z b negative positive (CellAlgebra D r) (fun i => F (.inl i))
    (fun i => onePlusSeries (F (.inr i)) (by simp [F, (f (.inr i)).property]))

/-- The formal product is expressed by integer series in the two sets of
parameters, with zero root constants and torus constants one. Its integer
polynomial truncations agree coefficientwise in every total degree. -/
def FormalBigCellProduct (z : RootCoordinates Q) : Prop :=
  ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ D.Y) (negative positive : List D.I),
    Enumerates negative {i | ¬ D.base.IsPos i} → Enumerates positive {i | D.base.IsPos i} →
    ∃ (f : D.I ⊕ Fin r → CenteredSeries (CellVariables D r)),
      genericCellPoint Q z b negative positive false * genericCellPoint Q z b negative positive true =
        integralCellPoint Q z b negative positive f ∧
      (letI : Finite D.I := D.finiteRoots
       ∃ p : ℕ → D.I ⊕ Fin r → MvPolynomial (CellVariables D r) ℤ,
        (∀ m i, p m i = MvPowerSeries.truncTotal (m + 1) (f i).val) ∧
        ∀ m n i d, m ≤ n → d.degree ≤ m → (p m i).coeff d = (p n i).coeff d)

/-- Fundamental weights form the basis dual to the simple coroots when the
cocharacters are the coroot lattice. -/
def FundamentalWeights : Prop :=
  ∀ D : BasedRootDatum.{u}, Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∃ b : Module.Basis D.base.support ℤ D.X,
      ∀ i, D.datum.toLinearMap (b i) (D.datum.coroot i) = 1 ∧
        ∀ j, j ≠ i → D.datum.toLinearMap (b i) (D.datum.coroot j) = 0

/-- The same Chevalley coordinates satisfy both sets of root relations and
give the integral multiplication in the chosen cell. -/
def HasIntegralRootRelations : Prop :=
  ∃ z : RootCoordinates Q, IsChevalley Q z ∧ OppositeRootRelations Q z ∧
    IndependentRootRelations Q z ∧ FormalBigCellProduct Q z

/-- The relations apply to a specified marked rational realization. -/
def RelationsInRealization : Prop :=
  ∀ D : BasedRootDatum.{u}, RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∀ (A : AdditiveLine (RationalField.{u})) (Q : Realization D A), HasIntegralRootRelations Q

/-- The integral root and big-cell relations for the semisimple rational model
whose cocharacter lattice is generated over the integers by the coroots. -/
def Statement : Prop :=
  ∀ D : BasedRootDatum.{u}, RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∃ (A : AdditiveLine (RationalField.{u})) (Q : Realization D A), HasIntegralRootRelations Q

end

end LinearAlgebraicGroups.Specs.IntegralRootRelations
