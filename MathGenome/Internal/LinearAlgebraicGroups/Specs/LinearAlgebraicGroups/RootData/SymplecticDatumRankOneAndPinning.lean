import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import Mathlib.Data.Matrix.Basis
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Reindex

open AlgebraicGeometry CategoryTheory Matrix
open scoped Matrix BigOperators

universe u v

namespace LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning

open SymplecticMatrixStructure
open AdjointRepresentation (GroupPoints)
open AbstractPairing (Root IsAttachedCoroot)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (characterValue)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open OrderedRootProducts (RootSubgroupFamily)
open Pinning (SplitBorelPair SimpleRoot RootCoordinate)
open RootGroups (AdditiveLine IsRootSubgroup rootPoint)
open SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition cocharacterPoint)

noncomputable section

abbrev SL₂ (R : Type u) [CommRing R] := Matrix.SpecialLinearGroup (Fin 2) R

/-- The second index in the hyperbolic pair of a signed coordinate. -/
def partner {I : Type u} : Indices I → Indices I :=
  Sum.swap

/-- The underlying unsigned coordinate. -/
def coordinate {I : Type u} : Indices I → I := Sum.elim id id

/-- The pairing of a signed basis vector with its partner for Mathlib's `J`. -/
def pairingSign {I : Type u} (R : Type v) [CommRing R] : Indices I → R :=
  Sum.elim (fun _ => -1) (fun _ => 1)

/-- First and second basis vector of an ordered pair. -/
def orderedPair {A : Type u} (p q : A) (h : p ≠ q) : Fin 2 ↪ A where
  toFun := ![p, q]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

def longFrame {I : Type u} (p : Indices I) : Fin 2 ↪ Indices I :=
  orderedPair p (partner p) (by cases p <;> simp [partner])

/-- The short-root frame consists of the two signed vectors, followed by their
ordered partners. The partners are rescaled in the matrix formula below. -/
def shortFrame {I : Type u} (p q : Indices I) (h : coordinate p ≠ coordinate q) :
    (Fin 2 ⊕ Fin 2) ↪ Indices I where
  toFun := Sum.elim ![p, q] ![partner p, partner q]
  inj' := by
    rintro (i | i) (j | j) hij <;> fin_cases i <;> fin_cases j
    all_goals
      simp only [Sum.elim_inl, Sum.elim_inr] at hij
      first
      | rfl
      | have hh := congrArg coordinate hij
        rcases p with a | a <;> rcases q with b | b <;>
          simp_all [coordinate, partner]

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The displayed coordinates, followed by their complement. -/
def frameEquiv (e : A ↪ B) : A ⊕ ↥((Set.range e)ᶜ : Set B) ≃ B :=
  letI : DecidablePred (· ∈ Set.range e) := Classical.decPred _
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

/-- Act by a matrix on the displayed coordinates and by the identity
on the complement. -/
def extendMatrix {R : Type*} [CommRing R] (e : A ↪ B) (M : Matrix A A R) :
    Matrix B B R :=
  Matrix.reindex (frameEquiv e) (frameEquiv e) (Matrix.fromBlocks M 0 0 1)

/-- Upper and lower transvections in the determinant-one source group. -/
def upper {R : Type u} [CommRing R] (a : R) : SL₂ R :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

def lower {R : Type u} [CommRing R] (a : R) : SL₂ R :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

def diagonal {R : Type u} [CommRing R] (a : Rˣ) : SL₂ R :=
  ⟨!![↑a, 0; 0, ↑a⁻¹], by simp [Matrix.det_fin_two]⟩

variable {I : Type u} [Fintype I] [DecidableEq I] {R : Type u} [CommRing R]

def shortSigns (R : Type u) [CommRing R] (p q : Indices I) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.diagonal ![pairingSign R p, pairingSign R q]

/-- On the partners the block is inverse transpose in the dual basis.
The two diagonal sign matrices convert to and from that basis. -/
def pairedBlock (p q : Indices I) (g : SL₂ R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  let D := shortSigns R p q
  Matrix.fromBlocks g.val 0 0 (D * (g⁻¹).valᵀ * D)

def longMatrix (p : Indices I) (g : SL₂ R) : Matrix (Indices I) (Indices I) R :=
  extendMatrix (longFrame p) g.val

def shortMatrix (p q : Indices I) (h : coordinate p ≠ coordinate q) (g : SL₂ R) :
    Matrix (Indices I) (Indices I) R :=
  extendMatrix (shortFrame p q h) (pairedBlock p q g)

/-- Test-algebra determinant-one group functor. -/
def determinantOnePoints (k : Type u) [Field k] : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (SL₂ R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro g; exact Subtype.ext rfl
  map_comp _ _ := by apply GrpCat.ext; intro g; exact Subtype.ext rfl

/-- The construction for all signed long roots, over all test algebras. -/
def LongMaps : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (p : Indices I),
    ∃ F : determinantOnePoints k ⟶ symplecticPoints k I,
      ∀ (R : TestAlgebra k) (g : SL₂ R),
        (show PointGroup I R from F.app R g).val = longMatrix p g

/-- The construction for all signed short roots, over all test algebras. -/
def ShortMaps : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (p q : Indices I)
    (h : coordinate p ≠ coordinate q),
    ∃ F : determinantOnePoints k ⟶ symplecticPoints k I,
      ∀ (R : TestAlgebra k) (g : SL₂ R),
        (show PointGroup I R from F.app R g).val = shortMatrix p q h g

/-- An ordered presentation of a signed root. The short presentations allow
either order; reversing appropriate signed coordinates may present the same root. -/
inductive RootIndex (I : Type u)
  | long (p : Indices I)
  | short (p q : Indices I) (distinct : coordinate p ≠ coordinate q)

namespace RootIndex

variable {I : Type u}

def first : RootIndex I → Indices I
  | .long p => p
  | .short p _ _ => p

def second : RootIndex I → Indices I
  | .long p => partner p
  | .short _ q _ => q

def matrix [Fintype I] [DecidableEq I] (r : RootIndex I) {R : Type u} [CommRing R]
    (g : SL₂ R) : Matrix (Indices I) (Indices I) R :=
  match r with
  | .long p => longMatrix p g
  | .short p q h => shortMatrix p q h g

variable [DecidableEq I]

def signedCoordinate : Indices I → (I → ℤ)
  | .inl i => Pi.single i 1
  | .inr i => Pi.single i (-1)

def weight (r : RootIndex I) : I → ℤ :=
  signedCoordinate r.first - signedCoordinate r.second

def coroot : RootIndex I → (I → ℤ)
  | .long p => signedCoordinate p
  | .short p q _ => signedCoordinate p - signedCoordinate q

/-- The two transvections in the ordered frame, with their companions on the
paired plane for a short root. -/
def upperMatrix [Fintype I] {R : Type u} [CommRing R] (r : RootIndex I) (a : R) :
    Matrix (Indices I) (Indices I) R :=
  match r with
  | .long p => 1 + Matrix.single p (partner p) a
  | .short p q _ => 1 + Matrix.single p q a +
      Matrix.single (partner q) (partner p) (-(pairingSign R p * pairingSign R q) * a)

def lowerMatrix [Fintype I] {R : Type u} [CommRing R] (r : RootIndex I) (a : R) :
    Matrix (Indices I) (Indices I) R :=
  match r with
  | .long p => 1 + Matrix.single (partner p) p a
  | .short p q _ => 1 + Matrix.single q p a +
      Matrix.single (partner p) (partner q) (-(pairingSign R p * pairingSign R q) * a)

end RootIndex

/-- The eigenvalue of a hyperbolic diagonal on a signed basis vector. -/
def signedUnit {I : Type u} {R : Type u} [CommRing R] (t : I → Rˣ) (p : Indices I) : Rˣ :=
  Sum.elim t (fun i => (t i)⁻¹) p

def torusTuple {I : Type u} (y : I → ℤ) {R : Type u} [CommRing R] (a : Rˣ) : I → Rˣ :=
  fun i => a ^ y i

/-- The formulas in the original hyperbolic basis, including the cocharacter
on each coordinate of the diagonal torus. -/
def MatrixValues : Prop :=
  ∀ (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R] (r : RootIndex I),
    (∀ a : R, r.matrix (upper a) = r.upperMatrix a) ∧
    (∀ a : R, r.matrix (lower a) = r.lowerMatrix a) ∧
    (∀ a : Rˣ, r.matrix (diagonal a) = hyperbolicDiagonal (torusTuple r.coroot a))

/-- The action into the given represented symplectic group, with its matrix
comparison. -/
def RepresentedMaps : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I) (r : RootIndex I),
    ∃ F : determinantOnePoints k ⟶ (groupPointsFunctor k).obj G.val,
      ∀ (R : TestAlgebra k) (g : SL₂ R),
        (show PointGroup I R from c.hom.app R (F.app R g)).val = r.matrix g

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]

/-- Marking of the actual closed diagonal torus, on all test algebras. -/
structure DiagonalMarking {G : AffineAlgebraicGroup k}
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I) (T : ClosedSubgroup G.val) where
  points : (groupPointsFunctor k).obj T.group ≅ StandardGroups.multiplicativePowerPoints k I
  diagonal_value : ∀ (R : TestAlgebra k) (t : GroupPoints T.group R),
    (show PointGroup I R from c.hom.app R (t ≫ T.inclusion.hom.hom)).val =
      hyperbolicDiagonal (points.hom.app R t)

/-- Character value of the signed difference. The two factors are the
monomials of the signed coordinate vectors; for a long root the second signed
coordinate is the partner of the first. -/
def MatchesRoot {G : AffineAlgebraicGroup k}
    {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I} {T : ClosedSubgroup G.val}
    (m : DiagonalMarking c T) (r : RootIndex I) (α : Character T.group) : Prop :=
  ∀ (R : TestAlgebra k) (t : GroupPoints T.group R),
    let z := m.points.hom.app R t
    characterValue α R t = ↑(signedUnit z r.first / signedUnit z r.second)

/-- The root matching condition is precisely the Laurent monomial of
the signed root vector in the marked character lattice. -/
def RootMonomialValues : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I] {G : AffineAlgebraicGroup k}
    {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I} {T : ClosedSubgroup G.val}
    (m : DiagonalMarking c T) (r : RootIndex I) (α : Character T.group),
    MatchesRoot m r α ↔
      ∀ (R : TestAlgebra k) (t : GroupPoints T.group R),
        characterValue α R t = ↑(∏ i, (m.points.hom.app R t) i ^ r.weight i)

/-- The representation has its actual split maximal torus with this marking. -/
def DiagonalMarkingExists : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I),
    ∃ T : ClosedSubgroup G.val,
      IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧ Nonempty (DiagonalMarking c T)

/-- The determinant-one source is represented, and the natural maps come from
homomorphisms of the represented groups. -/
def RepresentedSchemeMaps : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (S : AffineAlgebraicGroup k)
      (e : (groupPointsFunctor k).obj S.val ≅ determinantOnePoints k),
      ∀ (I : Type u) [Fintype I] [DecidableEq I] (G : AffineAlgebraicGroup k)
        (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I) (r : RootIndex I),
        ∃ f : S.val ⟶ G.val,
          ∀ (R : TestAlgebra k) (g : SL₂ R),
            (show PointGroup I R from
              c.hom.app R (((groupPointsFunctor k).map f).app R (e.inv.app R g))).val =
              r.matrix g

/-- The elementary matrices are coordinates on the actual opposite root
groups. Both use the same determinant-one homomorphism's parameter. -/
def RankOneCoordinates : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I] {G : AffineAlgebraicGroup k}
    {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I} {T : ClosedSubgroup G.val}
    (m : DiagonalMarking c T) (r : RootIndex I) (α : Character T.group),
    MatchesRoot m r α → ∀ A : AdditiveLine k,
      ∃ (U V : ClosedSubgroup G.val) (x : RootCoordinate A T U α)
        (y : RootCoordinate A T V α⁻¹),
        IsRootSubgroup T U α ∧ IsRootSubgroup T V α⁻¹ ∧
        ∀ (R : TestAlgebra k) (a : R),
          (show PointGroup I R from c.hom.app R (rootPoint (x.val.hom ≫ U.inclusion) R a)).val =
            r.matrix (upper a) ∧
          (show PointGroup I R from c.hom.app R (rootPoint (y.val.hom ≫ V.inclusion) R a)).val =
            r.matrix (lower a)

/-- Identification of every coroot attached by the marked flag construction
with the indicated signed torus monomial. -/
def AttachedCorootValues : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I] {G : AffineAlgebraicGroup k}
    {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I} {T : ClosedSubgroup G.val}
    (m : DiagonalMarking c T), IsReductive G → IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ (r : RootIndex I) (α : Root T), MatchesRoot m r α.val →
      (∃ cochar, IsAttachedCoroot T α cochar) ∧
      ∀ cochar, IsAttachedCoroot T α cochar →
        ∀ (R : TestAlgebra k) (a : Rˣ),
          m.points.hom.app R (cocharacterPoint cochar R a) = torusTuple r.coroot a

/-- A pinning on the regular limit Borel for the diagonal with decreasing
exponents. The pinning uses the upper determinant-one entry for every
simple root in the marked root enumeration. -/
def SimplePinning : Prop :=
  ∀ {k : Type u} [Field k] (n : ℕ) {G : AffineAlgebraicGroup k}
    {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k (ULift.{u} (Fin (n + 1)))}
    {T : ClosedSubgroup G.val} (m : DiagonalMarking c T)
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (lambda : Cocharacter T.group),
    (∀ (R : TestAlgebra k) (a : Rˣ) (i : ULift.{u} (Fin (n + 1))),
      (m.points.hom.app R (cocharacterPoint lambda R a)) i = a ^ (n + 1 - i.down.val)) →
    ∀ (r : Root T → RootIndex (ULift.{u} (Fin (n + 1)))),
      (∀ α, MatchesRoot m (r α) α.val) →
      Nonempty (LimitDecomposition (lambda ≫ T.inclusion)) ∧
      ∀ (D : LimitDecomposition (lambda ≫ T.inclusion)) (A : AdditiveLine k),
        ∃ (hB : IsKBorel D.parabolic) (hTB : IsSubgroupOf T D.parabolic),
          let P : SplitBorelPair k := ⟨G, hG, T, hT, hm, D.parabolic, hB, hTB⟩
          ∃ (U : RootSubgroupFamily T) (p : Pinning.Pinning A P U),
            ∀ (α : SimpleRoot P) (R : TestAlgebra k) (a : R),
              (show PointGroup (ULift.{u} (Fin (n + 1))) R from
                c.hom.app R (rootPoint ((p α).val.hom ≫ (U α.val).val.inclusion) R a)).val =
                (r α.val).matrix (upper a)

end

end LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning
