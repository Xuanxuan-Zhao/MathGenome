import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RationalContraction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FunctionFieldClosedOrbitWeights

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open ClosedHomogeneousOrbits (vectorPoint vectorSpace)
open GeneralLinearStructure (SpecialMatrixPoints)
open GeometricRadicals (IsSemisimple)
open RationalContraction (ActionHasLimit groundField)
open RootWeightAction (Representation act)
open SpecialLinearDatum (CocharacterLattice exponentDot)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
  {m : ℕ} {P : AffineAlgebraicGroup k}

/-- The linear change from the given coordinates to weight coordinates,
extended to the chosen test algebra. -/
def coordinates (C : Matrix.GeneralLinearGroup I k) (R : TestAlgebra k) (v : I → R) : I → R :=
  (Matrix.GeneralLinearGroup.map (algebraMap k R) C).val.mulVec v

/-- The coordinate basis for the determinant-one diagonal torus, with integer
monomial representatives of its characters and the corresponding cocharacters. -/
structure DiagonalWeightCoordinates (s : SpecialMatrixPoints P m)
    (ρ : Representation P.val I) where
  changeBasis : Matrix.GeneralLinearGroup I k
  exponents : I → Fin m → ℤ
  cocharacter : CocharacterLattice m → Cocharacter P.val
  diagonal_action : ∀ (R : TestAlgebra k) (d : Fin m → Rˣ) (g : GroupPoints P.val R),
    (s.hom.app R g).val = Matrix.diagonal (fun i => (d i.down : R)) →
    ∀ (v : I → R) (i : I), coordinates changeBasis R (act ρ R g v) i =
      (↑(∏ j : Fin m, d j ^ exponents i j) : R) * coordinates changeBasis R v i
  cocharacter_matrix : ∀ (n : CocharacterLattice m) (R : TestAlgebra k) (t : Rˣ),
    (s.hom.app R (cocharacterPoint (cocharacter n) R t)).val =
      Matrix.diagonal (fun j => (↑(t ^ n.val j.down) : R))
  cocharacter_action : ∀ (n : CocharacterLattice m) (R : TestAlgebra k) (t : Rˣ)
    (v : I → R) (i : I),
    coordinates changeBasis R (act ρ R (cocharacterPoint (cocharacter n) R t) v) i =
      (↑(t ^ exponentDot m (exponents i) n) : R) * coordinates changeBasis R v i
  trivial_iff : ∀ n, (cocharacter n).hom.hom = toUnit _ ≫ η[P.val.X] ↔ n = 0

/-- Coordinate weights as additive homomorphisms on the sum-zero lattice. -/
def DiagonalWeightCoordinates.weight {s : SpecialMatrixPoints P m} {ρ : Representation P.val I}
    (D : DiagonalWeightCoordinates s ρ) (i : I) : CocharacterLattice m →+ ℤ :=
  (exponentDot m (D.exponents i)).toAddMonoidHom

/-- No positive-rank split torus is included as a closed subgroup over the field. -/
def HasNoPositiveRankSplitTorus (G : GroupScheme k) : Prop :=
  ¬ ∃ (S : ClosedSubgroup G) (r : ℕ), 0 < r ∧
    Nonempty (S.group ≅ (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val)

/-- A rational representation of the matrix group admits coordinates adapted
to its diagonal torus in every matrix size. -/
def ExistsDiagonalWeightCoordinates : Prop :=
  ∀ (k : Type u) [Field k] (m : ℕ) (P : AffineAlgebraicGroup k)
    (s : SpecialMatrixPoints P m) (I : Type u) [Fintype I] [DecidableEq I]
    (ρ : Representation P.val I), Nonempty (DiagonalWeightCoordinates s ρ)

/-- The inverse rational orbit vectors in the closed homogeneous model have
polynomial limits in that model under cocharacters with nonnegative supported
weights. For an anisotropic stabilizer these cocharacters are zero. -/
def ClosedOrbitWeightCriterion : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (m : ℕ) (P : AffineAlgebraicGroup k) (s : SpecialMatrixPoints P m)
    (H : ClosedSubgroup P.val), IsSemisimple (closedSubgroupAlgebraicGroup H) →
    ∃ (Q : QuotientEmbedding.Presentation H)
      (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (ρ : Representation P.val I) (a : ModObj P.val.X (vectorSpace k I))
      (b : ModObj P.val.X Q.scheme) (j : Q.scheme ⟶ vectorSpace k I)
      (D : DiagonalWeightCoordinates s ρ)
      (v : GroupPoints P.val (groundField k) → I → k),
      IsAffine Q.scheme.left ∧ HomogeneousQuotient.IsQuotientTorsor Q ∧
      Smooth Q.projection.left ∧ IsClosedImmersion j.left ∧
      (∀ (R : TestAlgebra k) (g : GroupPoints P.val R) (w : I → R),
        lift g (vectorPoint R w) ≫ a.smul = vectorPoint R (act ρ R g w)) ∧
      b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul ∧
      Q.projection ≫ j = SmoothOrbit.orbitMap a (η[P.val.X] ≫ Q.projection ≫ j) ∧
      RepresentsSubgroup H (fun _ g => Stabilizes a.smul (η[P.val.X] ≫ Q.projection ≫ j) g) ∧
      (∀ g, vectorPoint (groundField k) (v g) = g⁻¹ ≫ Q.projection ≫ j) ∧
      ∀ (g : GroupPoints P.val (groundField k)) (n : CocharacterLattice m),
        (∀ i, coordinates D.changeBasis (groundField k) (v g) i ≠ 0 → 0 ≤ D.weight i n) →
        (∃ x₀, ActionHasLimit b (D.cocharacter n) (g⁻¹ ≫ Q.projection) x₀) ∧
        (HasNoPositiveRankSplitTorus H.group → n = 0)

end

end LinearAlgebraicGroups.Specs.FunctionFieldClosedOrbitWeights
