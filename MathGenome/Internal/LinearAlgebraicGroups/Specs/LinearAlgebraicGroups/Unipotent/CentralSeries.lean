import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

noncomputable section

open StandardGroups

variable {k : Type u} [Field k]

/-- The distance from a strictly upper entry to the main diagonal. -/
def entryHeight {n : ℕ} (p : StrictUpper.{u} n) : ℕ :=
  p.1.2.down.val - p.1.1.down.val

abbrev HeightEntries (n d : ℕ) := {p : StrictUpper.{u} n // entryHeight p = d}

abbrev UnitriangularMatrix (n : ℕ) (R : Type u) [CommRing R] :=
  upperUnitriangular (Index.{u} n) R

/-- Membership in the height filtration, over an arbitrary test ring. -/
def InHeight {n : ℕ} {R : Type u} [CommRing R] (d : ℕ)
    (g : UnitriangularMatrix n R) : Prop :=
  ∀ p : StrictUpper.{u} n, entryHeight p < d → g.val.val p.1.1 p.1.2 = 0

/-- Strict upper entries are ordered first by height, then by row. -/
def coordinateRank {n : ℕ} (p : StrictUpper.{u} n) : ℕ :=
  entryHeight p * (n + 1) + p.1.1.down.val

/-- The coordinate flag successively sets the earlier coordinates to zero. -/
def InCoordinateFlag {n : ℕ} {R : Type u} [CommRing R] (s : ℕ)
    (g : UnitriangularMatrix n R) : Prop :=
  ∀ p : StrictUpper.{u} n, coordinateRank p < s → g.val.val p.1.1 p.1.2 = 0

/-- The additive coordinates at height `d`. -/
def heightCoordinates {n d : ℕ} {R : Type u} [CommRing R]
    (g : UnitriangularMatrix n R) (p : HeightEntries.{u} n d) : Multiplicative R :=
  Multiplicative.ofAdd (g.val.val p.1.1.1 p.1.1.2)

/-- The scheme-theoretic commutator inclusion, tested on every test algebra. -/
def HeightCommutators : Prop :=
  ∀ (k : Type u) [Field k] (n i j : ℕ) (R : TestAlgebra k)
    (x y : UnitriangularMatrix n R),
    InHeight i x → InHeight j y → InHeight (i + j) (x * y * x⁻¹ * y⁻¹)

/-- A quotient map with the indicated closed kernel, using the fppf right-coset sheaf. -/
def IsFppfGroupQuotient {G Q : AffineAlgebraicGroup k}
    (N : ClosedSubgroup G.val) (q : G.val ⟶ Q.val) : Prop :=
  IsSchemeKernel q N ∧ Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
    LocallyOfFinitePresentation q.hom.hom.left ∧
    ∃ e : rightQuotientSheaf N ≅ schemeFppfSheaf Q.val.X,
      rightQuotientProjection N ≫ e.hom = (fppfOver k).uliftYoneda.map q.hom.hom

/-- The height-`d` group is a closed subgroup of the unitriangular group,
with the specified image on points. -/
structure HeightSubgroup {n : ℕ} (U : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n) (d : ℕ) where
  group : AffineAlgebraicGroup k
  inclusion : group.val ⟶ U.val
  closed : IsClosedImmersion inclusion.hom.hom.left
  range_eq : ∀ (R : TestAlgebra k) (g : UnitriangularMatrix n R),
    InHeight d g ↔ ∃ x : Points group.val.X R,
      e.hom.app R (((groupPointsFunctor k).map inclusion).app R x) = g

/-- Successive height groups have the scheme quotient given by the coordinate map. -/
def HeightQuotients : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (U : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n),
    ∃ H : ∀ d, HeightSubgroup U e d,
      ∀ d : ℕ,
        ∃ (j : (H (d + 1)).group.val ⟶ (H d).group.val)
          (hj : IsClosedImmersion j.hom.hom.left)
          (V : AffineAlgebraicGroup k)
          (c : (groupPointsFunctor k).obj V.val ≅ additivePowerPoints k (HeightEntries n d))
          (q : (H d).group.val ⟶ V.val),
          j ≫ (H d).inclusion = (H (d + 1)).inclusion ∧
          IsFppfGroupQuotient ⟨_, j, hj⟩ q ∧
          ∀ (R : TestAlgebra k) (x : Points (H d).group.val.X R),
            c.hom.app R (((groupPointsFunctor k).map q).app R x) =
              heightCoordinates (e.hom.app R
                (((groupPointsFunctor k).map (H d).inclusion).app R x))

/-- A finite descending series of closed subgroup schemes, normal in their predecessors
when each step is supplied with its group quotient. Indexing is extended beyond the end. -/
structure ClosedSeries (G : AffineAlgebraicGroup k) (length : ℕ) where
  term : ℕ → AffineAlgebraicGroup k
  top : (term 0).val ≅ G.val
  bottom : (term length).val ≅ Grp.trivial (SchemeOver k)
  step (i : ℕ) : (term (i + 1)).val ⟶ (term i).val
  closed (i : ℕ) : IsClosedImmersion (step i).hom.hom.left

def ClosedSeries.inclusion {G : AffineAlgebraicGroup k} {length : ℕ}
    (S : ClosedSeries G length) (i : ℕ) : (S.term i).val ⟶ G.val :=
  match i with
  | 0 => S.top.hom
  | i + 1 => S.step i ≫ S.inclusion i

/-- Centrality is the factorization of the commutator through the next term,
tested on all commutative ground-field algebras. -/
def ClosedSeries.IsCentral {G : AffineAlgebraicGroup k} {length : ℕ}
    (S : ClosedSeries G length) : Prop :=
  ∀ i < length, ∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj G.val).obj R)
    (y : ((groupPointsFunctor k).obj (S.term i).val).obj R),
    let f := fun j => ((groupPointsFunctor k).map (S.inclusion j)).app R
    ∃ z : Points (S.term (i + 1)).val.X R,
      f (i + 1) z = x * f i y * x⁻¹ * (f i y)⁻¹

/-- Nilpotence of group schemes via a finite central series. -/
def IsSchemeNilpotent (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (length : ℕ) (S : ClosedSeries G length), S.IsCentral

/-- Split unipotence means a subnormal series with additive nontrivial quotients.
Trivial steps can be deleted. -/
def IsSplitUnipotent (G : AffineAlgebraicGroup k) : Prop :=
  IsUnipotent G ∧ ∃ (length : ℕ) (S : ClosedSeries G length), ∀ i < length,
    ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
      (Nonempty (Q.val ≅ Grp.trivial (SchemeOver k)) ∨
        Nonempty ((groupPointsFunctor k).obj Q.val ≅ additivePoints k))

def IsSplitUnipotentType := ∀ {k : Type u} [Field k], AffineAlgebraicGroup k → Prop

/-- Each represented fppf factor embeds as a closed subgroup scheme of the additive group. -/
def ClosedSeries.HasAdditiveSubgroupFactors {G : AffineAlgebraicGroup k} {length : ℕ}
    (S : ClosedSeries G length) : Prop :=
  ∀ i < length, ∃ (Q A : AffineAlgebraicGroup k)
    (q : (S.term i).val ⟶ Q.val) (j : Q.val ⟶ A.val),
    Nonempty ((groupPointsFunctor k).obj A.val ≅ additivePoints k) ∧
    IsClosedImmersion j.hom.hom.left ∧
    IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q

/-- For any given embedding, the central terms are the intersections with
the coordinate flag of the unitriangular group. -/
def EmbeddedCentralSeries : Prop :=
  ∀ {k : Type u} [Field k] (n : ℕ) (G U : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n)
    (f : G.val ⟶ U.val), IsClosedImmersion f.hom.hom.left →
    ∃ S : ClosedSeries G (n * (n + 1)), S.IsCentral ∧ S.HasAdditiveSubgroupFactors ∧
      ∀ (i : ℕ) (R : TestAlgebra k) (x : Points G.val.X R),
        InCoordinateFlag i (e.hom.app R (((groupPointsFunctor k).map f).app R x)) ↔
          ∃ y : Points (S.term i).val.X R,
            ((groupPointsFunctor k).map (S.inclusion i)).app R y = x

def UnipotentCentralSeries : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsUnipotent G →
    ∃ (length : ℕ) (S : ClosedSeries G length), S.IsCentral ∧ S.HasAdditiveSubgroupFactors

def UnipotentNilpotence : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsUnipotent G → IsSchemeNilpotent G

end

end LinearAlgebraicGroups.Specs.Unipotent
