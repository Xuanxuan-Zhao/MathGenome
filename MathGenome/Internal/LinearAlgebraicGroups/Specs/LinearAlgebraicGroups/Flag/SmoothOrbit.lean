import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FlagSchemes
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.RightQuotientSheaf
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.KrullDimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SmoothOrbit

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k} {X : SchemeOver k}

/-- The map taking a group element to its translate of the chosen rational point. -/
def orbitMap (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) : G.X ⟶ X :=
  lift (𝟙 G.X) (toUnit G.X ≫ x) ≫ a.smul

/-- The schematic closure, with its structure morphism over the ground field. -/
abbrev orbitClosure (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) : SchemeOver k :=
  Over.mk ((orbitMap a x).left.imageι ≫ X.hom)

/-- The inclusion of the schematic closure into the ambient scheme. -/
abbrev closureInclusion (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    orbitClosure a x ⟶ X :=
  Over.homMk (orbitMap a x).left.imageι

/-- A surjective flat presentation of an orbit induces the canonical isomorphism
from the fppf quotient by its scheme stabilizer. -/
def OrbitQuotient : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) (X O : SchemeOver k)
    (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (i : O ⟶ X) (q : G.X ⟶ O) (H : ClosedSubgroup G),
    Mono i → q ≫ i = orbitMap a x →
    Flat q.left → Surjective q.left → LocallyOfFinitePresentation q.left →
    RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g) →
    ∃ e : rightQuotientSheaf H ≅ schemeFppfSheaf O,
      rightQuotientProjection H ≫ e.hom = (fppfOver k).uliftYoneda.map q

/-- The representative is the open subscheme of the schematic image swept out by the
orbit map. Its fppf sheaf represents the right-coset quotient by the full stabilizer. -/
structure Presentation (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) where
  orbit : SchemeOver k
  openInClosure : orbit ⟶ orbitClosure a x
  isOpen : IsOpenImmersion openInClosure.left
  projection : G.X ⟶ orbit
  factors : projection.left ≫ openInClosure.left = (orbitMap a x).left.toImage
  flat : Flat projection.left
  surjective : Surjective projection.left
  finitePresentation : LocallyOfFinitePresentation projection.left
  stabilizer : ClosedSubgroup G
  representsStabilizer : RepresentsSubgroup stabilizer (fun _ g ↦ Stabilizes a.smul x g)
  quotientIso : rightQuotientSheaf stabilizer ≅ schemeFppfSheaf orbit
  quotientProjection : rightQuotientProjection stabilizer ≫ quotientIso.hom =
    (fppfOver k).uliftYoneda.map projection
  affineProjection : IsAffineHom projection.left
  action : ModObj G.X orbit
  actionInclusion : action.smul ≫ (openInClosure ≫ closureInclusion a x) =
    (𝟙 G.X ⊗ₘ (openInClosure ≫ closureInclusion a x)) ≫ a.smul
  actionProjection : μ[G.X] ≫ projection = (𝟙 G.X ⊗ₘ projection) ≫ action.smul

/-- The orbit theorem for an action on a separated finite-type scheme. -/
def SchemeOrbit : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (X : SchemeOver k)
    (a : ModObj G.1.X X) (x : 𝟙_ (SchemeOver k) ⟶ X),
    Smooth G.1.X.hom → IsSeparated X.hom → LocallyOfFiniteType X.hom →
      QuasiCompact X.hom → Nonempty (Presentation a x)

/-- The projective orbit at the point corresponding to a line in the constant bundle
over the ground field. This applies in particular to projectivized linear actions. -/
def ProjectiveLineOrbit : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (G : AffineAlgebraicGroup k)
    (ρ : ProjectiveSpaces.LineRepresentation k V)
    (a : ModObj G.1.X (ProjectiveSpaces.projectiveSpace k V))
    (L : ProjectiveSpaces.LineFamily k V (𝟙_ (SchemeOver k))),
    Smooth G.1.X.hom → Nonempty (Presentation a ((ρ.points _).symm L))

/-- A linear representation acts on the scheme of lines by transport on all test
algebras, and the stabilizer in the orbit presentation preserves the line. -/
def LinearProjectiveOrbit : Prop :=
  ∀ (k V I : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Fintype I] [DecidableEq I] (v : Module.Basis I k V) (G : AffineAlgebraicGroup k)
    (M : GroupScheme k) (E : (groupPointsFunctor k).obj M ≅ StandardGroups.generalLinearPoints k I)
    (f : G.1 ⟶ M) (ρ : ProjectiveSpaces.LineRepresentation k V)
    (L : ProjectiveSpaces.LineFamily k V (𝟙_ (SchemeOver k))),
    Smooth G.1.X.hom →
    ∃ (a : ModObj G.1.X (ProjectiveSpaces.projectiveSpace k V))
      (P : Presentation a ((ρ.points _).symm L)),
      (∀ (R : TestAlgebra k) (g : Points G.1.X R) (p : Points (ProjectiveSpaces.projectiveSpace k V) R),
        ((ρ.points _ (lift g p ≫ a.smul)).line R (𝟙 _)).submodule =
          ((ρ.points _ p).line R (𝟙 _)).submodule.map
            (PluckerEmbedding.matrixTransport v R (E.hom.app R (g ≫ f.hom.hom))).toLinearMap) ∧
      ∀ (R : TestAlgebra k) (g : Points G.1.X R),
        g ∈ SubgroupSections P.stabilizer ((testSpec k).obj (op R)) ↔
          (L.line R (toUnit _)).submodule.map
            (PluckerEmbedding.matrixTransport v R (E.hom.app R (g ≫ f.hom.hom))).toLinearMap =
          (L.line R (toUnit _)).submodule

/-- For an equivariant closed embedding into a projective representation, the same orbit
and orbit map factor through the embedded scheme, with the same scheme stabilizer. This
applies to the closed equivariant embedding of the full flag scheme. -/
def EquivariantProjectiveOrbit : Prop :=
  ∀ (k W : Type u) [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    (G : AffineAlgebraicGroup k) (Y : SchemeOver k)
    (a : ModObj G.1.X Y) (b : ModObj G.1.X (ProjectiveSpaces.projectiveSpace k W))
    (j : Y ⟶ ProjectiveSpaces.projectiveSpace k W) (x : 𝟙_ (SchemeOver k) ⟶ Y),
    Smooth G.1.X.hom → IsClosedImmersion j.left →
    a.smul ≫ j = (𝟙 G.1.X ⊗ₘ j) ≫ b.smul →
    ∃ (P : Presentation b (x ≫ j)) (i : P.orbit ⟶ Y),
      IsImmersion i.left ∧
      i.left ≫ j.left = P.openInClosure.left ≫ (orbitMap b (x ≫ j)).left.imageι ∧
      P.projection ≫ i = orbitMap a x ∧
      RepresentsSubgroup P.stabilizer (fun _ g ↦ Stabilizes a.smul x g)

/-- Restrict the flag and projective actions along a representation. The stabilizer
of each flag is the inverse image of a conjugate of the coordinate flag stabilizer.
For full flags its equations are the vanishing of the entries below the diagonal. -/
def FlagOrbit : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (v : Module.Basis (Fin n) k V) (m : ℕ) (ranks : Fin m → ℕ)
    (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis v) (ranks i))
    (D : FlagIncidence.Presentation ranks (FlagSchemes.liftedBasis v)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    (M : GroupScheme k)
    (E : (groupPointsFunctor k).obj M ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action ranks (FlagSchemes.liftedBasis v) (fun i ↦ (P i).charts) D.inclusion M E)
    (J : FlagSchemes.ProjectivePresentation (FlagSchemes.liftedBasis v) ranks P D M E A)
    (C : FlagSchemes.CoordinateStabilizer v ranks P D M E A)
    (G : AffineAlgebraicGroup k) (f : G.1 ⟶ M),
    Smooth G.1.X.hom →
    FlagIncidence.HasLocalTransitivity ranks (FlagSchemes.liftedBasis v)
      (fun i ↦ (P i).charts) D.inclusion M E A →
    let j := FlagSchemes.flagEmbedding (FlagSchemes.liftedBasis v) ranks P D J.segre
    let W := FlagSchemes.flagRepresentation (k := k) (V := V) ranks
    ∃ (a : ModObj G.1.X D.scheme) (b : ModObj G.1.X (ProjectiveSpaces.projectiveSpace k W)),
      (∀ (S : SchemeOver k) (g : S ⟶ G.1.X) (p : S ⟶ D.scheme),
        lift g p ≫ a.smul = prod.lift (g ≫ f.hom.hom) p ≫ A.onFlags) ∧
      b.smul = (f.hom.hom ⊗ₘ 𝟙 _) ≫ J.action.act ∧
      ∀ x : 𝟙_ (SchemeOver k) ⟶ D.scheme,
        ∃ (Q : Presentation b (x ≫ j)) (i : Q.orbit ⟶ D.scheme)
          (t : (𝟙_ (SchemeOver k)) ⟶ M.X),
          IsImmersion i.left ∧
          i ≫ j = Q.openInClosure ≫ closureInclusion b (x ≫ j) ∧
          Q.projection ≫ i = orbitMap a x ∧
          RepresentsSubgroup Q.stabilizer (fun _ g ↦ Stabilizes a.smul x g) ∧
          x = prod.lift t (FlagSchemes.toBasePoint _ ≫ C.point) ≫ A.onFlags ∧
          ∀ (R : TestAlgebra k) (g : Points G.1.X R),
            let tR : Points M.X R := toUnit _ ≫ t
            let B : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R :=
              E.hom.app R (tR⁻¹ * (g ≫ f.hom.hom) * tR)
            let fix := g ∈ SubgroupSections Q.stabilizer ((testSpec k).obj (op R))
            (fix ↔ ∀ (a : Fin m) (r s : ULift.{u} (Fin n)),
              s.down.val < ranks a → ranks a ≤ r.down.val → B.val r s = 0) ∧
            ((∀ a : Fin n, 0 < a.val → ∃ i : Fin m, ranks i = a.val) →
              (fix ↔ ∀ r s : ULift.{u} (Fin n), s.down < r.down → B.val r s = 0))

/-- The underlying set of the scheme orbit, used for geometric orbit dimensions. -/
def orbitSet (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) : Set X.left :=
  Set.range (orbitMap a x).left

/-- Over an algebraically closed field, every rational point whose orbit has least
dimension among the orbits in a stable closed subscheme has closed orbit. The condition
on the closed subscheme is expressed by stability under the given scheme action. -/
def MinimumOrbitClosed : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (X Y : SchemeOver k) (j : Y ⟶ X) (a : ModObj G.1.X X) (b : ModObj G.1.X Y),
    Smooth G.1.X.hom → IsSeparated X.hom → LocallyOfFiniteType X.hom →
    QuasiCompact X.hom → IsClosedImmersion j.left →
    b.smul ≫ j = lift (fst _ _) (snd _ _ ≫ j) ≫ a.smul →
    ∀ x : 𝟙_ (SchemeOver k) ⟶ Y,
      (∀ y : 𝟙_ (SchemeOver k) ⟶ Y,
        topologicalKrullDim (orbitSet a (x ≫ j)) ≤
          topologicalKrullDim (orbitSet a (y ≫ j))) →
      IsClosed (orbitSet a (x ≫ j))

/-- Over an algebraically closed field there is a closed scheme orbit in every
nonempty separated finite-type scheme with an action of the smooth group. -/
def ClosedOrbitExists : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (X : SchemeOver k) (a : ModObj G.1.X X),
    Smooth G.1.X.hom → IsSeparated X.hom → LocallyOfFiniteType X.hom →
    QuasiCompact X.hom → Nonempty X.left →
    ∃ (x : 𝟙_ (SchemeOver k) ⟶ X) (P : Presentation a x),
      IsClosedImmersion (P.openInClosure ≫ closureInclusion a x).left

/-- Over an algebraically closed field the rational points in the image of
the orbit map are precisely the translates of the chosen point. -/
def GeometricOrbitLifts : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k) (X : SchemeOver k)
    (a : ModObj G.1.X X) (x y : 𝟙_ (SchemeOver k) ⟶ X),
    y.left (IsLocalRing.closedPoint k) ∈ orbitSet a x ↔
      ∃ g : 𝟙_ (SchemeOver k) ⟶ G.1.X, g ≫ orbitMap a x = y

end

end LinearAlgebraicGroups.Specs.SmoothOrbit
