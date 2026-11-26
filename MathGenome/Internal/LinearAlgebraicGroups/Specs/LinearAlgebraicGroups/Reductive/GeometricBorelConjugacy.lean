import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SmoothOrbit
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.GeometricBorelConjugacy

open GeometricRadicals (IsReductive IsTorus baseChangedSubgroup)
open SchemeDerivedGroup (IsSolvable IsSubgroupOf)

noncomputable section

variable {k : Type u} [Field k]

/-- A smooth connected solvable closed subgroup, without a normality condition. -/
def IsSmoothConnectedSolvable {G : GroupScheme k} (H : ClosedSubgroup G) : Prop :=
  Smooth H.group.X.hom ∧ ConnectedSpace H.group.X.left ∧ IsSolvable H.group

/-- Over an algebraically closed field a Borel is a maximal smooth connected
solvable closed subgroup. Mutual inclusion expresses equality as closed subgroups. -/
def IsBorel {G : GroupScheme k} (B : ClosedSubgroup G) : Prop :=
  IsSmoothConnectedSolvable B ∧
    ∀ H : ClosedSubgroup G, IsSmoothConnectedSolvable H →
      IsSubgroupOf B H → IsSubgroupOf H B

/-- A Borel defined over the ground field is a closed subgroup whose base change
to the algebraic closure is a Borel. -/
def IsKBorel {G : GroupScheme k} (B : ClosedSubgroup G) : Prop :=
  ∃ h : IsClosedImmersion ((groupBaseChange k (AlgebraicClosure k)).map B.inclusion).hom.hom.left,
    IsBorel (baseChangedSubgroup (AlgebraicClosure k) B h)

/-- A connected reductive group is quasi-split if it has a Borel over its ground field. -/
def IsQuasiSplit (G : AffineAlgebraicGroup k) : Prop :=
  IsReductive G ∧ ∃ B : ClosedSubgroup G.val, IsKBorel B

/-- Conjugation by a rational point identifies the closed subgroup schemes,
via an isomorphism intertwining their inclusions into the ambient group. -/
def ConjugatesSubgroups {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (H N : ClosedSubgroup G) : Prop :=
  ∃ e : H.group ≅ N.group,
    let c : H.group.X ⟶ G.X := toUnit H.group.X ≫ g
    (e.hom ≫ N.inclusion).hom.hom = c * H.inclusion.hom.hom * c⁻¹

/-- A reduced closed subgroup with support equal to the identity component
has the reduced subscheme structure on that component. -/
def IsReducedIdentityComponent {H : GroupScheme k} (C : ClosedSubgroup H) : Prop :=
  IsReduced C.group.X.left ∧
    Set.range C.inclusion.hom.hom.left =
      connectedComponent (η[H.X].left (IsLocalRing.closedPoint k))

/-- The composite of two closed subgroup inclusions. -/
def subgroupOfSubgroup {G : GroupScheme k} (H : ClosedSubgroup G)
    (C : ClosedSubgroup H.group) : ClosedSubgroup G := by
  letI := C.isClosedImmersion
  letI := H.isClosedImmersion
  exact ⟨C.group, C.inclusion ≫ H.inclusion, IsClosedImmersion.comp _ _⟩

/-- A full flag records the intermediate ranks, with endpoints implicit. -/
def fullFlagRanks (n : ℕ) : Fin (n - 1) → ℕ := fun i ↦ i.val + 1

variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V] {n : ℕ}

/-- The full flag scheme with the action restricted along a faithful matrix
representation, using the incidence and projective presentations. -/
structure FullFlagAction (G : AffineAlgebraicGroup k) (v : Module.Basis (Fin n) k V) where
  planes : ∀ i : Fin (n - 1),
    PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis v) (fullFlagRanks n i)
  flags : FlagIncidence.Presentation (fullFlagRanks n) (FlagSchemes.liftedBasis v)
    (fun i ↦ (planes i).charts) (fun i ↦ (planes i).families)
  linearGroup : GroupScheme k
  matrixPoints : (groupPointsFunctor k).obj linearGroup ≅
    StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))
  flagAction : FlagIncidence.Action (fullFlagRanks n) (FlagSchemes.liftedBasis v)
    (fun i ↦ (planes i).charts) flags.inclusion linearGroup matrixPoints
  projective : FlagSchemes.ProjectivePresentation (FlagSchemes.liftedBasis v)
    (fullFlagRanks n) planes flags linearGroup matrixPoints flagAction
  representation : G.val ⟶ linearGroup
  faithful : IsClosedImmersion representation.hom.hom.left
  action : ModObj G.val.X flags.scheme
  action_eq : ∀ (S : SchemeOver k) (g : S ⟶ G.val.X) (p : S ⟶ flags.scheme),
    lift g p ≫ action.smul = Limits.prod.lift (g ≫ representation.hom.hom) p ≫ flagAction.onFlags

/-- A smooth connected affine algebraic group over an algebraically closed
field has a Borel subgroup. -/
def BorelExists : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
      ∃ B : ClosedSubgroup G.val, IsBorel B

/-- Every closed torus in such a group is contained in a Borel. -/
def TorusContainedInBorel : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T : ClosedSubgroup G.val, IsTorus T.group →
      ∃ B : ClosedSubgroup G.val, IsBorel B ∧ IsSubgroupOf T B

/-- Any two Borels are conjugate as subgroup schemes by a point over the
algebraically closed ground field. -/
def BorelsConjugate : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ B₁ B₂ : ClosedSubgroup G.val, IsBorel B₁ → IsBorel B₂ →
      ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, ConjugatesSubgroups g B₁ B₂

/-- A faithful realization on a full flag scheme admits a closed orbit. The
orbit presentation includes the full stabilizer, which may be nonreduced. -/
def ClosedFlagOrbitExists : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∃ (n : ℕ) (v : Module.Basis (Fin n) k (Fin n → k)) (F : FullFlagAction G v)
      (x : 𝟙_ (SchemeOver k) ⟶ F.flags.scheme) (O : SmoothOrbit.Presentation F.action x),
      IsClosedImmersion (O.openInClosure ≫ SmoothOrbit.closureInclusion F.action x).left

/-- At a flag of a closed orbit, the reduced identity component of its scheme
stabilizer, included in the original group, is a Borel. -/
def ClosedFlagStabilizerIsBorel : Prop :=
  ∀ {k V : Type u} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ {n : ℕ} {v : Module.Basis (Fin n) k V} (F : FullFlagAction G v)
      (x : 𝟙_ (SchemeOver k) ⟶ F.flags.scheme) (O : SmoothOrbit.Presentation F.action x),
      IsClosedImmersion (O.openInClosure ≫ SmoothOrbit.closureInclusion F.action x).left →
      ∃ C : ClosedSubgroup O.stabilizer.group,
        IsReducedIdentityComponent C ∧ IsBorel (subgroupOfSubgroup O.stabilizer C)

end

end LinearAlgebraicGroups.Specs.GeometricBorelConjugacy
