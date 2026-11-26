import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RankOneFlag
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.RootGroups

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing
open GeometricBorelConjugacy (subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsSplitTorus)
open ProjectiveSpaces (LineRepresentation)
open RankOneFlag (Centralizer FlagIdentification HasCoordinates Index IsGeometricallyMaximal
  IsRankOneBorelPair IsSplitAdditive SameSubgroup lineBaseMap lineOver plane planeBasis projectiveLine)
open LinearAlgebraicGroups.CocharacterDynamics
  (LimitDecomposition cocharacterPoint oppositeCocharacter)

noncomputable section

variable {k : Type u} [Field k]

/-- The additive group with its standard affine coordinate. -/
structure AdditiveLine (k : Type u) [Field k] where
  operations : StandardGroups.HopfOperations k (Polynomial k)
  comultiplication : operations.delta Polynomial.X =
    Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X
  counit : operations.epsilon Polynomial.X = 0
  antipode : operations.inverse Polynomial.X = -Polynomial.X

abbrev AdditiveLine.group (A : AdditiveLine k) : GroupScheme k :=
  letI := A.operations.hopf
  (StandardGroups.spectrum k (Polynomial k)).val

/-- Evaluate a root parametrization at a scalar of a test algebra. -/
def rootPoint {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G)
    (R : TestAlgebra k) (a : R) : GroupPoints G R :=
  (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval a : Polynomial k →ₐ[k] R)).op ≫ x.hom.hom

/-- A smooth split additive subgroup normalized by the torus, whose Lie
algebra has the specified weight. The tangent map is the differential of the inclusion. -/
def IsRootSubgroup {G : GroupScheme k} (T U : ClosedSubgroup G)
    (α : Character T.group) : Prop :=
  Smooth U.group.X.hom ∧ IsSplitAdditive U.group ∧
    Normalizes U.inclusion T.inclusion.hom.hom ∧
    Set.range (mapPointKernel U.inclusion) ⊆ adjointWeightVectors T α

/-- The torus acts on the additive coordinate by the indicated character over
every commutative test algebra. -/
def HasScalarAction {G : GroupScheme k} (T : ClosedSubgroup G) (α : Character T.group)
    {A : AdditiveLine k} (x : A.group ⟶ G) : Prop :=
  ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (a : R),
    let g : GroupPoints G R := t ≫ T.inclusion.hom.hom
    g * rootPoint x R a * g⁻¹ = rootPoint x R (characterValue α R t * a)

/-- The two nonzero rationally proportional characters are expressed using
nonzero integer multiples in the character lattice. -/
def Proportional {T : GroupScheme k} (α β : Character T) : Prop :=
  ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ α ^ m = β ^ n

/-- The zero adjoint weight is the torus Lie algebra. Each nonzero weight has
a one-dimensional Lie algebra and a unique smooth additive root subgroup.
The only roots on its rational line are the two opposite roots. -/
def RootSubgroups : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    (Function.Injective (mapPointKernel T.inclusion) ∧
      Set.range (mapPointKernel T.inclusion) = adjointWeightVectors T 1) ∧
    ∀ α ∈ absoluteRoots T,
      (∀ s : IdentityLieStructure G.val,
        letI := s.lieRing
        letI := s.lieAlgebra
        Module.finrank k (adjointWeightSpace T α s) = 1) ∧
      (∀ β : Character T.group, β ∈ absoluteRoots T ∧ Proportional α β ↔
        β = α ∨ β = α⁻¹) ∧
      ∃ U : ClosedSubgroup G.val, IsRootSubgroup T U α ∧
        Function.Injective (mapPointKernel U.inclusion) ∧
        Set.range (mapPointKernel U.inclusion) = adjointWeightVectors T α ∧
        (∃ (A : AdditiveLine k) (x : A.group ≅ U.group), HasScalarAction T α (x.hom ≫ U.inclusion)) ∧
        ∀ V : ClosedSubgroup G.val, IsRootSubgroup T V α → SameSubgroup U V

/-- The action of the rank-one group on its flag quotient, expressed in
homogeneous coordinates using the group of automorphisms of the projective line. -/
structure ProjectiveAction {H : GroupScheme k} {X : SchemeOver k}
    (a : ModObj H.X X) (infinity zero : 𝟙_ (SchemeOver k) ⟶ X) where
  coordinates : LineRepresentation k (plane k)
  frame : X ≅ projectiveLine k
  infinityCoordinates : HasCoordinates coordinates (CommAlgCat.of k k)
    (toUnit _ ≫ infinity ≫ frame.hom) (fun i => if i.down = 0 then 1 else 0)
  zeroCoordinates : HasCoordinates coordinates (CommAlgCat.of k k)
    (toUnit _ ≫ zero ≫ frame.hom) (fun i => if i.down = 1 then 1 else 0)
  linearGroup : AffineAlgebraicGroup k
  matrices : (groupPointsFunctor k).obj linearGroup.val ≅
    StandardGroups.generalLinearPoints k Index.{u}
  projectiveGroup : AffineAlgebraicGroup k
  quotient : linearGroup.val ⟶ projectiveGroup.val
  action : ModObj projectiveGroup.val.X (projectiveLine k)
  automorphisms : ∀ R : TestAlgebra k, GroupPoints projectiveGroup.val R ≃* Aut (lineOver R)
  automorphismNaturality :
    ∀ (R S : TestAlgebra k) (b : R ⟶ S) (g : GroupPoints projectiveGroup.val R),
      (automorphisms S (mapPoints b g)).asIso.hom.left ≫ lineBaseMap b =
        lineBaseMap b ≫ (automorphisms R g).asIso.hom.left
  automorphismAction :
    ∀ (R : TestAlgebra k) (g : GroupPoints projectiveGroup.val R),
      (automorphisms R g).asIso.hom.left ≫ fst _ _ =
        lift (snd _ _ ≫ g) (fst _ _) ≫ action.smul
  matrixAction :
    ∀ (R : TestAlgebra k) (m : GroupPoints linearGroup.val R) (p : Points (projectiveLine k) R),
      ((coordinates.points _ (lift (m ≫ quotient.hom.hom) p ≫ action.smul)).line R (𝟙 _)).submodule =
        ((coordinates.points _ p).line R (𝟙 _)).submodule.map
          (PluckerEmbedding.matrixTransport (planeBasis k) R (matrices.hom.app R m)).toLinearMap
  hom : H ⟶ projectiveGroup.val
  transportsAction : (hom.hom.hom ⊗ₘ frame.hom) ≫ action.smul = a.smul ≫ frame.hom

/-- The root parametrization identifies the contracting subgroup
isomorphically with the projective image of elementary matrices. -/
structure TransvectionParametrization {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {infinity zero : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a infinity zero) (A : AdditiveLine k)
    (U : ClosedSubgroup H) (i j : Index.{u}) (hij : i ≠ j) where
  root : A.group ≅ U.group
  transvection : A.group ⟶ P.projectiveGroup.val
  closedImmersion : IsClosedImmersion transvection.hom.hom.left
  matchesTransvection : root.hom ≫ U.inclusion ≫ P.hom = transvection
  matrixPoints :
    ∀ (R : TestAlgebra k) (b : R),
      rootPoint transvection R b =
        (P.matrices.inv.app R (Matrix.GeneralLinearGroup.transvection i j hij b)) ≫
          P.quotient.hom.hom

/-- The rank-one word over a test algebra uses the same two additive coordinates. -/
def rankOneWord {A : AdditiveLine k} {G : GroupScheme k} (xpos xneg : A.group ⟶ G)
    (R : TestAlgebra k) (b : Rˣ) : GroupPoints G R :=
  rootPoint xpos R (↑b : R) * rootPoint xneg R (-(↑b⁻¹ : R)) * rootPoint xpos R (↑b : R)

/-- The coroot and the rational normalizer representative arise from the
rank-one word. Conjugation induces the reflection on the actual character
lattice, with the left Weyl action given by pullback by inverse conjugation. -/
structure CorootReflection {G : GroupScheme k} (T : ClosedSubgroup G)
    (α : Character T.group) {A : AdditiveLine k} (xpos xneg : A.group ⟶ G) where
  coroot : Cocharacter T.group
  representative : 𝟙_ (SchemeOver k) ⟶ G.X
  normalizes : Normalizes T.inclusion representative
  representative_word : toUnit _ ≫ representative = rankOneWord xpos xneg (CommAlgCat.of k k) 1
  coroot_word :
    ∀ (R : TestAlgebra k) (b : Rˣ),
      cocharacterPoint coroot R b ≫ T.inclusion.hom.hom =
        rankOneWord xpos xneg R b * (rankOneWord xpos xneg R 1)⁻¹
  conjugation : T.group ≅ T.group
  conjugates :
    (conjugation.hom ≫ T.inclusion).hom.hom =
      (toUnit T.group.X ≫ representative) * T.inclusion.hom.hom *
        (toUnit T.group.X ≫ representative)⁻¹
  reflection : ∀ χ : Character T.group, conjugation.inv ≫ χ =
    χ * α ^ (-pairing T.group χ coroot)
  root_pairing : pairing T.group α coroot = 2

/-- The rank-one centralizer supplies the two opposite root coordinates,
matched with the upper and lower elementary matrices through its action on
the marked flag quotient. These coordinates give the coroot and reflection. -/
def RankOneRootGroups : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ α ∈ absoluteRoots T,
      ∃ (C : Centralizer T α) (cochar : Cocharacter T.group),
        IsReductive (Unipotent.closedSubgroupAlgebraicGroup C.subgroup) ∧
        0 < pairing T.group α cochar ∧
        ∃ (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
          (E : LimitDecomposition (oppositeCocharacter (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))),
          IsRankOneBorelPair C cochar D E ∧
          ∃ (Q : QuotientEmbedding.Presentation D.parabolic)
            (F : FlagIdentification C.torus D.parabolic E.parabolic E.contracting Q)
            (P : ProjectiveAction F.action (η[C.subgroup.group.X] ≫ Q.projection)
              (F.normalizerPoint ≫ Q.projection))
            (A : AdditiveLine k)
            (p : TransvectionParametrization P A D.contracting ⟨0⟩ ⟨1⟩ (by decide))
            (n : TransvectionParametrization P A E.contracting ⟨1⟩ ⟨0⟩ (by decide)),
            IsRootSubgroup T (subgroupOfSubgroup C.subgroup D.contracting) α ∧
            IsRootSubgroup T (subgroupOfSubgroup C.subgroup E.contracting) α⁻¹ ∧
            let xpos := p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion
            let xneg := n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion
            HasScalarAction T α xpos ∧ HasScalarAction T α⁻¹ xneg ∧
              Nonempty (CorootReflection T α xpos xneg)

/-- The dimension counts the torus and one dimension for each absolute root,
including the case of an empty root set. -/
def RootDimension : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      (absoluteRoots T).Finite ∧
      topologicalKrullDim G.val.X.left =
        topologicalKrullDim T.group.X.left + (↑((absoluteRoots T).ncard : ℕ∞) : WithBot ℕ∞)

end

end LinearAlgebraicGroups.Specs.RootGroups
