import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.RankOneFlag

open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open GeometricBorelConjugacy (IsBorel IsKBorel ConjugatesSubgroups)
open GeometricRadicals (IsReductive IsSplitTorus IsTorus IsMaximalTorus baseChangedSubgroup)
open ProjectiveSpaces (LineRepresentation projectiveSpace)
open SchemeDerivedGroup (IsSubgroupOf)
open SubtorusCentralizer (IsCentralizer)

noncomputable section

variable {k : Type u} [Field k]

/-- The given split torus is maximal after extension to an algebraic closure. -/
def IsGeometricallyMaximal {G : GroupScheme k} (T : ClosedSubgroup G) : Prop :=
  ∃ h : IsClosedImmersion
      ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
    IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)

/-- The largest closed torus in the scheme kernel of the character. -/
def IsKernelSubtorus {T : GroupScheme k} (α : Character T) (S : ClosedSubgroup T) : Prop :=
  IsTorus S.group ∧ S.inclusion ≫ α = 1 ∧
    ∀ D : ClosedSubgroup T, IsTorus D.group → D.inclusion ≫ α = 1 → IsSubgroupOf D S

/-- The centralizer and its specified maximal torus, with their inclusions in G. -/
structure Centralizer {G : GroupScheme k} (T : ClosedSubgroup G) (α : Character T.group) where
  kernelTorus : ClosedSubgroup T.group
  kernelTorus_largest : IsKernelSubtorus α kernelTorus
  subgroup : ClosedSubgroup G
  centralizes : IsCentralizer (GeometricBorelConjugacy.subgroupOfSubgroup T kernelTorus) subgroup
  torus : ClosedSubgroup subgroup.group
  torusIso : T.group ≅ torus.group
  torus_inclusion : torusIso.hom ≫ torus.inclusion ≫ subgroup.inclusion = T.inclusion
  torus_maximal : IsGeometricallyMaximal torus

/-- The rank-one centralizer is reductive, and the chosen sign of the cocharacter
is detected by the integral pairing. -/
def CentralizerAndPositiveCocharacter : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ α ∈ absoluteRoots T,
      ∃ C : Centralizer T α,
        IsReductive (Unipotent.closedSubgroupAlgebraicGroup C.subgroup) ∧
          ∃ cochar : Cocharacter T.group, 0 < pairing T.group α cochar

/-- Equality as subgroup schemes compares the inclusions in the ambient group. -/
def SameSubgroup {G : GroupScheme k} (A B : ClosedSubgroup G) : Prop :=
  IsSubgroupOf A B ∧ IsSubgroupOf B A

/-- After scalar extension, these are precisely the two distinct Borels through T. -/
def AreTwoBorels {H : GroupScheme k} (T Bpos Bneg : ClosedSubgroup H) : Prop :=
  IsKBorel Bpos ∧ IsKBorel Bneg ∧ ¬ SameSubgroup Bpos Bneg ∧
    IsSubgroupOf T Bpos ∧ IsSubgroupOf T Bneg ∧
    ∃ ht hp hn,
      let Tbar := baseChangedSubgroup (AlgebraicClosure k) T ht
      let BposBar := baseChangedSubgroup (AlgebraicClosure k) Bpos hp
      let BnegBar := baseChangedSubgroup (AlgebraicClosure k) Bneg hn
      ∀ B : ClosedSubgroup ((groupBaseChange k (AlgebraicClosure k)).obj H),
        IsBorel B → IsSubgroupOf Tbar B →
          SameSubgroup B BposBar ∨ SameSubgroup B BnegBar

/-- The additive group with its primitive polynomial coordinate. -/
def IsSplitAdditive (U : GroupScheme k) : Prop :=
  ∃ h : StandardGroups.HopfOperations k (Polynomial k),
    letI := h.hopf
    h.delta Polynomial.X = Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X ∧
      h.epsilon Polynomial.X = 0 ∧ h.inverse Polynomial.X = -Polynomial.X ∧
      Nonempty (U ≅ (StandardGroups.spectrum (k := k) (Polynomial k)).val)

abbrev Index := ULift.{u} (Fin 2)
abbrev plane (k : Type u) := Index.{u} → k
abbrev projectiveLine (k : Type u) [Field k] : SchemeOver k := projectiveSpace k (plane k)

def planeBasis (k : Type u) [Field k] : Module.Basis Index.{u} k (plane k) :=
  Pi.basisFun k Index

/-- Equality with a specified homogeneous line in the base-changed coordinate basis. -/
def HasCoordinates (ρ : LineRepresentation k (plane k)) (R : TestAlgebra k)
    (x : Points (projectiveLine k) R) (v : Index.{u} → R) : Prop :=
  ((ρ.points _ x).line R (𝟙 _)).submodule =
    Submodule.span R (Set.singleton (((planeBasis k).baseChange R).equivFun.symm v))

/-- The two limit decompositions have the same Levi torus. The multiplication
isomorphisms and the split kernel sequences are those in `LimitDecomposition`. -/
def IsRankOneBorelPair {G : GroupScheme k} {T : ClosedSubgroup G}
    {α : Character T.group} (C : Centralizer T α) (cochar : Cocharacter T.group)
    (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (E : LimitDecomposition (oppositeCocharacter (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))) : Prop :=
  SameSubgroup D.centralizer C.torus ∧ SameSubgroup E.centralizer C.torus ∧
    AreTwoBorels C.torus D.parabolic E.parabolic ∧
    Smooth D.contracting.group.X.hom ∧ Smooth E.contracting.group.X.hom ∧
    topologicalKrullDim D.contracting.group.X.left = 1 ∧
    topologicalKrullDim E.contracting.group.X.left = 1 ∧
    IsSplitAdditive D.contracting.group ∧ IsSplitAdditive E.contracting.group

/-- The marked projective-line identification of the right-coset quotient,
including its rational normalizer representative and its opposite open cell. -/
structure FlagIdentification {H : GroupScheme k} (T Bpos Bneg Uneg : ClosedSubgroup H)
    (Q : QuotientEmbedding.Presentation Bpos) where
  action : ModObj H.X Q.scheme
  quotientEquivariance :
    (𝟙 H.X ⊗ₘ Q.projection) ≫ action.smul = μ[H.X] ≫ Q.projection
  coordinates : LineRepresentation k (plane k)
  iso : Q.scheme ≅ projectiveLine k
  normalizerPoint : 𝟙_ (SchemeOver k) ⟶ H.X
  normalizes : Normalizes T.inclusion normalizerPoint
  conjugates : ConjugatesSubgroups normalizerPoint Bpos Bneg
  infinityCoordinates :
    HasCoordinates coordinates (CommAlgCat.of k k)
      (toUnit _ ≫ η[H.X] ≫ Q.projection ≫ iso.hom) (fun i => if i.down = 0 then 1 else 0)
  zeroCoordinates :
    HasCoordinates coordinates (CommAlgCat.of k k)
      (toUnit _ ≫ normalizerPoint ≫ Q.projection ≫ iso.hom) (fun i => if i.down = 1 then 1 else 0)
  distinct : η[H.X] ≫ Q.projection ≠ normalizerPoint ≫ Q.projection
  rationalFixedPoints :
    ∀ x : 𝟙_ (SchemeOver k) ⟶ Q.scheme,
      IsFixedBy ((T.inclusion.hom.hom ▷ Q.scheme) ≫ action.smul) x ↔
        x = η[H.X] ≫ Q.projection ∨ x = normalizerPoint ≫ Q.projection
  geometricFixedPoints :
    ∀ x : 𝟙_ (SchemeOver (AlgebraicClosure k)) ⟶ (baseChange k (AlgebraicClosure k)).obj Q.scheme,
      IsFixedBy (baseChangeAction (AlgebraicClosure k) ((T.inclusion.hom.hom ▷ Q.scheme) ≫ action.smul)) x ↔
        x = scalarExtendedRationalPoint (AlgebraicClosure k) (η[H.X] ≫ Q.projection) ∨
        x = scalarExtendedRationalPoint (AlgebraicClosure k) (normalizerPoint ≫ Q.projection)
  positiveStabilizer :
    RepresentsSubgroup Bpos (fun _ g ↦ Stabilizes action.smul (η[H.X] ≫ Q.projection) g)
  negativeStabilizer :
    RepresentsSubgroup Bneg
      (fun _ g ↦ Stabilizes action.smul (normalizerPoint ≫ Q.projection) g)
  openCell : IsOpenImmersion (Uneg.inclusion.hom.hom ≫ Q.projection).left
  openCellRange :
    Set.range (Uneg.inclusion.hom.hom ≫ Q.projection).left =
      (Set.range (normalizerPoint ≫ Q.projection).left)ᶜ

/-- For any cocharacter with positive pairing, its two dynamic Borels give the
rank-one flag variety over the ground field. -/
def RankOneFlagGeometry : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ α ∈ absoluteRoots T, ∀ (C : Centralizer T α) (cochar : Cocharacter T.group),
      0 < pairing T.group α cochar →
      ∃ (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
        (E : LimitDecomposition (oppositeCocharacter (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))),
        IsRankOneBorelPair C cochar D E ∧
        Nonempty (QuotientEmbedding.Presentation D.parabolic) ∧
        ∀ Q : QuotientEmbedding.Presentation D.parabolic,
          Smooth Q.scheme.hom ∧ IsProper Q.scheme.hom ∧
          topologicalKrullDim Q.scheme.left = 1 ∧
          Nonempty (FlagIdentification C.torus D.parabolic E.parabolic E.contracting Q)

/-- The projective line after scalar extension to an arbitrary test algebra,
viewed in the slice over that affine test scheme. -/
abbrev lineOver (R : TestAlgebra k) : Over ((testSpec k).obj (op R)) :=
  Over.mk (snd (projectiveLine k) ((testSpec k).obj (op R)))

def lineBaseMap {R S : TestAlgebra k} (a : R ⟶ S) :
    (lineOver S).left ⟶ (lineOver R).left :=
  lift (fst _ _) (snd _ _ ≫ (testSpec k).map a.op)

open StandardGroups in
/-- PGL₂ is the right fppf quotient of GL₂ by the scalar torus.
Its projective action identifies its points with all automorphisms of the
scalar-extended line, compatibly with extension along maps of test algebras. -/
def ProjectiveLineAutomorphisms : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (hm : HopfOperations k (LaurentPolynomial k))
      (hl : HopfOperations k (GLCoordinates k Index.{u})),
      letI := hm.hopf
      letI := hl.hopf
      let M := spectrum (k := k) (LaurentPolynomial k)
      let L := spectrum (k := k) (GLCoordinates k Index.{u})
      ∃ (em : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
        (el : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k Index.{u})
        (s : M.val ⟶ L.val) (hs : IsClosedImmersion s.hom.hom.left),
        (∀ (R : TestAlgebra k) (a : Points M.val.X R),
          el.hom.app R (a ≫ s.hom.hom) = Matrix.GeneralLinearGroup.scalar Index (em.hom.app R a)) ∧
        IsNormalSubgroup s ∧
        let H : ClosedSubgroup L.val := ⟨M.val, s, hs⟩
        ∃ (P : QuotientEmbedding.Presentation H) (PGL : AffineAlgebraicGroup k)
          (q : L.val ⟶ PGL.val) (i : P.scheme ≅ PGL.val.X)
          (action : ModObj PGL.val.X (projectiveLine k))
          (ρ : LineRepresentation k (plane k))
          (e : ∀ R : TestAlgebra k, ((groupPointsFunctor k).obj PGL.val).obj R ≃* Aut (lineOver R)),
          HomogeneousQuotient.IsQuotientTorsor P ∧ IsSchemeKernel q H ∧
          P.projection ≫ i.hom = q.hom.hom ∧
          (∀ (R S : TestAlgebra k) (a : R ⟶ S) (g : Points PGL.val.X R),
            (e S (mapPoints a g)).asIso.hom.left ≫ lineBaseMap a =
              lineBaseMap a ≫ (e R g).asIso.hom.left) ∧
          (∀ (R : TestAlgebra k) (g : Points PGL.val.X R),
            (e R g).asIso.hom.left ≫ fst _ _ = lift (snd _ _ ≫ g) (fst _ _) ≫ action.smul) ∧
          (∀ (R : TestAlgebra k) (g : Points L.val.X R) (x : Points (projectiveLine k) R),
            ((ρ.points _ (lift (g ≫ q.hom.hom) x ≫ action.smul)).line R (𝟙 _)).submodule =
              ((ρ.points _ x).line R (𝟙 _)).submodule.map
                (PluckerEmbedding.matrixTransport (planeBasis k) R (el.hom.app R g)).toLinearMap) ∧
          (∀ (R : TestAlgebra k) (g : Points PGL.val.X R),
            ∃ (S : TestAlgebra k) (a : R ⟶ S) (m : Points L.val.X S),
              Fppf.IsFppf ((testSpec k).map a.op).left ∧ m ≫ q.hom.hom = mapPoints a g) ∧
          (∀ (R : TestAlgebra k) (x : Points (projectiveLine k) R),
            ∃ (S : TestAlgebra k) (a : R ⟶ S) (v : Index.{u} → S),
              Fppf.IsFppf ((testSpec k).map a.op).left ∧
                Ideal.span (Set.range v) = ⊤ ∧ HasCoordinates ρ S (mapPoints a x) v)

end

end LinearAlgebraicGroups.Specs.RankOneFlag
