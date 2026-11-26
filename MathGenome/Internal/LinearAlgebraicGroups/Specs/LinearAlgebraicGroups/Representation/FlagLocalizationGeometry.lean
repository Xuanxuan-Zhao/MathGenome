import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.BruhatCells
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SchubertClosures
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLineBundle
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.Ideal.Cotangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FlagLocalizationGeometry

open AbstractPairing (Datum Root)
open BorelsAndChambers (subgroupRoots)
open BruhatOrbitParametrization (Cell FixedOver IsRepresentative OrderedParametrization)
open CharacterDescent (Character)
open DatumAndWeyl (Identification)
open FlagLineBundle (OppositeBorelPair)
open OrderedRootProducts (RootSubgroupFamily)
open QuotientEmbedding (Presentation)

noncomputable section

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}

/-- Equivariance for the two specified actions. -/
def IsEquivariantMap (a : ModObj T.X X) (b : ModObj T.X Y) (f : Y ⟶ X) : Prop :=
  b.smul ≫ f = (𝟙 T.X ⊗ₘ f) ≫ a.smul

abbrev pointAction (T : GroupScheme k) := ModObj.trivialAction T.X (𝟙_ (SchemeOver k))

abbrev torusAction {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val)
    (a : ModObj G.val.X X) : ModObj S.group.X X :=
  letI := a
  Mod.scalarRestriction S.inclusion.hom.hom X

abbrev PositiveRoot {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G) :=
  ↥(subgroupRoots P.torus P.positive)

/-- The character on functions is the inverse of the character on points. -/
def cotangentWeight {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (J : Identification D) (w : D.rootDatum.weylGroup) (α : PositiveRoot P) :
    Character P.torus.group :=
  (J.labelEquiv w).val α.val.val⁻¹

def characterFunction (χ : Character T) : Γ(T.X.left, ⊤) :=
  χ.hom.hom.left.appTop
    ((Scheme.ΓSpecIso _).inv
      (MonoidAlgebra.of k _ DiagonalizableGroups.integerGenerator))

/-- Homogeneity for the induced action on functions by inverse translation. -/
def HasFunctionWeight (a : ModObj T.X X) (f : Γ(X.left, ⊤)) (χ : Character T) : Prop :=
  a.smul.left.appTop f =
    (fst T.X X).left.appTop (characterFunction χ⁻¹) * (snd T.X X).left.appTop f

abbrev groundRingHom (X : SchemeOver k) : k →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom

def IsInvariantOpen (a : ModObj T.X X) (V : X.left.Opens) : Prop :=
  a.smul.left ⁻¹ᵁ V = (snd T.X X).left ⁻¹ᵁ V

def HasInvariantAffineCover (a : ModObj T.X X) : Prop :=
  ∀ x : X.left, ∃ V : X.left.Opens, x ∈ V ∧ IsAffineOpen V ∧ IsInvariantOpen a V

/-- The finiteness and separation needed for the coherent restriction sequence. -/
def RestrictionGeometry (a : ModObj T.X X) : Prop :=
  LocallyOfFiniteType X.hom ∧ CompactSpace X.left ∧ IsSeparated X.hom ∧
    HasInvariantAffineCover a

/-- Polynomial coordinates and the actual torus action on their generators. -/
structure PolynomialCoordinates (a : ModObj T.X X)
    (o : 𝟙_ (SchemeOver k) ⟶ X) {I : Type u} (ν : I → Character T) where
  affine : IsAffine X.left
  coordinates : letI : Algebra k Γ(X.left, ⊤) := (groundRingHom X).toAlgebra
    MvPolynomial I k ≃ₐ[k] Γ(X.left, ⊤)
  vanishes : ∀ i, o.left.appTop (coordinates (MvPolynomial.X i)) = 0
  weight : ∀ i, HasFunctionWeight a (coordinates (MvPolynomial.X i)) (ν i)

/-- The same coordinates give the cotangent basis at the marked fixed point. -/
structure FixedPointChart (a : ModObj T.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    {I : Type u} (ν : I → Character T) where
  scheme : SchemeOver k
  action : ModObj T.X scheme
  inclusion : scheme ⟶ X
  point : 𝟙_ (SchemeOver k) ⟶ scheme
  openImmersion : IsOpenImmersion inclusion.left
  equivariant : IsEquivariantMap a action inclusion
  over : point ≫ inclusion = x
  polynomial : PolynomialCoordinates action point ν
  cotangent : letI : Algebra k Γ(scheme.left, ⊤) := (groundRingHom scheme).toAlgebra
    ∃ b : Module.Basis I k (RingHom.ker point.left.appTop.hom).Cotangent,
      ∀ i, (RingHom.ker point.left.appTop.hom).toCotangent
        ⟨polynomial.coordinates (MvPolynomial.X i), polynomial.vanishes i⟩ = b i

/-- A reduced closed subscheme with the induced torus action. -/
structure InvariantClosed (a : ModObj T.X X) where
  scheme : SchemeOver k
  action : ModObj T.X scheme
  inclusion : scheme ⟶ X
  reduced : IsReduced scheme.left
  closedImmersion : IsClosedImmersion inclusion.left
  equivariant : IsEquivariantMap a action inclusion

/-- The open complement of the closed immersion, with the induced action. -/
structure InvariantComplement (a : ModObj T.X X) (S : InvariantClosed a) where
  scheme : SchemeOver k
  action : ModObj T.X scheme
  inclusion : scheme ⟶ X
  openImmersion : IsOpenImmersion inclusion.left
  equivariant : IsEquivariantMap a action inclusion
  range_eq : Set.range inclusion.left = (Set.range S.inclusion.left)ᶜ

/-- Assemble one scalar in each of the specified root coordinates in list order. -/
def orderedPoint {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {S : Set (Root T)}
    (coord : ∀ α : S, Σ L : RootGroups.AdditiveLine k, L.group ≅ (U α.val).val.group)
    (R : TestAlgebra k) (v : S → R)
    (l : List (Root T)) (h : ∀ α ∈ l, α ∈ S) :
      Points (OrderedRootProducts.product (fun α ↦ (U α).val.group.X) l) R := by
  induction l with
  | nil => exact toUnit _
  | cons α l ih =>
    let β : S := ⟨α, h α List.mem_cons_self⟩
    exact lift (RootGroups.rootPoint (coord β).2.hom R (v β))
      (ih (fun beta hbeta ↦ h beta (List.mem_cons_of_mem α hbeta)))

/-- Cell coordinates indexed by precisely the roots for the quotient Borel.
The scalar formula for each chosen root parametrization is on all test algebras. -/
structure OrderedCellCoordinates {G : AffineAlgebraicGroup k} {T B : ClosedSubgroup G.val}
    {Q : Presentation B} {a : ModObj G.val.X Q.scheme}
    {g : 𝟙_ (SchemeOver k) ⟶ G.val.X} {H : ClosedSubgroup G.val}
    (C : Cell (T := T) Q a g H) (U : RootSubgroupFamily T)
    (S : Set (Root T)) where
  order : List (Root T)
  enumerates : OrderedRootProducts.Enumerates order S
  rootIso : OrderedRootProducts.product (fun α ↦ (U α).val.group.X) order ≅ H.group.X
  rootIso_eq : rootIso.hom ≫ H.inclusion.hom.hom = OrderedRootProducts.rootProduct U order
  rootCoordinate : ∀ α : S, Σ L : RootGroups.AdditiveLine k, L.group ≅ (U α.val).val.group
  scalar : ∀ α : S, RootGroups.HasScalarAction T α.val.val
    ((rootCoordinate α).2.hom ≫ (U α.val).val.inclusion)
  action : ModObj T.group.X C.orbit
  equivariant : IsEquivariantMap (torusAction T a) action C.orbitInclusion
  polynomial : PolynomialCoordinates action (η[H.group.X] ≫ C.orbitIso.hom)
    (fun α : S ↦ α.val.val⁻¹)
  evaluates : ∀ (R : TestAlgebra k) (v : S → R) (α : S),
    (Scheme.ΓSpecIso _).hom
      ((orderedPoint rootCoordinate R v order (fun β hβ ↦ (enumerates.2 β).mp hβ) ≫
        rootIso.hom ≫ C.orbitIso.hom).left.appTop
        (polynomial.coordinates (MvPolynomial.X α))) = v α
  puncture : (⋃ α : S, (C.orbit.left.basicOpen (polynomial.coordinates (MvPolynomial.X α)) :
      Set C.orbit.left)) = (Set.range (η[H.group.X] ≫ C.orbitIso.hom).left)ᶜ

/-- The actual fixed points on the opposite-Borel flag and their invariant closed union. -/
def FixedPointLocus : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∃ hT : IsCommMonObj P.torus.group.X, letI := hT
    ∃ (D : Datum P.torus) (J : Identification D)
      (_ : Fintype D.rootDatum.weylGroup) (_ : Fintype (PositiveRoot P)),
      (∀ w, ∃ n, IsRepresentative J w n) ∧
      ∀ (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X)),
        (∀ w, IsRepresentative J w (n w)) →
        let x := fun w ↦ n w ≫ J.normalizer.inclusion.hom.hom ≫ Q.projection
        let t := torusAction P.torus a
        (∀ (K : Type u) [Field K] [Algebra k K]
            (y : Over.mk (fieldSpecMap k K) ⟶ Q.scheme),
          FixedOver (T := P.torus) a y ↔ ∃! w, y = toUnit _ ≫ x w) ∧
        ∃ (Z : InvariantClosed t) (_ : InvariantComplement t Z),
          ∃ e : (∐ fun _ : D.rootDatum.weylGroup ↦ 𝟙_ (SchemeOver k)) ≅ Z.scheme,
            ∀ w, Sigma.ι _ w ≫ e.hom ≫ Z.inclusion = x w

/-- A finite order in which each prefix of the cell partition is closed. -/
def ClosedPrefixes {W : Type u} (F : W → Set X.left) (e : Fin m ≃ W) : Prop :=
  ∀ j : ℕ, IsClosed (⋃ i : Fin m, ⋃ (_ : i.val < j), F (e i))

/-- A filtration of the complement, with successive strata identified by
their actual maps into the flag. -/
structure ComplementFiltration (a : ModObj T.X X) (S : InvariantClosed a)
    (V : InvariantComplement a S) {W : Type u}
    (cells : W → SchemeOver k) (acts : ∀ w, ModObj T.X (cells w))
    (inc : ∀ w, cells w ⟶ X) (origin : ∀ w, 𝟙_ (SchemeOver k) ⟶ cells w) where
  length : ℕ
  order : Fin length ≃ W
  stage : Fin (length + 1) → InvariantClosed V.action
  geometry : ∀ j, RestrictionGeometry (stage j).action
  first_empty : IsEmpty (stage 0).scheme.left
  last_full : IsIso (stage (Fin.last length)).inclusion
  step : ∀ i : Fin length, ∃ (Z : InvariantClosed (stage i.succ).action)
    (E : Z.scheme ≅ (stage i.castSucc).scheme),
    E.hom ≫ (stage i.castSucc).inclusion = Z.inclusion ≫ (stage i.succ).inclusion ∧
    IsEquivariantMap (stage i.castSucc).action Z.action E.hom ∧
    ∃ (O : InvariantComplement (stage i.succ).action Z)
      (j : O.scheme ⟶ cells (order i)),
      IsOpenImmersion j.left ∧ IsEquivariantMap (acts (order i)) O.action j ∧
      Set.range j.left = (Set.range (origin (order i)).left)ᶜ ∧
      j ≫ inc (order i) = O.inclusion ≫ (stage i.succ).inclusion ≫ V.inclusion ∧
      RestrictionGeometry O.action

/-- The geometry of the opposite-Borel flag used in fixed-point localization. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∃ hT : IsCommMonObj P.torus.group.X, letI := hT
    ∃ (D : Datum P.torus) (J : Identification D)
      (_ : Fintype D.rootDatum.weylGroup) (_ : Fintype (PositiveRoot P)),
      (∀ w, ∃ n, IsRepresentative J w n) ∧
      ∀ (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X)),
        (∀ w, IsRepresentative J w (n w)) →
        let g := fun w ↦ n w ≫ J.normalizer.inclusion.hom.hom
        let x := fun w ↦ g w ≫ Q.projection
        let t := torusAction P.torus a
        (∀ (K : Type u) [Field K] [Algebra k K]
            (y : Over.mk (fieldSpecMap k K) ⟶ Q.scheme),
          FixedOver (T := P.torus) a y ↔ ∃! w, y = toUnit _ ≫ x w) ∧
        (∀ w, Nonempty (FixedPointChart t (x w) (cotangentWeight J w))) ∧
        RestrictionGeometry t ∧
        ∃ (Z : InvariantClosed t) (V : InvariantComplement t Z),
          (∃ e : (∐ fun _ : D.rootDatum.weylGroup ↦ 𝟙_ (SchemeOver k)) ≅ Z.scheme,
            ∀ w, Sigma.ι _ w ≫ e.hom ≫ Z.inclusion = x w) ∧
          RestrictionGeometry Z.action ∧ RestrictionGeometry V.action ∧
          ∃ (U : RootSubgroupFamily P.torus)
            (H : D.rootDatum.weylGroup → ClosedSubgroup G.val)
            (C : ∀ w, Cell (T := P.torus) Q a (g w) (H w))
            (c : ∀ w, OrderedCellCoordinates (C w) U
              (subgroupRoots P.torus P.negative ∩
                (D.rootDatum.weylGroupToPerm w '' subgroupRoots P.torus P.positive))),
            Nonempty (ComplementFiltration t Z V (fun w ↦ (C w).orbit)
              (fun w ↦ (c w).action) (fun w ↦ (C w).orbitInclusion)
              (fun w ↦ η[(H w).group.X] ≫ (C w).orbitIso.hom))

end

end LinearAlgebraicGroups.Specs.FlagLocalizationGeometry
