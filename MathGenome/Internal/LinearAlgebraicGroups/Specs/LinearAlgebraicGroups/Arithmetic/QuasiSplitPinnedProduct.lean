import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.OpenCell
import Mathlib.GroupTheory.GroupAction.Quotient

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory
universe u v

namespace LinearAlgebraicGroups.Specs.QuasiSplitPinnedProduct

open AbsoluteDynkinTypes (SupportedOn IsAbsolutelyAlmostSimple)
open Pinning (AttachedDatum BasedRootDatum BasedIso PinnedGroup)
open GeometricRadicals (IsReductive IsSemisimple IsSplitTorus IsTorus IsUnipotentRadical)
open GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open OpenCell (AreOpposite)
open SchemeDerivedGroup (IsSubgroupOf)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open RankOneFlag (IsGeometricallyMaximal)
open Unipotent (closedSubgroupAlgebraicGroup)
open Pinning (PinnedIso SimpleRoot SplitBorelPair transportCharacter)
open CharacterDescent (Character)
open RootGroups (AdditiveLine)


noncomputable section

/-- The adjacency relation of a Cartan diagram, using both Cartan entries. -/
def Adjacent {I : Type*} (A : Matrix I I ℤ) (i j : I) : Prop :=
  i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0)

/-- The connected components of the simple vertices. -/
def componentSetoid {I : Type*} (A : Matrix I I ℤ) : Setoid I where
  r := Relation.EqvGen (Adjacent A)
  iseqv := ⟨Relation.EqvGen.refl, fun h => .symm _ _ h, fun h h' => .trans _ _ _ h h'⟩

abbrev Components {I : Type*} (A : Matrix I I ℤ) := Quotient (componentSetoid A)

abbrev component {I : Type*} {A : Matrix I I ℤ} (i : I) : Components A :=
  Quotient.mk (componentSetoid A) i

/-- Vertex permutations preserving the Cartan matrix act on its connected components. -/
def ComponentAction : Prop :=
  ∀ {Γ : Type u} {I : Type v} [Group Γ] [MulAction Γ I] (A : Matrix I I ℤ),
    (∀ σ : Γ, ∀ i j, A (σ • i) (σ • j) = A i j) →
    ∃ ρ : MulAction Γ (Components A),
      letI := ρ
      (∀ σ : Γ, ∀ i : I, σ • component (A := A) i = component (σ • i)) ∧
      (∀ i j : I, component (A := A) i ≠ component j → A i j = 0 ∧ A j i = 0)

/-- A connected block of the full lattices and the actual paired roots. -/
structure ComponentDatum {I X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) (B : P.Base)
    (c : Components (RootData.integralCartan P B)) where
  datum : BasedRootDatum.{u}
  fullCorootLattice : Submodule.span ℤ (Set.range datum.datum.coroot) = ⊤
  vertices : datum.base.support ≃ {i : B.support // component i = c}
  preservesCartan : ∀ i j : datum.base.support,
    RootData.integralCartan datum.datum datum.base i j =
      RootData.integralCartan P B (vertices i).val (vertices j).val

/-- Coordinates of the full simply connected datum, with each actual matched
root and coroot pair on a unique connected block. -/
def RootComponentCoordinates : Prop :=
  ∀ {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) [P.IsReduced] (B : P.Base),
    Submodule.span ℤ (Set.range P.coroot) = ⊤ →
    ∃ (x : X ≃ₗ[ℤ] (B.support → ℤ)) (y : Y ≃ₗ[ℤ] (B.support → ℤ)),
      (∀ i j : B.support, x (P.root i.val) j = RootData.integralCartan P B j i) ∧
      (∀ i : B.support, y (P.coroot i.val) = (by classical exact Pi.single i 1)) ∧
      (∀ a b, P.toLinearMap a b = ∑ j, y b j * x a j) ∧
      ∀ i : I, ∃! c : Components (RootData.integralCartan P B),
        SupportedOn {j | component j = c} (x (P.root i), y (P.coroot i))

/-- The connected blocks of a simply connected based datum, with all roots,
coroots and base vertices matched to the corresponding original ones. -/
def RootComponentData : Prop :=
  ∀ {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) [P.IsReduced] (B : P.Base),
    Submodule.span ℤ (Set.range P.coroot) = ⊤ →
    ∃ (x : X ≃ₗ[ℤ] (B.support → ℤ)) (y : Y ≃ₗ[ℤ] (B.support → ℤ)),
      (∀ a b, P.toLinearMap a b = ∑ j, y b j * x a j) ∧
      (∀ i : B.support, y (P.coroot i.val) = (by classical exact Pi.single i 1)) ∧
      (∀ i : I, ∃! c : Components (RootData.integralCartan P B),
        SupportedOn {j | component j = c} (x (P.root i), y (P.coroot i))) ∧
      ∀ c : Components (RootData.integralCartan P B),
        let S := {j : B.support | component (A := RootData.integralCartan P B) j = c}
        letI : DecidablePred (· ∈ S) := Classical.decPred _
        ∃ (D : ComponentDatum P B c)
          (a : D.datum.I ≃ {i : I // SupportedOn S (x (P.root i), y (P.coroot i))})
          (v : D.datum.X ≃ₗ[ℤ] (S → ℤ)) (w : D.datum.Y ≃ₗ[ℤ] (S → ℤ)),
          (∀ h k, D.datum.datum.toLinearMap h k = ∑ j, w k j * v h j) ∧
          (∀ i, v (D.datum.datum.root i) = fun j => x (P.root (a i).val) j.val) ∧
          (∀ i, w (D.datum.datum.coroot i) = fun j => y (P.coroot (a i).val) j.val) ∧
          ∀ i : D.datum.base.support, (a i.val).val = (D.vertices i).val.val




/-- The two Borels, common torus, and their unipotent radicals as subgroup
schemes, with the radicals viewed inside their Borels. -/
structure BorelPair {F : Type u} [Field F] (G : AffineAlgebraicGroup F) where
  positive : ClosedSubgroup G.val
  negative : ClosedSubgroup G.val
  torus : ClosedSubgroup G.val
  positiveRadical : ClosedSubgroup positive.group
  negativeRadical : ClosedSubgroup negative.group
  positiveBorel : IsKBorel positive
  negativeBorel : IsKBorel negative
  isTorus : IsTorus torus.group
  maximal : IsGeometricallyMaximal torus
  torusInPositive : IsSubgroupOf torus positive
  torusInNegative : IsSubgroupOf torus negative
  opposite : AreOpposite torus positive negative
  positiveUnipotentRadical : IsUnipotentRadical (closedSubgroupAlgebraicGroup positive)
    positiveRadical
  negativeUnipotentRadical : IsUnipotentRadical (closedSubgroupAlgebraicGroup negative)
    negativeRadical

/-- The subgroup inclusions to be carried along in an isomorphism of pairs. -/
inductive Marking
  | positive | negative | torus | positiveRadical | negativeRadical

variable {F : Type u} [Field F]

def BorelPair.subgroup {G : AffineAlgebraicGroup F} (M : BorelPair G) :
    Marking → ClosedSubgroup G.val
  | .positive => M.positive
  | .negative => M.negative
  | .torus => M.torus
  | .positiveRadical => subgroupOfSubgroup M.positive M.positiveRadical
  | .negativeRadical => subgroupOfSubgroup M.negative M.negativeRadical


/-- Scheme products are specified by their projections, with the universal
property also checked on each of the five subgroup schemes. -/
structure MarkedProduct {I : Type u}
    {G : AffineAlgebraicGroup F} {H : I → AffineAlgebraicGroup F}
    (M : BorelPair G) (N : ∀ i, BorelPair (H i)) where
  projection : ∀ i, G.val ⟶ (H i).val
  subgroupProjection : ∀ m i, (M.subgroup m).group ⟶ ((N i).subgroup m).group
  commutes : ∀ m i, (M.subgroup m).inclusion ≫ projection i =
    subgroupProjection m i ≫ ((N i).subgroup m).inclusion
  product : IsLimit (Fan.mk G.val projection)
  subgroupProduct : ∀ m, IsLimit (Fan.mk (M.subgroup m).group (subgroupProjection m))

/-- Simple-vertex permutations induced by the based automorphisms. -/
def simplePermutation (D : BasedRootDatum.{u}) (a : Aut D) : Equiv.Perm D.base.support := by
  let e := a.asIso.hom.val.indexEquiv
  have h : e '' (D.base.support : Set D.I) = D.base.support := a.asIso.hom.property
  exact e.subtypeEquiv fun i => by
    change i ∈ (D.base.support : Set D.I) ↔ e i ∈ (D.base.support : Set D.I)
    constructor
    · intro hi
      have he : e i ∈ e '' (D.base.support : Set D.I) := ⟨i, hi, rfl⟩
      exact h ▸ he
    · intro hi
      have he : e i ∈ e '' (D.base.support : Set D.I) := h.symm ▸ hi
      obtain ⟨j, hj, hji⟩ := he
      exact e.injective hji ▸ hj


/-- The connected-component relation agrees with the relation defined by
the edge multiplicities of the actual integral Dynkin diagram. -/
def DiagramAdjacency : Prop :=
  ∀ {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) (B : P.Base) (i j : B.support),
    Adjacent (RootData.integralCartan P B) i j ↔
      (AbsoluteDynkinTypes.integralDiagram (RootData.integralCartan P B)).edges i j ≠ 0

/-- Any based action induces the actual action on connected components. -/
def BasedComponentAction : Prop :=
  ∀ {Γ : Type u} [Group Γ] (D : BasedRootDatum.{u}) (ω : Γ →* Aut D),
    let A := RootData.integralCartan D.datum D.base
    ∃ ρ : MulAction Γ (Components A), letI := ρ
    ∀ σ : Γ, ∀ i : D.base.support,
      σ • component (A := A) i = component (A := A) (simplePermutation D (ω σ) i)

/-- A block indexed by a connected component has a nonempty connected
diagram, with the edges prescribed by the original Cartan pairing. -/
def ComponentDiagramConnected : Prop :=
  ∀ (D : BasedRootDatum.{u}) {c : Components (RootData.integralCartan D.datum D.base)}
    (B : ComponentDatum D.datum D.base c),
    (AbsoluteDynkinTypes.integralDiagram
      (RootData.integralCartan B.datum.datum B.datum.base)).IsConnected

/-- Each based automorphism identifies the full root datum of a block with
that of the permuted block. On a fixed block the lifts form an action of
its stabilizer and agree with the transports. -/
def BasedComponentTransport : Prop :=
  ∀ {Γ : Type u} [Group Γ] (D : BasedRootDatum.{u}) (ω : Γ →* Aut D),
    let A := RootData.integralCartan D.datum D.base
    ∀ [MulAction Γ (Components A)],
    (∀ σ : Γ, ∀ i : D.base.support,
      σ • component (A := A) i = component (A := A) (simplePermutation D (ω σ) i)) →
    ∀ B : ∀ c : Components A, ComponentDatum D.datum D.base c,
    ∃ e : ∀ (σ : Γ) c, BasedIso (B c).datum (B (σ • c)).datum,
      (∀ (σ : Γ) c (i : (B c).datum.base.support) (j : (B (σ • c)).datum.base.support),
        (e σ c).val.indexEquiv i.val = j.val ↔
          simplePermutation D (ω σ) ((B c).vertices i).val = ((B (σ • c)).vertices j).val) ∧
      ∀ c, ∃ s : MulAction.stabilizer Γ c →* Aut (B c).datum,
        ∀ (σ : MulAction.stabilizer Γ c),
          (s σ).asIso.hom = e σ.val c ≫
            eqToHom (congrArg (fun d => (B d).datum) (MulAction.mem_stabilizer_iff.mp σ.property))

/-- Each actual connected block admits a split pinned simply connected
semisimple realization, with its full based datum identified. -/
def PinnedComponentModels : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} (P : PinnedGroup A)
    (D : AttachedDatum P.pair),
    corootLattice D = ⊤ →
    let B := D.toBased
    ∃ (block : ∀ c, ComponentDatum B.datum B.base c)
      (Q : Components (RootData.integralCartan B.datum B.base) → PinnedGroup A)
      (T : ∀ c, AttachedDatum (Q c).pair),
      ∀ c, IsSemisimple (Q c).pair.G ∧ GeometricallySimplyConnected (Q c).pair.G ∧
        Nonempty (BasedIso (block c).datum (T c).toBased)

/-- With a full coroot lattice, an empty diagram gives the empty marked
product, including the trivial radicals and torus. -/
def EmptyMarkedSplitProduct : Prop :=
  ∀ {F : Type u} [Field F] (P : Pinning.SplitBorelPair F) (D : AttachedDatum P)
    (M : BorelPair P.G),
    corootLattice D = ⊤ → IsEmpty D.toBased.base.support →
    ∀ {I : Type u} [IsEmpty I] {H : I → AffineAlgebraicGroup F}
      (N : ∀ i, BorelPair (H i)), Nonempty (MarkedProduct M N)

/-- The components and vertices refer to the Cartan matrix of the specified datum. -/
abbrev DatumComponents (D : BasedRootDatum.{u}) :=
  Components (RootData.integralCartan D.datum D.base)

abbrev BlockVertices (D : BasedRootDatum.{u}) (c : DatumComponents D) :=
  {j : D.base.support // component j = c}

/-- Coordinate identifications of the full lattices and of every paired root
of a block, in the basis of simple coroots and its dual basis. -/
structure BlockCoordinates (D : BasedRootDatum.{u}) (x : D.X ≃ₗ[ℤ] (D.base.support → ℤ))
    (y : D.Y ≃ₗ[ℤ] (D.base.support → ℤ)) (c : DatumComponents D) where
  block : ComponentDatum D.datum D.base c
  roots : block.datum.I ≃ {i : D.I //
    SupportedOn {j | component (A := RootData.integralCartan D.datum D.base) j = c}
      (x (D.datum.root i), y (D.datum.coroot i))}
  weights : block.datum.X ≃ₗ[ℤ] (BlockVertices D c → ℤ)
  coweights : block.datum.Y ≃ₗ[ℤ] (BlockVertices D c → ℤ)
  pairing :
    letI : DecidablePred (fun j : D.base.support => component j = c) := Classical.decPred _
    ∀ a b, block.datum.datum.toLinearMap a b = ∑ j, coweights b j * weights a j
  root_eq : ∀ i, weights (block.datum.datum.root i) = fun j => x (D.datum.root (roots i).val) j.val
  coroot_eq : ∀ i, coweights (block.datum.datum.coroot i) =
    fun j => y (D.datum.coroot (roots i).val) j.val
  base_eq : ∀ i : block.datum.base.support, (roots i.val).val = (block.vertices i).val.val

structure ComponentCoordinates (D : BasedRootDatum.{u}) where
  weights : D.X ≃ₗ[ℤ] (D.base.support → ℤ)
  coweights : D.Y ≃ₗ[ℤ] (D.base.support → ℤ)
  pairing : ∀ a b, D.datum.toLinearMap a b = ∑ j, coweights b j * weights a j
  simpleCoroot : ∀ j : D.base.support,
    coweights (D.datum.coroot j.val) = (by classical exact Pi.single j 1)
  supported : ∀ i : D.I, ∃! c : DatumComponents D,
    SupportedOn {j | component j = c} (weights (D.datum.root i), coweights (D.datum.coroot i))
  blocks : ∀ c, BlockCoordinates D weights coweights c

/-- Marked split factors with their attached data identified with the
actual paired lattice blocks of the original group. -/
structure PinnedFactors {A : AdditiveLine F} {P : PinnedGroup A} (D : AttachedDatum P.pair) where
  coordinates : ComponentCoordinates D.toBased
  factor : DatumComponents D.toBased → PinnedGroup A
  attached : ∀ c, AttachedDatum (factor c).pair
  based : ∀ c, BasedIso (coordinates.blocks c).block.datum (attached c).toBased
  semisimple : ∀ c, IsSemisimple (factor c).pair.G
  simplyConnected : ∀ c, GeometricallySimplyConnected (factor c).pair.G

/-- The lattice formula is zero extension from the component. -/
def IsBlockTorusProjection {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (W : PinnedFactors D) (c : DatumComponents D.toBased)
    (p : P.pair.T.group ⟶ (W.factor c).pair.T.group) : Prop :=
  letI := Classical.decEq (DatumComponents D.toBased)
  ∀ (χ : Character (W.factor c).pair.T.group) (i : D.toBased.base.support),
    W.coordinates.weights (Additive.ofMul (p ≫ χ)) i =
      if h : component i = c then
        (W.coordinates.blocks c).weights
          ((W.based c).val.weightEquiv.symm (Additive.ofMul χ)) ⟨i, h⟩
      else 0

/-- Coordinate maps here are maps into the whole group scheme. -/
def pinnedCoordinate {A : AdditiveLine F} (P : PinnedGroup A) (i : SimpleRoot P.pair) :
    A.group ⟶ P.pair.G.val :=
  (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion

def labeledSimpleRoot {A : AdditiveLine F} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (i : D.toBased.base.support) : SimpleRoot P.pair :=
  ⟨i.val, (D.simple_iff _).mp i.property⟩

/-- Identify a simple vertex in a block with the corresponding pinned root in the factor. -/
def factorSimpleRoot {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    (W : PinnedFactors D) (c : DatumComponents D.toBased) (i : BlockVertices D.toBased c) :
    SimpleRoot (W.factor c).pair := by
  let b := (W.coordinates.blocks c).block
  let j := b.vertices.symm i
  let α := (W.based c).val.indexEquiv j.val
  exact ⟨α, ((W.attached c).simple_iff α).mp (by
    change α ∈ ((W.attached c).toBased.base.support : Set _)
    rw [← (W.based c).property]
    exact ⟨j.val, j.property, rfl⟩)⟩

/-- The based automorphism and its lift have the same action on actual characters. -/
def LiftsBasedAutomorphism {A : AdditiveLine F} {P : PinnedGroup A} (D : AttachedDatum P.pair)
    (g : Aut D.toBased) (f : PinnedIso P P) : Prop :=
  ∀ χ : Character P.pair.T.group,
    g.asIso.hom.val.weightEquiv (Additive.ofMul χ) = Additive.ofMul (transportCharacter f.torus χ)

/-- The product projections on the group, the marked subgroups, and the
pinned coordinates, including transport under based automorphisms. -/
def ProjectionData {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    (W : PinnedFactors D) (M : BorelPair P.pair.G)
    (N : ∀ c, BorelPair (W.factor c).pair.G) : Prop :=
  ∃ (p : MarkedProduct M N)
    (t : ∀ c, P.pair.T.group ⟶ (W.factor c).pair.T.group),
    (∀ c, P.pair.T.inclusion ≫ p.projection c = t c ≫ (W.factor c).pair.T.inclusion) ∧
    (∀ c, IsBlockTorusProjection W c (t c)) ∧
    (∀ (i : D.toBased.base.support) c (h : component i = c),
      pinnedCoordinate P (labeledSimpleRoot D i) ≫ p.projection c =
        pinnedCoordinate (W.factor c) (factorSimpleRoot W c ⟨i, h⟩)) ∧
    (∀ (i : D.toBased.base.support) c, component i ≠ c →
      pinnedCoordinate P (labeledSimpleRoot D i) ≫ p.projection c = 0) ∧
    ∀ (g : Aut D.toBased) (f : PinnedIso P P), LiftsBasedAutomorphism D g f →
      ∃ (σ : Equiv.Perm (DatumComponents D.toBased))
        (l : ∀ c, PinnedIso (W.factor c) (W.factor (σ c))),
        (∀ i : D.toBased.base.support, σ (component i) = component (simplePermutation D.toBased g i)) ∧
        (∀ c, f.group.hom ≫ p.projection (σ c) = p.projection c ≫ (l c).group.hom) ∧
        ∀ c, f.torus.hom ≫ t (σ c) = t c ≫ (l c).torus.hom

/-- The actual product of the connected pinned factors, with their
geometric simplicity and their marked projections. -/
def ProductConclusion {A : AdditiveLine F} (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (M : BorelPair P.pair.G) : Prop :=
  ∃ (W : PinnedFactors D) (N : ∀ c, BorelPair (W.factor c).pair.G),
    (∀ c, IsAbsolutelyAlmostSimple (W.factor c).pair.G ∧
      (N c).positive = (W.factor c).pair.B ∧ (N c).torus = (W.factor c).pair.T) ∧
    ProjectionData W M N

/-- The marked product and equivariant projections for the split pinned
group, with the factors identified by the actual paired lattice blocks. -/
def MarkedSplitPinnedProduct : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (M : BorelPair P.pair.G),
    M.positive = P.pair.B → M.torus = P.pair.T → corootLattice D = ⊤ →
    ∃ (W : PinnedFactors D) (N : ∀ c, BorelPair (W.factor c).pair.G),
      (∀ c, (N c).positive = (W.factor c).pair.B ∧ (N c).torus = (W.factor c).pair.T) ∧
      ProjectionData W M N

/-- The split product for the specified opposite Borel pair. -/
def Statement : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (M : BorelPair P.pair.G),
    M.positive = P.pair.B → M.torus = P.pair.T →
    IsSemisimple P.pair.G → corootLattice D = ⊤ → ProductConclusion P D M

/-- The same conclusion when the diagram has no vertices. -/
def EmptyDiagramProduct : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (M : BorelPair P.pair.G),
    corootLattice D = ⊤ → IsEmpty D.toBased.base.support → ProductConclusion P D M

/-- The based blocks have split pinned semisimple models with full coroot lattice. -/
def PinnedFactorsExist : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} {P : PinnedGroup A}
    (D : AttachedDatum P.pair), corootLattice D = ⊤ → Nonempty (PinnedFactors D)

/-- The factors for the connected components are absolutely almost simple. -/
def PinnedFactorsAbsolutelyAlmostSimple : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (W : PinnedFactors D) (c : DatumComponents D.toBased),
    IsAbsolutelyAlmostSimple (W.factor c).pair.G

/-- Opposite Borels and their radicals can be chosen over the split field. -/
def SplitMarkingsExist : Prop :=
  ∀ {F : Type u} [Field F] (P : Pinning.SplitBorelPair F),
    ∃ M : BorelPair P.G, M.positive = P.B ∧ M.torus = P.T

/-- The split torus of the original group is the product of the block tori,
whose character pullbacks are the respective zero extensions. -/
def SplitTorusComponentProduct : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (W : PinnedFactors D),
    ∃ p : ∀ c, P.pair.T.group ⟶ (W.factor c).pair.T.group,
      (∀ c, IsBlockTorusProjection W c (p c)) ∧ Nonempty (IsLimit (Fan.mk _ p))

/-- Block permutations lift between the fixed pinned models. -/
def PinnedFactorTransport : Prop :=
  ∀ {F Γ : Type u} [Field F] [Group Γ] {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (W : PinnedFactors D) (ω : Γ →* Aut D.toBased),
    ∀ [MulAction Γ (DatumComponents D.toBased)],
    (∀ σ : Γ, ∀ i : D.toBased.base.support, σ • component (A := RootData.integralCartan D.toBased.datum D.toBased.base) i =
      component (simplePermutation D.toBased (ω σ) i)) →
    ∃ e : ∀ σ c, BasedIso (W.attached c).toBased (W.attached (σ • c)).toBased,
      ∃ g : ∀ σ c, PinnedIso (W.factor c) (W.factor (σ • c)),
        (∀ σ c χ, (e σ c).val.weightEquiv (Additive.ofMul χ) =
          Additive.ofMul (transportCharacter (g σ c).torus χ)) ∧
        ∀ (σ : Γ) c (i : BlockVertices D.toBased c) (j : BlockVertices D.toBased (σ • c)),
          simplePermutation D.toBased (ω σ) i.val = j.val →
          (g σ c).torus.inv ≫ (factorSimpleRoot W c i).val.val =
            (factorSimpleRoot W (σ • c) j).val.val

/-- The pinning and character pullbacks determine the permutation action
on all the block torus projections. The matching pinned coordinates are
identified by the same transport. -/
def TorusProjectionEquivariance : Prop :=
  ∀ {F Γ : Type u} [Field F] [Group Γ] {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (W : PinnedFactors D) (ω : Γ →* Aut D.toBased),
    ∀ [MulAction Γ (DatumComponents D.toBased)],
    (∀ σ : Γ, ∀ i : D.toBased.base.support,
      σ • component (A := RootData.integralCartan D.toBased.datum D.toBased.base) i =
        component (simplePermutation D.toBased (ω σ) i)) →
    ∀ (p : ∀ c, P.pair.T.group ⟶ (W.factor c).pair.T.group),
    (∀ c, IsBlockTorusProjection W c (p c)) →
    ∃ l : ∀ (σ : Γ) c, PinnedIso (W.factor c) (W.factor (σ • c)),
      (∀ (σ : Γ) c (i : BlockVertices D.toBased c) (j : BlockVertices D.toBased (σ • c)),
        simplePermutation D.toBased (ω σ) i.val = j.val →
        pinnedCoordinate (W.factor c) (factorSimpleRoot W c i) ≫ (l σ c).group.hom =
          pinnedCoordinate (W.factor (σ • c)) (factorSimpleRoot W (σ • c) j)) ∧
      ∀ (σ : Γ) (f : PinnedIso P P), LiftsBasedAutomorphism D (ω σ) f →
        ∀ c, f.torus.hom ≫ p (σ • c) = p c ≫ (l σ c).torus.hom

/-- Once the marked product is constructed, its ambient projections
intertwine the induced pinned isomorphisms on components. -/
def ProductProjectionEquivariance : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (W : PinnedFactors D),
    ∀ (p : ∀ c, P.pair.G.val ⟶ (W.factor c).pair.G.val)
      (b : ∀ c, P.pair.B.group ⟶ (W.factor c).pair.B.group)
      (t : ∀ c, P.pair.T.group ⟶ (W.factor c).pair.T.group),
      IsLimit (Fan.mk _ p) → IsLimit (Fan.mk _ b) →
      (∀ c, P.pair.B.inclusion ≫ p c = b c ≫ (W.factor c).pair.B.inclusion) →
      (∀ c, P.pair.T.inclusion ≫ p c = t c ≫ (W.factor c).pair.T.inclusion) →
      (∀ c, IsBlockTorusProjection W c (t c)) →
      (∀ (i : D.toBased.base.support) c (h : component i = c),
        pinnedCoordinate P (labeledSimpleRoot D i) ≫ p c =
          pinnedCoordinate (W.factor c) (factorSimpleRoot W c ⟨i, h⟩)) →
      (∀ (i : D.toBased.base.support) c, component i ≠ c →
        pinnedCoordinate P (labeledSimpleRoot D i) ≫ p c = 0) →
      ∀ (g : Aut D.toBased) (f : PinnedIso P P), LiftsBasedAutomorphism D g f →
        ∃ (σ : Equiv.Perm (DatumComponents D.toBased))
          (l : ∀ c, PinnedIso (W.factor c) (W.factor (σ c))),
          (∀ i : D.toBased.base.support, σ (component i) = component (simplePermutation D.toBased g i)) ∧
          (∀ c, f.group.hom ≫ p (σ c) = p c ≫ (l c).group.hom) ∧
          ∀ c, f.torus.hom ≫ t (σ c) = t c ≫ (l c).torus.hom

/-- The tensor product represents the binary product of split reductive groups
and of their actual marked maximal tori, over the original field. -/
def BinarySplitReductiveProduct : Prop :=
  ∀ {F : Type u} [Field F] (P Q : SplitBorelPair F),
    ∃ (G : AffineAlgebraicGroup F) (g : P.G.val ⊗ Q.G.val ≅ G.val)
      (T : ClosedSubgroup G.val) (t : P.T.group ⊗ Q.T.group ≅ T.group),
      (t.hom ≫ T.inclusion = (P.T.inclusion ⊗ₘ Q.T.inclusion) ≫ g.hom) ∧
      IsReductive G ∧ IsSplitTorus T.group ∧ IsGeometricallyMaximal T

/-- A saturated sublattice of the full cocharacter lattice that is stable
under the simple coreflections of a connected diagram is zero or everything. -/
def ConnectedCoreflectionInvariantLattice : Prop :=
  ∀ (D : BasedRootDatum.{u}),
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    (AbsoluteDynkinTypes.integralDiagram (RootData.integralCartan D.datum D.base)).IsConnected →
    ∀ M : Submodule ℤ D.Y,
      (∀ n : ℤ, ∀ y, n ≠ 0 → n • y ∈ M → y ∈ M) →
      (∀ i : D.base.support, ∀ y ∈ M, D.datum.coreflection i.val y ∈ M) →
      M = ⊥ ∨ M = ⊤

/-- Smooth connected normal subgroups inherit semisimplicity over an
algebraically closed field. -/
def NormalSubgroupSemisimplicity : Prop :=
  ∀ {F : Type u} [Field F] [IsAlgClosed F] (G : AffineAlgebraicGroup F),
    IsSemisimple G → ∀ N : ClosedSubgroup G.val, GeometricRadicals.IsSmoothConnectedNormal N →
      IsSemisimple (closedSubgroupAlgebraicGroup N)

/-- A closed torus lies in a maximal torus over an algebraically closed field. -/
def TorusInMaximalTorus : Prop :=
  ∀ {F : Type u} [Field F] [IsAlgClosed F] (G : AffineAlgebraicGroup F)
    (T : ClosedSubgroup G.val), IsTorus T.group →
    ∃ S : ClosedSubgroup G.val, GeometricRadicals.IsMaximalTorus S ∧ IsSubgroupOf T S

end

end LinearAlgebraicGroups.Specs.QuasiSplitPinnedProduct
