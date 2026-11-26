import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.EuclideanComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DynkinExhaustion
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalCoordinateRoots

noncomputable section

open LieAlgebrasAndRepresentations

namespace LinearAlgebraicGroups.Specs.AbsoluteDynkinTypes

/-- Relabelling vertices while preserving all entries, with rows indexed by coroots. -/
def PreservesCartan {ι κ : Type*} (A : Matrix ι ι ℤ) (B : Matrix κ κ ℤ)
    (e : ι ≃ κ) : Prop :=
  ∀ i j, A i j = B (e i) (e j)

/-- The oriented diagram of the integral Cartan matrix. -/
def integralDiagram {ι : Type*} (A : Matrix ι ι ℤ) : DynkinDiagram ι := by
  classical
  exact ⟨fun i j => if i = j then 0 else (A i j * A j i).toNat,
    fun i j => i ≠ j ∧ A j i < A i j⟩

/-- Finite type on an integral Cartan matrix, with a specified relabelling. -/
def HasDynkinType {ι : Type*} (A : Matrix ι ι ℤ) (t : FiniteDynkinType) : Prop :=
  ∃ e, PreservesCartan A t.cartan e

/-- Classification of the integral Cartan matrix for a connected based root datum. -/
def ConnectedCartanClassification.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ X] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base),
    (integralDiagram (RootData.integralCartan P B)).IsConnected →
      ∃ t, HasDynkinType (RootData.integralCartan P B) t

/-- The two names of the rank-two double-edge type have isomorphic full matrices. -/
def RankTwoCoincidence : Prop :=
  HasDynkinType (FiniteDynkinType.B 2 (by decide)).cartan (.C 2 (by decide))

/-- Oriented Dynkin type determines the label up to the rank-two coincidence. -/
def CartanTypeUniqueness.{u} : Prop :=
  ∀ {ι : Type u} (A : Matrix ι ι ℤ) (t s : FiniteDynkinType),
    HasDynkinType A t → HasDynkinType A s →
    t = s ∨
    (t = .B 2 (by decide) ∧ s = .C 2 (by decide)) ∨
    (t = .C 2 (by decide) ∧ s = .B 2 (by decide))

/-- In the chosen numbering of D₄, vertex 1 is the trivalent vertex.
The outer vertices are 0, 2 and 3. -/
def D4Outer := {i : Fin 4 // i ≠ 1}

abbrev D4Cartan := (FiniteDynkinType.D 4 (by decide)).cartan

def D4Permutations : Prop :=
  ∀ σ : Equiv.Perm (Fin 4), PreservesCartan D4Cartan D4Cartan σ ↔ σ 1 = 1

/-- A subgroup of the permutations preserving the D₄ Cartan matrix fixes an
outer vertex exactly when it fails to be transitive on the three outer vertices. -/
def D4ActionDichotomy : Prop :=
  ∀ H : Subgroup (Equiv.Perm (Fin 4)),
    (∀ σ ∈ H, PreservesCartan D4Cartan D4Cartan σ) →
    ((∃ i : D4Outer, ∀ σ ∈ H, σ i.val = i.val) ↔
      ¬ ∀ i j : D4Outer, ∃ σ ∈ H, σ i.val = j.val)

/-- A diagram action on D₄ fixes an outer vertex exactly when its image
has order at most two. -/
def D4ActionOrder : Prop :=
  ∀ H : Subgroup (Equiv.Perm (Fin 4)),
    (∀ σ ∈ H, PreservesCartan D4Cartan D4Cartan σ) →
    ((∃ i : D4Outer, ∀ σ ∈ H, σ i.val = i.val) ↔ Nat.card H ≤ 2)

/-- Any fixed outer vertex can be given the number of the vector vertex
by a Cartan-preserving relabelling. -/
def D4VectorRelabelling : Prop :=
  ∀ i : D4Outer, ∃ e : Equiv.Perm (Fin 4),
    PreservesCartan D4Cartan D4Cartan e ∧ e i.val = 0

/-- The vector and the odd and even half-spin highest weights give the
fundamental characters at vertices 0, 2 and 3 of the coordinate model. -/
def D4OuterWeights : Prop :=
  let a := ClassicalCoordinates.simpleD 4
  let ε := @ClassicalCoordinates.epsilon 4
  let v := ε 0
  let sOdd := (1 / 2 : ℝ) • (ε 0 + ε 1 + ε 2 - ε 3)
  let sEven := (1 / 2 : ℝ) • (ε 0 + ε 1 + ε 2 + ε 3)
  (∀ i j, rootCartan (a j) (a i) = (D4Cartan i j : ℝ)) ∧
  (∀ i, rootCartan v (a i) = (Pi.single 0 1 : Fin 4 → ℝ) i) ∧
  (∀ i, rootCartan sOdd (a i) = (Pi.single 2 1 : Fin 4 → ℝ) i) ∧
  (∀ i, rootCartan sEven (a i) = (Pi.single 3 1 : Fin 4 → ℝ) i)


open Set Module

/-- The simple character in the basis dual to the simple coroots. -/
def simpleCharacter {ι : Type*} (A : Matrix ι ι ℤ) (i : ι) : ι → ℤ :=
  fun j => A j i

/-- The reflection and coreflection on the two dual coordinate lattices. -/
def reflectCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (i : ι) (p : (ι → ℤ) × (ι → ℤ)) : (ι → ℤ) × (ι → ℤ) :=
  (p.1 - p.1 i • simpleCharacter A i, p.2 - (∑ j, p.2 j * A j i) • Pi.single i 1)

/-- The root and coroot pairs recovered from a Cartan matrix in the dual
coordinate lattices. The sign and reflection operations are simultaneous. -/
inductive CartanRoots {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) :
    (ι → ℤ) × (ι → ℤ) → Prop
  | simple (i : ι) : CartanRoots A (simpleCharacter A i, Pi.single i 1)
  | neg {p} : CartanRoots A p → CartanRoots A (-p.1, -p.2)
  | reflect (i : ι) {p} : CartanRoots A p → CartanRoots A (reflectCoordinates A i p)

/-- Realize the simply connected datum by a Cartan matrix on the chosen
vertices. The pairings and complete matched root and coroot set are retained. -/
def CartanCoordinates.{u,v,w,z} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} {κ : Type z}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Fintype κ] [DecidableEq κ]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base),
    Submodule.span ℤ (range P.coroot) = ⊤ →
    ∀ (A : Matrix κ κ ℤ) (e : B.support ≃ κ),
    PreservesCartan (RootData.integralCartan P B) A e →
    ∃ (c : Basis κ ℤ Y) (x : X ≃ₗ[ℤ] (κ → ℤ)),
      (∀ i, c i = P.coroot (e.symm i).val) ∧
      (∀ a b, P.toLinearMap a b = ∑ i, c.equivFun b i * x a i) ∧
      (∀ i, x (P.root (e.symm i).val) = simpleCharacter A i) ∧
      range (fun i => (x (P.root i), c.equivFun (P.coroot i))) = {p | CartanRoots A p}

/-- For data with full coroot lattices, Cartan relabellings are precisely
the restrictions of based datum isomorphisms to the simple vertices. -/
def CartanDeterminesBasedDatum.{u} : Prop :=
  ∀ (P Q : Pinning.BasedRootDatum.{u}),
    Submodule.span ℤ (range P.datum.coroot) = ⊤ →
    Submodule.span ℤ (range Q.datum.coroot) = ⊤ →
    ∀ e : P.base.support ≃ Q.base.support,
      PreservesCartan (RootData.integralCartan P.datum P.base)
        (RootData.integralCartan Q.datum Q.base) e ↔
      ∃! f : Pinning.BasedIso P Q, ∀ i : P.base.support, f.val.indexEquiv i.val = (e i).val

/-- A root and its matching coroot vanish off the same collection of vertices. -/
def SupportedOn {ι : Type*} (S : Set ι) (p : (ι → ℤ) × (ι → ℤ)) : Prop :=
  ∀ i ∉ S, p.1 i = 0 ∧ p.2 i = 0

/-- Orthogonal blocks of the Cartan matrix contain every matched pair. A simple
reflection in the opposite block fixes the pair. -/
def CartanRootBlocks.{u} : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (S : Set ι),
    (∀ i ∈ S, ∀ j ∉ S, A i j = 0 ∧ A j i = 0) →
    (∀ p, CartanRoots A p → SupportedOn S p ∨ SupportedOn Sᶜ p) ∧
    ∀ p, SupportedOn S p → ∀ i,
      (i ∉ S → reflectCoordinates A i p = p) ∧
      (i ∈ S → SupportedOn S (reflectCoordinates A i p))

/-- A disconnected nonempty diagram gives two nonempty mutually orthogonal
blocks of the actual simple roots and coroots. -/
def DisconnectedPartition.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ X] [Module.Finite ℤ Y]
    (P : RootDatum (ι := ι) X Y) [P.IsReduced] (B : P.Base),
    Nonempty B.support → ¬ (integralDiagram (RootData.integralCartan P B)).IsConnected →
      ∃ S : Set B.support, S.Nonempty ∧ Sᶜ.Nonempty ∧
        ∀ i ∈ S, ∀ j ∉ S,
          RootData.integralCartan P B i j = 0 ∧ RootData.integralCartan P B j i = 0

/-- The real and integral Weyl actions induce the same permutations on the
actual root indices. -/
def WeylActionComparison.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y),
    (∀ g : RootData.realWeylGroup P, ∃ w : P.weylGroup,
      ∀ i, g.val (RootData.realRoot P i) = RootData.realRoot P (P.weylGroupToPerm w i)) ∧
    (∀ w : P.weylGroup, ∃ g : RootData.realWeylGroup P,
      ∀ i, g.val (RootData.realRoot P i) = RootData.realRoot P (P.weylGroupToPerm w i))

/-- The Weyl groups are isomorphic compatibly with their actions on the
roots and with each generating reflection when the coroots span the lattice. -/
def WeylGroupComparison.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] (P : RootDatum (ι := ι) X Y),
    Submodule.span ℤ (range P.coroot) = ⊤ →
    ∃ e : P.weylGroup ≃* RootData.realWeylGroup P,
      (∀ w i, (e w).val (RootData.realRoot P i) = RootData.realRoot P (P.weylGroupToPerm w i)) ∧
      (∀ i, (e (RootPairing.weylGroup.ofIdx P i)).val = RootData.realReflection P i)

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

open Pinning (SplitBorelPair AttachedDatum)
open RootGroups (AdditiveLine)
open GeometricRadicals (GeometricGroup IsSemisimple)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)

/-- The based datum of a pinned split Borel pair, including the actual
normalizer quotient. -/
def SplitPinnedComparison.{u} : Prop :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k) (P : SplitBorelPair k),
    ∃ (U : OrderedRootProducts.RootSubgroupFamily P.T) (_ : Pinning.Pinning A P U)
      (D : AttachedDatum P),
      letI := D.comm
      Nonempty (DatumAndWeyl.Identification D.datum)

/-- Over the algebraic closure, the geometric group has a pinned split
Borel pair with its actual Weyl group and full simple coroot lattice. -/
def GeometricPinnedDatum.{u} : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsSemisimple G → GeometricallySimplyConnected G →
    ∀ A : AdditiveLine (AlgebraicClosure k),
      ∃ (P : SplitBorelPair (AlgebraicClosure k)) (_ : P.G = GeometricGroup G)
        (U : OrderedRootProducts.RootSubgroupFamily P.T) (_ : Pinning.Pinning A P U)
        (D : AttachedDatum P),
        letI := D.comm
        Nonempty (DatumAndWeyl.Identification D.datum) ∧ corootLattice D = ⊤

/-- Type A has just the two path orientations, which agree in rank one. -/
def TypeAPermutations : Prop :=
  ∀ n, ∀ σ : Equiv.Perm (Fin n),
    PreservesCartan (CartanMatrix.A n) (CartanMatrix.A n) σ ↔
      σ = Equiv.refl _ ∨ σ = Fin.revPerm

/-- The orientations at the multiple edge rule out all nonidentity symmetries. -/
def TypeBCPermutations : Prop :=
  ∀ n, 2 ≤ n → ∀ σ : Equiv.Perm (Fin n),
    (PreservesCartan (CartanMatrix.B n) (CartanMatrix.B n) σ ↔ σ = Equiv.refl _) ∧
    (PreservesCartan (CartanMatrix.C n) (CartanMatrix.C n) σ ↔ σ = Equiv.refl _)

/-- The symmetry of E₆ in the numbering of `CartanMatrix.E`. -/
def E6Reflection : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 5).trans (Equiv.swap 2 4)

/-- The exceptional diagrams have only the stated Cartan symmetries. -/
def ExceptionalPermutations : Prop :=
  (∀ σ : Equiv.Perm (Fin 6), PreservesCartan (CartanMatrix.E 6) (CartanMatrix.E 6) σ ↔
    σ = Equiv.refl _ ∨ σ = E6Reflection) ∧
  (∀ σ : Equiv.Perm (Fin 7), PreservesCartan (CartanMatrix.E 7) (CartanMatrix.E 7) σ ↔
    σ = Equiv.refl _) ∧
  (∀ σ : Equiv.Perm (Fin 8), PreservesCartan (CartanMatrix.E 8) (CartanMatrix.E 8) σ ↔
    σ = Equiv.refl _) ∧
  (∀ σ : Equiv.Perm (Fin 4), PreservesCartan CartanMatrix.F₄ CartanMatrix.F₄ σ ↔
    σ = Equiv.refl _) ∧
  (∀ σ : Equiv.Perm (Fin 2), PreservesCartan CartanMatrix.G₂ CartanMatrix.G₂ σ ↔
    σ = Equiv.refl _)

/-- A simply connected datum on a nontrivial split group has a simple root. -/
def NonemptySimpleRoots.{u} : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P),
    letI := D.comm
    corootLattice D = ⊤ → ¬ IsZero P.G.val → Nonempty D.base.support

/-- For ranks greater than four, the long arm is fixed and the two short
arms can be interchanged. -/
def TypeDPermutations : Prop :=
  ∀ n, ∀ h : 5 ≤ n, ∀ σ : Equiv.Perm (Fin n),
    PreservesCartan (CartanMatrix.D n) (CartanMatrix.D n) σ ↔
      σ = Equiv.refl _ ∨
      σ = Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩

/-- Absolute almost simplicity tests smooth connected normal subgroups over
the algebraic closure and excludes the trivial group. -/
def IsAbsolutelyAlmostSimple {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  IsSemisimple G ∧ ¬ IsZero (GeometricGroup G).val ∧
    ∀ N : ClosedSubgroup (GeometricGroup G).val,
      GeometricRadicals.IsSmoothConnectedNormal N →
        IsZero N.group ∨ IsIso N.inclusion

/-- An orthogonal partition of the simple vertices of a split datum with full
coroot lattice is realized by a product over the algebraically closed field. -/
def GeometricProductOfBlocks.{u} : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (P : SplitBorelPair k) (D : AttachedDatum P),
    letI := D.comm
    corootLattice D = ⊤ →
    ∀ S : Set D.base.support, S.Nonempty → Sᶜ.Nonempty →
      (∀ i ∈ S, ∀ j ∉ S,
        RootData.integralCartan D.datum.rootDatum D.base i j = 0 ∧
        RootData.integralCartan D.datum.rootDatum D.base j i = 0) →
      ∃ H J : AffineAlgebraicGroup k,
        IsSemisimple H ∧ IsSemisimple J ∧ ¬ IsZero H.val ∧ ¬ IsZero J.val ∧
        Nonempty (P.G.val ≅ Limits.prod H.val J.val)

/-- The geometric obstruction to a disconnected diagram. -/
def GeometricDiagramConnected.{u} : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsAbsolutelyAlmostSimple G →
    ∀ (P : SplitBorelPair (AlgebraicClosure k)), P.G = GeometricGroup G →
    ∀ D : AttachedDatum P,
      letI := D.comm
      corootLattice D = ⊤ →
      (integralDiagram (RootData.integralCartan D.datum.rootDatum D.base)).IsConnected

/-- Classification on the actual based datum. The real realization uses
the absolute characters and the simple roots of the chosen Borel. -/
def ClassifiedDatum {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P) : Prop :=
  letI := D.comm
  let Q := D.datum.rootDatum
  let E := RootData.realRootSpan Q
  let R := range (RootData.realRoot Q)
  corootLattice D = ⊤ ∧
  ∃ (W : DatumAndWeyl.Identification D.datum) (ρ : W.image.labels ≃* RootData.realWeylGroup Q),
    (∀ (w : W.image.labels) (i : AbstractPairing.Root P.T),
      ((ρ w).val (RootData.realRoot Q i)).val = (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul (w.val i.val)) ∧
    (∀ i, (ρ (W.labelEquiv (RootPairing.weylGroup.ofIdx Q i))).val = RootData.realReflection Q i) ∧
    ∃ (t : FiniteDynkinType) (e : D.base.support ≃ Fin t.rank),
      PreservesCartan (RootData.integralCartan Q D.base) t.cartan e ∧
      (Function.Injective (RootData.realRoot Q) ∧
        (∀ i, (RootData.realRoot Q i).val = (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul i.val) ∧
        ∃ metric : InnerProductSpace.Core ℝ E,
          letI : NormedAddCommGroup E := metric.toNormedAddCommGroup
          letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore metric.toCore
          (∀ (w : W.image.labels) (x y : E), inner ℝ ((ρ w).val x) ((ρ w).val y) = inner ℝ x y) ∧
          (∀ i (x : E), RootData.realCoroot Q i x =
            2 * inner ℝ x (RootData.realRoot Q i) / inner ℝ (RootData.realRoot Q i) (RootData.realRoot Q i)) ∧
          (∀ i (x : E), RootData.realReflection Q i x = rootReflection (RootData.realRoot Q i) x) ∧
          IsRootSystem R ∧
          ∃ (z : E) (b : Basis D.base.support ℝ E),
            RootRegular R z ∧ positiveRoots R z = RootData.realRoot Q '' {i | D.base.IsPos i} ∧
            (∀ i, b i = RootData.realRoot Q i) ∧ IsSimpleBasis R z b ∧
            cartanMatrix b = (RootData.integralCartan Q D.base).map (fun n : ℤ => (n : ℝ)) ∧
            (dynkinDiagram b).IsConnected) ∧
      ∃ (c : Basis (Fin t.rank) ℤ (Additive (CharacterDescent.Cocharacter P.T.group)))
        (x : Additive (CharacterDescent.Character P.T.group) ≃ₗ[ℤ] (Fin t.rank → ℤ)),
        (∀ i, c i = Q.coroot (e.symm i).val) ∧
        (∀ a b, Q.toLinearMap a b = ∑ i, c.equivFun b i * x a i) ∧
        (∀ i, x (Q.root (e.symm i).val) = simpleCharacter t.cartan i) ∧
        range (fun i => (x (Q.root i), c.equivFun (Q.coroot i))) = {p | CartanRoots t.cartan p}

/-- The classification applies to any split Borel pair of the geometric group. -/
def ClassificationOfGeometricPair.{u} : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ (P : SplitBorelPair (AlgebraicClosure k)), P.G = GeometricGroup G →
      ∀ A : AdditiveLine (AlgebraicClosure k),
        ∃ (U : OrderedRootProducts.RootSubgroupFamily P.T) (_ : Pinning.Pinning A P U)
          (D : AttachedDatum P), ClassifiedDatum D

/-- An absolutely almost simple simply connected group has a classified
absolute based datum in a pinned Borel pair over the algebraic closure. -/
def AbsoluteClassification.{u} : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ A : AdditiveLine (AlgebraicClosure k),
      ∃ (P : SplitBorelPair (AlgebraicClosure k)) (_ : P.G = GeometricGroup G)
        (U : OrderedRootProducts.RootSubgroupFamily P.T) (_ : Pinning.Pinning A P U)
        (D : AttachedDatum P), ClassifiedDatum D

/-- A Cartan relabelling transports the based diagram permutations by conjugation. -/
def CartanPermutationTransport.{u,v} : Prop :=
  ∀ {I : Type u} {J : Type v} {A : Matrix I I ℤ} {B : Matrix J J ℤ} {e : I ≃ J},
    PreservesCartan A B e → ∀ σ : Equiv.Perm I,
      PreservesCartan A A σ ↔ PreservesCartan B B ((e.symm.trans σ).trans e)

/-- A geometric product with two nontrivial semisimple factors contradicts
absolute almost simplicity. -/
def NoGeometricProduct.{u} : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsAbsolutelyAlmostSimple G →
    ∀ H J : AffineAlgebraicGroup (AlgebraicClosure k),
      IsSemisimple H → IsSemisimple J → ¬ IsZero H.val → ¬ IsZero J.val →
      IsEmpty ((GeometricGroup G).val ≅ Limits.prod H.val J.val)

end LinearAlgebraicGroups.Specs.AbsoluteDynkinTypes
