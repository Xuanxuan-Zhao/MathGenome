import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.NormalizerComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.RankOneRelations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SteinbergPinnedDescent

open Pinning (PinnedGroup AttachedDatum SimpleRoot)
open RootGroups (AdditiveLine rootPoint)
open NormalizerComparison (SimpleRepresentative)
open AdjointRepresentation (GroupPoints)
open RootWeightAction (Representation)

noncomputable section

variable {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
variable {D : AttachedDatum P.pair}

/-- The factor of the Steinberg word associated to a pinned simple root. -/
def factor (i : SimpleRoot P.pair) (n : SimpleRepresentative P D i)
    (R : TestAlgebra k) (t : R) : GroupPoints P.pair.G.val R :=
  rootPoint ((P.pin i).val.hom ≫ (P.roots i.val).val.inclusion) R t *
    (show GroupPoints P.pair.G.val R from toUnit _ ≫ n.reflection.representative)

/-- Orthogonality in both orders of the actual simple roots. -/
def Orthogonal (D : AttachedDatum P.pair) (i j : SimpleRoot P.pair) : Prop :=
  letI := D.comm
  D.datum.rootDatum.pairing i.val j.val = 0 ∧ D.datum.rootDatum.pairing j.val i.val = 0

def OrthogonalFactors : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (i j : SimpleRoot P.pair), i ≠ j → Orthogonal D i j →
      ∀ (n : SimpleRepresentative P D i) (m : SimpleRepresentative P D j)
        (R : TestAlgebra k) (t s : R), Commute (factor i n R t) (factor j m R s)

/-- The diagram involution in zero-based Bourbaki numbering. -/
def e6Involution : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 5 * Equiv.swap 2 4

/-- List the simple roots with each diagram orbit consecutive. -/
def e6Blocks : List (List (Fin 6)) := [[0, 5], [1], [2, 4], [3]]

def E6Diagram : Prop :=
  (∀ e : Equiv.Perm (Fin 6), (∀ i j, CartanMatrix.E 6 (e i) (e j) = CartanMatrix.E 6 i j) →
    e = 1 ∨ e = e6Involution) ∧
  (∀ i j, CartanMatrix.E 6 (e6Involution i) (e6Involution j) = CartanMatrix.E 6 i j) ∧
  e6Involution 0 = 5 ∧ e6Involution 5 = 0 ∧
  e6Involution 2 = 4 ∧ e6Involution 4 = 2 ∧
  e6Involution 1 = 1 ∧ e6Involution 3 = 3 ∧
  CartanMatrix.E 6 0 5 = 0 ∧ CartanMatrix.E 6 5 0 = 0 ∧
  CartanMatrix.E 6 2 4 = 0 ∧ CartanMatrix.E 6 4 2 = 0

/-- The ordered word using a list of consecutive orbit blocks. -/
def word (n : ∀ i : SimpleRoot P.pair, SimpleRepresentative P D i)
    (blocks : List (List (SimpleRoot P.pair))) (R : TestAlgebra k)
    (t : SimpleRoot P.pair → R) : GroupPoints P.pair.G.val R :=
  (blocks.flatten.map fun i ↦ factor i (n i) R (t i)).prod

/-- Action on parameters indexed by simple roots. -/
def permuteParameters {I S : Type*} (e : Equiv.Perm I) (σ : S → S) (t : I → S) :
    I → S :=
  fun j ↦ σ (t (e.symm j))

/-- The trace of a rational representation on split-field points. -/
def traceValue {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation P.pair.G.val I)
    (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R) : R :=
  Matrix.trace (ρ.app R g : Matrix.GeneralLinearGroup I R).val

/-- Equivariance and uniqueness give a fixed parameter and hence a fixed word.
Conjugacy invariance permits the matching trace tuple to come from an
inner-twisted fixed point. -/
def FixedMatching : Prop :=
  ∀ {J S H Δ : Type*} [Group H] (e : Δ → Equiv.Perm J) (σ : Δ → S → S)
    (a : Δ → MulAut H) (w : (J → S) → H) (tr : H → J → S),
    (∀ δ t, a δ (w t) = w (permuteParameters (e δ) (σ δ) t)) →
    (∀ δ g, tr (a δ g) = permuteParameters (e δ) (σ δ) (tr g)) →
    (∀ g z, tr (z * g * z⁻¹) = tr g) →
    ∀ (v : J → S),
      ((∀ δ, permuteParameters (e δ) (σ δ) v = v) ∨
        ∃ (y : H) (z : Δ → H), tr y = v ∧ ∀ δ, z δ * a δ y * (z δ)⁻¹ = y) →
      (∃! t, tr (w t) = v) →
      ∃ t, tr (w t) = v ∧
        (∀ δ, permuteParameters (e δ) (σ δ) t = t) ∧ ∀ δ, a δ (w t) = w t

/-- Each block is preserved setwise, and only commuting factors are reordered. -/
def BlockEquivariance : Prop :=
  ∀ {J S H : Type*} [Group H] (p : Equiv.Perm J) (σ : S → S) (a : MulAut H)
    (b : List (List J)) (f : J → S → H),
    (∀ i t, a (f i t) = f (p i) (σ t)) →
    (∀ B ∈ b, (B.map p).Perm B) →
    (∀ (t : J → S) (B : List J), B ∈ b → (B.map fun i ↦ f i (t i)).Pairwise Commute) →
    ∀ (t : J → S), a ((b.flatten.map fun i ↦ f i (t i)).prod) =
      (b.flatten.map fun i ↦ f i (permuteParameters p σ t i)).prod

def E6BlockOrder : Prop :=
  e6Blocks.flatten.Nodup ∧ (∀ i : Fin 6, i ∈ e6Blocks.flatten) ∧
  (∀ e : Equiv.Perm (Fin 6), (∀ i j, CartanMatrix.E 6 (e i) (e j) = CartanMatrix.E 6 i j) →
    ∀ b ∈ e6Blocks, (b.map e).Perm b) ∧
  ∀ b ∈ e6Blocks, b.Pairwise (fun i j ↦ i ≠ j ∧ CartanMatrix.E 6 i j = 0 ∧ CartanMatrix.E 6 j i = 0)

section Pinning

open Pinning (PinnedIso transportCharacter)
open CharacterDescent (Character Cocharacter)

def IsBasedLift (D : AttachedDatum P.pair) (d : Aut D.toBased) (f : PinnedIso P P) : Prop :=
  letI := D.comm
  (∀ χ : Character P.pair.T.group, d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
    Additive.ofMul (transportCharacter f.torus χ)) ∧
  (∀ i : AbstractPairing.Root P.pair.T,
    Additive.toMul (D.datum.rootDatum.coroot i) ≫ f.torus.hom =
      Additive.toMul (D.datum.rootDatum.coroot (d.asIso.hom.val.indexEquiv i)))

/-- The diagram permutation is obtained by restricting the actual based automorphism. -/
def diagramPermutation (D : AttachedDatum P.pair) (d : Aut D.toBased) :
    Equiv.Perm (SimpleRoot P.pair) := by
  letI := D.comm
  let e : Equiv.Perm (AbstractPairing.Root P.pair.T) := d.asIso.hom.val.indexEquiv
  have h (i : AbstractPairing.Root P.pair.T) : Pinning.IsSimple P.pair i ↔
      Pinning.IsSimple P.pair (e i) := by
    rw [← D.simple_iff, ← D.simple_iff]
    have he : e '' (D.base.support : Set (AbstractPairing.Root P.pair.T)) =
        D.base.support := d.asIso.hom.property
    change i ∈ (D.base.support : Set (AbstractPairing.Root P.pair.T)) ↔
      e i ∈ (D.base.support : Set (AbstractPairing.Root P.pair.T))
    constructor
    · intro hi
      rw [← he]
      exact ⟨i, hi, rfl⟩
    · intro hi
      rw [← he] at hi
      obtain ⟨j, hj, hij⟩ := hi
      exact e.injective hij ▸ hj
  exact e.subtypeEquiv (fun i ↦ h i)

/-- The pinned map acts on both the parametrized positive root and the linked
Weyl lift. The equation holds on every test algebra. -/
def PinnedFactors : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (d : Aut D.toBased) (f : PinnedIso P P),
    IsBasedLift D d f →
    ∀ (n : ∀ i : SimpleRoot P.pair, SimpleRepresentative P D i)
      (R : TestAlgebra k) (i : SimpleRoot P.pair) (t : R),
      let j := diagramPermutation D d i
      ((groupPointsFunctor k).map f.group.hom).app R (factor i (n i) R t) =
        factor j (n j) R t

end Pinning

/-- The diagram action is trivial in the split cases. In the outer case
the Cartan matrix is that of Bourbaki-numbered E₆. -/
def ExceptionalDiagram (D : AttachedDatum P.pair) {Δ : Type u}
    (outer : Δ → Aut D.toBased) : Prop :=
  (∀ δ, diagramPermutation D (outer δ) = 1) ∨
    ∃ e : Fin 6 ≃ SimpleRoot P.pair,
      ∀ i j, letI := D.comm
        D.datum.rootDatum.pairing (e i).val (e j).val = CartanMatrix.E 6 i j

/-- The orbits of a nontrivial E₆ diagram action in Bourbaki coordinates. -/
def E6DiagramOrbits : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) {Γ : Type u} [Group Γ] (outer : Γ →* Aut D.toBased)
    (e : Fin 6 ≃ SimpleRoot P.pair),
    (∀ i j, letI := D.comm
      D.datum.rootDatum.pairing (e i).val (e j).val = CartanMatrix.E 6 i j) →
    (∃ σ, diagramPermutation D (outer σ) ≠ 1) →
    ∀ i j, (∃ σ, diagramPermutation D (outer σ) (e i) = e j) ↔ j = i ∨ j = e6Involution i

/-- An order for the actual simple roots compatible with the diagram action. -/
def ExceptionalOrbitOrder : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) {Δ : Type u} (outer : Δ → Aut D.toBased),
    ExceptionalDiagram D outer →
    ∃ blocks : List (List (SimpleRoot P.pair)),
      blocks.flatten.Nodup ∧ (∀ i, i ∈ blocks.flatten) ∧
      (∀ δ b, b ∈ blocks → (b.map (diagramPermutation D (outer δ))).Perm b) ∧
      ∀ b ∈ blocks, b.Pairwise (fun i j ↦ i ≠ j ∧ Orthogonal D i j)

section FieldPoints

open RelativeFormComparison (fieldMap fieldTest)

/-- Ordinary scalar Galois action on split-field points of a ground-field group. -/
def coefficientAction (S : Type u) [Field S] [Algebra k S] (G : GroupScheme k)
    (σ : Gal(S/k)) :
    MulAut (GroupPoints G (CommAlgCat.of k S)) :=
  RelativeFormComparison.relativeAction k S (yonedaGrp.obj G) σ

def RationalPoints : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    (G : AffineAlgebraicGroup k) (g : GroupPoints G.val (CommAlgCat.of k S)),
    (∀ σ : Gal(S/k), coefficientAction S G.val σ g = g) ↔
    ∃ x : GroupPoints G.val (CommAlgCat.of k k),
      mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x = g

def TraceConjugacy : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I] {A : AdditiveLine k}
    {P : PinnedGroup A} (ρ : Representation P.pair.G.val I) (R : TestAlgebra k)
    (g z : GroupPoints P.pair.G.val R), traceValue ρ R (z * g * z⁻¹) = traceValue ρ R g

def TraceCoefficients : Prop :=
  ∀ {k S I : Type u} [Field k] [Field S] [Algebra k S] [Fintype I] [DecidableEq I]
    {A : AdditiveLine k} {P : PinnedGroup A} (ρ : Representation P.pair.G.val I)
    (σ : Gal(S/k)) (g : GroupPoints P.pair.G.val (CommAlgCat.of k S)),
      traceValue ρ _ (coefficientAction S P.pair.G.val σ g) = σ (traceValue ρ _ g)

end FieldPoints

section WordEquivariance

open Pinning (PinnedIso)
open CharacterDescent (Character)

def pinnedPointMap {R : TestAlgebra k} (f : PinnedIso P P) :
    MulAut (GroupPoints P.pair.G.val R) :=
  (((groupPointsFunctor k).mapIso f.group).app R).groupIsoToMulEquiv

def pinnedAction (S : Type u) [Field S] [Algebra k S]
    (f : PinnedIso P P) (σ : Gal(S/k)) :
    MulAut (GroupPoints P.pair.G.val (CommAlgCat.of k S)) :=
  pinnedPointMap f * coefficientAction S P.pair.G.val σ

def WordEquivariance : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (d : Aut D.toBased) (f : PinnedIso P P),
    IsBasedLift D d f →
    ∀ (n : ∀ i : SimpleRoot P.pair, SimpleRepresentative P D i)
      (blocks : List (List (SimpleRoot P.pair))),
      (∀ b ∈ blocks, (b.map (diagramPermutation D d)).Perm b) →
      (∀ b ∈ blocks, b.Pairwise (fun i j ↦ i ≠ j ∧ Orthogonal D i j)) →
      ∀ (σ : Gal(S/k)) (t : SimpleRoot P.pair → S),
        pinnedAction S f σ (word n blocks (CommAlgCat.of k S) t) =
          word n blocks (CommAlgCat.of k S) (permuteParameters (diagramPermutation D d) σ t)

end WordEquivariance

section RelativeDescent

open AutomorphismSequence (relativePoints scalarAut forgetPinning)
open RelativeFormComparison (fieldTest transportedAut)
open Pinning (PinnedIso)

/-- Evaluate the scalar-extension comparison at the splitting field itself. -/
def comparisonOnPoints {S : Type u} [Field S] [Algebra k S]
    {G H : GroupScheme k}
    (e : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)) :
    GroupPoints G (CommAlgCat.of k S) ≃* GroupPoints H (CommAlgCat.of k S) :=
  (e.app (op (Over.mk (𝟙 (fieldTest k S))))).groupIsoToMulEquiv

def RelativeDescent : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    {A : AdditiveLine k} {P : PinnedGroup A} (G : AffineAlgebraicGroup k)
    (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (p : Gal(S/k) → Aut P),
    (∀ σ, transportedAut k S e σ =
      scalarAut (Functor.mapAut P (forgetPinning (A := A)) (p σ)) (fieldTest k S)) →
    ∀ y : GroupPoints P.pair.G.val (CommAlgCat.of k S),
    (∀ σ, pinnedAction S (p σ).asIso.hom σ y = y) →
    ∃ x : GroupPoints G.val (CommAlgCat.of k k),
      mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x = comparisonOnPoints e y

end RelativeDescent

section FundamentalTraces

open Pinning (PinnedIso)
open CharacterDescent (Character)
open FlagLineBundle (OppositeBorelPair)
open GeometricRadicals (IsUnipotentRadical)
open Unipotent (closedSubgroupAlgebraicGroup)
open PrimitiveLine (IsSimple)
open SimpleClassification (HasHighestWeight)

/-- Complete the given pinned pair by a choice of opposite Borel. -/
structure OppositeBorel (P : Pinning.SplitBorelPair k) where
  negative : ClosedSubgroup P.G.val
  borel : GeometricBorelConjugacy.IsKBorel negative
  containsTorus : SchemeDerivedGroup.IsSubgroupOf P.T negative
  opposite : OpenCell.AreOpposite P.T P.B negative

def OppositeBorel.pair (N : OppositeBorel P.pair) : OppositeBorelPair P.pair.G :=
  ⟨P.pair.T, P.pair.B, N.negative, P.pair.reductive, P.pair.split, P.pair.maximal,
    P.pair.borel, N.borel, P.pair.containsTorus, N.containsTorus, N.opposite⟩

/-- Simple rational representations indexed by the simple roots of the pinning,
with their highest weights. -/
structure HighestWeightModules (N : OppositeBorel P.pair)
    (U : ClosedSubgroup P.pair.B.group) where
  weight : SimpleRoot P.pair → Character P.pair.T.group
  index : SimpleRoot P.pair → Type u
  [finiteIndex : ∀ i, Fintype (index i)]
  [decidableIndex : ∀ i, DecidableEq (index i)]
  representation : ∀ i, Representation P.pair.G.val (index i)
  simple : ∀ i, IsSimple (representation i)
  highest : ∀ i, HasHighestWeight N.pair U (representation i) (weight i)

attribute [instance] HighestWeightModules.finiteIndex HighestWeightModules.decidableIndex

/-- Pinned automorphisms permute the regular trace characters. The equality
on every test algebra also specifies the transformation over finite fields. -/
def PinnedTracePermutation : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (d : Aut D.toBased) (f : PinnedIso P P)
    (N : OppositeBorel P.pair) (U : ClosedSubgroup P.pair.B.group),
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
    ∀ (M : HighestWeightModules N U),
    (∀ i, f.torus.hom ≫ M.weight (diagramPermutation D d i) = M.weight i) →
    ∀ (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R),
      (fun i ↦ traceValue (M.representation i) R (pinnedPointMap f g)) =
        permuteParameters (diagramPermutation D d) id (fun i ↦ traceValue (M.representation i) R g)

/-- Trace transformation with scalar Galois action over the splitting field. -/
def TracePermutation : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (d : Aut D.toBased) (f : PinnedIso P P)
    (N : OppositeBorel P.pair) (U : ClosedSubgroup P.pair.B.group),
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
    ∀ (M : HighestWeightModules N U),
    (∀ i, f.torus.hom ≫ M.weight (diagramPermutation D d i) = M.weight i) →
    ∀ (σ : Gal(S/k)) (g : GroupPoints P.pair.G.val (CommAlgCat.of k S)),
      (fun i ↦ traceValue (M.representation i) _ (pinnedAction S f σ g)) =
        permuteParameters (diagramPermutation D d) σ
          (fun i ↦ traceValue (M.representation i) _ g)

end FundamentalTraces

section FundamentalWeights

open CharacterDescent (Character)
open Pinning (PinnedIso)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)

/-- Evaluate an actual torus character on the ordered simple coroots. -/
def simpleCorootValues (D : AttachedDatum P.pair) (χ : Character P.pair.T.group) :
    SimpleRoot P.pair → ℤ :=
  letI := D.comm
  fun i ↦ D.datum.rootDatum.toLinearMap (Additive.ofMul χ) (D.datum.rootDatum.coroot i.val)

def IsFundamental (D : AttachedDatum P.pair) (χ : SimpleRoot P.pair → Character P.pair.T.group) :
    Prop :=
  letI := Classical.decEq (SimpleRoot P.pair)
  ∀ i j, simpleCorootValues D (χ i) j = if j = i then 1 else 0

/-- The fundamental modules are available for the actual pinning of the
simply connected group. -/
def FundamentalModulesExist : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∃ (N : OppositeBorel P.pair) (U : ClosedSubgroup P.pair.B.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U ∧
      ∃ M : HighestWeightModules N U, IsFundamental D M.weight

/-- The Kronecker conditions against the actual simple coroots specify the
fundamental weights. Character detection holds for the semisimple root datum. -/
def FundamentalWeightPermutation : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (d : Aut D.toBased) (f : PinnedIso P P),
    IsBasedLift D d f →
    Function.Injective (simpleCorootValues D) →
    ∀ χ : SimpleRoot P.pair → Character P.pair.T.group,
      IsFundamental D χ →
      ∀ i, f.torus.hom ≫ χ (diagramPermutation D d i) = χ i

end FundamentalWeights

section PinnedReference

open AutomorphismSequence (AdjointQuotient SplitSequence)
open QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction)
open LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle)

def ReferenceDescent : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q} {ω : @Cocycle (Gal(S/k)) (Aut D.toBased) _ (krullTopology k S) _ ⊥
      (trivialOuterAction (k := k) (S := S) D.toBased)}
    (V : PinnedRepresentative (S := S) E ω)
    (y : GroupPoints P.pair.G.val (CommAlgCat.of k S)),
    (∀ σ : Gal(S/k), pinnedAction S (l (ω σ)).asIso.hom σ y = y) →
    ∃ x : GroupPoints V.model.val.val (CommAlgCat.of k k),
      mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x = comparisonOnPoints V.trivialization y

end PinnedReference

section PinnedLifts

open AutomorphismSequence (AdjointQuotient SplitSequence)

def PinnedSequenceLifts : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G},
    SplitSequence P D l Q → ∀ d : Aut D.toBased, IsBasedLift D d (l d).asIso.hom

end PinnedLifts

section Matching

open AutomorphismSequence (AdjointQuotient SplitSequence)
open QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction)
open LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle)
open CharacterDescent (Character)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)
open AutomorphismSequence (relativePoints)
open RelativeFormComparison (fieldTest)

/-- Match either Galois-compatible trace data or the trace tuple of an
inner-twisted fixed point. The unique-preimage hypothesis is supplied by
the split-field trace computation. -/
def MatchingOnPoints {S : Type u} [Field S] [Algebra k S]
    (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P)
    (outer : Gal(S/k) → Aut D.toBased) {G : AffineAlgebraicGroup k}
    (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group}
    (M : HighestWeightModules N U) : Prop :=
  ∃ (n : ∀ i : SimpleRoot P.pair, SimpleRepresentative P D i)
    (blocks : List (List (SimpleRoot P.pair))),
    blocks.flatten.Nodup ∧ (∀ i, i ∈ blocks.flatten) ∧
    (∀ σ b, b ∈ blocks → (b.map (diagramPermutation D (outer σ))).Perm b) ∧
    (∀ b ∈ blocks, b.Pairwise (fun i j ↦ i ≠ j ∧ Orthogonal D i j)) ∧
    let R := CommAlgCat.of k S
    let tr := fun g i ↦ traceValue (M.representation i) R g
    let wrd := word n blocks R
    let a := fun σ : Gal(S/k) ↦ pinnedAction S (l (outer σ)).asIso.hom σ
    let π := fun σ : Gal(S/k) ↦ diagramPermutation D (outer σ)
    let changeParameters := fun σ ↦ permuteParameters (π σ) (fun c : S ↦ σ c)
    (∀ σ t, a σ (wrd t) = wrd (changeParameters σ t)) ∧
    (∀ σ g, tr (a σ g) = changeParameters σ (tr g)) ∧
    ∀ (v : SimpleRoot P.pair → S),
      ((∀ σ, changeParameters σ v = v) ∨
        ∃ (y : GroupPoints P.pair.G.val R) (z : Gal(S/k) → GroupPoints P.pair.G.val R),
          tr y = v ∧ ∀ σ, z σ * a σ y * (z σ)⁻¹ = y) →
      (∃! t, tr (wrd t) = v) →
      ∃ (t : SimpleRoot P.pair → S) (x : GroupPoints G.val (CommAlgCat.of k k)),
        tr (wrd t) = v ∧ (∀ σ, changeParameters σ t = t) ∧
        mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x = comparisonOnPoints e (wrd t)

/-- Pinned word and trace equivariance and rational matching over the
separable closure in the quasi-split reference of F06. -/
def ReferenceMatching : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q} {ω : @Cocycle (Gal(S/k)) (Aut D.toBased) _ (krullTopology k S) _ ⊥
      (trivialOuterAction (k := k) (S := S) D.toBased)}
    (V : PinnedRepresentative (S := S) E ω)
    (N : OppositeBorel P.pair) (U : ClosedSubgroup P.pair.B.group),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
    ∀ (M : HighestWeightModules N U),
      IsFundamental D M.weight → ExceptionalDiagram D (fun σ : Gal(S/k) ↦ ω σ) →
      MatchingOnPoints D l (fun σ : Gal(S/k) ↦ ω σ) V.trivialization M

end Matching

section FinitePinnedReference

open AutomorphismSequence (relativePoints scalarAut forgetPinning)
open RelativeFormComparison (fieldTest transportedAut)
open AdjointBorelCohomology (PinnedTwist)

/-- The scalar-extension isomorphism of the finite descended pair induces
the pinned automorphism on descent of the actual point functors. -/
def FiniteReferenceComparison : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k}
    {B T : ClosedSubgroup G.val} (V : PinnedTwist (P := P) S D l B T),
    ∃ (t : ∀ C : HopfAlgebraCategory k,
          specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C))
      (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S)),
      LinearAlgebraicGroups.Descent.Forms.IsScalarExtensionComparison t ∧
      RelativeFormComparison.IsInducedByHopf t
        (AdjointCocharacters.coordinateHopfIso P.pair.G) (AdjointCocharacters.coordinateHopfIso G)
        V.groupIso e ∧
      ∀ σ : Gal(S/k), transportedAut k S e σ =
        scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l (V.outer σ))) (fieldTest k S)

end FinitePinnedReference

section FinitePointDescent

open AdjointBorelCohomology (PinnedTwist)
open AutomorphismSequence (relativePoints)
open RelativeFormComparison (fieldTest)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)

/-- A fixed split point of the actual finite pinned model has a rational
point as its preimage under scalar extension. -/
def FiniteReferenceDescent : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k}
    {B T : ClosedSubgroup G.val} (V : PinnedTwist (P := P) S D l B T),
    ∃ (t : ∀ C : HopfAlgebraCategory k,
          specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C))
      (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S)),
      LinearAlgebraicGroups.Descent.Forms.IsScalarExtensionComparison t ∧
      RelativeFormComparison.IsInducedByHopf t
        (AdjointCocharacters.coordinateHopfIso P.pair.G) (AdjointCocharacters.coordinateHopfIso G)
        V.groupIso e ∧
      ∀ y : GroupPoints P.pair.G.val (CommAlgCat.of k S),
        (∀ σ : Gal(S/k), pinnedAction S (l (V.outer σ)).asIso.hom σ y = y) →
        ∃ x : GroupPoints G.val (CommAlgCat.of k k),
          mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x = comparisonOnPoints e y

/-- Pinned word and trace equivariance and rational matching over a finite
Galois splitting field of the actual descended pair. -/
def FiniteReferenceMatching : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [FiniteDimensional k S] [IsGalois k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (V : PinnedTwist (P := P) S D l B T) (E : SplitSequence P D l Q)
    (N : OppositeBorel P.pair) (U : ClosedSubgroup P.pair.B.group),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
    ∀ (M : HighestWeightModules N U), IsFundamental D M.weight → ExceptionalDiagram D V.outer →
      ∃ (t : ∀ C : HopfAlgebraCategory k,
          specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C))
        (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S)),
        LinearAlgebraicGroups.Descent.Forms.IsScalarExtensionComparison t ∧
        RelativeFormComparison.IsInducedByHopf t
          (AdjointCocharacters.coordinateHopfIso P.pair.G) (AdjointCocharacters.coordinateHopfIso G)
          V.groupIso e ∧ MatchingOnPoints D l V.outer e M

end FinitePointDescent

end

end LinearAlgebraicGroups.Specs.SteinbergPinnedDescent
