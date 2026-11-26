import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeChambers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeWeylScheme
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
import Mathlib.LinearAlgebra.RootSystem.Defs

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Relative.RelativeReflections

open CharacterDescent (Character Cocharacter)
open CharacterPairing (adjointWeightVectors pairing)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open GeometricBorelConjugacy (IsReducedIdentityComponent subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsSplitTorus)
open MaximalSplitTori (IsMaximalSplitTorus)
open RelativeChambers (IsChamber relativeRoots)
open RelativeWeylScheme (QuotientData rationalProjection)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (lieImage)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
local notation "Gm" => specGroup (groupAlgebra k IntegerCharacters)

abbrev Root (S : ClosedSubgroup G.val) := ↥(relativeRoots S)

/-- The full kernel of a nontrivial split torus character, with its integral
annihilator and the universal factorization of maps killing it. -/
structure CharacterKernel {S : GroupScheme k} (a : Character S) where
  subgroup : ClosedSubgroup S
  isKernel : IsSchemeKernel a subgroup
  flat : Flat a.hom.hom.left
  surjective : Surjective a.hom.hom.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation a.hom.hom.left
  trivialRestrict_iff : ∀ b : Character S,
    subgroup.inclusion ≫ b = 1 ↔ ∃ n : ℤ, b = a ^ n
  factor : ∀ (L : GroupScheme k) (f : S ⟶ L),
    (∀ (X : SchemeOver k) (d : X ⟶ subgroup.group.X),
      d ≫ (subgroup.inclusion ≫ f).hom.hom = toUnit X ≫ η[L.X]) →
    ∃! c : Gm ⟶ L, a ≫ c = f

/-- The kernel and its quotient are constructed for all nontrivial
characters over any ground field. -/
def CharacterKernels : Prop :=
  ∀ {k : Type u} [Field k] (S : GroupScheme k), IsSplitTorus S →
    ∀ a : Character S, a ≠ 1 → Nonempty (CharacterKernel a)

/-- The identity component of the scheme centralizer of the full kernel,
with the original split torus identified inside it. -/
structure RootCentralizer (S : ClosedSubgroup G.val) (a : Root S) where
  kernel : CharacterKernel a.val
  centralizer : ClosedSubgroup G.val
  represents : RepresentsSubgroup centralizer
    (fun _ g ↦ Centralizes (kernel.subgroup.inclusion ≫ S.inclusion) g)
  smooth : Smooth centralizer.group.X.hom
  component : ClosedSubgroup centralizer.group
  isIdentityComponent : IsReducedIdentityComponent component
  isOpen : IsOpenImmersion component.inclusion.hom.hom.left
  reductive : IsReductive
    (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup centralizer) component)
  torus : ClosedSubgroup component.group
  torusIso : S.group ≅ torus.group
  torusInclusion :
    torusIso.hom ≫ torus.inclusion ≫ component.inclusion ≫ centralizer.inclusion = S.inclusion
  maximal : IsMaximalSplitTorus torus
  lieWeights : ∀ (b : Character S.group) (v : Lie k G.val),
    v ∈ adjointWeightVectors S b → v ≠ 0 →
      (v ∈ lieImage (subgroupOfSubgroup centralizer component) ↔
        kernel.subgroup.inclusion ≫ b = 1)
  roots : (fun b : Character torus.group ↦ torusIso.hom ≫ b) '' relativeRoots torus =
    {b ∈ relativeRoots S | ∃ n : ℤ, b = a.val ^ n}
  rootPresent : a.val ∈ (fun b : Character torus.group ↦ torusIso.hom ≫ b) '' relativeRoots torus
  oppositePresent :
    a.val⁻¹ ∈ (fun b : Character torus.group ↦ torusIso.hom ≫ b) '' relativeRoots torus
  twoChambers : ∃ A B : Set (relativeRoots torus),
    IsChamber torus A ∧ IsChamber torus B ∧ A ≠ B ∧
      ∀ C, IsChamber torus C → C = A ∨ C = B

def RootCentralizers : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      ∀ a : Root S, Nonempty (RootCentralizer S a)

/-- The Weyl labels act on the actual roots and simply transitively on the
chambers obtained from their positive sign patterns. -/
structure ChamberAction {S : ClosedSubgroup G.val} (D : QuotientData S) where
  permutation : D.splitImage.labels →* Equiv.Perm (Root S)
  root_eq : ∀ w a, (permutation w a).val = w.val a.val
  existsChamber : ∃ A : Set (Root S), IsChamber S A
  preserves : ∀ (w : D.splitImage.labels) A, IsChamber S A → IsChamber S (permutation w '' A)
  simplyTransitive : ∀ A B, IsChamber S A → IsChamber S B →
    ∃! w : D.splitImage.labels, permutation w '' A = B

/-- The indicated label sends each of a pair of distinct chambers to the other. -/
def ChamberAction.SwapsChambers {S : ClosedSubgroup G.val} {D : QuotientData S}
    (A : ChamberAction D) (w : D.splitImage.labels) : Prop :=
  ∃ U V : Set (Root S), IsChamber S U ∧ IsChamber S V ∧ U ≠ V ∧
    A.permutation w '' U = V ∧ A.permutation w '' V = U

/-- The label of the reflection is represented inside the rank-one group.
Its local Weyl label is the nonidentity element of the two-element group. -/
structure RootReflection {S : ClosedSubgroup G.val} (D : QuotientData S) (a : Root S) where
  centralizer : RootCentralizer S a
  localQuotient : QuotientData
    (G := closedSubgroupAlgebraicGroup
      (G := closedSubgroupAlgebraicGroup centralizer.centralizer) centralizer.component) centralizer.torus
  localLabel : localQuotient.splitImage.labels
  localLabel_ne_one : localLabel ≠ 1
  localWeylGroup : ∀ w : localQuotient.splitImage.labels, w = 1 ∨ w = localLabel
  localRepresentative : 𝟙_ (SchemeOver k) ⟶ localQuotient.normalizer.group.X
  localProjects : rationalProjection localQuotient localRepresentative =
    localQuotient.splitImage.constantGroup.sectionPoint localLabel
  localChambers : ∃ A : ChamberAction localQuotient, A.SwapsChambers localLabel
  label : D.splitImage.labels
  representative : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X
  representative_eq : representative ≫ D.normalizer.inclusion.hom.hom =
    localRepresentative ≫ localQuotient.normalizer.inclusion.hom.hom ≫
      centralizer.component.inclusion.hom.hom ≫ centralizer.centralizer.inclusion.hom.hom
  projects : rationalProjection D representative = D.splitImage.constantGroup.sectionPoint label
  involution : label ^ 2 = 1
  schemeInvolution : (D.splitImage.conjugation label).hom ≫ (D.splitImage.conjugation label).hom =
    𝟙 S.group
  fixesKernel : centralizer.kernel.subgroup.inclusion ≫ (D.splitImage.conjugation label).hom =
    centralizer.kernel.subgroup.inclusion
  coroot : Cocharacter S.group
  factorization : (a.val ≫ coroot).hom.hom =
    (𝟙 S.group.X) * (D.splitImage.conjugation label).hom.hom.hom⁻¹
  characterFormula : ∀ b : Character S.group, label.val b = b * a.val ^ (-pairing S.group b coroot)
  rootPairing : pairing S.group a.val coroot = 2

/-- The per-root construction, with the integral cocharacter on the
original torus, for any presentation of the relative Weyl group. -/
def RootReflections : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      ∀ (D : QuotientData S) (a : Root S), Nonempty (RootReflection D a)

def NormalizerChambers : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      ∀ D : QuotientData S, Nonempty (ChamberAction D)

/-- The whole chamber set is acted on via the action on root characters.
The root and coroot permutations agree on the integral lattices. -/
structure Datum {S : ClosedSubgroup G.val} [IsCommMonObj S.group.X]
    (D : QuotientData S) where
  finiteRoots : Finite (Root S)
  freeCharacters : Module.Free ℤ (Additive (Character S.group))
  finiteCharacters : Module.Finite ℤ (Additive (Character S.group))
  freeCocharacters : Module.Free ℤ (Additive (Cocharacter S.group))
  finiteCocharacters : Module.Finite ℤ (Additive (Cocharacter S.group))
  reflection : ∀ a : Root S, RootReflection D a
  rootDatum : RootDatum (Root S) (Additive (Character S.group)) (Additive (Cocharacter S.group))
  root_eq : ∀ a, rootDatum.root a = Additive.ofMul a.val
  coroot_eq : ∀ a, rootDatum.coroot a = Additive.ofMul (reflection a).coroot
  pairing_eq : ∀ x y, rootDatum.toLinearMap (Additive.ofMul x) (Additive.ofMul y) = pairing S.group x y
  normalizerPerm : D.splitImage.labels →* Equiv.Perm (Root S)
  rootAction : ∀ (w : D.splitImage.labels) (a : Root S), (normalizerPerm w a).val = w.val a.val
  corootAction : ∀ (w : D.splitImage.labels) (a : Root S),
    (reflection (normalizerPerm w a)).coroot =
      (reflection a).coroot ≫ (D.splitImage.conjugation w).hom
  reflectionAction : ∀ (w : D.splitImage.labels) (a : Root S),
    (reflection (normalizerPerm w a)).label = w * (reflection a).label * w⁻¹
  sameWall : ∀ a b : Root S, RootGroups.Proportional a.val b.val →
    (reflection a).label = (reflection b).label
  generates : Subgroup.closure (Set.range (fun a ↦ (reflection a).label)) = ⊤
  chamberPreservation : ∀ (w : D.splitImage.labels) A,
    IsChamber S A → IsChamber S (normalizerPerm w '' A)
  chamberAction : ∀ A B, IsChamber S A → IsChamber S B →
    ∃! w : D.splitImage.labels, normalizerPerm w '' A = B

/-- The relative root datum on the actual character and cocharacter
lattices, permitting an empty root set and proportional roots. -/
def RelativeRootDatum : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
    ∀ D : QuotientData S, ∃ h : IsCommMonObj S.group.X, letI := h; Nonempty (Datum D)

/-- The lattice and generation argument from the scheme-theoretic
reflections and the compatible Weyl chamber action. -/
def RelativeRootDatumAssembly : Prop :=
  RootReflections.{u} → NormalizerChambers.{u} → RelativeRootDatum.{u}

end

end LinearAlgebraicGroups.Specs.Relative.RelativeReflections
