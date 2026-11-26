import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RationalHighestWeightComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleCorootTangents
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PBWSpecialization
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Semisimple.Defs

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SplitLieIntegration

open AbstractPairing (IsAttachedCoroot Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (adjointWeightVectors characterValue pairing)
open FlagLineBundle (OppositeBorelPair)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open RootWeightAction (SimpleRoot)
open AdjointRepresentation (GroupPoints)
open _root_.Shared.Lie.PBW (OrderedWord orderedMonomial)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The point (1+\varepsilon) of the multiplicative group. -/
abbrev infinitesimalUnit (k : Type u) [Field k] : (DualNumber k)ˣ :=
  SimpleCorootTangents.infinitesimalUnit k

/-- The torus differential of a character evaluated on a tangent vector. -/
def characterDifferential {T : GroupScheme k} (χ : Character T) (x : Lie k T) : k :=
  (characterValue χ (CommAlgCat.of k (DualNumber k)) x.toMul.val).snd

/-- The tangent of a cocharacter on the standard first-order unit. -/
abbrev IsCocharacterTangent {T : GroupScheme k} (c : Cocharacter T) (h : Lie k T) : Prop :=
  SimpleCorootTangents.IsCocharacterTangent c h

/-- A weight on the actual ground-field torus Lie algebra. -/
abbrev Weight {T : GroupScheme k} (t : IdentityLieStructure T) : Type u :=
  letI := t.lieRing
  letI := t.lieAlgebra
  Module.Dual k (Lie k T)

/-- Differentiation is linear on torus tangents, embeds the character lattice,
and evaluates on cocharacter tangents by the original integer pairing. -/
def CharacterComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : GroupScheme k),
    IsSplitTorus T → ∀ t : IdentityLieStructure T,
    (∀ c : Cocharacter T, ∃! h : Lie k T, IsCocharacterTangent c h) ∧
    Function.Injective (characterDifferential (T := T)) ∧
    (∃ d : Additive (Character T) →+ Weight t,
      ∀ (χ : Character T) x, d (Additive.ofMul χ) x = characterDifferential χ x) ∧
    ∀ (χ : Character T) (c : Cocharacter T) (h : Lie k T),
      IsCocharacterTangent c h → characterDifferential χ h = (pairing T χ c : k)

/-- The two linked root coordinates of a simple root and its actual coroot
differentiate to a Mathlib `IsSl2Triple`. -/
def RankOneComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k)
    (P : OppositeBorelPair G) (s : IdentityLieStructure G.val),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (α : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group),
      IsAttachedCoroot P.torus α.val c →
      ∃ (h₀ : Lie k P.torus.group) (e f : Lie k G.val),
        IsCocharacterTangent c h₀ ∧
        e ∈ adjointWeightVectors P.torus α.val.val ∧
        f ∈ adjointWeightVectors P.torus α.val.val⁻¹ ∧
        IsSl2Triple (mapPointKernel P.torus.inclusion h₀) e f

/-- The ordered basis of the actual group Lie algebra is sorted into its
negative root spaces, its toral part, and its positive root spaces. Its degrees
come from a regular cocharacter in the positive chamber. -/
structure TriangularBasis {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (s : IdentityLieStructure G.val) where
  J : Type u
  [order : LinearOrder J]
  [finite : Fintype J]
  basis : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis J k (Lie k G.val)
  cochar : Cocharacter P.torus.group
  tangent : Lie k P.torus.group
  tangent_spec : IsCocharacterTangent cochar tangent
  regular : BorelsAndChambers.IsRegular P.torus cochar
  positive : BorelsAndChambers.positiveRoots P.torus cochar = subgroupRoots P.torus P.positive
  degree : J → ℤ
  ordered : Monotone degree
  zero_part : letI := s.lieRing; letI := s.lieAlgebra
    Set.range (mapPointKernel P.torus.inclusion) =
    {x | ∀ j, degree j ≠ 0 → basis.repr x j = 0}
  root_part : letI := s.lieRing; letI := s.lieAlgebra
    ∀ j, degree j ≠ 0 → ∃ α : Root P.torus,
    degree j = pairing P.torus.group α.val cochar ∧
    basis j ∈ adjointWeightVectors P.torus α.val
  root_support : letI := s.lieRing; letI := s.lieAlgebra
    ∀ (α : Root P.torus) (x : Lie k G.val), x ∈ adjointWeightVectors P.torus α.val →
      ∀ j, degree j ≠ pairing P.torus.group α.val cochar → basis.repr x j = 0
  bracket : letI := s.lieRing; letI := s.lieAlgebra
    ∀ j, ⁅mapPointKernel P.torus.inclusion tangent, basis j⁆ = (degree j : k) • basis j

attribute [instance] TriangularBasis.order TriangularBasis.finite

/-- PBW on an ordered basis of the actual Lie algebra, using the pinned
enveloping algebra and the very same monomials as the library theorem. -/
def OrderedPBW : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (s : IdentityLieStructure G.val) {J : Type u} [LinearOrder J],
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ b : Module.Basis J k (Lie k G.val),
    ∃ B : Module.Basis (OrderedWord J) k (UniversalEnvelopingAlgebra k (Lie k G.val)),
      ∀ l, B l = orderedMonomial b l

/-- The triangular basis and its ordered PBW basis exist for the marked split pair. -/
def TriangularPBW : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k)
    (P : OppositeBorelPair G), IsSemisimple G → ∀ s : IdentityLieStructure G.val,
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ b : TriangularBasis P s,
      ∃ B : Module.Basis (OrderedWord b.J) k (UniversalEnvelopingAlgebra k (Lie k G.val)),
        ∀ l, B l = orderedMonomial b.basis l

variable {V : Type u} [AddCommGroup V] [Module k V]

section LieModule
variable [LieRing (Lie k G.val)] [LieAlgebra k (Lie k G.val)]
variable [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V]

/-- A nonzero toral eigenvector annihilated by every positive root space. -/
def IsHighestVector (P : OppositeBorelPair G) (t : IdentityLieStructure P.torus.group)
    (lam : Weight t) (v : V) : Prop :=
  v ≠ 0 ∧ (∀ h : Lie k P.torus.group, ⁅mapPointKernel P.torus.inclusion h, v⁆ = lam h • v) ∧
    ∀ α ∈ subgroupRoots P.torus P.positive, ∀ x ∈ adjointWeightVectors P.torus α.val,
      ⁅x, v⁆ = 0

end LieModule

/-- The coaction is a rational action of the given group whose tangent action
equals the specified Lie action on the same vector space. -/
def Integrates (G : AffineAlgebraicGroup k) (V : Type u) [AddCommGroup V] [Module k V]
    [LieRing (Lie k G.val)] [LieRingModule (Lie k G.val) V] : Prop :=
  ∃ (A : HopfAlgebraCategory k) (e : specGroup A ≅ G.val) (ρ : RightComodule k A V),
    RationalHighestWeightComparison.AgreesWithCoaction e ρ

/-- Dominance on the Lie torus means natural-number evaluation on the
differential of each attached simple coroot of the specified Borel. -/
def IsDominant (P : OppositeBorelPair G) (t : IdentityLieStructure P.torus.group)
    (lam : Weight t) : Prop :=
  ∀ (α : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group)
    (h : Lie k P.torus.group), IsAttachedCoroot P.torus α.val c → IsCocharacterTangent c h →
      ∃ n : ℕ, lam h = (n : k)

/-- PBW identifies the highest line in an irreducible module and compares
two irreducible modules with the same weight over the given field. -/
def HighestWeightUniqueness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) (s : IdentityLieStructure G.val)
    (t : IdentityLieStructure P.torus.group) (_b : TriangularBasis P s),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ {V : Type u} [AddCommGroup V] [Module k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
      LieModule.IsIrreducible k (Lie k G.val) V →
      ∀ {lam : Weight t} {v : V}, IsHighestVector P t lam v →
        (∀ {mu : Weight t} {w : V}, IsHighestVector P t mu w →
          mu = lam ∧ w ∈ Submodule.span k {v}) ∧
        ∀ {W : Type u} [AddCommGroup W] [Module k W]
          [LieRingModule (Lie k G.val) W] [LieModule k (Lie k G.val) W],
          LieModule.IsIrreducible k (Lie k G.val) W →
          ((∃ w : W, IsHighestVector P t lam w) ↔ Nonempty (V ≃ₗ⁅k, Lie k G.val⁆ W))

/-- The split characteristic-zero highest weight and integration criterion,
including uniqueness of the highest weight and of the simple module for it. -/
def SplitIntegration : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    IsSemisimple G → ∀ (P : OppositeBorelPair G) (s : IdentityLieStructure G.val)
      (t : IdentityLieStructure P.torus.group),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
      LieModule.IsIrreducible k (Lie k G.val) V →
      (∃! lam : Weight t, ∃ v : V, IsHighestVector P t lam v) ∧
      ∀ lam : Weight t, (∃ v : V, IsHighestVector P t lam v) →
        IsDominant P t lam ∧
        (Integrates G V ↔ ∃ χ : Character P.torus.group,
            ∀ h, lam h = characterDifferential χ h) ∧
        ∀ (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
          [LieRingModule (Lie k G.val) W] [LieModule k (Lie k G.val) W],
          LieModule.IsIrreducible k (Lie k G.val) W →
          ((∃ w : W, IsHighestVector P t lam w) ↔ Nonempty (V ≃ₗ⁅k, Lie k G.val⁆ W))

/-- Existence of a highest vector over the split ground field. -/
def HighestWeightExistence : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    IsSemisimple G → ∀ (P : OppositeBorelPair G) (s : IdentityLieStructure G.val)
      (t : IdentityLieStructure P.torus.group),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
      LieModule.IsIrreducible k (Lie k G.val) V →
      ∃ (lam : Weight t) (v : V), IsHighestVector P t lam v

/-- Differentiation carries the rational highest line to the highest line of
the corresponding simple Lie module, and realizes the dominant characters. -/
def RationalHighestWeightComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    IsSemisimple G → ∀ (P : OppositeBorelPair G) (s : IdentityLieStructure G.val)
      (t : IdentityLieStructure P.torus.group),
    letI := s.lieRing
    letI := s.lieAlgebra
    (∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
      LieModule.IsIrreducible k (Lie k G.val) V → Integrates G V →
      ∃ (χ : Character P.torus.group) (lam : Weight t) (v : V),
        IsHighestVector P t lam v ∧ ∀ h, lam h = characterDifferential χ h) ∧
    (∀ χ : Character P.torus.group, InducedNonvanishing.Dominant P χ →
      ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
        (_ : LieRingModule (Lie k G.val) W) (_ : LieModule k (Lie k G.val) W),
        LieModule.IsIrreducible k (Lie k G.val) W ∧ Integrates G W ∧
          ∃ (lam : Weight t) (w : W),
            IsHighestVector P t lam w ∧ ∀ h, lam h = characterDifferential χ h)

end

end LinearAlgebraicGroups.Specs.SplitLieIntegration
