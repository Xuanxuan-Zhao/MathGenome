import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.LieStableSubspaces
import Mathlib.Algebra.Lie.Semisimple.Defs

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.RationalHighestWeightComparison

open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open CharacterPairing (adjointWeightVectors characterValue)
open FlagLineBundle (OppositeBorelPair)
open GeometricRadicals (IsSemisimple)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {V : Type u} [AddCommGroup V] [Module k V]

/-- The given Lie action is the differential of the right coaction in the
specified Hopf presentation of the group. -/
def AgreesWithCoaction [LieRing (Lie k G.val)] [LieRingModule (Lie k G.val) V]
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (δ : RightComodule k A V) : Prop :=
  ∀ (x : Lie k G.val) (v : V),
    differentiatedCoaction A δ (tangentPointOfLie A (mapPointKernel e.inv x)) v = ⁅x, v⁆

/-- A highest vector with toral eigenvalues given by the differential of the
actual character of the marked split torus. -/
def IsHighestVector [LieRing (Lie k G.val)] [LieRingModule (Lie k G.val) V]
    (P : OppositeBorelPair G) (χ : Character P.torus.group) (v : V) : Prop :=
  v ≠ 0 ∧
    (∀ h : Lie k P.torus.group, ⁅mapPointKernel P.torus.inclusion h, v⁆ =
      (characterValue χ (CommAlgCat.of k (DualNumber k)) h.toMul.val).snd • v) ∧
    ∀ α ∈ subgroupRoots P.torus P.positive,
      ∀ x ∈ adjointWeightVectors P.torus α.val, ⁅x, v⁆ = 0

/-- An irreducible Lie action arising by differentiation has a highest vector
of an actual torus character. Each dominant character is realized by the
differential of a finite-dimensional rational module with irreducible Lie action. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k), IsSemisimple G →
    ∀ (P : OppositeBorelPair G) (s : IdentityLieStructure G.val),
      letI := s.lieRing
      letI := s.lieAlgebra
      (∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
        [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
        LieModule.IsIrreducible k (Lie k G.val) V →
        ∀ (A : HopfAlgebraCategory k) (e : specGroup A ≅ G.val) (δ : RightComodule k A V),
          AgreesWithCoaction e δ → ∃ (χ : Character P.torus.group) (v : V), IsHighestVector P χ v) ∧
      (∀ χ : Character P.torus.group, InducedNonvanishing.Dominant P χ →
        ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
          (_ : LieRingModule (Lie k G.val) V) (_ : LieModule k (Lie k G.val) V),
          LieModule.IsIrreducible k (Lie k G.val) V ∧
            ∃ (A : HopfAlgebraCategory k) (e : specGroup A ≅ G.val) (δ : RightComodule k A V),
              AgreesWithCoaction e δ ∧ ∃ v : V, IsHighestVector P χ v)

end LinearAlgebraicGroups.Specs.RationalHighestWeightComparison
