import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RestrictedSimplicity
import Mathlib.RingTheory.RingHom.FaithfullyFlat

open CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.SteinbergTensorStep

open LinearAlgebraicGroups.RationalRepresentations
open LinearAlgebraicGroups.FiniteDistributions (twistCoordinates FrobeniusFormula)
open FlagLineBundle (OppositeBorelPair)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open RootWeightAction (SimpleRoot Representation)
open InducedNonvanishing (Dominant)
open AbstractPairing (IsAttachedCoroot)
open SimpleClassification (SocleModel Realizes HasHighestWeight)

noncomputable section

/-- Simplicity on the coordinate-comodule side, including nonvanishing. -/
def SimpleCoaction {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    {A : HopfAlgebraCategory k} (ρ : RightComodule k A V) : Prop :=
  (⊤ : Submodule k V) ≠ ⊥ ∧
    ∀ N : Submodule k V, ρ.IsSubcomodule N → N = ⊥ ∨ N = ⊤

/-- The split-model Frobenius twist in a basis. Its matrix entries are the
pullbacks, by relative Frobenius, of the entries in the scalar-twisted basis. -/
def IsFirstTwist {k V I : Type u} [Field k] [AddCommGroup V] [Module k V]
    [Fintype I] (p : ℕ) (A : HopfAlgebraCategory k)
    (b : Module.Basis I k V) (ρ σ : RightComodule k A V) : Prop :=
  ∀ i j, coefficients A b σ i j = (coefficients A b ρ i j) ^ p

/-- Frobenius on a reduced finite-type affine group over an algebraically
closed field is finite faithfully flat. The coordinate criterion is
equivalent to finite faithful flatness of the scheme morphism. -/
def FrobeniusFiniteFaithfullyFlat : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] [IsReduced A]
    (F : twistCoordinates k p 1 A ⟶ A), FrobeniusFormula k p 1 A F →
    F.hom.toAlgHom.toRingHom.Finite ∧ F.hom.toAlgHom.toRingHom.FaithfullyFlat

/-- The matrix description is the pullback of the scalar twist along the
relative Frobenius. This pullback is trivial on the scheme kernel. -/
def RelativeTwist : Prop :=
  ∀ {k V I : Type u} [Field k] [AddCommGroup V] [Module k V]
    [Fintype I] [DecidableEq I] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k) (F : twistCoordinates k p 1 A ⟶ A),
    FrobeniusFormula k p 1 A F →
    ∀ (b : Module.Basis I k V) (ρ σ : RightComodule k A V),
      IsFirstTwist p A b ρ σ →
      ∃ δ : RightComodule k (twistCoordinates k p 1 A) V,
        (∀ i j, coefficients (twistCoordinates k p 1 A) b δ i j =
          RelativeFrobenius.scalarTensor (iterateFrobenius k p 1) A 1
            (coefficients A b ρ i j)) ∧
        σ.coaction = F.hom.toAlgHom.toLinearMap.lTensor V ∘ₗ δ.coaction ∧
        ∀ h : (kernelIdeal F).IsHopfIdeal k,
          letI := h
          let Q := hopfQuotient A (kernelIdeal F)
          let q := hopfQuotientMap A (kernelIdeal F)
          ∀ v : V, q.hom.toAlgHom.toLinearMap.lTensor V (σ.coaction v) =
            v ⊗ₜ[k] (1 : Q)

/-- The tensor step with the simple modules realized as the socles of the
opposite-Borel induced modules. The right factor uses the Frobenius-twisted
matrices in the basis of that socle. -/
def OneStep : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k), IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (P : OppositeBorelPair G) (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
      ∀ (η μ : Character P.torus.group), Dominant P η → Dominant P μ →
        (∀ (α : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group),
          IsAttachedCoroot P.torus α.val c → pairing P.torus.group η c < (p : ℤ)) →
        ∀ (S : SocleModel P U η) (M : SocleModel P U μ),
          ∃ (a : M.A ⟶ S.A) (ρ σ : RightComodule k S.A M.socle)
            (τ : RightComodule k S.A (S.socle ⊗[k] M.socle))
            (r : Representation G.val (S.J × M.J)),
            specGroupMap a ≫ M.groupIso.hom = S.groupIso.hom ∧
            ρ.coaction = a.hom.toAlgHom.toLinearMap.lTensor M.socle ∘ₗ M.socleCoaction.coaction ∧
            (∃ F : twistCoordinates k p 1 S.A ⟶ S.A,
              FrobeniusFormula k p 1 S.A F ∧
              F.hom.toAlgHom.toRingHom.Finite ∧ F.hom.toAlgHom.toRingHom.FaithfullyFlat) ∧
            IsFirstTwist p S.A M.socleBasis ρ σ ∧
            τ.coaction = tensorCoactionMap S.A S.socleCoaction σ ∧
            Realizes S.groupIso (S.socleBasis.tensorProduct M.socleBasis) τ r ∧
            PrimitiveLine.IsSimple r ∧ HasHighestWeight P U r (η * μ ^ p) ∧
            ∃ L : SocleModel P U (η * μ ^ p),
              Nonempty { f : ((S.J × M.J) → k) ≃ₗ[k] (L.J → k) //
                PrimitiveLine.IsEquivariant r L.socleAction f.toLinearMap }

end
end LinearAlgebraicGroups.Specs.SteinbergTensorStep
