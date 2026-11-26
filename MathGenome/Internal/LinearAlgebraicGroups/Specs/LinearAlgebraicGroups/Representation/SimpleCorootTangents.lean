import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RootWeightAction
import Mathlib.LinearAlgebra.TensorProduct.Tower

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.SimpleCorootTangents

open CharacterDescent (Cocharacter)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open Pinning (AttachedDatum SplitBorelPair)
open RootWeightAction (SimpleRoot)
open SimplyConnectedLattice (corootLattice)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

noncomputable section

variable {k : Type u} [Field k]

/-- The unit of the dual numbers with coordinates `(1, 1)`. -/
def infinitesimalUnit (k : Type u) [Field k] : (DualNumber k)ˣ :=
  (IsNilpotent.isUnit_one_add
    (show IsNilpotent (DualNumber.eps : DualNumber k) from ⟨2, by simp [pow_two]⟩)).unit

/-- The cocharacter differential is evaluated at `1 + ε`. -/
def IsCocharacterTangent {T : GroupScheme k} (c : Cocharacter T) (h : Lie k T) : Prop :=
  h.toMul.val = cocharacterPoint c (CommAlgCat.of k (DualNumber k)) (infinitesimalUnit k)

/-- Scalar extension of the actual integral cocharacter lattice, with its
value fixed on each pure tensor by differentiation. -/
def ScalarExtension : Prop :=
  ∀ {k : Type u} [Field k] (T : GroupScheme k) [IsCommMonObj T.X],
    IsSplitTorus T → ∀ t : IdentityLieStructure T,
      letI := t.lieRing
      letI := t.lieAlgebra
      ∃ e : (k ⊗[ℤ] Additive (Cocharacter T)) ≃ₗ[k] Lie k T,
        ∀ c : Cocharacter T, IsCocharacterTangent c (e (1 ⊗ₜ[ℤ] Additive.ofMul c))

/-- For the marked positive Borel, its simple coroots generate the actual coroot
lattice integrally and their differentials form a basis of the toral Lie algebra. -/
def BasisAndLattice : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (P : SplitBorelPair k),
    IsSemisimple P.G → ∀ (D : AttachedDatum P) (t : IdentityLieStructure P.T.group),
      letI := D.comm
      letI := t.lieRing
      letI := t.lieAlgebra
      Submodule.span ℤ (Set.range fun α : SimpleRoot P.T P.B ↦ D.datum.rootDatum.coroot α.val) =
        corootLattice D ∧
      ∃ b : Module.Basis (SimpleRoot P.T P.B) k (Lie k P.T.group),
        ∀ α, IsCocharacterTangent (Additive.toMul (D.datum.rootDatum.coroot α.val)) (b α)

/-- The toral Lie algebra is abelian and its original inclusion induces an
injective Lie morphism for the given identity Lie structures. -/
def LieEmbedding : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val), IsSplitTorus T.group →
    ∀ (t : IdentityLieStructure T.group) (s : IdentityLieStructure G.val),
      letI := t.lieRing
      letI := t.lieAlgebra
      letI := s.lieRing
      letI := s.lieAlgebra
      (∀ x y : Lie k T.group, ⁅x, y⁆ = 0) ∧
      ∃ f : Lie k T.group →ₗ⁅k⁆ Lie k G.val,
        Function.Injective f ∧ ∀ x, f x = mapPointKernel T.inclusion x

end

end LinearAlgebraicGroups.Specs.SimpleCorootTangents
