import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.InverseLimit.Gluing
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.InitialDescriptions
import Mathlib.Topology.Homeomorph.Lemmas

/-!
Independent specification of FT-T06, notes/003/advanced-field-theory.tex:543–574.
The source group has its Krull topology and the compatible tuples have the
subspace topology from the product of the discrete finite stage groups.
The isomorphism is required to be the canonical restriction map, including
its projection formulas. Compact, Hausdorff, totally disconnected topological
groups are profinite; these properties are exposed as the standard classes.
-/

universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory

/-- The canonical algebraic isomorphism is an isomorphism of topological groups. -/
def canonicalRestriction_topologicalIsomorphism_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    ∃! e : (L ≃ₐ[K] L) ≃ₜ* compatibleTuples_value K L,
      e.toMulEquiv.toMonoidHom = canonicalRestriction_value K L ∧
      ∀ (E : finiteGaloisStage_value K L) (σ : L ≃ₐ[K] L),
        compatibleTupleProjection_value E (e σ) = restriction_value E.val σ

def galoisGroup_compactSpace_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    CompactSpace (L ≃ₐ[K] L)

def galoisGroup_t2Space_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    T2Space (L ≃ₐ[K] L)

def galoisGroup_totallyDisconnectedSpace_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    TotallyDisconnectedSpace (L ≃ₐ[K] L)

end Specs.AdvancedFieldTheory
