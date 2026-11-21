import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.CompactActions.FiniteOrbitFields
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! Independent statements for C11, notes/003/advanced-field-theory.tex:957–1012.
The base is the literal fixed subfield, and the target carries Mathlib's
Krull topology. The isomorphism must induce exactly the given action.
No separation assumption on G or finiteness assumption is added. -/

universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory.CompactActions

/-- The given automorphisms commute with multiplication by fixed elements. -/
instance fixedBaseComm (G : Type u) (E : Type v) [Group G] [Field E]
    [MulSemiringAction G E] : SMulCommClass G (fixedBase G E) E :=
  inferInstanceAs (SMulCommClass G (FixedPoints.subfield G E) E)

/-- Compactness and open element stabilizers imply that the fixed-base
extension is algebraic, normal and separable (`IsGalois`). -/
def isGalois_compact_fixedBase_type : Prop :=
  ∀ (G : Type u) (E : Type v) [Group G] [Field E] [MulSemiringAction G E]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G],
    (∀ a : E, IsOpen (MulAction.stabilizer G a : Set G)) →
    IsGalois (fixedBase G E) E

/-- For a faithful action the action homomorphism itself is a topological
isomorphism, so in particular it is onto and its inverse is continuous. -/
def compactAction_topologicalIsomorphism_type : Prop :=
  ∀ (G : Type u) (E : Type v) [Group G] [Field E] [MulSemiringAction G E]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G],
    (∀ a : E, IsOpen (MulAction.stabilizer G a : Set G)) →
    ∀ [FaithfulSMul G E], ∃! e : G ≃ₜ* (E ≃ₐ[fixedBase G E] E),
      e.toMulEquiv.toMonoidHom = MulSemiringAction.toAlgAut G (fixedBase G E) E

end Specs.AdvancedFieldTheory.CompactActions
