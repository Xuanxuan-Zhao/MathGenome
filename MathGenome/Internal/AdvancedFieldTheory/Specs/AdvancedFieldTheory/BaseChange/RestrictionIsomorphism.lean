import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.BaseChange.GaloisExtensions
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! C10, lines 903–954: literal intersection and compositum in a common
 overfield, with their inclusion algebra maps and intrinsic Krull topologies. -/
universe u v
namespace Specs.AdvancedFieldTheory

def baseChange_restriction_topologicalIsomorphism_type : Prop :=
  ∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (E M : IntermediateField K Ω) [IsGalois K E],
    letI : Algebra M (E ⊔ M : IntermediateField K Ω) :=
      (IntermediateField.inclusion le_sup_right).toAlgebra
    letI : Algebra (E ⊓ M : IntermediateField K Ω) E :=
      (IntermediateField.inclusion inf_le_left).toAlgebra
    IsGalois M (E ⊔ M : IntermediateField K Ω) ∧
    IsGalois (E ⊓ M : IntermediateField K Ω) E ∧
    ∃! e : ((E ⊔ M : IntermediateField K Ω) ≃ₐ[M]
        (E ⊔ M : IntermediateField K Ω)) ≃ₜ*
        (E ≃ₐ[(E ⊓ M : IntermediateField K Ω)] E),
      ∀ g x, ((e g x : E) : Ω) =
        (g ⟨(x : Ω), (le_sup_left : E ≤ E ⊔ M) x.property⟩ : Ω)

end Specs.AdvancedFieldTheory
