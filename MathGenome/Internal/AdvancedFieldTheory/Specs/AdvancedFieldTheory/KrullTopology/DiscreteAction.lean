import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.InitialDescriptions
import Mathlib.Topology.ContinuousOn

/-! Independent specification of FT-T03B.
Source: notes/003/advanced-field-theory.tex:433–441, 451–458.
The automorphism group carries the Krull topology. The explicitly chosen
bottom topology on L is discrete, both in the product and in the codomain.
The second assertion quantifies over arbitrary spaces and arbitrary set maps.
-/

universe u v w
noncomputable section
set_option linter.checkUnivs false

namespace Specs.AdvancedFieldTheory.KrullTopology

def continuous_action_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    letI : TopologicalSpace L := ⊥
    Continuous (fun p : (L ≃ₐ[K] L) × L => p.1 p.2)

def continuous_of_continuous_action_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Type w} [TopologicalSpace X] (u : X → (L ≃ₐ[K] L)),
    letI : TopologicalSpace L := ⊥
    Continuous (fun p : X × L => u p.1 p.2) → Continuous u

end Specs.AdvancedFieldTheory.KrullTopology
