import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual

/-! Annihilators and Banach transposes for the shared continuous linear dual.
The bundled submodules have the precise underlying sets in Definition
`fa2:p1:c04:annihilators`. The transpose carries the native continuous linear
map structure between the duals, with their operator norm topologies. -/

namespace ExpandedFA.P1.C04Annihilators

universe u v w

/-- A^⊥: the continuous linear functionals vanishing on the arbitrary set A. -/
abbrev annihilator : Spec.AnnihilatorType.{u, v} :=
  Spec.AnnihilatorValue

/-- ⊥B: the vectors on which every continuous linear functional in B vanishes. -/
abbrev preannihilator : Spec.PreannihilatorType.{u, v} :=
  Spec.PreannihilatorValue

/-- The Banach transpose T′f = f ∘ T, linear over the original scalar field. -/
noncomputable abbrev banachTranspose : Spec.BanachTransposeType.{u, v, w} :=
  Spec.BanachTransposeValue

@[simp] theorem mem_annihilator (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : Set E) (f : C04Dual.ContinuousDual 𝕜 E) :
    f ∈ annihilator 𝕜 E A ↔ ∀ a ∈ A, f a = 0 := Iff.rfl

@[simp] theorem mem_preannihilator (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (B : Set (C04Dual.ContinuousDual 𝕜 E)) (x : E) :
    x ∈ preannihilator 𝕜 E B ↔ ∀ f ∈ B, f x = 0 := Iff.rfl

@[simp] theorem banachTranspose_apply (𝕜 : Type u) (E : Type v) (F : Type w)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : C03OperatorNorm.Operator 𝕜 E F) (f : C04Dual.ContinuousDual 𝕜 F) (x : E) :
    banachTranspose 𝕜 E F T f x = f (T x) := rfl

end ExpandedFA.P1.C04Annihilators
