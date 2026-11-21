import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.GelfandTransform

/-! The Gelfand transform for general commutative unital complex Banach algebras. -/
noncomputable section

namespace ExpandedFA.BanachAlgebra.GelfandTransform

open Specs.ExpandedFA.BanachAlgebra.GelfandTransform
open Specs.ExpandedFA.BanachAlgebra.Characters
open Specs.ExpandedFA.BanachAlgebra.Conventions

universe u

local instance characterTop (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A] :
    TopologicalSpace (Character ℂ A) := CharacterTopologyValue A

local instance characterCompact (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A] : CompactSpace (Character ℂ A) :=
  (Characters.compact_hausdorff A).1

/-- Evaluation is continuous in Δ and preserves the scalar algebra operations. -/
abbrev gelfandTransform : TransformType.{u} := TransformValue

theorem gelfandTransform_apply : Evaluation.{u} := by
  intro A _ _ _ _ _ a χ
  rfl

theorem norm_contractive : NormContractive.{u} := by
  intro A _ _ _ _ _ a
  apply (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
  intro χ
  exact (Characters.automatic_boundedness A χ).choose_spec.2.2 a

theorem lipschitz : Lipschitz.{u} := by
  intro A _ _ _ _ _
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
  exact norm_contractive A (a - b)

theorem norm_eq_spectralRadius : NormSpectralRadius.{u} := by
  intro A _ _ _ _ _ a
  rw [ContinuousMap.norm_eq_iSup_norm]
  change sSup (Set.range (fun χ : Character ℂ A => ‖χ.val a‖)) =
    sSup ((fun z : ℂ => ‖z‖) '' AlgebraSpectrumValue ℂ A a)
  rw [Characters.spectrum_characters A a, ← Set.range_comp']

theorem kernel_eq_intersection : KernelIntersection.{u} := by
  intro A _ _ _ _ _
  ext a
  simp only [RingHom.mem_ker, Ideal.mem_iInf]
  constructor
  · intro ha I
    obtain ⟨e, χ, _, hχ⟩ := Characters.maximal_quotient A I.val I.property
    apply (hχ a).mp
    exact congrArg (fun f : C(Character ℂ A, ℂ) => f χ) ha
  · intro ha
    apply ContinuousMap.ext
    intro χ
    obtain ⟨I, hI, e, _, hχ⟩ := Characters.character_quotient A χ
    exact (hχ a).mpr (ha ⟨I, hI⟩)

end ExpandedFA.BanachAlgebra.GelfandTransform
