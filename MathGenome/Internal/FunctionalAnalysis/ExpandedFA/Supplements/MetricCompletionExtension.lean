import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.MetricCompletionExtension

/-! Metric completion and uniformly continuous extension, including empty spaces.
The standard uniform completion carries the metric supplied by Mathlib.
For an arbitrary dense isometric completion, its abstract-completion package
provides extension; a closed inequality on the dense product preserves the
exact prescribed Lipschitz constant.
-/

universe u v w

namespace ExpandedFA.Supplements.MetricCompletionExtension

open UniformSpace

private def completionPackage {X : Type u} {H : Type v}
    [MetricSpace X] [MetricSpace H] [CompleteSpace H]
    (j : X → H) (hj : Isometry j) (hd : DenseRange j) : AbstractCompletion X where
  space := H
  coe := j
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := hj.isUniformInducing
  dense := hd

/-- The canonical completion gives the required complete dense isometric embedding. -/
theorem completion_exists :
    Specs.ExpandedFA.Supplements.MetricCompletionExtension.CompletionExists.{u} := by
  intro X _
  exact ⟨Completion X, inferInstance, inferInstance, (↑),
    Completion.coe_isometry, Completion.denseRange_coe⟩

/-- Extend a uniformly continuous map across any dense isometric completion. -/
theorem uniform_extension :
    Specs.ExpandedFA.Supplements.MetricCompletionExtension.UniformExtension.{u, v, w} := by
  intro X H _ _ _ j hj hd Y _ _ f hf
  let pkg := completionPackage j hj hd
  refine ⟨pkg.extend f, ⟨pkg.uniformContinuous_extend, ?_⟩, ?_⟩
  · exact pkg.extend_coe hf
  · intro g hg
    exact (pkg.extend_unique hf hg.1 (fun x => (hg.2 x).symm)).symm

/-- Preserve the exact real Lipschitz bound, with uniqueness among all
uniformly continuous extensions, rather than only the Lipschitz ones. -/
theorem lipschitz_extension :
    Specs.ExpandedFA.Supplements.MetricCompletionExtension.LipschitzExtension.{u, v, w} := by
  intro X H _ _ _ j hj hd Y _ _ L hL f hf
  have hfl : LipschitzWith ⟨L, hL⟩ f := LipschitzWith.of_dist_le_mul hf
  obtain ⟨g, ⟨hg, hgf⟩, huniq⟩ := uniform_extension X H j hj hd Y f hfl.uniformContinuous
  refine ⟨g, hg, hgf, ?_, fun k hk hkf => huniq k ⟨hk, hkf⟩⟩
  have hc : IsClosed {p : H × H | dist (g p.1) (g p.2) ≤ L * dist p.1 p.2} :=
    isClosed_le ((hg.continuous.comp continuous_fst).dist
      (hg.continuous.comp continuous_snd)) (continuous_const.mul continuous_dist)
  intro z t
  exact isClosed_property (hd.prodMap hd) hc
    (fun p => by simpa only [Prod.map_fst, Prod.map_snd, hgf, hj.dist_eq] using hf p.1 p.2)
    (z, t)

/-- No point is introduced when completing an empty source. -/
theorem empty_completion :
    Specs.ExpandedFA.Supplements.MetricCompletionExtension.EmptyCompletion.{u} := by
  intro X _ _
  exact ⟨fun z => by
    have hn : Nonempty X :=
      (Completion.nonempty_completion_iff X).mp ⟨z⟩
    exact not_nonempty_iff.mpr (inferInstance : IsEmpty X) hn⟩

end ExpandedFA.Supplements.MetricCompletionExtension
