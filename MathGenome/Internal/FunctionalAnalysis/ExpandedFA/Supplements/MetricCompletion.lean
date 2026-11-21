import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.MetricCompletion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.MetricCompletionExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02Completion

/-!
Metric uniqueness and the comparison with the linear completion.
Extend the two dense embeddings in opposite directions. Density makes the
composites identities. Distance equality is closed on the product, so the
forward extension is an isometry. This works without choosing any point of X,
and hence also for the empty space.
-/

universe u v w z

namespace ExpandedFA.Supplements.MetricCompletion

/-- Any two complete dense isometric embeddings have a unique surjective
isometry intertwining them. -/
theorem completion_uniqueness :
    Specs.ExpandedFA.Supplements.MetricCompletion.Uniqueness.{u, v, w} := by
  intro X H G _ _ _ _ _ i j hi hdi hj hdj
  obtain ⟨f, ⟨hf, hfi⟩, _⟩ :=
    MetricCompletionExtension.uniform_extension X H i hi hdi G j hj.uniformContinuous
  obtain ⟨g, ⟨hg, hgj⟩, _⟩ :=
    MetricCompletionExtension.uniform_extension X G j hj hdj H i hi.uniformContinuous
  have hgf : g ∘ f = id :=
    hdi.equalizer (hg.comp hf).continuous continuous_id
      (funext fun x => by simp only [Function.comp_apply, hfi, hgj, id_eq])
  have hfg : f ∘ g = id :=
    hdj.equalizer (hf.comp hg).continuous continuous_id
      (funext fun x => by simp only [Function.comp_apply, hgj, hfi, id_eq])
  have hiso : Isometry f := by
    apply Isometry.of_dist_eq
    intro a b
    have hc : IsClosed {p : H × H | dist (f p.1) (f p.2) = dist p.1 p.2} :=
      isClosed_eq ((hf.continuous.comp continuous_fst).dist
        (hf.continuous.comp continuous_snd)) continuous_dist
    exact isClosed_property (hdi.prodMap hdi) hc
      (fun p => by simpa only [Prod.map_fst, Prod.map_snd, hfi, hi.dist_eq]
        using hj.dist_eq p.1 p.2) (a, b)
  let U : H ≃ᵢ G :=
    { toFun := f
      invFun := g
      left_inv := congrFun hgf
      right_inv := congrFun hfg
      isometry_toFun := hiso }
  refine ⟨U, hfi, ?_⟩
  intro V hV
  apply IsometryEquiv.ext
  exact congrFun (hdi.equalizer V.continuous U.continuous
    (funext fun x => (hV x).trans (hfi x).symm))

/-- Existence and extension from the accepted prerequisite, together with
uniqueness, establish the entire metric completion theorem. -/
theorem metric_completion :
    Specs.ExpandedFA.Supplements.MetricCompletion.MetricCompletionTheorem.{u, v, w, z} :=
  ⟨MetricCompletionExtension.completion_exists, completion_uniqueness,
    MetricCompletionExtension.uniform_extension,
    MetricCompletionExtension.lipschitz_extension⟩

/-- The linear completion, with its actual norm and dense linear embedding,
is the metric completion relative to every other dense isometric embedding. -/
theorem linear_completion_identification :
    Specs.ExpandedFA.Supplements.MetricCompletion.LinearCompletionIdentification.{u, v, w} := by
  intro 𝕜 E _ _ _
  let i := P1.C02Completion.completionEmbedding 𝕜 E
  have hi : Isometry i := i.isometry
  have hd : DenseRange i := (P1.C02Completion.completion_embedding_properties 𝕜 E).1
  refine ⟨(P1.C02Completion.completion_banach 𝕜 E).1, hi, hd, ?_⟩
  intro H _ _ j hj hdj
  exact completion_uniqueness E (UniformSpace.Completion E) H i j hi hd hj hdj

end ExpandedFA.Supplements.MetricCompletion
