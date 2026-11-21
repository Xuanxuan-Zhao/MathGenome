import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ConvergingTogether
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ContinuousMapping
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.VaryingMapping
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Slutsky

/-! Slutsky's theorem (paper.tex 1680–1697).
The product uses the maximum metric. Thus the distance from `(Xs, Ys)` to
`(Xs, c)` is exactly `dist Ys c`. No independence is needed.
-/
open MeasureTheory Filter Topology

namespace ProbabilityFoundations.Ch06
universe u v w z t
noncomputable section

/-- Composition of a random element corresponds to mapping its probability law. -/
lemma probabilityLaw_comp {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (hX : Measurable X)
    (g : S → T) (hg : Measurable g) :
    probabilityLaw P (g ∘ X) (hg.comp hX) = (probabilityLaw P X hX).map g := by
  apply Subtype.ext
  exact (Measure.map_map hg hX).symm

/-- Slutsky's joint limit; this includes finite-dimensional real vectors. -/
theorem slutsky_joint :
    Specs.ProbabilityFoundations.Ch06.Slutsky.jointType.{u,v,w,z} := by
  intro S T _ _ _ _ _ _ _ _ Ω Ωs _ _ Ps _ Xs Ys hXs hYs P _ X hX c hlim hprob
  have hemb : Continuous (fun x : S => (x, c)) := continuous_id.prodMk continuous_const
  have hc := convergesInLaw_continuous atTop Ps Xs hXs P X hX _ hemb hlim
  apply weak_limit_of_perturbation Ps
    (fun n ω => (Xs n ω, Ys n ω)) (fun n ω => (Xs n ω, c))
    (fun n => (hXs n).prodMk (hYs n))
    (fun n => (hXs n).prodMk measurable_const)
    (probabilityLaw P (fun ω => (X ω, c)) (hX.prodMk measurable_const))
  · intro n
    exact ((hXs n).prodMk (hYs n)).dist ((hXs n).prodMk measurable_const)
  · exact hc
  · intro ε hε
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hprob ε hε

/-- Joint convergence for real vectors of dimensions d and e, including zero. -/
theorem slutsky_vectors : Specs.ProbabilityFoundations.Ch06.Slutsky.vectorsType.{w,z} := by
  intro d e Ω Ωs _ _ Ps _ Xs Ys hXs hYs P _ X hX c hlim hprob
  exact slutsky_joint Ps Xs Ys hXs hYs P X hX c hlim hprob

/-- Every continuous function of the pair preserves Slutsky's limit. -/
theorem slutsky_continuous :
    Specs.ProbabilityFoundations.Ch06.Slutsky.continuousType.{u,v,w,z,t} := by
  intro S T _ _ _ _ _ _ _ _ Ω Ωs _ _ Ps _ Xs Ys hXs hYs P _ X hX c hlim hprob
    U _ _ _ g hg
  exact convergesInLaw_continuous atTop Ps (fun n ω => (Xs n ω, Ys n ω))
    (fun n => (hXs n).prodMk (hYs n)) P (fun ω => (X ω, c))
    (hX.prodMk measurable_const) g hg
    (slutsky_joint Ps Xs Ys hXs hYs P X hX c hlim hprob)

/-- A Borel map need only be continuous at points whose second coordinate is c. -/
theorem slutsky_continuousAt_slice :
    Specs.ProbabilityFoundations.Ch06.Slutsky.continuousAtSliceType.{u,v,w,z,t} := by
  intro S T _ _ _ _ _ _ _ _ Ω Ωs _ _ Ps _ Xs Ys hXs hYs P _ X hX c hlim hprob
    U _ _ _ g hg hcont
  have hj := slutsky_joint Ps Xs Ys hXs hYs P X hX c hlim hprob
  have hc : ∀ᵐ p ∂(probabilityLaw P (fun ω => (X ω, c))
      (hX.prodMk measurable_const) : Measure (S × T)), ContinuousAt g p := by
    rw [probabilityLaw_toMeasure]
    exact (ae_map_iff (hX.prodMk measurable_const).aemeasurable
      (measurableSet_of_continuousAt g)).mpr
        (Eventually.of_forall (fun ω => hcont (X ω)))
  have hm := almostEverywhere_continuous_mapping
    (fun n => probabilityLaw (Ps n) (fun ω => (Xs n ω, Ys n ω))
      ((hXs n).prodMk (hYs n)))
    (probabilityLaw P (fun ω => (X ω, c)) (hX.prodMk measurable_const))
    g hg hj hc
  have heq (n : ℕ) := probabilityLaw_comp (Ps n)
    (fun ω => (Xs n ω, Ys n ω)) ((hXs n).prodMk (hYs n)) g hg
  have heq' := probabilityLaw_comp P (fun ω => (X ω, c))
    (hX.prodMk measurable_const) g hg
  simp_rw [← heq, ← heq'] at hm
  exact hm

/-- The scalar sum specialization. -/
theorem slutsky_sum : Specs.ProbabilityFoundations.Ch06.Slutsky.sumType.{w,z} := by
  intro Ω Ωs _ _ Ps _ Xs Ys hXs hYs P _ X hX c hlim hprob
  exact slutsky_continuous Ps Xs Ys hXs hYs P X hX c hlim hprob
    (fun p : ℝ × ℝ => p.1 + p.2) (continuous_fst.add continuous_snd)

/-- The scalar product specialization. -/
theorem slutsky_product : Specs.ProbabilityFoundations.Ch06.Slutsky.productType.{w,z} := by
  intro Ω Ωs _ _ Ps _ Xs Ys hXs hYs P _ X hX c hlim hprob
  exact slutsky_continuous Ps Xs Ys hXs hYs P X hX c hlim hprob
    (fun p : ℝ × ℝ => p.1 * p.2) (continuous_fst.mul continuous_snd)

/-- The quotient specialization, with an arbitrary Borel value on the zero slice. -/
theorem slutsky_quotient : Specs.ProbabilityFoundations.Ch06.Slutsky.quotientType.{w,z} := by
  intro Ω Ωs _ _ Ps _ Xs Ys hXs hYs P _ X hX c hlim hprob hc a ha
  let q : ℝ × ℝ → ℝ := fun p => if p.2 = 0 then a p.1 else p.1 / p.2
  have hq : Measurable q :=
    Measurable.ite (measurable_snd (measurableSet_singleton 0))
      (ha.comp measurable_fst) (measurable_fst.div measurable_snd)
  have hqc (x : ℝ) : ContinuousAt q (x, c) := by
    have heq : q =ᶠ[𝓝 (x, c)] (fun p : ℝ × ℝ => p.1 / p.2) := by
      filter_upwards [continuousAt_snd.eventually_ne hc] with p hp
      simp only [q, ite_eq_right hp]
    apply ContinuousAt.congr_of_eventuallyEq ?_ heq
    exact continuousAt_fst.div continuousAt_snd hc
  have hm := slutsky_continuousAt_slice Ps Xs Ys hXs hYs P X hX c hlim hprob q hq hqc
  refine ⟨fun n => hq.comp ((hXs n).prodMk (hYs n)), hX.div_const c, ?_⟩
  simpa only [q, ite_eq_right hc] using hm

end
end ProbabilityFoundations.Ch06
