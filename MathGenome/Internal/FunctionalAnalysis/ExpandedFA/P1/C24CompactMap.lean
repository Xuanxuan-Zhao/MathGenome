import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24CompactMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24Schauder
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-! Compact-map fixed points, paper.tex:5114–5143.

Finite convex approximation of the compact image closure gives arbitrarily
accurate approximate fixed points in D. A convergent subsequence of their
images transfers its limit to the approximate fixed points. Closedness and
continuity give an actual fixed point. This works without completeness.
-/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1.C24CompactMap

universe u

/-- Approximate fixed points using finite polytopes in the domain. -/
theorem compactImage_approximateFixedPoint
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hne : D.Nonempty) (hclosed : IsClosed D) (hconvex : Convex ℝ D)
    (T : D → D) (hT : Continuous T)
    (hcompact : IsCompact (closure (range (fun x : D => (T x : E)))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : D, ‖(T x : E) - (x : E)‖ < ε := by
  let Q := closure (range (fun x : D => (T x : E)))
  have hQD : Q ⊆ D := closure_minimal (by
    rintro _ ⟨x, rfl⟩
    exact (T x).property) hclosed
  have hQne : Q.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨T ⟨x, hx⟩, subset_closure (mem_range_self _)⟩
  obtain ⟨s, hs, hsne, hsQ, P, hP, herr⟩ :=
    C24FiniteApproximation.finiteConvexApproximation E Q hQne hcompact ε hε
  have hsD : convexHull ℝ s ⊆ D := convexHull_min (hsQ.trans hQD) hconvex
  let i : convexHull ℝ s → D := fun x => ⟨x.val, hsD x.property⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  let TQ : D → Q := fun x => ⟨T x, subset_closure (mem_range_self x)⟩
  have hTQ : Continuous TQ := (continuous_subtype_val.comp hT).subtype_mk _
  obtain ⟨x, hx⟩ := C24Schauder.finitePolytope_fixedPoint s hs hsne (P ∘ TQ ∘ i)
    (hP.comp (hTQ.comp hi))
  refine ⟨i x, ?_⟩
  have he := herr (TQ (i x))
  have hval : (P (TQ (i x)) : E) = (i x : E) := congrArg Subtype.val hx
  rw [hval, norm_sub_rev] at he
  exact he

/-- The real normed-space assertion, retaining compactness in E itself. -/
theorem realNormedCompactMap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hne : D.Nonempty) (hclosed : IsClosed D) (hconvex : Convex ℝ D)
    (T : D → D) (hT : Continuous T)
    (hcompact : IsCompact (closure (range (fun x : D => (T x : E))))) :
    ∃ x : D, T x = x := by
  choose x hx using (fun n : ℕ => compactImage_approximateFixedPoint
    D hne hclosed hconvex T hT hcompact (1 / ((n : ℝ) + 1)) (by positivity))
  have hr : Tendsto (fun n => ‖(T (x n) : E) - (x n : E)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => (hx n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨a, _ha, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self (x n)))
  have hdist : Tendsto (fun n => dist (T (x (φ n)) : E) (x (φ n) : E)) atTop (𝓝 0) := by
    simpa only [dist_eq_norm, Function.comp_def] using hr.comp hφ.tendsto_atTop
  have hxlim : Tendsto (fun n => (x (φ n) : E)) atTop (𝓝 a) := hlim.congr_dist hdist
  have haD : a ∈ D := hclosed.mem_of_tendsto hxlim
    (Eventually.of_forall fun n => (x (φ n)).property)
  have hxD : Tendsto (fun n => x (φ n)) atTop (𝓝 (⟨a, haD⟩ : D)) :=
    tendsto_subtype_rng.mpr hxlim
  have hTlim : Tendsto (fun n => (T (x (φ n)) : E)) atTop (𝓝 (T ⟨a, haD⟩ : E)) :=
    (continuous_subtype_val.comp hT).tendsto _ |>.comp hxD
  exact ⟨⟨a, haD⟩, Subtype.ext (tendsto_nhds_unique hTlim hlim)⟩

/-- Real and complex normed spaces, with real convexity. -/
theorem normedCompactMap : Spec.NormedCompactMap.{u} := by
  intro 𝕜 E _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  exact realNormedCompactMap

/-- The Banach assertion is a specialization of the normed-space theorem. -/
theorem banachCompactMap : Spec.BanachCompactMap.{u} := by
  intro 𝕜 E _ _ _ _
  exact normedCompactMap 𝕜 E

/-- A bounded domain lets the compact-map hypothesis apply to the full image. -/
theorem normedCompactSelfMap : Spec.NormedCompactSelfMap.{u} := by
  intro 𝕜 E _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro D hne hclosed hbounded hconvex T hT hcompact
  apply normedCompactMap 𝕜 E D hne hclosed hconvex T hT
  have hbound : Bornology.IsBounded (Subtype.val '' (univ : Set D) : Set E) := by
    simpa using hbounded
  simpa only [image_univ] using hcompact univ hbound

/-- The manuscript's bounded-domain Banach corollary. -/
theorem banachCompactSelfMap : Spec.BanachCompactSelfMap.{u} := by
  intro 𝕜 E _ _ _ _
  exact normedCompactSelfMap 𝕜 E

end ExpandedFA.P1.C24CompactMap
