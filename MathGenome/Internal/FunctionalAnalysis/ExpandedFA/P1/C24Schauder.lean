import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Schauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24FiniteApproximation
import MathGenome.PointSetTopology.Topics.D10Topology.Ch17
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact

/-! Schauder fixed points, paper.tex lines 5070–5091.

Brouwer is applied in the finite real span with the inherited norm. Compactness
of the residual range then turns approximate fixed points into an exact fixed
point. Ambient completeness and positive dimension are never assumed. -/

open Set

namespace ExpandedFA.P1.C24Schauder

universe u

/-- Brouwer on the finite real span of the vertices of a polytope, with the
inherited norm. The ambient normed space need not be complete. -/
theorem finitePolytope_fixedPoint
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (hs : s.Finite) (hne : s.Nonempty)
    (f : convexHull ℝ s → convexHull ℝ s) (hf : Continuous f) :
    ∃ x, f x = x := by
  let V := Submodule.span ℝ s
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ hs
  have hspan : convexHull ℝ s ⊆ V :=
    convexHull_min (Submodule.subset_span) V.convex
  let K : Set V := Subtype.val ⁻¹' convexHull ℝ s
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, Submodule.subset_span hx⟩, subset_convexHull ℝ s hx⟩
  have hKcompact : IsCompact K := by
    apply Topology.IsInducing.isCompact_preimage' Topology.IsEmbedding.subtypeVal.isInducing
      (hs.isCompact_convexHull ℝ)
    intro x hx
    exact ⟨⟨x, hspan hx⟩, rfl⟩
  have hKconvex : Convex ℝ K :=
    (convex_convexHull ℝ s).linear_preimage V.subtype
  let e : K ≃ₜ convexHull ℝ s :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, hspan x.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  obtain ⟨x, hx⟩ := D10Topology.Ch17.brouwer_finiteDimensional V K hKne
    hKcompact hKconvex (e.symm ∘ f ∘ e)
    (e.symm.continuous.comp (hf.comp e.continuous))
  exact ⟨e x, by simpa using congrArg e hx⟩

/-- Every positive error admits an approximate fixed point. -/
theorem schauder_approximateFixedPoint
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hne : C.Nonempty) (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) (T : C → C) (hT : Continuous T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : C, ‖(T x : E) - (x : E)‖ < ε := by
  obtain ⟨s, hs, hsne, hsC, P, hP, herr⟩ :=
    C24FiniteApproximation.finiteConvexApproximation E C hne hcompact ε hε
  have hDC : convexHull ℝ s ⊆ C := convexHull_min hsC hconvex
  let i : convexHull ℝ s → C := fun x => ⟨x.val, hDC x.property⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  obtain ⟨x, hx⟩ := finitePolytope_fixedPoint s hs hsne (P ∘ T ∘ i)
    (hP.comp (hT.comp hi))
  refine ⟨i x, ?_⟩
  have he := herr (T (i x))
  have hval : (P (T (i x)) : E) = (i x : E) := congrArg Subtype.val hx
  rw [hval, norm_sub_rev] at he
  exact he

/-- Schauder on a compact convex set. The continuous residual attains its
minimum; arbitrarily accurate approximate fixed points force that minimum to
be zero. This compactness argument requires no ambient completeness. -/
theorem schauder : Spec.Schauder.{u} := by
  intro E _ _ C hne hcompact hconvex T hT
  have : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  have : Nonempty C := hne.to_subtype
  have hr : Continuous (fun x : C => ‖(T x : E) - (x : E)‖) :=
    ((continuous_subtype_val.comp hT).sub continuous_subtype_val).norm
  obtain ⟨x, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hr.continuousOn
  refine ⟨x, Subtype.ext ?_⟩
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  by_contra hn
  have hpos : 0 < ‖(T x : E) - (x : E)‖ := lt_of_not_ge hn
  obtain ⟨y, hy⟩ := schauder_approximateFixedPoint C hne hcompact hconvex T hT _ hpos
  exact (not_lt_of_ge (hmin (Set.mem_univ y))) hy

/-- Complex Schauder uses the same norm topology and real convexity. -/
theorem schauderComplex : Spec.SchauderComplex.{u} := by
  intro E _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  exact schauder E

end ExpandedFA.P1.C24Schauder
