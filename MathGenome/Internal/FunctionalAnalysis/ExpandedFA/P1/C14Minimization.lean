import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14Minimization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14BallCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12NormLsc
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure

/-!
The direct compactness argument for fa2:p1:c14:minimization. A proper value
selects a nonempty real sublevel. Its ambient weak compactness transfers to
the subtype C. The order-valued semicontinuous extreme-value theorem then
produces a minimizer; comparison with the original proper value makes it
finite. No minimizing sequence, sequential compactness, or lower bound is
assumed. The two final results supply exactly the sufficient boundedness
conditions in the manuscript.
-/
namespace ExpandedFA.P1.C14Minimization
universe u v
open Set
open Spec
noncomputable section

/-- Proper weakly l.s.c. functions with bounded real sublevels attain a
finite global minimum, including when no lower bound has been given. -/
theorem weak_compact_minimization : Attainment.{u, v} := by
  intro 𝕜 E _ _ _ _ hE C _hCne hC Φ hproper hΦ hb
  obtain ⟨a, ha⟩ := hproper
  lift Φ a to ℝ using ha with r hr
  have hbound := hb r
  have hcompact := (C14BallCharacterization.weakCompact_unitBall_iff_closed_bounded 𝕜 E).mp
    ((C14BallCharacterization.reflexive_iff_weakCompact_unitBall 𝕜 E).mp hE)
  letI : TopologicalSpace E := C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  have hlsc : LowerSemicontinuous Φ := hΦ
  let K : Set C := {x | Φ x ≤ (r : WithTop ℝ)}
  have hKclosed : IsClosed K := hlsc.isClosed_preimage r
  have hambclosed : IsClosed (sublevel C Φ r) :=
    hC.isClosedMap_subtype_val K hKclosed
  have hambcompact : IsCompact (Subtype.val '' K) :=
    hcompact (sublevel C Φ r) hbound hambclosed
  have hKcompact : IsCompact K :=
    Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr hambcompact
  have haK : a ∈ K := by change Φ a ≤ (r : WithTop ℝ); rw [← hr]
  obtain ⟨x₀, hx₀, hmin⟩ :=
    hlsc.lowerSemicontinuousOn K |>.exists_isMinOn ⟨a, haK⟩ hKcompact
  have hxfinite : Φ x₀ ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hx₀
  lift Φ x₀ to ℝ using hxfinite with m hm
  refine ⟨x₀, m, hm.symm, ?_⟩
  intro x
  by_cases hx : x ∈ K
  · exact hmin hx
  · exact hx₀.trans (le_of_not_ge hx)

/-- Boundedness of C bounds every sublevel, without regularity assumptions. -/
theorem bounded_domain_bounded_sublevels : BoundedDomainSublevels.{v} := by
  intro E _ C Φ hC a
  apply hC.subset
  rintro x ⟨y, _hy, rfl⟩
  exact y.property

/-- Coercivity on C bounds all real sublevels, without assuming C unbounded. -/
theorem coercive_bounded_sublevels : CoerciveSublevels.{v} := by
  intro E _ C Φ hΦ a
  obtain ⟨R, hR⟩ := hΦ a
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  exact le_of_lt (lt_of_not_ge fun hn => (hR y hn).not_ge hy)

end
end ExpandedFA.P1.C14Minimization

/-!
The convex direct method, including its weak-regularity bridge, over ℝ and ℂ.
The general nonconvex conclusion uses the upstream weak compactness theorem.
For the specialization, real convexity and norm closedness give weak closedness;
convexity of the finite-height epigraph and norm lower semicontinuity give weak
lower semicontinuity. Restricting along the continuous subtype inclusion gives
the precise relative weak lower semicontinuity needed by the general theorem.
-/
namespace ExpandedFA.P1.C14Minimization
universe u v
open Spec
noncomputable section

/-- General weak direct method, with each sufficient sublevel condition. -/
theorem general_direct_method : Spec.GeneralDirectMethod.{u, v} := by
  intro 𝕜 E _ _ _ _ hE C hCne hC Φ hproper hΦ hbound
  apply weak_compact_minimization 𝕜 E hE C hCne hC Φ hproper hΦ
  rcases hbound with hb | hc | hCbound
  · exact hb
  · exact coercive_bounded_sublevels E C Φ hc
  · exact bounded_domain_bounded_sublevels E C Φ hCbound

/-- Norm-convex hypotheses establish applicability in the relative weak topology. -/
theorem convex_direct_method_applicability :
    Spec.ConvexApplicability.{u, v} := by
  intro 𝕜 E _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro C hconvC hclosed Φ hconvΦ hlsc
  have hC := C12ConvexClosure.isWeaklyClosed_of_isClosed_convex 𝕜 E C hconvC hclosed
  have hΦ := C12NormLsc.convex_weak_lowerSemicontinuous 𝕜 E Φ hconvΦ hlsc
  refine ⟨hC, hΦ, ?_⟩
  letI : TopologicalSpace E := C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  exact hΦ.comp continuous_subtype_val

/-- The convex specialization of attainment by weak compactness. -/
theorem convex_direct_method : Spec.ConvexDirectMethod.{u, v} := by
  intro 𝕜 E _ _ _ _ hE
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro C hCne hconvC hclosed Φ hconvΦ hlsc hproper hbound
  obtain ⟨hC, _, hΦ⟩ :=
    convex_direct_method_applicability 𝕜 E C hconvC hclosed Φ hconvΦ hlsc
  exact general_direct_method 𝕜 E hE C hCne hC
    (fun x : C => Φ (x : E)) hproper hΦ hbound

end
end ExpandedFA.P1.C14Minimization
