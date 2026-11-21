import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04DualMaps
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04EvaluationContractive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorEstimates

/-! Basic dual maps, Proposition `fa2:p1:c04:dual-maps`.
Closedness and closed-span invariance follow from continuous evaluation and
closed kernels. Quotient factorization supplies both norm preservation and
surjectivity of pullback. No Hahn–Banach theorem or completeness is used. -/

noncomputable section

namespace ExpandedFA.P1.C04DualMaps

universe u v

theorem annihilator_isClosed : Spec.AnnihilatorClosed.{u, v} := by
  intro 𝕜 E _ _ _ A
  change IsClosed {f : C04Dual.ContinuousDual 𝕜 E | ∀ a ∈ A, f a = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun _ =>
    isClosed_eq (C04CanonicalMap.canonicalEvaluation 𝕜 E a).continuous continuous_const

theorem preannihilator_isClosed : Spec.PreannihilatorClosed.{u, v} := by
  intro 𝕜 E _ _ _ B
  change IsClosed {x : E | ∀ f ∈ B, f x = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_eq f.continuous continuous_const

/-- A continuous linear functional vanishes on the closed linear span of a set
exactly when it vanishes on the set itself. -/
theorem vanishes_on_closed_span_iff (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : C04Dual.ContinuousDual 𝕜 E) (A : Set E) :
    (∀ x ∈ ((Submodule.span 𝕜 A).topologicalClosure : Set E), f x = 0) ↔
      ∀ x ∈ A, f x = 0 := by
  constructor
  · intro h x hx
    exact h x ((Submodule.span 𝕜 A).le_topologicalClosure (Submodule.subset_span hx))
  · intro h x hx
    have hspan : Submodule.span 𝕜 A ≤ f.ker := Submodule.span_le.mpr h
    exact (Submodule.span 𝕜 A).topologicalClosure_minimal hspan f.isClosed_ker hx

theorem annihilator_closed_span : Spec.AnnihilatorClosedSpan.{u, v} := by
  intro 𝕜 E _ _ _ A
  apply Submodule.ext
  intro f
  exact vanishes_on_closed_span_iff 𝕜 E f A

theorem preannihilator_closed_span :
    Spec.PreannihilatorClosedSpan.{u, v} := by
  intro 𝕜 E _ _ _ B
  apply Submodule.ext
  intro x
  exact vanishes_on_closed_span_iff 𝕜 (C04Dual.ContinuousDual 𝕜 E)
    (C04CanonicalMap.canonicalEvaluation 𝕜 E x) B

theorem annihilator_antitone : Spec.AnnihilatorAntitone.{u, v} := by
  intro 𝕜 E _ _ _ A₁ A₂ hA f hf a ha
  exact hf a (hA ha)

theorem preannihilator_antitone :
    Spec.PreannihilatorAntitone.{u, v} := by
  intro 𝕜 E _ _ _ B₁ B₂ hB x hx f hf
  exact hx f (hB hf)

end ExpandedFA.P1.C04DualMaps

namespace ExpandedFA.P1.C04DualMaps

universe u v w z

/-- The bounded scalar-linear restriction map E′ → M′, for any subspace M. -/
noncomputable abbrev dualRestriction :
    Spec.DualRestrictionType.{u, v} :=
  Spec.DualRestrictionValue

@[simp] theorem dualRestriction_apply (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (f : C04Dual.ContinuousDual 𝕜 E) (x : M) :
    dualRestriction 𝕜 E M f x = f (x : E) := rfl

/-- Taking a supremum over the subspace unit ball cannot increase the norm. -/
theorem dualRestriction_le (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (f : C04Dual.ContinuousDual 𝕜 E) :
    ‖dualRestriction 𝕜 E M f‖ ≤ ‖f‖ := by
  exact C03OperatorEstimates.operator_domain_restriction_bound 𝕜 E 𝕜 f M

theorem dualRestriction_norm_le :
    Spec.DualRestrictionNormBound.{u, v} := by
  intro 𝕜 E _ _ _ M
  apply (dualRestriction 𝕜 E M).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using dualRestriction_le 𝕜 E M f

/-- Composition gives ‖T′f‖ ≤ ‖f‖ ‖T‖, and hence the norm bound for T′. -/
theorem banachTranspose_norm_le (𝕜 : Type u) (E : Type v) (F : Type w)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : C03OperatorNorm.Operator 𝕜 E F) :
    ‖C04Annihilators.banachTranspose 𝕜 E F T‖ ≤ ‖T‖ := by
  apply (C04Annihilators.banachTranspose 𝕜 E F T).opNorm_le_bound (norm_nonneg T)
  intro f
  have hcomp : C04Annihilators.banachTranspose 𝕜 E F T f = f.comp T := by
    ext x
    rfl
  rw [hcomp]
  simpa only [mul_comm] using C03OperatorEstimates.operator_composition_bound 𝕜 E F 𝕜 f T

/-- Evaluation reduces both sides to f (S (T x)). -/
theorem banachTranspose_comp (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (S : C03OperatorNorm.Operator 𝕜 F G) (T : C03OperatorNorm.Operator 𝕜 E F) :
    C04Annihilators.banachTranspose 𝕜 E G (S.comp T) =
      (C04Annihilators.banachTranspose 𝕜 E F T).comp (C04Annihilators.banachTranspose 𝕜 F G S) := by
  ext f x
  rfl

end ExpandedFA.P1.C04DualMaps

namespace ExpandedFA.P1.C04DualMaps

universe u v

theorem quotient_dual_factorization :
    Spec.NormPreservingFactorization.{u, v} := by
  intro 𝕜 E _ _ _ M hM f
  exact C02QuotientMap.quotient_bounded_factorization 𝕜 E 𝕜 M hM f.val f.property

theorem quotient_dual_isometry :
    Spec.QuotientDualIsometry.{u, v} := by
  intro 𝕜 E _ _ _ M hM
  let : IsClosed (M : Set E) := hM
  let q : E →L[𝕜] (E ⧸ M) := ⟨M.mkQ, M.continuous_mkQ⟩
  let L : ((E ⧸ M) →L[𝕜] 𝕜) →ₗ[𝕜] C04Annihilators.annihilator 𝕜 E (M : Set E) :=
    { toFun := fun f => ⟨f.comp q, by
        intro m hm
        change f (Submodule.Quotient.mk m) = 0
        rw [(Submodule.Quotient.mk_eq_zero M).mpr hm, map_zero]⟩
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl }
  have hnorm (f : (E ⧸ M) →L[𝕜] 𝕜) : ‖L f‖ = ‖f‖ := by
    obtain ⟨U, hU, hn, hu⟩ := quotient_dual_factorization 𝕜 E M hM (L f)
    have hf : f = U := hu f (fun _ => rfl)
    exact hn.symm.trans (congrArg norm hf.symm)
  let I : ((E ⧸ M) →L[𝕜] 𝕜) →ₗᵢ[𝕜] C04Annihilators.annihilator 𝕜 E (M : Set E) :=
    { L with norm_map' := hnorm }
  have hsurj : Function.Surjective I := by
    intro f
    obtain ⟨U, hU, _, _⟩ := quotient_dual_factorization 𝕜 E M hM f
    refine ⟨U, ?_⟩
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    exact hU
  exact ⟨LinearIsometryEquiv.ofSurjective I hsurj, fun _ _ => rfl⟩

end ExpandedFA.P1.C04DualMaps
