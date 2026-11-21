import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.WeakVariants.UnboundedAdjointClosures
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06DoubleAnnihilator

/-! Adjoint closures in the scalar-linear dual pairing.

Double annihilation of the closed original graph identifies the preannihilator
of Ran A′ with ker A and that of D(A′) with {0}. Weak-star double annihilation
then gives the two general identities. For a reflexive predual, apply primal
double annihilation in its normed dual and represent every bidual functional by
canonical evaluation. This yields precisely the two qualified norm statements. -/

noncomputable section
namespace ExpandedFA.WeakVariants.UnboundedAdjointClosures

universe u v w
open ExpandedFA.Unbounded ExpandedFA.P1

section Graph
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A closed graph is recovered from all its adjoint pairing identities. -/
theorem mem_graph_iff_adjoint_pairing (A : Operator 𝕜 X Y)
    (hd : Dense (A.domain : Set X)) (hc : A.IsClosed) (z : X × Y) :
    z ∈ A.graph ↔ ∀ q : (banachAdjoint A).domain,
      banachAdjoint A q z.1 = (q : Y →L[𝕜] 𝕜) z.2 := by
  constructor
  · intro hz q
    rcases A.mem_graph_iff.mp hz with ⟨x, hx, hy⟩
    rw [← hx, ← hy]
    exact banachAdjoint_apply A hd q x
  · intro hz
    have hzcl : z ∈ _root_.closure (A.graph : Set (X × Y)) := by
      rw [← C06DoubleAnnihilator.double_annihilator_primal 𝕜 (X × Y) A.graph]
      change ∀ f : (X × Y) →L[𝕜] 𝕜,
        (∀ t ∈ A.graph, f t = 0) → f z = 0
      intro f hf
      let p : X →L[𝕜] 𝕜 := f.comp (ContinuousLinearMap.inl 𝕜 X Y)
      let q : Y →L[𝕜] 𝕜 := f.comp (ContinuousLinearMap.inr 𝕜 X Y)
      have hsum (t : X × Y) : p t.1 + q t.2 = f t := by
        change f (t.1, 0) + f (0, t.2) = f t
        rw [← map_add]
        simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
      have hpq : (p, q) ∈ {r : (X →L[𝕜] 𝕜) × (Y →L[𝕜] 𝕜) |
          ∀ t : X × Y, t ∈ A.graph → r.1 t.1 + r.2 t.2 = 0} := by
        intro t ht
        rw [hsum]
        exact hf t ht
      rw [banachAdjoint_graph_annihilator A hd] at hpq
      obtain ⟨r, hr⟩ := hpq
      have hp : p = -banachAdjoint A r := congrArg Prod.fst hr
      have hq : q = (r : Y →L[𝕜] 𝕜) := congrArg Prod.snd hr
      rw [← hsum z, hp, hq]
      change -(banachAdjoint A r z.1) + (r : Y →L[𝕜] 𝕜) z.2 = 0
      rw [hz r, neg_add_cancel]
    exact hc.closure_subset hzcl

/-- The preannihilator of the adjoint range is exactly ker A. -/
theorem preannihilator_adjoint_range (A : Operator 𝕜 X Y)
    (hd : Dense (A.domain : Set X)) (hc : A.IsClosed) :
    C04Annihilators.Spec.PreannihilatorValue 𝕜 X
      ((banachAdjoint A).toFun.range : Set (X →L[𝕜] 𝕜)) = A.ker := by
  ext x
  change (∀ f ∈ (banachAdjoint A).toFun.range, f x = 0) ↔ x ∈ A.ker
  constructor
  · intro hx
    have hg : (x, (0 : Y)) ∈ A.graph :=
      (mem_graph_iff_adjoint_pairing A hd hc (x, 0)).mpr (fun q => by
        simpa using hx (banachAdjoint A q) (LinearMap.mem_range_self _ q))
    rcases A.mem_graph_iff.mp hg with ⟨d, hdx, hd0⟩
    exact LinearPMap.mem_ker_iff.mpr ⟨d, hdx.symm, hd0⟩
  · intro hx f hf
    rcases LinearPMap.mem_ker_iff.mp hx with ⟨d, rfl, hd0⟩
    rcases hf with ⟨q, rfl⟩
    change banachAdjoint A q (d : X) = 0
    rw [banachAdjoint_apply A hd q d, hd0, map_zero]

/-- The preannihilator of the actual adjoint domain is zero. -/
theorem preannihilator_adjoint_domain (A : Operator 𝕜 X Y)
    (hd : Dense (A.domain : Set X)) (hc : A.IsClosed) :
    C04Annihilators.Spec.PreannihilatorValue 𝕜 Y
      ((banachAdjoint A).domain : Set (Y →L[𝕜] 𝕜)) = ⊥ := by
  ext y
  change (∀ q ∈ (banachAdjoint A).domain, q y = 0) ↔ y = 0
  constructor
  · intro hy
    have hg : ((0 : X), y) ∈ A.graph :=
      (mem_graph_iff_adjoint_pairing A hd hc (0, y)).mpr (fun q => by
        simpa using (hy q q.2).symm)
    rcases A.mem_graph_iff.mp hg with ⟨d, hd0, hdy⟩
    have hd : d = 0 := Subtype.ext hd0
    simpa only [hd, A.map_zero] using hdy.symm
  · rintro rfl q _
    exact map_zero q

end Graph

/-- In a reflexive predual, norm double annihilation of a dual subspace
uses exactly the same evaluations as weak-star double annihilation. -/
theorem norm_closure_eq_double_annihilator
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hE : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E)
    (N : Submodule 𝕜 (E →L[𝕜] 𝕜)) :
    _root_.closure (N : Set (E →L[𝕜] 𝕜)) =
      (C04Annihilators.Spec.AnnihilatorValue 𝕜 E
        (C04Annihilators.Spec.PreannihilatorValue 𝕜 E
          (N : Set (E →L[𝕜] 𝕜)) : Set E) : Set (E →L[𝕜] 𝕜)) := by
  rw [← C06DoubleAnnihilator.double_annihilator_primal 𝕜 (E →L[𝕜] 𝕜) N]
  ext f
  change (∀ F : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜,
    (∀ g ∈ N, F g = 0) → F f = 0) ↔
      (∀ x : E, (∀ g ∈ N, g x = 0) → f x = 0)
  constructor
  · intro hf x hx
    exact hf (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x) hx
  · intro hf F hF
    obtain ⟨x, rfl⟩ := hE F
    exact hf x hF

/-- Weak-star closure of Ran A′, with no reflexivity assumption. -/
theorem weakStar_range_closure : Spec.WeakStarRangeClosure.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A hd hc
  rw [← C06DoubleAnnihilator.double_annihilator_dual 𝕜 X
    (banachAdjoint A).toFun.range]
  rw [preannihilator_adjoint_range A hd hc]

/-- Weak-star density of D(A′), with no reflexivity assumption. -/
theorem weakStar_domain_closure : Spec.WeakStarDomainClosure.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A hd hc
  rw [← C06DoubleAnnihilator.double_annihilator_dual 𝕜 Y
    (banachAdjoint A).domain]
  rw [preannihilator_adjoint_domain A hd hc]
  ext q
  change (∀ y : Y, y ∈ (⊥ : Submodule 𝕜 Y) → q y = 0) ↔ True
  simp

/-- Norm closure of Ran A′ when X is reflexive. -/
theorem norm_range_closure : Spec.NormRangeClosure.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ hX A hd hc
  rw [norm_closure_eq_double_annihilator 𝕜 X hX (banachAdjoint A).toFun.range]
  rw [preannihilator_adjoint_range A hd hc]

/-- Norm density of D(A′) when Y is reflexive. -/
theorem norm_domain_closure : Spec.NormDomainClosure.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ hY A hd hc
  rw [norm_closure_eq_double_annihilator 𝕜 Y hY (banachAdjoint A).domain]
  rw [preannihilator_adjoint_domain A hd hc]
  ext q
  change (∀ y : Y, y ∈ (⊥ : Submodule 𝕜 Y) → q y = 0) ↔ True
  simp

end ExpandedFA.WeakVariants.UnboundedAdjointClosures
