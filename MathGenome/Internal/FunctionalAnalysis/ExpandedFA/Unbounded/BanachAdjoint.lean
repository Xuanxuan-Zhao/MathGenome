import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! The Banach adjoint is represented by its extension relation. Density makes
this relation single valued. Its domain is then identified with boundedness in
the original X norm. All duals and all pairings are scalar-linear. -/

noncomputable section
namespace ExpandedFA.Unbounded

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- D(A') is defined by boundedness in the ambient X norm. -/
abbrev banachAdjointDomain : BanachAdjointSpec.DomainType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  BanachAdjointSpec.domainValue

/-- The scalar-linear adjoint, valid on densely defined operators. -/
abbrev banachAdjoint : BanachAdjointSpec.AdjointType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  BanachAdjointSpec.adjointValue

/-- Continuous functionals agreeing on the domain agree everywhere. -/
theorem dual_eq_of_eq_on_domain (A : Operator 𝕜 X Y)
    (hA : Dense (A.domain : Set X)) (f g : X →L[𝕜] 𝕜)
    (h : ∀ x : A.domain, f (x : X) = g (x : X)) : f = g := by
  ext x
  exact hA.induction (fun y hy => h ⟨y, hy⟩)
    (isClosed_eq f.continuous g.continuous) x

private theorem extensionRelation_vertical (A : Operator 𝕜 X Y)
    (hA : Dense (A.domain : Set X)) :
    ∀ p ∈ BanachAdjointSpec.extensionRelation A, p.1 = 0 → p.2 = 0 := by
  intro p hp hp0
  apply dual_eq_of_eq_on_domain A hA
  intro x
  simpa only [hp0, zero_apply] using hp x

/-- Exact graph, including the domain membership condition. -/
theorem banachAdjoint_graph (A : Operator 𝕜 X Y)
    (hA : Dense (A.domain : Set X)) :
    (banachAdjoint A).graph = BanachAdjointSpec.extensionRelation A :=
  Submodule.toLinearPMap_graph_eq _ (extensionRelation_vertical A hA)

/-- A functional belongs to the adjoint domain iff its composition has a
continuous extension to X. -/
theorem mem_banachAdjoint_domain_iff (A : Operator 𝕜 X Y)
    (q : Y →L[𝕜] 𝕜) :
    q ∈ (banachAdjoint A).domain ↔
      ∃ f : X →L[𝕜] 𝕜, ∀ x : A.domain, f (x : X) = q (A x) := by
  change q ∈ (BanachAdjointSpec.extensionRelation A).map
    (LinearMap.fst 𝕜 _ _) ↔ _
  constructor
  · rintro ⟨⟨r, f⟩, hp, hr⟩
    change r = q at hr
    subst r
    exact ⟨f, hp⟩
  · rintro ⟨f, hf⟩
    exact ⟨(q, f), hf, rfl⟩

theorem banachAdjoint_domain : BanachAdjointSpec.DomainLaw
    (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A hA
  ext q
  change q ∈ (banachAdjoint A).domain ↔ q ∈ banachAdjointDomain A
  rw [mem_banachAdjoint_domain_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨‖f‖, fun x => by rw [← hf x]; exact f.le_opNorm (x : X)⟩
  · rintro ⟨C, hC⟩
    let f := q.toLinearMap.comp A.toFun
    refine ⟨f.extendOfNorm A.domain.subtype, fun x => ?_⟩
    exact LinearMap.extendOfNorm_eq (by simpa using hA) ⟨C, hC⟩ x

theorem banachAdjoint_apply : BanachAdjointSpec.ExtensionLaw
    (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A hA q x
  have h := LinearPMap.mem_graph (banachAdjoint A) q
  rw [banachAdjoint_graph A hA] at h
  exact h x

theorem banachAdjoint_unique_extension : BanachAdjointSpec.UniqueExtensionLaw
    (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A hA q f hf
  apply dual_eq_of_eq_on_domain A hA
  intro x
  exact (hf x).trans (banachAdjoint_apply A hA q x).symm

theorem banachAdjoint_closed : BanachAdjointSpec.ClosedLaw
    (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A hA
  change _root_.IsClosed ((banachAdjoint A).graph : Set ((Y →L[𝕜] 𝕜) × (X →L[𝕜] 𝕜)))
  rw [banachAdjoint_graph A hA]
  change _root_.IsClosed {p : (Y →L[𝕜] 𝕜) × (X →L[𝕜] 𝕜) |
    ∀ x : A.domain, p.2 (x : X) = p.1 (A x)}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun (x : A.domain) => isClosed_eq
    ((ContinuousLinearMap.apply 𝕜 𝕜 (x : X)).continuous.comp continuous_snd)
    ((ContinuousLinearMap.apply 𝕜 𝕜 (A x)).continuous.comp continuous_fst)

/-- The adjoint kernel is precisely the continuous annihilator of the range. -/
theorem mem_banachAdjoint_kernel_iff (A : Operator 𝕜 X Y)
    (hA : Dense (A.domain : Set X)) (q : Y →L[𝕜] 𝕜) :
    q ∈ (banachAdjoint A).ker ↔ ∀ x : A.domain, q (A x) = 0 := by
  constructor
  · intro hq
    rcases LinearPMap.mem_ker_iff.mp hq with ⟨r, rfl, hr⟩
    intro x
    rw [← banachAdjoint_apply A hA r x, hr]
    rfl
  · intro hq
    have hmem : q ∈ (banachAdjoint A).domain :=
      (mem_banachAdjoint_domain_iff A q).mpr ⟨0, fun x => (hq x).symm⟩
    let r : (banachAdjoint A).domain := ⟨q, hmem⟩
    refine LinearPMap.mem_ker_iff.mpr ⟨r, rfl, ?_⟩
    exact (banachAdjoint_unique_extension A hA r 0
      (fun x => (hq x).symm)).symm

/-- Hahn–Banach separates a vector outside the norm closure of a subspace.
The quotient carries the ambient quotient norm. -/
theorem exists_dual_vanishing_of_not_mem_closure (S : Submodule 𝕜 Y) (y : Y)
    (hy : y ∉ _root_.closure (S : Set Y)) :
    ∃ q : Y →L[𝕜] 𝕜, (∀ z ∈ S, q z = 0) ∧ q y ≠ 0 := by
  let M := S.topologicalClosure
  haveI : _root_.IsClosed (M : Set Y) := S.isClosed_topologicalClosure
  have hyq : M.mkQ y ≠ 0 := by
    intro h
    exact hy ((Submodule.Quotient.mk_eq_zero M).mp h)
  obtain ⟨f, hf⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hyq
  refine ⟨f.comp M.mkQL, ?_, hf⟩
  intro z hz
  change f (M.mkQ z) = 0
  have hzq : M.mkQ z = 0 :=
    (Submodule.Quotient.mk_eq_zero M).mpr (S.le_topologicalClosure hz)
  rw [hzq, map_zero]

theorem banachAdjoint_range_closure : BanachAdjointSpec.RangeClosureLaw
    (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A hA
  ext y
  constructor
  · intro hy q hq
    have hvan := (mem_banachAdjoint_kernel_iff A hA q).mp hq
    exact (isClosed_eq q.continuous continuous_const).closure_subset_iff.mpr
      (by rintro z ⟨x, rfl⟩; exact hvan x) hy
  · intro hy
    by_contra hnot
    obtain ⟨q, hvan, hqy⟩ :=
      exists_dual_vanishing_of_not_mem_closure A.toFun.range y hnot
    apply hqy
    apply hy q
    exact (mem_banachAdjoint_kernel_iff A hA q).mpr
      (fun x => hvan (A x) (LinearMap.mem_range_self A.toFun x))

theorem banachAdjoint_graph_annihilator : BanachAdjointSpec.GraphAnnihilatorLaw
    (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A hA
  ext p
  constructor
  · intro hp
    have hf : ∀ x : A.domain, (-p.1) (x : X) = p.2 (A x) := by
      intro x
      have hx := hp ((x : X), A x) (A.mem_graph x)
      change -p.1 (x : X) = p.2 (A x)
      exact neg_eq_iff_add_eq_zero.mpr hx
    have hmem : p.2 ∈ (banachAdjoint A).domain :=
      (mem_banachAdjoint_domain_iff A p.2).mpr ⟨-p.1, hf⟩
    let q : (banachAdjoint A).domain := ⟨p.2, hmem⟩
    have hval : banachAdjoint A q = -p.1 :=
      (banachAdjoint_unique_extension A hA q (-p.1) hf).symm
    refine ⟨q, ?_⟩
    change p = (-banachAdjoint A q, p.2)
    rw [hval, neg_neg]
  · rintro ⟨q, rfl⟩ z hz
    rcases A.mem_graph_iff.mp hz with ⟨x, hx, hy⟩
    change -(banachAdjoint A q) z.1 + (q : Y →L[𝕜] 𝕜) z.2 = 0
    rw [← hx, ← hy, banachAdjoint_apply A hA q x]
    exact neg_add_cancel _

end ExpandedFA.Unbounded
