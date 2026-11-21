import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.ClosedSymmetricExtensions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.DeficiencyGraphDecomposition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SelfAdjointRangeCriterion
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! Closed symmetric extensions with exact domains, paper.tex:13687–13724. -/
noncomputable section
universe u
namespace ExpandedFA.Unbounded
open ClosedSymmetricExtensionsSpec DeficiencyGraphDecompositionSpec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- S_W is the restriction of the canonical Hilbert adjoint. -/
def closedSymmetricExtension : ExtensionTypeExpected := extensionValue

/-- Each defect vector is in the full adjoint domain. -/
theorem deficiencySpace_le_adjoint_domain (S : Operator ℂ H H) (z : ℂ) :
    deficiencySpace S z ≤ (hilbertAdjoint S).domain := by
  intro x hx
  exact ((mem_deficiencySpace_iff S z x).mp hx).1

/-- The prescribed domain really lies in D(S*). -/
theorem extensionDomain_le_adjoint (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) : extensionDomain S p ≤ (hilbertAdjoint S).domain := by
  apply sup_le hS.2.1
  rintro y ⟨u, rfl⟩
  exact (hilbertAdjoint S).domain.add_mem
    (deficiencySpace_le_adjoint_domain S Complex.I u.val.prop)
    (deficiencySpace_le_adjoint_domain S (-Complex.I) (p.isometry u).prop)

theorem closedSymmetricExtension_domain (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) :
    (extensionValue S p).domain = extensionDomain S p :=
  inf_eq_left.mpr (extensionDomain_le_adjoint S hS p)

/-- Inclusion holds as partial maps, including the values on all of D(S). -/
theorem le_closedSymmetricExtension (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) : S ≤ extensionValue S p := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact ⟨(show S.domain ≤ extensionDomain S p from le_sup_left) hx, hS.2.1 hx⟩
  · intro x y hxy
    exact hS.2.2 hxy

theorem closedSymmetricExtension_le_adjoint (S : Operator ℂ H H)
    (p : ExtensionParameter S) : extensionValue S p ≤ hilbertAdjoint S :=
  LinearPMap.domRestrict_le

/-- The graph form of the action formula avoids arbitrary choices of domain proofs. -/
theorem closedSymmetricExtension_action (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) (x : S.domain) (u : p.initialSpace) :
    ((x : H) + ((u : SymmetryAndDeficienciesSpec.deficiencyPlusValue S) : H) +
        (p.isometry u : H),
      S x + Complex.I • ((u : SymmetryAndDeficienciesSpec.deficiencyPlusValue S) : H) -
        Complex.I • (p.isometry u : H)) ∈ (extensionValue S p).graph := by
  have hu := (mem_deficiencySpace_iff S Complex.I (u.val : H)).mp u.val.prop
  have hv := (mem_deficiencySpace_iff S (-Complex.I) (p.isometry u : H)).mp
    (p.isometry u).prop
  have hg : ((x : H) + (u.val : H) + (p.isometry u : H),
      S x + Complex.I • (u.val : H) - Complex.I • (p.isometry u : H)) ∈
      (hilbertAdjoint S).graph := by
    have hx := LinearPMap.le_graph_of_le hS.2 (S.mem_graph x)
    have hu' : ((u.val : H), Complex.I • (u.val : H)) ∈ (hilbertAdjoint S).graph :=
      (hilbertAdjoint S).mem_graph_iff.mpr ⟨⟨_, hu.1⟩, rfl, hu.2⟩
    have hv' : ((p.isometry u : H), (-Complex.I) • (p.isometry u : H)) ∈
        (hilbertAdjoint S).graph :=
      (hilbertAdjoint S).mem_graph_iff.mpr ⟨⟨_, hv.1⟩, rfl, hv.2⟩
    simpa only [Prod.mk_add_mk, neg_smul, sub_eq_add_neg] using
      (hilbertAdjoint S).graph.add_mem ((hilbertAdjoint S).graph.add_mem hx hu') hv'
  obtain ⟨y, hy, he⟩ := (hilbertAdjoint S).mem_graph_iff.mp hg
  have hd : (y : H) ∈ extensionDomain S p := by
    rw [hy]
    have hm : (u.val : H) + (p.isometry u : H) ∈ (boundaryMap S p).range := ⟨u, rfl⟩
    simpa only [add_assoc] using (extensionDomain S p).add_mem
      ((show S.domain ≤ extensionDomain S p from le_sup_left) x.prop) ((show (boundaryMap S p).range ≤ extensionDomain S p from le_sup_right) hm)
  exact (extensionValue S p).mem_graph_iff.mpr ⟨⟨y, hd, y.prop⟩, hy, he⟩

theorem closedSymmetricExtension_action_formula : ActionExpected := by
  intro H _ _ _ S _ hS p x u
  exact closedSymmetricExtension_action S hS p x u

/-- Graph-coordinate embedding of an adjoint eigenspace. -/
def deficiencyGraphMap (S : Operator ℂ H H) (z : ℂ) :
    deficiencySpace S z →ₗ[ℂ] WithLp 2 (H × H) :=
  (WithLp.linearEquiv 2 ℂ (H × H)).symm.toLinearMap.comp
    ((deficiencySpace S z).subtype.prod (z • (deficiencySpace S z).subtype))

@[simp] theorem deficiencyGraphMap_apply (S : Operator ℂ H H) (z : ℂ)
    (u : deficiencySpace S z) :
    deficiencyGraphMap S z u = WithLp.toLp 2 ((u : H), z • (u : H)) := rfl

theorem deficiencyGraphMap_mem (S : Operator ℂ H H) (z : ℂ)
    (u : deficiencySpace S z) : deficiencyGraphMap S z u ∈ defectSpace S z :=
  (mem_defectSpace_iff S z _ _).mpr ⟨u.prop, rfl⟩

/-- The part of the graph contributed by u+Wu. -/
def extensionGraphMap (S : Operator ℂ H H) (p : ExtensionParameter S) :
    p.initialSpace →ₗ[ℂ] WithLp 2 (H × H) :=
  (deficiencyGraphMap S Complex.I).comp p.initialSpace.subtype +
    (deficiencyGraphMap S (-Complex.I)).comp p.isometry.toLinearMap

@[simp] theorem extensionGraphMap_apply (S : Operator ℂ H H) (p : ExtensionParameter S)
    (u : p.initialSpace) : extensionGraphMap S p u =
      WithLp.toLp 2 ((u.val : H) + (p.isometry u : H),
        Complex.I • (u.val : H) - Complex.I • (p.isometry u : H)) := by
  change WithLp.toLp 2 ((u.val : H), Complex.I • (u.val : H)) +
    WithLp.toLp 2 ((p.isometry u : H), (-Complex.I) • (p.isometry u : H)) = _
  simp only [neg_smul, sub_eq_add_neg]
  rfl

theorem extensionGraphMap_mem_defect_sup (S : Operator ℂ H H) (p : ExtensionParameter S)
    (u : p.initialSpace) : extensionGraphMap S p u ∈
      defectSpace S Complex.I ⊔ defectSpace S (-Complex.I) := by
  exact Submodule.mem_sup.mpr ⟨_, deficiencyGraphMap_mem S Complex.I u.val,
    _, deficiencyGraphMap_mem S (-Complex.I) (p.isometry u), rfl⟩

theorem extensionGraphMap_mem_adjoint (S : Operator ℂ H H) (p : ExtensionParameter S)
    (u : p.initialSpace) : extensionGraphMap S p u ∈ graphSpace (hilbertAdjoint S) :=
  (graphSpace (hilbertAdjoint S)).add_mem
    (deficiencyGraphMap_mem S Complex.I u.val).1
    (deficiencyGraphMap_mem S (-Complex.I) (p.isometry u)).1

theorem graphSpace_ortho_extensionGraphMap (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) : (graphSpace S).IsOrtho (extensionGraphMap S p).range := by
  apply (Submodule.isOrtho_sup_right.mpr
    ⟨graphSpace_ortho_defectSpace S hS.1 Complex.I (by simp),
      graphSpace_ortho_defectSpace S hS.1 (-Complex.I) (by simp)⟩).mono_right
  rintro _ ⟨u, rfl⟩
  exact extensionGraphMap_mem_defect_sup S p u

/-- Cancellation of the two cross terms is what makes closed L₊ sufficient. -/
theorem extensionGraphMap_norm (S : Operator ℂ H H) (p : ExtensionParameter S)
    (u : p.initialSpace) : ‖extensionGraphMap S p u‖ = 2 * ‖u‖ := by
  have hn := WithLp.prod_norm_sq_eq_of_L2
    (WithLp.toLp 2 ((u.val : H) + (p.isometry u : H),
      Complex.I • ((u.val : H) - (p.isometry u : H))))
  have hp := parallelogram_law_with_norm ℂ (u.val : H) (p.isometry u : H)
  have hw : ‖(p.isometry u : H)‖ = ‖u‖ := p.isometry.norm_map u
  have hu : ‖(u.val : H)‖ = ‖u‖ := rfl
  change ‖WithLp.toLp 2 ((u.val : H) + (p.isometry u : H),
      Complex.I • ((u.val : H) - (p.isometry u : H)))‖ ^ 2 =
    ‖(u.val : H) + (p.isometry u : H)‖ ^ 2 +
      ‖Complex.I • ((u.val : H) - (p.isometry u : H))‖ ^ 2 at hn
  rw [norm_smul, Complex.norm_I, one_mul] at hn
  rw [hw, hu] at hp
  have he : ‖extensionGraphMap S p u‖ ^ 2 = 4 * ‖u‖ ^ 2 := by
    rw [extensionGraphMap_apply, ← smul_sub]
    nlinarith [hn, hp]
  nlinarith [norm_nonneg (extensionGraphMap S p u), norm_nonneg u]

/-- Exact graph equality for the constructed restriction. -/
theorem graphSpace_closedSymmetricExtension (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) :
    graphSpace (extensionValue S p) = graphSpace S ⊔ (extensionGraphMap S p).range := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨a, b⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective g
    obtain ⟨y, hy, hb⟩ := (extensionValue S p).mem_graph_iff.mp
      ((mem_graphSpace_iff _ a b).mp hg)
    change (y : H) = a at hy
    change extensionValue S p y = b at hb
    have hm : a ∈ extensionDomain S p := by
      rw [← hy]
      exact y.prop.1
    obtain ⟨x, hx, v, ⟨u, rfl⟩, he⟩ := Submodule.mem_sup.mp hm
    have hact := closedSymmetricExtension_action S hS p ⟨x, hx⟩ u
    have hval : b = S ⟨x, hx⟩ + Complex.I • (u.val : H) -
        Complex.I • (p.isometry u : H) := by
      obtain ⟨t, ht, ht'⟩ := (extensionValue S p).mem_graph_iff.mp hact
      change (t : H) = x + (u.val : H) + (p.isometry u : H) at ht
      change extensionValue S p t = _ at ht'
      have hyt : y = t := by
        apply Subtype.ext
        rw [hy, ht, ← he]
        change x + ((u.val : H) + (p.isometry u : H)) = _
        abel
      rw [← hb, hyt, ht']
    apply Submodule.mem_sup.mpr
    refine ⟨WithLp.toLp 2 (x, S ⟨x, hx⟩),
      (mem_graphSpace_iff S _ _).mpr (S.mem_graph ⟨x, hx⟩),
      extensionGraphMap S p u, ⟨u, rfl⟩, ?_⟩
    rw [extensionGraphMap_apply, hval, ← he]
    apply (WithLp.linearEquiv 2 ℂ (H × H)).injective
    change (x + ((u.val : H) + (p.isometry u : H)),
      S ⟨x, hx⟩ + (Complex.I • (u.val : H) - Complex.I • (p.isometry u : H))) = _
    congr 1; abel
  · apply sup_le
    · exact Submodule.map_mono (LinearPMap.le_graph_of_le (le_closedSymmetricExtension S hS p))
    · rintro g ⟨u, rfl⟩
      rw [extensionGraphMap_apply]
      have h := closedSymmetricExtension_action S hS p 0 u
      simpa only [Submodule.coe_zero, zero_add, S.map_zero] using
        (mem_graphSpace_iff _ _ _).mpr h

/-- A closed initial space has closed image in the adjoint graph. -/
theorem extensionGraphMap_range_isClosed (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) :
    _root_.IsClosed ((extensionGraphMap S p).range : Set (WithLp 2 (H × H))) := by
  let : CompleteSpace (SymmetryAndDeficienciesSpec.deficiencyPlusValue S) :=
    (deficiencySpace_isClosed S hS.1 Complex.I).isComplete.completeSpace_coe
  let : CompleteSpace p.initialSpace := p.closed_initialSpace.isComplete.completeSpace_coe
  let F := (extensionGraphMap S p).mkContinuous 2
    (fun u => (extensionGraphMap_norm S p u).le)
  have ha : AntilipschitzWith (1 / 2) F := F.antilipschitz_of_bound (by
    intro u
    change ‖u‖ ≤ (1 / 2 : ℝ) * ‖extensionGraphMap S p u‖
    rw [extensionGraphMap_norm]
    linarith)
  exact ha.isClosed_range F.uniformContinuous

/-- Orthogonal sums of closed subspaces are closed, by projection onto the
first summand. This does not assume finite dimension. -/
theorem isClosed_sup_of_isOrtho {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E)
    (hU : _root_.IsClosed (U : Set E)) (hV : _root_.IsClosed (V : Set E))
    (ho : U.IsOrtho V) : _root_.IsClosed ((U ⊔ V : Submodule ℂ E) : Set E) := by
  let : CompleteSpace U := hU.isComplete.completeSpace_coe
  have he : ((U ⊔ V : Submodule ℂ E) : Set E) =
      (fun x : E => x - U.starProjection x) ⁻¹' (V : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
      change u + v - U.starProjection (u + v) ∈ V
      rw [map_add, (U.starProjection_eq_self_iff).mpr hu,
        (U.starProjection_apply_eq_zero_iff).mpr (ho.symm hv)]
      simpa only [add_zero, add_sub_cancel_left] using hv
    · intro hx
      apply Submodule.mem_sup.mpr
      exact ⟨U.starProjection x, (U.orthogonalProjectionOnto x).prop,
        x - U.starProjection x, hx, by abel⟩
  rw [he]
  exact hV.preimage (continuous_id.sub U.starProjection.continuous)

theorem closedSymmetricExtension_isClosed (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) (p : ExtensionParameter S) :
    IsClosed (extensionValue S p) := by
  have h := isClosed_sup_of_isOrtho (graphSpace S) (extensionGraphMap S p).range
    (graphSpace_isClosed S hc) (extensionGraphMap_range_isClosed S hS p)
    (graphSpace_ortho_extensionGraphMap S hS p)
  rw [← graphSpace_closedSymmetricExtension S hS p] at h
  have he : ((extensionValue S p).graph : Set (H × H)) =
      (WithLp.toLp 2) ⁻¹' (graphSpace (extensionValue S p) : Set _) := by
    ext q
    exact (mem_graphSpace_iff _ q.1 q.2).symm
  change _root_.IsClosed ((extensionValue S p).graph : Set (H × H))
  rw [he]
  exact h.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.continuous

/-- Boundary pairing of a base graph vector and an adjoint graph vector. -/
theorem graphSpace_boundary (S : Operator ℂ H H) (hS : DenselyDefined S)
    (g k : WithLp 2 (H × H)) (hg : g ∈ graphSpace S)
    (hk : k ∈ graphSpace (hilbertAdjoint S)) :
    inner ℂ g.snd k.fst = inner ℂ g.fst k.snd := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective g
  obtain ⟨⟨y, b⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective k
  obtain ⟨v, hv, ha⟩ := S.mem_graph_iff.mp ((mem_graphSpace_iff S _ _).mp hg)
  have hb := (mem_hilbertAdjoint_graph_iff S hS y b).mp
    ((mem_graphSpace_iff _ _ _).mp hk) v
  change inner ℂ a y = inner ℂ x b
  change (v : H) = x at hv
  change S v = a at ha
  rwa [hv, ha] at hb

/-- The isometry condition cancels precisely the two signed boundary terms. -/
theorem extensionGraphMap_boundary (S : Operator ℂ H H) (p : ExtensionParameter S)
    (u v : p.initialSpace) :
    inner ℂ (extensionGraphMap S p u).snd (extensionGraphMap S p v).fst =
      inner ℂ (extensionGraphMap S p u).fst (extensionGraphMap S p v).snd := by
  have hw := LinearIsometry.inner_map_map (𝕜 := ℂ) p.isometry u v
  change inner ℂ (p.isometry u : H) (p.isometry v : H) =
    inner ℂ (u.val : H) (v.val : H) at hw
  simp only [extensionGraphMap_apply]
  change inner ℂ (Complex.I • (u.val : H) - Complex.I • (p.isometry u : H))
      ((v.val : H) + (p.isometry v : H)) =
    inner ℂ ((u.val : H) + (p.isometry u : H))
      (Complex.I • (v.val : H) - Complex.I • (p.isometry v : H))
  simp only [inner_sub_left, inner_add_right, inner_add_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_I, hw]
  ring

theorem closedSymmetricExtension_isSymmetric (S : Operator ℂ H H)
    (hS : IsSymmetric S) (p : ExtensionParameter S) : IsSymmetric (extensionValue S p) := by
  have hd : DenselyDefined (extensionValue S p) :=
    hS.1.mono (le_closedSymmetricExtension S hS p).1
  refine ⟨hd, LinearPMap.IsFormalAdjoint.le_adjoint hd ?_⟩
  intro x y
  let gx := WithLp.toLp 2 ((x : H), extensionValue S p x)
  let gy := WithLp.toLp 2 ((y : H), extensionValue S p y)
  have hx : gx ∈ graphSpace (extensionValue S p) :=
    (mem_graphSpace_iff _ _ _).mpr ((extensionValue S p).mem_graph x)
  have hy : gy ∈ graphSpace (extensionValue S p) :=
    (mem_graphSpace_iff _ _ _).mpr ((extensionValue S p).mem_graph y)
  rw [graphSpace_closedSymmetricExtension S hS p] at hx hy
  obtain ⟨s, hs, _, ⟨u, rfl⟩, he⟩ := Submodule.mem_sup.mp hx
  obtain ⟨t, ht, _, ⟨v, rfl⟩, hf⟩ := Submodule.mem_sup.mp hy
  have hst := graphSpace_boundary S hS.1 s t hs (graphSpace_le_adjoint hS ht)
  have hsv := graphSpace_boundary S hS.1 s (extensionGraphMap S p v) hs
    (extensionGraphMap_mem_adjoint S p v)
  have htu := graphSpace_boundary S hS.1 t (extensionGraphMap S p u) ht
    (extensionGraphMap_mem_adjoint S p u)
  have hut : inner ℂ (extensionGraphMap S p u).snd t.fst =
      inner ℂ (extensionGraphMap S p u).fst t.snd := by
    simpa only [inner_conj_symm] using (congrArg (starRingEnd ℂ) htu).symm
  have huv := extensionGraphMap_boundary S p u v
  change inner ℂ gx.snd gy.fst = inner ℂ gx.fst gy.snd
  rw [← he, ← hf]
  change inner ℂ (s.snd + (extensionGraphMap S p u).snd)
      (t.fst + (extensionGraphMap S p v).fst) =
    inner ℂ (s.fst + (extensionGraphMap S p u).fst)
      (t.snd + (extensionGraphMap S p v).snd)
  simp only [inner_add_left, inner_add_right, hst, hsv, hut, huv]

/-- Forward construction: all parameters give closed symmetric extensions. -/
theorem closedSymmetricExtension_closed_symmetric_extends : ConstructionExpected := by
  intro H _ _ _ S hc hS p
  exact ⟨closedSymmetricExtension_isClosed S hc hS p,
    closedSymmetricExtension_isSymmetric S hS p, le_closedSymmetricExtension S hS p,
    closedSymmetricExtension_le_adjoint S p⟩

omit [CompleteSpace H] in
/-- A graph is determined by its first coordinate. -/
theorem graphSpace_fst_injective (A : Operator ℂ H H) {g k : WithLp 2 (H × H)}
    (hg : g ∈ graphSpace A) (hk : k ∈ graphSpace A) (he : g.fst = k.fst) : g = k := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective g
  obtain ⟨⟨y, b⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective k
  obtain ⟨v, hv, ha⟩ := A.mem_graph_iff.mp ((mem_graphSpace_iff A _ _).mp hg)
  obtain ⟨w, hw, hb⟩ := A.mem_graph_iff.mp ((mem_graphSpace_iff A _ _).mp hk)
  change x = y at he
  change (v : H) = x at hv
  change (w : H) = y at hw
  have hvw : v = w := Subtype.ext (hv.trans (he.trans hw.symm))
  have hab : a = b := ha.symm.trans ((congrArg A hvw).trans hb)
  exact congrArg (WithLp.toLp 2) (Prod.ext he hab)

theorem extensionGraphMap_injective (S : Operator ℂ H H) (p : ExtensionParameter S) :
    Function.Injective (extensionGraphMap S p) := by
  intro u v huv
  have hz : extensionGraphMap S p (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hn := extensionGraphMap_norm S p (u - v)
  rw [hz, norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith))

theorem boundaryMap_injective (S : Operator ℂ H H) (p : ExtensionParameter S) :
    Function.Injective (boundaryMap S p) := by
  intro u v huv
  apply extensionGraphMap_injective S p
  apply graphSpace_fst_injective (hilbertAdjoint S)
    (extensionGraphMap_mem_adjoint S p u) (extensionGraphMap_mem_adjoint S p v)
  exact huv

theorem extensionDomain_disjoint (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) : Disjoint S.domain (boundaryMap S p).range := by
  apply Submodule.disjoint_def.mpr
  intro x hx hm
  obtain ⟨u, hux⟩ := hm
  have he : extensionGraphMap S p u = WithLp.toLp 2 (x, S ⟨x, hx⟩) :=
    graphSpace_fst_injective (hilbertAdjoint S)
      (extensionGraphMap_mem_adjoint S p u)
      (graphSpace_le_adjoint hS ((mem_graphSpace_iff S _ _).mpr (S.mem_graph ⟨x, hx⟩))) hux
  have ho := (graphSpace_ortho_extensionGraphMap S hS p).inner_eq
    ((mem_graphSpace_iff S _ _).mpr (S.mem_graph ⟨x, hx⟩))
    (show extensionGraphMap S p u ∈ (extensionGraphMap S p).range from ⟨u, rfl⟩)
  rw [← he] at ho
  have hz := inner_self_eq_zero.mp ho
  have hfst := congrArg (fun g : WithLp 2 (H × H) => g.fst) hz
  change boundaryMap S p u = 0 at hfst
  rwa [hux] at hfst

/-- The sum in the exact domain is direct and has a unique u coordinate. -/
theorem closedSymmetricExtension_direct_domain : DomainExpected := by
  intro H _ _ _ S _ hS p
  exact ⟨closedSymmetricExtension_domain S hS p, extensionDomain_disjoint S hS p,
    boundaryMap_injective S p⟩

/-- Both deficiency coordinates, with the ambient product norm on the source. -/
def deficiencyPairMap (S : Operator ℂ H H) :
    (SymmetryAndDeficienciesSpec.deficiencyPlusValue S ×
      SymmetryAndDeficienciesSpec.deficiencyMinusValue S) →L[ℂ] WithLp 2 (H × H) := by
  let f := (SymmetryAndDeficienciesSpec.deficiencyPlusValue S).subtypeL.comp
    (ContinuousLinearMap.fst ℂ _ (SymmetryAndDeficienciesSpec.deficiencyMinusValue S))
  let g := (SymmetryAndDeficienciesSpec.deficiencyMinusValue S).subtypeL.comp
    (ContinuousLinearMap.snd ℂ (SymmetryAndDeficienciesSpec.deficiencyPlusValue S) _)
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    ((f + g).prod (Complex.I • f - Complex.I • g))

@[simp] theorem deficiencyPairMap_apply (S : Operator ℂ H H)
    (q : SymmetryAndDeficienciesSpec.deficiencyPlusValue S ×
      SymmetryAndDeficienciesSpec.deficiencyMinusValue S) :
    deficiencyPairMap S q = WithLp.toLp 2
      ((q.1 : H) + (q.2 : H), Complex.I • (q.1 : H) - Complex.I • (q.2 : H)) := rfl

theorem deficiencyPairMap_eq_sum (S : Operator ℂ H H)
    (q : SymmetryAndDeficienciesSpec.deficiencyPlusValue S ×
      SymmetryAndDeficienciesSpec.deficiencyMinusValue S) :
    deficiencyPairMap S q = deficiencyGraphMap S Complex.I q.1 +
      deficiencyGraphMap S (-Complex.I) q.2 := by
  change WithLp.toLp 2 ((q.1 : H) + (q.2 : H),
      Complex.I • (q.1 : H) - Complex.I • (q.2 : H)) =
    WithLp.toLp 2 ((q.1 : H), Complex.I • (q.1 : H)) +
      WithLp.toLp 2 ((q.2 : H), (-Complex.I) • (q.2 : H))
  simp only [neg_smul, sub_eq_add_neg]
  rfl

theorem deficiencyPairMap_injective (S : Operator ℂ H H) :
    Function.Injective (deficiencyPairMap S) := by
  intro q r hqr
  have hfst := congrArg (fun g : WithLp 2 (H × H) => g.fst) hqr
  have hsnd := congrArg (fun g : WithLp 2 (H × H) => g.snd) hqr
  change (q.1 : H) + (q.2 : H) = (r.1 : H) + (r.2 : H) at hfst
  change Complex.I • (q.1 : H) - Complex.I • (q.2 : H) =
    Complex.I • (r.1 : H) - Complex.I • (r.2 : H) at hsnd
  have hd : (q.1 : H) - (q.2 : H) = (r.1 : H) - (r.2 : H) := by
    apply (smul_right_injective H Complex.I_ne_zero)
    simpa only [smul_sub] using hsnd
  apply Prod.ext <;> apply Subtype.ext
  · have : (2 : ℂ) • ((q.1 : H) - (r.1 : H)) = 0 := by
      rw [two_smul]
      calc
        _ = ((q.1 : H) + (q.2 : H) - ((r.1 : H) + (r.2 : H))) +
            ((q.1 : H) - (q.2 : H) - ((r.1 : H) - (r.2 : H))) := by abel
        _ = 0 := by rw [hfst, hd, sub_self, sub_self, add_zero]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_left (by norm_num))
  · have : (2 : ℂ) • ((q.2 : H) - (r.2 : H)) = 0 := by
      rw [two_smul]
      calc
        _ = ((q.1 : H) + (q.2 : H) - ((r.1 : H) + (r.2 : H))) -
            ((q.1 : H) - (q.2 : H) - ((r.1 : H) - (r.2 : H))) := by abel
        _ = 0 := by rw [hfst, hd, sub_self, sub_self, sub_zero]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_left (by norm_num))

/-- The boundary form in the deficiency coordinates. -/
theorem deficiencyPairMap_boundary (S : Operator ℂ H H)
    (q r : SymmetryAndDeficienciesSpec.deficiencyPlusValue S ×
      SymmetryAndDeficienciesSpec.deficiencyMinusValue S) :
    inner ℂ (deficiencyPairMap S q).snd (deficiencyPairMap S r).fst -
      inner ℂ (deficiencyPairMap S q).fst (deficiencyPairMap S r).snd =
        (-2 * Complex.I) * (inner ℂ (q.1 : H) (r.1 : H) -
          inner ℂ (q.2 : H) (r.2 : H)) := by
  change inner ℂ (Complex.I • (q.1 : H) - Complex.I • (q.2 : H))
      ((r.1 : H) + (r.2 : H)) -
    inner ℂ ((q.1 : H) + (q.2 : H))
      (Complex.I • (r.1 : H) - Complex.I • (r.2 : H)) = _
  simp only [inner_sub_left, inner_add_right, inner_add_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  ring

/-- The part of G(T) lying entirely in the two deficiency summands. -/
def extensionBoundarySpace (S T : Operator ℂ H H) :
    Submodule ℂ (SymmetryAndDeficienciesSpec.deficiencyPlusValue S ×
      SymmetryAndDeficienciesSpec.deficiencyMinusValue S) :=
  (graphSpace T).comap (deficiencyPairMap S).toLinearMap

theorem extensionBoundarySpace_isClosed (S T : Operator ℂ H H) (hcT : IsClosed T) :
    _root_.IsClosed ((extensionBoundarySpace S T : Submodule ℂ _) : Set
      (SymmetryAndDeficienciesSpec.deficiencyPlusValue S ×
        SymmetryAndDeficienciesSpec.deficiencyMinusValue S)) :=
  (graphSpace_isClosed T hcT).preimage (deficiencyPairMap S).continuous

/-- Symmetry forces equality of the two deficiency-coordinate norms. -/
theorem extensionBoundarySpace_norm (S T : Operator ℂ H H) (hT : IsSymmetric T)
    (q : extensionBoundarySpace S T) : ‖q.val.1‖ = ‖q.val.2‖ := by
  have hb := graphSpace_boundary T hT.1 (deficiencyPairMap S q.val)
    (deficiencyPairMap S q.val) q.prop (graphSpace_le_adjoint hT q.prop)
  have he := deficiencyPairMap_boundary S q.val q.val
  rw [hb, sub_self] at he
  have hi : inner ℂ (q.val.1 : H) (q.val.1 : H) =
      inner ℂ (q.val.2 : H) (q.val.2 : H) := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  simp only [inner_self_eq_norm_sq_to_K] at hi
  have hn : ‖q.val.1‖ ^ 2 = ‖q.val.2‖ ^ 2 := by exact_mod_cast hi
  nlinarith [norm_nonneg q.val.1, norm_nonneg q.val.2]

/-- On a symmetric extension's boundary space, the first projection is isometric. -/
def extensionBoundaryFst (S T : Operator ℂ H H) (hT : IsSymmetric T) :
    extensionBoundarySpace S T →ₗᵢ[ℂ] SymmetryAndDeficienciesSpec.deficiencyPlusValue S where
  toLinearMap := (LinearMap.fst ℂ _ _).comp (extensionBoundarySpace S T).subtype
  norm_map' q := by
    change ‖q.val.1‖ = max ‖q.val.1‖ ‖q.val.2‖
    rw [extensionBoundarySpace_norm S T hT q, max_self]

/-- Recover the unique isometry from the two projections. -/
def recoveredIsometry (S T : Operator ℂ H H) (hT : IsSymmetric T) :
    (extensionBoundaryFst S T hT).toLinearMap.range →ₗᵢ[ℂ]
      SymmetryAndDeficienciesSpec.deficiencyMinusValue S where
  toLinearMap := ((LinearMap.snd ℂ _ _).comp (extensionBoundarySpace S T).subtype).comp
    (extensionBoundaryFst S T hT).equivRange.symm.toLinearEquiv.toLinearMap
  norm_map' u := by
    let q := (extensionBoundaryFst S T hT).equivRange.symm u
    change ‖q.val.2‖ = ‖u‖
    rw [← extensionBoundarySpace_norm S T hT q]
    exact (extensionBoundaryFst S T hT).norm_map q |>.trans
      ((extensionBoundaryFst S T hT).equivRange.symm.norm_map u)

/-- Recovery uses only closedness and symmetry, with no extension assumed yet. -/
def recoveredParameter (S T : Operator ℂ H H) (hS : IsSymmetric S)
    (hcT : IsClosed T) (hT : IsSymmetric T) : ExtensionParameter S := by
  let : CompleteSpace (SymmetryAndDeficienciesSpec.deficiencyPlusValue S) :=
    (deficiencySpace_isClosed S hS.1 Complex.I).isComplete.completeSpace_coe
  let : CompleteSpace (SymmetryAndDeficienciesSpec.deficiencyMinusValue S) :=
    (deficiencySpace_isClosed S hS.1 (-Complex.I)).isComplete.completeSpace_coe
  let : CompleteSpace (extensionBoundarySpace S T) :=
    (extensionBoundarySpace_isClosed S T hcT).isComplete.completeSpace_coe
  exact
    { initialSpace := (extensionBoundaryFst S T hT).toLinearMap.range
      closed_initialSpace := (extensionBoundaryFst S T hT).isometry.antilipschitzWith.isClosed_range
        (extensionBoundaryFst S T hT).isometry.uniformContinuous
      isometry := recoveredIsometry S T hT }

/-- The graph of W in N₊×N₋ records both parts of its parameter. -/
def parameterPairSpace (S : Operator ℂ H H) (p : ExtensionParameter S) :
    Submodule ℂ (SymmetryAndDeficienciesSpec.deficiencyPlusValue S ×
      SymmetryAndDeficienciesSpec.deficiencyMinusValue S) :=
  (p.initialSpace.subtype.prod p.isometry.toLinearMap).range

theorem deficiencyPairMap_parameter (S : Operator ℂ H H) (p : ExtensionParameter S)
    (u : p.initialSpace) :
    deficiencyPairMap S (u.val, p.isometry u) = extensionGraphMap S p u := by
  rw [deficiencyPairMap_eq_sum]
  rfl

theorem pairMap_parameter_range (S : Operator ℂ H H) (p : ExtensionParameter S) :
    (parameterPairSpace S p).map (deficiencyPairMap S).toLinearMap =
      (extensionGraphMap S p).range := by
  ext g
  constructor
  · rintro ⟨q, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (deficiencyPairMap_parameter S p u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(u.val, p.isometry u), ⟨u, rfl⟩, deficiencyPairMap_parameter S p u⟩

/-- A symmetric extension is contained in the original adjoint. -/
theorem symmetric_extension_le_adjoint (S T : Operator ℂ H H)
    (hS : IsSymmetric S) (hT : IsSymmetric T) (hST : S ≤ T) : T ≤ hilbertAdjoint S := by
  apply LinearPMap.IsFormalAdjoint.le_adjoint hS.1
  intro x y
  have he : S x = T ⟨x, hST.1 x.prop⟩ := hST.2 rfl
  rw [he]
  exact hT.inner_map ⟨x, hST.1 x.prop⟩ y

/-- Remove the base graph and use the accepted three-summand decomposition. -/
theorem graphSpace_extension_decomposition (S T : Operator ℂ H H)
    (hcS : IsClosed S) (hS : IsSymmetric S) (hT : IsSymmetric T) (hST : S ≤ T) :
    graphSpace T = graphSpace S ⊔
      (extensionBoundarySpace S T).map (deficiencyPairMap S).toLinearMap := by
  have hinc : graphSpace S ≤ graphSpace T := Submodule.map_mono
    (LinearPMap.le_graph_of_le hST)
  have hinc' : graphSpace T ≤ graphSpace (hilbertAdjoint S) := Submodule.map_mono
    (LinearPMap.le_graph_of_le (symmetric_extension_le_adjoint S T hS hT hST))
  apply le_antisymm
  · intro g hg
    have ha := hinc' hg
    rw [adjoint_graph_eq_sup S hcS hS] at ha
    obtain ⟨s', hs', b, hb, he'⟩ := Submodule.mem_sup.mp ha
    obtain ⟨s, hs, a, ha, he⟩ := Submodule.mem_sup.mp hs'
    have ha' := (mem_defectSpace_iff S Complex.I a.fst a.snd).mp ha
    have hb' := (mem_defectSpace_iff S (-Complex.I) b.fst b.snd).mp hb
    let u : SymmetryAndDeficienciesSpec.deficiencyPlusValue S := ⟨a.fst, ha'.1⟩
    let v : SymmetryAndDeficienciesSpec.deficiencyMinusValue S := ⟨b.fst, hb'.1⟩
    have hua : deficiencyGraphMap S Complex.I u = a := by
      apply (WithLp.linearEquiv 2 ℂ (H × H)).injective
      exact Prod.ext rfl ha'.2.symm
    have hvb : deficiencyGraphMap S (-Complex.I) v = b := by
      apply (WithLp.linearEquiv 2 ℂ (H × H)).injective
      exact Prod.ext rfl hb'.2.symm
    have hp : deficiencyPairMap S (u, v) = a + b := by
      rw [deficiencyPairMap_eq_sum, hua, hvb]
    have hq : (u, v) ∈ extensionBoundarySpace S T := by
      change deficiencyPairMap S (u, v) ∈ graphSpace T
      rw [hp]
      have hz : a + b = g - s := by rw [← he', ← he]; abel
      rw [hz]
      exact (graphSpace T).sub_mem hg (hinc hs)
    exact Submodule.mem_sup.mpr ⟨s, hs, deficiencyPairMap S (u, v),
      ⟨(u, v), hq, rfl⟩, by rw [hp, ← he', ← he]; abel⟩
  · apply sup_le hinc
    rintro _ ⟨q, hq, rfl⟩
    exact hq

/-- Recovering the isometry on the range of the first projection returns the
original second coordinate. -/
theorem recoveredIsometry_apply_fst (S T : Operator ℂ H H) (hT : IsSymmetric T)
    (q : extensionBoundarySpace S T) :
    recoveredIsometry S T hT ((extensionBoundaryFst S T hT).equivRange q) = q.val.2 := by
  change ((extensionBoundaryFst S T hT).equivRange.symm
    ((extensionBoundaryFst S T hT).equivRange q)).val.2 = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem recoveredParameter_pairSpace (S T : Operator ℂ H H) (hS : IsSymmetric S)
    (hcT : IsClosed T) (hT : IsSymmetric T) :
    parameterPairSpace S (recoveredParameter S T hS hcT hT) = extensionBoundarySpace S T := by
  let e := (extensionBoundaryFst S T hT).equivRange
  apply le_antisymm
  · rintro q ⟨u, rfl⟩
    let r := e.symm u
    have he : e r = u := e.apply_symm_apply u
    have hfst : r.val.1 = u.val := congrArg Subtype.val he
    have hsnd : recoveredIsometry S T hT u = r.val.2 := by
      rw [← he]
      exact recoveredIsometry_apply_fst S T hT r
    change (u.val, recoveredIsometry S T hT u) ∈ extensionBoundarySpace S T
    rw [hsnd, ← hfst]
    exact r.prop
  · intro q hq
    let r : extensionBoundarySpace S T := ⟨q, hq⟩
    refine ⟨e r, ?_⟩
    apply Prod.ext
    · rfl
    · exact recoveredIsometry_apply_fst S T hT r

/-- Exhaustion: the recovered parameter gives exactly T, including its domain. -/
theorem closedSymmetricExtension_recovered (S T : Operator ℂ H H)
    (hcS : IsClosed S) (hS : IsSymmetric S) (hcT : IsClosed T)
    (hT : IsSymmetric T) (hST : S ≤ T) :
    extensionValue S (recoveredParameter S T hS hcT hT) = T := by
  apply LinearPMap.eq_of_eq_graph
  have hg : graphSpace (extensionValue S (recoveredParameter S T hS hcT hT)) =
      graphSpace T := by
    rw [graphSpace_closedSymmetricExtension S hS,
      ← pairMap_parameter_range, recoveredParameter_pairSpace,
      ← graphSpace_extension_decomposition S T hcS hS hT hST]
  ext q
  exact (mem_graphSpace_iff _ q.1 q.2).symm.trans
    ((show WithLp.toLp 2 q ∈ graphSpace (extensionValue S (recoveredParameter S T hS hcT hT)) ↔
      WithLp.toLp 2 q ∈ graphSpace T from by rw [hg]).trans (mem_graphSpace_iff T q.1 q.2))

/-- No nonzero base graph component can occur in a sum of defect graphs. -/
theorem extensionBoundarySpace_parameter (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) :
    extensionBoundarySpace S (extensionValue S p) = parameterPairSpace S p := by
  apply le_antisymm
  · intro q hq
    change deficiencyPairMap S q ∈ graphSpace (extensionValue S p) at hq
    rw [graphSpace_closedSymmetricExtension S hS p] at hq
    obtain ⟨s, hs, _, ⟨u, rfl⟩, he⟩ := Submodule.mem_sup.mp hq
    have hp : deficiencyPairMap S q ∈ defectSpace S Complex.I ⊔ defectSpace S (-Complex.I) := by
      rw [deficiencyPairMap_eq_sum]
      exact Submodule.mem_sup.mpr ⟨_, deficiencyGraphMap_mem S Complex.I q.1,
        _, deficiencyGraphMap_mem S (-Complex.I) q.2, rfl⟩
    have hs' : s ∈ defectSpace S Complex.I ⊔ defectSpace S (-Complex.I) := by
      have hm := (defectSpace S Complex.I ⊔ defectSpace S (-Complex.I)).sub_mem hp
        (extensionGraphMap_mem_defect_sup S p u)
      rwa [← he, add_sub_cancel_right] at hm
    have ho := (Submodule.isOrtho_sup_right.mpr
      ⟨graphSpace_ortho_defectSpace S hS.1 Complex.I (by simp),
        graphSpace_ortho_defectSpace S hS.1 (-Complex.I) (by simp)⟩).inner_eq hs hs'
    have hz : s = 0 := inner_self_eq_zero.mp ho
    rw [hz, zero_add] at he
    have hpair : deficiencyPairMap S (u.val, p.isometry u) = deficiencyPairMap S q := (deficiencyPairMap_parameter S p u).trans he
    have hqu := deficiencyPairMap_injective S hpair
    exact ⟨u, hqu⟩
  · rintro q ⟨u, rfl⟩
    change deficiencyPairMap S (u.val, p.isometry u) ∈ graphSpace (extensionValue S p)
    rw [deficiencyPairMap_parameter, graphSpace_closedSymmetricExtension S hS p]
    exact (show (extensionGraphMap S p).range ≤
      graphSpace S ⊔ (extensionGraphMap S p).range from le_sup_right) ⟨u, rfl⟩

/-- Equality of the isometry graphs includes equality of the initial subspaces. -/
theorem ExtensionParameter.ext_pairSpace (S : Operator ℂ H H) (p q : ExtensionParameter S)
    (he : parameterPairSpace S p = parameterPairSpace S q) : p = q := by
  have hd : p.initialSpace = q.initialSpace := by
    apply le_antisymm
    · intro u hu
      have hm : (u, p.isometry ⟨u, hu⟩) ∈ parameterPairSpace S p := ⟨⟨u, hu⟩, rfl⟩
      rw [he] at hm
      obtain ⟨v, hv⟩ := hm
      have hvu : v.val = u := congrArg Prod.fst hv
      exact hvu ▸ v.prop
    · intro u hu
      have hm : (u, q.isometry ⟨u, hu⟩) ∈ parameterPairSpace S q := ⟨⟨u, hu⟩, rfl⟩
      rw [← he] at hm
      obtain ⟨v, hv⟩ := hm
      have hvu : v.val = u := congrArg Prod.fst hv
      exact hvu ▸ v.prop
  cases p with
  | mk L hL W =>
    cases q with
    | mk M hM V =>
      dsimp only at hd
      subst M
      have hWV : W = V := by
        apply LinearIsometry.ext
        intro u
        have hm : (u.val, W u) ∈ parameterPairSpace S ⟨L, hL, W⟩ := ⟨u, rfl⟩
        rw [he] at hm
        obtain ⟨v, hv⟩ := hm
        have hvu : v = u := Subtype.ext (congrArg Prod.fst hv)
        exact ((congrArg Prod.snd hv).symm.trans (congrArg V hvu))
      subst V
      rfl

/-- Uniqueness is equality of the complete parameter, not just of dimensions. -/
theorem closedSymmetricExtension_injective (S : Operator ℂ H H) (hS : IsSymmetric S) :
    Function.Injective (extensionValue S) := by
  intro p q he
  apply ExtensionParameter.ext_pairSpace S p q
  rw [← extensionBoundarySpace_parameter S hS p,
    ← extensionBoundarySpace_parameter S hS q, he]

theorem closedSymmetricExtension_classification : ClassificationExpected := by
  intro H _ _ _ S hcS hS T hcT hT hST
  refine ⟨recoveredParameter S T hS hcT hT,
    closedSymmetricExtension_recovered S T hcS hS hcT hT hST, ?_⟩
  intro q hq
  apply closedSymmetricExtension_injective S hS
  rw [hq, closedSymmetricExtension_recovered S T hcS hS hcT hT hST]

/-- Taking z times the first graph coordinate minus the second gives zI−A. -/
def graphShiftMap (z : ℂ) : WithLp 2 (H × H) →ₗ[ℂ] H :=
  (z • WithLp.fstL 2 ℂ H H - WithLp.sndL 2 ℂ H H).toLinearMap

omit [CompleteSpace H] in
theorem range_shift_graphSpace (A : Operator ℂ H H) (z : ℂ) :
    range (shift z A) = (graphSpace A).map (graphShiftMap z) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨WithLp.toLp 2 ((x : H), A x),
      (mem_graphSpace_iff A _ _).mpr (A.mem_graph x), rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨⟨x, a⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective g
    obtain ⟨v, hv, ha⟩ := A.mem_graph_iff.mp ((mem_graphSpace_iff A _ _).mp hg)
    refine ⟨v, ?_⟩
    change z • (v : H) - A v = z • x - a
    rw [hv, ha]

/-- Ran(S_W+i) and Ran(S_W−i) add precisely the chosen initial and final spaces. -/
theorem closedSymmetricExtension_signed_ranges (S : Operator ℂ H H) (hS : IsSymmetric S)
    (p : ExtensionParameter S) :
    range (shift (-Complex.I) (extensionValue S p)) = range (shift (-Complex.I) S) ⊔
      p.initialSpace.map (SymmetryAndDeficienciesSpec.deficiencyPlusValue S).subtype ∧
    range (shift Complex.I (extensionValue S p)) = range (shift Complex.I S) ⊔
      p.isometry.toLinearMap.range.map
        (SymmetryAndDeficienciesSpec.deficiencyMinusValue S).subtype := by
  have hp : (graphShiftMap (-Complex.I)).comp (extensionGraphMap S p) =
      (-2 * Complex.I) •
        ((SymmetryAndDeficienciesSpec.deficiencyPlusValue S).subtype.comp p.initialSpace.subtype) := by
    ext u
    rw [LinearMap.comp_apply, extensionGraphMap_apply]
    change (-Complex.I) • ((u.val : H) + (p.isometry u : H)) -
        (Complex.I • (u.val : H) - Complex.I • (p.isometry u : H)) =
      (-2 * Complex.I) • (u.val : H)
    module
  have hm : (graphShiftMap Complex.I).comp (extensionGraphMap S p) =
      (2 * Complex.I) •
        ((SymmetryAndDeficienciesSpec.deficiencyMinusValue S).subtype.comp p.isometry.toLinearMap) := by
    ext u
    rw [LinearMap.comp_apply, extensionGraphMap_apply]
    change Complex.I • ((u.val : H) + (p.isometry u : H)) -
        (Complex.I • (u.val : H) - Complex.I • (p.isometry u : H)) =
      (2 * Complex.I) • (p.isometry u : H)
    module
  constructor
  · rw [range_shift_graphSpace, graphSpace_closedSymmetricExtension S hS p,
      Submodule.map_sup, ← range_shift_graphSpace, ← LinearMap.range_comp, hp,
      LinearMap.range_smul _ _ (mul_ne_zero (by norm_num) Complex.I_ne_zero),
      LinearMap.range_comp, Submodule.range_subtype]
  · rw [range_shift_graphSpace, graphSpace_closedSymmetricExtension S hS p,
      Submodule.map_sup, ← range_shift_graphSpace, ← LinearMap.range_comp, hm,
      LinearMap.range_smul _ _ (mul_ne_zero (by norm_num) Complex.I_ne_zero),
      LinearMap.range_comp]

/-- Inside N, adding N⊥ fills H precisely when the chosen subspace is all N. -/
theorem orthogonal_sup_map_eq_top_iff (N : Submodule ℂ H)
    (hN : _root_.IsClosed (N : Set H)) (L : Submodule ℂ N) :
    N.orthogonal ⊔ L.map N.subtype = ⊤ ↔ L = ⊤ := by
  let : CompleteSpace N := hN.isComplete.completeSpace_coe
  constructor
  · intro he
    apply top_unique
    intro u _
    have hm : (u : H) ∈ N.orthogonal ⊔ L.map N.subtype := by rw [he]; trivial
    obtain ⟨a, ha, b, ⟨v, hv, rfl⟩, hab⟩ := Submodule.mem_sup.mp hm
    have haN : a ∈ N := by
      have he' : a = (u : H) - (v : H) := eq_sub_of_add_eq hab
      rw [he']
      exact N.sub_mem u.prop v.prop
    have hz : a = 0 := inner_self_eq_zero.mp
      ((Submodule.isOrtho_orthogonal_left N).inner_eq ha haN)
    rw [hz, zero_add] at hab
    have hvu : v = u := Subtype.ext hab
    exact hvu ▸ hv
  · rintro rfl
    rw [Submodule.map_top, Submodule.range_subtype, sup_comm]
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- The self-adjoint parameters are exactly the unitary maps N₊→N₋. -/
theorem closedSymmetricExtension_selfAdjoint_iff : SelfAdjointExpected := by
  intro H _ _ _ S hc hS p
  have hcW := closedSymmetricExtension_isClosed S hc hS p
  have hW := closedSymmetricExtension_isSymmetric S hS p
  have hp := orthogonal_sup_map_eq_top_iff
    (SymmetryAndDeficienciesSpec.deficiencyPlusValue S)
    (deficiencySpace_isClosed S hS.1 Complex.I) p.initialSpace
  have hm := orthogonal_sup_map_eq_top_iff
    (SymmetryAndDeficienciesSpec.deficiencyMinusValue S)
    (deficiencySpace_isClosed S hS.1 (-Complex.I)) p.isometry.toLinearMap.range
  rw [show SymmetryAndDeficienciesSpec.selfAdjointValue (extensionValue S p) ↔
      IsSelfAdjoint (extensionValue S p) from Iff.rfl,
    closed_symmetric_selfAdjoint_iff_ranges _ hcW hW,
    (closedSymmetricExtension_signed_ranges S hS p).1,
    (closedSymmetricExtension_signed_ranges S hS p).2,
    (closed_symmetric_signed_ranges S hc hS).1,
    (closed_symmetric_signed_ranges S hc hS).2]
  exact hp.and (hm.trans LinearMap.range_eq_top)

section HilbertCardinality
variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {ι κ : Type u}

omit [CompleteSpace E] in
/-- An arbitrary Hilbert basis has at most the cardinality of any other one.
The infinite case uses countable orthonormal supports; the finite case uses
algebraic dimension only after the finite Hilbert basis is known to span. -/
theorem hilbertBasis_card_le (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) :
    Cardinal.mk ι ≤ Cardinal.mk κ := by
  classical
  cases finite_or_infinite κ with
  | inl hκ =>
    let : Fintype κ := Fintype.ofFinite κ
    exact b.orthonormal.linearIndependent.cardinal_le_rank.trans_eq
      c.toOrthonormalBasis.toBasis.mk_eq_rank''.symm
  | inr hκ =>
    let A : κ → Set ι := fun j => {i | inner ℂ (b i) (c j) ≠ 0}
    have hcount (j : κ) : (A j).Countable := by
      apply (b.summable_inner_mul_inner (c j) (c j)).countable_support.mono
      intro i hi
      change inner ℂ (c j) (b i) * inner ℂ (b i) (c j) ≠ 0
      change inner ℂ (b i) (c j) ≠ 0 at hi
      exact mul_ne_zero (fun h => hi (inner_eq_zero_symm.mp h)) hi
    have hcover : (⋃ j, A j) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro i
      have hn : c.repr (b i) ≠ 0 := by
        intro hz
        have hi : b i = 0 := c.repr.injective (hz.trans (map_zero c.repr).symm)
        exact b.orthonormal.ne_zero i hi
      obtain ⟨j, hj⟩ : ∃ j, c.repr (b i) j ≠ 0 := by
        by_contra h
        apply hn
        ext j
        exact not_not.mp (not_exists.mp h j)
      rw [c.repr_apply_apply] at hj
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      change inner ℂ (b i) (c j) ≠ 0
      exact fun h => hj (inner_eq_zero_symm.mp h)
    have hsup : (⨆ j, Cardinal.mk (A j)) ≤ (Cardinal.aleph0 : Cardinal.{u}) :=
      ciSup_le' fun j => (hcount j).le_aleph0
    calc
      Cardinal.mk ι = Cardinal.mk (Set.univ : Set ι) := Cardinal.mk_univ.symm
      _ = Cardinal.mk (⋃ j, A j) := by rw [hcover]
      _ ≤ Cardinal.mk κ * ⨆ j, Cardinal.mk (A j) := Cardinal.mk_iUnion_le A
      _ ≤ Cardinal.mk κ * Cardinal.aleph0 := mul_le_mul_right hsup (Cardinal.mk κ)
      _ = Cardinal.mk κ := Cardinal.mk_mul_aleph0_eq

omit [CompleteSpace E] in
theorem hilbertBasis_card_eq (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) :
    Cardinal.mk ι = Cardinal.mk κ :=
  le_antisymm (hilbertBasis_card_le b c) (hilbertBasis_card_le c b)

/-- Hilbert cardinal dimension is invariant under any linear isometric equivalence. -/
theorem hilbertDimension_eq_of_linearIsometryEquiv (e : E ≃ₗᵢ[ℂ] F) :
    SymmetryAndDeficienciesSpec.hilbertDimensionValue E =
      SymmetryAndDeficienciesSpec.hilbertDimensionValue F := by
  let b := (exists_hilbertBasis ℂ E).choose_spec.choose
  let c := (exists_hilbertBasis ℂ F).choose_spec.choose
  exact hilbertBasis_card_eq b (HilbertBasis.ofRepr (e.trans c.repr))

/-- Equal Hilbert cardinal dimensions give a unitary equivalence, even for
nonseparable spaces. No algebraic-rank comparison is used in the infinite case. -/
theorem exists_linearIsometryEquiv_of_hilbertDimension_eq
    (he : SymmetryAndDeficienciesSpec.hilbertDimensionValue E =
      SymmetryAndDeficienciesSpec.hilbertDimensionValue F) : Nonempty (E ≃ₗᵢ[ℂ] F) := by
  classical
  let b := (exists_hilbertBasis ℂ E).choose_spec.choose
  let c := (exists_hilbertBasis ℂ F).choose_spec.choose
  obtain ⟨e⟩ := Cardinal.eq.mp he
  let v := fun i => c (e i)
  have hv : Orthonormal ℂ v := c.orthonormal.comp e e.injective
  have hr : Set.range v = Set.range c := e.surjective.range_comp _
  let d : HilbertBasis (exists_hilbertBasis ℂ E).choose ℂ F := HilbertBasis.mk hv (by
    rw [hr, c.dense_span])
  exact ⟨b.repr.trans d.repr.symm⟩

end HilbertCardinality

/-- Equal deficiency cardinalities, including arbitrary infinite cardinals,
are equivalent to existence of a self-adjoint extension. -/
theorem exists_selfAdjoint_extension_iff_deficiencyIndices_eq : ExistenceExpected := by
  intro H _ _ _ S hc hS
  let : CompleteSpace (SymmetryAndDeficienciesSpec.deficiencyPlusValue S) :=
    (deficiencySpace_isClosed S hS.1 Complex.I).isComplete.completeSpace_coe
  let : CompleteSpace (SymmetryAndDeficienciesSpec.deficiencyMinusValue S) :=
    (deficiencySpace_isClosed S hS.1 (-Complex.I)).isComplete.completeSpace_coe
  change (∃ T, S ≤ T ∧ SymmetryAndDeficienciesSpec.selfAdjointValue T) ↔
    SymmetryAndDeficienciesSpec.hilbertDimensionValue
      (SymmetryAndDeficienciesSpec.deficiencyPlusValue S) =
    SymmetryAndDeficienciesSpec.hilbertDimensionValue
      (SymmetryAndDeficienciesSpec.deficiencyMinusValue S)
  constructor
  · rintro ⟨T, hST, hT⟩
    have hcT : IsClosed T := by
      have he : T = hilbertAdjoint T := hT.2
      rw [he]
      exact hilbertAdjoint_isClosed T hT.1
    have hsT : IsSymmetric T := ⟨hT.1, (show T = hilbertAdjoint T from hT.2).le⟩
    obtain ⟨p, hp, _⟩ := closedSymmetricExtension_classification S hc hS T hcT hsT hST
    have hsW : SymmetryAndDeficienciesSpec.selfAdjointValue (extensionValue S p) := by
      rw [hp]; exact hT
    obtain ⟨hL, hW⟩ := (closedSymmetricExtension_selfAdjoint_iff S hc hS p).mp hsW
    let inc : SymmetryAndDeficienciesSpec.deficiencyPlusValue S →ₗᵢ[ℂ] p.initialSpace :=
      { toLinearMap :=
          { toFun := fun u => ⟨u, by rw [hL]; trivial⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        norm_map' := fun _ => rfl }
    let U := p.isometry.comp inc
    have hU : Function.Surjective U := by
      intro v
      obtain ⟨u, hu⟩ := hW v
      exact ⟨u.val, hu⟩
    exact hilbertDimension_eq_of_linearIsometryEquiv (LinearIsometryEquiv.ofSurjective U hU)
  · intro he
    obtain ⟨e⟩ := exists_linearIsometryEquiv_of_hilbertDimension_eq he
    let W : (⊤ : Submodule ℂ (SymmetryAndDeficienciesSpec.deficiencyPlusValue S)) →ₗᵢ[ℂ]
        SymmetryAndDeficienciesSpec.deficiencyMinusValue S :=
      { toLinearMap := e.toLinearEquiv.toLinearMap.comp (⊤ : Submodule ℂ
          (SymmetryAndDeficienciesSpec.deficiencyPlusValue S)).subtype
        norm_map' := fun u => e.norm_map u.val }
    let p : ExtensionParameter S :=
      { initialSpace := ⊤
        closed_initialSpace := isClosed_univ
        isometry := W }
    have hW : Function.Surjective p.isometry := by
      intro v
      exact ⟨⟨e.symm v, trivial⟩, e.apply_symm_apply v⟩
    exact ⟨extensionValue S p, le_closedSymmetricExtension S hS p,
      (closedSymmetricExtension_selfAdjoint_iff S hc hS p).mpr ⟨rfl, hW⟩⟩

end ExpandedFA.Unbounded
