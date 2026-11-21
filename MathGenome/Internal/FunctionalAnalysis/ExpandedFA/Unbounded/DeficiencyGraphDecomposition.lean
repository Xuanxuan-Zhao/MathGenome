import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.DeficiencyGraphDecomposition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosabilityAndDoubleAdjoint
import Mathlib.Tactic.Module

/-! Von Neumann's decomposition, paper.tex:13687–13704. Project onto G(S)
in H ⊕₂ H. For a residual (x,a), orthogonality gives (a,-x) ∈ G(S*),
so its ±i parts are half of (x,a) ∓ i(a,-x). This proves spanning directly,
without assuming closedness of a sum of subspaces. -/
noncomputable section
universe u
namespace ExpandedFA.Unbounded
open DeficiencyGraphDecompositionSpec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem mem_graphSpace_iff (A : Operator ℂ H H) (x b : H) :
    WithLp.toLp 2 (x, b) ∈ graphSpace A ↔ (x, b) ∈ A.graph := by
  rw [graphSpace, Submodule.mem_map_equiv]
  rfl

omit [CompleteSpace H] in
theorem graphSpace_isClosed (A : Operator ℂ H H) (hA : IsClosed A) :
    _root_.IsClosed (graphSpace A : Set (WithLp 2 (H × H))) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toHomeomorph.isClosedMap _ hA

theorem mem_defectSpace_iff (S : Operator ℂ H H) (z : ℂ) (x b : H) :
    WithLp.toLp 2 (x, b) ∈ defectSpace S z ↔
      x ∈ deficiencySpace S z ∧ b = z • x := by
  change (WithLp.toLp 2 (x, b) ∈ graphSpace (hilbertAdjoint S) ∧ _) ↔ _
  rw [mem_graphSpace_iff]
  rw [show (x, b) ∈ (hilbertAdjoint S).graph ↔
    ∃ hx, hilbertAdjoint S ⟨x, hx⟩ = b from mem_graph_iff (hilbertAdjoint S) (x, b),
    mem_deficiencySpace_iff]
  change ((∃ hx, hilbertAdjoint S ⟨x, hx⟩ = b) ∧ b - z • x = 0) ↔ _
  simp only [sub_eq_zero]
  constructor
  · rintro ⟨⟨hx, hxb⟩, hb⟩
    exact ⟨⟨hx, hxb.trans hb⟩, hb⟩
  · rintro ⟨⟨hx, hxz⟩, rfl⟩
    exact ⟨⟨hx, hxz⟩, rfl⟩

theorem defectSpace_isClosed (S : Operator ℂ H H) (hS : DenselyDefined S) (z : ℂ) :
    _root_.IsClosed (defectSpace S z : Set (WithLp 2 (H × H))) :=
  (graphSpace_isClosed _ (hilbertAdjoint_isClosed S hS)).inter
    (WithLp.sndL 2 ℂ H H - z • WithLp.fstL 2 ℂ H H).isClosed_ker

omit [CompleteSpace H] in
theorem hilbert_graph_inner (A : Operator ℂ H H) (x y : A.domain) :
    inner ℂ (WithLp.toLp 2 ((x : H), A x)) (WithLp.toLp 2 ((y : H), A y)) =
      inner ℂ (x : H) (y : H) + inner ℂ (A x) (A y) := rfl

omit [CompleteSpace H] in
theorem hilbert_graph_norm_sq (A : Operator ℂ H H) (x : A.domain) :
    ‖WithLp.toLp 2 ((x : H), A x)‖ ^ 2 = ‖(x : H)‖ ^ 2 + ‖A x‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

omit [CompleteSpace H] in
theorem hilbert_graph_norm_equiv (A : Operator ℂ H H) (x : A.domain) :
    ‖WithLp.toLp 2 ((x : H), A x)‖ ≤ graphNorm A x ∧
    graphNorm A x ≤ 2 * ‖WithLp.toLp 2 ((x : H), A x)‖ := by
  change ‖WithLp.toLp 2 ((x : H), A x)‖ ≤ ‖(x : H)‖ + ‖A x‖ ∧
    ‖(x : H)‖ + ‖A x‖ ≤ 2 * ‖WithLp.toLp 2 ((x : H), A x)‖
  constructor
  · have hn := hilbert_graph_norm_sq A x
    nlinarith [norm_nonneg (WithLp.toLp 2 ((x : H), A x)), norm_nonneg (x : H),
      norm_nonneg (A x), mul_nonneg (norm_nonneg (x : H)) (norm_nonneg (A x))]
  · have hx := WithLp.norm_fst_le (p := 2) H (WithLp.toLp 2 ((x : H), A x))
    have ha := WithLp.norm_snd_le (p := 2) H (WithLp.toLp 2 ((x : H), A x))
    change ‖(x : H)‖ ≤ _ at hx
    change ‖A x‖ ≤ _ at ha
    linarith

omit [CompleteSpace H] in
theorem exists_graphDomain_equiv (A : Operator ℂ H H) :
    ∃ e : GraphDomain A ≃L[ℂ] graphSpace A, ∀ x : GraphDomain A,
      (e x : WithLp 2 (H × H)) = WithLp.toLp 2
        ((GraphDomain.toDomain A x : H), A (GraphDomain.toDomain A x)) := by
  let f : GraphDomain A →ₗ[ℂ] graphSpace A :=
    { toFun := fun x => ⟨WithLp.toLp 2
        ((GraphDomain.toDomain A x : H), A (GraphDomain.toDomain A x)),
        (mem_graphSpace_iff A _ _).mpr (A.mem_graph _)⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change WithLp.toLp 2
          (((GraphDomain.toDomain A x + GraphDomain.toDomain A y : A.domain) : H),
            A (GraphDomain.toDomain A x + GraphDomain.toDomain A y)) = _
        rw [A.map_add]
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        change WithLp.toLp 2
          (((c • GraphDomain.toDomain A x : A.domain) : H),
            A (c • GraphDomain.toDomain A x)) = _
        rw [A.map_smul]
        rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      exact congrArg (fun g : graphSpace A => (g : WithLp 2 (H × H)).fst) he
    · intro g
      obtain ⟨p, hp, hpg⟩ := Submodule.mem_map.mp g.prop
      obtain ⟨v, hv, hb⟩ := A.mem_graph_iff.mp hp
      refine ⟨v, Subtype.ext ?_⟩
      change WithLp.toLp 2 ((v : H), A v) = (g : WithLp 2 (H × H))
      calc
        _ = WithLp.toLp 2 p := congrArg (WithLp.toLp 2) (Prod.ext hv hb)
        _ = _ := hpg
  let e := LinearEquiv.ofBijective f hf
  refine ⟨e.toContinuousLinearEquivOfBounds 1 2 ?_ ?_, fun _ => rfl⟩
  · intro x
    change ‖WithLp.toLp 2 ((GraphDomain.toDomain A x : H), A (GraphDomain.toDomain A x))‖ ≤
      1 * (‖(GraphDomain.toDomain A x : H)‖ + ‖A (GraphDomain.toDomain A x)‖)
    rw [one_mul]
    exact (hilbert_graph_norm_equiv A (GraphDomain.toDomain A x)).1
  · intro y
    have h := (hilbert_graph_norm_equiv A (GraphDomain.toDomain A (e.symm y))).2
    change ‖e.symm y‖ ≤ 2 * ‖e (e.symm y)‖ at h
    simpa only [e.apply_symm_apply] using h

/-- Graph orthogonality uses the adjoint equation and z² = -1. -/
theorem graphSpace_ortho_defectSpace (S : Operator ℂ H H) (hS : DenselyDefined S)
    (z : ℂ) (hz : z * z = -1) : (graphSpace S).IsOrtho (defectSpace S z) := by
  apply Submodule.isOrtho_iff_inner_eq.mpr
  intro g hg k hk
  obtain ⟨⟨x, a⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective g
  obtain ⟨⟨y, b⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective k
  obtain ⟨v, hv, ha⟩ := S.mem_graph_iff.mp ((mem_graphSpace_iff S x a).mp hg)
  change (v : H) = x at hv
  change S v = a at ha
  obtain ⟨hy, rfl⟩ := (mem_defectSpace_iff S z y b).mp hk
  obtain ⟨hy, he⟩ := (mem_deficiencySpace_iff S z y).mp hy
  have hi := hilbertAdjoint_inner S hS ⟨y, hy⟩ v
  rw [he, inner_smul_right] at hi
  change inner ℂ x y + inner ℂ a (z • y) = 0
  rw [← hv, ← ha, inner_smul_right, hi, ← mul_assoc, hz]
  simp

theorem defectSpace_plus_ortho_minus (S : Operator ℂ H H) :
    (defectSpace S Complex.I).IsOrtho (defectSpace S (-Complex.I)) := by
  apply Submodule.isOrtho_iff_inner_eq.mpr
  intro g hg k hk
  obtain ⟨⟨x, a⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective g
  obtain ⟨⟨y, b⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective k
  have ha := ((mem_defectSpace_iff S Complex.I x a).mp hg).2
  have hb := ((mem_defectSpace_iff S (-Complex.I) y b).mp hk).2
  change inner ℂ x y + inner ℂ a b = 0
  rw [ha, hb, inner_smul_left, inner_smul_right, ← mul_assoc]
  simp

theorem graphSpace_le_adjoint {S : Operator ℂ H H} (hS : IsSymmetric S) :
    graphSpace S ≤ graphSpace (hilbertAdjoint S) := by
  apply Submodule.map_mono
  exact LinearPMap.le_graph_of_le hS.2

/-- In the orthogonal residual, the adjoint maps (x,a) to (a,-x). -/
theorem residual_rotated_mem (S : Operator ℂ H H) (hS : DenselyDefined S)
    (x a : H) (h : WithLp.toLp 2 (x, a) ∈ (graphSpace S).orthogonal) :
    WithLp.toLp 2 (a, -x) ∈ graphSpace (hilbertAdjoint S) := by
  rw [mem_graphSpace_iff, mem_hilbertAdjoint_graph_iff S hS]
  intro v
  have ht := h (WithLp.toLp 2 ((v : H), S v))
    ((mem_graphSpace_iff S _ _).mpr (S.mem_graph_iff.mpr ⟨v, rfl, rfl⟩))
  change inner ℂ (v : H) x + inner ℂ (S v) a = 0 at ht
  rw [inner_neg_right]
  exact eq_neg_of_add_eq_zero_right ht

theorem residual_mem_defect_sup (S : Operator ℂ H H) (hS : DenselyDefined S)
    (g : WithLp 2 (H × H)) (hg : g ∈ graphSpace (hilbertAdjoint S))
    (ho : g ∈ (graphSpace S).orthogonal) :
    g ∈ defectSpace S Complex.I ⊔ defectSpace S (-Complex.I) := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (WithLp.linearEquiv 2 ℂ (H × H)).symm.surjective g
  let g := WithLp.toLp 2 (x, a)
  let r := WithLp.toLp 2 (a, -x)
  have hr : r ∈ graphSpace (hilbertAdjoint S) := residual_rotated_mem S hS x a ho
  let p := (1 / 2 : ℂ) • (g - Complex.I • r)
  let q := (1 / 2 : ℂ) • (g + Complex.I • r)
  have hp : p ∈ defectSpace S Complex.I := by
    refine ⟨(graphSpace _).smul_mem _ ((graphSpace _).sub_mem hg
      ((graphSpace _).smul_mem _ hr)), ?_⟩
    change p.snd - Complex.I • p.fst = 0
    dsimp [p, g, r]
    simp only [smul_sub, smul_neg, smul_smul]
    match_scalars <;> ring_nf
    all_goals simp
  have hq : q ∈ defectSpace S (-Complex.I) := by
    refine ⟨(graphSpace _).smul_mem _ ((graphSpace _).add_mem hg
      ((graphSpace _).smul_mem _ hr)), ?_⟩
    change q.snd - (-Complex.I) • q.fst = 0
    dsimp [q, g, r]
    simp only [smul_add, smul_neg, smul_smul]
    match_scalars <;> ring_nf
    all_goals simp
  apply Submodule.mem_sup.mpr
  refine ⟨p, hp, q, hq, ?_⟩
  change (1 / 2 : ℂ) • (g - Complex.I • r) + (1 / 2 : ℂ) • (g + Complex.I • r) = g
  module

theorem adjoint_graph_eq_sup (S : Operator ℂ H H) (hc : IsClosed S) (hS : IsSymmetric S) :
    graphSpace (hilbertAdjoint S) =
      graphSpace S ⊔ defectSpace S Complex.I ⊔ defectSpace S (-Complex.I) := by
  apply le_antisymm
  · intro g hg
    let : CompleteSpace (graphSpace S) :=
      (graphSpace_isClosed S hc).isComplete.completeSpace_coe
    obtain ⟨s, hs, r, hr, he⟩ := (graphSpace S).exists_add_mem_mem_orthogonal g
    have hrg : r ∈ graphSpace (hilbertAdjoint S) := by
      have hm := (graphSpace _).sub_mem hg (graphSpace_le_adjoint hS hs)
      rwa [he, add_sub_cancel_left] at hm
    rw [sup_assoc]
    exact Submodule.mem_sup.mpr
      ⟨s, hs, r, residual_mem_defect_sup S hS.1 r hrg hr, he.symm⟩
  · exact sup_le (sup_le (graphSpace_le_adjoint hS) inf_le_left) inf_le_left

/-- Von Neumann's graph-orthogonal direct decomposition, with closed summands. -/
theorem deficiency_graph_decomposition : DecompositionExpected := by
  intro H _ _ _ S hc hS
  change IsSymmetric S at hS
  exact ⟨adjoint_graph_eq_sup S hc hS,
    graphSpace_ortho_defectSpace S hS.1 Complex.I (by simp),
    graphSpace_ortho_defectSpace S hS.1 (-Complex.I) (by simp),
    defectSpace_plus_ortho_minus S,
    (Submodule.isOrtho_sup_right.mpr
      ⟨graphSpace_ortho_defectSpace S hS.1 Complex.I (by simp),
        graphSpace_ortho_defectSpace S hS.1 (-Complex.I) (by simp)⟩).disjoint,
    (defectSpace_plus_ortho_minus S).disjoint,
    graphSpace_isClosed S hc,
    defectSpace_isClosed S hS.1 Complex.I,
    defectSpace_isClosed S hS.1 (-Complex.I),
    graphSpace_isClosed _ (hilbertAdjoint_isClosed S hS.1)⟩

/-- All three domains are closed also for the canonical sum graph norm. -/
theorem deficiency_graph_closed_summands : ClosedSummandsExpected := by
  intro H _ _ _ S hc hS
  change IsSymmetric S at hS
  obtain ⟨e, he⟩ := exists_graphDomain_equiv (hilbertAdjoint S)
  have hcont : Continuous (fun x : GraphDomain (hilbertAdjoint S) =>
      (e x : WithLp 2 (H × H))) := continuous_subtype_val.comp e.continuous
  have hbase : {x : GraphDomain (hilbertAdjoint S) |
      (GraphDomain.toDomain _ x : H) ∈ S.domain} =
      (fun x => (e x : WithLp 2 (H × H))) ⁻¹' (graphSpace S : Set _) := by
    ext x
    change (GraphDomain.toDomain _ x : H) ∈ S.domain ↔ (e x : WithLp 2 (H × H)) ∈ graphSpace S
    rw [he x, mem_graphSpace_iff]
    constructor
    · intro hx
      exact S.mem_graph_iff.mpr ⟨⟨_, hx⟩, rfl, hS.2.2 rfl⟩
    · intro hx
      obtain ⟨v, hv, _⟩ := S.mem_graph_iff.mp hx
      change (v : H) = (GraphDomain.toDomain _ x : H) at hv
      rw [← hv]
      exact v.prop
  have hdef (z : ℂ) : {x : GraphDomain (hilbertAdjoint S) |
      (GraphDomain.toDomain _ x : H) ∈ deficiencySpace S z} =
      (fun x => (e x : WithLp 2 (H × H))) ⁻¹' (defectSpace S z : Set _) := by
    ext x
    change (GraphDomain.toDomain _ x : H) ∈ deficiencySpace S z ↔
      (e x : WithLp 2 (H × H)) ∈ defectSpace S z
    rw [he x, mem_defectSpace_iff]
    constructor
    · intro hx
      obtain ⟨_, hz⟩ := (mem_deficiencySpace_iff S z _).mp hx
      exact ⟨hx, hz⟩
    · exact fun hx => hx.1
  refine ⟨?_, ?_, ?_⟩
  · change _root_.IsClosed {x : GraphDomain (hilbertAdjoint S) |
      (GraphDomain.toDomain _ x : H) ∈ S.domain}
    rw [hbase]
    exact (graphSpace_isClosed S hc).preimage hcont
  · change _root_.IsClosed {x : GraphDomain (hilbertAdjoint S) |
      (GraphDomain.toDomain _ x : H) ∈ deficiencySpace S Complex.I}
    rw [hdef]
    exact (defectSpace_isClosed S hS.1 Complex.I).preimage hcont
  · change _root_.IsClosed {x : GraphDomain (hilbertAdjoint S) |
      (GraphDomain.toDomain _ x : H) ∈ deficiencySpace S (-Complex.I)}
    rw [hdef]
    exact (defectSpace_isClosed S hS.1 (-Complex.I)).preimage hcont

end ExpandedFA.Unbounded
