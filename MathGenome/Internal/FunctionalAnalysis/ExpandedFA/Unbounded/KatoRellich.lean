import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.KatoRellich
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SelfAdjointRangeCriterion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Positivity

noncomputable section
universe u
namespace ExpandedFA.Unbounded
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inner-product characterization with the manuscript's density convention. -/
theorem isSymmetric_of_inner (S : Operator ℂ H H) (hd : DenselyDefined S)
    (hi : ∀ x y : S.domain, inner ℂ (S x) (y : H) = inner ℂ (x : H) (S y)) :
    IsSymmetric S := by
  refine ⟨hd, ?_⟩
  apply LinearPMap.IsFormalAdjoint.le_adjoint (hT := hd)
  intro x y
  exact hi x y

/-- Self-adjointness supplies closedness without an extra assumption. -/
theorem IsSelfAdjoint.isClosed_operator {A : Operator ℂ H H} (hA : IsSelfAdjoint A) :
    IsClosed A := by
  have he : A = hilbertAdjoint A := hA.2
  rw [he]
  exact hilbertAdjoint_isClosed A hA.1

theorem IsSelfAdjoint.isSymmetric_operator {A : Operator ℂ H H} (hA : IsSelfAdjoint A) :
    IsSymmetric A := ⟨hA.1, hA.2.le⟩

/-- All nonreal shifts of a self-adjoint operator are onto. -/
theorem IsSelfAdjoint.shift_range {A : Operator ℂ H H} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) : range (shift z A) = ⊤ := by
  rw [closed_symmetric_shift_range A hA.isClosed_operator hA.isSymmetric_operator z hz,
    hA.deficiencySpace_eq_bot _ (by simpa using hz), Submodule.bot_orthogonal_eq_top]

/-- The exact linear inverse of zI−A, before any continuity assertion. -/
def IsSelfAdjoint.shiftEquiv {A : Operator ℂ H H} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) : A.domain ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective (shift z A).toFun ⟨by
    intro x y hxy
    have h := hA.isSymmetric_operator.nonreal_lower_bound z (x - y)
    have he : A (x - y) - z • ((x - y : A.domain) : H) = 0 := by
      have hh := (shift z A).map_sub x y
      change (shift z A) x = (shift z A) y at hxy
      rw [hxy, sub_self] at hh
      change z • ((x - y : A.domain) : H) - A (x - y) = 0 at hh
      exact (sub_eq_zero.mp hh).symm ▸ sub_self _
    rw [he, norm_zero] at h
    have hp : 0 < |z.im| := abs_pos.mpr hz
    have hn : ‖((x - y : A.domain) : H)‖ = 0 := by nlinarith [norm_nonneg ((x - y : A.domain) : H)]
    exact sub_eq_zero.mp (Subtype.ext (norm_eq_zero.mp hn)), by
    intro y
    have hm : y ∈ range (shift z A) := by rw [hA.shift_range z hz]; trivial
    exact hm⟩

/-- Purely imaginary parameters control both coordinates of the inverse graph. -/
theorem IsSelfAdjoint.imaginary_shift_bounds {A : Operator ℂ H H} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.re = 0) (x : A.domain) :
    ‖A x‖ ≤ ‖(shift z A) x‖ ∧
      |z.im| * ‖(x : H)‖ ≤ ‖(shift z A) x‖ := by
  change ‖A x‖ ≤ ‖z • (x : H) - A x‖ ∧
    |z.im| * ‖(x : H)‖ ≤ ‖z • (x : H) - A x‖
  have h := hA.isSymmetric_operator.norm_sub_sq z x
  rw [hz, Complex.ofReal_zero, zero_smul, sub_zero, norm_sub_rev] at h
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [mul_nonneg (sq_nonneg |z.im|) (sq_nonneg ‖(x : H)‖)]
  · simpa only [norm_sub_rev] using hA.isSymmetric_operator.nonreal_lower_bound z x

/-- Symmetric sums retain exactly the common domain. -/
theorem symmetric_add_of_domain_le (A B : Operator ℂ H H)
    (hA : IsSymmetric A) (hB : IsSymmetric B) (hD : A.domain ≤ B.domain) :
    IsSymmetric (A + B) := by
  apply isSymmetric_of_inner
  · change Dense ((A.domain ⊓ B.domain : Submodule ℂ H) : Set H)
    simpa only [inf_eq_left.mpr hD] using hA.1
  · intro x y
    change inner ℂ (A ⟨x, x.prop.1⟩ + B ⟨x, x.prop.2⟩) (y : H) =
      inner ℂ (x : H) (A ⟨y, y.prop.1⟩ + B ⟨y, y.prop.2⟩)
    rw [inner_add_left, inner_add_right]
    exact congrArg₂ (· + ·)
      (hA.inner_map ⟨x, x.prop.1⟩ ⟨y, y.prop.1⟩)
      (hB.inner_map ⟨x, x.prop.2⟩ ⟨y, y.prop.2⟩)

/-- A relative bound smaller than one makes the imaginary shifts of the sum onto. -/
theorem relative_sum_shift_range (A B : Operator ℂ H H)
    (hA : IsSelfAdjoint A) (hD : A.domain ≤ B.domain)
    (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hb : ∀ x : A.domain, ‖B ⟨x, hD x.prop⟩‖ ≤ a * ‖A x‖ + b * ‖(x : H)‖)
    (z : ℂ) (hzre : z.re = 0) (hz : z.im ≠ 0)
    (hsmall : a + b / |z.im| < 1) : range (shift z (A + B)) = ⊤ := by
  let e := hA.shiftEquiv z hz
  let T : H →ₗ[ℂ] H :=
    B.toFun.comp ((Submodule.inclusion hD).comp e.symm.toLinearMap)
  have he (y : H) : (shift z A) (e.symm y) = y := e.apply_symm_apply y
  have hT (y : H) : ‖T y‖ ≤ (a + b / |z.im|) * ‖y‖ := by
    have hh := hA.imaginary_shift_bounds z hzre (e.symm y)
    rw [he] at hh
    have hx : ‖((e.symm y : A.domain) : H)‖ ≤ ‖y‖ / |z.im| :=
      (le_div_iff₀ (abs_pos.mpr hz)).mpr (by simpa only [mul_comm] using hh.2)
    calc
      ‖T y‖ ≤ a * ‖A (e.symm y)‖ + b * ‖((e.symm y : A.domain) : H)‖ := hb _
      _ ≤ a * ‖y‖ + b * (‖y‖ / |z.im|) :=
        add_le_add (mul_le_mul_of_nonneg_left hh.1 ha0)
          (mul_le_mul_of_nonneg_left hx hb0)
      _ = (a + b / |z.im|) * ‖y‖ := by ring
  let C : H →L[ℂ] H := T.mkContinuous (a + b / |z.im|) hT
  have hn : ‖C‖ < 1 :=
    (C.opNorm_le_bound (by positivity) hT).trans_lt hsmall
  let U := Units.oneSub C hn
  apply top_unique
  intro y _
  let w := ((↑U⁻¹ : H →L[ℂ] H) y)
  have hw : w - C w = y := by
    have h' := congrArg (fun f : H →L[ℂ] H => f y) U.mul_inv
    have hu : (U : H →L[ℂ] H) = 1 - C := Units.val_oneSub _ _
    change (U : H →L[ℂ] H) w = y at h'
    rw [hu] at h'
    exact h'
  refine ⟨⟨(e.symm w : H), (e.symm w).prop, hD (e.symm w).prop⟩, ?_⟩
  change z • (e.symm w : H) -
    (A (e.symm w) + B ⟨e.symm w, hD (e.symm w).prop⟩) = y
  have hew : z • (e.symm w : H) - A (e.symm w) = w := he w
  change w - B ⟨e.symm w, hD (e.symm w).prop⟩ = y at hw
  calc
    _ = (z • (e.symm w : H) - A (e.symm w)) -
        B ⟨e.symm w, hD (e.symm w).prop⟩ := by abel
    _ = w - B ⟨e.symm w, hD (e.symm w).prop⟩ := congrArg (· - _) hew
    _ = y := hw

/-- Kato–Rellich on precisely D(A), including arbitrary real a,b as in the source. -/
theorem kato_rellich : KatoRellichSpec.KatoRellich.{u} := by
  intro H _ _ _ A B hA hB hD a b ha hb
  have hsa : IsSelfAdjoint A := hA
  have hsb : IsSymmetric B := hB
  let α := max a 0
  let β := max b 0
  have hα : 0 ≤ α := le_max_right _ _
  have hβ : 0 ≤ β := le_max_right _ _
  have hα1 : α < 1 := max_lt ha zero_lt_one
  have hbound (x : A.domain) : ‖B ⟨x, hD x.prop⟩‖ ≤ α * ‖A x‖ + β * ‖(x : H)‖ :=
    (hb x).trans (add_le_add
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  obtain ⟨L, hL⟩ := exists_gt (max 0 (β / (1 - α)))
  have hL0 : 0 < L := (le_max_left _ _).trans_lt hL
  have hsmall : α + β / L < 1 := by
    have h := (div_lt_iff₀ (sub_pos.mpr hα1)).mp ((le_max_right _ _).trans_lt hL)
    have hh : β / L < 1 - α := (div_lt_iff₀ hL0).mpr (by nlinarith)
    linarith
  let z : ℂ := (L : ℂ) * Complex.I
  have hzre : z.re = 0 := by simp [z]
  have hzim : z.im = L := by simp [z]
  have hz : z.im ≠ 0 := by rw [hzim]; exact ne_of_gt hL0
  have hr : range (shift z (A + B)) = ⊤ :=
    relative_sum_shift_range A B hsa hD α β hα hβ hbound z hzre hz
      (by simpa only [hzim, abs_of_pos hL0] using hsmall)
  have hrc : range (shift (starRingEnd ℂ z) (A + B)) = ⊤ :=
    relative_sum_shift_range A B hsa hD α β hα hβ hbound _
      (by simpa only [Complex.conj_re] using hzre)
      (by simpa only [Complex.conj_im, neg_ne_zero] using hz)
      (by simpa only [Complex.conj_im, abs_neg, hzim, abs_of_pos hL0] using hsmall)
  exact ⟨isSelfAdjoint_of_conjugate_shift_ranges (A + B)
    (symmetric_add_of_domain_le A B hsa.isSymmetric_operator hsb hD) z hr hrc,
    inf_eq_left.mpr hD⟩

/-- A closed extension contains the closure of every operator it extends. -/
theorem closure_le_of_closed {S T : Operator ℂ H H}
    (hc : IsClosable S) (hT : IsClosed T) (hST : S ≤ T) : S.closure ≤ T := by
  apply LinearPMap.le_of_le_graph
  rw [← hc.graph_closure_eq_closure_graph]
  exact S.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hST) hT

/-- Symmetry persists on the graph closure. -/
theorem IsSymmetric.closure_operator {B : Operator ℂ H H} (hB : IsSymmetric B) :
    IsSymmetric B.closure := by
  have hd : DenselyDefined B.closure := hB.1.mono B.le_closure.1
  have hi : B.closure ≤ hilbertAdjoint B :=
    closure_le_of_closed hB.isClosable (hilbertAdjoint_isClosed B hB.1) hB.2
  apply isSymmetric_of_inner B.closure hd
  intro x y
  have hx : ((x : H), B.closure x) ∈ B.graph.topologicalClosure := by
    rw [hB.isClosable.graph_closure_eq_closure_graph]
    exact B.closure.mem_graph x
  have hh := (mem_graphClosure_iff_adjoint B hB.1 _ _).mp hx
    ⟨y, hi.1 y.prop⟩
  have he : hilbertAdjoint B ⟨y, hi.1 y.prop⟩ = B.closure y := (hi.2 rfl).symm
  simpa only [he] using hh

/-- Extend a relatively bounded map from a graph-dense operator C to A.
The extension is the restriction of closure B, with the original constants. -/
theorem relative_extension_from_graph_core (A C B : Operator ℂ H H)
    (hCA : C ≤ A) (hcore : C.graph.topologicalClosure = A.graph)
    (hB : IsClosable B) (hD : C.domain ≤ B.domain)
    (a b : ℝ)
    (hb : ∀ x : C.domain, ‖B ⟨x, hD x.prop⟩‖ ≤ a * ‖C x‖ + b * ‖(x : H)‖) :
    ∃ hDA : A.domain ≤ B.closure.domain,
      (∃ F : GraphDomain A →L[ℂ] H, ∀ x : GraphDomain A,
        F x = B.closure ⟨GraphDomain.toDomain A x, hDA x.prop⟩) ∧
      (∀ x : A.domain, ‖B.closure ⟨x, hDA x.prop⟩‖ ≤
        a * ‖A x‖ + b * ‖(x : H)‖) := by
  have hg : C.graph ≤ A.graph := LinearPMap.le_graph_of_le hCA
  let e : C.domain →ₗ[ℂ] A.graph :=
    { toFun := fun x => ⟨((x : H), C x), hg (C.mem_graph x)⟩
      map_add' := fun x y => Subtype.ext (Prod.ext rfl (C.map_add x y))
      map_smul' := fun c x => Subtype.ext (Prod.ext rfl (C.map_smul c x)) }
  have hr : Set.range e = Set.range (Submodule.inclusion hg) := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : H), C x), C.mem_graph x⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨x, hx, hy⟩ := C.mem_graph_iff.mp q.prop
      exact ⟨x, Subtype.ext (Prod.ext hx hy)⟩
  have hed : DenseRange e := by
    change Dense (Set.range e)
    rw [hr]
    apply (denseRange_inclusion_iff hg).mpr
    intro p hp
    change p ∈ C.graph.topologicalClosure
    rw [hcore]
    exact hp
  let f : C.domain →ₗ[ℂ] H := B.toFun.comp (Submodule.inclusion hD)
  have hnorm (x : C.domain) : ‖f x‖ ≤ (|a| + |b|) * ‖e x‖ := by
    have h₁ : ‖C x‖ ≤ ‖e x‖ := le_max_right _ _
    have h₂ : ‖(x : H)‖ ≤ ‖e x‖ := le_max_left _ _
    calc
      ‖f x‖ ≤ a * ‖C x‖ + b * ‖(x : H)‖ := hb x
      _ ≤ |a| * ‖C x‖ + |b| * ‖(x : H)‖ := add_le_add
        (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _))
      _ ≤ |a| * ‖e x‖ + |b| * ‖e x‖ := add_le_add
        (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h₂ (abs_nonneg _))
      _ = _ := by ring
  let F := f.extendOfNorm e
  have hF (x : C.domain) : F (e x) = B ⟨x, hD x.prop⟩ :=
    LinearMap.extendOfNorm_eq hed ⟨_, hnorm⟩ x
  let P : A.graph →L[ℂ] H := (ContinuousLinearMap.fst ℂ H H).comp A.graph.subtypeL
  let Q : A.graph →L[ℂ] H := (ContinuousLinearMap.snd ℂ H H).comp A.graph.subtypeL
  have hmem (p : A.graph) : (P p, F p) ∈ B.closure.graph := by
    refine hed.induction_on (p := fun q => (P q, F q) ∈ B.closure.graph) p ?_ ?_
    · exact hB.closure_isClosed.preimage (P.continuous.prodMk F.continuous)
    · intro x
      rw [hF]
      exact LinearPMap.le_graph_of_le B.le_closure (B.mem_graph ⟨x, hD x.prop⟩)
  have hbound (p : A.graph) : ‖F p‖ ≤ a * ‖Q p‖ + b * ‖P p‖ := by
    refine hed.induction_on (p := fun q => ‖F q‖ ≤ a * ‖Q q‖ + b * ‖P q‖) p ?_ ?_
    · exact isClosed_le F.continuous.norm
        ((continuous_const.mul Q.continuous.norm).add
          (continuous_const.mul P.continuous.norm))
    · intro x
      rw [hF]
      exact hb x
  let j : GraphDomain A →ₗ[ℂ] A.graph :=
    { toFun := fun x => ⟨((GraphDomain.toDomain A x : H), A (GraphDomain.toDomain A x)),
        A.mem_graph _⟩
      map_add' := fun x y => Subtype.ext (Prod.ext rfl (A.map_add _ _))
      map_smul' := fun c x => Subtype.ext (Prod.ext rfl (A.map_smul _ _)) }
  have hj (x : GraphDomain A) : ‖j x‖ ≤ 1 * ‖x‖ := by
    change max ‖(GraphDomain.toDomain A x : H)‖ ‖A (GraphDomain.toDomain A x)‖ ≤
      1 * (‖(GraphDomain.toDomain A x : H)‖ + ‖A (GraphDomain.toDomain A x)‖)
    rw [one_mul]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  let J := j.mkContinuous 1 hj
  have hjmem (x : A.domain) :
      (x.val, F (j (x : GraphDomain A))) ∈ B.closure.graph := hmem (j x)
  have hDA : A.domain ≤ B.closure.domain := fun x hx =>
    ((mem_graph_iff B.closure (x, F (j (⟨x, hx⟩ : GraphDomain A)))).mp (hjmem ⟨x, hx⟩)).choose
  have hval (x : A.domain) : B.closure ⟨x, hDA x.prop⟩ = F (j (x : GraphDomain A)) :=
    ((mem_graph_iff B.closure _).mp (hjmem x)).choose_spec
  refine ⟨hDA, ⟨F.comp J, ?_⟩, ?_⟩
  · intro x
    exact (hval (GraphDomain.toDomain A x)).symm
  · intro x
    rw [hval]
    exact hbound (j x)

/-- The graph, with its ordinary product norm, maps continuously to the
same domain equipped with the sum graph norm. -/
def graphToGraphDomain (A : Operator ℂ H H) : A.graph →L[ℂ] GraphDomain A := by
  let j : A.graph →ₗ[ℂ] GraphDomain A :=
    { toFun := fun p => (⟨p.val.1, ((mem_graph_iff A p.val).mp p.prop).choose⟩ : A.domain)
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  apply j.mkContinuous 2
  intro p
  have hv : A (GraphDomain.toDomain A (j p)) = p.val.2 :=
    ((mem_graph_iff A p.val).mp p.prop).choose_spec
  change ‖p.val.1‖ + ‖A (GraphDomain.toDomain A (j p))‖ ≤ 2 * ‖p‖
  rw [hv]
  change ‖p.val.1‖ + ‖p.val.2‖ ≤ 2 * max ‖p.val.1‖ ‖p.val.2‖
  linarith [le_max_left ‖p.val.1‖ ‖p.val.2‖, le_max_right ‖p.val.1‖ ‖p.val.2‖]

/-- Inclusion is compatible with sums of domain-carrying operators. -/
theorem add_mono_operator {C A B T : Operator ℂ H H} (hCA : C ≤ A) (hBT : B ≤ T) :
    C + B ≤ A + T := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact ⟨hCA.1 hx.1, hBT.1 hx.2⟩
  · intro x y hxy
    change C ⟨x, x.prop.1⟩ + B ⟨x, x.prop.2⟩ =
      A ⟨y, y.prop.1⟩ + T ⟨y, y.prop.2⟩
    exact congrArg₂ (· + ·) (hCA.2 hxy) (hBT.2 hxy)

/-- A graph-continuous perturbation preserves graph-density of the core.
Closedness of the sum then identifies the closure as an exact partial map. -/
theorem graph_core_sum_closure (A C B T : Operator ℂ H H)
    (hCA : C ≤ A) (hcore : C.graph.topologicalClosure = A.graph)
    (hBT : B ≤ T) (hCD : C.domain ≤ B.domain) (hAD : A.domain ≤ T.domain)
    (F : GraphDomain A →L[ℂ] H)
    (hF : ∀ x : GraphDomain A, F x = T ⟨GraphDomain.toDomain A x, hAD x.prop⟩)
    (hclosed : IsClosed (A + T)) :
    (C + B).IsClosable ∧ (C + B).closure = A + T := by
  have hg : C.graph ≤ A.graph := LinearPMap.le_graph_of_le hCA
  let e : C.graph →ₗ[ℂ] A.graph := Submodule.inclusion hg
  have hed : DenseRange e := by
    apply (denseRange_inclusion_iff hg).mpr
    intro p hp
    change p ∈ C.graph.topologicalClosure
    rwa [hcore]
  let P : A.graph →L[ℂ] H := (ContinuousLinearMap.fst ℂ H H).comp A.graph.subtypeL
  let Q : A.graph →L[ℂ] H := (ContinuousLinearMap.snd ℂ H H).comp A.graph.subtypeL
  let G : A.graph →L[ℂ] (H × H) := P.prod (Q + F.comp (graphToGraphDomain A))
  have hmem (p : A.graph) : G p ∈ (C + B).graph.topologicalClosure := by
    refine hed.induction_on (p := fun q => G q ∈ (C + B).graph.topologicalClosure) p ?_ ?_
    · exact (C + B).graph.isClosed_topologicalClosure.preimage G.continuous
    · intro q
      obtain ⟨x, hx, hy⟩ := C.mem_graph_iff.mp q.prop
      apply (C + B).graph.le_topologicalClosure
      apply (mem_graph_iff (C + B) (G (e q))).mpr
      have hxC : (G (e q)).1 ∈ C.domain := by
        change q.val.1 ∈ C.domain
        rw [← hx]
        exact x.prop
      have hxB : (G (e q)).1 ∈ B.domain := hCD hxC
      refine ⟨⟨hxC, hxB⟩, ?_⟩
      change C ⟨q.val.1, hxC⟩ + B ⟨q.val.1, hxB⟩ =
        q.val.2 + F (graphToGraphDomain A (e q))
      have hcval : C ⟨q.val.1, hxC⟩ = q.val.2 := by
        have he : (⟨q.val.1, hxC⟩ : C.domain) = x := Subtype.ext hx.symm
        rw [he]
        exact hy
      rw [hcval, hF]
      congr 1
      exact hBT.2 rfl
  have hle : C + B ≤ A + T := add_mono_operator hCA hBT
  have hc : (C + B).IsClosable := hclosed.isClosable.leIsClosable hle
  refine ⟨hc, LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hc.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact (C + B).graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hle) hclosed
  · intro p hp
    obtain ⟨x, hx, hy⟩ := (A + T).mem_graph_iff.mp hp
    let q : A.graph := ⟨((x : H), A ⟨x, x.prop.1⟩), A.mem_graph ⟨x, x.prop.1⟩⟩
    have heq : G q = p := by
      apply Prod.ext
      · exact hx
      · change A ⟨x, x.prop.1⟩ + F (graphToGraphDomain A q) = p.2
        rw [hF]
        exact hy
    rw [← heq]
    exact hmem q

/-- Kato–Rellich on a core, with the continuous graph-norm extension of B,
the closure of the original restricted sum, and its exact domain. -/
theorem kato_rellich_core : KatoRellichSpec.KatoRellichCore.{u} := by
  intro H _ _ _ A B D₀ hA hcore hB hBD a b ha hb
  have he : IsEssentiallySelfAdjoint A := hA
  have hs : IsSymmetric B := hB
  have hAc : IsClosable A := he.2.1
  have hAs : IsSelfAdjoint A.closure := he.2.2
  let C := A.domRestrict D₀
  have hCA : C ≤ A.closure := LinearPMap.domRestrict_le.trans A.le_closure
  have hCcore : C.graph.topologicalClosure = A.closure.graph :=
    hcore.2.trans hAc.graph_closure_eq_closure_graph
  have hCD : C.domain ≤ B.domain := fun x hx => hBD hx.1
  obtain ⟨hD, ⟨F, hF⟩, hbound⟩ :=
    relative_extension_from_graph_core A.closure C B hCA hCcore hs.isClosable hCD a b hb
  have hsum : IsSelfAdjoint (A.closure + B.closure) :=
    (kato_rellich A.closure B.closure hAs hs.closure_operator hD a b ha hbound).1
  obtain ⟨hc, hcl⟩ := graph_core_sum_closure A.closure C B B.closure
    hCA hCcore B.le_closure hCD hD F hF hsum.isClosed_operator
  have hrestrict : (A + B).domRestrict D₀ = C + B := by
    apply LinearPMap.ext_iff.mpr
    refine ⟨?_, ?_⟩
    · exact (inf_assoc D₀ A.domain B.domain).symm
    · intro x hx hy
      rfl
  refine ⟨hD, ⟨F, hF⟩, hbound, hsum, ?_, ?_, ?_⟩
  · rw [hrestrict]
    exact hc
  · rw [hrestrict]
    exact hcl
  · rw [hrestrict, hcl]
    exact inf_eq_left.mpr hD

namespace RealPerturbation
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem real_symmetric_of_inner (S : Operator ℝ E E) (hd : DenselyDefined S)
    (hi : ∀ x y : S.domain, inner ℝ (S x) (y : E) = inner ℝ (x : E) (S y)) :
    KatoRellichSpec.realSymmetricValue S := by
  refine ⟨hd, ?_⟩
  apply LinearPMap.IsFormalAdjoint.le_adjoint (hT := hd)
  exact hi

theorem real_symmetric_inner {S : Operator ℝ E E}
    (hS : KatoRellichSpec.realSymmetricValue S) (x y : S.domain) :
    inner ℝ (S x) (y : E) = inner ℝ (x : E) (S y) := by
  have hy : S y = hilbertAdjoint S ⟨y, hS.2.1 y.2⟩ := hS.2.2 rfl
  rw [hy]
  exact hilbertAdjoint_inner S hS.1 ⟨y, hS.2.1 y.2⟩ x

theorem real_symmetric_closable {S : Operator ℝ E E}
    (hS : KatoRellichSpec.realSymmetricValue S) : IsClosable S :=
  (hilbertAdjoint_isClosed S hS.1).isClosable.leIsClosable hS.2

theorem real_selfAdjoint_closed {A : Operator ℝ E E}
    (hA : KatoRellichSpec.realSelfAdjointValue A) : IsClosed A := by
  have he : A = hilbertAdjoint A := hA.2
  rw [he]
  exact hilbertAdjoint_isClosed A hA.1

/-- A closed extension contains the closure of every operator it extends. -/
theorem closure_le_of_closed {S T : Operator ℝ E E}
    (hc : IsClosable S) (hT : IsClosed T) (hST : S ≤ T) : S.closure ≤ T := by
  apply LinearPMap.le_of_le_graph
  rw [← hc.graph_closure_eq_closure_graph]
  exact S.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hST) hT

/-- Symmetry persists on the graph closure. -/
theorem real_symmetric_closure {B : Operator ℝ E E} (hB : KatoRellichSpec.realSymmetricValue B) :
    KatoRellichSpec.realSymmetricValue B.closure := by
  have hd : DenselyDefined B.closure := hB.1.mono B.le_closure.1
  have hi : B.closure ≤ hilbertAdjoint B :=
    closure_le_of_closed (real_symmetric_closable hB) (hilbertAdjoint_isClosed B hB.1) hB.2
  apply real_symmetric_of_inner B.closure hd
  intro x y
  have hx : ((x : E), B.closure x) ∈ B.graph.topologicalClosure := by
    rw [(real_symmetric_closable hB).graph_closure_eq_closure_graph]
    exact B.closure.mem_graph x
  have hh := (mem_graphClosure_iff_adjoint B hB.1 _ _).mp hx
    ⟨y, hi.1 y.prop⟩
  have he : hilbertAdjoint B ⟨y, hi.1 y.prop⟩ = B.closure y := (hi.2 rfl).symm
  simpa only [he] using hh

/-- Extend a relatively bounded map from a graph-dense operator C to A.
The extension is the restriction of closure B, with the original constants. -/
theorem relative_extension_from_graph_core (A C B : Operator ℝ E E)
    (hCA : C ≤ A) (hcore : C.graph.topologicalClosure = A.graph)
    (hB : IsClosable B) (hD : C.domain ≤ B.domain)
    (a b : ℝ)
    (hb : ∀ x : C.domain, ‖B ⟨x, hD x.prop⟩‖ ≤ a * ‖C x‖ + b * ‖(x : E)‖) :
    ∃ hDA : A.domain ≤ B.closure.domain,
      (∃ F : GraphDomain A →L[ℝ] E, ∀ x : GraphDomain A,
        F x = B.closure ⟨GraphDomain.toDomain A x, hDA x.prop⟩) ∧
      (∀ x : A.domain, ‖B.closure ⟨x, hDA x.prop⟩‖ ≤
        a * ‖A x‖ + b * ‖(x : E)‖) := by
  have hg : C.graph ≤ A.graph := LinearPMap.le_graph_of_le hCA
  let e : C.domain →ₗ[ℝ] A.graph :=
    { toFun := fun x => ⟨((x : E), C x), hg (C.mem_graph x)⟩
      map_add' := fun x y => Subtype.ext (Prod.ext rfl (C.map_add x y))
      map_smul' := fun c x => Subtype.ext (Prod.ext rfl (C.map_smul c x)) }
  have hr : Set.range e = Set.range (Submodule.inclusion hg) := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : E), C x), C.mem_graph x⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨x, hx, hy⟩ := C.mem_graph_iff.mp q.prop
      exact ⟨x, Subtype.ext (Prod.ext hx hy)⟩
  have hed : DenseRange e := by
    change Dense (Set.range e)
    rw [hr]
    apply (denseRange_inclusion_iff hg).mpr
    intro p hp
    change p ∈ C.graph.topologicalClosure
    rw [hcore]
    exact hp
  let f : C.domain →ₗ[ℝ] E := B.toFun.comp (Submodule.inclusion hD)
  have hnorm (x : C.domain) : ‖f x‖ ≤ (|a| + |b|) * ‖e x‖ := by
    have h₁ : ‖C x‖ ≤ ‖e x‖ := le_max_right _ _
    have h₂ : ‖(x : E)‖ ≤ ‖e x‖ := le_max_left _ _
    calc
      ‖f x‖ ≤ a * ‖C x‖ + b * ‖(x : E)‖ := hb x
      _ ≤ |a| * ‖C x‖ + |b| * ‖(x : E)‖ := add_le_add
        (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _))
      _ ≤ |a| * ‖e x‖ + |b| * ‖e x‖ := add_le_add
        (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h₂ (abs_nonneg _))
      _ = _ := by ring
  let F := f.extendOfNorm e
  have hF (x : C.domain) : F (e x) = B ⟨x, hD x.prop⟩ :=
    LinearMap.extendOfNorm_eq hed ⟨_, hnorm⟩ x
  let P : A.graph →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp A.graph.subtypeL
  let Q : A.graph →L[ℝ] E := (ContinuousLinearMap.snd ℝ E E).comp A.graph.subtypeL
  have hmem (p : A.graph) : (P p, F p) ∈ B.closure.graph := by
    refine hed.induction_on (p := fun q => (P q, F q) ∈ B.closure.graph) p ?_ ?_
    · exact hB.closure_isClosed.preimage (P.continuous.prodMk F.continuous)
    · intro x
      rw [hF]
      exact LinearPMap.le_graph_of_le B.le_closure (B.mem_graph ⟨x, hD x.prop⟩)
  have hbound (p : A.graph) : ‖F p‖ ≤ a * ‖Q p‖ + b * ‖P p‖ := by
    refine hed.induction_on (p := fun q => ‖F q‖ ≤ a * ‖Q q‖ + b * ‖P q‖) p ?_ ?_
    · exact isClosed_le F.continuous.norm
        ((continuous_const.mul Q.continuous.norm).add
          (continuous_const.mul P.continuous.norm))
    · intro x
      rw [hF]
      exact hb x
  let j : GraphDomain A →ₗ[ℝ] A.graph :=
    { toFun := fun x => ⟨((GraphDomain.toDomain A x : E), A (GraphDomain.toDomain A x)),
        A.mem_graph _⟩
      map_add' := fun x y => Subtype.ext (Prod.ext rfl (A.map_add _ _))
      map_smul' := fun c x => Subtype.ext (Prod.ext rfl (A.map_smul _ _)) }
  have hj (x : GraphDomain A) : ‖j x‖ ≤ 1 * ‖x‖ := by
    change max ‖(GraphDomain.toDomain A x : E)‖ ‖A (GraphDomain.toDomain A x)‖ ≤
      1 * (‖(GraphDomain.toDomain A x : E)‖ + ‖A (GraphDomain.toDomain A x)‖)
    rw [one_mul]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  let J := j.mkContinuous 1 hj
  have hjmem (x : A.domain) :
      (x.val, F (j (x : GraphDomain A))) ∈ B.closure.graph := hmem (j x)
  have hDA : A.domain ≤ B.closure.domain := fun x hx =>
    ((mem_graph_iff B.closure (x, F (j (⟨x, hx⟩ : GraphDomain A)))).mp (hjmem ⟨x, hx⟩)).choose
  have hval (x : A.domain) : B.closure ⟨x, hDA x.prop⟩ = F (j (x : GraphDomain A)) :=
    ((mem_graph_iff B.closure _).mp (hjmem x)).choose_spec
  refine ⟨hDA, ⟨F.comp J, ?_⟩, ?_⟩
  · intro x
    exact (hval (GraphDomain.toDomain A x)).symm
  · intro x
    rw [hval]
    exact hbound (j x)

/-- The graph, with its ordinary product norm, maps continuously to the
same domain equipped with the sum graph norm. -/
def graphToGraphDomain (A : Operator ℝ E E) : A.graph →L[ℝ] GraphDomain A := by
  let j : A.graph →ₗ[ℝ] GraphDomain A :=
    { toFun := fun p => (⟨p.val.1, ((mem_graph_iff A p.val).mp p.prop).choose⟩ : A.domain)
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  apply j.mkContinuous 2
  intro p
  have hv : A (GraphDomain.toDomain A (j p)) = p.val.2 :=
    ((mem_graph_iff A p.val).mp p.prop).choose_spec
  change ‖p.val.1‖ + ‖A (GraphDomain.toDomain A (j p))‖ ≤ 2 * ‖p‖
  rw [hv]
  change ‖p.val.1‖ + ‖p.val.2‖ ≤ 2 * max ‖p.val.1‖ ‖p.val.2‖
  linarith [le_max_left ‖p.val.1‖ ‖p.val.2‖, le_max_right ‖p.val.1‖ ‖p.val.2‖]

/-- Inclusion is compatible with sums of domain-carrying operators. -/
theorem add_mono_operator {C A B T : Operator ℝ E E} (hCA : C ≤ A) (hBT : B ≤ T) :
    C + B ≤ A + T := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact ⟨hCA.1 hx.1, hBT.1 hx.2⟩
  · intro x y hxy
    change C ⟨x, x.prop.1⟩ + B ⟨x, x.prop.2⟩ =
      A ⟨y, y.prop.1⟩ + T ⟨y, y.prop.2⟩
    exact congrArg₂ (· + ·) (hCA.2 hxy) (hBT.2 hxy)

/-- A graph-continuous perturbation preserves graph-density of the core.
Closedness of the sum then identifies the closure as an exact partial map. -/
theorem graph_core_sum_closure (A C B T : Operator ℝ E E)
    (hCA : C ≤ A) (hcore : C.graph.topologicalClosure = A.graph)
    (hBT : B ≤ T) (hCD : C.domain ≤ B.domain) (hAD : A.domain ≤ T.domain)
    (F : GraphDomain A →L[ℝ] E)
    (hF : ∀ x : GraphDomain A, F x = T ⟨GraphDomain.toDomain A x, hAD x.prop⟩)
    (hclosed : IsClosed (A + T)) :
    (C + B).IsClosable ∧ (C + B).closure = A + T := by
  have hg : C.graph ≤ A.graph := LinearPMap.le_graph_of_le hCA
  let e : C.graph →ₗ[ℝ] A.graph := Submodule.inclusion hg
  have hed : DenseRange e := by
    apply (denseRange_inclusion_iff hg).mpr
    intro p hp
    change p ∈ C.graph.topologicalClosure
    rwa [hcore]
  let P : A.graph →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp A.graph.subtypeL
  let Q : A.graph →L[ℝ] E := (ContinuousLinearMap.snd ℝ E E).comp A.graph.subtypeL
  let G : A.graph →L[ℝ] (E × E) := P.prod (Q + F.comp (graphToGraphDomain A))
  have hmem (p : A.graph) : G p ∈ (C + B).graph.topologicalClosure := by
    refine hed.induction_on (p := fun q => G q ∈ (C + B).graph.topologicalClosure) p ?_ ?_
    · exact (C + B).graph.isClosed_topologicalClosure.preimage G.continuous
    · intro q
      obtain ⟨x, hx, hy⟩ := C.mem_graph_iff.mp q.prop
      apply (C + B).graph.le_topologicalClosure
      apply (mem_graph_iff (C + B) (G (e q))).mpr
      have hxC : (G (e q)).1 ∈ C.domain := by
        change q.val.1 ∈ C.domain
        rw [← hx]
        exact x.prop
      have hxB : (G (e q)).1 ∈ B.domain := hCD hxC
      refine ⟨⟨hxC, hxB⟩, ?_⟩
      change C ⟨q.val.1, hxC⟩ + B ⟨q.val.1, hxB⟩ =
        q.val.2 + F (graphToGraphDomain A (e q))
      have hcval : C ⟨q.val.1, hxC⟩ = q.val.2 := by
        have he : (⟨q.val.1, hxC⟩ : C.domain) = x := Subtype.ext hx.symm
        rw [he]
        exact hy
      rw [hcval, hF]
      congr 1
      exact hBT.2 rfl
  have hle : C + B ≤ A + T := add_mono_operator hCA hBT
  have hc : (C + B).IsClosable := hclosed.isClosable.leIsClosable hle
  refine ⟨hc, LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hc.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact (C + B).graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hle) hclosed
  · intro p hp
    obtain ⟨x, hx, hy⟩ := (A + T).mem_graph_iff.mp hp
    let q : A.graph := ⟨((x : E), A ⟨x, x.prop.1⟩), A.mem_graph ⟨x, x.prop.1⟩⟩
    have heq : G q = p := by
      apply Prod.ext
      · exact hx
      · change A ⟨x, x.prop.1⟩ + F (graphToGraphDomain A q) = p.2
        rw [hF]
        exact hy
    rw [← heq]
    exact hmem q


/-- A real block substitute for the nonreal resolvent. -/
def blockMap (A : Operator ℝ E E) (L : ℝ) :
    (A.graph × A.graph) →L[ℝ] WithLp 2 (E × E) :=
  let P : A.graph →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp A.graph.subtypeL
  let Q : A.graph →L[ℝ] E := (ContinuousLinearMap.snd ℝ E E).comp A.graph.subtypeL
  let f := ContinuousLinearMap.fst ℝ A.graph A.graph
  let g := ContinuousLinearMap.snd ℝ A.graph A.graph
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((Q.comp f + L • P.comp g).prod (L • P.comp f - Q.comp g))

@[simp] theorem blockMap_apply (A : Operator ℝ E E) (L : ℝ) (p : A.graph × A.graph) :
    blockMap A L p = WithLp.toLp 2 (p.1.val.2 + L • p.2.val.1,
      L • p.1.val.1 - p.2.val.2) := rfl

/-- The mixed terms cancel over a real Hilbert space. -/
theorem blockMap_norm_sq (A : Operator ℝ E E)
    (hs : KatoRellichSpec.realSymmetricValue A) (L : ℝ) (p : A.graph × A.graph) :
    ‖blockMap A L p‖ ^ 2 =
      ‖p.1.val.2‖ ^ 2 + ‖p.2.val.2‖ ^ 2 +
        L ^ 2 * (‖p.1.val.1‖ ^ 2 + ‖p.2.val.1‖ ^ 2) := by
  obtain ⟨x, hx, hAx⟩ := A.mem_graph_iff.mp p.1.prop
  obtain ⟨y, hy, hAy⟩ := A.mem_graph_iff.mp p.2.prop
  have hi : inner ℝ p.1.val.2 p.2.val.1 = inner ℝ p.1.val.1 p.2.val.2 := by
    rw [← hx, ← hAx, ← hy, ← hAy]
    exact real_symmetric_inner hs x y
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖p.1.val.2 + L • p.2.val.1‖ ^ 2 +
    ‖L • p.1.val.1 - p.2.val.2‖ ^ 2 = _
  rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_right,
    real_inner_smul_left, hi, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Closedness and the block lower bound give closed range. -/
theorem blockMap_closed_range (A : Operator ℝ E E)
    (hc : IsClosed A) (hs : KatoRellichSpec.realSymmetricValue A)
    (L : ℝ) (hL : 0 < L) : _root_.IsClosed (Set.range (blockMap A L)) := by
  let : CompleteSpace A.graph := hc.isComplete.completeSpace_coe
  have hbound (p : A.graph × A.graph) :
      ‖p‖ ≤ (1 + L⁻¹) * ‖blockMap A L p‖ := by
    have he := blockMap_norm_sq A hs L p
    have h₁ : ‖p.1.val.2‖ ≤ ‖blockMap A L p‖ := by
      nlinarith [sq_nonneg ‖p.2.val.2‖,
        mul_nonneg (sq_nonneg L) (add_nonneg (sq_nonneg ‖p.1.val.1‖)
          (sq_nonneg ‖p.2.val.1‖)), norm_nonneg (blockMap A L p), norm_nonneg p.1.val.2]
    have h₂ : ‖p.2.val.2‖ ≤ ‖blockMap A L p‖ := by
      nlinarith [sq_nonneg ‖p.1.val.2‖,
        mul_nonneg (sq_nonneg L) (add_nonneg (sq_nonneg ‖p.1.val.1‖)
          (sq_nonneg ‖p.2.val.1‖)), norm_nonneg (blockMap A L p), norm_nonneg p.2.val.2]
    have h₃ : L * ‖p.1.val.1‖ ≤ ‖blockMap A L p‖ := by
      nlinarith [sq_nonneg ‖p.1.val.2‖, sq_nonneg ‖p.2.val.2‖,
        mul_nonneg (sq_nonneg L) (sq_nonneg ‖p.2.val.1‖),
        norm_nonneg (blockMap A L p), mul_nonneg hL.le (norm_nonneg p.1.val.1)]
    have h₄ : L * ‖p.2.val.1‖ ≤ ‖blockMap A L p‖ := by
      nlinarith [sq_nonneg ‖p.1.val.2‖, sq_nonneg ‖p.2.val.2‖,
        mul_nonneg (sq_nonneg L) (sq_nonneg ‖p.1.val.1‖),
        norm_nonneg (blockMap A L p), mul_nonneg hL.le (norm_nonneg p.2.val.1)]
    have h₃' : ‖p.1.val.1‖ ≤ L⁻¹ * ‖blockMap A L p‖ := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact (le_div_iff₀ hL).mpr (by simpa [mul_comm] using h₃)
    have h₄' : ‖p.2.val.1‖ ≤ L⁻¹ * ‖blockMap A L p‖ := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact (le_div_iff₀ hL).mpr (by simpa [mul_comm] using h₄)
    change max (max ‖p.1.val.1‖ ‖p.1.val.2‖) (max ‖p.2.val.1‖ ‖p.2.val.2‖) ≤ _
    have hnon : 0 ≤ L⁻¹ * ‖blockMap A L p‖ := by positivity
    apply max_le <;> apply max_le <;> nlinarith [norm_nonneg (blockMap A L p)]
  exact ((blockMap A L).antilipschitz_of_bound (K := ⟨1 + L⁻¹, by positivity⟩)
    hbound).isClosed_range (blockMap A L).uniformContinuous

/-- Self-adjointness annihilates the orthogonal complement of the block range. -/
theorem blockMap_surjective (A : Operator ℝ E E)
    (hA : KatoRellichSpec.realSelfAdjointValue A) (L : ℝ) (hL : 0 < L) :
    Function.Surjective (blockMap A L) := by
  have hs : KatoRellichSpec.realSymmetricValue A := ⟨hA.1, hA.2.le⟩
  have hc := blockMap_closed_range A (real_selfAdjoint_closed hA) hs L hL
  have hbot : (blockMap A L).range.orthogonal = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro w hw
    have hx (x : A.domain) : inner ℝ (A x) w.fst = inner ℝ (x : E) (-L • w.snd) := by
      have h := hw _ ⟨(⟨((x : E), A x), A.mem_graph x⟩, 0), rfl⟩
      change inner ℝ (A x + L • (0 : E)) w.fst +
        inner ℝ (L • (x : E) - (0 : E)) w.snd = 0 at h
      simpa only [smul_zero, add_zero, sub_zero, real_inner_smul_left,
        real_inner_smul_right, neg_mul, eq_neg_iff_add_eq_zero] using h
    have hy (y : A.domain) : inner ℝ (A y) w.snd = inner ℝ (y : E) (L • w.fst) := by
      have h := hw _ ⟨(0, ⟨((y : E), A y), A.mem_graph y⟩), rfl⟩
      change inner ℝ ((0 : E) + L • (y : E)) w.fst +
        inner ℝ (L • (0 : E) - A y) w.snd = 0 at h
      simp only [zero_add, smul_zero, zero_sub, inner_neg_left,
        real_inner_smul_left] at h
      rw [real_inner_smul_right]
      linarith
    have hxd := (mem_hilbertAdjoint_domain_iff A hA.1 w.fst).mpr ⟨_, hx⟩
    have hyd := (mem_hilbertAdjoint_domain_iff A hA.1 w.snd).mpr ⟨_, hy⟩
    have hxe := hilbertAdjoint_apply_eq A hA.1 ⟨w.fst, hxd⟩ _ hx
    have hye := hilbertAdjoint_apply_eq A hA.1 ⟨w.snd, hyd⟩ _ hy
    have he : A = hilbertAdjoint A := hA.2
    have hxA : w.fst ∈ A.domain := he.ge.1 hxd
    have hyA : w.snd ∈ A.domain := he.ge.1 hyd
    have hxval : A ⟨w.fst, hxA⟩ = -L • w.snd := (he.le.2 rfl).trans hxe
    have hyval : A ⟨w.snd, hyA⟩ = L • w.fst := (he.le.2 rfl).trans hye
    have hi := real_symmetric_inner hs ⟨w.fst, hxA⟩ ⟨w.snd, hyA⟩
    rw [hxval, hyval, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
    change -L * ‖w.snd‖ ^ 2 = L * ‖w.fst‖ ^ 2 at hi
    have hz : ‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2 = 0 :=
      (mul_eq_zero.mp (by nlinarith : L * (‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2) = 0)).resolve_left hL.ne'
    have hw1 : w.fst = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖w.snd‖, norm_nonneg w.fst])
    have hw2 : w.snd = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖w.fst‖, norm_nonneg w.snd])
    exact (WithLp.equiv 2 (E × E)).injective (Prod.ext hw1 hw2)
  change _root_.IsClosed ((blockMap A L).range : Set (WithLp 2 (E × E))) at hc
  have ht : (blockMap A L).range = ⊤ := by
    rw [← hc.submodule_topologicalClosure_eq,
      ← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
  intro y
  have : y ∈ (blockMap A L).range := by rw [ht]; trivial
  exact this


/-- A real symmetric operator with an onto block is self-adjoint, including domains. -/
theorem selfAdjoint_of_block_surjective (S : Operator ℝ E E)
    (hs : KatoRellichSpec.realSymmetricValue S) (L : ℝ) (hL : 0 < L)
    (hr : Function.Surjective (blockMap S L)) : KatoRellichSpec.realSelfAdjointValue S := by
  refine ⟨hs.1, LinearPMap.eq_of_le_of_domain_eq hs.2 (le_antisymm hs.2.1 ?_)⟩
  intro z hz
  let v := hilbertAdjoint S ⟨z, hz⟩
  obtain ⟨p, hp⟩ := hr (WithLp.toLp 2 (v, L • z))
  obtain ⟨x, hx, hSx⟩ := S.mem_graph_iff.mp p.1.prop
  obtain ⟨y, hy, hSy⟩ := S.mem_graph_iff.mp p.2.prop
  have he₁ := congrArg WithLp.fst hp
  have he₂ := congrArg WithLp.snd hp
  change p.1.val.2 + L • p.2.val.1 = v at he₁
  change L • p.1.val.1 - p.2.val.2 = L • z at he₂
  rw [← hy, ← hSx] at he₁
  rw [← hx, ← hSy] at he₂
  have hi := hilbertAdjoint_inner S hs.1 ⟨z, hz⟩ y
  change inner ℝ (S y) z = inner ℝ (y : E) v at hi
  rw [← he₁, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at hi
  have hh := congrArg (fun t => inner ℝ (S y) t) he₂
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hi] at hh
  have hsym : inner ℝ (S y) (x : E) = inner ℝ (y : E) (S x) := real_symmetric_inner hs y x
  rw [hsym] at hh
  change L * inner ℝ (y : E) (S x) - ‖S y‖ ^ 2 =
    L * (inner ℝ (y : E) (S x) + L * ‖(y : E)‖ ^ 2) at hh
  have hzsq : L ^ 2 * ‖(y : E)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖S y‖, mul_nonneg (sq_nonneg L) (sq_nonneg ‖(y : E)‖)]
  have hyn : ‖(y : E)‖ = 0 := by
    have hh := (mul_eq_zero.mp hzsq).resolve_left (pow_ne_zero 2 hL.ne')
    nlinarith [norm_nonneg (y : E)]
  have hy0 : y = 0 := Subtype.ext (norm_eq_zero.mp hyn)
  rw [hy0, S.map_zero, sub_zero] at he₂
  have hxz : (x : E) = z := (smul_right_injective E hL.ne') he₂
  rw [← hxz]
  exact x.prop

/-- A scalar Cauchy–Schwarz estimate with a convenient nonnegative constant. -/
private theorem two_coordinate_bound (a c u v : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (a * u + c * v) ^ 2 ≤ (a + c) ^ 2 * (u ^ 2 + v ^ 2) := by
  have h := sq_nonneg (a * v - c * u)
  have h' : 0 ≤ 2 * a * c * (u ^ 2 + v ^ 2) := by positivity
  nlinarith

/-- Apply B to the two domain coordinates with opposite signs. -/
def blockPerturbation (A B : Operator ℝ E E) (hD : A.domain ≤ B.domain) :
    (A.graph × A.graph) →ₗ[ℝ] WithLp 2 (E × E) :=
  let d : A.graph →ₗ[ℝ] B.domain :=
    { toFun := fun p => ⟨p.val.1, hD ((mem_graph_iff A p.val).mp p.prop).choose⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  (WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap.comp
    ((B.toFun.comp (d.comp (LinearMap.fst ℝ A.graph A.graph))).prod
      (-(B.toFun.comp (d.comp (LinearMap.snd ℝ A.graph A.graph)))))

/-- The exact relative constant is small on the inverse block. -/
theorem blockPerturbation_bound (A B : Operator ℝ E E)
    (hs : KatoRellichSpec.realSymmetricValue A) (hD : A.domain ≤ B.domain)
    (a b L : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 < L)
    (hbound : ∀ x : A.domain, ‖B ⟨x, hD x.prop⟩‖ ≤ a * ‖A x‖ + b * ‖(x : E)‖)
    (p : A.graph × A.graph) :
    ‖blockPerturbation A B hD p‖ ≤ (a + b / L) * ‖blockMap A L p‖ := by
  have hcoord (q : A.graph) :
      ‖B ⟨q.val.1, hD ((mem_graph_iff A q.val).mp q.prop).choose⟩‖ ^ 2 ≤
        (a + b / L) ^ 2 * (‖q.val.2‖ ^ 2 + L ^ 2 * ‖q.val.1‖ ^ 2) := by
    obtain ⟨x, hx, hAx⟩ := A.mem_graph_iff.mp q.prop
    have h := hbound x
    have he : b * ‖(x : E)‖ = (b / L) * (L * ‖(x : E)‖) := by field_simp
    rw [he] at h
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h
    have hc := two_coordinate_bound a (b / L) ‖A x‖ (L * ‖(x : E)‖) ha (by positivity)
    have hn : ‖B ⟨q.val.1, hD ((mem_graph_iff A q.val).mp q.prop).choose⟩‖ =
        ‖B ⟨x, hD x.prop⟩‖ := by
      apply congrArg norm
      apply congrArg B
      exact Subtype.ext hx.symm
    rw [hn, ← hx, ← hAx]
    exact hsquare.trans (by simpa only [mul_pow] using hc)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, blockMap_norm_sq A hs L p, WithLp.prod_norm_sq_eq_of_L2]
  change ‖B _‖ ^ 2 + ‖-B _‖ ^ 2 ≤ _
  rw [norm_neg]
  exact (add_le_add (hcoord p.1) (hcoord p.2)).trans_eq (by ring)


/-- Symmetry of a real sum on the original exact domain. -/
theorem real_symmetric_add (A B : Operator ℝ E E)
    (hA : KatoRellichSpec.realSymmetricValue A)
    (hB : KatoRellichSpec.realSymmetricValue B) (hD : A.domain ≤ B.domain) :
    KatoRellichSpec.realSymmetricValue (A + B) := by
  apply real_symmetric_of_inner
  · change Dense ((A.domain ⊓ B.domain : Submodule ℝ E) : Set E)
    simpa only [inf_eq_left.mpr hD] using hA.1
  · intro x y
    change inner ℝ (A ⟨x, x.prop.1⟩ + B ⟨x, x.prop.2⟩) (y : E) =
      inner ℝ (x : E) (A ⟨y, y.prop.1⟩ + B ⟨y, y.prop.2⟩)
    rw [inner_add_left, inner_add_right]
    exact congrArg₂ (· + ·)
      (real_symmetric_inner hA ⟨x, x.prop.1⟩ ⟨y, y.prop.1⟩)
      (real_symmetric_inner hB ⟨x, x.prop.2⟩ ⟨y, y.prop.2⟩)

/-- Inverting the perturbed real block by a geometric series. -/
theorem perturbed_block_surjective (A B : Operator ℝ E E)
    (hA : KatoRellichSpec.realSelfAdjointValue A) (hD : A.domain ≤ B.domain)
    (a b L : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 < L)
    (hbound : ∀ x : A.domain, ‖B ⟨x, hD x.prop⟩‖ ≤ a * ‖A x‖ + b * ‖(x : E)‖)
    (hsmall : a + b / L < 1) : Function.Surjective (blockMap (A + B) L) := by
  have hs : KatoRellichSpec.realSymmetricValue A := ⟨hA.1, hA.2.le⟩
  have hinj : Function.Injective (blockMap A L) := by
    apply (injective_iff_map_eq_zero (blockMap A L).toLinearMap).mpr
    intro p hp
    change blockMap A L p = 0 at hp
    have he := blockMap_norm_sq A hs L p
    rw [hp, norm_zero, zero_pow (by decide)] at he
    have hnorm (q : A.graph) (h₁ : ‖q.val.2‖ ^ 2 ≤ 0)
        (h₂ : L ^ 2 * ‖q.val.1‖ ^ 2 ≤ 0) : q = 0 := by
      have hq1sq : ‖q.val.1‖ ^ 2 = 0 :=
        (mul_eq_zero.mp (le_antisymm h₂ (by positivity))).resolve_left (pow_ne_zero 2 hL.ne')
      have hq1 : q.val.1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg q.val.1])
      have hq2 : q.val.2 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg q.val.2])
      exact Subtype.ext (Prod.ext hq1 hq2)
    have hp1 : p.1 = 0 := by
      apply hnorm
      · nlinarith [sq_nonneg ‖p.2.val.2‖,
          mul_nonneg (sq_nonneg L) (add_nonneg (sq_nonneg ‖p.1.val.1‖) (sq_nonneg ‖p.2.val.1‖))]
      · nlinarith [sq_nonneg ‖p.1.val.2‖, sq_nonneg ‖p.2.val.2‖,
          mul_nonneg (sq_nonneg L) (sq_nonneg ‖p.2.val.1‖)]
    have hp2 : p.2 = 0 := by
      apply hnorm
      · nlinarith [sq_nonneg ‖p.1.val.2‖,
          mul_nonneg (sq_nonneg L) (add_nonneg (sq_nonneg ‖p.1.val.1‖) (sq_nonneg ‖p.2.val.1‖))]
      · nlinarith [sq_nonneg ‖p.1.val.2‖, sq_nonneg ‖p.2.val.2‖,
          mul_nonneg (sq_nonneg L) (sq_nonneg ‖p.1.val.1‖)]
    exact Prod.ext hp1 hp2
  let e := LinearEquiv.ofBijective (blockMap A L).toLinearMap
    ⟨hinj, blockMap_surjective A hA L hL⟩
  let T := (blockPerturbation A B hD).comp e.symm.toLinearMap
  have he (w : WithLp 2 (E × E)) : blockMap A L (e.symm w) = w := e.apply_symm_apply w
  have hT (w : WithLp 2 (E × E)) : ‖T w‖ ≤ (a + b / L) * ‖w‖ := by
    have hh := blockPerturbation_bound A B hs hD a b L ha hb hL hbound (e.symm w)
    rwa [he] at hh
  let C := T.mkContinuous (a + b / L) hT
  have hn : ‖(-C : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E))‖ < 1 := by
    exact (norm_neg C).trans_lt ((C.opNorm_le_bound (by positivity) hT).trans_lt hsmall)
  let U := Units.oneSub (-C) hn
  intro w
  let v := (↑U⁻¹ : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E)) w
  have hv : v + C v = w := by
    have hh := congrArg (fun f : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E) => f w) U.mul_inv
    have hu : (U : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E)) = 1 - -C := Units.val_oneSub _ _
    change (U : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E)) v = w at hh
    rw [hu] at hh
    simpa using hh
  let p := e.symm v
  let d : A.graph → (A + B).graph := fun q =>
    ⟨(q.val.1, q.val.2 + B ⟨q.val.1, hD ((mem_graph_iff A q.val).mp q.prop).choose⟩), by
      obtain ⟨hx, hAx⟩ := (mem_graph_iff A q.val).mp q.prop
      apply (mem_graph_iff (A + B) _).mpr
      refine ⟨⟨hx, hD hx⟩, ?_⟩
      change A ⟨q.val.1, hx⟩ + B ⟨q.val.1, hD hx⟩ = _
      rw [hAx]⟩
  refine ⟨(d p.1, d p.2), ?_⟩
  have hv' : blockMap A L p + blockPerturbation A B hD p = w := by
    rw [he]
    exact hv
  convert hv' using 1
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext
  · change (p.1.val.2 + B ⟨p.1.val.1, _⟩) + L • p.2.val.1 =
      (p.1.val.2 + L • p.2.val.1) + B ⟨p.1.val.1, _⟩
    abel
  · change L • p.1.val.1 - (p.2.val.2 + B ⟨p.2.val.1, _⟩) =
      (L • p.1.val.1 - p.2.val.2) + -B ⟨p.2.val.1, _⟩
    abel

/-- Real Kato–Rellich on exactly the original domain, with unrestricted real bounds. -/
theorem kato_rellich_real : KatoRellichSpec.KatoRellichReal.{u} := by
  intro E _ _ _ A B hA hB hD a b ha hb
  let α := max a 0
  let β := max b 0
  have hα : 0 ≤ α := le_max_right _ _
  have hβ : 0 ≤ β := le_max_right _ _
  have hα1 : α < 1 := max_lt ha zero_lt_one
  have hbound (x : A.domain) : ‖B ⟨x, hD x.prop⟩‖ ≤ α * ‖A x‖ + β * ‖(x : E)‖ :=
    (hb x).trans (add_le_add
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  obtain ⟨L, hL⟩ := exists_gt (max 0 (β / (1 - α)))
  have hL0 : 0 < L := (le_max_left _ _).trans_lt hL
  have hsmall : α + β / L < 1 := by
    have h := (div_lt_iff₀ (sub_pos.mpr hα1)).mp ((le_max_right _ _).trans_lt hL)
    have hh : β / L < 1 - α := (div_lt_iff₀ hL0).mpr (by nlinarith)
    linarith
  exact ⟨selfAdjoint_of_block_surjective (A + B)
    (real_symmetric_add A B ⟨hA.1, hA.2.le⟩ hB hD) L hL0
    (perturbed_block_surjective A B hA hD α β L hα hβ hL0 hbound hsmall),
    inf_eq_left.mpr hD⟩

/-- The full real core and exact closure clause. -/
theorem kato_rellich_core_real : KatoRellichSpec.KatoRellichCoreReal.{u} := by
  intro E _ _ _ A B D₀ hA hcore hB hBD a b ha hb
  have hAc : IsClosable A := hA.2.1
  have hAs : KatoRellichSpec.realSelfAdjointValue A.closure := hA.2.2
  let C := A.domRestrict D₀
  have hCA : C ≤ A.closure := LinearPMap.domRestrict_le.trans A.le_closure
  have hCcore : C.graph.topologicalClosure = A.closure.graph :=
    hcore.2.trans hAc.graph_closure_eq_closure_graph
  have hCD : C.domain ≤ B.domain := fun x hx => hBD hx.1
  obtain ⟨hD, ⟨F, hF⟩, hbound⟩ :=
    relative_extension_from_graph_core A.closure C B hCA hCcore
      (real_symmetric_closable hB) hCD a b hb
  have hsum : KatoRellichSpec.realSelfAdjointValue (A.closure + B.closure) :=
    (kato_rellich_real A.closure B.closure hAs (real_symmetric_closure hB)
      hD a b ha hbound).1
  obtain ⟨hc, hcl⟩ := graph_core_sum_closure A.closure C B B.closure
    hCA hCcore B.le_closure hCD hD F hF (real_selfAdjoint_closed hsum)
  have hrestrict : (A + B).domRestrict D₀ = C + B := by
    apply LinearPMap.ext_iff.mpr
    refine ⟨?_, ?_⟩
    · exact (inf_assoc D₀ A.domain B.domain).symm
    · intro x hx hy
      rfl
  refine ⟨hD, ⟨F, hF⟩, hbound, hsum, ?_, ?_, ?_⟩
  · rw [hrestrict]
    exact hc
  · rw [hrestrict]
    exact hcl
  · rw [hrestrict, hcl]
    exact inf_eq_left.mpr hD


end RealPerturbation
end ExpandedFA.Unbounded
