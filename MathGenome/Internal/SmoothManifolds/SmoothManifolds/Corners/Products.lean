import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.LocalAndResolvedGeometry
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.Products

namespace SmoothManifolds.CornerProducts
open ModelData CornerData CornerProductData Set Filter
open scoped Topology

/-- Send the first constrained block, then the second constrained block, then
both free blocks to their original factor coordinates. -/
def productIndex {n m : ℕ} (k : Fin (n+1)) (l : Fin (m+1)) :
    Fin (n+m) ≃ (Fin n ⊕ Fin m) where
  toFun i :=
    if h₁ : i.val < k.val then Sum.inl ⟨i.val, by have := k.isLt; omega⟩
    else if h₂ : i.val < k.val + l.val then Sum.inr ⟨i.val-k.val, by have := l.isLt; omega⟩
    else if h₃ : i.val < n+l.val then Sum.inl ⟨i.val-l.val, by omega⟩
    else Sum.inr ⟨i.val-n, by have := i.isLt; omega⟩
  invFun j := match j with
    | Sum.inl i => if h : i.val < k.val then ⟨i.val, by have := i.isLt; omega⟩
      else ⟨i.val+l.val, by have := i.isLt; have := l.isLt; omega⟩
    | Sum.inr i => if h : i.val < l.val then ⟨k.val+i.val, by have := k.isLt; have := i.isLt; omega⟩
      else ⟨n+i.val, by have := i.isLt; omega⟩
  left_inv i := by
    have := k.isLt
    have := l.isLt
    have := i.isLt
    dsimp
    split_ifs <;> dsimp <;> split_ifs <;> apply Fin.ext <;> dsimp <;> omega
  right_inv j := by
    have hk := k.isLt
    have hl := l.isLt
    rcases j with i | i
    · have hi := i.isLt
      by_cases h : i.val < k.val
      · dsimp
        rw [ite_eq_left h]
        dsimp
        rw [dite_eq_left h]
      · have h₁ : ¬ i.val+l.val < k.val := by omega
        have h₂ : ¬ i.val+l.val < k.val+l.val := by omega
        have h₃ : i.val+l.val < n+l.val := by omega
        dsimp
        rw [ite_eq_right h]
        dsimp
        rw [dite_eq_right h₁, dite_eq_right h₂, dite_eq_left h₃]
        congr 1
        apply Fin.ext
        dsimp
        omega
    · have hi := i.isLt
      by_cases h : i.val < l.val
      · have h₁ : ¬ k.val+i.val < k.val := by omega
        have h₂ : k.val+i.val < k.val+l.val := by omega
        dsimp
        rw [ite_eq_left h]
        dsimp
        rw [dite_eq_right h₁, dite_eq_left h₂]
        congr 1
        apply Fin.ext
        dsimp
        omega
      · have h₁ : ¬ n+i.val < k.val := by omega
        have h₂ : ¬ n+i.val < k.val+l.val := by omega
        have h₃ : ¬ n+i.val < n+l.val := by omega
        dsimp
        rw [ite_eq_right h]
        dsimp
        rw [dite_eq_right h₁, dite_eq_right h₂, dite_eq_right h₃]
        congr 1
        apply Fin.ext
        dsimp
        omega

/-- A coordinate permutation, so smoothness holds on the whole ambient space. -/
noncomputable def productLinear {n m : ℕ} (k : Fin (n+1)) (l : Fin (m+1)) :
    (Euclidean n × Euclidean m) ≃L[ℝ] Euclidean (n+m) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) ℝ ℝ).symm.trans
    (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin n ⊕ Fin m => ℝ)
      (productIndex k l).symm)).toContinuousLinearEquiv

theorem productLinear_apply {n m : ℕ} (k : Fin (n+1)) (l : Fin (m+1))
    (z : Euclidean n × Euclidean m) (i : Fin (n+m)) :
    productLinear k l z i = Sum.elim z.1 z.2 (productIndex k l i) := rfl

theorem productLinear_mem {n m : ℕ} (k : Fin (n+1)) (l : Fin (m+1))
    (z : Euclidean n × Euclidean m) :
    productLinear k l z ∈ orthantSet (n+m) (constraintSum k l) ↔
      z.1 ∈ orthantSet n k ∧ z.2 ∈ orthantSet m l := by
  have hk := k.isLt
  have hl := l.isLt
  constructor
  · intro h
    constructor
    · intro i hi
      let j : Fin (n+m) := ⟨i.val, by have := i.isLt; omega⟩
      have hj := h j (by change i.val < k.val+l.val; omega)
      simpa [productLinear_apply, productIndex, j, hi] using hj
    · intro i hi
      let j : Fin (n+m) := ⟨k.val+i.val, by have := i.isLt; omega⟩
      have hj := h j (by change k.val+i.val < k.val+l.val; omega)
      have h₁ : ¬ k.val+i.val < k.val := by omega
      have h₂ : k.val+i.val < k.val+l.val := by omega
      simpa [productLinear_apply, productIndex, j, h₁, h₂] using hj
  · rintro ⟨hx, hy⟩ i hi
    change i.val < k.val+l.val at hi
    rw [productLinear_apply]
    dsimp [productIndex]
    split_ifs with h₁
    · exact hx _ h₁
    · exact hy _ (by simp; omega)

noncomputable def productCoordinates (n m : ℕ) : ProductCoordinateFamily n m :=
  fun k l => ⟨productLinear k l, productLinear_mem k l⟩

theorem orthant_product_coordinates :
    Specs.SmoothManifolds.Corners.Products.orthant_product_coordinatesType :=
  fun n m => ⟨productCoordinates n m⟩

@[simp] theorem productChart_source {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart n M) (d : CornerChart m N) :
    (productChart C c d).2.source = c.2.source ×ˢ d.2.source := by
  simp [productChart]

@[simp] theorem productChart_val {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart n M) (d : CornerChart m N) (p : M × N) :
    ((productChart C c d).2 p).val =
      (C c.1 d.1).linearEquiv ((c.2 p.1).val, (d.2 p.2).val) := rfl

theorem product_chart : Specs.SmoothManifolds.Corners.Products.product_chartType :=
  fun C c d => ⟨productChart_source C c d, productChart_val C c d⟩

/-- Inverse coordinates in a generating product chart. -/
theorem productChart_inverse {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart n M) (d : CornerChart m N)
    (x : Orthant (n+m) (constraintSum c.1 d.1))
    (hx : x ∈ (productChart C c d).2.target) :
    (C c.1 d.1).linearEquiv.symm x.val =
      ((c.2 ((productChart C c d).2.symm x).1).val,
       (d.2 ((productChart C c d).2.symm x).2).val) := by
  have h := congrArg Subtype.val ((productChart C c d).2.right_inv hx)
  rw [productChart_val] at h
  rw [← h, ContinuousLinearEquiv.symm_apply_apply]

/-- Local extensions of the factor transitions give the product transition,
conjugated by the two ambient linear coordinate identifications. -/
theorem product_transition_between {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C D : ProductCoordinateFamily n m)
    {c c' : CornerChart n M} {d d' : CornerChart m N}
    (hc : CornerCompatible c c') (hd : CornerCompatible d d') :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      ((productChart C c d).2.symm.trans (productChart D c' d').2).source
      (fun x => ((productChart C c d).2.symm.trans (productChart D c' d').2) x.val) := by
  intro x
  let e := productChart C c d
  let e' := productChart D c' d'
  let p := e.2.symm x.val
  have hp : p ∈ c.2.source ×ˢ d.2.source := by
    rw [← productChart_source C c d]
    exact e.2.map_target x.property.1
  have hp' : p ∈ c'.2.source ×ˢ d'.2.source := by
    rw [← productChart_source D c' d']
    exact x.property.2
  have hcx : c.2 p.1 ∈ (c.2.symm.trans c'.2).source := by
    refine ⟨c.2.map_source hp.1, ?_⟩
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
      c.2.left_inv hp.1] using hp'.1
  have hdx : d.2 p.2 ∈ (d.2.symm.trans d'.2).source := by
    refine ⟨d.2.map_source hp.2, ?_⟩
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
      d.2.left_inv hp.2] using hp'.2
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hc.1 ⟨c.2 p.1, hcx⟩
  obtain ⟨V, hV, hxV, G, hG, hGeq⟩ := hd.1 ⟨d.2 p.2, hdx⟩
  let L := (C c.1 d.1).linearEquiv
  let L' := (D c'.1 d'.1).linearEquiv
  let W : Set (Euclidean (n+m)) := L.symm ⁻¹' (U ×ˢ V)
  refine ⟨W, (hU.prod hV).preimage L.symm.continuous, ?_,
    fun z => L' (F (L.symm z).1, G (L.symm z).2), ?_, ?_⟩
  · change L.symm x.val.val ∈ U ×ˢ V
    rw [productChart_inverse C c d x.val x.property.1]
    exact ⟨hxU, hxV⟩
  · exact L'.contDiff.contDiffOn.comp
      ((hF.comp L.symm.contDiff.fst.contDiffOn (fun _ hz => hz.1)).prodMk
       (hG.comp L.symm.contDiff.snd.contDiffOn (fun _ hz => hz.2))) (mapsTo_univ _ _)
  · intro y hy
    let q := e.2.symm y.val
    have hq : q ∈ c.2.source ×ˢ d.2.source := by
      rw [← productChart_source C c d]
      exact e.2.map_target y.property.1
    have hq' : q ∈ c'.2.source ×ˢ d'.2.source := by
      rw [← productChart_source D c' d']
      exact y.property.2
    have hcy : c.2 q.1 ∈ (c.2.symm.trans c'.2).source := by
      refine ⟨c.2.map_source hq.1, ?_⟩
      simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
        c.2.left_inv hq.1] using hq'.1
    have hdy : d.2 q.2 ∈ (d.2.symm.trans d'.2).source := by
      refine ⟨d.2.map_source hq.2, ?_⟩
      simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
        d.2.left_inv hq.2] using hq'.2
    have hiy := productChart_inverse C c d y.val y.property.1
    change L.symm y.val.val = ((c.2 q.1).val, (d.2 q.2).val) at hiy
    change L.symm y.val.val ∈ U ×ˢ V at hy
    rw [hiy] at hy
    change L' (F (L.symm y.val.val).1, G (L.symm y.val.val).2) = (e'.2 q).val
    rw [hiy, hFeq ⟨c.2 q.1, hcy⟩ hy.1, hGeq ⟨d.2 q.2, hdy⟩ hy.2]
    change L' ((c'.2 (c.2.symm (c.2 q.1))).val,
      (d'.2 (d.2.symm (d.2 q.2))).val) = _
    rw [c.2.left_inv hq.1, d.2.left_inv hq.2]
    rfl

theorem product_transition {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    {c c' : CornerChart n M} {d d' : CornerChart m N}
    (hc : CornerCompatible c c') (hd : CornerCompatible d d') :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      ((productChart C c d).2.symm.trans (productChart C c' d').2).source
      (fun x => ((productChart C c d).2.symm.trans (productChart C c' d').2) x.val) :=
  product_transition_between C C hc hd

theorem product_compatible_between {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C D : ProductCoordinateFamily n m)
    {c c' : CornerChart n M} {d d' : CornerChart m N}
    (hc : CornerCompatible c c') (hd : CornerCompatible d d') :
    CornerCompatible (productChart C c d) (productChart D c' d') := by
  refine ⟨product_transition_between C D hc hd, ?_⟩
  simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source, inter_comm] using
      product_transition_between D C (Corners.cornerCompatible_symm hc) (Corners.cornerCompatible_symm hd)

theorem product_compatible {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    {c c' : CornerChart n M} {d d' : CornerChart m N}
    (hc : CornerCompatible c c') (hd : CornerCompatible d d') :
    CornerCompatible (productChart C c d) (productChart C c' d') := by
  refine ⟨product_transition C hc hd, ?_⟩
  simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source, inter_comm] using
      product_transition C (Corners.cornerCompatible_symm hc) (Corners.cornerCompatible_symm hd)

theorem product_atlas : Specs.SmoothManifolds.Corners.Products.product_atlasType := by
  intro n m M N _ _ C A B hA hB
  constructor
  · intro p
    obtain ⟨c, hc, hp⟩ := hA.1 p.1
    obtain ⟨d, hd, hq⟩ := hB.1 p.2
    exact ⟨productChart C c d, ⟨c, hc, d, hd, rfl⟩, by
      rw [productChart_source]; exact ⟨hp, hq⟩⟩
  · rintro _ ⟨c, hc, d, hd, rfl⟩ _ ⟨c', hc', d', hd', rfl⟩
    exact product_compatible C (hA.2 c hc c' hc') (hB.2 d hd d' hd')

theorem product_corner_structure :
    Specs.SmoothManifolds.Corners.Products.product_corner_structureType := by
  intro n m M N _ _ S T C
  let : T2Space M := S.hausdorff
  let : T2Space N := T.hausdorff
  let : SecondCountableTopology M := S.secondCountable
  let : SecondCountableTopology N := T.secondCountable
  have hA := product_atlas C S.atlas T.atlas S.maximal.1 T.maximal.1
  exact ⟨⟨inferInstance, inferInstance, _, Corners.cornerMaximalExtension_isMaximal hA⟩,
    rfl, Corners.cornerAtlas_subset_maximalExtension hA⟩

/-- Move the manuscript's last constrained coordinate to the first position. -/
noncomputable def halfSpaceOrthantLinear (n : ℕ) :
    Euclidean (n+1) ≃L[ℝ] Euclidean (n+1) :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin (n+1) => ℝ)
    (Equiv.swap 0 (Fin.last n))).toContinuousLinearEquiv

@[simp] theorem halfSpaceOrthantLinear_zero (n : ℕ) (x : Euclidean (n+1)) :
    halfSpaceOrthantLinear n x 0 = x (Fin.last n) := by
  simp [halfSpaceOrthantLinear, LinearEquiv.piCongrLeft', Equiv.piCongrLeft']

noncomputable def ordinaryCoordinates : (n : ℕ) → (a : ModelKind) → ModelOrthantCoordinates n a
  | 0, a => ⟨ContinuousLinearEquiv.refl ℝ _, by
      intro x; cases a <;> simp [ModelData.orthantSet, ModelData.modelSet, ModelData.halfSpaceSet, modelConstraintCount]⟩
  | n+1, .euclidean => ⟨ContinuousLinearEquiv.refl ℝ _, by
      intro x; simp [ModelData.orthantSet, ModelData.modelSet, modelConstraintCount]⟩
  | n+1, .halfSpace => ⟨halfSpaceOrthantLinear n, by
      intro x
      change (∀ i : Fin (n+1), i.val < 1 → 0 ≤ halfSpaceOrthantLinear n x i) ↔
        0 ≤ x (Fin.last n)
      constructor
      · intro h
        simpa using h 0 (by simp)
      · intro h i hi
        have he : i = 0 := Fin.ext (by change i.val = 0; omega)
        simpa [he] using h⟩

theorem ordinary_model_coordinates :
    Specs.SmoothManifolds.Corners.Products.ordinary_model_coordinatesType :=
  fun n a => ⟨ordinaryCoordinates n a⟩

@[simp] theorem ordinaryCornerChart_source {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (E : ModelOrthantCoordinates n a) (c : ModelChart n a M) :
    (ordinaryCornerChart E c).2.source = c.source := by simp [ordinaryCornerChart]

@[simp] theorem ordinaryCornerChart_val {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (E : ModelOrthantCoordinates n a) (c : ModelChart n a M) (p : M) :
    ((ordinaryCornerChart E c).2 p).val = E.linearEquiv (c p).val := rfl

theorem ordinaryCornerChart_inverse {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (E : ModelOrthantCoordinates n a) (c : ModelChart n a M)
    (x : Orthant n (modelConstraintCount n a))
    (hx : x ∈ (ordinaryCornerChart E c).2.target) :
    E.linearEquiv.symm x.val = (c ((ordinaryCornerChart E c).2.symm x)).val := by
  have h := congrArg Subtype.val ((ordinaryCornerChart E c).2.right_inv hx)
  rw [ordinaryCornerChart_val] at h
  rw [← h, ContinuousLinearEquiv.symm_apply_apply]

theorem ordinary_transition_between {n : ℕ} {a : ModelKind} {M : Type*} [TopologicalSpace M]
    (E F : ModelOrthantCoordinates n a) {c d : ModelChart n a M}
    (hcd : ContDiffCompatible (⊤ : ℕ∞) c d) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      ((ordinaryCornerChart E c).2.symm.trans (ordinaryCornerChart F d).2).source
      (fun x => ((ordinaryCornerChart E c).2.symm.trans (ordinaryCornerChart F d).2) x.val) := by
  intro x
  let e := ordinaryCornerChart E c
  let e' := ordinaryCornerChart F d
  let p := e.2.symm x.val
  have hp : p ∈ c.source := by
    rw [← ordinaryCornerChart_source E c]; exact e.2.map_target x.property.1
  have hp' : p ∈ d.source := by
    rw [← ordinaryCornerChart_source F d]; exact x.property.2
  have hx : c p ∈ (c.symm.trans d).source := by
    refine ⟨c.map_source hp, ?_⟩
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv hp] using hp'
  obtain ⟨U, hU, hxU, H, hH, hHeq⟩ := hcd.1 (c p) hx
  let L := E.linearEquiv
  let K := F.linearEquiv
  refine ⟨L.symm ⁻¹' U, hU.preimage L.symm.continuous, ?_,
    fun z => K (H (L.symm z)), ?_, ?_⟩
  · change L.symm x.val.val ∈ U
    rw [ordinaryCornerChart_inverse E c x.val x.property.1]
    exact hxU
  · exact K.contDiff.contDiffOn.comp
      (hH.comp L.symm.contDiff.contDiffOn (fun _ hz => hz)) (mapsTo_univ _ _)
  · intro y hy
    let q := e.2.symm y.val
    have hq : q ∈ c.source := by
      rw [← ordinaryCornerChart_source E c]; exact e.2.map_target y.property.1
    have hq' : q ∈ d.source := by
      rw [← ordinaryCornerChart_source F d]; exact y.property.2
    have hcy : c q ∈ (c.symm.trans d).source := by
      refine ⟨c.map_source hq, ?_⟩
      simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv hq] using hq'
    have hiy := ordinaryCornerChart_inverse E c y.val y.property.1
    change L.symm y.val.val = (c q).val at hiy
    change L.symm y.val.val ∈ U at hy
    rw [hiy] at hy
    change K (H (L.symm y.val.val)) = (e'.2 q).val
    rw [hiy, hHeq (c q) hcy hy]
    change K (d (c.symm (c q))).val = _
    rw [c.left_inv hq]
    rfl

theorem ordinary_transition {n : ℕ} {a : ModelKind} {M : Type*} [TopologicalSpace M]
    (E : ModelOrthantCoordinates n a) {c d : ModelChart n a M}
    (hcd : ContDiffCompatible (⊤ : ℕ∞) c d) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      ((ordinaryCornerChart E c).2.symm.trans (ordinaryCornerChart E d).2).source
      (fun x => ((ordinaryCornerChart E c).2.symm.trans (ordinaryCornerChart E d).2) x.val) :=
  ordinary_transition_between E E hcd

theorem ordinary_compatible_between {n : ℕ} {a : ModelKind} {M : Type*} [TopologicalSpace M]
    (E F : ModelOrthantCoordinates n a) {c d : ModelChart n a M}
    (hcd : ContDiffCompatible (⊤ : ℕ∞) c d) :
    CornerCompatible (ordinaryCornerChart E c) (ordinaryCornerChart F d) := by
  refine ⟨ordinary_transition_between E F hcd, ?_⟩
  have hdc : ContDiffCompatible (⊤ : ℕ∞) d c := by
    simpa [AtlasData.ContDiffCompatible, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source, inter_comm] using hcd.symm
  simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source, inter_comm] using
      ordinary_transition_between F E hdc

theorem ordinary_compatible {n : ℕ} {a : ModelKind} {M : Type*} [TopologicalSpace M]
    (E : ModelOrthantCoordinates n a) {c d : ModelChart n a M}
    (hcd : ContDiffCompatible (⊤ : ℕ∞) c d) :
    CornerCompatible (ordinaryCornerChart E c) (ordinaryCornerChart E d) :=
  ordinary_compatible_between E E hcd

theorem ordinary_atlas {n : ℕ} {a : ModelKind} {M : Type*} [TopologicalSpace M]
    (E : ModelOrthantCoordinates n a) {A : Set (ModelChart n a M)}
    (hA : IsContDiffAtlas (⊤ : ℕ∞) A) : IsSmoothCornerAtlas (ordinaryCornerAtlas E A) := by
  constructor
  · intro p
    obtain ⟨c, hc, hp⟩ := hA.1 p
    exact ⟨ordinaryCornerChart E c, ⟨c, hc, rfl⟩, by simpa using hp⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    exact ordinary_compatible E (hA.2 c hc d hd)

theorem ordinary_corner_bridge :
    Specs.SmoothManifolds.Corners.Products.ordinary_corner_bridgeType := by
  intro n a M _ S E
  have hA := ordinary_atlas E S.smoothStructure.property.1
  exact ⟨⟨S.topologicalManifold.hausdorff, S.topologicalManifold.secondCountable,
    _, Corners.cornerMaximalExtension_isMaximal hA⟩, rfl,
    Corners.cornerAtlas_subset_maximalExtension hA⟩

/-- It suffices to check target charts in a generating atlas. -/
theorem coordinateSmooth_target_of_cover {n m : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {B : Set (CornerChart m Y)} (hcover : ∀ p : Y, ∃ b ∈ B, p ∈ b.2.source)
    (c : CornerChart n X) (d : CornerChart m Y) (hd : d ∈ cornerMaximalExtension B)
    (f : X → Y) (hf : Continuous f)
    (hfb : ∀ b ∈ B, OrthantMapContDiffOn (⊤ : ℕ∞)
      {x : Orthant n c.1 | x ∈ c.2.target ∧ f (c.2.symm x) ∈ b.2.source}
      (fun x => b.2 (f (c.2.symm x.val)))) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      {x : Orthant n c.1 | x ∈ c.2.target ∧ f (c.2.symm x) ∈ d.2.source}
      (fun x => d.2 (f (c.2.symm x.val))) := by
  intro x
  let p := c.2.symm x.val
  obtain ⟨b, hb, hpb⟩ := hcover (f p)
  let t := b.2.symm.trans d.2
  have hxt : b.2 (f p) ∈ t.source := by
    refine ⟨b.2.map_source hpb, ?_⟩
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, b.2.left_inv hpb] using x.property.2
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hfb b hb ⟨x.val, x.property.1, hpb⟩
  obtain ⟨V, hV, hxV, G, hG, hGeq⟩ := (Corners.cornerCompatible_symm (hd b hb)).1 ⟨b.2 (f p), hxt⟩
  have hopen : IsOpen {y : Orthant n c.1 | y ∈ c.2.target ∧ f (c.2.symm y) ∈ b.2.source} :=
    (hf.comp_continuousOn c.2.continuousOn_symm).isOpen_inter_preimage c.2.open_target b.2.open_source
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp hopen
  have hxW : x.val.val ∈ W := by
    change x.val ∈ Subtype.val ⁻¹' W
    rw [hWeq]
    exact ⟨x.property.1, hpb⟩
  refine ⟨(U ∩ W) ∩ F ⁻¹' V,
    (hF.mono inter_subset_left).continuousOn.isOpen_inter_preimage (hU.inter hW) hV,
    ⟨⟨hxU, hxW⟩, ?_⟩, G ∘ F,
    hG.comp (hF.mono (inter_subset_left.trans inter_subset_left)) (fun _ hy => hy.2), ?_⟩
  · change F x.val.val ∈ V
    rwa [hFeq ⟨x.val, x.property.1, hpb⟩ hxU]
  · intro y hy
    have hyb : y.val ∈ {z : Orthant n c.1 | z ∈ c.2.target ∧ f (c.2.symm z) ∈ b.2.source} := by
      rw [← hWeq]; exact hy.1.2
    let q := f (c.2.symm y.val)
    have hqb : q ∈ b.2.source := hyb.2
    have hyt : b.2 q ∈ t.source := by
      refine ⟨b.2.map_source hqb, ?_⟩
      simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, b.2.left_inv hqb] using y.property.2
    change G (F y.val.val) = (d.2 q).val
    rw [hFeq ⟨y.val, hyb⟩ hy.1.1]
    have hyV : (b.2 q).val ∈ V := by
      have hh := hy.2
      change F y.val.val ∈ V at hh
      rwa [hFeq ⟨y.val, hyb⟩ hy.1.1] at hh
    rw [hGeq ⟨b.2 q, hyt⟩ hyV]
    change (d.2 (b.2.symm (b.2 q))).val = _
    rw [b.2.left_inv hqb]

theorem generating_fst_smooth {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart n M) (d : CornerChart m N) (a : CornerChart n M)
    (ha : CornerCompatible c a) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      {x | x ∈ (productChart C c d).2.target ∧
        ((productChart C c d).2.symm x).1 ∈ a.2.source}
      (fun x => a.2 (((productChart C c d).2.symm x.val).1)) := by
  intro x
  let e := productChart C c d
  let p := e.2.symm x.val
  have hp : p ∈ c.2.source ×ˢ d.2.source := by
    rw [← productChart_source C c d]; exact e.2.map_target x.property.1
  have hx : c.2 p.1 ∈ (c.2.symm.trans a.2).source := by
    refine ⟨c.2.map_source hp.1, ?_⟩
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
      c.2.left_inv hp.1] using x.property.2
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := ha.1 ⟨c.2 p.1, hx⟩
  let L := (C c.1 d.1).linearEquiv
  refine ⟨(fun z => (L.symm z).1) ⁻¹' U,
    hU.preimage L.symm.continuous.fst, ?_, fun z => F (L.symm z).1,
    hF.comp L.symm.contDiff.fst.contDiffOn (fun _ hz => hz), ?_⟩
  · change (L.symm x.val.val).1 ∈ U
    rw [productChart_inverse C c d x.val x.property.1]
    exact hxU
  · intro y hy
    let q := e.2.symm y.val
    have hq : q ∈ c.2.source ×ˢ d.2.source := by
      rw [← productChart_source C c d]; exact e.2.map_target y.property.1
    have hcy : c.2 q.1 ∈ (c.2.symm.trans a.2).source := by
      refine ⟨c.2.map_source hq.1, ?_⟩
      simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
        c.2.left_inv hq.1] using y.property.2
    have hiy := productChart_inverse C c d y.val y.property.1
    change L.symm y.val.val = ((c.2 q.1).val, (d.2 q.2).val) at hiy
    change (L.symm y.val.val).1 ∈ U at hy
    rw [hiy] at hy
    change F (L.symm y.val.val).1 = (a.2 q.1).val
    rw [hiy, hFeq ⟨c.2 q.1, hcy⟩ hy]
    change (a.2 (c.2.symm (c.2 q.1))).val = _
    rw [c.2.left_inv hq.1]

theorem generating_snd_smooth {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart n M) (d : CornerChart m N) (a : CornerChart m N)
    (ha : CornerCompatible d a) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      {x | x ∈ (productChart C c d).2.target ∧
        ((productChart C c d).2.symm x).2 ∈ a.2.source}
      (fun x => a.2 (((productChart C c d).2.symm x.val).2)) := by
  intro x
  let e := productChart C c d
  let p := e.2.symm x.val
  have hp : p ∈ c.2.source ×ˢ d.2.source := by
    rw [← productChart_source C c d]; exact e.2.map_target x.property.1
  have hx : d.2 p.2 ∈ (d.2.symm.trans a.2).source := by
    refine ⟨d.2.map_source hp.2, ?_⟩
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
      d.2.left_inv hp.2] using x.property.2
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := ha.1 ⟨d.2 p.2, hx⟩
  let L := (C c.1 d.1).linearEquiv
  refine ⟨(fun z => (L.symm z).2) ⁻¹' U,
    hU.preimage L.symm.continuous.snd, ?_, fun z => F (L.symm z).2,
    hF.comp L.symm.contDiff.snd.contDiffOn (fun _ hz => hz), ?_⟩
  · change (L.symm x.val.val).2 ∈ U
    rw [productChart_inverse C c d x.val x.property.1]
    exact hxU
  · intro y hy
    let q := e.2.symm y.val
    have hq : q ∈ c.2.source ×ˢ d.2.source := by
      rw [← productChart_source C c d]; exact e.2.map_target y.property.1
    have hcy : d.2 q.2 ∈ (d.2.symm.trans a.2).source := by
      refine ⟨d.2.map_source hq.2, ?_⟩
      simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
        d.2.left_inv hq.2] using y.property.2
    have hiy := productChart_inverse C c d y.val y.property.1
    change L.symm y.val.val = ((c.2 q.1).val, (d.2 q.2).val) at hiy
    change (L.symm y.val.val).2 ∈ U at hy
    rw [hiy] at hy
    change F (L.symm y.val.val).2 = (a.2 q.2).val
    rw [hiy, hFeq ⟨d.2 q.2, hcy⟩ hy]
    change (a.2 (d.2.symm (d.2 q.2))).val = _
    rw [d.2.left_inv hq.2]

theorem product_projections :
    Specs.SmoothManifolds.Corners.Products.product_projectionsType := by
  intro n m M N _ _ S T C P hP
  have hA := product_atlas C S.atlas T.atlas S.maximal.1 T.maximal.1
  constructor
  · refine ⟨continuous_fst, ?_⟩
    intro e he a ha
    rw [hP] at he
    apply Corners.cornerCoordinateSmooth_of_cover hA.1 e he a Prod.fst
    rintro _ ⟨c, hc, d, hd, rfl⟩
    exact generating_fst_smooth C c d a (S.maximal.1.2 c hc a ha)
  · refine ⟨continuous_snd, ?_⟩
    intro e he a ha
    rw [hP] at he
    apply Corners.cornerCoordinateSmooth_of_cover hA.1 e he a Prod.snd
    rintro _ ⟨c, hc, d, hd, rfl⟩
    exact generating_snd_smooth C c d a (T.maximal.1.2 d hd a ha)

theorem generating_left_inclusion_smooth {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart n M) (a : CornerChart n M) (b : CornerChart m N)
    (hc : CornerCompatible c a) (q : N) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      {x : Orthant n c.1 | x ∈ c.2.target ∧
        (c.2.symm x,q) ∈ (productChart C a b).2.source}
      (fun x => (productChart C a b).2 (c.2.symm x.val,q)) := by
  intro x
  have hx : x.val ∈ (c.2.symm.trans a.2).source := by
    refine ⟨x.property.1, ?_⟩
    have hh := x.property.2
    simp only [productChart_source] at hh
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage] using hh.1
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hc.1 ⟨x.val, hx⟩
  let L := (C a.1 b.1).linearEquiv
  refine ⟨U, hU, hxU, fun z => L (F z, (b.2 q).val),
    L.contDiff.contDiffOn.comp (hF.prodMk contDiffOn_const) (mapsTo_univ _ _), ?_⟩
  intro y hy
  have hcy : y.val ∈ (c.2.symm.trans a.2).source := by
    refine ⟨y.property.1, ?_⟩
    have hh := y.property.2
    simp only [productChart_source] at hh
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage] using hh.1
  change L (F y.val.val, (b.2 q).val) =
    ((productChart C a b).2 (c.2.symm y.val,q)).val
  rw [productChart_val]
  rw [hFeq ⟨y.val, hcy⟩ hy]
  rfl

theorem generating_right_inclusion_smooth {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart m N) (a : CornerChart n M) (b : CornerChart m N)
    (hc : CornerCompatible c b) (p : M) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      {x : Orthant m c.1 | x ∈ c.2.target ∧
        (p,c.2.symm x) ∈ (productChart C a b).2.source}
      (fun x => (productChart C a b).2 (p,c.2.symm x.val)) := by
  intro x
  have hx : x.val ∈ (c.2.symm.trans b.2).source := by
    refine ⟨x.property.1, ?_⟩
    have hh := x.property.2
    simp only [productChart_source] at hh
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage] using hh.2
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hc.1 ⟨x.val, hx⟩
  let L := (C a.1 b.1).linearEquiv
  refine ⟨U, hU, hxU, fun z => L ((a.2 p).val, F z),
    L.contDiff.contDiffOn.comp (contDiffOn_const.prodMk hF) (mapsTo_univ _ _), ?_⟩
  intro y hy
  have hcy : y.val ∈ (c.2.symm.trans b.2).source := by
    refine ⟨y.property.1, ?_⟩
    have hh := y.property.2
    simp only [productChart_source] at hh
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage] using hh.2
  change L ((a.2 p).val, F y.val.val) =
    ((productChart C a b).2 (p,c.2.symm y.val)).val
  rw [productChart_val]
  rw [hFeq ⟨y.val, hcy⟩ hy]
  rfl

theorem product_inclusions :
    Specs.SmoothManifolds.Corners.Products.product_inclusionsType := by
  intro n m M N _ _ S T C P hP
  have hA := product_atlas C S.atlas T.atlas S.maximal.1 T.maximal.1
  constructor
  · intro q
    refine ⟨continuous_id.prodMk continuous_const, ?_⟩
    intro c hc e he
    rw [hP] at he
    apply coordinateSmooth_target_of_cover hA.1 c e he (fun p => (p,q))
      (continuous_id.prodMk continuous_const)
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact generating_left_inclusion_smooth C c a b (S.maximal.1.2 c hc a ha) q
  · intro p
    refine ⟨continuous_const.prodMk continuous_id, ?_⟩
    intro c hc e he
    rw [hP] at he
    apply coordinateSmooth_target_of_cover hA.1 c e he (fun q => (p,q))
      (continuous_const.prodMk continuous_id)
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact generating_right_inclusion_smooth C c a b (T.maximal.1.2 c hc b hb) p

attribute [local instance] Classical.propDecidable

theorem ordinaryCoordinates_depth (n : ℕ) (a : ModelKind) (x : ModelSpace n a) :
    modelDepth ((ordinaryCoordinates n a).homeomorph x) =
      if x.val ∈ BoundaryData.modelFace n a then 1 else 0 := by
  classical
  cases n with
  | zero =>
    cases a <;>
      simp [modelDepth, activeCoordinates, modelConstraintCount, ordinaryCoordinates,
        BoundaryData.modelFace, ModelData.halfSpaceFace]
  | succ n =>
    cases a with
    | euclidean =>
      simp [modelDepth, activeCoordinates, modelConstraintCount, ordinaryCoordinates,
        BoundaryData.modelFace]
    | halfSpace =>
      have hzero : ((ordinaryCoordinates (n+1) .halfSpace).homeomorph x).val 0 =
          x.val (Fin.last n) := halfSpaceOrthantLinear_zero n x.val
      have hactive : activeCoordinates ((ordinaryCoordinates (n+1) .halfSpace).homeomorph x) =
          if x.val (Fin.last n) = 0 then {0} else ∅ := by
        ext i
        simp only [activeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
        change (i.val < 1 ∧ ((ordinaryCoordinates (n+1) .halfSpace).homeomorph x).val i = 0) ↔ _
        by_cases hi : i = 0
        · subst i
          rw [hzero]
          split_ifs <;> simp_all
        · have hi' : ¬ i.val < 1 := by
            intro hi'
            apply hi
            exact Fin.ext (by change i.val = 0; omega)
          split_ifs <;> simp_all
      simp only [modelDepth, hactive, BoundaryData.modelFace, ModelData.halfSpaceFace, mem_ofPred_eq]
      split_ifs <;> simp_all

theorem ordinary_boundary_faces :
    Specs.SmoothManifolds.Corners.Products.ordinary_boundary_facesType := by
  classical
  intro n a M _ S
  let E := ordinaryCoordinates n a
  obtain ⟨R, hR, hsub⟩ := ordinary_corner_bridge S E
  refine ⟨E, R, hR, ?_⟩
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let d := ordinaryCornerChart E c
  have hd : d ∈ R.atlas := hsub ⟨c,hc,rfl⟩
  have hpd : p ∈ d.2.source := by simpa [d] using hp
  rw [(Corners.local_face_cardinality R d hd p hpd).2]
  change modelDepth (E.homeomorph (c p)) = _
  rw [ordinaryCoordinates_depth]
  rw [intrinsicBoundary_iff_chart S c hc p hp]


theorem boundary_product : Specs.SmoothManifolds.Corners.Products.boundary_productType := by
  intro n m a b M N _ _ S T
  obtain ⟨E, R, hR, hRfaces⟩ := ordinary_boundary_faces S
  obtain ⟨F, Q, hQ, hQfaces⟩ := ordinary_boundary_faces T
  let C := productCoordinates n m
  obtain ⟨P, hP, _⟩ := product_corner_structure R Q C
  have hproj := product_projections R Q C P hP
  have hinc := product_inclusions R Q C P hP
  exact ⟨E, F, R, Q, C, P, hR, hQ, hP, hproj.1, hproj.2, hinc.1, hinc.2, hRfaces, hQfaces⟩

theorem coordinate_tangent_sum :
    Specs.SmoothManifolds.Corners.Products.coordinate_tangent_sumType := by
  intro n m M N _ _ C c d
  let L := (C c.1 d.1).linearEquiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (productChart_inverse C c d x hx).symm
  · intro z
    exact ⟨(ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean m)).hasFDerivAt.comp z L.symm.hasFDerivAt,
      (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean m)).hasFDerivAt.comp z L.symm.hasFDerivAt⟩
  · intro q x hx
    rw [productChart_val, c.2.right_inv hx]
  · intro p y hy
    rw [productChart_val, d.2.right_inv hy]
  · intro v x
    exact L.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x v)
  · intro u y
    exact L.hasFDerivAt.comp y (hasFDerivAt_prodMk_right u y)

theorem transition_derivative :
    Specs.SmoothManifolds.Corners.Products.transition_derivativeType := by
  intro n m k k' l l' C D F G x A B hF hG
  exact D.linearEquiv.hasFDerivAt.comp x
    ((HasFDerivAt.prodMap (C.linearEquiv.symm x) hF hG).comp x C.linearEquiv.symm.hasFDerivAt)

theorem productIndex_constrained {n m : ℕ} (k : Fin (n+1)) (l : Fin (m+1))
    (i : Fin (n+m)) : i.val < k.val+l.val ↔
    Sum.elim (fun j : Fin n => j.val < k.val) (fun j : Fin m => j.val < l.val) (productIndex k l i) := by
  have hk := k.isLt
  have hl := l.isLt
  dsimp [productIndex]
  split_ifs <;> dsimp <;> omega

noncomputable def productLabels {n m : ℕ} (k : Fin (n+1)) (l : Fin (m+1)) :
    ProductLabels (productCoordinates n m k l) :=
  ⟨productIndex k l, productIndex_constrained k l, productLinear_apply k l⟩

theorem labelled_product_coordinates :
    Specs.SmoothManifolds.Corners.Products.labelled_product_coordinatesType :=
  fun n m => ⟨productCoordinates n m, fun k l => ⟨productLabels k l⟩⟩

/-- The active coordinates of a product point split into two tagged families. -/
noncomputable def activeSumEquiv {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart n M) (d : CornerChart m N) (L : ProductLabels (C c.1 d.1))
    (p : M × N) :
    activeCoordinates ((productChart C c d).2 p) ≃
      (activeCoordinates (c.2 p.1) ⊕ activeCoordinates (d.2 p.2)) := by
  classical
  let Q : Fin n ⊕ Fin m → Prop :=
    Sum.elim (fun i => i ∈ activeCoordinates (c.2 p.1))
      (fun i => i ∈ activeCoordinates (d.2 p.2))
  have h : ∀ i, i ∈ activeCoordinates ((productChart C c d).2 p) ↔ Q (L.indexEquiv i) := by
    intro i
    have hi := L.constrained i
    simp only [activeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [productChart_val, L.coordinate]
    rcases he : L.indexEquiv i with j | j
    · simpa [Q, activeCoordinates, he, productChart, constraintSum] using and_congr hi (Iff.rfl :
        Sum.elim (c.2 p.1).val (d.2 p.2).val (L.indexEquiv i) = 0 ↔
        Sum.elim (c.2 p.1).val (d.2 p.2).val (L.indexEquiv i) = 0)
    · simpa [Q, activeCoordinates, he, productChart, constraintSum] using and_congr hi (Iff.rfl :
        Sum.elim (c.2 p.1).val (d.2 p.2).val (L.indexEquiv i) = 0 ↔
        Sum.elim (c.2 p.1).val (d.2 p.2).val (L.indexEquiv i) = 0)
  exact (L.indexEquiv.subtypeEquiv h).trans Equiv.subtypeSum

theorem activeSumEquiv_index {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (C : ProductCoordinateFamily n m)
    (c : CornerChart n M) (d : CornerChart m N) (L : ProductLabels (C c.1 d.1))
    (p : M × N) (a : activeCoordinates ((productChart C c d).2 p)) :
    Sum.map Subtype.val Subtype.val (activeSumEquiv C c d L p a) = L.indexEquiv a.val := by
  dsimp only [activeSumEquiv, Equiv.trans, Equiv.subtypeEquiv]
  rcases h : L.indexEquiv a.val with j | j <;> simp [Equiv.subtypeSum, h]

theorem product_face_germs : Specs.SmoothManifolds.Corners.Products.product_face_germsType := by
  classical
  intro n m M N _ _ C c d L P he p hp
  let e := productChart C c d
  have hpe : p ∈ e.2.source := by rw [productChart_source]; exact hp
  let E := activeSumEquiv C c d L p
  let g := chartFaceAt P e he p hpe
  let f := g ∘ E.symm
  refine ⟨f, (Corners.chart_face_germs P e he p hpe).comp E.symm.bijective, ?_⟩
  have h : ∀ a : activeCoordinates (e.2 p), (g a).val = factorFaceGerm c d p (E a) := by
    intro a
    change chartFaceGerm e p a.val = _
    have hE := activeSumEquiv_index C c d L p a
    change Sum.map Subtype.val Subtype.val (E a) = L.indexEquiv a.val at hE
    rcases hEa : E a with j | j
    · have hσ : L.indexEquiv a.val = Sum.inl j.val := by rw [← hE, hEa]; rfl
      have hv : ∀ q : M × N, (e.2 q).val a.val = (c.2 q.1).val j.val := by
        intro q
        rw [productChart_val, L.coordinate, hσ]
        rfl
      change _ = (chartFaceGerm c p.1 j.val).compTendsto Prod.fst continuous_fst.continuousAt
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [continuous_snd.continuousAt (d.2.open_source.mem_nhds hp.2)] with q hq
      change (q ∈ e.2.source ∧ (e.2 q).val a.val = 0) =
        (q.1 ∈ c.2.source ∧ (c.2 q.1).val j.val = 0)
      rw [productChart_source, hv]
      change q.2 ∈ d.2.source at hq
      simp only [mem_prod, hq, and_true]
    · have hσ : L.indexEquiv a.val = Sum.inr j.val := by rw [← hE, hEa]; rfl
      have hv : ∀ q : M × N, (e.2 q).val a.val = (d.2 q.2).val j.val := by
        intro q
        rw [productChart_val, L.coordinate, hσ]
        rfl
      change _ = (chartFaceGerm d p.2 j.val).compTendsto Prod.snd continuous_snd.continuousAt
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [continuous_fst.continuousAt (c.2.open_source.mem_nhds hp.1)] with q hq
      change (q ∈ e.2.source ∧ (e.2 q).val a.val = 0) =
        (q.2 ∈ d.2.source ∧ (d.2 q.2).val j.val = 0)
      rw [productChart_source, hv]
      change q.1 ∈ c.2.source at hq
      simp only [mem_prod, hq, true_and]
  intro i
  simpa [f] using h (E.symm i)

/-- The interval is the actual subtype of the real line, identified with its
one-coordinate box without changing its topology. -/
def intervalBoxHomeomorph (a b : ℝ) :
    Icc a b ≃ₜ ClosedBox (fun _ : Fin 1 => a) (fun _ => b) where
  toFun x := ⟨fun _ => x.val, fun _ => x.property⟩
  invFun y := ⟨y.val 0, y.property 0⟩
  left_inv x := rfl
  right_inv y := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
  continuous_toFun := (continuous_pi (fun _ => continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _

def pullbackChart {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) (c : CornerChart n Y) : CornerChart n X :=
  ⟨c.1, H.transOpenPartialHomeomorph c.2⟩

theorem pullback_compatible {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) {c d : CornerChart n Y} (h : CornerCompatible c d) :
    CornerCompatible (pullbackChart H c) (pullbackChart H d) := by
  have he : (H.transOpenPartialHomeomorph c.2).symm.trans
      (H.transOpenPartialHomeomorph d.2) = c.2.symm.trans d.2 := by
    simp [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc H.toOpenPartialHomeomorph.symm,
      Homeomorph.transOpenPartialHomeomorph_eq_trans]
  let F : OpenPartialHomeomorph (Orthant n c.1) (Orthant n d.1) → Prop := fun e =>
    OrthantMapContDiffOn (⊤ : ℕ∞) e.source (fun x => e x.val) ∧
    OrthantMapContDiffOn (⊤ : ℕ∞) e.target (fun x => e.symm x.val)
  exact (congrArg F he).mpr h

theorem interval_charts : Specs.SmoothManifolds.Corners.Products.interval_chartsType := by
  classical
  intro a b hab
  let A : Euclidean 1 := fun _ => a
  let B : Euclidean 1 := fun _ => b
  obtain ⟨J, d, hd, hcover, _⟩ := CornerExamples.box_corner_charts 1 A B (fun _ => hab)
  let H := intervalBoxHomeomorph a b
  let c : Bool → CornerChart 1 (Icc a b) := fun s => pullbackChart H (d (fun _ => s))
  have hC : IsSmoothCornerAtlas (Set.range c) := by
    constructor
    · intro x
      obtain ⟨ε, hx⟩ := hcover (H x)
      have hε : ε = fun _ => ε 0 := by funext i; congr 1; exact Subsingleton.elim _ _
      refine ⟨c (ε 0), mem_range_self _, ?_⟩
      change H x ∈ (d (fun _ => ε 0)).2.source
      rwa [← hε]
    · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact pullback_compatible H (J.maximal.1.2 _ (hd _).1 _ (hd _).1)
  let I : CornerManifold 1 (Icc a b) :=
    ⟨inferInstance, inferInstance, cornerMaximalExtension (range c),
      Corners.cornerMaximalExtension_isMaximal hC⟩
  have hdata : ∀ s, c s ∈ I.atlas ∧ (c s).1 = 1 ∧
      (c s).2.source = {x | if s then a < x.val else x.val < b} ∧
      ∀ x, ((c s).2 x).val 0 = if s then b - x.val else x.val - a := by
    intro s
    refine ⟨Corners.cornerAtlas_subset_maximalExtension hC (mem_range_self s),
      (hd (fun _ => s)).2.1, ?_, ?_⟩
    · change H ⁻¹' (d (fun _ => s)).2.source = _
      rw [(hd _).2.2.1]
      ext x
      change (∀ i : Fin 1, if s then a < x.val else x.val < b) ↔ _
      exact ⟨fun h => h 0, fun h _ => h⟩
    · intro x
      change ((d (fun _ => s)).2 (H x)).val 0 = _
      rw [(hd _).2.2.2.2.1]
      rfl
  have hcCover : ∀ x : Icc a b, ∃ s, x ∈ (c s).2.source := by
    intro x
    obtain ⟨e, ⟨s, rfl⟩, hx⟩ := hC.1 x
    exact ⟨s, hx⟩
  refine ⟨I, c, hdata, hcCover, ?_⟩
  intro s x i
  have hi : i = 0 := Subsingleton.elim _ _
  simp only [activeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
    (hdata s).2.1, hi]
  rw [(hdata s).2.2.2 x]
  cases s <;> simp <;> constructor <;> intro h <;> linarith

theorem interval_boundary_product :
    Specs.SmoothManifolds.Corners.Products.interval_boundary_productType := by
  intro a b hab n k N _ T
  obtain ⟨I, c, hI⟩ := interval_charts a b hab
  obtain ⟨E, Q, hQ, hQfaces⟩ := ordinary_boundary_faces T
  let C := productCoordinates 1 n
  obtain ⟨P, hP, hsub⟩ := product_corner_structure I Q C
  have hproj := product_projections I Q C P hP
  refine ⟨I, c, E, Q, C, P, hI, hQ, hP, hproj.1, hproj.2, hQfaces, ?_⟩
  intro s d hd
  have he : productChart C (c s) d ∈ P.atlas :=
    hsub ⟨c s, (hI.1 s).1, d, hd, rfl⟩
  refine ⟨he, ?_⟩
  intro p hp
  exact product_face_germs C (c s) d (productLabels (c s).1 d.1) P he p hp

theorem cornerMaximalExtension_of_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    {A B : Set (CornerChart n M)} (hA : IsSmoothCornerAtlas A)
    (hB : IsSmoothCornerAtlas B) (hAB : A ⊆ B) :
    cornerMaximalExtension A = cornerMaximalExtension B := by
  apply Set.Subset.antisymm
  · intro c hc b hb
    exact Corners.cornerCompatible_of_cover hA.1 hc (fun a ha => hB.2 b hb a (hAB ha))
  · intro c hc a ha
    exact hc a (hAB ha)

theorem boundary_product_original_charts :
    Specs.SmoothManifolds.Corners.Products.boundary_product_original_chartsType := by
  intro n m a b M N _ _ S T
  let E := ordinaryCoordinates n a
  let F := ordinaryCoordinates m b
  let C := productCoordinates n m
  obtain ⟨R, hR, hRsub⟩ := ordinary_corner_bridge S E
  obtain ⟨Q, hQ, hQsub⟩ := ordinary_corner_bridge T F
  obtain ⟨P, hP, hPsub⟩ := product_corner_structure R Q C
  have hA := product_atlas C _ _ (ordinary_atlas E S.smoothStructure.property.1)
    (ordinary_atlas F T.smoothStructure.property.1)
  have hB := product_atlas C R.atlas Q.atlas R.maximal.1 Q.maximal.1
  have hAB : productAtlas C (ordinaryCornerAtlas E S.smoothStructure.val)
      (ordinaryCornerAtlas F T.smoothStructure.val) ⊆ productAtlas C R.atlas Q.atlas := by
    rintro e ⟨c, hc, d, hd, rfl⟩
    exact ⟨c, hRsub hc, d, hQsub hd, rfl⟩
  refine ⟨E, F, C, P, hP.trans (cornerMaximalExtension_of_subset hA hB hAB).symm, ?_⟩
  intro c hc d hd
  refine ⟨hPsub (hAB ⟨ordinaryCornerChart E c, ⟨c,hc,rfl⟩,
    ordinaryCornerChart F d, ⟨d,hd,rfl⟩, rfl⟩), ?_, fun _ => rfl⟩
  simp only [productChart_source, ordinaryCornerChart_source]

theorem product_canonical : Specs.SmoothManifolds.Corners.Products.product_canonicalType := by
  intro n m M N _ _ S T C D P Q hP hQ
  rw [hP, hQ]
  have hA := product_atlas C S.atlas T.atlas S.maximal.1 T.maximal.1
  have hB := product_atlas D S.atlas T.atlas S.maximal.1 T.maximal.1
  have hCross : ∀ a ∈ productAtlas C S.atlas T.atlas,
      ∀ b ∈ productAtlas D S.atlas T.atlas, CornerCompatible a b := by
    rintro _ ⟨c,hc,d,hd,rfl⟩ _ ⟨c',hc',d',hd',rfl⟩
    exact product_compatible_between C D (S.maximal.1.2 c hc c' hc') (T.maximal.1.2 d hd d' hd')
  apply Set.Subset.antisymm
  · intro c hc b hb
    exact Corners.cornerCompatible_of_cover hA.1 hc
      (fun a ha => Corners.cornerCompatible_symm (hCross a ha b hb))
  · intro c hc a ha
    exact Corners.cornerCompatible_of_cover hB.1 hc (fun b hb => hCross a ha b hb)

/-- The corner structure induced by an ordinary smooth structure is independent
of the ambient linear identification of its model with an orthant. -/
theorem ordinary_canonical {n : ℕ} {a : ModelKind} {M : Type*} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (E F : ModelOrthantCoordinates n a)
    (R Q : CornerManifold n M)
    (hR : R.atlas = cornerMaximalExtension (ordinaryCornerAtlas E S.smoothStructure.val))
    (hQ : Q.atlas = cornerMaximalExtension (ordinaryCornerAtlas F S.smoothStructure.val)) :
    R.atlas = Q.atlas := by
  rw [hR, hQ]
  have hA := ordinary_atlas E S.smoothStructure.property.1
  have hB := ordinary_atlas F S.smoothStructure.property.1
  have hCross : ∀ c ∈ ordinaryCornerAtlas E S.smoothStructure.val,
      ∀ d ∈ ordinaryCornerAtlas F S.smoothStructure.val, CornerCompatible c d := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    exact ordinary_compatible_between E F (S.smoothStructure.property.1.2 c hc d hd)
  apply Set.Subset.antisymm
  · intro c hc d hd
    exact Corners.cornerCompatible_of_cover hA.1 hc
      (fun e he => Corners.cornerCompatible_symm (hCross e he d hd))
  · intro c hc d hd
    exact Corners.cornerCompatible_of_cover hB.1 hc (fun e he => hCross d hd e he)


end SmoothManifolds.CornerProducts
