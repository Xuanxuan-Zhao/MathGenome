import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Products

namespace SmoothManifolds
open Set Filter ProductData
open scoped Topology ContDiff
universe u v

/-- Restricting an atlas to an open subspace preserves its smooth transitions. -/
theorem openSubsetAtlas_isContDiffAtlas {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (r : ℕ∞) (A : Set (ModelChart n a M))
    (hA : IsContDiffAtlas r A) (s : Set M) (hs : IsOpen s) :
    IsContDiffAtlas r (openSubsetAtlas A s hs) := by
  constructor
  · intro p
    obtain ⟨c, hc, hp⟩ := hA.1 p.val
    exact ⟨c.subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩, ⟨⟨p⟩, c, hc, rfl⟩, by simpa using hp⟩
  · rintro _ ⟨hne, c, hc, rfl⟩ _ ⟨hne', d, hd, rfl⟩
    apply contDiffCompatible_of_germs
    · intro p hp hp'
      exact LocalCoordinateExtension.precomp (h := (Subtype.val : s → M))
        (chartContDiffAt_of_compatible (hA.2 c hc d hd) (by simpa using hp) (by simpa using hp'))
        continuousAt_subtype_val rfl
    · intro p hp hp'
      exact LocalCoordinateExtension.precomp (h := (Subtype.val : s → M))
        (chartContDiffAt_of_compatible (hA.2 d hd c hc) (by simpa using hp) (by simpa using hp'))
        continuousAt_subtype_val rfl

/-- The restricted smooth structure exists even when the open subset is empty. -/
theorem exists_openSubset_smoothManifold {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (s : Set M) (hs : IsOpen s) :
    ∃ R : SmoothManifold n a s,
      R.topologicalManifold.atlas = openSubsetAtlas S.smoothStructure.val s hs ∧
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val s hs) ∧
      IsSmoothMap R S Subtype.val := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let : SecondCountableTopology M := S.topologicalManifold.secondCountable
  have hA := openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ S.smoothStructure.property.1 s hs
  let R : SmoothManifold n a s := {
    topologicalManifold := ⟨inferInstance, inferInstance, _, hA.1⟩
    smoothStructure := ⟨_, maximalExtension_isMaximal hA⟩ }
  refine ⟨R, rfl, rfl, ?_⟩
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    R.smoothStructure.property.1 S.smoothStructure.property.1 Subtype.val p).mpr
  refine ⟨continuousAt_subtype_val,
    c.subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩,
    subset_maximalExtension hA ⟨⟨p⟩, c, hc, rfl⟩, c, hc, by simpa using hp, hp, ?_⟩
  exact LocalCoordinateExtension.self _ (fun q : s => (c q.val).val) p

@[simp] theorem productChart_source {n m : ℕ} {a b k : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k) (c : ModelChart n a M) (d : ModelChart m b N) :
    (productChart C c d).source = c.source ×ˢ d.source := by
  simp [ProductData.productChart]

@[simp] theorem productChart_val {n m : ℕ} {a b k : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k) (c : ModelChart n a M) (d : ModelChart m b N)
    (p : M × N) :
    ((productChart C c d) p).val = C.linearEquiv ((c p.1).val, (d p.2).val) := rfl

theorem productChart_source_apply {n m : ℕ} {a b k : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k) (c : ModelChart n a M) (d : ModelChart m b N) :
    (productChart C c d).source = c.source ×ˢ d.source ∧
    ∀ p : M × N, ((productChart C c d) p).val = C.linearEquiv ((c p.1).val, (d p.2).val) :=
  ⟨productChart_source C c d, fun _ => rfl⟩

/-- Concatenating two coordinate blocks is an ambient linear isomorphism. -/
noncomputable def appendCoordinates (n m : ℕ) :
    (Euclidean n × Euclidean m) ≃L[ℝ] Euclidean (n + m) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) ℝ ℝ).symm.trans
    (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin n ⊕ Fin m => ℝ)
      finSumFinEquiv)).toContinuousLinearEquiv

@[simp] theorem appendCoordinates_castAdd (n m : ℕ)
    (z : Euclidean n × Euclidean m) (i : Fin n) :
    appendCoordinates n m z (i.castAdd m) = z.1 i := by
  rcases z with ⟨x, y⟩
  simp [appendCoordinates, LinearEquiv.piCongrLeft', Equiv.piCongrLeft']

@[simp] theorem appendCoordinates_natAdd (n m : ℕ)
    (z : Euclidean n × Euclidean m) (i : Fin m) :
    appendCoordinates n m z (i.natAdd n) = z.2 i := by
  rcases z with ⟨x, y⟩
  simp [appendCoordinates, LinearEquiv.piCongrLeft', Equiv.piCongrLeft']

theorem exists_euclidean_productCoordinates (n m : ℕ) :
    Nonempty (ProductCoordinates n .euclidean m .euclidean .euclidean) := by
  exact ⟨⟨appendCoordinates n m, fun _ => by simp [ModelData.modelSet]⟩⟩

theorem exists_rightHalfSpace_productCoordinates (n m : ℕ) :
    ∃ C : ProductCoordinates n .euclidean (m + 1) .halfSpace .halfSpace,
      ∀ z, C.linearEquiv z (Fin.last (n + m)) = z.2 (Fin.last m) := by
  have he : ∀ z, appendCoordinates n (m + 1) z (Fin.last (n + m)) =
      z.2 (Fin.last m) := by
    intro z
    exact appendCoordinates_natAdd n (m + 1) z (Fin.last m)
  refine ⟨⟨appendCoordinates n (m + 1), ?_⟩, he⟩
  intro z
  change 0 ≤ appendCoordinates n (m + 1) z (Fin.last (n + m)) ↔
    True ∧ 0 ≤ z.2 (Fin.last m)
  rw [he]
  simp

/-- The zero-dimensional half-space imposes no constraint. -/
theorem exists_zeroHalfSpace_productCoordinates :
    (∀ m : ℕ, Nonempty (ProductCoordinates 0 .halfSpace m .euclidean .euclidean)) ∧
    (∀ n : ℕ, Nonempty (ProductCoordinates n .euclidean 0 .halfSpace .euclidean)) := by
  constructor <;> intro n
  · exact ⟨⟨appendCoordinates 0 n, fun _ => by
      simp [ModelData.modelSet, ModelData.halfSpaceSet]⟩⟩
  · exact ⟨⟨appendCoordinates n 0, fun _ => by
      simp [ModelData.modelSet, ModelData.halfSpaceSet]⟩⟩

/-- Reindex coordinate tuples along an equality of dimensions. -/
noncomputable def castCoordinates {n m : ℕ} (h : n = m) :
    Euclidean n ≃L[ℝ] Euclidean m :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin n => ℝ) (finCongr h)).toContinuousLinearEquiv

@[simp] theorem castCoordinates_apply {n m : ℕ} (h : n = m)
    (x : Euclidean n) (i : Fin m) :
    castCoordinates h x i = x (i.cast h.symm) := rfl

theorem castCoordinates_mem_model {n m : ℕ} (h : n = m)
    (k : ModelKind) (x : Euclidean n) :
    castCoordinates h x ∈ modelSet m k ↔ x ∈ modelSet n k := by
  subst m
  rfl

theorem exists_leftHalfSpace_productCoordinates (n m : ℕ) :
    ∃ C : ProductCoordinates (n + 1) .halfSpace m .euclidean .halfSpace,
      ∀ z, C.linearEquiv z ((Fin.last (n + m)).cast (Nat.add_right_comm n m 1)) =
        z.1 (Fin.last n) := by
  obtain ⟨C, hC⟩ := exists_rightHalfSpace_productCoordinates m n
  let e : (Euclidean (n + 1) × Euclidean m) ≃L[ℝ] Euclidean (n + 1 + m) :=
    (LinearEquiv.prodComm ℝ (Euclidean (n + 1)) (Euclidean m)).toContinuousLinearEquiv.trans
      (C.linearEquiv.trans (castCoordinates (Nat.add_comm m (n + 1))))
  refine ⟨⟨e, ?_⟩, ?_⟩
  · intro z
    change castCoordinates (Nat.add_comm m (n + 1)) (C.linearEquiv z.swap) ∈ _ ↔ _
    rw [castCoordinates_mem_model, C.mem_model]
    exact and_comm
  · intro z
    change castCoordinates (Nat.add_comm m (n + 1)) (C.linearEquiv z.swap)
      ((Fin.last (n + m)).cast (Nat.add_right_comm n m 1)) = _
    rw [castCoordinates_apply]
    have hi : (((Fin.last (n + m)).cast (Nat.add_right_comm n m 1)).cast
        (Nat.add_comm m (n + 1)).symm) = Fin.last (m + n) := by
      apply Fin.ext
      exact Nat.add_comm n m
    rw [hi, hC]
    rfl

/-- Product coordinate transitions are products of ambient local extensions,
conjugated by the ambient linear change of coordinates. -/
theorem productChart_transition {n m : ℕ} {a b k : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k) {r : ℕ∞}
    {c c' : ModelChart n a M} {d d' : ModelChart m b N}
    (hc : ContDiffCompatible r c c') (hd : ContDiffCompatible r d d')
    (p : M × N) (hp : p ∈ (productChart C c d).source)
    (hp' : p ∈ (productChart C c' d').source) :
    ChartContDiffAt r (productChart C c d) (productChart C c' d') id p := by
  rw [productChart_source] at hp hp'
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := chartContDiffAt_of_compatible hc hp.1 hp'.1
  obtain ⟨V, hV, hxV, G, hG, heG⟩ := chartContDiffAt_of_compatible hd hp.2 hp'.2
  let W : Set (Euclidean (n + m)) := C.linearEquiv.symm ⁻¹' (U ×ˢ V)
  have hWF : MapsTo (fun z : Euclidean (n + m) => (C.linearEquiv.symm z).1) W U :=
    fun _ hz => hz.1
  have hWG : MapsTo (fun z : Euclidean (n + m) => (C.linearEquiv.symm z).2) W V :=
    fun _ hz => hz.2
  refine ⟨W, (hU.prod hV).preimage C.linearEquiv.symm.continuous, ?_,
    fun z => C.linearEquiv (F (C.linearEquiv.symm z).1, G (C.linearEquiv.symm z).2), ?_, ?_⟩
  · change C.linearEquiv.symm ((productChart C c d) p).val ∈ U ×ˢ V
    rw [productChart_val, C.linearEquiv.symm_apply_apply]
    exact ⟨hxU, hxV⟩
  · exact C.linearEquiv.contDiff.contDiffOn.comp
      ((hF.comp C.linearEquiv.symm.contDiff.fst.contDiffOn hWF).prodMk
        (hG.comp C.linearEquiv.symm.contDiff.snd.contDiffOn hWG))
      (mapsTo_univ _ _)
  · have heF' := heF.comp_tendsto (continuous_fst.continuousAt : ContinuousAt Prod.fst p)
    have heG' := heG.comp_tendsto (continuous_snd.continuousAt : ContinuousAt Prod.snd p)
    filter_upwards [heF', heG'] with q hqF hqG
    simp only [productChart_val, C.linearEquiv.symm_apply_apply, id_eq]
    change F (c q.1).val = (c' q.1).val at hqF
    change G (d q.2).val = (d' q.2).val at hqG
    rw [hqF, hqG]

theorem productAtlas_isContDiffAtlas {n m : ℕ} {a b k : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k) (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (hA : IsContDiffAtlas r A) (hB : IsContDiffAtlas r B) :
    IsContDiffAtlas r (productAtlas C A B) := by
  constructor
  · intro p
    obtain ⟨c, hc, hp⟩ := hA.1 p.1
    obtain ⟨d, hd, hp'⟩ := hB.1 p.2
    exact ⟨productChart C c d, ⟨c, hc, d, hd, rfl⟩, by
      rw [productChart_source]; exact ⟨hp, hp'⟩⟩
  · rintro _ ⟨c, hc, d, hd, rfl⟩ _ ⟨c', hc', d', hd', rfl⟩
    apply contDiffCompatible_of_germs
    · exact productChart_transition C (hA.2 c hc c' hc') (hB.2 d hd d' hd')
    · exact productChart_transition C (hA.2 c' hc' c hc) (hB.2 d' hd' d hd)

theorem exists_product_smoothManifold {n m : ℕ} {a b k : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : ProductCoordinates n a m b k) :
    ∃ P : SmoothManifold (n + m) k (M × N),
      P.topologicalManifold.atlas = productAtlas C S.smoothStructure.val T.smoothStructure.val ∧
      P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (productAtlas C S.smoothStructure.val T.smoothStructure.val) := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let : T2Space N := T.topologicalManifold.hausdorff
  let : SecondCountableTopology M := S.topologicalManifold.secondCountable
  let : SecondCountableTopology N := T.topologicalManifold.secondCountable
  have hA := productAtlas_isContDiffAtlas C (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 T.smoothStructure.property.1
  exact ⟨⟨⟨inferInstance, inferInstance, _, hA.1⟩,
    ⟨_, maximalExtension_isMaximal hA⟩⟩, rfl, rfl⟩

/-- Zero-dimensional half-space constraints can be erased without changing the
linear coordinates or the product topology. -/
theorem exists_productCoordinates {n m : ℕ} {a b : ModelKind}
    (h : a = .euclidean ∨ b = .euclidean ∨ n = 0 ∨ m = 0) :
    Nonempty (ProductCoordinates n a m b (productKind n a m b)) := by
  cases a with
  | euclidean =>
    cases b with
    | euclidean =>
      simpa [productKind] using exists_euclidean_productCoordinates n m
    | halfSpace =>
      cases m with
      | zero => simpa [productKind] using exists_zeroHalfSpace_productCoordinates.2 n
      | succ m =>
        obtain ⟨C, _⟩ := exists_rightHalfSpace_productCoordinates n m
        exact ⟨by simpa [productKind] using C⟩
  | halfSpace =>
    cases b with
    | euclidean =>
      cases n with
      | zero => simpa [productKind] using exists_zeroHalfSpace_productCoordinates.1 m
      | succ n =>
        obtain ⟨C, _⟩ := exists_leftHalfSpace_productCoordinates n m
        exact ⟨by simpa [productKind] using C⟩
    | halfSpace =>
      have hz : n = 0 ∨ m = 0 := by simpa using h
      rcases hz with rfl | rfl
      · cases m with
        | zero =>
          exact ⟨⟨appendCoordinates 0 0, fun _ => by
            simp [productKind, ModelData.modelSet, ModelData.halfSpaceSet]⟩⟩
        | succ m =>
          obtain ⟨C, _⟩ := exists_rightHalfSpace_productCoordinates 0 m
          refine ⟨⟨C.linearEquiv, ?_⟩⟩
          intro z
          simpa [productKind, ModelData.modelSet, ModelData.halfSpaceSet] using C.mem_model z
      · cases n with
        | zero =>
          exact ⟨⟨appendCoordinates 0 0, fun _ => by
            simp [productKind, ModelData.modelSet, ModelData.halfSpaceSet]⟩⟩
        | succ n =>
          obtain ⟨C, _⟩ := exists_leftHalfSpace_productCoordinates n 0
          refine ⟨⟨C.linearEquiv, ?_⟩⟩
          intro z
          simpa [productKind, ModelData.modelSet, ModelData.halfSpaceSet] using C.mem_model z

theorem exists_ordinaryProduct_smoothManifold {n m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : a = .euclidean ∨ b = .euclidean ∨ n = 0 ∨ m = 0) :
    ∃ C : ProductCoordinates n a m b (productKind n a m b),
    ∃ P : SmoothManifold (n + m) (productKind n a m b) (M × N),
      P.topologicalManifold.atlas = productAtlas C S.smoothStructure.val T.smoothStructure.val ∧
      P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (productAtlas C S.smoothStructure.val T.smoothStructure.val) := by
  obtain ⟨C⟩ := exists_productCoordinates h
  exact ⟨C, exists_product_smoothManifold S T C⟩

/-- The interior of either permitted model has its ordinary Euclidean chart.
The inverse has an irrelevant default outside the model. -/
private noncomputable def modelInteriorChart (n : ℕ) (a : ModelKind) :
    OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n .euclidean) := by
  classical
  let zeroModel : ModelSpace n a := ⟨0, by
    cases a <;> cases n <;> simp [ModelData.modelSet, ModelData.halfSpaceSet]⟩
  exact {
    toFun x := ⟨x.val, mem_univ _⟩
    invFun y := if hy : y.val ∈ modelSet n a then ⟨y.val, hy⟩ else zeroModel
    source := {x | x.val ∈ interior (modelSet n a)}
    target := {y | y.val ∈ interior (modelSet n a)}
    map_source' _ hx := hx
    map_target' y hy := by
      have hm := interior_subset hy
      simp only [dite_eq_left hm]
      exact hy
    left_inv' x _ := by simp only [dite_eq_left x.property]
    right_inv' y hy := by
      have hm := interior_subset hy
      simp only [dite_eq_left hm]
    open_source := isOpen_interior.preimage continuous_subtype_val
    open_target := isOpen_interior.preimage continuous_subtype_val
    continuousOn_toFun := (continuous_subtype_val.subtype_mk _).continuousOn
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply continuous_subtype_val.continuousOn.congr
      intro y hy
      dsimp only [Function.comp_apply]
      rw [dite_eq_left (interior_subset hy)] }

private noncomputable def euclideanInteriorChart {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (c : ModelChart n a M) :
    ModelChart n .euclidean M := c.trans (modelInteriorChart n a)

@[simp] private theorem euclideanInteriorChart_val {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (c : ModelChart n a M) (p : M) :
    ((euclideanInteriorChart c) p).val = (c p).val := rfl

private theorem euclideanInteriorChart_source {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (c : ModelChart n a M) :
    (euclideanInteriorChart c).source =
      c.source ∩ {p | (c p).val ∈ interior (modelSet n a)} := by
  rw [euclideanInteriorChart, OpenPartialHomeomorph.trans_source]
  rfl

private theorem chart_interior_of_boundary_empty {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M)
    (hS : intrinsicBoundary S = ∅) {c : ModelChart n a M}
    (hc : c ∈ S.smoothStructure.val) {p : M} (hp : p ∈ c.source) :
    (c p).val ∈ interior (modelSet n a) := by
  by_contra h
  have hb := (intrinsicBoundary_iff_chart S c hc p hp).mpr
    ((mem_modelFace_iff_not_mem_interior (c p)).mpr h)
  rw [hS] at hb
  exact hb

private def euclideanInteriorAtlas {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M) :
    Set (ModelChart n .euclidean M) :=
  {e | ∃ c ∈ S.smoothStructure.val, e = euclideanInteriorChart c}

private theorem euclideanInteriorAtlas_isContDiffAtlas {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M)
    (hS : intrinsicBoundary S = ∅) :
    IsContDiffAtlas (⊤ : ℕ∞) (euclideanInteriorAtlas S) := by
  constructor
  · intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    exact ⟨euclideanInteriorChart c, ⟨c, hc, rfl⟩, by
      rw [euclideanInteriorChart_source]
      exact ⟨hp, chart_interior_of_boundary_empty S hS hc hp⟩⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    apply contDiffCompatible_of_germs
    · intro p hp hp'
      rw [euclideanInteriorChart_source] at hp hp'
      exact chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 c hc d hd) hp.1 hp'.1
    · intro p hp hp'
      rw [euclideanInteriorChart_source] at hp hp'
      exact chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 d hd c hc) hp.1 hp'.1

/-- Empty intrinsic boundary permits Euclidean charts in the same smooth
structure, even if the original model kind was a half-space. -/
theorem exists_boundaryless_euclidean_smoothManifold {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M)
    (hS : intrinsicBoundary S = ∅) :
    ∃ E : SmoothManifold n .euclidean M, IsSmoothMap S E id ∧ IsSmoothMap E S id := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let : SecondCountableTopology M := S.topologicalManifold.secondCountable
  have hA := euclideanInteriorAtlas_isContDiffAtlas S hS
  let E : SmoothManifold n .euclidean M := {
    topologicalManifold := ⟨inferInstance, inferInstance, _, hA.1⟩
    smoothStructure := ⟨_, maximalExtension_isMaximal hA⟩ }
  refine ⟨E, ?_, ?_⟩
  · intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    have hpE : p ∈ (euclideanInteriorChart c).source := by
      rw [euclideanInteriorChart_source]
      exact ⟨hp, chart_interior_of_boundary_empty S hS hc hp⟩
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      S.smoothStructure.property.1 E.smoothStructure.property.1 id p).mpr
    exact ⟨continuousAt_id, c, hc, euclideanInteriorChart c,
      subset_maximalExtension hA ⟨c, hc, rfl⟩, hp, hpE,
      LocalCoordinateExtension.self _ (fun q => (c q).val) p⟩
  · intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    have hpE : p ∈ (euclideanInteriorChart c).source := by
      rw [euclideanInteriorChart_source]
      exact ⟨hp, chart_interior_of_boundary_empty S hS hc hp⟩
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      E.smoothStructure.property.1 S.smoothStructure.property.1 id p).mpr
    exact ⟨continuousAt_id, euclideanInteriorChart c,
      subset_maximalExtension hA ⟨c, hc, rfl⟩, c, hc, hpE, hp,
      LocalCoordinateExtension.self _ (fun q => (c q).val) p⟩

theorem exists_product_leftBoundaryless {n m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (hS : intrinsicBoundary S = ∅) :
    ∃ E : SmoothManifold n .euclidean M,
      IsSmoothMap S E id ∧ IsSmoothMap E S id ∧
      ∃ C : ProductCoordinates n .euclidean m b (productKind n .euclidean m b),
      ∃ P : SmoothManifold (n + m) (productKind n .euclidean m b) (M × N),
        P.topologicalManifold.atlas = productAtlas C E.smoothStructure.val T.smoothStructure.val ∧
        P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (productAtlas C E.smoothStructure.val T.smoothStructure.val) := by
  obtain ⟨E, hSE, hES⟩ := exists_boundaryless_euclidean_smoothManifold S hS
  obtain ⟨C, P, hP⟩ := exists_ordinaryProduct_smoothManifold E T (Or.inl rfl)
  exact ⟨E, hSE, hES, C, P, hP⟩

theorem exists_product_rightBoundaryless {n m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (hT : intrinsicBoundary T = ∅) :
    ∃ E : SmoothManifold m .euclidean N,
      IsSmoothMap T E id ∧ IsSmoothMap E T id ∧
      ∃ C : ProductCoordinates n a m .euclidean (productKind n a m .euclidean),
      ∃ P : SmoothManifold (n + m) (productKind n a m .euclidean) (M × N),
        P.topologicalManifold.atlas = productAtlas C S.smoothStructure.val E.smoothStructure.val ∧
        P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (productAtlas C S.smoothStructure.val E.smoothStructure.val) := by
  obtain ⟨E, hTE, hET⟩ := exists_boundaryless_euclidean_smoothManifold T hT
  obtain ⟨C, P, hP⟩ := exists_ordinaryProduct_smoothManifold S E (Or.inr (Or.inl rfl))
  exact ⟨E, hTE, hET, C, P, hP⟩

theorem exists_product_boundaryless {n m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (hS : intrinsicBoundary S = ∅) (hT : intrinsicBoundary T = ∅) :
    ∃ E : SmoothManifold n .euclidean M, ∃ F : SmoothManifold m .euclidean N,
      IsSmoothMap S E id ∧ IsSmoothMap E S id ∧
      IsSmoothMap T F id ∧ IsSmoothMap F T id ∧
      ∃ C : ProductCoordinates n .euclidean m .euclidean .euclidean,
      ∃ P : SmoothManifold (n + m) .euclidean (M × N),
        P.topologicalManifold.atlas = productAtlas C E.smoothStructure.val F.smoothStructure.val ∧
        P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (productAtlas C E.smoothStructure.val F.smoothStructure.val) ∧
        intrinsicBoundary P = ∅ := by
  obtain ⟨E, hSE, hES⟩ := exists_boundaryless_euclidean_smoothManifold S hS
  obtain ⟨F, hTF, hFT⟩ := exists_boundaryless_euclidean_smoothManifold T hT
  obtain ⟨C⟩ := exists_euclidean_productCoordinates n m
  obtain ⟨P, hP, hP'⟩ := exists_product_smoothManifold E F C
  exact ⟨E, F, hSE, hES, hTF, hFT, C, P, hP, hP', intrinsicBoundary_euclidean P⟩

end SmoothManifolds
