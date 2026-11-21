import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Frames
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.ConstantRankBundles

namespace SmoothManifolds.ConstantRankBundles
open ModelData AtlasData MapData ProductData BundleData FrameData ConstantRankData
  Bundle Set Filter Module
open scoped Topology
universe u v w z t q

/-- Every subspace has adapted ambient linear coordinates. -/
theorem exists_adapted_coordinates {r d : ℕ} (K : Submodule ℝ (Euclidean r))
    (hd : finrank ℝ K = d) :
    ∃ e : Euclidean r ≃L[ℝ] Euclidean r,
      ∀ v, v ∈ K ↔ ∀ j : Fin r, d ≤ j.val → e.symm v j = 0 := by
  classical
  have hle : d ≤ r := by simpa [hd] using K.finrank_le
  let I : Set (Fin r) := {j | j.val < d}
  let C := Pi.spanSubset ℝ I
  have hcard : I.ncard = d := by
    let e : Fin d ≃ I :=
      { toFun := fun j => ⟨j.castLE hle, j.isLt⟩
        invFun := fun j => ⟨j.val.val, j.property⟩
        left_inv := fun j => rfl
        right_inv := fun j => rfl }
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr e, Nat.card_fin]
  have hdim : finrank ℝ C = finrank ℝ K := by
    rw [hd, Pi.dim_spanSubset, hcard]
  let f : C ≃ₗ[ℝ] K := LinearEquiv.ofFinrankEq C K hdim
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g.toContinuousLinearEquiv, fun v => ?_⟩
  have he : v ∈ K ↔ g.symm v ∈ C := by
    constructor
    · intro hv
      have hh := hg (f.symm ⟨v, hv⟩)
      have hv' : v = g (f.symm ⟨v, hv⟩) := by simpa using hh
      rw [hv', g.symm_apply_apply]
      exact (f.symm ⟨v, hv⟩).property
    · intro hv
      have hh := hg ⟨g.symm v, hv⟩
      rw [g.apply_symm_apply] at hh
      exact hh ▸ (f ⟨g.symm v, hv⟩).property
  rw [he, Pi.mem_spanSubset_iff]
  simp only [I, mem_ofPred_eq, not_lt]
  rfl

/-- A linear generalized inverse exists without any rank restriction. -/
theorem exists_generalized_inverse {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] W) :
    ∃ G : W →ₗ[ℝ] V, ∀ v, T (G (T v)) = T v := by
  obtain ⟨s, hs⟩ := T.rangeRestrict.exists_rightInverse_of_surjective
    T.range_rangeRestrict
  obtain ⟨p, hp⟩ := T.range.subtype.exists_leftInverse_of_injective T.range.ker_subtype
  refine ⟨s.comp p, fun v => ?_⟩
  have hpv : p (T v) = T.rangeRestrict v :=
    LinearMap.congr_fun hp (T.rangeRestrict v)
  have hsv := LinearMap.congr_fun hs (T.rangeRestrict v)
  change T (s (p (T v))) = T v
  rw [hpv]
  exact congrArg Subtype.val hsv

/-- The domain perturbation transports kernels when their dimensions agree. -/
theorem kernel_perturbation {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ V]
    (T₀ T : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] V)
    (hG : ∀ v, T₀ (G (T₀ v)) = T₀ v)
    (H : V ≃ₗ[ℝ] V)
    (hH : ∀ v, H v = v - G (T₀ v) + G (T v))
    (hd : finrank ℝ (LinearMap.ker T) = finrank ℝ (LinearMap.ker T₀)) :
    ∀ v, v ∈ LinearMap.ker T ↔ H v ∈ LinearMap.ker T₀ := by
  have hmap : (LinearMap.ker T).map H.toLinearMap = LinearMap.ker T₀ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro v ⟨w, hw, rfl⟩
      change T₀ (H w) = 0
      rw [hH, LinearMap.mem_ker.mp hw, map_zero, add_zero, map_sub, hG, sub_self]
    · rw [H.finrank_map_eq, hd]
  intro v
  rw [← hmap]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, he⟩
    exact H.injective he ▸ hw

/-- The companion perturbation transports the image in the forward direction. -/
theorem image_perturbation {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    (T₀ T : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] V)
    (hG : ∀ v, T₀ (G (T₀ v)) = T₀ v)
    (J : W ≃ₗ[ℝ] W)
    (hJ : ∀ w, J w = w - T₀ (G w) + T (G w))
    (hd : finrank ℝ (LinearMap.range T₀) = finrank ℝ (LinearMap.range T)) :
    ∀ w, w ∈ LinearMap.range T ↔ J.symm w ∈ LinearMap.range T₀ := by
  have hmap : (LinearMap.range T₀).map J.toLinearMap = LinearMap.range T := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro w ⟨_, ⟨v, rfl⟩, rfl⟩
      change J (T₀ v) ∈ LinearMap.range T
      rw [hJ, hG, sub_self, zero_add]
      exact ⟨G (T₀ v), rfl⟩
    · rw [J.finrank_map_eq, hd]
  intro w
  rw [← hmap]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro hw
    exact ⟨J.symm w, hw, J.apply_symm_apply w⟩

theorem vectorSmoothAt_subtype {n : ℕ} {a : ModelKind} {X V : Type*}
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Set (ModelChart n a X)} {f : X → V} {U : Set X} (hU : IsOpen U)
    (p : U) (hf : VectorSmoothAt A f p.val) :
    VectorSmoothAt (openSubsetAtlas A U hU) (fun q : U => f q.val) p := by
  refine ⟨hf.1.comp continuousAt_subtype_val, ?_⟩
  rintro _ ⟨hne, c, hc, rfl⟩ hp
  obtain ⟨W, hW, hpW, F, hF, he⟩ := hf.2 c hc (by simpa using hp)
  exact ⟨W, hW, hpW, F, hF, he.comp_tendsto continuousAt_subtype_val⟩

/-- Smooth local adapted coordinates for a constant-rank family of linear maps.
Choose G with T₀ G T₀ = T₀. The operators H = id - G T₀ + G T and
J = id - T₀ G + T G equal the identity at the base point and are therefore
invertible nearby. H maps ker T into ker T₀, and J maps range T₀ into range T;
the constant dimensions make these inclusions equalities. Transport fixed
adapted coordinates by H⁻¹ and J. Only ranks on O are constrained, including
when O lies in a boundary model. -/
theorem matrix_local_frames {n r s : ℕ} {a : ModelKind} {X : Type*}
    [TopologicalSpace X] (A : Set (ModelChart n a X))
    (T : X → Euclidean r →L[ℝ] Euclidean s) (O : Set X)
    (hO : IsOpen O) (hT : ∀ x ∈ O, VectorSmoothAt A T x)
    (k : ℕ) (hrank : ∀ x ∈ O, finrank ℝ (LinearMap.range (T x).toLinearMap) = k)
    (p : X) (hp : p ∈ O) :
    ∃ U : Set X, ∃ hU : IsOpen U, p ∈ U ∧ U ⊆ O ∧
      ∃ L : U → Euclidean r ≃L[ℝ] Euclidean r,
      ∃ R : U → Euclidean s ≃L[ℝ] Euclidean s,
        VectorSmooth (openSubsetAtlas A U hU) (fun q => (L q).toContinuousLinearMap) ∧
        VectorSmooth (openSubsetAtlas A U hU) (fun q => (R q).toContinuousLinearMap) ∧
        (∀ q : U, ∀ v, T q.val v = 0 ↔
          ∀ j : Fin r, r-k ≤ j.val → (L q).symm v j = 0) ∧
        (∀ q : U, ∀ w, w ∈ LinearMap.range (T q.val).toLinearMap ↔
          ∀ j : Fin s, k ≤ j.val → (R q).symm w j = 0) := by
  classical
  let T₀ := T p
  obtain ⟨G₀, hG₀⟩ := exists_generalized_inverse T₀.toLinearMap
  let G := G₀.toContinuousLinearMap
  let H : X → Euclidean r →L[ℝ] Euclidean r := fun x =>
    ContinuousLinearMap.id ℝ _ - G.comp T₀ + G.comp (T x)
  let J : X → Euclidean s →L[ℝ] Euclidean s := fun x =>
    ContinuousLinearMap.id ℝ _ - T₀.comp G + (T x).comp G
  have hH : ∀ x ∈ O, VectorSmoothAt A H x := by
    intro x hx
    exact (hT x hx).postcomp ((contDiff_const.sub contDiff_const).add
      (contDiff_const.clm_comp contDiff_id))
  have hJ : ∀ x ∈ O, VectorSmoothAt A J x := by
    intro x hx
    exact (hT x hx).postcomp ((contDiff_const.sub contDiff_const).add
      (contDiff_id.clm_comp contDiff_const))
  have hHp : H p = ContinuousLinearMap.id ℝ _ := sub_add_cancel _ _
  have hJp : J p = ContinuousLinearMap.id ℝ _ := sub_add_cancel _ _
  have hHi : (H p).IsInvertible := hHp ▸ ContinuousLinearMap.isInvertible_equiv
    (f := ContinuousLinearEquiv.refl ℝ _)
  have hJi : (J p).IsInvertible := hJp ▸ ContinuousLinearMap.isInvertible_equiv
    (f := ContinuousLinearEquiv.refl ℝ _)
  have hev : ∀ᶠ x in 𝓝 p, x ∈ O ∧ (H x).IsInvertible ∧ (J x).IsInvertible :=
    Filter.Eventually.and (hO.mem_nhds hp)
      (Filter.Eventually.and
        (Filter.Tendsto.eventually (hH p hp).1 hHi.eventually_nhds)
        (Filter.Tendsto.eventually (hJ p hp).1 hJi.eventually_nhds))
  obtain ⟨U, hUv, hU, hpU⟩ := mem_nhds_iff.mp hev
  have hUi : U ⊆ O := fun x hx => (hUv hx).1
  let HE : U → Euclidean r ≃L[ℝ] Euclidean r := fun q => (hUv q.property).2.1.choose
  let JE : U → Euclidean s ≃L[ℝ] Euclidean s := fun q => (hUv q.property).2.2.choose
  have hHE : ∀ q : U, (HE q).toContinuousLinearMap = H q.val := fun q =>
    (hUv q.property).2.1.choose_spec
  have hJE : ∀ q : U, (JE q).toContinuousLinearMap = J q.val := fun q =>
    (hUv q.property).2.2.choose_spec
  have hdim : ∀ x ∈ O, finrank ℝ (LinearMap.ker (T x).toLinearMap) = r-k := by
    intro x hx
    have hh := (T x).toLinearMap.finrank_range_add_finrank_ker
    rw [hrank x hx, Module.finrank_pi, Fintype.card_fin] at hh
    omega
  obtain ⟨eK, heK⟩ := exists_adapted_coordinates (LinearMap.ker T₀.toLinearMap) (hdim p hp)
  obtain ⟨eI, heI⟩ := exists_adapted_coordinates (LinearMap.range T₀.toLinearMap) (hrank p hp)
  refine ⟨U, hU, hpU, hUi, (fun q => eK.trans (HE q).symm),
    (fun q => eI.trans (JE q)), ?_, ?_, ?_, ?_⟩
  · intro q
    have hf := ((hH q.val (hUi q.property)).inverse (hUv q.property).2.1)
    have hs := vectorSmoothAt_subtype hU q hf
    have hs' := hs.postcomp (contDiff_id.clm_comp (contDiff_const (c := eK.toContinuousLinearMap)))
    apply hs'.congr
    apply Filter.Eventually.of_forall
    intro y
    change (H y.val).inverse.comp eK.toContinuousLinearMap =
      (HE y).symm.toContinuousLinearMap.comp eK.toContinuousLinearMap
    rw [← hHE, ContinuousLinearMap.inverse_equiv]
  · intro q
    have hs := vectorSmoothAt_subtype hU q (hJ q.val (hUi q.property))
    have hs' := hs.postcomp (contDiff_id.clm_comp (contDiff_const (c := eI.toContinuousLinearMap)))
    apply hs'.congr
    exact Filter.Eventually.of_forall fun y => by
      change (J y.val).comp eI.toContinuousLinearMap =
        (JE y).toContinuousLinearMap.comp eI.toContinuousLinearMap
      rw [hJE]
  · intro q v
    have hh := kernel_perturbation T₀.toLinearMap (T q.val).toLinearMap G₀ hG₀
      (HE q).toLinearEquiv (fun v => by
        change (HE q).toContinuousLinearMap v = _
        rw [hHE]; rfl) ((hdim q.val (hUi q.property)).trans (hdim p hp).symm) v
    exact hh.trans (heK _)
  · intro q w
    have hh := image_perturbation T₀.toLinearMap (T q.val).toLinearMap G₀ hG₀
      (JE q).toLinearEquiv (fun w => by
        change (JE q).toContinuousLinearMap w = _
        rw [hJE]; rfl) ((hrank p hp).trans (hrank q.val (hUi q.property)).symm) w
    exact hh.trans (heI _)

section Bundle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : BundleData.SmoothVectorBundle S r ι E)

include B

/-- Finite-dimensionality is derived from a bundle chart, not assumed on fibers. -/
theorem finite_fiber (p : M) : Module.Finite ℝ (E p) := by
  obtain ⟨i, hi⟩ := B.covers p
  exact (B.fiberCoordinates i p hi).symm.finiteDimensional

theorem finrank_fiber (p : M) : finrank ℝ (E p) = r := by
  obtain ⟨i, hi⟩ := B.covers p
  simpa using (B.fiberCoordinates i p hi).finrank_eq

/-- The canonical frame in a specified original local trivialization. -/
noncomputable def trivializationFrame (i : ι) :
    LocalFrame B (B.baseSet i)
      (B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet) := by
  let U := B.baseSet i
  have hU : IsOpen U := by
    change IsOpen (B.baseSet i)
    rw [← B.trivialization_baseSet i]
    exact (B.trivialization i).open_baseSet
  let b : (p : U) → Basis (Fin r) ℝ (E p.val) := fun p =>
    (Pi.basisFun ℝ (Fin r)).map (B.fiberCoordinates i p.val p.property).symm
  refine {
    section_ := fun j p => b p j
    basis := b
    basis_eq := fun _ _ => rfl
    smooth := ?_ }
  intro j p
  apply Frames.smoothAt_of_sectionCoordinates B U hU i (fun p => b p j) p p.property
  have heq : Frames.sectionCoordinates B U i (fun p => b p j) =
      (fun _ : U => Pi.single j (1 : ℝ)) := by
    funext q
    change B.fiberCoordinates i q.val q.property
      ((B.fiberCoordinates i q.val q.property).symm ((Pi.basisFun ℝ (Fin r)) j)) = _
    rw [LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  rw [heq]
  exact FrameData.VectorSmoothAt.const _ _ _

theorem exists_localFrame (p : M) :
    ∃ U : Set M, ∃ hU : IsOpen U, p ∈ U ∧ Nonempty (LocalFrame B U hU) := by
  obtain ⟨i, hi⟩ := B.covers p
  exact ⟨B.baseSet i, _, hi, ⟨trivializationFrame B i⟩⟩

/-- A smoothly varying invertible coordinate matrix gives an actual smooth
ambient frame. Smoothness of both frame maps then follows from Frames. -/
theorem localFrame_of_coordinates (i : ι) (U : Set M) (hU : IsOpen U)
    (hUi : U ⊆ B.baseSet i) (L : U → Euclidean r ≃L[ℝ] Euclidean r)
    (hL : VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (fun p => (L p).toContinuousLinearMap)) :
    ∃ b : LocalFrame B U hU, ∀ p : U,
      b.basis p = (Pi.basisFun ℝ (Fin r)).map
        ((L p).toLinearEquiv.trans (B.fiberCoordinates i p.val (hUi p.property)).symm) := by
  let b : (p : U) → Basis (Fin r) ℝ (E p.val) := fun p =>
    (Pi.basisFun ℝ (Fin r)).map
      ((L p).toLinearEquiv.trans (B.fiberCoordinates i p.val (hUi p.property)).symm)
  refine ⟨{ section_ := fun j p => b p j
            basis := b
            basis_eq := fun _ _ => rfl
            smooth := ?_ }, fun _ => rfl⟩
  intro j p
  apply Frames.smoothAt_of_sectionCoordinates B U hU i (fun q => b q j) p (hUi p.property)
  have hc := (hL p).clm_apply
    (FrameData.VectorSmoothAt.const (openSubsetAtlas S.smoothStructure.val U hU)
      ((Pi.basisFun ℝ (Fin r)) j) p)
  apply hc.congr
  apply Filter.Eventually.of_forall
  intro q
  change L q ((Pi.basisFun ℝ (Fin r)) j) = B.fiberCoordinates i q.val (hUi q.property)
    ((B.fiberCoordinates i q.val (hUi q.property)).symm
      (L q ((Pi.basisFun ℝ (Fin r)) j)))
  rw [LinearEquiv.apply_symm_apply]

theorem bot_isSmoothSubbundle :
    IsSmoothSubbundle B 0 (fun p => (⊥ : Submodule ℝ (E p))) := by
  intro p
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := exists_localFrame B p
  refine ⟨Nat.zero_le _, U, hU, hp, b, ?_⟩
  intro q v
  simp only [Submodule.mem_bot]
  constructor
  · intro hv j _
    simp [hv]
  · intro hv
    apply (b.basis q).equivFun.injective
    ext j
    simpa using hv j (Nat.zero_le _)

theorem top_isSmoothSubbundle :
    IsSmoothSubbundle B r (fun p => (⊤ : Submodule ℝ (E p))) := by
  intro p
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := exists_localFrame B p
  refine ⟨le_rfl, U, hU, hp, b, ?_⟩
  intro q v
  simp only [Submodule.mem_top, true_iff]
  intro j hj
  exact False.elim (Nat.not_le_of_lt j.isLt hj)

end Bundle

section Morphism
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  [TopologicalSpace (TotalSpace (Euclidean s) F)]
  (B : BundleData.SmoothVectorBundle S r ι E)
  (D : BundleData.SmoothVectorBundle S s κ F)
  (A : SmoothBundleMorphism B D)

/-- Fiber dimensions and rank-nullity imply the required numerical conclusions
without using smoothness or a local normal form. -/
theorem fiber_rank_bounds (p : M) :
    finrank ℝ (LinearMap.range (A.linearMap p)) ≤ r ∧
    finrank ℝ (LinearMap.range (A.linearMap p)) ≤ s := by
  letI := finite_fiber B p
  letI := finite_fiber D p
  constructor
  · simpa [finrank_fiber B p] using (A.linearMap p).finrank_range_le
  · simpa [finrank_fiber D p] using (LinearMap.range (A.linearMap p)).finrank_le

theorem finrank_kernel (p : M) :
    finrank ℝ (LinearMap.ker (A.linearMap p)) =
      r - finrank ℝ (LinearMap.range (A.linearMap p)) := by
  letI := finite_fiber B p
  have h := (A.linearMap p).finrank_range_add_finrank_ker
  rw [finrank_fiber B p] at h
  omega

/-- The zero-rank case includes the actual subbundle conclusions. -/
theorem rank_zero (h : ∀ p, finrank ℝ (LinearMap.range (A.linearMap p)) = 0) :
    IsSmoothSubbundle B r (fun p => LinearMap.ker (A.linearMap p)) ∧
    IsSmoothSubbundle D 0 (fun p => LinearMap.range (A.linearMap p)) := by
  have hz : ∀ p, A.linearMap p = 0 := by
    intro p
    letI := finite_fiber D p
    have hr : LinearMap.range (A.linearMap p) = ⊥ :=
      Submodule.finrank_eq_zero.mp (h p)
    exact LinearMap.range_eq_bot.mp hr
  simp only [hz, LinearMap.ker_zero, LinearMap.range_zero]
  exact ⟨top_isSmoothSubbundle B, bot_isSmoothSubbundle D⟩

/-- The local matrix as a continuous linear map. Outside its overlap its
values are irrelevant. It uses only the actual morphism and trivializations. -/
noncomputable def morphismMatrix (i : ι) (j : κ) (p : M) :
    Euclidean r →L[ℝ] Euclidean s :=
  ∑ l : Fin r, (ContinuousLinearMap.proj l).smulRight
    (((D.trivialization j) (⟨p, A.linearMap p
      ((B.trivialization i).symm p (Pi.single l 1))⟩ : TotalSpace (Euclidean s) F)).2)

/-- Smoothness of the total morphism implies smoothness of its local matrix.
Ambient extensions at boundary points are inherited from the upstream tests. -/
theorem morphismMatrix_smoothAt (i : ι) (j : κ) (p : M)
    (hi : p ∈ B.baseSet i) (hj : p ∈ D.baseSet j) :
    VectorSmoothAt S.smoothStructure.val (morphismMatrix B D A i j) p := by
  have hU : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  let b := trivializationFrame B i
  let q : B.baseSet i := ⟨p, hi⟩
  apply FrameData.VectorSmoothAt.sum
  intro l
  let f : (x : B.baseSet i) → F x.val := fun x => A.linearMap x.val (b.section_ l x)
  have hf : ManifoldSmoothAt (openSubsetAtlas S.smoothStructure.val (B.baseSet i) hU)
      D.totalManifold.smoothStructure.val
      (fun x : B.baseSet i => (⟨x.val, f x⟩ : TotalSpace (Euclidean s) F)) q :=
    manifoldContDiffAt_comp B.totalManifold.smoothStructure.property.1.1
      (b.smooth l q) (A.smooth _)
  have hc := Frames.sectionCoordinates_smoothAt D _ hU j f q hj hf
  have ht := hc.totalize hU
  have heq : VectorSmoothAt S.smoothStructure.val
      (fun x => ((D.trivialization j)
        (⟨x, A.linearMap x ((B.trivialization i).symm x (Pi.single l 1))⟩ :
          TotalSpace (Euclidean s) F)).2) p := by
    apply ht.congr
    filter_upwards [hU.mem_nhds hi] with x hx
    rw [totalize_of_mem _ _ hx]
    change ((D.trivialization j) (⟨x, A.linearMap x
      ((B.fiberCoordinates i x hx).symm ((Pi.basisFun ℝ (Fin r)) l))⟩ :
        TotalSpace (Euclidean s) F)).2 = _
    rw [Pi.basisFun_apply, BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]
  exact heq.postcomp (contDiff_const.smulRight contDiff_id)

/-- On the overlap this is precisely the conjugated fiber linear map. -/
theorem morphismMatrix_apply (i : ι) (j : κ) (p : M)
    (hi : p ∈ B.baseSet i) (hj : p ∈ D.baseSet j) (v : Euclidean r) :
    morphismMatrix B D A i j p v =
      D.fiberCoordinates j p hj (A.linearMap p ((B.fiberCoordinates i p hi).symm v)) := by
  classical
  have hv : v = ∑ l : Fin r, v l • Pi.single l (1 : ℝ) := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply] using
      ((Pi.basisFun ℝ (Fin r)).sum_equivFun v).symm
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul, morphismMatrix, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    BundleData.SmoothVectorBundle.fiberCoordinates_apply,
    BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]

/-- The coordinate matrix has exactly the original fiber rank. -/
theorem morphismMatrix_finrank_range (i : ι) (j : κ) (p : M)
    (hi : p ∈ B.baseSet i) (hj : p ∈ D.baseSet j) :
    finrank ℝ (LinearMap.range (morphismMatrix B D A i j p).toLinearMap) =
      finrank ℝ (LinearMap.range (A.linearMap p)) := by
  have hr : LinearMap.range (morphismMatrix B D A i j p).toLinearMap =
      (LinearMap.range (A.linearMap p)).map (D.fiberCoordinates j p hj).toLinearMap := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨A.linearMap p ((B.fiberCoordinates i p hi).symm v), ⟨_, rfl⟩, ?_⟩
      exact (morphismMatrix_apply B D A i j p hi hj v).symm
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
      refine ⟨B.fiberCoordinates i p hi v, ?_⟩
      change morphismMatrix B D A i j p (B.fiberCoordinates i p hi v) = _
      rw [morphismMatrix_apply B D A i j p hi hj, LinearEquiv.symm_apply_apply]
      rfl
  rw [hr]
  exact (D.fiberCoordinates j p hj).finrank_map_eq _

/-- Adapted ambient frames obtained from the constant-rank matrix lemma. -/
theorem kernel_image_local_frames (k : ℕ)
    (h : ∀ p, finrank ℝ (LinearMap.range (A.linearMap p)) = k) :
    IsSmoothSubbundle B (r - k) (fun p => LinearMap.ker (A.linearMap p)) ∧
    IsSmoothSubbundle D k (fun p => LinearMap.range (A.linearMap p)) := by
  constructor <;> intro p
  all_goals
    obtain ⟨i, hi⟩ := B.covers p
    obtain ⟨j, hj⟩ := D.covers p
    let O := B.baseSet i ∩ D.baseSet j
    have hO : IsOpen O :=
      (B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet).inter
        (D.trivialization_baseSet j ▸ (D.trivialization j).open_baseSet)
    obtain ⟨U, hU, hpU, hUi, L, R, hL, hR, hker, him⟩ :=
      matrix_local_frames S.smoothStructure.val (morphismMatrix B D A i j) O hO
        (fun q hq => morphismMatrix_smoothAt B D A i j q hq.1 hq.2) k
        (fun q hq => (morphismMatrix_finrank_range B D A i j q hq.1 hq.2).trans (h q))
        p ⟨hi, hj⟩
    obtain ⟨bK, hbK⟩ := localFrame_of_coordinates B i U hU
      (fun q hq => (hUi hq).1) L hL
    obtain ⟨bI, hbI⟩ := localFrame_of_coordinates D j U hU
      (fun q hq => (hUi hq).2) R hR
  · refine ⟨Nat.sub_le _ _, U, hU, hpU, bK, ?_⟩
    intro q v
    rw [hbK q, Basis.map_equivFun]
    change A.linearMap q.val v = 0 ↔
      ∀ l : Fin r, r-k ≤ l.val →
        (L q).symm (B.fiberCoordinates i q.val (hUi q.property).1 v) l = 0
    have hh := hker q (B.fiberCoordinates i q.val (hUi q.property).1 v)
    rw [morphismMatrix_apply B D A i j q.val (hUi q.property).1
      (hUi q.property).2, LinearEquiv.symm_apply_apply] at hh
    simpa only [map_eq_zero_iff _ (D.fiberCoordinates j q.val (hUi q.property).2).injective]
      using hh
  · refine ⟨(h p) ▸ (fiber_rank_bounds B D A p).2, U, hU, hpU, bI, ?_⟩
    intro q w
    rw [hbI q, Basis.map_equivFun]
    change w ∈ LinearMap.range (A.linearMap q.val) ↔
      ∀ l : Fin s, k ≤ l.val →
        (R q).symm (D.fiberCoordinates j q.val (hUi q.property).2 w) l = 0
    rw [← him q]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨B.fiberCoordinates i q.val (hUi q.property).1 v, ?_⟩
      change morphismMatrix B D A i j q.val
        (B.fiberCoordinates i q.val (hUi q.property).1 v) = _
      rw [morphismMatrix_apply B D A i j q.val (hUi q.property).1
        (hUi q.property).2, LinearEquiv.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨(B.fiberCoordinates i q.val (hUi q.property).1).symm v, ?_⟩
      apply (D.fiberCoordinates j q.val (hUi q.property).2).injective
      exact (morphismMatrix_apply B D A i j q.val (hUi q.property).1
        (hUi q.property).2 v).symm.trans hv

end Morphism

/-- M05.03 with the kernel and image ranks. -/
theorem kernel_image_subbundles :
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F)
    (A : SmoothBundleMorphism B D) (k : ℕ),
    (∀ p, finrank ℝ (LinearMap.range (A.linearMap p)) = k) →
    IsSmoothSubbundle B (r - k) (fun p => LinearMap.ker (A.linearMap p)) ∧
    IsSmoothSubbundle D k (fun p => LinearMap.range (A.linearMap p)) ∧
    (∀ p, finrank ℝ (LinearMap.ker (A.linearMap p)) = r - k) := by
  intro n r s a M _ S ι κ E F _ _ _ _ _ _ B D A k h
  obtain ⟨hker, him⟩ := kernel_image_local_frames B D A k h
  refine ⟨hker, him, ?_⟩
  intro p
  rw [finrank_kernel B D A p, h p]

/-- There is no uniform-rank assumption across the family of components. -/
theorem componentwise_kernel_image :
  ∀ {J : Type*} {n : J → ℕ} {r s : J → ℕ} {a : J → ModelKind}
    {M : J → Type u} [∀ j, TopologicalSpace (M j)]
    {S : (j : J) → SmoothManifold (n j) (a j) (M j)}
    {ι : J → Type v} {κ : J → Type t}
    {E : (j : J) → M j → Type w} {F : (j : J) → M j → Type z}
    [∀ j p, AddCommGroup (E j p)] [∀ j p, Module ℝ (E j p)]
    [∀ j p, AddCommGroup (F j p)] [∀ j p, Module ℝ (F j p)]
    [∀ j, TopologicalSpace (TotalSpace (Euclidean (r j)) (E j))]
    [∀ j, TopologicalSpace (TotalSpace (Euclidean (s j)) (F j))]
    (B : (j : J) → SmoothVectorBundle (S j) (r j) (ι j) (E j))
    (D : (j : J) → SmoothVectorBundle (S j) (s j) (κ j) (F j))
    (A : (j : J) → SmoothBundleMorphism (B j) (D j)) (k : J → ℕ),
    (∀ j p, finrank ℝ (LinearMap.range ((A j).linearMap p)) = k j) →
    ∀ j, IsSmoothSubbundle (B j) (r j - k j)
        (fun p => LinearMap.ker ((A j).linearMap p)) ∧
      IsSmoothSubbundle (D j) (k j) (fun p => LinearMap.range ((A j).linearMap p)) ∧
      (∀ p, finrank ℝ (LinearMap.ker ((A j).linearMap p)) = r j - k j) := by
  intro J n r s a M _ S ι κ E F _ _ _ _ _ _ B D A k h j
  exact kernel_image_subbundles (B j) (D j) (A j) (k j) (h j)

/-- The family theorem applied to the actual open connected components.
The restriction manifolds and their compatibility with S are constructed. -/
theorem components_kernel_image :
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
  let C := ↥(Set.range (connectedComponent (α := M)))
  ∃ hOpen : ∀ c : C, IsOpen c.val,
    ∃ T : (c : C) → SmoothManifold n a c.val,
      (∀ c, (T c).smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val c.val (hOpen c))) ∧
      ∀ {r s : C → ℕ} {ι : C → Type v} {κ : C → Type t}
        {E : (c : C) → c.val → Type w} {F : (c : C) → c.val → Type z}
        [∀ c p, AddCommGroup (E c p)] [∀ c p, Module ℝ (E c p)]
        [∀ c p, AddCommGroup (F c p)] [∀ c p, Module ℝ (F c p)]
        [∀ c, TopologicalSpace (TotalSpace (Euclidean (r c)) (E c))]
        [∀ c, TopologicalSpace (TotalSpace (Euclidean (s c)) (F c))]
        (B : (c : C) → SmoothVectorBundle (T c) (r c) (ι c) (E c))
        (D : (c : C) → SmoothVectorBundle (T c) (s c) (κ c) (F c))
        (A : (c : C) → SmoothBundleMorphism (B c) (D c)) (k : C → ℕ),
        (∀ c p, finrank ℝ (LinearMap.range ((A c).linearMap p)) = k c) →
        ∀ c, IsSmoothSubbundle (B c) (r c - k c)
            (fun p => LinearMap.ker ((A c).linearMap p)) ∧
          IsSmoothSubbundle (D c) (k c) (fun p => LinearMap.range ((A c).linearMap p)) ∧
          (∀ p, finrank ℝ (LinearMap.ker ((A c).linearMap p)) = r c - k c) := by
  intro n a M _ S
  let C := ↥(Set.range (connectedComponent (α := M)))
  have hOpen : ∀ c : C, IsOpen c.val := by
    intro c
    obtain ⟨p, hp⟩ := c.property
    rw [← hp]
    exact _root_.SmoothManifolds.TopologicalManifold.isOpen_connectedComponent
      S.topologicalManifold p
  choose T hTat hTmax hTinc using fun c : C =>
    exists_openSubset_smoothManifold S c.val (hOpen c)
  refine ⟨hOpen, T, hTmax, ?_⟩
  intro r s ι κ E F _ _ _ _ _ _ B D A k h c
  exact kernel_image_subbundles (B c) (D c) (A c) (k c) (h c)

abbrev SmoothBundleMorphism := @ConstantRankData.SmoothBundleMorphism
abbrev IsSmoothSubbundle := @ConstantRankData.IsSmoothSubbundle

end SmoothManifolds.ConstantRankBundles
