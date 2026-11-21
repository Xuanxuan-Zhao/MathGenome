import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.DistributionTests
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.ConstantRankBundles
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.InvariantExteriorFormula

/-! Bracket and annihilator tests for distributions, paper.tex 1613--1633.
The constructions use the intrinsic tangent, cotangent and exterior fibers.
Local tests and global ideal preservation are related by smooth cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace SmoothManifolds
abbrev SmoothDistribution := @DistributionData.SmoothDistribution
end SmoothManifolds

namespace SmoothManifolds.DistributionTests
open ModelData AtlasData MapData PartitionData TangentData DifferentialData
  TangentBundleData BundleData BundleOperationsData ConstantRankData FrameData FiniteRegularityData
  CovectorData ExteriorData ExteriorDerivativeData VectorFieldData LieBracketData
  DistributionData Set Filter
open scoped Topology
universe u

abbrev IsInvolutive := @DistributionData.IsInvolutive
abbrev IsIntegralSubmanifold := @DistributionData.IsIntegralSubmanifold
abbrev IsIntegrable := @DistributionData.IsIntegrable
abbrev annihilator := @DistributionData.annihilator

/-- Algebraic annihilators detect the original subspace, also in ranks zero
and n. This uses the algebraic dual rather than a metric orthogonal space. -/
theorem annihilator_separates :
    Specs.SmoothManifolds.Ch08.DistributionTests.annihilator_separatesType.{u} := by
  intro n M _ S C k D p v
  exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (D.fiber p) v).symm

theorem vanishing_linear :
    Specs.SmoothManifolds.Ch08.DistributionTests.vanishing_linearType.{u} := by
  intro n M _ S C k D U j
  refine ⟨?_, ?_, ?_⟩
  · intro p hp v hv
    simp
  · intro α β hα hβ p hp v hv
    change evaluate (TangentSpace S p) j (α p + β p) v = 0
    simp only [map_add, AlternatingMap.add_apply, hα p hp v hv, hβ p hp v hv, add_zero]
  · intro r α hα p hp v hv
    change evaluate (TangentSpace S p) j (r • α p) v = 0
    simp only [map_smul, AlternatingMap.smul_apply, hα p hp v hv, smul_zero]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}

/-- The algebraic dual of any smooth ambient frame is a smooth cotangent
frame. Smoothness follows from inversion of its coordinate matrix. -/
noncomputable def dualTangentFrame {U : Set M} {hU : IsOpen U}
    (b : @LocalFrame n n .euclidean M _ S (TangentIndex S) (TangentSpace S)
      (fun _ => inferInstance) (fun _ => inferInstance) C.realization.space.topology
      C.realization.space.bundle U hU) :
    letI := (cotangentSpace C).topology
    LocalFrame (cotangentSpace C).bundle U hU := by
  letI := C.realization.space.topology
  letI := (cotangentSpace C).topology
  let A := C.realization.space.bundle
  let B := (cotangentSpace C).bundle
  let s (j : Fin n) (p : U) := (b.basis p).dualBasis j
  refine { section_ := s
           basis := fun p => (b.basis p).dualBasis
           basis_eq := fun _ _ => rfl
           smooth := ?_ }
  intro j p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let i : TangentIndex S := ⟨c, hc⟩
  have hi : p.val ∈ A.baseSet i := by
    rw [C.realization.baseSet]
    exact hp
  have hiB : p.val ∈ B.baseSet i := by
    change p.val ∈ C.dual.space.bundle.baseSet i
    rw [C.dual.baseSet]
    exact hi
  apply Frames.smoothAt_of_sectionCoordinates B U hU i (s j) p hiB
  have hs := (Frames.frameMatrix_smoothAt A U hU b i p hi).inverse
    (Frames.frameMatrix_invertible A U hU b i p hi)
  have ht : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U hU)
      (fun q : U => fun t : Fin n =>
        ContinuousLinearMap.inverse (Frames.frameMatrix A U hU b i q) (Pi.single t 1) j) p := by
    refine hs.postcomp (h := fun z : Euclidean n →L[ℝ] Euclidean n =>
      fun t : Fin n => z (Pi.single t 1) j) ?_
    apply contDiff_pi.mpr
    intro t
    exact (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).comp (contDiff_id.clm_apply contDiff_const)
  apply ht.congr
  have hOpen : IsOpen (A.baseSet i) := by
    rw [← A.trivialization_baseSet i]
    exact (A.trivialization i).open_baseSet
  have he : ∀ᶠ q : U in 𝓝 p, q.val ∈ A.baseSet i :=
    continuousAt_subtype_val.preimage_mem_nhds (hOpen.mem_nhds hi)
  filter_upwards [he] with q hq
  funext t
  rw [Frames.frameMatrix_eq A U hU b i q hq, ContinuousLinearMap.inverse_equiv]
  change (b.basis q).equivFun
    ((A.fiberCoordinates i q.val hq).symm (Pi.single t 1)) j =
    ((B.trivialization i) (⟨q.val, s j q⟩ : Bundle.TotalSpace (Euclidean n)
      (CotangentFiber S))).2 t
  rw [SmoothVectorBundle.fiberCoordinates_symm_apply]
  exact ((b.basis q).dualBasis_apply j _).symm.trans
    (C.dual.coordinates i q.val hq (s j q) t).symm

/-- An adapted vector basis tests its annihilator on precisely the first k
basis vectors. This argument also covers the empty family when k=0. -/
theorem annihilator_iff_basis {V : Type*} [AddCommGroup V] [Module ℝ V]
    {r k : ℕ} (b : Module.Basis (Fin r) ℝ V) (K : Submodule ℝ V)
    (hK : ∀ v, v ∈ K ↔ ∀ j : Fin r, k ≤ j.val → b.equivFun v j = 0)
    (lam : Module.Dual ℝ V) :
    lam ∈ K.dualAnnihilator ↔ ∀ j : Fin r, j.val < k → lam (b j) = 0 := by
  classical
  constructor
  · intro h j hj
    apply ((Submodule.mem_dualAnnihilator (W := K) lam).mp h) _
    apply (hK _).mpr
    intro t ht
    rw [b.equivFun_self]
    have hne : j ≠ t := by intro he; subst t; omega
    simp [hne]
  · intro h
    apply (Submodule.mem_dualAnnihilator (W := K) lam).mpr
    intro v hv
    rw [← b.sum_repr v, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul]
    by_cases hj : j.val < k
    · rw [h j hj, smul_zero]
    · have hz := (hK v).mp hv j (Nat.le_of_not_lt hj)
      change b.repr v j • lam (b j) = 0
      rw [← b.equivFun_apply, hz, zero_smul]

/-- Reverse the smooth dual adapted basis so its first n-k vectors span
D's annihilator. No choice of a Riemannian metric is involved. -/
theorem annihilator_subbundle :
    Specs.SmoothManifolds.Ch08.DistributionTests.annihilator_subbundleType.{u} := by
  intro n M _ S C k D
  letI := C.realization.space.topology
  letI := (cotangentSpace C).topology
  intro p
  obtain ⟨hk, U, hU, hp, b, hb⟩ := D.smooth p
  let d := dualTangentFrame b
  let F : LocalFrame (cotangentSpace C).bundle U hU :=
    { section_ := fun j q => d.section_ j.rev q
      basis := fun q => (d.basis q).reindex Fin.revPerm
      basis_eq := by intro q j; simpa using d.basis_eq q j.rev
      smooth := fun j => d.smooth j.rev }
  refine ⟨Nat.sub_le _ _, U, hU, hp, F, ?_⟩
  intro q lam
  change lam ∈ (D.fiber q.val).dualAnnihilator ↔ _
  rw [annihilator_iff_basis (b.basis q) (D.fiber q.val) (hb q)]
  have hrepr (j : Fin n) : (F.basis q).equivFun lam j = lam (b.basis q j.rev) := by
    rw [Module.Basis.equivFun_apply]
    change ((d.basis q).reindex Fin.revPerm).repr lam j = _
    rw [Module.Basis.repr_reindex_apply]
    change (b.basis q).dualBasis.repr lam j.rev = _
    exact (b.basis q).dualBasis_repr lam j.rev
  constructor
  · intro h j hj
    rw [hrepr]
    apply h j.rev
    simp only [Fin.val_rev]
    omega
  · intro h j hj
    have hrev : n-k ≤ j.rev.val := by
      simp only [Fin.val_rev]
      omega
    have hz := h j.rev hrev
    rwa [hrepr, Fin.rev_rev] at hz

/-- Every annihilator covector has a genuine smooth local annihilator
section representative. This is local, with no false claim of extension by
zero without a cutoff. -/
theorem annihilator_local_extension (D : SmoothDistribution C k) (p : M)
    (lam : CotangentFiber S p) (hlam : lam ∈ DistributionData.annihilator D p) :
    letI := (cotangentSpace C).topology
    ∃ (U : Set M) (hU : IsOpen U) (hp : p ∈ U)
      (s : (q : U) → CotangentFiber S q.val),
      s ⟨p, hp⟩ = lam ∧
      (∀ q, s q ∈ DistributionData.annihilator D q.val) ∧
      ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
        (cotangentSpace C).bundle.totalManifold.smoothStructure.val
        (fun q : U => (⟨q.val, s q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))) := by
  letI := (cotangentSpace C).topology
  obtain ⟨hk, U, hU, hp, b, hb⟩ := annihilator_subbundle D p
  let a : Euclidean n := (b.basis ⟨p, hp⟩).equivFun lam
  let s (q : U) := (b.basis q).equivFun.symm a
  refine ⟨U, hU, hp, s, ?_, ?_, ?_⟩
  · exact (b.basis ⟨p, hp⟩).equivFun.symm_apply_apply lam
  · intro q
    apply (hb q _).mpr
    intro j hj
    change (b.basis q).equivFun ((b.basis q).equivFun.symm a) j = 0
    rw [LinearEquiv.apply_symm_apply]
    exact (hb ⟨p, hp⟩ lam).mp hlam j hj
  · apply (Frames.smooth_section_iff_coefficients (cotangentSpace C).bundle U hU b s).mpr
    intro j q
    have heq : (fun z : U => FrameData.coefficients b s z j) = fun _ => a j := by
      funext z
      exact congrFun ((b.basis z).equivFun.apply_symm_apply a) j
    rw [heq]
    exact FrameData.VectorSmoothAt.const _ _ q

/-- Ranks of D and its algebraic annihilator. -/
theorem fiber_ranks :
    Specs.SmoothManifolds.Ch08.DistributionTests.fiber_ranksType.{u} := by
  intro n M _ S C k D p
  letI := C.realization.space.topology
  obtain ⟨hk, U, hU, hp, b, hb⟩ := D.smooth p
  let e := BundleOperations.adaptedCoordinates (b.basis ⟨p, hp⟩) (D.fiber p)
    hk (hb ⟨p, hp⟩)
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    Module.Finite.of_basis (b.basis ⟨p, hp⟩)
  have hdim : Module.finrank ℝ (D.fiber p) = k := by
    simpa using e.finrank_eq
  have hamb : Module.finrank ℝ (TangentSpace S p) = n := by
    simpa using (b.basis ⟨p, hp⟩).equivFun.finrank_eq
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq (K := ℝ) (V := TangentSpace S p) (D.fiber p)
  refine ⟨hk, hdim, ?_⟩
  change Module.finrank ℝ (D.fiber p).dualAnnihilator = n-k
  rw [hdim, hamb] at hann
  exact (Nat.add_sub_cancel_left k _).symm.trans (congrArg (fun r => r-k) hann)

/-- Adapted tangent frames supply genuine smooth local frames of D. -/
theorem distribution_frame_exists (D : SmoothDistribution C k) (p : M) :
    ∃ (U : Set M) (hU : IsOpen U), p ∈ U ∧ Nonempty (DistributionFrame D U hU) := by
  letI := C.realization.space.topology
  letI := C.tangent.topology
  obtain ⟨hk, U, hU, hp, b, hb⟩ := D.smooth p
  let F := BundleOperations.adaptedSubbundleFrame b hk hb
  refine ⟨U, hU, hp, ⟨{ basis := F.basis, smooth := ?_ }⟩⟩
  intro i q
  exact manifoldContDiffAt_comp
    C.realization.space.bundle.totalManifold.smoothStructure.property.1.1
    (F.smooth i q) (C.realization.smooth_to_original _)

theorem global_bracket_isLocal (U : Set M)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent)
    (hb : BracketOperation b) (X Y : SmoothField C.tangent) :
    HasLocalBracket C.tangent U X.val Y.val (b X Y).val := by
  have h := LieBrackets.bracket_coordinates S C.tangent b hb X Y
  exact ⟨fun e he p _ hp => h.1 e he p hp,
    fun e he p _ hp L K hL hK => h.2 e he p hp L K hL hK⟩

theorem smoothField_isLocal (U : Set M) (X : SmoothField C.tangent) :
    IsLocalField C.tangent U X.val := fun p _ => X.smooth p

/-- Involutivity applies to ambient global fields with D-values only near the
point being tested. No global tangency hypothesis is introduced. -/
theorem involutive_global_bracket (D : SmoothDistribution C k) (hD : IsInvolutive D)
    (U : Set M) (hU : IsOpen U)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent)
    (hb : BracketOperation b) (X Y : SmoothField C.tangent)
    (hX : ValuesIn D U X.val) (hY : ValuesIn D U Y.val) :
    ValuesIn D U (b X Y).val :=
  hD U hU X.val Y.val (b X Y).val
    (smoothField_isLocal U X) (smoothField_isLocal U Y)
    (global_bracket_isLocal U b hb X Y) hX hY

/-- The bracket characterization determines every value on its open domain. -/
theorem local_bracket_unique (U : Set M) (X Y Z W : Section S)
    (hZ : HasLocalBracket C.tangent U X Y Z)
    (hW : HasLocalBracket C.tangent U X Y W) : ∀ p ∈ U, Z p = W p := by
  intro p hp
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨L, K, hL, hK⟩ := hZ.1 e he p hp hpe
  apply (C.tangent.fiberCoordinates.equiv e he p hpe).injective
  funext j
  have hz := hZ.2 e he p hp hpe L K hL hK j
  have hw := hW.2 e he p hp hpe L K hL hK j
  simpa only [LieBracketData.coefficients, dif_pos hpe] using hz.trans hw.symm

theorem frameSection_isLocal {D : SmoothDistribution C k} {U : Set M} {hU : IsOpen U}
    (F : DistributionFrame D U hU) (i : Fin k) :
    IsLocalField C.tangent U (frameSection F i) := by
  classical
  letI := C.tangent.topology
  apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
    C.tangent.manifold.smoothStructure.val
    (fun p => (⟨p, frameSection F i p⟩ : TangentBundleData.TotalSpace S)) U hU).mpr
  have heq : (fun q : U => (⟨q.val, frameSection F i q.val⟩ : TangentBundleData.TotalSpace S)) =
      (fun q : U => (⟨q.val, (F.basis q i).val⟩ : TangentBundleData.TotalSpace S)) := by
    funext q
    simp only [frameSection, dif_pos q.property]
  rw [heq]
  exact F.smooth i

theorem frameSection_valuesIn {D : SmoothDistribution C k} {U : Set M} {hU : IsOpen U}
    (F : DistributionFrame D U hU) (i : Fin k) : ValuesIn D U (frameSection F i) := by
  classical
  intro p hp
  simpa only [frameSection, dif_pos hp] using (F.basis ⟨p, hp⟩ i).property

theorem involutive_frame_test (D : SmoothDistribution C k) (hD : IsInvolutive D)
    (U : Set M) (hU : IsOpen U) (F : DistributionFrame D U hU) : FrameBracketClosed F := by
  intro i j Z hZ
  exact hD U hU _ _ Z (frameSection_isLocal F i) (frameSection_isLocal F j) hZ
    (frameSection_valuesIn F i) (frameSection_valuesIn F j)

/-- Rank zero gives the actual zero subspaces, rather than a separate model. -/
theorem zero_rank_fiber (D : SmoothDistribution C 0) (p : M) : D.fiber p = ⊥ := by
  letI := C.realization.space.topology
  obtain ⟨hk, U, hU, hp, b, hb⟩ := D.smooth p
  apply (Submodule.eq_bot_iff (D.fiber p)).mpr
  intro v hv
  apply (b.basis ⟨p, hp⟩).equivFun.injective
  funext j
  simpa using (hb ⟨p, hp⟩ v).mp hv j (Nat.zero_le _)

/-- At full rank the subspaces are the original full tangent spaces. -/
theorem full_rank_fiber (D : SmoothDistribution C n) (p : M) : D.fiber p = ⊤ := by
  letI := C.realization.space.topology
  obtain ⟨hk, U, hU, hp, b, hb⟩ := D.smooth p
  apply top_unique
  intro v _
  apply (hb ⟨p, hp⟩ v).mpr
  intro j hj
  omega

theorem zero_rank_involutive (D : SmoothDistribution C 0) : IsInvolutive D := by
  intro U hU X Y Z _ _ hZ hX hY p hp
  have hx : X p = 0 := by simpa only [zero_rank_fiber D p, Submodule.mem_bot] using hX p hp
  have hy : Y p = 0 := by simpa only [zero_rank_fiber D p, Submodule.mem_bot] using hY p hp
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨L, K, hL, hK⟩ := hZ.1 e he p hp hpe
  have hz : Z p = 0 := by
    apply (C.tangent.fiberCoordinates.equiv e he p hpe).injective
    funext j
    have h := hZ.2 e he p hp hpe L K hL hK j
    simpa [LieBracketData.coefficients, hpe, hx, hy] using h
  rw [hz]
  exact (D.fiber p).zero_mem

theorem full_rank_involutive (D : SmoothDistribution C n) : IsInvolutive D := by
  intro U _ X Y Z _ _ _ _ _ p _
  rw [full_rank_fiber D p]
  exact Submodule.mem_top

theorem extreme_ranks : Specs.SmoothManifolds.Ch08.DistributionTests.extreme_ranksType.{u} := by
  intro n M _ S C
  exact ⟨fun D => ⟨zero_rank_involutive D, zero_rank_fiber D⟩,
    fun D => ⟨full_rank_involutive D, full_rank_fiber D⟩⟩

theorem involutiveOn_univ_iff (D : SmoothDistribution C k) :
    IsInvolutiveOn D univ ↔ IsInvolutive D := by
  constructor
  · intro h U hU X Y Z hX hY hZ hDX hDY
    exact h U hU (subset_univ U) X Y Z hX hY hZ hDX hDY
  · intro h U hU _ X Y Z hX hY hZ hDX hDY
    exact h U hU X Y Z hX hY hZ hDX hDY

theorem involutiveOn_frame_test (D : SmoothDistribution C k)
    (U : Set M) (hU : IsOpen U) (F : DistributionFrame D U hU)
    (hD : IsInvolutiveOn D U) : FrameBracketClosed F := by
  intro i j Z hZ
  exact hD U hU (Subset.rfl) _ _ Z (frameSection_isLocal F i) (frameSection_isLocal F j) hZ
    (frameSection_valuesIn F i) (frameSection_valuesIn F j)

set_option maxHeartbeats 1200000 in
/-- Restriction to a subspace commutes with wedge, so forms vanishing on
D constitute a graded exterior ideal, including degree zero. -/
theorem vanishing_wedge :
    Specs.SmoothManifolds.Ch08.DistributionTests.vanishing_wedgeType.{u} := by
  intro n M _ S C k D U j l α β hα p hp v hv
  letI := C.realization.space.topology
  obtain ⟨hk, O, hO, hpO, b, hb⟩ := D.smooth p
  let A := BundleOperations.adaptedCoordinates (b.basis ⟨p, hpO⟩) (D.fiber p)
    hk (hb ⟨p, hpO⟩)
  letI : AddCommGroup (D.fiber p) := @Submodule.addCommGroup ℝ (TangentSpace S p) _ _ _ (D.fiber p)
  letI : Module ℝ (D.fiber p) := (D.fiber p).module
  letI : FiniteDimensional ℝ (D.fiber p) :=
    FiniteDimensional.of_injective A.toLinearMap A.injective
  let L : (D.fiber p) →ₗ[ℝ] TangentSpace S p := (D.fiber p).subtype
  have hrest : FormPullbackData.fiberPullback (V := D.fiber p)
      (W := TangentSpace S p) j L (α p) = 0 := by
    apply (ExteriorAlgebraResults.alternating_interpretation (D.fiber p) j).1
    apply AlternatingMap.ext
    intro w
    rw [FormPullbackResults.evaluate_fiberPullback, map_zero]
    change _ = 0
    exact hα p hp (fun i => L (w i)) (fun i => (w i).property)
  let w (i : Fin (j+l)) : D.fiber p := ⟨v i, hv i⟩
  have hL (i : Fin (j+l)) : L (w i) = v i := rfl
  have h := FormPullbackResults.evaluate_fiberPullback (V := D.fiber p)
    (W := TangentSpace S p) (j+l) L
    (ExteriorData.wedge (V := TangentSpace S p) (α p) (β p)) w
  change evaluate (TangentSpace S p) (j+l)
    (ExteriorData.wedge (V := TangentSpace S p) (α p) (β p)) v = 0
  simp only [hL] at h
  rw [← h, FormPullbackResults.fiberPullback_wedge, hrest]
  simp

/-- A zero scalar germ is killed by every tangent derivation. -/
theorem tangent_kills_zero_germ (p : M) (v : TangentSpace S p)
    (f : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f)
    (h : f =ᶠ[𝓝 p] 0) : v.val (functionGerm S f hf p) = 0 := by
  have hg : functionGerm S f hf p = 0 := by
    apply Subtype.ext
    exact h.germ_eq
  rw [hg, map_zero]

/-- Cartan's one-form identity on an open set where θ annihilates D.
The equality is local even though the participating ambient sections are global. -/
theorem annihilator_bracket_identity :
    Specs.SmoothManifolds.Ch08.DistributionTests.annihilator_bracket_identityType.{u} := by
  intro n M _ S C k D B U hU θ η hθ hη hvan b hb X Y hX hY p hp
  obtain ⟨f, hf, hval, hformula⟩ :=
    InvariantExteriorFormulaResults.invariant_positive C 0 B θ η hθ hη b hb ![X, Y]
  have hz (i : Fin 2) : f i =ᶠ[𝓝 p] 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    rw [hval]
    exact hvan q hq _ (fun j => by
      fin_cases i <;> fin_cases j <;> simp <;> first | exact hX q hq | exact hY q hq)
  have hact (i : Fin 2) :
      ((![(X), (Y)] i).val p).val (functionGerm S (f i) (hf i) p) = 0 :=
    tangent_kills_zero_germ p _ (f i) (hf i) (hz i)
  have h := hformula p
  simp only [hact, mul_zero, Finset.sum_const_zero, zero_add] at h
  have hIci : Finset.Ici (0 : Fin 1) = Finset.univ := by
    ext i
    simp
  have hfields : (fun j : Fin 2 => (![X, Y] j).val p) = ![X.val p, Y.val p] := by
    ext j
    fin_cases j <;> rfl
  simpa [Fin.sum_univ_succ, hIci, hfields] using h

/-- The invariant formula proves preservation on every tuple of smooth
ambient fields taking D-values on U. Extension of arbitrary fiber tuples to
such fields is kept as a separate, still necessary localization step. -/
theorem involutive_derivative_on_fields (D : SmoothDistribution C k) (hD : IsInvolutive D)
    (U : Set M) (hU : IsOpen U) (j : ℕ) (B : FormBundle C j)
    (ω : Field S j) (η : Field S (j+1)) (hω : IsForm B ω)
    (hη : HasExteriorDerivative C ω η) (hvan : VanishesOn D U ω)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent)
    (hb : BracketOperation b) (X : Fin (j+1) → SmoothField C.tangent)
    (hX : ∀ i, ValuesIn D U (X i).val) :
    ∀ p ∈ U, evaluate (TangentSpace S p) (j+1) (η p) (fun i => (X i).val p) = 0 := by
  intro p hp
  cases j with
  | zero =>
    obtain ⟨f, hf, hval, hformula⟩ :=
      InvariantExteriorFormulaResults.invariant_zero C B ω η hω hη (X 0)
    have hz : f =ᶠ[𝓝 p] 0 := by
      filter_upwards [hU.mem_nhds hp] with q hq
      rw [hval]
      exact hvan q hq _ (fun i => Fin.elim0 i)
    have h := hformula p
    have hact := tangent_kills_zero_germ p ((X 0).val p) f hf hz
    rw [hact] at h
    have heq : (fun i : Fin 1 => (X i).val p) = (fun _ => (X 0).val p) := by
      funext i
      exact congrArg (fun t => (X t).val p) (Subsingleton.elim i 0)
    simpa only [heq] using h
  | succ r =>
    obtain ⟨f, hf, hval, hformula⟩ :=
      InvariantExteriorFormulaResults.invariant_positive C r B ω η hω hη b hb X
    have hz (i : Fin (r+2)) : f i =ᶠ[𝓝 p] 0 := by
      filter_upwards [hU.mem_nhds hp] with q hq
      rw [hval]
      exact hvan q hq _ (fun t => hX (i.succAbove t) q hq)
    have hact (i : Fin (r+2)) :
        ((X i).val p).val (functionGerm S (f i) (hf i) p) = 0 :=
      tangent_kills_zero_germ p _ (f i) (hf i) (hz i)
    have h := hformula p
    simp only [hact, mul_zero, Finset.sum_const_zero, zero_add] at h
    rw [h]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro t ht
    have hbr := involutive_global_bracket D hD U hU b hb (X i.castSucc) (X t.succ)
      (hX i.castSucc) (hX t.succ) p hp
    have hv := hvan p hp
      (Matrix.vecCons ((b (X i.castSucc) (X t.succ)).val p)
        (t.removeNth (i.castSucc.removeNth (fun l => (X l).val p)))) (fun q => ?_)
    · rw [hv, mul_zero]
    · refine Fin.cases hbr (fun q => ?_) q
      exact hX (i.castSucc.succAbove (t.succAbove q)) p hp


universe v w

/-- Scalar multiplication of sections is smooth wherever both factors are smooth. -/
theorem bundle_section_smul_smoothAt {n r : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    {ι : Type v} {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (s : (p : M) → E p) (f : M → ℝ) (p : M)
    (hs : ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun q => (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E)) p)
    (hf : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f p) :
    ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun q => (⟨q, f q • s q⟩ : Bundle.TotalSpace (Euclidean r) E)) p := by
  obtain ⟨i, hi⟩ := B.covers p
  let z (q : M) := ((B.trivialization i) (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E)).2
  have hz : VectorSmoothAt S.smoothStructure.val z p :=
    FrameData.VectorSmoothAt.comp
      (C := B.totalManifold.smoothStructure.val)
      (g := fun q => (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E))
      (f := fun z : Bundle.TotalSpace (Euclidean r) E => ((B.trivialization i) z).2)
      B.totalManifold.smoothStructure.property.1.1
      (Frames.trivializationCoordinates_smoothAt B i ⟨p, s p⟩ hi) hs
  have hf' : VectorSmoothAt S.smoothStructure.val f p :=
    (scalarContDiffAt_iff _ _ _ _).mp hf
  apply Frames.smoothAt_from_trivialization B S.smoothStructure.property.1 i hi
    (manifoldContDiff_id _ _ S.smoothStructure.property.1 p)
    ((hf'.prod hz).postcomp (contDiff_fst.smul contDiff_snd)) (fun _ => rfl)
  have hopen : IsOpen (B.baseSet i) := by
    rw [← B.trivialization_baseSet i]
    exact (B.trivialization i).open_baseSet
  filter_upwards [hopen.mem_nhds hi] with q hq
  change ((B.trivialization i) (⟨q, f q • s q⟩ : Bundle.TotalSpace (Euclidean r) E)).2 = f q • z q
  have hqi : q ∈ (B.trivialization i).baseSet := by rwa [B.trivialization_baseSet]
  rw [← SmoothVectorBundle.fiberCoordinates_apply B i q hq,
    map_smul, SmoothVectorBundle.fiberCoordinates_apply]

/-- A local section multiplied by a smooth function supported inside its domain
is globally smooth. Closed support controls the boundary of the domain. -/
theorem bundle_cutoff_smooth {n r : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    {ι : Type v} {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (U : Set M) (s : (p : M) → E p)
    (hs : ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun q => (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E)) U)
    (χ : M → ℝ) (hχ : ScalarSmooth S.smoothStructure.val χ)
    (hsupp : sectionSupport χ ⊆ U) :
    IsSmoothMap S B.totalManifold
      (fun q => (⟨q, χ q • s q⟩ : Bundle.TotalSpace (Euclidean r) E)) := by
  intro p
  by_cases hp : p ∈ U
  · exact bundle_section_smul_smoothAt B s χ p (hs p hp) (hχ p)
  · have hout : p ∈ (sectionSupport χ)ᶜ := fun h => hp (hsupp h)
    apply manifoldContDiffAt_congr (B.zero_smooth p)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hout] with q hq
    have hz : χ q = 0 := Function.notMem_support.mp (fun h => hq (subset_closure h))
    simp only [hz, zero_smul]

/-- Every local smooth section has a global smooth representative of its germ. -/
theorem bundle_local_extension {n r : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    {ι : Type v} {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (U : Set M) (hU : IsOpen U)
    (s : (p : M) → E p)
    (hs : ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun q => (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E)) U)
    (p : M) (hp : p ∈ U) :
    ∃ t : (q : M) → E q,
      IsSmoothMap S B.totalManifold
        (fun q => (⟨q, t q⟩ : Bundle.TotalSpace (Euclidean r) E)) ∧
      ∀ᶠ q in 𝓝 p, t q = s q := by
  letI := S.topologicalManifold.hausdorff
  obtain ⟨χ, hχ, _, ⟨V, hV, hpV, hVχ⟩, hsupp⟩ :=
    exists_smooth_cutoff S {p} U isClosed_singleton hU (by simpa)
  refine ⟨fun q => χ q • s q, bundle_cutoff_smooth B U s hs χ hχ hsupp, ?_⟩
  filter_upwards [hV.mem_nhds (hpV (mem_singleton p))] with q hq
  rw [hVχ hq, one_smul]

theorem localField_extension (U : Set M) (hU : IsOpen U) (X : Section S)
    (hX : IsLocalField C.tangent U X) (p : M) (hp : p ∈ U) :
    ∃ Y : SmoothField C.tangent, ∀ᶠ q in 𝓝 p, Y.val q = X q := by
  letI := C.tangent.topology
  letI := C.realization.space.topology
  have hs : ManifoldSmoothOn S.smoothStructure.val
      C.realization.space.bundle.totalManifold.smoothStructure.val
      (fun q => (⟨q, X q⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) U := by
    intro q hq
    exact manifoldContDiffAt_comp C.tangent.manifold.smoothStructure.property.1.1
      (hX q hq) (C.realization.smooth_from_original _)
  obtain ⟨Y, hY, he⟩ := bundle_local_extension C.realization.space.bundle U hU X hs p hp
  refine ⟨⟨Y, ?_⟩, he⟩
  intro q
  exact manifoldContDiffAt_comp
    C.realization.space.bundle.totalManifold.smoothStructure.property.1.1
    (hY q) (C.realization.smooth_to_original _)

theorem localForm_extension (j : ℕ) (B : FormBundle C j)
    (U : Set M) (hU : IsOpen U) (ω : Field S j) (hω : IsLocalForm B U ω)
    (p : M) (hp : p ∈ U) :
    ∃ α : Field S j, IsForm B α ∧ ∀ᶠ q in 𝓝 p, α q = ω q := by
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  exact bundle_local_extension B.space.bundle U hU ω hω p hp

namespace LocalBracketWork
variable {B : TangentBundleStructure S}

theorem coefficients_germ {X Y : Section S} {p : M}
    (h : ∀ᶠ q in 𝓝 p, X q = Y q) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) :
    LieBracketData.coefficients B X e he =ᶠ[𝓝 p] LieBracketData.coefficients B Y e he := by
  filter_upwards [h] with q hq
  simp only [LieBracketData.coefficients, hq]

theorem coordinateDerivative_germ {m : ℕ}
    (e : ModelChart n .euclidean M) {f g : M → Euclidean m}
    {p : M} {L : Euclidean n →L[ℝ] Euclidean m}
    (hf : HasCoordinateDerivative e f p L) (h : f =ᶠ[𝓝 p] g) :
    HasCoordinateDerivative e g p L := by
  obtain ⟨F, hF, heF⟩ := hf
  exact ⟨F, hF, heF.trans h⟩

theorem bracket_point_unique {U V : Set M} {X Y Z W : Section S}
    (hZ : HasLocalBracket B U X Y Z) (hW : HasLocalBracket B V X Y W)
    {p : M} (hpU : p ∈ U) (hpV : p ∈ V) : Z p = W p := by
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨L, K, hL, hK⟩ := hZ.1 e he p hpU hpe
  apply (B.fiberCoordinates.equiv e he p hpe).injective
  funext j
  have hz := hZ.2 e he p hpU hpe L K hL hK j
  have hw := hW.2 e he p hpV hpe L K hL hK j
  simpa only [LieBracketData.coefficients, dif_pos hpe] using hz.trans hw.symm

theorem localBracket_congr {U : Set M} {X Y Z X' Y' Z' : Section S}
    (h : HasLocalBracket B U X Y Z)
    (hX : ∀ p ∈ U, ∀ᶠ q in 𝓝 p, X q = X' q)
    (hY : ∀ p ∈ U, ∀ᶠ q in 𝓝 p, Y q = Y' q)
    (hZ : ∀ p ∈ U, Z p = Z' p) : HasLocalBracket B U X' Y' Z' := by
  constructor
  · intro e he p hp hpe
    obtain ⟨L, K, hL, hK⟩ := h.1 e he p hp hpe
    exact ⟨L, K, coordinateDerivative_germ e hL (coefficients_germ (hX p hp) e he),
      coordinateDerivative_germ e hK (coefficients_germ (hY p hp) e he)⟩
  · intro e he p hp hpe L K hL hK j
    have hx := coefficients_germ (B := B) (hX p hp) e he
    have hy := coefficients_germ (B := B) (hY p hp) e he
    have h' := h.2 e he p hp hpe L K
      (coordinateDerivative_germ e hL hx.symm) (coordinateDerivative_germ e hK hy.symm) j
    have hz : LieBracketData.coefficients B Z e he p = LieBracketData.coefficients B Z' e he p := by
      simp only [LieBracketData.coefficients, hZ p hp]
    rw [hz, hx.eq_of_nhds, hy.eq_of_nhds] at h'
    exact h'

theorem localBracket_mono {U V : Set M} {X Y Z : Section S}
    (h : HasLocalBracket B U X Y Z) (hVU : V ⊆ U) :
    HasLocalBracket B V X Y Z :=
  ⟨fun e he p hp hpe => h.1 e he p (hVU hp) hpe,
    fun e he p hp hpe => h.2 e he p (hVU hp) hpe⟩

-- A gluing principle: genuinely smooth local bracket representatives give a
-- single smooth local bracket on an arbitrary open domain.
theorem localBracket_glue (U : Set M) (hU : IsOpen U) (X Y : Section S)
    (hlocal : ∀ p ∈ U, ∃ (V : Set M), IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∃ Z : SmoothField B, HasLocalBracket B V X Y Z.val) :
    ∃ Z : Section S, IsLocalField B U Z ∧ HasLocalBracket B U X Y Z ∧
      ∀ W, HasLocalBracket B U X Y W → ∀ p ∈ U, W p = Z p := by
  classical
  choose V hV hpV hVU W hW using fun p : U => hlocal p.val p.property
  let Z : Section S := fun p => if hp : p ∈ U then (W ⟨p, hp⟩).val p else 0
  have hZW (p : U) : ∀ᶠ q in 𝓝 p.val, Z q = (W p).val q := by
    filter_upwards [(hV p).mem_nhds (hpV p)] with q hq
    have hqU : q ∈ U := hVU p hq
    change (if hp : q ∈ U then (W ⟨q, hp⟩).val q else 0) = _
    rw [dif_pos hqU]
    exact bracket_point_unique (hW ⟨q, hqU⟩) (hW p) (hpV ⟨q, hqU⟩) hq
  have hbr : HasLocalBracket B U X Y Z := by
    constructor
    · intro e he p hp hpe
      exact (hW ⟨p, hp⟩).1 e he p (hpV ⟨p, hp⟩) hpe
    · intro e he p hp hpe L K hL hK j
      have hz := coefficients_germ (B := B) (hZW ⟨p, hp⟩) e he
      rw [hz.eq_of_nhds]
      exact (hW ⟨p, hp⟩).2 e he p (hpV ⟨p, hp⟩) hpe L K hL hK j
  refine ⟨Z, ?_, hbr, ?_⟩
  · letI := B.topology
    intro p hp
    apply manifoldContDiffAt_congr ((W ⟨p, hp⟩).smooth p)
    filter_upwards [(hZW ⟨p, hp⟩).mono (fun _ h => h.symm)] with q hq
    exact congrArg (fun v : TangentSpace S q => (⟨q, v⟩ : TotalSpace S)) hq
  · intro T hT p hp
    exact bracket_point_unique hT hbr hp hp


/-- Germ extension to genuine global smooth fields is the only input to this
local existence construction. The bracket itself is the accepted global bracket. -/
theorem localBracket_exists_of_global_extension (U : Set M) (hU : IsOpen U)
    (X Y : Section S)
    (hX : ∀ p ∈ U, ∃ X' : SmoothField B, ∀ᶠ q in 𝓝 p, X'.val q = X q)
    (hY : ∀ p ∈ U, ∃ Y' : SmoothField B, ∀ᶠ q in 𝓝 p, Y'.val q = Y q) :
    ∃ Z : Section S, IsLocalField B U Z ∧ HasLocalBracket B U X Y Z ∧
      ∀ W, HasLocalBracket B U X Y W → ∀ p ∈ U, W p = Z p := by
  classical
  obtain ⟨b, hb, _⟩ := LieBrackets.bracket_exists S B
  apply localBracket_glue U hU X Y
  intro p hp
  obtain ⟨X', hX'⟩ := hX p hp
  obtain ⟨Y', hY'⟩ := hY p hp
  obtain ⟨V, hsub, hV, hpV⟩ := mem_nhds_iff.mp (hX'.and hY')
  let O := U ∩ V
  have hO : IsOpen O := hU.inter hV
  have hpO : p ∈ O := ⟨hp, hpV⟩
  refine ⟨O, hO, hpO, inter_subset_left, b X' Y', ?_⟩
  have hcoords := LieBrackets.bracket_coordinates S B b hb X' Y'
  have hbr : HasLocalBracket B O X'.val Y'.val (b X' Y').val :=
    ⟨fun e he q _ hqe => hcoords.1 e he q hqe,
      fun e he q _ hqe => hcoords.2 e he q hqe⟩
  apply localBracket_congr hbr
  · intro q hq
    filter_upwards [hO.mem_nhds hq] with z hz
    exact (hsub hz.2).1
  · intro q hq
    filter_upwards [hO.mem_nhds hq] with z hz
    exact (hsub hz.2).2
  · intro q hq
    rfl

end LocalBracketWork

theorem chartDerivative_germ_value (j : ℕ) (ω α : Field S j) (p : M)
    (he : ∀ᶠ q in 𝓝 p, ω q = α q) :
    ExteriorDerivativeResults.chartDerivative C j ω p =
      ExteriorDerivativeResults.chartDerivative C j α p := by
  unfold ExteriorDerivativeResults.chartDerivative
  exact ExteriorDerivativeResults.coordinate_locality C j _ _ ω α p _ he

theorem local_derivative_unique (j : ℕ) (U : Set M) (ω : Field S j)
    (η ζ : Field S (j+1))
    (hη : HasLocalExteriorDerivative (C := C) U ω η)
    (hζ : HasLocalExteriorDerivative (C := C) U ω ζ) :
    ∀ p ∈ U, η p = ζ p := by
  intro p hp
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  exact (hη c hc p hp hpc).trans (hζ c hc p hp hpc).symm

theorem local_derivative_locality (j : ℕ) (U V : Set M) (ω α : Field S j)
    (η β : Field S (j+1))
    (hη : HasLocalExteriorDerivative (C := C) U ω η)
    (hβ : HasLocalExteriorDerivative (C := C) V α β)
    (p : M) (hpU : p ∈ U) (hpV : p ∈ V)
    (he : ∀ᶠ q in 𝓝 p, ω q = α q) : η p = β p := by
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  rw [hη c hc p hpU hpc, hβ c hc p hpV hpc]
  exact ExteriorDerivativeResults.coordinate_locality C j c hc ω α p hpc he

theorem local_derivative_of_global_germs (j : ℕ)
    (B : FormBundle C j) (E : FormBundle C (j+1))
    (U : Set M) (ω : Field S j)
    (hglobal : ∀ p ∈ U, ∃ α : Field S j, IsForm B α ∧
      ∀ᶠ q in 𝓝 p, α q = ω q) :
    ∃ η : Field S (j+1), IsLocalForm E U η ∧
      HasLocalExteriorDerivative (C := C) U ω η := by
  let η := ExteriorDerivativeResults.chartDerivative C j ω
  have hsame (p : M) (α : Field S j)
      (he : ∀ᶠ q in 𝓝 p, α q = ω q) :
      ∀ᶠ q in 𝓝 p, ExteriorDerivativeResults.chartDerivative C j α q = η q := by
    filter_upwards [eventually_eventually_nhds.mpr he] with q hq
    exact chartDerivative_germ_value j α ω q hq
  refine ⟨η, ?_, ?_⟩
  · letI := (cotangentSpace C).topology
    letI := E.space.topology
    intro p hp
    obtain ⟨α, hα, he⟩ := hglobal p hp
    have hdα := ExteriorDerivativeResults.chartDerivative_has C j α
      (ExteriorDerivativeResults.smooth_regular C j B α 1 hα)
    have hsα := ExteriorDerivativeResults.derivative_smooth C j B E α _ hα hdα
    apply manifoldContDiffAt_congr (hsα p)
    filter_upwards [hsame p α he] with q hq
    change (⟨q, ExteriorDerivativeResults.chartDerivative C j α q⟩ :
      Bundle.TotalSpace (Euclidean (n.choose (j+1)))
        (fun r => ExteriorData.Fiber (TangentSpace S r) (j+1))) = ⟨q, η q⟩
    rw [hq]
  · intro c hc p hp hpc
    obtain ⟨α, hα, he⟩ := hglobal p hp
    have hdα := ExteriorDerivativeResults.chartDerivative_has C j α
      (ExteriorDerivativeResults.smooth_regular C j B α 1 hα)
    calc
      η p = ExteriorDerivativeResults.chartDerivative C j α p :=
        chartDerivative_germ_value j ω α p (he.mono fun _ h => h.symm)
      _ = coordinateDerivative C j c hc α p hpc := hdα c hc p hpc
      _ = coordinateDerivative C j c hc ω p hpc :=
        ExteriorDerivativeResults.coordinate_locality C j c hc α ω p hpc he

theorem local_bracket_exists :
    Specs.SmoothManifolds.Ch08.DistributionTests.local_bracket_existsType.{u} := by
  intro n M _ S C U hU X Y hX hY
  exact LocalBracketWork.localBracket_exists_of_global_extension U hU X Y
    (localField_extension U hU X hX) (localField_extension U hU Y hY)

theorem local_derivative_exists :
    Specs.SmoothManifolds.Ch08.DistributionTests.local_derivative_existsType.{u} := by
  intro n M _ S C j B E U hU ω hω
  exact local_derivative_of_global_germs j B E U ω
    (localForm_extension j B U hU ω hω)

/-- A vector in a smooth subbundle extends to a globally smooth section of that
subbundle, using constant adapted-frame coefficients and a cutoff. -/
theorem distribution_vector_extension (D : SmoothDistribution C k) (p : M)
    (v : TangentSpace S p) (hv : v ∈ D.fiber p) :
    ∃ X : SmoothField C.tangent, X.val p = v ∧ ValuesIn D univ X.val := by
  classical
  letI := C.realization.space.topology
  letI := C.tangent.topology
  letI := S.topologicalManifold.hausdorff
  obtain ⟨hk, U, hU, hp, b, hb⟩ := D.smooth p
  let a : Euclidean n := (b.basis ⟨p, hp⟩).equivFun v
  let s (q : U) := (b.basis q).equivFun.symm a
  have hs : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      C.realization.space.bundle.totalManifold.smoothStructure.val
      (fun q : U => (⟨q.val, s q⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) := by
    apply (Frames.smooth_section_iff_coefficients C.realization.space.bundle U hU b s).mpr
    intro j q
    have heq : (fun z : U => FrameData.coefficients b s z j) = fun _ => a j := by
      funext z
      exact congrFun ((b.basis z).equivFun.apply_symm_apply a) j
    rw [heq]
    exact FrameData.VectorSmoothAt.const _ _ q
  let Y : Section S := fun q => if hq : q ∈ U then s ⟨q, hq⟩ else 0
  have hY : ManifoldSmoothOn S.smoothStructure.val
      C.realization.space.bundle.totalManifold.smoothStructure.val
      (fun q => (⟨q, Y q⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) U := by
    apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
      C.realization.space.bundle.totalManifold.smoothStructure.val _ U hU).mpr
    have heq : (fun q : U => (⟨q.val, Y q.val⟩ :
        Bundle.TotalSpace (Euclidean n) (TangentSpace S))) =
        (fun q : U => (⟨q.val, s q⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) := by
      funext q
      simp only [Y, dif_pos q.property]
    rw [heq]
    exact hs
  have hDY : ValuesIn D univ Y := by
    intro q _
    by_cases hq : q ∈ U
    · simp only [Y, dif_pos hq]
      apply (hb ⟨q,hq⟩ _).mpr
      intro j hj
      change (b.basis ⟨q,hq⟩).equivFun ((b.basis ⟨q,hq⟩).equivFun.symm a) j = 0
      rw [LinearEquiv.apply_symm_apply]
      exact (hb ⟨p,hp⟩ v).mp hv j hj
    · simp only [Y, dif_neg hq]
      exact (D.fiber q).zero_mem
  obtain ⟨χ, hχ, _, ⟨V, hV, hpV, hVχ⟩, hsupp⟩ :=
    exists_smooth_cutoff S {p} U isClosed_singleton hU (by simpa)
  let X : Section S := fun q => χ q • Y q
  have hX := bundle_cutoff_smooth C.realization.space.bundle U Y hY χ hχ hsupp
  refine ⟨⟨X, ?_⟩, ?_, ?_⟩
  · intro q
    exact manifoldContDiffAt_comp
      C.realization.space.bundle.totalManifold.smoothStructure.property.1.1
      (hX q) (C.realization.smooth_to_original _)
  · change χ p • Y p = v
    rw [hVχ (hpV (mem_singleton p)), one_smul]
    simp only [Y, dif_pos hp]
    exact (b.basis ⟨p,hp⟩).equivFun.symm_apply_apply v
  · intro q _
    exact (D.fiber q).smul_mem _ (hDY q (mem_univ q))

/-- The invariant formula, together with smooth extension of arbitrary fiber
vectors, proves preservation of the global vanishing ideal in every degree. -/
theorem involutive_globalIdealStable (D : SmoothDistribution C k)
    (hD : IsInvolutive D) (B : ∀ j, FormBundle C j) : GlobalIdealStable D B := by
  classical
  intro j ω η hω hη hvan p _ v hv
  choose X hXp hX using fun i => distribution_vector_extension D p (v i) (hv i)
  obtain ⟨b, hb, _⟩ := LieBrackets.bracket_exists S C.tangent
  have he := involutive_derivative_on_fields D hD univ isOpen_univ j (B j)
    ω η hω hη hvan b hb X hX p (mem_univ p)
  simpa only [show (fun i => (X i).val p) = v from funext hXp] using he

/-- A cutoff transfers global ideal preservation to all local degrees. -/
theorem globalIdealStable_local (D : SmoothDistribution C k)
    (B : ∀ j, FormBundle C j) (hD : GlobalIdealStable D B)
    (U : Set M) (hU : IsOpen U) (j : ℕ) (ω : Field S j) (η : Field S (j+1))
    (hω : IsLocalForm (B j) U ω)
    (hη : HasLocalExteriorDerivative (C := C) U ω η) (hvan : VanishesOn D U ω) :
    VanishesOn D U η := by
  letI := (cotangentSpace C).topology
  letI := (B j).space.topology
  letI := S.topologicalManifold.hausdorff
  intro p hp v hv
  obtain ⟨χ, hχ, _, ⟨V, hV, hpV, hVχ⟩, hsupp⟩ :=
    exists_smooth_cutoff S {p} U isClosed_singleton hU (by simpa)
  let α : Field S j := fun q => χ q • ω q
  have hα : IsForm (B j) α := bundle_cutoff_smooth (B j).space.bundle U ω hω χ hχ hsupp
  have he : ∀ᶠ q in 𝓝 p, α q = ω q := by
    filter_upwards [hV.mem_nhds (hpV (mem_singleton p))] with q hq
    change χ q • ω q = ω q
    rw [hVχ hq, one_smul]
  have hαvan : VanishesOn D univ α := by
    intro q _ w hw
    change evaluate (TangentSpace S q) j (χ q • ω q) w = 0
    rw [map_smul, AlternatingMap.smul_apply]
    by_cases hq : q ∈ U
    · rw [hvan q hq w hw, smul_zero]
    · have hz : χ q = 0 := Function.notMem_support.mp
        (fun h => hq (hsupp (subset_closure h)))
      rw [hz, zero_smul]
  let δ := ExteriorDerivativeResults.chartDerivative C j α
  have hδ : HasExteriorDerivative C α δ :=
    ExteriorDerivativeResults.chartDerivative_has C j α
      (ExteriorDerivativeResults.smooth_regular C j (B j) α 1 hα)
  have hδvan := hD j α δ hα hδ hαvan p (mem_univ p) v hv
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  have heq : δ p = η p := by
    rw [hδ c hc p hpc, hη c hc p hp hpc]
    exact ExteriorDerivativeResults.coordinate_locality C j c hc α ω p hpc he
  rw [heq] at hδvan
  exact hδvan

theorem globalIdealStable_localAnnihilatorTest (D : SmoothDistribution C k)
    (B : ∀ j, FormBundle C j) (hD : GlobalIdealStable D B) : LocalAnnihilatorTest D (B 1) := by
  intro U hU θ η hθ hη hvan
  exact globalIdealStable_local D B hD U hU 1 θ η hθ hη hvan

theorem field_coefficients_germ (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (X Y : Section S) (p : M)
    (h : ∀ᶠ q in 𝓝 p, X q = Y q) :
    LieBracketData.coefficients C.tangent X e he =ᶠ[𝓝 p]
      LieBracketData.coefficients C.tangent Y e he := by
  filter_upwards [h] with q hq
  unfold LieBracketData.coefficients
  split_ifs <;> simp only [hq]

theorem local_bracket_germ_value (U V : Set M) (X Y Z X' Y' Z' : Section S)
    (hZ : HasLocalBracket C.tangent U X Y Z)
    (hZ' : HasLocalBracket C.tangent V X' Y' Z')
    (p : M) (hpU : p ∈ U) (hpV : p ∈ V)
    (hX : ∀ᶠ q in 𝓝 p, X q = X' q) (hY : ∀ᶠ q in 𝓝 p, Y q = Y' q) :
    Z p = Z' p := by
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨L, K, hL, hK⟩ := hZ.1 e he p hpU hpe
  have hx  := field_coefficients_germ (C := C) e he X X' p hX
  have hy  := field_coefficients_germ (C := C) e he Y Y' p hY
  have hL' : HasCoordinateDerivative e (LieBracketData.coefficients C.tangent X' e he) p L := by
    obtain ⟨F, hF, heq⟩ := hL
    exact ⟨F, hF, heq.trans hx⟩
  have hK' : HasCoordinateDerivative e (LieBracketData.coefficients C.tangent Y' e he) p K := by
    obtain ⟨F, hF, heq⟩ := hK
    exact ⟨F, hF, heq.trans hy⟩
  apply (C.tangent.fiberCoordinates.equiv e he p hpe).injective
  funext j
  have hz := hZ.2 e he p hpU hpe L K hL hK j
  have hz' := hZ'.2 e he p hpV hpe L K hL' hK' j
  rw [← hx.eq_of_nhds, ← hy.eq_of_nhds] at hz'
  simpa only [LieBracketData.coefficients, dif_pos hpe] using hz.trans hz'.symm

theorem local_annihilator_bracket_identity
    (D : SmoothDistribution C k) (B : FormBundle C 1)
    (U : Set M) (hU : IsOpen U) (θ : Field S 1) (η : Field S 2)
    (hθ : IsLocalForm B U θ)
    (hη : HasLocalExteriorDerivative (C := C) U θ η)
    (hvan : VanishesOn D U θ) (X Y Z : Section S)
    (hX : IsLocalField C.tangent U X) (hY : IsLocalField C.tangent U Y)
    (hZ : HasLocalBracket C.tangent U X Y Z)
    (hXD : ValuesIn D U X) (hYD : ValuesIn D U Y) :
    ∀ p ∈ U, evaluate (TangentSpace S p) 2 (η p) ![X p, Y p] =
      -evaluate (TangentSpace S p) 1 (θ p) ![Z p] := by
  intro p hp
  obtain ⟨α, hα, heθ⟩ := localForm_extension 1 B U hU θ hθ p hp
  obtain ⟨X', heX⟩ := localField_extension U hU X hX p hp
  obtain ⟨Y', heY⟩ := localField_extension U hU Y hY p hp
  obtain ⟨η', hη', _⟩ := ExteriorDerivativeResults.c1_derivative_exists C 1 α
    (ExteriorDerivativeResults.smooth_regular C 1 B α 1 hα)
  have heAll : ∀ᶠ q in 𝓝 p,
      q ∈ U ∧ α q = θ q ∧ X'.val q = X q ∧ Y'.val q = Y q := by
    filter_upwards [hU.mem_nhds hp, heθ, heX, heY] with q hq hθq hXq hYq
    exact ⟨hq, hθq, hXq, hYq⟩
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp heAll
  have hvanα : VanishesOn D W α := by
    intro q hq v hv
    rw [(hWsub hq).2.1]
    exact hvan q (hWsub hq).1 v hv
  have hXD' : ValuesIn D W X'.val := by
    intro q hq
    rw [(hWsub hq).2.2.1]
    exact hXD q (hWsub hq).1
  have hYD' : ValuesIn D W Y'.val := by
    intro q hq
    rw [(hWsub hq).2.2.2]
    exact hYD q (hWsub hq).1
  obtain ⟨b, hb, _⟩ := LieBrackets.bracket_exists S C.tangent
  have hid := annihilator_bracket_identity D B W hW α η' hα hη' hvanα
    b hb X' Y' hXD' hYD' p hpW
  have heta : η' p = η p :=
    local_derivative_locality 1 univ U α θ η' η
      (fun c hc q _ hqc => hη' c hc q hqc) hη p (mem_univ _) hp heθ
  have hzp : (b X' Y').val p = Z p :=
    local_bracket_germ_value univ U
      X'.val Y'.val (b X' Y').val X Y Z
      (global_bracket_isLocal univ b hb X' Y') hZ p (mem_univ _) hp heX heY
  rw [heta, (hWsub hpW).2.2.1, (hWsub hpW).2.2.2, (hWsub hpW).2.1, hzp] at hid
  exact hid

theorem evaluate_one_covector {V : Type*} [AddCommGroup V] [Module ℝ V]
    (lam : Module.Dual ℝ V) (v : Fin 1 → V) :
    evaluate V 1 ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm lam) v = lam (v 0) := by
  have he : (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm lam =
      exteriorPower.ιMulti ℝ 1 (fun _ => lam) := by
    apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).injective
    simp [exteriorPower.oneEquiv_ιMulti]
  rw [he, ExteriorAlgebraResults.determinant_normalization]
  exact Matrix.det_fin_one _

/-- Cutoff extension within the annihilator, preserving its actual covector
value at the selected point. -/
theorem annihilator_global_covector (D : SmoothDistribution C k) (p : M)
    (lam : CotangentFiber S p) (hlam : lam ∈ DistributionData.annihilator D p) :
    ∃ α : CovectorField S, IsOneForm C α ∧
      (∀ q, α q ∈ DistributionData.annihilator D q) ∧ α p = lam := by
  classical
  letI := (cotangentSpace C).topology
  letI := S.topologicalManifold.hausdorff
  obtain ⟨U, hU, hp, s, hsp, hsD, hs⟩ := annihilator_local_extension D p lam hlam
  let α : CovectorField S := fun q => if hq : q ∈ U then s ⟨q, hq⟩ else 0
  have hα : ManifoldSmoothOn S.smoothStructure.val
      (cotangentSpace C).bundle.totalManifold.smoothStructure.val
      (fun q => (⟨q, α q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))) U := by
    apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
      (cotangentSpace C).bundle.totalManifold.smoothStructure.val
      (fun q => (⟨q, α q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))) U hU).mpr
    have he : (fun q : U => (⟨q.val, α q.val⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))) =
        (fun q : U => (⟨q.val, s q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))) := by
      funext q
      simp only [α, dite_eq_left q.property]
    rw [he]
    exact hs
  obtain ⟨χ, hχ, _, ⟨V, hV, hpV, hVχ⟩, hsupp⟩ :=
    exists_smooth_cutoff S {p} U isClosed_singleton hU (by simpa)
  refine ⟨fun q => χ q • α q,
    bundle_cutoff_smooth (cotangentSpace C).bundle U α hα χ hχ hsupp, ?_, ?_⟩
  · intro q
    apply (DistributionData.annihilator D q).smul_mem
    by_cases hq : q ∈ U
    · simpa only [α, dite_eq_left hq] using hsD ⟨q, hq⟩
    · simp only [α, dite_eq_right hq]
      exact (DistributionData.annihilator D q).zero_mem
  · change χ p • α p = lam
    rw [hVχ (hpV (mem_singleton p)), one_smul]
    simpa only [α, dite_eq_left hp] using hsp

/-- Every annihilator covector is the value of a global smooth degree-one
form in the global vanishing ideal. -/
theorem annihilator_global_form (D : SmoothDistribution C k) (B : FormBundle C 1)
    (p : M) (lam : CotangentFiber S p) (hlam : lam ∈ DistributionData.annihilator D p) :
    ∃ θ : Field S 1, IsForm B θ ∧ VanishesOn D univ θ ∧
      θ p = (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm lam := by
  obtain ⟨α, hα, hαD, hαp⟩ := annihilator_global_covector D p lam hlam
  refine ⟨fun q => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S q))).symm (α q),
    ExteriorDerivativeResults.oneForm_isForm C B α hα, ?_, ?_⟩
  · intro q hq v hv
    rw [evaluate_one_covector]
    exact (Submodule.mem_dualAnnihilator (W := D.fiber q) (α q)).mp (hαD q) _ (hv 0)
  · dsimp only
    rw [hαp]

/-- Naturality along integral immersions proves stability of the full global
vanishing ideal without choosing an embedded patch or lifting vector fields. -/
theorem integrable_globalIdealStable (D : SmoothDistribution C k)
    (hD : IsIntegrable D) (B : ∀ j, FormBundle C j) : GlobalIdealStable D B := by
  classical
  intro j ω η hω hη hvan p hp v hv
  obtain ⟨A, hpA, t, T, hi, himm, L, hL, hrange⟩ := hD p
  letI : TopologicalSpace A := t
  let q : A := ⟨p, hpA⟩
  obtain ⟨CT⟩ := BundleOperations.exists_cotangent T
  have hzero : FormPullbackData.pullbackField T S Subtype.val L ω = 0 := by
    funext z
    letI : FiniteDimensional ℝ (TangentSpace T z) := (tangent_dimension T z).1
    apply (ExteriorAlgebraResults.alternating_interpretation (TangentSpace T z) j).1
    apply AlternatingMap.ext
    intro w
    rw [FormPullbackResults.pullback_apply, Pi.zero_apply, map_zero]
    exact hvan z.val (mem_univ _) (fun i => L z (w i)) (fun i => by
      rw [← hrange z]
      exact LinearMap.mem_range.mpr ⟨w i, rfl⟩)
  have hnat := (ExteriorDerivativeResults.c1_naturality T S CT C Subtype.val hi L hL j ω η
    (ExteriorDerivativeResults.smooth_regular C j (B j) ω 1 hω) hη).2
  rw [hzero] at hnat
  have hdeta : FormPullbackData.pullbackField T S Subtype.val L η = 0 :=
    ExteriorDerivativeResults.derivative_unique CT j 0 _ 0 hnat
      (ExteriorDerivativeResults.zero_derivative CT j)
  have hlift (i : Fin (j+1)) : ∃ x : TangentSpace T q, L q x = v i := by
    apply LinearMap.mem_range.mp
    rw [hrange]
    exact hv i
  choose w hw using hlift
  have he := FormPullbackResults.pullback_apply T S Subtype.val L (j+1) η q w
  rw [show (fun i => L q (w i)) = v from funext hw] at he
  rw [hdeta, Pi.zero_apply, map_zero] at he
  exact he.symm

/-- Multilinearity reduces vanishing on a subspace to any of its bases. -/
theorem alternating_vanishesOn_basis {V : Type*} [AddCommGroup V] [Module ℝ V]
    {d r : ℕ} (K : Submodule ℝ V) (b : Module.Basis (Fin r) ℝ K)
    (α : AlternatingMap ℝ V ℝ (Fin d))
    (hα : ∀ w : Fin d → Fin r, α (fun i => (b (w i)).val) = 0)
    (v : Fin d → V) (hv : ∀ i, v i ∈ K) : α v = 0 := by
  let β := α.compLinearMap K.subtype
  have hz : β.toMultilinearMap = 0 := by
    apply Module.Basis.ext_multilinear (fun _ => b)
    intro w
    exact hα w
  have he := congrArg (fun f : MultilinearMap ℝ (fun _ : Fin d => K) ℝ =>
    f (fun i => (⟨v i, hv i⟩ : K))) hz
  exact he

/-- A two-form vanishes on D iff it vanishes on each pair in a specified
frame; no positivity hypothesis on the distribution rank is needed. -/
theorem twoForm_vanishesOn_frame (D : SmoothDistribution C k)
    (U : Set M) (hU : IsOpen U) (F : DistributionFrame D U hU)
    (η : Field S 2)
    (hη : ∀ p ∈ U, ∀ i j : Fin k,
      evaluate (TangentSpace S p) 2 (η p)
        ![frameSection F i p, frameSection F j p] = 0) :
    VanishesOn D U η := by
  classical
  intro p hp v hv
  apply alternating_vanishesOn_basis (D.fiber p) (F.basis ⟨p, hp⟩)
    (evaluate (TangentSpace S p) 2 (η p)) ?_ v hv
  intro w
  have he : (fun i => ((F.basis ⟨p, hp⟩) (w i)).val) =
      ![frameSection F (w 0) p, frameSection F (w 1) p] := by
    funext i
    fin_cases i <;> simp [frameSection, hp]
  rw [he]
  exact hη p hp (w 0) (w 1)

theorem involutive_localAnnihilatorTest (D : SmoothDistribution C k)
    (hD : IsInvolutive D) (B : FormBundle C 1) : LocalAnnihilatorTest D B := by
  intro U hU θ η hθ hη hvan p hp v hv
  obtain ⟨X, hXp, hXD⟩ := distribution_vector_extension D p (v 0) (hv 0)
  obtain ⟨Y, hYp, hYD⟩ := distribution_vector_extension D p (v 1) (hv 1)
  obtain ⟨b, hb, _⟩ := LieBrackets.bracket_exists S C.tangent
  have hXU : ValuesIn D U X.val := fun q _ => hXD q (mem_univ q)
  have hYU : ValuesIn D U Y.val := fun q _ => hYD q (mem_univ q)
  have hbr : ValuesIn D U (b X Y).val := hD U hU X.val Y.val (b X Y).val
    (smoothField_isLocal U X) (smoothField_isLocal U Y)
    (global_bracket_isLocal U b hb X Y) hXU hYU
  have hz := hvan p hp ![(b X Y).val p] (by
    intro i
    fin_cases i
    exact hbr p hp)
  have hi := local_annihilator_bracket_identity D B U hU θ η hθ hη hvan
    X.val Y.val (b X Y).val (smoothField_isLocal U X) (smoothField_isLocal U Y)
    (global_bracket_isLocal U b hb X Y) hXU hYU p hp
  rw [hz, neg_zero, hXp, hYp] at hi
  have he : ![v 0, v 1] = v := by
    ext i
    fin_cases i <;> rfl
  simpa only [he] using hi

/-- Global stability detects brackets of arbitrary local fields, by extending
both the test covector and the germs of the two fields. -/
theorem derivative_closed_involutiveOn (D : SmoothDistribution C k)
    (B : FormBundle C 1) (R : Set M)
    (hclosed : ∀ (θ : Field S 1) (η : Field S 2), IsForm B θ →
      HasExteriorDerivative C θ η → VanishesOn D univ θ → VanishesOn D R η) :
    IsInvolutiveOn D R := by
  intro U hU hUR X Y Z hX hY hZ hDX hDY p hp
  apply (annihilator_separates D p (Z p)).mpr
  intro lam hlam
  obtain ⟨θ, hθ, hθD, hθp⟩ := annihilator_global_form D B p lam hlam
  let η := ExteriorDerivativeResults.chartDerivative C 1 θ
  have hη : HasExteriorDerivative C θ η :=
    ExteriorDerivativeResults.chartDerivative_has C 1 θ
      (ExteriorDerivativeResults.smooth_regular C 1 B θ 1 hθ)
  have hηD := hclosed θ η hθ hη hθD
  obtain ⟨X', heX⟩ := localField_extension U hU X hX p hp
  obtain ⟨Y', heY⟩ := localField_extension U hU Y hY p hp
  obtain ⟨V, hsub, hV, hpV⟩ := mem_nhds_iff.mp (heX.and heY)
  let O := U ∩ V
  have hO : IsOpen O := hU.inter hV
  have hpO : p ∈ O := ⟨hp, hpV⟩
  have hX'D : ValuesIn D O X'.val := by
    intro q hq
    rw [(hsub hq.2).1]
    exact hDX q hq.1
  have hY'D : ValuesIn D O Y'.val := by
    intro q hq
    rw [(hsub hq.2).2]
    exact hDY q hq.1
  obtain ⟨b, hb, _⟩ := LieBrackets.bracket_exists S C.tangent
  have hbr : HasLocalBracket C.tangent O X Y (b X' Y').val := by
    apply LocalBracketWork.localBracket_congr (global_bracket_isLocal O b hb X' Y')
    · intro q hq
      filter_upwards [hO.mem_nhds hq] with z hz
      exact (hsub hz.2).1
    · intro q hq
      filter_upwards [hO.mem_nhds hq] with z hz
      exact (hsub hz.2).2
    · intro q hq
      rfl
  have hZp := LocalBracketWork.bracket_point_unique hZ hbr hp hpO
  have hidentity := annihilator_bracket_identity D B O hO θ η hθ hη
    (fun q _ => hθD q (mem_univ _)) b hb X' Y' hX'D hY'D p hpO
  have hz : evaluate (TangentSpace S p) 2 (η p) ![X'.val p, Y'.val p] = 0 := by
    apply hηD p (hUR hp) _
    intro i
    fin_cases i
    · exact hX'D p hpO
    · exact hY'D p hpO
  rw [hz, hθp, evaluate_one_covector] at hidentity
  change 0 = -lam ((b X' Y').val p) at hidentity
  rw [hZp]
  exact neg_eq_zero.mp hidentity.symm


theorem localAnnihilatorTest_involutive (D : SmoothDistribution C k)
    (B : FormBundle C 1) (hlocal : LocalAnnihilatorTest D B) : IsInvolutive D := by
  apply (involutiveOn_univ_iff D).mp
  apply derivative_closed_involutiveOn D B univ
  intro θ η hθ hη hθD
  exact hlocal univ isOpen_univ θ η (fun p _ => hθ p) (fun c hc p _ hp => hη c hc p hp) hθD

theorem globalIdealStable_involutive (D : SmoothDistribution C k)
    (B : ∀ j, FormBundle C j) (hstable : GlobalIdealStable D B) : IsInvolutive D := by
  apply (involutiveOn_univ_iff D).mp
  exact derivative_closed_involutiveOn D (B 1) univ (hstable 1)



/-- The local annihilator criterion for involutivity. -/
theorem annihilator_test :
    Specs.SmoothManifolds.Ch08.DistributionTests.annihilator_testType.{u} := by
  intro n M _ S C k D B
  exact ⟨fun hD => involutive_localAnnihilatorTest D hD B,
    localAnnihilatorTest_involutive D B⟩

/-- Preservation of the global graded vanishing ideal characterizes involutivity. -/
theorem ideal_test :
    Specs.SmoothManifolds.Ch08.DistributionTests.ideal_testType.{u} := by
  intro n M _ S C k D B
  exact ⟨fun hD => involutive_globalIdealStable D hD B,
    globalIdealStable_involutive D B⟩

/-- Integral submanifolds force involutivity, via naturality of the exterior
 derivative and the annihilator test. -/
theorem integrable_involutive :
    Specs.SmoothManifolds.Ch08.DistributionTests.integrable_involutiveType.{u} := by
  intro n M _ S C k D hD
  let B : ∀ j, FormBundle C j := fun j =>
    Classical.choice (ExteriorAlgebraResults.exists_formBundle C j)
  exact globalIdealStable_involutive D B (integrable_globalIdealStable D hD B)


/-- Frame closure implies the annihilator derivative test on every smaller
open domain. This uses the local bracket construction and local one-form identity. -/
theorem frame_annihilator_test
    (D : SmoothDistribution C k)
    (U : Set M) (hU : IsOpen U) (F : DistributionFrame D U hU)
    (hF : FrameBracketClosed F) (V : Set M) (hV : IsOpen V) (hVU : V ⊆ U)
    (B : FormBundle C 1) (θ : Field S 1) (η : Field S 2)
    (hθ : IsLocalForm B V θ) (hη : HasLocalExteriorDerivative (C := C) V θ η)
    (hvan : VanishesOn D V θ) : VanishesOn D V η := by
  classical
  intro p hp v hv
  apply alternating_vanishesOn_basis (D.fiber p) (F.basis ⟨p, hVU hp⟩)
    (evaluate (TangentSpace S p) 2 (η p)) ?_ v hv
  intro w
  let X := frameSection F (w 0)
  let Y := frameSection F (w 1)
  have hsX := DistributionTests.frameSection_isLocal F (w 0)
  have hsY := DistributionTests.frameSection_isLocal F (w 1)
  obtain ⟨Z, hsZ, hZ, hunique⟩ := local_bracket_exists C U hU X Y hsX hsY
  have hZV : HasLocalBracket C.tangent V X Y Z :=
    ⟨fun e he p hp hpe => hZ.1 e he p (hVU hp) hpe,
      fun e he p hp hpe => hZ.2 e he p (hVU hp) hpe⟩
  have hXD := DistributionTests.frameSection_valuesIn F (w 0)
  have hYD := DistributionTests.frameSection_valuesIn F (w 1)
  have htest := local_annihilator_bracket_identity D B V hV θ η hθ hη hvan X Y Z
    (fun p hp => hsX p (hVU hp)) (fun p hp => hsY p (hVU hp)) hZV
    (fun p hp => hXD p (hVU hp)) (fun p hp => hYD p (hVU hp)) p hp
  have hz : Z p ∈ D.fiber p := hF (w 0) (w 1) Z hZ p (hVU hp)
  have hθZ : evaluate (TangentSpace S p) 1 (θ p) ![Z p] = 0 := by
    apply hvan p hp
    intro i
    fin_cases i
    exact hz
  rw [hθZ, neg_zero] at htest
  have he : (fun i => ((F.basis ⟨p, hVU hp⟩) (w i)).val) = ![X p, Y p] := by
    funext i
    fin_cases i <;> simp [X, Y, frameSection, hVU hp]
  rw [he]
  exact htest


theorem frame_test : Specs.SmoothManifolds.Ch08.DistributionTests.frame_testType.{u} := by
  intro n M _ S C k D U hU F
  constructor
  · exact DistributionTests.involutiveOn_frame_test D U hU F
  · intro hF V hV hVU X Y Z hX hY hZ hDX hDY p hp
    apply (DistributionTests.annihilator_separates D p (Z p)).mpr
    intro lam hlam
    obtain ⟨B⟩ := ExteriorAlgebraResults.exists_formBundle C 1
    obtain ⟨θ, hθ, hθD, hθp⟩ := DistributionTests.annihilator_global_form D B p lam hlam
    let η := ExteriorDerivativeResults.chartDerivative C 1 θ
    have hη : HasExteriorDerivative C θ η :=
      ExteriorDerivativeResults.chartDerivative_has C 1 θ
        (ExteriorDerivativeResults.smooth_regular C 1 B θ 1 hθ)
    have hθV : IsLocalForm B V θ := fun q _ => hθ q
    have hηV : HasLocalExteriorDerivative (C := C) V θ η :=
      fun c hc q _ hqc => hη c hc q hqc
    have hθDV : VanishesOn D V θ := fun q _ => hθD q (mem_univ _)
    have hηDV := frame_annihilator_test D U hU F hF V hV hVU B θ η hθV hηV hθDV
    have hidentity := DistributionTests.local_annihilator_bracket_identity D B V hV θ η
      hθV hηV hθDV X Y Z hX hY hZ hDX hDY p hp
    have hz : evaluate (TangentSpace S p) 2 (η p) ![X p, Y p] = 0 := by
      apply hηDV p hp
      intro i
      fin_cases i
      · exact hDX p hp
      · exact hDY p hp
    rw [hz, hθp, evaluate_one_covector] at hidentity
    exact neg_eq_zero.mp hidentity.symm


end SmoothManifolds.DistributionTests
