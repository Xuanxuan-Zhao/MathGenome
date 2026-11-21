import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PullbackConnections
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionForms

/-! Pullback bundles and connections for Proposition 6.2. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.PullbackConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
open Set Filter
open scoped Topology
universe u v w

noncomputable abbrev bundle := @P202.PullbackData.bundle

section PullbackSections
variable {n m r : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (F : N → M) (hF : IsSmoothMap T S F)
  (P : PullbackBundle B T F)

include hF

/-- Smoothness of a section pulled back to the actual P104 bundle, tested in
its prescribed trivializations. -/
theorem section_pullback_smoothOn (U : Set M) (s : (p : M) → E p)
    (hs : ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, s p⟩ : Bundle.TotalSpace (Euclidean r) E)) U) :
    letI := P.space.topology
    ManifoldSmoothOn T.smoothStructure.val P.space.bundle.totalManifold.smoothStructure.val
      (fun q => (⟨q, s (F q)⟩ : Bundle.TotalSpace (Euclidean r) (fun q => E (F q))))
      (F ⁻¹' U) := by
  letI := P.space.topology
  intro q hq
  obtain ⟨i, hi⟩ := B.covers (F q)
  apply SmoothManifolds.SectionExtension.smoothAt_of_coordinates P.space.bundle i
    (by rw [P.baseSet]; exact hi)
  have hc := (SmoothManifolds.SectionExtension.coordinates_smoothAt B i hi (hs (F q) hq)).comp
    S.smoothStructure.property.1.1 (hF q)
  apply hc.congr
  have ho : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  filter_upwards [(hF q).1.preimage_mem_nhds (ho.mem_nhds hi)] with z hz
  exact (P.coordinates i z hz (s (F z))).symm

/-- Canonical pullback of a globally smooth section. -/
noncomputable def pullSection (s : Section B) :
    letI := P.space.topology; Section P.space.bundle := by
  letI := P.space.topology
  exact ⟨fun q => s.val (F q), fun q =>
    section_pullback_smoothOn B F hF P Set.univ s.val (fun p _ => s.property p)
      q (Set.mem_univ (F q))⟩

@[simp] theorem pullSection_apply (s : Section B) (q : N) :
    (pullSection B F hF P s).val q = s.val (F q) := rfl

/-- Pullback of an arbitrary local smooth frame; its basis is the same basis
in the identical fiber E_(F q). -/
noncomputable def pullFrame {U : Set M} (hU : IsOpen U) (e : LocalFrame B U hU) :
    letI := P.space.topology
    LocalFrame P.space.bundle (F ⁻¹' U)
      (hU.preimage (continuous_iff_continuousAt.mpr (fun q => (hF q).1))) := by
  letI := P.space.topology
  let hV := hU.preimage (continuous_iff_continuousAt.mpr (fun q => (hF q).1))
  refine { section_ := fun j q => e.section_ j ⟨F q.val, q.property⟩
           basis := fun q => e.basis ⟨F q.val, q.property⟩
           basis_eq := fun q j => e.basis_eq _ j
           smooth := ?_ }
  intro j
  have hs := section_pullback_smoothOn B F hF P U
    (SmoothManifolds.SectionExtension.totalSection (e.section_ j))
    (SmoothManifolds.SectionExtension.totalSection_smooth B hU _ (e.smooth j))
  have hr := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    _ _ _ (F ⁻¹' U) hV).mp hs
  have heq : (fun q : F ⁻¹' U => (⟨q.val,
      SmoothManifolds.SectionExtension.totalSection (e.section_ j) (F q.val)⟩ :
      Bundle.TotalSpace (Euclidean r) (fun q => E (F q)))) =
      (fun q : F ⁻¹' U => (⟨q.val, e.section_ j ⟨F q.val, q.property⟩⟩ :
      Bundle.TotalSpace (Euclidean r) (fun q => E (F q)))) := by
    funext q
    rw [SmoothManifolds.SectionExtension.totalSection_of_mem (e.section_ j) (F q.val) q.property]
  rw [← heq]
  exact hr

/-- Pullback of a globally smooth scalar, in the genuine scalar algebra. -/
noncomputable def pullScalar (f : GlobalSmooth S) : GlobalSmooth T := by
  refine ⟨fun q => f.val (F q), (SmoothManifolds.mem_globalSmoothAlgebra_iff T _).mpr ?_⟩
  intro q
  apply (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
  have hf : VectorSmoothAt S.smoothStructure.val f.val (F q) :=
    (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
      ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp f.property (F q))
  exact hf.comp S.smoothStructure.property.1.1 (hF q)

/-- The chain rule follows directly from the intrinsic action on smooth germs. -/
theorem scalar_chain (f : GlobalSmooth S) (X : Field T) (q : N) :
    (act T X (pullScalar F hF f)).val q =
      scalarDerivative S f.val (F q)
        (SmoothManifolds.differential T S F hF q (X.val q)) := by
  rw [ConnectionForms.scalarDerivative_representative f.val f (F q) Filter.EventuallyEq.rfl]
  exact (SmoothManifolds.differential_spec T S F hF q (X.val q)
    (SmoothManifolds.globalToGerm S (F q) f)
    (SmoothManifolds.globalToGerm T q (pullScalar F hF f)) f.val rfl rfl).symm

omit hF in
/-- Independence of the local representative in a scalar differential. -/
theorem scalarDerivative_congr (f g : M → ℝ) (p : M)
    (hf : ∃ h : GlobalSmooth S, h.val =ᶠ[𝓝 p] f)
    (hfg : f =ᶠ[𝓝 p] g) : scalarDerivative S f p = scalarDerivative S g p := by
  obtain ⟨h, hh⟩ := hf
  ext v
  rw [ConnectionForms.scalarDerivative_representative f h p hh,
    ConnectionForms.scalarDerivative_representative g h p (hh.trans hfg)]

/-- Differentiating a finite pulled-back expansion gives zero whenever the
expansion vanishes near the point. This is the well-definedness argument for
the construction; the coefficient functions need not descend through F. -/
theorem expansion_derivative_zero (C : Connection B) {κ : Type*} [Fintype κ]
    (X : Field T) (f : κ → GlobalSmooth T) (s : κ → Section B) (q : N)
    (hz : ∀ᶠ z in 𝓝 q, ∑ j, (f j).val z • (s j).val (F z) = 0) :
    ∑ j, ((act T X (f j)).val q • (s j).val (F q) +
      (f j).val q • pointDerivative C (s j).val (F q)
        (SmoothManifolds.differential T S F hF q (X.val q))) = 0 := by
  classical
  obtain ⟨U, hU, hpU, ⟨e⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (F q)
  let p : U := ⟨F q, hpU⟩
  have hs (j : κ) := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    S.smoothStructure.val B.totalManifold.smoothStructure.val _ U hU).mp
      (fun z _ => (s j).property z)
  have ha (j : κ) := ConnectionForms.local_coefficients_representative B e
    (fun z => (s j).val z.val) (hs j) p
  choose a ha using ha
  let H (i : Fin r) : GlobalSmooth T := ∑ j, f j * pullScalar F hF (a j i)
  have hHz (i : Fin r) : (H i).val =ᶠ[𝓝 q] (fun _ => 0) := by
    have hnear : ∀ᶠ z in 𝓝 (F q), ∀ j i, (a j i).val z =
        totalize (fun z : U => SmoothManifolds.FrameData.coefficients e
          (fun z => (s j).val z.val) z i) z :=
      Filter.eventually_all.mpr (fun j => Filter.eventually_all.mpr (ha j))
    filter_upwards [hz, (hF q).1.tendsto.eventually hnear,
      (hF q).1.preimage_mem_nhds (hU.mem_nhds hpU)] with z hzz hza hzU
    have he := congrArg (fun v : E (F z) => (e.basis ⟨F z, hzU⟩).equivFun v i) hzz
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      map_zero, Pi.zero_apply] at he
    simp only [H, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,
      Subalgebra.coe_mul, Pi.mul_apply, pullScalar]
    convert he using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hza j i, totalize_of_mem _ (F z) hzU]
    rfl
  have hH (i : Fin r) : (H i).val q = 0 := (hHz i).eq_of_nhds
  have hdH (i : Fin r) : (act T X (H i)).val q = 0 := by
    have he := ConnectionForms.act_congr X (H i) 0 q (hHz i)
    simpa only [map_zero, ZeroMemClass.coe_zero, Pi.zero_apply] using he
  apply (e.basis p).equivFun.injective
  ext i
  simp only [map_sum, map_add, map_smul, Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_zero, Pi.zero_apply]
  have hv (j : κ) : (e.basis p).equivFun ((s j).val (F q)) =
      fun i => (a j i).val (F q) := by
    funext i
    exact ((ha j i).eq_of_nhds.trans
      (totalize_of_mem _ (F q) hpU)).symm
  have hd (j : κ) : (e.basis p).equivFun
      (pointDerivative C (s j).val (F q)
        (SmoothManifolds.differential T S F hF q (X.val q))) i =
      (act T X (pullScalar F hF (a j i))).val q +
        ∑ l, connectionForm C e p i l
          (SmoothManifolds.differential T S F hF q (X.val q)) * (a j l).val (F q) := by
    have hc := ConnectionForms.local_frame_formula B C e
      (restrictGlobalSection (s j) U hU) p
      (SmoothManifolds.differential T S F hF q (X.val q)) i
    have heq : ∀ᶠ z in 𝓝 (F q), (s j).val z =
        SmoothManifolds.SectionExtension.totalSection
          (restrictGlobalSection (s j) U hU).val z := by
      filter_upwards [hU.mem_nhds hpU] with z hzU
      simp only [SmoothManifolds.SectionExtension.totalSection_of_mem _ z hzU]
      rfl
    rw [← ConnectionForms.pointDerivative_congr B C (s j).val _ (F q)
      ⟨s j, Filter.Eventually.of_forall (fun _ => rfl)⟩ heq] at hc
    rw [hc, scalar_chain F hF (a j i) X q]
    congr 1
    · exact ConnectionForms.scalarDerivative_representative _ (a j i) (F q)
        (ha j i) _
        |>.trans (ConnectionForms.scalarDerivative_representative (a j i).val (a j i)
          (F q) Filter.EventuallyEq.rfl _).symm
    · apply Finset.sum_congr rfl
      intro l _
      change _ * ((e.basis p).equivFun ((s j).val (F q)) l) = _
      rw [hv j]
  simp_rw [hv, hd]
  have hder : (∑ j, ((act T X (f j)).val q * (a j i).val (F q) +
      (f j).val q * (act T X (pullScalar F hF (a j i))).val q)) = 0 := by
    have hh := hdH i
    simp only [H, map_sum, Derivation.leibniz, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_apply, smul_eq_mul, Subalgebra.coe_add, Pi.add_apply, Subalgebra.coe_mul,
      Pi.mul_apply, pullScalar] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    change _ = (f j).val q * (act T X (pullScalar F hF (a j i))).val q +
      (a j i).val (F q) * (act T X (f j)).val q
    ring
  calc
    _ = (∑ j, ((act T X (f j)).val q * (a j i).val (F q) +
        (f j).val q * (act T X (pullScalar F hF (a j i))).val q)) +
        ∑ l, connectionForm C e p i l
          (SmoothManifolds.differential T S F hF q (X.val q)) *
            (∑ j, (f j).val q * (a j l).val (F q)) := by
      simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      rw [add_assoc]
      congr 1
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by
      rw [hder]
      have hh (l : Fin r) : (∑ j, (f j).val q * (a j l).val (F q)) = 0 := by
        simpa only [H, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,
          Subalgebra.coe_mul, Pi.mul_apply, pullScalar] using hH l
      simp only [hh, mul_zero, Finset.sum_const_zero, add_zero]

/-- Smoothness of the genuine differential along a smooth source field,
using the two canonical tangent realizations. -/
theorem differential_field_smooth (X : Field T) :
    letI := (P202.MetricData.tangentStructure S).topology
    IsSmoothMap T (P202.MetricData.tangentStructure S).manifold
      (fun q => (⟨F q, SmoothManifolds.differential T S F hF q (X.val q)⟩ :
        SmoothManifolds.TangentBundleData.TotalSpace S)) := by
  letI := (P202.MetricData.tangentStructure T).topology
  letI := (P202.MetricData.tangentStructure S).topology
  have hd := SmoothManifolds.TangentBundle.map_smooth T S
    (P202.MetricData.tangentStructure T) (P202.MetricData.tangentStructure S)
    F hF (SmoothManifolds.differential T S F hF)
    (SmoothManifolds.differential_spec T S F hF)
  exact SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (P202.MetricData.tangentStructure T).manifold.smoothStructure.property.1.1
    _ _ (originalField T X).smooth hd

/-- The derivative of a target section evaluated along dF(X) is smooth in the
actual pullback bundle. Smoothness is tested by cotangent evaluation, rather
than an assumed smoothness certificate for the connection. -/
theorem derivative_pullSection_smooth (C : Connection B) (X : Field T) (s : Section B) :
    letI := P.space.topology
    SmoothSection P.space.bundle (fun q => pointDerivative C s.val (F q)
      (SmoothManifolds.differential T S F hF q (X.val q))) := by
  letI := P.space.topology
  classical
  intro q
  obtain ⟨k, hk⟩ := B.covers (F q)
  have ho : IsOpen (B.baseSet k) := B.trivialization_baseSet k ▸
    (B.trivialization k).open_baseSet
  let ω (i : Fin r) (p : M) : TangentSpace S p →ₗ[ℝ] ℝ :=
    if hp : p ∈ B.baseSet k then (LinearMap.proj i).comp
      ((B.fiberCoordinates k p hp).toLinearMap.comp (pointDerivative C s.val p)) else 0
  have hω (i : Fin r) : ManifoldSmoothOn S.smoothStructure.val
      (cotangentBundle S).totalManifold.smoothStructure.val
      (fun p => (⟨p, ω i p⟩ : Bundle.TotalSpace (Euclidean n)
        (fun p => Module.Dual ℝ (TangentSpace S p)))) (B.baseSet k) := by
    apply ConnectionForms.covector_smoothOn_of_evaluations (B.baseSet k)
    intro Y p hp
    have hc := (SmoothManifolds.SectionExtension.coordinates_smoothAt B k hp
      ((C.cov Y s).property p)).postcomp (contDiff_apply ℝ (fun _ : Fin r => ℝ) i)
    apply hc.congr
    filter_upwards [ho.mem_nhds hp] with z hz
    simp only [ω, dif_pos hz, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [ConnectionForms.pointDerivative_global B C]
    rfl
  let K : SmoothManifolds.BundleOperationsData.CotangentBundle S := {
    tangent := P202.MetricData.tangentStructure S
    realization := P202.MetricData.tangentRealization S
    dual := cotangentDual S }
  have heval (i : Fin r) : VectorSmoothAt T.smoothStructure.val
      (fun z => ω i (F z) (SmoothManifolds.differential T S F hF z (X.val z))) q := by
    apply SmoothManifolds.Covectors.evaluation_smoothAt T K F
      (fun z => ω i (F z))
      (fun z => SmoothManifolds.differential T S F hF z (X.val z)) q hF
    · exact SmoothManifolds.manifoldContDiffAt_comp S.smoothStructure.property.1.1
        (hF q) (hω i (F q) hk)
    · exact differential_field_smooth F hF X q
  apply SmoothManifolds.SectionExtension.smoothAt_of_coordinates P.space.bundle k
    (by rw [P.baseSet]; exact hk)
  apply (SmoothManifolds.FrameData.VectorSmoothAt.pi heval).congr
  filter_upwards [(hF q).1.preimage_mem_nhds (ho.mem_nhds hk)] with z hz
  rw [P.coordinates k z hz]
  funext i
  dsimp only [ω]
  rw [dif_pos (show F z ∈ B.baseSet k from hz)]
  rfl

/-- Scalar chain rule for a locally smooth representative, at any tangent
vector. Both sides use intrinsic germ differentials. -/
theorem scalar_chain_local (f : M → ℝ) (q : N)
    (hf : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val f (F q)) (v : TangentSpace T q) :
    scalarDerivative T (fun z => f (F z)) q v =
      scalarDerivative S f (F q) (SmoothManifolds.differential T S F hF q v) := by
  obtain ⟨g, hg, he⟩ := SmoothManifolds.exists_global_representative S (F q) f hf
  let g' : GlobalSmooth S := ⟨g, (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr hg⟩
  have heF : (pullScalar F hF g').val =ᶠ[𝓝 q] (fun z => f (F z)) :=
    (hF q).1.tendsto.eventually he
  rw [ConnectionForms.scalarDerivative_representative _ (pullScalar F hF g') q heF,
    ConnectionForms.scalarDerivative_representative f g' (F q) he]
  exact (SmoothManifolds.differential_spec T S F hF q v
    (SmoothManifolds.globalToGerm S (F q) g')
    (SmoothManifolds.globalToGerm T q (pullScalar F hF g')) g rfl rfl).symm

/-- Frame-change matrices pull back by composition, for arbitrary local frames
and arbitrary realizations of their pulled-back frames. -/
theorem transition_pullback {U : Set M} (hU : IsOpen U) (hV : IsOpen (F ⁻¹' U))
    (e e' : LocalFrame B U hU)
    : letI := P.space.topology
    ∀ (c c' : LocalFrame P.space.bundle (F ⁻¹' U) hV)
    (hc : ∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩)
    (hc' : ∀ j q, c'.section_ j q = e'.section_ j ⟨F q.val, q.property⟩)
    (q : F ⁻¹' U),
    localTransition c c' q = localTransition e e' ⟨F q.val, q.property⟩ := by
  letI := P.space.topology
  intro c c' hc hc' q
  have hb : c.basis q = e.basis ⟨F q.val, q.property⟩ := by
    ext j
    rw [c.basis_eq, e.basis_eq, hc j q]
  funext i j
  change (c.basis q).equivFun (c'.section_ j q) i = _
  rw [hb, hc' j q]
  rfl

/-- The chain rule for pulled-back frame changes: d(A∘F)=dA∘dF. -/
theorem transition_derivative_pullback {U : Set M} (hU : IsOpen U)
    (hV : IsOpen (F ⁻¹' U)) (e e' : LocalFrame B U hU)
    : letI := P.space.topology
    ∀ (c c' : LocalFrame P.space.bundle (F ⁻¹' U) hV)
    (hc : ∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩)
    (hc' : ∀ j q, c'.section_ j q = e'.section_ j ⟨F q.val, q.property⟩)
    (q : F ⁻¹' U) (v : TangentSpace T q.val),
    localTransitionDerivative c c' q v =
      localTransitionDerivative e e' ⟨F q.val, q.property⟩
        (SmoothManifolds.differential T S F hF q.val v) := by
  letI := P.space.topology
  intro c c' hc hc' q v
  funext i j
  let f := totalize (fun p : U => localTransition e e' p i j)
  have hf : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val f (F q.val) :=
    (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
      (SmoothManifolds.FrameData.VectorSmoothAt.totalize hU
        (ConnectionForms.localTransition_smooth B e e' i j ⟨F q.val, q.property⟩))
  obtain ⟨g, hg, hge⟩ := SmoothManifolds.exists_global_representative S (F q.val) f hf
  let g' : GlobalSmooth S := ⟨g, (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr hg⟩
  have he : (fun z => f (F z)) =ᶠ[𝓝 q.val]
      totalize (fun z : F ⁻¹' U => localTransition c c' z i j) := by
    filter_upwards [hV.mem_nhds q.property] with z hz
    rw [totalize_of_mem _ z hz]
    dsimp only [f]
    rw [totalize_of_mem _ (F z) hz, transition_pullback B F hF P hU hV e e' c c' hc hc']
  have hgF : (pullScalar F hF g').val =ᶠ[𝓝 q.val] (fun z => f (F z)) :=
    (hF q.val).1.tendsto.eventually hge
  change scalarDerivative T _ q.val v = scalarDerivative S f (F q.val) _
  rw [← scalarDerivative_congr (S := T) (fun z => f (F z)) _ q.val
    ⟨pullScalar F hF g', hgF⟩ he]
  exact scalar_chain_local F hF f q.val hf v

/-- The pulled-back matrices obey the gauge law. This is precisely the
compatibility used when gluing the local connection formulas. -/
theorem pulled_frame_transformation (C : Connection B) {U : Set M} (hU : IsOpen U)
    (hV : IsOpen (F ⁻¹' U)) (e e' : LocalFrame B U hU)
    : letI := P.space.topology
    ∀ (c c' : LocalFrame P.space.bundle (F ⁻¹' U) hV)
    (hc : ∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩)
    (hc' : ∀ j q, c'.section_ j q = e'.section_ j ⟨F q.val, q.property⟩)
    (q : F ⁻¹' U) (v : TangentSpace T q.val),
    connectionMatrix C e' ⟨F q.val, q.property⟩
        (SmoothManifolds.differential T S F hF q.val v) =
      localTransition c' c q * connectionMatrix C e ⟨F q.val, q.property⟩
          (SmoothManifolds.differential T S F hF q.val v) * localTransition c c' q +
        localTransition c' c q * localTransitionDerivative c c' q v := by
  letI := P.space.topology
  intro c c' hc hc' q v
  rw [transition_pullback B F hF P hU hV e' e c' c hc' hc,
    transition_pullback B F hF P hU hV e e' c c' hc hc',
    transition_derivative_pullback B F hF P hU hV e e' c c' hc hc']
  exact ConnectionForms.local_frame_transformation B C e e' _ _

/-- The universal rule determines the intrinsic derivative on all tangent
vectors, because every tangent value extends to a global smooth field. -/
theorem pointDerivative_pullSection (C : Connection B)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hD : P202.PullbackData.IsPullback B C F hF P D)
    (s : Section B) (q : N) (v : TangentSpace T q) :
    letI := P.space.topology
    pointDerivative D (pullSection B F hF P s).val q v =
      pointDerivative C s.val (F q) (SmoothManifolds.differential T S F hF q v) := by
  letI := P.space.topology
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle T) q v
  rw [← hX, ConnectionForms.pointDerivative_global P.space.bundle D]
  exact hD X s (pullSection B F hF P s) (fun _ => rfl) q

/-- Global source sections generate every smooth pullback-section germ.
The coefficients live on N; no rank condition on F is involved. -/
theorem section_germ_expansion (s : letI := P.space.topology; Section P.space.bundle)
    (q : N) :
    letI := P.space.topology
    ∃ (f : Fin r → GlobalSmooth T) (e : Fin r → Section B),
      ∀ᶠ z in 𝓝 q, s.val z =
        (∑ j, mulSection (f j) (pullSection B F hF P (e j))).val z := by
  letI := P.space.topology
  classical
  obtain ⟨U, hU, hq, ⟨e⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (F q)
  let V := F ⁻¹' U
  have hV : IsOpen V := hU.preimage
    (continuous_iff_continuousAt.mpr (fun z => (hF z).1))
  let c := pullFrame B F hF P hU e
  have hs := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    T.smoothStructure.val P.space.bundle.totalManifold.smoothStructure.val
    _ V hV).mp (fun z _ => s.property z)
  obtain ⟨f, hf⟩ := ConnectionForms.local_coefficients_representative P.space.bundle c
    (fun z => s.val z.val) hs ⟨q, hq⟩
  obtain ⟨t, ht⟩ := ConnectionForms.local_frame_representative B e ⟨F q, hq⟩
  refine ⟨f, t, ?_⟩
  have htF := (hF q).1.tendsto.eventually (Filter.eventually_all.mpr ht)
  filter_upwards [hV.mem_nhds hq, Filter.eventually_all.mpr hf, htF] with z hz hfz htz
  rw [SmoothManifolds.Frames.section_expansion P.space.bundle V hV c
    (fun z => s.val z.val) ⟨z, hz⟩]
  simp only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply,
    pullSection_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hfz j, htz j]
  simp only [SmoothManifolds.FrameData.totalize_of_mem _ z hz,
    SmoothManifolds.SectionExtension.totalSection_of_mem _ (F z) hz]
  rfl

/-- The finite Leibniz expression on an arbitrary expansion. -/
noncomputable def expansionValue (C : Connection B) {κ : Type*} [Fintype κ]
    (X : Field T) (f : κ → GlobalSmooth T) (s : κ → Section B) (q : N) : E (F q) :=
  ∑ j, ((act T X (f j)).val q • (s j).val (F q) +
    (f j).val q • pointDerivative C (s j).val (F q)
      (SmoothManifolds.differential T S F hF q (X.val q)))

/-- The finite Leibniz expression is independent of its expansion. -/
theorem expansionValue_eq (C : Connection B) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (X : Field T) (f : κ → GlobalSmooth T) (s : κ → Section B)
    (g : τ → GlobalSmooth T) (t : τ → Section B) (q : N)
    (he : ∀ᶠ z in 𝓝 q, ∑ j, (f j).val z • (s j).val (F z) =
      ∑ j, (g j).val z • (t j).val (F z)) :
    expansionValue B F hF C X f s q = expansionValue B F hF C X g t q := by
  classical
  have hz : ∀ᶠ z in 𝓝 q,
      ∑ j : κ ⊕ τ, (Sum.elim f (fun j => -(g j)) j).val z •
        (Sum.elim s t j).val (F z) = 0 := by
    filter_upwards [he] with z hz
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Subalgebra.coe_neg, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
      add_neg_eq_zero] using hz
  have hd := expansion_derivative_zero B F hF C X
    (Sum.elim f (fun j => -(g j))) (Sum.elim s t) q hz
  simpa only [expansionValue, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    map_neg, Subalgebra.coe_neg, Pi.neg_apply, neg_smul, ← neg_add,
    Finset.sum_neg_distrib, add_neg_eq_zero] using hd

/-- Choice of a finite germ expansion, with well-definedness supplied by the
preceding theorem. This is a value, not an assumed connection certificate. -/
noncomputable def derivativeValue (C : Connection B) (X : Field T)
    (s : letI := P.space.topology; Section P.space.bundle) (q : N) : E (F q) := by
  classical
  let h := section_germ_expansion B F hF P s q
  exact expansionValue B F hF C X (Classical.choose h)
    (Classical.choose (Classical.choose_spec h)) q

/-- Every finite local presentation computes the same derivative. -/
theorem derivativeValue_eq (C : Connection B) (X : Field T)
    (s : letI := P.space.topology; Section P.space.bundle) (q : N)
    {κ : Type*} [Fintype κ] (f : κ → GlobalSmooth T) (e : κ → Section B)
    (he : ∀ᶠ z in 𝓝 q, s.val z = ∑ j, (f j).val z • (e j).val (F z)) :
    derivativeValue B F hF P C X s q = expansionValue B F hF C X f e q := by
  classical
  apply expansionValue_eq B F hF C
  have h := Classical.choose_spec (Classical.choose_spec
    (section_germ_expansion B F hF P s q))
  filter_upwards [h, he] with z hz hz'
  simpa only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply,
    pullSection_apply] using hz.symm.trans hz'

theorem exists_expansion (s : letI := P.space.topology; Section P.space.bundle) (q : N) :
    ∃ (f : Fin r → GlobalSmooth T) (e : Fin r → Section B),
      ∀ᶠ z in 𝓝 q, s.val z = ∑ j, (f j).val z • (e j).val (F z) := by
  obtain ⟨f, e, he⟩ := section_germ_expansion B F hF P s q
  exact ⟨f, e, by simpa only [Submodule.coe_sum, Finset.sum_apply,
    ConnectionForms.mulSection_apply, pullSection_apply] using he⟩

theorem expansionValue_smooth (C : Connection B) {κ : Type*} [Fintype κ]
    (X : Field T) (f : κ → GlobalSmooth T) (e : κ → Section B) :
    letI := P.space.topology
    SmoothSection P.space.bundle (fun q => expansionValue B F hF C X f e q) := by
  letI := P.space.topology
  let d (j : κ) : Section P.space.bundle := ⟨_, derivative_pullSection_smooth B F hF P C X (e j)⟩
  let z : Section P.space.bundle := ∑ j,
    (mulSection (act T X (f j)) (pullSection B F hF P (e j)) + mulSection (f j) (d j))
  intro q
  simpa only [z, Submodule.coe_sum, Finset.sum_apply, ConnectionForms.section_add_apply,
    ConnectionForms.mulSection_apply, pullSection_apply, d, expansionValue] using z.property q

theorem derivativeValue_smooth (C : Connection B) (X : Field T)
    (s : letI := P.space.topology; Section P.space.bundle) :
    letI := P.space.topology
    SmoothSection P.space.bundle (fun q => derivativeValue B F hF P C X s q) := by
  letI := P.space.topology
  intro q
  obtain ⟨f, e, he⟩ := exists_expansion B F hF P s q
  apply SmoothManifolds.SectionExtension.section_smoothAt_congr P.space.bundle
    (expansionValue_smooth B F hF P C X f e q)
  filter_upwards [he.eventually_nhds] with z hz
  exact (derivativeValue_eq B F hF P C X s z f e hz).symm

omit hF in
@[simp] theorem act_add_field (X Y : Field T) (f : GlobalSmooth T) (q : N) :
    (act T (X + Y) f).val q = (act T X f).val q + (act T Y f).val q := rfl

omit hF in
@[simp] theorem act_smul_field (c : ℝ) (X : Field T) (f : GlobalSmooth T) (q : N) :
    (act T (c • X) f).val q = c * (act T X f).val q := rfl

omit hF in
@[simp] theorem act_mul_field (g : GlobalSmooth T) (X : Field T)
    (f : GlobalSmooth T) (q : N) :
    (act T (mulSection g X) f).val q = g.val q * (act T X f).val q := rfl

omit hF in
@[simp] theorem scalar_smul_apply (c : ℝ) (f : GlobalSmooth T) (q : N) :
    (c • f).val q = c * f.val q := rfl

omit hF in
@[simp] theorem scalar_mul_apply (f g : GlobalSmooth T) (q : N) :
    (f * g).val q = f.val q * g.val q := rfl

omit hF in
@[simp] theorem scalar_add_apply (f g : GlobalSmooth T) (q : N) :
    (f + g).val q = f.val q + g.val q := rfl

theorem expansionValue_add_field (C : Connection B) {κ : Type*} [Fintype κ]
    (X Y : Field T) (f : κ → GlobalSmooth T) (e : κ → Section B) (q : N) :
    expansionValue B F hF C (X + Y) f e q =
      expansionValue B F hF C X f e q + expansionValue B F hF C Y f e q := by
  simp only [expansionValue, act_add_field, ConnectionForms.section_add_apply, map_add,
    add_smul, smul_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  abel

theorem expansionValue_smul_field (C : Connection B) {κ : Type*} [Fintype κ]
    (c : ℝ) (X : Field T) (f : κ → GlobalSmooth T) (e : κ → Section B) (q : N) :
    expansionValue B F hF C (c • X) f e q = c • expansionValue B F hF C X f e q := by
  simp only [expansionValue, act_smul_field, ConnectionForms.section_smul_apply,
    map_smul, Finset.smul_sum, smul_add, smul_smul, mul_comm c]

theorem expansionValue_mul_field (C : Connection B) {κ : Type*} [Fintype κ]
    (g : GlobalSmooth T) (X : Field T) (f : κ → GlobalSmooth T)
    (e : κ → Section B) (q : N) :
    expansionValue B F hF C (mulSection g X) f e q =
      g.val q • expansionValue B F hF C X f e q := by
  simp only [expansionValue, act_mul_field, ConnectionForms.mulSection_apply,
    map_smul, Finset.smul_sum, smul_add, smul_smul, mul_comm (g.val q)]

omit hF in
@[simp] theorem act_mul_apply (X : Field T) (f g : GlobalSmooth T) (q : N) :
    (act T X (f * g)).val q =
      (act T X f).val q * g.val q + f.val q * (act T X g).val q := by
  have h := congrArg (fun z : GlobalSmooth T => z.val q) ((act T X).leibniz f g)
  simpa only [smul_eq_mul, scalar_add_apply, scalar_mul_apply, mul_comm, add_comm] using h

theorem expansionValue_mul_coefficients (C : Connection B) {κ : Type*} [Fintype κ]
    (X : Field T) (g : GlobalSmooth T) (f : κ → GlobalSmooth T)
    (e : κ → Section B) (q : N) :
    expansionValue B F hF C X (fun j => g * f j) e q =
      (act T X g).val q • (∑ j, (f j).val q • (e j).val (F q)) +
        g.val q • expansionValue B F hF C X f e q := by
  simp only [expansionValue, act_mul_apply, scalar_mul_apply,
    Finset.smul_sum, smul_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  module

theorem derivativeValue_add_field (C : Connection B) (X Y : Field T)
    (s : letI := P.space.topology; Section P.space.bundle) (q : N) :
    derivativeValue B F hF P C (X + Y) s q =
      derivativeValue B F hF P C X s q + derivativeValue B F hF P C Y s q := by
  obtain ⟨f, e, he⟩ := exists_expansion B F hF P s q
  simp only [derivativeValue_eq B F hF P C _ s q f e he,
    expansionValue_add_field]

theorem derivativeValue_smul_field (C : Connection B) (c : ℝ) (X : Field T)
    (s : letI := P.space.topology; Section P.space.bundle) (q : N) :
    derivativeValue B F hF P C (c • X) s q = c • derivativeValue B F hF P C X s q := by
  obtain ⟨f, e, he⟩ := exists_expansion B F hF P s q
  simp only [derivativeValue_eq B F hF P C _ s q f e he,
    expansionValue_smul_field]

theorem derivativeValue_mul_field (C : Connection B) (g : GlobalSmooth T) (X : Field T)
    (s : letI := P.space.topology; Section P.space.bundle) (q : N) :
    derivativeValue B F hF P C (mulSection g X) s q =
      g.val q • derivativeValue B F hF P C X s q := by
  obtain ⟨f, e, he⟩ := exists_expansion B F hF P s q
  simp only [derivativeValue_eq B F hF P C _ s q f e he,
    expansionValue_mul_field]

theorem derivativeValue_add_section (C : Connection B) (X : Field T)
    (s t : letI := P.space.topology; Section P.space.bundle) (q : N) :
    derivativeValue B F hF P C X (s + t) q =
      derivativeValue B F hF P C X s q + derivativeValue B F hF P C X t q := by
  obtain ⟨f, e, he⟩ := exists_expansion B F hF P s q
  obtain ⟨g, d, hd⟩ := exists_expansion B F hF P t q
  have hst : ∀ᶠ z in 𝓝 q, (s + t).val z =
      ∑ j : Fin r ⊕ Fin r, (Sum.elim f g j).val z • (Sum.elim e d j).val (F z) := by
    filter_upwards [he, hd] with z hz hz'
    simpa only [ConnectionForms.section_add_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr] using congrArg₂ (· + ·) hz hz'
  rw [derivativeValue_eq B F hF P C X (s + t) q _ _ hst,
    derivativeValue_eq B F hF P C X s q f e he,
    derivativeValue_eq B F hF P C X t q g d hd]
  simp only [expansionValue, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem derivativeValue_smul_section (C : Connection B) (X : Field T) (c : ℝ)
    (s : letI := P.space.topology; Section P.space.bundle) (q : N) :
    derivativeValue B F hF P C X (c • s) q = c • derivativeValue B F hF P C X s q := by
  obtain ⟨f, e, he⟩ := exists_expansion B F hF P s q
  have hcs : ∀ᶠ z in 𝓝 q, (c • s).val z = ∑ j, (c • f j).val z • (e j).val (F z) := by
    filter_upwards [he] with z hz
    simpa only [ConnectionForms.section_smul_apply, Finset.smul_sum, scalar_smul_apply,
      smul_smul] using congrArg (c • ·) hz
  rw [derivativeValue_eq B F hF P C X (c • s) q _ e hcs,
    derivativeValue_eq B F hF P C X s q f e he]
  simp only [expansionValue, Derivation.map_smul, scalar_smul_apply, Finset.smul_sum, smul_add, smul_smul]

theorem derivativeValue_leibniz (C : Connection B) (X : Field T) (g : GlobalSmooth T)
    (s : letI := P.space.topology; Section P.space.bundle) (q : N) :
    letI := P.space.topology
    derivativeValue B F hF P C X (mulSection g s) q =
      (act T X g).val q • s.val q + g.val q • derivativeValue B F hF P C X s q := by
  letI := P.space.topology
  obtain ⟨f, e, he⟩ := exists_expansion B F hF P s q
  have hgs : ∀ᶠ z in 𝓝 q, (mulSection g s).val z =
      ∑ j, (g * f j).val z • (e j).val (F z) := by
    filter_upwards [he] with z hz
    simpa only [ConnectionForms.mulSection_apply, Finset.smul_sum, scalar_mul_apply,
      smul_smul] using congrArg (g.val z • ·) hz
  rw [derivativeValue_eq B F hF P C X (mulSection g s) q _ e hgs,
    derivativeValue_eq B F hF P C X s q f e he,
    expansionValue_mul_coefficients, he.self_of_nhds]

/-- The constructed smooth connection, with all algebraic axioms proved. -/
noncomputable def pullback (C : Connection B) :
    letI := P.space.topology; Connection P.space.bundle := by
  letI := P.space.topology
  refine {
    cov := {
      toFun := fun X => {
        toFun := fun s => ⟨fun q => derivativeValue B F hF P C X s q,
          derivativeValue_smooth B F hF P C X s⟩
        map_add' := ?_
        map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
    linear_field := ?_
    leibniz := ?_ }
  · rename_i X
    intro s t
    apply ConnectionForms.section_ext
    intro q
    exact derivativeValue_add_section B F hF P C X s t q
  · rename_i X
    intro c s
    apply ConnectionForms.section_ext
    intro q
    exact derivativeValue_smul_section B F hF P C X c s q
  · intro X Y
    apply LinearMap.ext
    intro s
    apply ConnectionForms.section_ext
    intro q
    exact derivativeValue_add_field B F hF P C X Y s q
  · intro c X
    apply LinearMap.ext
    intro s
    apply ConnectionForms.section_ext
    intro q
    exact derivativeValue_smul_field B F hF P C c X s q
  · intro g X s
    apply ConnectionForms.section_ext
    intro q
    exact derivativeValue_mul_field B F hF P C g X s q
  · intro X g s
    apply ConnectionForms.section_ext
    intro q
    exact derivativeValue_leibniz B F hF P C X g s q

/-- Its universal rule holds on every pulled-back smooth section. -/
theorem pullback_isPullback (C : Connection B) :
    P202.PullbackData.IsPullback B C F hF P (pullback B F hF P C) := by
  letI := P.space.topology
  intro X s t ht q
  change derivativeValue B F hF P C X t q = _
  have he : ∀ᶠ z in 𝓝 q, t.val z =
      ∑ _j : Fin 1, (1 : GlobalSmooth T).val z • s.val (F z) := by
    simpa only [Fin.sum_univ_one, OneMemClass.coe_one, Pi.one_apply, one_smul]
      using Filter.Eventually.of_forall ht
  rw [derivativeValue_eq B F hF P C X t q (fun _ : Fin 1 => 1)
    (fun _ => s) he]
  simp only [expansionValue, ConnectionForms.act_one, Fin.sum_univ_one,
    ZeroMemClass.coe_zero, Pi.zero_apply, OneMemClass.coe_one, Pi.one_apply,
    zero_smul, one_smul, zero_add]

/-- The global universal rule extends to arbitrary local smooth sections. -/
theorem local_rule_of_isPullback (C : Connection B)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hD : P202.PullbackData.IsPullback B C F hF P D) :
    P202.PullbackData.LocalRule B C F hF P D := by
  letI := P.space.topology
  intro U hU hV s t X ht q
  obtain ⟨u, hu⟩ := ConnectionForms.exists_section_representative B U hU
    (SmoothManifolds.SectionExtension.totalSection s.val)
    (SmoothManifolds.SectionExtension.totalSection_smooth B hU _ s.property)
    (F q.val) q.property
  have hpull : ∀ᶠ z in 𝓝 q.val, (pullSection B F hF P u).val z =
      SmoothManifolds.SectionExtension.totalSection (E := fun p => E (F p)) t.val z := by
    filter_upwards [(hF q.val).1.tendsto.eventually hu,
      hV.mem_nhds q.property] with z hz hzV
    rw [pullSection_apply, hz,
      SmoothManifolds.SectionExtension.totalSection_of_mem s.val (F z) hzV,
      SmoothManifolds.SectionExtension.totalSection_of_mem (E := fun p => E (F p)) t.val z hzV,
      ht ⟨z, hzV⟩]
  have htD := ConnectionForms.pointDerivative_congr P.space.bundle D
    (pullSection B F hF P u).val
    (SmoothManifolds.SectionExtension.totalSection (E := fun p => E (F p)) t.val)
    q.val ⟨pullSection B F hF P u, Filter.Eventually.of_forall (fun _ => rfl)⟩ hpull
  have hsD := ConnectionForms.pointDerivative_congr B C u.val
    (SmoothManifolds.SectionExtension.totalSection s.val) (F q.val)
    ⟨u, Filter.Eventually.of_forall (fun _ => rfl)⟩ hu
  calc
    _ = _ := ConnectionForms.covOn_pointDerivative P.space.bundle D X t q
    _ = _ := congrArg (fun L : TangentSpace T q.val →ₗ[ℝ] E (F q.val) => L (X.val q)) htD.symm
    _ = _ := pointDerivative_pullSection B F hF P C D hD u q.val (X.val q)
    _ = _ := congrArg (fun L : TangentSpace S (F q.val) →ₗ[ℝ] E (F q.val) =>
      L (SmoothManifolds.differential T S F hF q.val (X.val q))) hsD

/-- The connection's actual one-form matrix is the pulled-back matrix in every
pulled-back local frame, not only in the original bundle atlas. -/
theorem frame_rule_of_isPullback (C : Connection B)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hD : P202.PullbackData.IsPullback B C F hF P D) :
    P202.PullbackData.FrameRule B C F hF P D := by
  letI := P.space.topology
  intro U hU hV e c hc q v i j
  obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle T) q.val v
  have hb : c.basis q = e.basis ⟨F q.val, q.property⟩ := by
    ext k
    rw [c.basis_eq, e.basis_eq, hc k q]
  rw [← hY]
  have he := ConnectionForms.connectionForm_characterization P.space.bundle D c
    (restrictGlobalSection Y (F ⁻¹' U) hV) q i j
  change connectionForm D c q i j (Y.val q.val) = _ at he
  have hl := local_rule_of_isPullback B F hF P C D hD U hU hV
    (⟨e.section_ j, e.smooth j⟩ : LocalSection B U hU)
    (⟨c.section_ j, c.smooth j⟩ : LocalSection P.space.bundle (F ⁻¹' U) hV)
    (restrictGlobalSection Y (F ⁻¹' U) hV) (hc j) q
  calc
    _ = _ := he
    _ = _ := congrArg (fun z : E (F q.val) => (c.basis q).equivFun z i) hl
    _ = _ := by rw [hb]; rfl

/-- Uniqueness among all connections on the actual pullback bundle follows
from locality, Leibniz and the differentiation rule on pulled-back sections. -/
theorem uniqueness (C : Connection B)
    (D D' : letI := P.space.topology; Connection P.space.bundle)
    (hD : P202.PullbackData.IsPullback B C F hF P D)
    (hD' : P202.PullbackData.IsPullback B C F hF P D') : D = D' := by
  letI := P.space.topology
  have hcov : D.cov = D'.cov := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro s
    apply ConnectionForms.section_ext
    intro q
    obtain ⟨f, e, he⟩ := section_germ_expansion B F hF P s q
    rw [ConnectionForms.locality_section P.space.bundle D X s _ q he,
      ConnectionForms.locality_section P.space.bundle D' X s _ q he,
      ConnectionForms.finite_expansion P.space.bundle D,
      ConnectionForms.finite_expansion P.space.bundle D']
    simp only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.section_add_apply,
      ConnectionForms.mulSection_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hD X (e j) (pullSection B F hF P (e j)) (fun _ => rfl) q,
      hD' X (e j) (pullSection B F hF P (e j)) (fun _ => rfl) q]
  cases D
  cases D'
  cases hcov
  rfl

/-- Existence, the global and local universal properties, the frame formula,
and uniqueness all hold on any realization with the prescribed pullback atlas. -/
theorem exists_unique (C : Connection B) :
    letI := P.space.topology
    ∃ D : Connection P.space.bundle,
      P202.PullbackData.IsPullback B C F hF P D ∧
      P202.PullbackData.LocalRule B C F hF P D ∧
      P202.PullbackData.FrameRule B C F hF P D ∧
      ∀ D' : Connection P.space.bundle,
        P202.PullbackData.IsPullback B C F hF P D' → D' = D := by
  letI := P.space.topology
  let D := pullback B F hF P C
  have hD := pullback_isPullback B F hF P C
  refine ⟨D, hD, local_rule_of_isPullback B F hF P C D hD,
    frame_rule_of_isPullback B F hF P C D hD, ?_⟩
  intro D' hD'
  exact uniqueness B F hF P C D' D hD' hD

/-- Every local recipe is the intrinsic derivative of the constructed
connection. In particular no frame choice enters the resulting section. -/
theorem local_formula_correct (C : Connection B)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hD : P202.PullbackData.IsPullback B C F hF P D)
    (U : Set M) (hU : IsOpen U) (hV : IsOpen (F ⁻¹' U))
    (e : LocalFrame B U hU) :
    letI := P.space.topology
    ∀ (c : LocalFrame P.space.bundle (F ⁻¹' U) hV),
      (∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩) →
      ∀ (s : LocalSection P.space.bundle (F ⁻¹' U) hV)
        (q : F ⁻¹' U) (v : TangentSpace T q.val),
      pointDerivative D (SmoothManifolds.SectionExtension.totalSection s.val) q.val v =
        P202.PullbackData.localFormula B C F hF P U hU hV e c s q v := by
  letI := P.space.topology
  intro c hc s q v
  apply (c.basis q).equivFun.injective
  funext i
  change _ = ((c.basis q).equivFun ((c.basis q).equivFun.symm _)) i
  rw [LinearEquiv.apply_symm_apply]
  calc
    _ = _ := ConnectionForms.local_frame_formula P.space.bundle D c s q v i
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [frame_rule_of_isPullback B F hF P C D hD U hU hV e c hc q v i j]

/-- Gluing holds in the actual fiber, for all local sections and all tangent
vectors. Restricting frames to intersections gives the overlap version. -/
theorem local_formulas_agree (C : Connection B)
    (U : Set M) (hU : IsOpen U) (hV : IsOpen (F ⁻¹' U)) (e e' : LocalFrame B U hU) :
    letI := P.space.topology
    ∀ (c c' : LocalFrame P.space.bundle (F ⁻¹' U) hV),
      (∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩) →
      (∀ j q, c'.section_ j q = e'.section_ j ⟨F q.val, q.property⟩) →
      ∀ (s : LocalSection P.space.bundle (F ⁻¹' U) hV)
        (q : F ⁻¹' U) (v : TangentSpace T q.val),
      P202.PullbackData.localFormula B C F hF P U hU hV e c s q v =
        P202.PullbackData.localFormula B C F hF P U hU hV e' c' s q v := by
  letI := P.space.topology
  intro c c' hc hc' s q v
  have hD := pullback_isPullback B F hF P C
  exact (local_formula_correct B F hF P C _ hD U hU hV e c hc s q v).symm.trans
    (local_formula_correct B F hF P C _ hD U hU hV e' c' hc' s q v)

/-- Combined frame-change interface, including composition, chain rule and
the gauge compatibility of the pulled-back connection matrices. -/
theorem frame_change (C : Connection B)
    (U : Set M) (hU : IsOpen U) (hV : IsOpen (F ⁻¹' U)) (e e' : LocalFrame B U hU) :
    letI := P.space.topology
    ∀ (c c' : LocalFrame P.space.bundle (F ⁻¹' U) hV),
      (∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩) →
      (∀ j q, c'.section_ j q = e'.section_ j ⟨F q.val, q.property⟩) →
      ∀ (q : F ⁻¹' U) (v : TangentSpace T q.val),
      localTransition c c' q = localTransition e e' ⟨F q.val, q.property⟩ ∧
      localTransitionDerivative c c' q v =
        localTransitionDerivative e e' ⟨F q.val, q.property⟩
          (SmoothManifolds.differential T S F hF q.val v) ∧
      connectionMatrix C e' ⟨F q.val, q.property⟩
          (SmoothManifolds.differential T S F hF q.val v) =
        localTransition c' c q * connectionMatrix C e ⟨F q.val, q.property⟩
            (SmoothManifolds.differential T S F hF q.val v) * localTransition c c' q +
          localTransition c' c q * localTransitionDerivative c c' q v := by
  letI := P.space.topology
  intro c c' hc hc' q v
  exact ⟨transition_pullback B F hF P hU hV e e' c c' hc hc' q,
    transition_derivative_pullback B F hF P hU hV e e' c c' hc hc' q v,
    pulled_frame_transformation B F hF P C hU hV e e' c c' hc hc' q v⟩

/-- The canonical choice needs only B, its arbitrary connection and F. -/
noncomputable def canonicalConnection (C : Connection B) :
    let P := P202.PullbackData.bundle B T F hF
    letI := P.space.topology
    Connection P.space.bundle :=
  pullback B F hF (P202.PullbackData.bundle B T F hF) C

end PullbackSections
theorem pullback_exists_unique :
    P202Specs.Geometry.PullbackConnections.exists_uniqueType.{u,v,w} := by
  intro n m r a b M N _ _ S T ι E _ _ _ B C F hF P
  exact exists_unique B F hF P C

theorem pullback_unique :
    P202Specs.Geometry.PullbackConnections.uniquenessType.{u,v,w} := by
  intro n m r a b M N _ _ S T ι E _ _ _ B C F hF P
  exact uniqueness B F hF P C

theorem pullback_frame_change :
    P202Specs.Geometry.PullbackConnections.frame_changeType.{u,v,w} := by
  intro n m r a b M N _ _ S T ι E _ _ _ B C F hF P U hU hV e e'
  exact frame_change B F hF P C U hU hV e e'

theorem pullback_local_formulas_agree :
    P202Specs.Geometry.PullbackConnections.local_formulas_agreeType.{u,v,w} := by
  intro n m r a b M N _ _ S T ι E _ _ _ B C F hF P U hU hV e e'
  exact local_formulas_agree B F hF P C U hU hV e e'

theorem canonical_pullback_exists_unique :
    P202Specs.Geometry.PullbackConnections.canonical_exists_uniqueType.{u,v,w} := by
  intro n m r a b M N _ _ S T ι E _ _ _ B C F hF
  exact exists_unique B F hF (P202.PullbackData.bundle B T F hF) C

theorem pullback_frame_exists :
    P202Specs.Geometry.PullbackConnections.frame_existsType.{u,v,w} := by
  intro n m r a b M N _ _ S T ι E _ _ _ B F hF P U hU e
  exact ⟨pullFrame B F hF P hU e, fun _ _ => rfl⟩

end P202.Geometry.PullbackConnections
