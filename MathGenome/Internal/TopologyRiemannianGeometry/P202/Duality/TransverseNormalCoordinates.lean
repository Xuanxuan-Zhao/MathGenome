import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.TransverseNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.ThomClass
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
open Filter Set
open scoped Topology
universe u
namespace P202.TransverseNormalCoordinates
open P202Specs.TransverseNormalCoordinates
attribute [local instance] normalTopology

variable {n k : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

lemma normalFiber_dimension (A : EmbeddedData S) (p : A.source) :
    FiniteDimensional ℝ (NormalFiber A.normal p) ∧
      Module.finrank ℝ (NormalFiber A.normal p) = n - A.dimension := by
  obtain ⟨a, ha⟩ := (normalBundle A.normal).covers p
  let e := P202Specs.ThomClass.fiberLinearCoordinates A.normal a p ha
  exact ⟨Module.Finite.equiv e.symm, by rw [e.finrank_eq]; simp [Euclidean]⟩

/-- Surjectivity of the full normal projection bounds the sum of codimensions;
no transversality of a subfamily away from this common point is used. -/
theorem codimensionBound : codimensionBound_type.{u} := by
  intro n k M _ S F x p h hsurj
  cases k with
  | zero => simp [totalCodimension]
  | succ k =>
    obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 x
    let e := (F 0).normal.ambientTangent.fiberCoordinates.equiv c hc x hxc
    letI : FiniteDimensional ℝ (TangentSpace S x) := Module.Finite.equiv e.symm
    letI : ∀ j : Fin (k+1), FiniteDimensional ℝ (NormalFiber (F j).normal (p j)) :=
      fun j => (normalFiber_dimension (F j) (p j)).1
    have hdim := LinearMap.finrank_le_finrank_of_surjective hsurj
    rw [Module.finrank_pi_fintype, e.finrank_eq] at hdim
    have heq : (∑ j : Fin (k+1), Module.finrank ℝ (NormalFiber (F j).normal (p j))) =
        totalCodimension F :=
      Finset.sum_congr rfl (fun j _ => (normalFiber_dimension (F j) (p j)).2)
    rw [heq] at hdim
    simpa [Euclidean] using hdim

attribute [local instance] normalTopology

/-- A normalized tube has its quotient-normal full derivative in any prescribed
ambient chart. The horizontal part is killed by the genuine quotient map. -/
theorem full_derivative_in_chart
    {m : ℕ} {P : Type u} [TopologicalSpace P]
    {T : SmoothManifold m .euclidean P} {i : P → M}
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i)
    (K : TubularNeighborhood N) (hK : P202Specs.ThomClass.NormalCompatible N K)
    (F : NormalTotal N → M)
    (hF : ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
      S.smoothStructure.val F K.domain)
    (heF : ∀ z (hz : z ∈ K.domain), F z = (K.homeomorph ⟨z, hz⟩).val)
    (p a : P) (hp : p ∈ (normalBundle N).baseSet a)
    (c : ModelChart m .euclidean P) (hc : c ∈ T.smoothStructure.val)
    (hpc : p ∈ c.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hip : i p ∈ d.source) :
    ∃ J : Euclidean (m + (n-m)) →L[ℝ] Euclidean n,
      SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative
        (bundleChart (normalBundle N).coordinates ((normalBundle N).trivialization a) c)
        (fun z => (d (F z)).val) (normalZero N p) J ∧
      ∀ (b : Euclidean m) (v : Euclidean (n-m)),
        (LinearMap.range (N.differential p)).mkQ
          ((N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip).symm
            (J ((normalBundle N).coordinates.linearEquiv (b, v)))) =
              (P202Specs.ThomClass.fiberLinearCoordinates N a p hp).symm v := by
  let B := normalBundle N
  obtain ⟨L, hL, hn⟩ := P202.ThomClass.normalCompatible_fiber_derivative_in_charts
    N K hK F hF heF p a hp d hd hip
  have hzero : ∀ q : P, F (normalZero N q) = i q :=
    fun q => (heF _ (K.zero_mem q)).trans (K.zero_eq q)
  have hFp : F (normalZero N p) ∈ d.source := by rw [hzero p]; exact hip
  have hAt := SmoothManifolds.TubularLocalGeometry.smoothAt_target_chart _ _ F (normalZero N p)
    (hF _ (K.zero_mem p)) d hd hFp
  obtain ⟨J, hJ, hblocks⟩ := SmoothManifolds.TubularLocalGeometry.bundle_derivative_at_zero B
    (fun z => (d (F z)).val) (fun q => (d (i q)).val) p a hp c hc hpc
    hAt (fun q => congrArg (fun y => (d y).val) (hzero q)) L hL
  refine ⟨J, hJ, ?_⟩
  let C := N.sourceTangent.fiberCoordinates.equiv c hc p hpc
  let E := N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip
  have hhorizontal (b : Euclidean m) :
      E.symm (SmoothManifolds.FiniteRegularityData.chartDerivative c d i p b) =
        N.differential p (C.symm b) := by
    have hj := SmoothManifolds.FiniteRegularity.smooth_jacobian_coordinateDerivative T S i hi.1 p
      (N.differential p) (N.isDifferential p) c d hc hd hpc hip C E
      (N.sourceTangent.fiberCoordinates.isCoordinates c hc p hpc)
      (N.ambientTangent.fiberCoordinates.isCoordinates d hd (i p) hip) (C.symm b)
    apply E.injective
    simpa only [LinearEquiv.apply_symm_apply] using hj.symm
  intro b v
  have hj := congrArg (fun A => A (b, v)) hblocks
  change J (B.coordinates.linearEquiv (b, v)) =
    SmoothManifolds.FiniteRegularityData.chartDerivative c d i p b + L v at hj
  rw [hj, map_add, map_add, hhorizontal]
  have hqzero : (LinearMap.range (N.differential p)).mkQ (N.differential p (C.symm b)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)
  rw [hqzero, zero_add]
  exact hn v

/-- The normal component of the inverse full tubular differential is the
original quotient projection, in the chosen original fiber chart. -/
theorem inverse_normal_derivative
    {B V A C Q : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [AddCommGroup Q] [Module ℝ Q]
    (coord : (B × V) ≃L[ℝ] A) (quot : C →ₗ[ℝ] Q) (fiber : Q ≃ₗ[ℝ] V)
    (J : A →L[ℝ] C) (I : C →L[ℝ] A)
    (hJI : J.comp I = ContinuousLinearMap.id ℝ C)
    (hJ : ∀ b v, quot (J (coord (b, v))) = fiber.symm v) :
    ∀ w, (coord.symm (I w)).2 = fiber (quot w) := by
  intro w
  have hh := hJ (coord.symm (I w)).1 (coord.symm (I w)).2
  rw [Prod.eta, coord.apply_symm_apply] at hh
  have hi : J (I w) = w := congrArg (fun A => A w) hJI
  rw [hi] at hh
  have hv := congrArg fiber hh
  simpa only [LinearEquiv.apply_symm_apply] using hv.symm

section LocalEquations
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false

/-- A local smooth normal equation in any original ambient chart, with the
actual quotient differential. The target fiber coordinates are not changed. -/
theorem local_normal_equation (A : EmbeddedData S) (p : A.source)
    (x : M) (h : A.inclusion p = x)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hxd : x ∈ d.source) (C : TangentSpace S x ≃ₗ[ℝ] Euclidean n)
    (hC : IsChartCoordinates S x d C) :
    ∃ (a : A.source) (hp : p ∈ (normalBundle A.normal).baseSet a)
      (O : Set (Euclidean n)) (f : Euclidean n → Euclidean (n-A.dimension))
      (D : Euclidean n →L[ℝ] Euclidean (n-A.dimension)) (U : Set M),
      IsOpen O ∧ (d x).val ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) f O ∧
      HasFDerivAt f D (d x).val ∧
      (∀ v, D (C v) = P202Specs.ThomClass.fiberLinearCoordinates A.normal a p hp
        (normalProjection A p x h v)) ∧
      IsOpen U ∧ x ∈ U ∧ U ⊆ d.source ∧
      (∀ y ∈ U, (d y).val ∈ O ∧ (y ∈ Set.range A.inclusion ↔ f (d y).val = 0)) := by
  subst x
  let N := A.normal
  let B := normalBundle N
  obtain ⟨K, hK⟩ := P202.ThomClass.normalized_tubular_exists A.embedding N
  obtain ⟨F, G, hF, hG, heF, heG⟩ := P202.ThomClass.tubular_smoothRepresentatives N K p
  obtain ⟨a, hp⟩ := B.covers p
  obtain ⟨c, hc, hpc⟩ := A.manifold.smoothStructure.property.1.1 p
  let b := bundleChart B.coordinates (B.trivialization a) c
  have hb : b ∈ B.totalManifold.smoothStructure.val := B.chart_mem a c hc
  have hpbase : p ∈ (B.trivialization a).baseSet := (B.trivialization_baseSet a).symm ▸ hp
  have hzb : normalZero N p ∈ b.source :=
    (mem_bundleChart_source _ _ _ _).mpr ⟨hpbase, hpc⟩
  have hiK : A.inclusion p ∈ K.target := K.inclusion_mem ⟨p, rfl⟩
  have hGzero : G (A.inclusion p) = normalZero N p := by
    rw [heG _ hiK]
    have he : (⟨A.inclusion p, hiK⟩ : K.target) =
        K.homeomorph ⟨normalZero N p, K.zero_mem p⟩ := Subtype.ext (K.zero_eq p).symm
    rw [he, K.homeomorph.symm_apply_apply]
  have hbG : G (A.inclusion p) ∈ b.source := hGzero.symm ▸ hzb
  obtain ⟨O, hO, haO, H, hH, heH⟩ := (hG _ hiK).2 d hd b hb hxd hbG
  let I : Euclidean n →L[ℝ] Euclidean (A.dimension+(n-A.dimension)) :=
    fderiv ℝ H (d (A.inclusion p)).val
  have hI : SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative d
      (fun y => (b (G y)).val) (A.inclusion p) I :=
    ⟨H, (hH.contDiffAt (hO.mem_nhds haO)).differentiableAt (by simp) |>.hasFDerivAt, heH⟩
  obtain ⟨J, hJ, hnJ⟩ := full_derivative_in_chart A.embedding N K hK F hF heF
    p a hp c hc hpc d hd hxd
  have hFG : ∀ᶠ y in 𝓝 (A.inclusion p), F (G y) = y := by
    filter_upwards [K.isOpen_target.mem_nhds hiK] with y hy
    rw [heG y hy, heF _ (K.homeomorph.symm ⟨y, hy⟩).property]
    exact congrArg Subtype.val (K.homeomorph.apply_symm_apply ⟨y, hy⟩)
  have hJI := P202.ThomClass.coordinate_inverse_derivative b d F G
    (normalZero N p) (A.inclusion p) hxd hGzero (hG _ hiK).1 hFG J I hJ hI
  let R : Euclidean (A.dimension+(n-A.dimension)) →L[ℝ] Euclidean (n-A.dimension) :=
    (ContinuousLinearMap.snd ℝ _ _).comp B.coordinates.linearEquiv.symm.toContinuousLinearMap
  let f := R ∘ H
  let D := R.comp I
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f O := R.contDiff.comp_contDiffOn hH
  have hD : HasFDerivAt f D (d (A.inclusion p)).val :=
    R.hasFDerivAt.comp _ ((hH.contDiffAt (hO.mem_nhds haO)).differentiableAt (by simp)).hasFDerivAt
  let E := N.ambientTangent.fiberCoordinates.equiv d hd (A.inclusion p) hxd
  have hEC : E = C := SmoothManifolds.TangentBundle.chartCoordinates_unique
    (N.ambientTangent.fiberCoordinates.isCoordinates d hd (A.inclusion p) hxd) hC
  have hnormal (v : TangentSpace S (A.inclusion p)) :
      D (C v) = P202Specs.ThomClass.fiberLinearCoordinates N a p hp
        (normalProjection A p (A.inclusion p) rfl v) := by
    have hproj : normalProjection A p (A.inclusion p) rfl v =
        (N.differential p).range.mkQ v := rfl
    rw [hproj, ← hEC]
    dsimp only [D, R, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    apply (P202Specs.ThomClass.fiberLinearCoordinates N a p hp).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    have hh := hnJ (B.coordinates.linearEquiv.symm (I (E v))).1
      (B.coordinates.linearEquiv.symm (I (E v))).2
    rw [Prod.eta, B.coordinates.linearEquiv.apply_symm_apply] at hh
    have hi : J (I (E v)) = E v := congrArg (fun A => A (E v)) hJI
    rw [hi, LinearEquiv.symm_apply_apply] at hh
    exact hh.symm
  have hnear : ∀ᶠ y in 𝓝 (A.inclusion p),
      y ∈ K.target ∧ G y ∈ b.source ∧ y ∈ d.source ∧ (d y).val ∈ O ∧
        H (d y).val = (b (G y)).val := by
    have hGb := (hG _ hiK).1 (b.open_source.mem_nhds hbG)
    have hdc := continuous_subtype_val.continuousAt.comp (d.continuousAt hxd)
    filter_upwards [K.isOpen_target.mem_nhds hiK, hGb, d.open_source.mem_nhds hxd,
      hdc (hO.mem_nhds haO), heH] with y hy hyb hyd hyO hyH
    exact ⟨hy, hyb, hyd, hyO, hyH⟩
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  refine ⟨a, hp, O, f, D, U, hO, haO, hf, hD, hnormal, hU, hxU,
    fun y hy => (hUsub hy).2.2.1, ?_⟩
  intro y hy
  obtain ⟨hyK, hyb, hyd, hyO, hyH⟩ := hUsub hy
  refine ⟨hyO, ?_⟩
  have hzbase := (mem_bundleChart_source B.coordinates (B.trivialization a) c (G y)).mp hyb
  have hbase : (G y).proj ∈ B.baseSet a := (B.trivialization_baseSet a) ▸ hzbase.1
  have hfval : f (d y).val =
      P202Specs.ThomClass.fiberLinearCoordinates N a (G y).proj hbase (G y).snd := by
    change R (H (d y).val) = _
    rw [hyH, bundleChart_val B.coordinates (B.trivialization a) c (G y) hzbase.1]
    change (B.coordinates.linearEquiv.symm (B.coordinates.linearEquiv _)).2 = _
    rw [B.coordinates.linearEquiv.symm_apply_apply]
    rfl
  have hzero : f (d y).val = 0 ↔ G y = normalZero N (G y).proj := by
    rw [hfval, LinearEquiv.map_eq_zero_iff]
    constructor
    · intro hz
      exact congrArg (Bundle.TotalSpace.mk (G y).proj) hz
    · intro hz
      exact Bundle.TotalSpace.mk_injective (G y).proj hz
  have hGy : G y ∈ K.domain := by rw [heG y hyK]; exact (K.homeomorph.symm ⟨y, hyK⟩).property
  have hFy : (K.homeomorph ⟨G y, hGy⟩).val = y := by
    have he : (⟨G y, hGy⟩ : K.domain) = K.homeomorph.symm ⟨y, hyK⟩ :=
      Subtype.ext (heG y hyK)
    rw [he, K.homeomorph.apply_symm_apply]
  have hh := P202Specs.ThomClass.tubular_mem_range_iff N K (G y).proj
    (⟨G y, rfl, hGy⟩ : P202Specs.ThomClass.Slice N K (G y).proj)
  rw [hFy] at hh
  exact hh.trans hzero.symm

end LocalEquations

section SmoothSubmersion
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Smooth submersion coordinates retain the original target without any
change of its coordinate blocks. Smoothness holds on actual open neighborhoods. -/
theorem smooth_submersion_chart (f : E → V) (L : E →L[ℝ] V)
    (a : E) (O : Set E) (hO : IsOpen O) (ha : a ∈ O)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (hd : HasFDerivAt f L a)
    (hL : Function.Surjective L) :
    ∃ e : OpenPartialHomeomorph E (V × L.ker),
      a ∈ e.source ∧ e.source ⊆ O ∧ e a = (f a, 0) ∧
      (∀ z, (e z).1 = f z) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hL' : L.range = ⊤ := LinearMap.range_eq_top.mpr hL
  let hk := L.ker_closedComplemented_of_finiteDimensional_range
  let P : E →L[ℝ] L.ker := Classical.choose hk
  have hP : ∀ z : L.ker, P z = z := Classical.choose_spec hk
  let g : E → V × L.ker := fun z => (f z, P (z-a))
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g O :=
    hf.prodMk (P.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn
  let A : E ≃L[ℝ] V × L.ker :=
    L.equivProdOfSurjectiveOfIsCompl P hL' (LinearMap.range_eq_of_proj hP)
      (LinearMap.isCompl_of_proj hP)
  have hgd : HasFDerivAt g (A : E →L[ℝ] V × L.ker) a :=
    hd.prodMk (P.hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const a))
  let e₀ := (hg.contDiffAt (hO.mem_nhds ha)).toOpenPartialHomeomorph g hgd (by simp)
  have hbase : a ∈ e₀.source :=
    (hg.contDiffAt (hO.mem_nhds ha)).mem_toOpenPartialHomeomorph_source hgd (by simp)
  have hnear : ∀ᶠ z in 𝓝 a, (fderiv ℝ g z).IsInvertible := by
    have hc := (hg.continuousOn_fderiv_of_isOpen hO (by simp) a ha).continuousAt
      (hO.mem_nhds ha)
    have hh : (fderiv ℝ g a).IsInvertible := by
      rw [hgd.fderiv]
      exact ⟨A, rfl⟩
    exact hc.tendsto hh.eventually_nhds
  obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hO.mem_nhds ha) hnear)
  let e := e₀.restrOpen W hW
  refine ⟨e, ⟨hbase, haW⟩, fun z hz => (hWsub hz.2).1, ?_,
    fun _ => rfl, hg.mono (fun z hz => (hWsub hz.2).1), ?_⟩
  · change (f a, P (a-a)) = (f a, 0)
    simp
  · intro y hy
    have hx := e.map_target hy
    have hxO := (hWsub hx.2).1
    obtain ⟨B, hB⟩ := (hWsub hx.2).2
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy (f₀' := B)
    · change HasFDerivAt g (B : E →L[ℝ] V × L.ker) (e.symm y)
      rw [hB]
      exact (hg.contDiffAt (hO.mem_nhds hxO)).differentiableAt (by simp) |>.hasFDerivAt
    · exact hg.contDiffAt (hO.mem_nhds hxO)

/-- A smooth local right inverse, with normalized derivative, obtained from
submersion coordinates. This includes a zero-dimensional target. -/
theorem smooth_local_section (f : E → V) (L : E →L[ℝ] V)
    (a : E) (O : Set E) (hO : IsOpen O) (ha : a ∈ O)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (hd : HasFDerivAt f L a)
    (hL : Function.Surjective L) :
    ∃ U : Set V, IsOpen U ∧ f a ∈ U ∧ ∃ s : V → E,
      ContDiffOn ℝ (⊤ : ℕ∞) s U ∧ ContinuousOn s U ∧ s (f a) = a ∧
      (∀ y ∈ U, s y ∈ O ∧ f (s y) = y) ∧ Set.InjOn s U ∧
      L.comp (fderiv ℝ s (f a)) = ContinuousLinearMap.id ℝ V := by
  obtain ⟨e, haE, heO, hea, hef, hes, hei⟩ :=
    smooth_submersion_chart f L a O hO ha hf hd hL
  let j : V → V × L.ker := fun y => (y, 0)
  have hj : ContDiff ℝ (⊤ : ℕ∞) j := contDiff_id.prodMk contDiff_const
  let U := j ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage hj.continuous
  have hfa : f a ∈ U := by
    change (f a, 0) ∈ e.target
    rw [← hea]
    exact e.map_source haE
  let s : V → E := e.symm ∘ j
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) s U :=
    hei.comp hj.contDiffOn (fun _ hy => hy)
  have hsa : s (f a) = a := by
    change e.symm (f a, 0) = a
    rw [← hea, e.left_inv haE]
  have hfs (y : V) (hy : y ∈ U) : f (s y) = y := by
    rw [← hef]
    exact congrArg Prod.fst (e.right_inv hy)
  refine ⟨U, hU, hfa, s, hs, hs.continuousOn, hsa,
    fun y hy => ⟨heO (e.map_target hy), hfs y hy⟩, ?_, ?_⟩
  · intro y hy z hz heq
    exact (hfs y hy).symm.trans ((congrArg f heq).trans (hfs z hz))
  · have hds := (hs.contDiffAt (hU.mem_nhds hfa)).differentiableAt (by simp)
    have hcomp := (show HasFDerivAt f L (s (f a)) by rwa [hsa]).comp (f a) hds.hasFDerivAt
    have heq : (fun y => f (s y)) =ᶠ[𝓝 (f a)] id := by
      filter_upwards [hU.mem_nhds hfa] with y hy
      exact hfs y hy
    exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id (f a))
end SmoothSubmersion

lemma euclideanChart_apply (c : ModelChart n .euclidean M) (y : M) :
    euclideanChart c y = (c y).val := rfl

lemma euclideanChart_source (c : ModelChart n .euclidean M) :
    (euclideanChart c).source = c.source := by
  ext y
  simp [euclideanChart, OpenPartialHomeomorph.trans_source]

/-- Simultaneous smooth normal blocks and their normalized smooth slice. -/
theorem simultaneousCoordinates : simultaneousCoordinates_type.{u} := by
  intro n k M _ S F x p h hsurj
  classical
  obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 x
  obtain ⟨TC⟩ := SmoothManifolds.TangentBundle.fiberCoordinates_exists S
  let C := TC.equiv c hc x hxc
  have hC := TC.isCoordinates c hc x hxc
  choose a hp O f D U hO haO hf hd hn hU hxU hUc hEq using
    (fun j => local_normal_equation (F j) (p j) x (h j) c hc hxc C hC)
  let χ : Euclidean n → Blocks F := fun z j => f j z
  let L : Euclidean n →L[ℝ] Blocks F := ContinuousLinearMap.pi D
  let W : Set (Euclidean n) := ⋂ j, O j
  have hW : IsOpen W := isOpen_iInter_of_finite hO
  have haW : (c x).val ∈ W := Set.mem_iInter.mpr haO
  have hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ W := contDiffOn_pi.mpr
    (fun j => (hf j).mono (Set.iInter_subset O j))
  have hχd : HasFDerivAt χ L (c x).val := hasFDerivAt_pi.mpr hd
  have hχ0 : χ (c x).val = 0 := by
    funext j
    exact ((hEq j x (hxU j)).2).mp ⟨p j, h j⟩
  have hL : Function.Surjective L := by
    intro z
    let q : ∀ j, NormalFiber (F j).normal (p j) := fun j =>
      (P202Specs.ThomClass.fiberLinearCoordinates (F j).normal (a j) (p j) (hp j)).symm (z j)
    obtain ⟨v, hv⟩ := hsurj q
    refine ⟨C v, ?_⟩
    funext j
    change D j (C v) = z j
    rw [hn j]
    have hvj : normalProjection (F j) (p j) x (h j) v = q j := congrFun hv j
    rw [hvj]
    exact LinearEquiv.apply_symm_apply _ _
  let E := euclideanChart c
  have hxE : x ∈ E.source := (euclideanChart_source c).symm ▸ hxc
  let B : Set M := ⋂ j, U j
  have hB : IsOpen B := isOpen_iInter_of_finite hU
  have hxB : x ∈ B := Set.mem_iInter.mpr hxU
  let V := W ∩ (E.target ∩ E.symm ⁻¹' B)
  have hV : IsOpen V := hW.inter (E.symm.isOpen_inter_preimage hB)
  have haV : (c x).val ∈ V := by
    refine ⟨haW, E.map_source hxE, ?_⟩
    change E.symm (E x) ∈ B
    rwa [E.left_inv hxE]
  obtain ⟨e₀, ha₀, he₀V, he₀a, he₀fst, he₀s, he₀i⟩ :=
    smooth_submersion_chart χ L (c x).val V hV haV (hχ.mono Set.inter_subset_left) hχd hL
  let e := E.trans e₀
  have hxe : x ∈ e.source := ⟨hxE, ha₀⟩
  have hecenter : e x = (0,0) := by
    change e₀ (c x).val = (0,0)
    rw [he₀a, hχ0]
  have hesource (y : M) (hy : y ∈ e.source) : y ∈ c.source := by
    exact euclideanChart_source c ▸ hy.1
  have heB (y : M) (hy : y ∈ e.source) : y ∈ B := by
    have hh := (he₀V hy.2).2.2
    change E.symm (E y) ∈ B at hh
    rwa [E.left_inv hy.1] at hh
  have hefst (y : M) : (e y).1 = χ (c y).val := he₀fst (E y)
  have hezero (y : M) (hy : y ∈ e.source) (j : Fin k) :
      y ∈ Set.range (F j).inclusion ↔ (e y).1 j = 0 := by
    rw [hefst]
    exact (hEq j y (Set.mem_iInter.mp (heB y hy) j)).2
  have he_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (e ∘ E.symm) (E '' e.source) := by
    apply he₀s.congr_mono
    · rintro z ⟨y, hy, rfl⟩
      change e₀ (E (E.symm (E y))) = e₀ (E y)
      rw [E.left_inv hy.1]
    · rintro z ⟨y, hy, rfl⟩
      exact hy.2
  have hinv (z : Blocks F × L.ker) (hz : z ∈ e.target) :
      (c (e.symm z)).val = e₀.symm z := by
    change E (E.symm (e₀.symm z)) = e₀.symm z
    exact E.right_inv hz.2
  have he_inverse : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (c (e.symm z)).val) e.target :=
    he₀i.congr_mono hinv (fun _ hz => hz.1)
  let j : Blocks F → Blocks F × L.ker := fun z => (z,0)
  have hj : ContDiff ℝ (⊤ : ℕ∞) j := contDiff_id.prodMk contDiff_const
  let Q := j ⁻¹' e.target
  have hQ : IsOpen Q := e.open_target.preimage hj.continuous
  have h0Q : (0 : Blocks F) ∈ Q := by
    change (0,0) ∈ e.target
    rw [← hecenter]
    exact e.map_source hxe
  let s : Blocks F → M := e.symm ∘ j
  have hs0 : s 0 = x := by
    change e.symm (0,0) = x
    rw [← hecenter, e.left_inv hxe]
  have hsmem (z : Blocks F) (hz : z ∈ Q) : s z ∈ e.source := e.map_target hz
  have hse (z : Blocks F) (hz : z ∈ Q) : e (s z) = (z,0) := e.right_inv hz
  have hs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (c (s z)).val) Q :=
    he_inverse.comp hj.contDiffOn (fun _ hz => hz)
  have hs_cont : ContinuousOn s Q :=
    e.symm.continuousOn.comp hj.continuous.continuousOn (fun _ hz => hz)
  have hs_inj : Set.InjOn s Q := by
    intro z hz w hw heq
    exact congrArg Prod.fst ((hse z hz).symm.trans ((congrArg e heq).trans (hse w hw)))
  have hχs (z : Blocks F) (hz : z ∈ Q) : χ (c (s z)).val = z := by
    rw [← hefst]
    exact congrArg Prod.fst (hse z hz)
  have hLs : L.comp (fderiv ℝ (fun z => (c (s z)).val) 0) =
      ContinuousLinearMap.id ℝ (Blocks F) := by
    have hχd' : HasFDerivAt χ L (c (s 0)).val := by rwa [hs0]
    have hds := (hs_smooth.contDiffAt (hQ.mem_nhds h0Q)).differentiableAt (by simp)
    have hcomp := hχd'.comp 0 hds.hasFDerivAt
    have heq : (fun z => χ (c (s z)).val) =ᶠ[𝓝 (0 : Blocks F)] id := by
      filter_upwards [hQ.mem_nhds h0Q] with z hz
      exact hχs z hz
    exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id 0)
  refine ⟨{
    codimension_le := codimensionBound n k M S F x p h hsurj
    chart := c
    chart_mem := hc
    point_mem := hxc
    tangentCoordinates := C
    tangent_isCoordinates := hC
    chartPoint := a
    base_mem := hp
    derivative := L
    normal_derivative := fun v j => hn j v
    coordinates := e
    center := hecenter
    mem_source := hxe
    source_in_chart := hesource
    smooth := he_smooth
    inverse_smooth := he_inverse
    has_derivative := ⟨χ, hχd, Filter.Eventually.of_forall (fun y => (hefst y).symm)⟩
    zero_equations := hezero
    sliceDomain := Q
    sliceDomain_open := hQ
    sliceDomain_zero := h0Q
    slice := s
    slice_center := hs0
    slice_mem := hsmem
    slice_coordinates := hse
    slice_smooth := hs_smooth
    slice_continuous := hs_cont
    slice_injective := hs_inj
    slice_normal_derivative := ?_
    slice_zero_equations := ?_ }⟩
  · intro v j
    apply (P202Specs.ThomClass.fiberLinearCoordinates (F j).normal (a j) (p j) (hp j)).injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := hn j (C.symm (fderiv ℝ (fun z => (c (s z)).val) 0 v))
    rw [LinearEquiv.apply_symm_apply] at hh
    rw [← hh]
    exact congrFun (congrArg (fun A => A v) hLs) j
  · intro z hz j
    rw [hezero (s z) (hsmem z hz) j, hse z hz]

end P202.TransverseNormalCoordinates
