import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.IrrationalSlopeDistribution
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.IrrationalLine
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.DistributionTests

set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.IrrationalSlopeDistribution
open ModelData AtlasData MapData SphereTorusData IrrationalLineData TangentData
  DifferentialData TangentBundleData BundleOperationsData DistributionData
  GlobalLeafData FrameData ConstantRankData BundleData FiniteRegularityData
  Set Filter
open scoped Topology

/-- Two continuous lifts of the same quotient map differ locally by a constant.
The argument uses injectivity of the quotient on a box of width less than one. -/
lemma lift_difference_germ {X : Type*} [TopologicalSpace X] {x : X}
    {f g : X → Euclidean 2} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hproj : (fun y => quotientProjection 2 (f y)) =ᶠ[𝓝 x]
      (fun y => quotientProjection 2 (g y))) :
    (fun y => f y + (g x - f x)) =ᶠ[𝓝 x] g := by
  let F : X → Euclidean 2 := fun y => f y + (g x - f x)
  have hF : ContinuousAt F x := hf.add continuousAt_const
  have hFx : F x = g x := by dsimp [F]; abel
  have hbox := (SphereTorus.isOpen_angleBox (g x) (1 / 4)).mem_nhds
    (SphereTorus.mem_angleBox_center (g x) (by norm_num))
  have hFbox : ∀ᶠ y in 𝓝 x, F y ∈ angleBox (g x) (1 / 4) :=
    hF.preimage_mem_nhds (by simpa [hFx] using hbox)
  have hgbox := hg.preimage_mem_nhds hbox
  have hz : quotientProjection 2 (g x - f x) = 0 := by
    ext i
    change (g x i : AddCircle (1 : ℝ)) - (f x i : AddCircle (1 : ℝ)) = 0
    exact sub_eq_zero.mpr (congrFun hproj.eq_of_nhds.symm i)
  filter_upwards [hFbox, hgbox, hproj] with y hyF hyg hy
  apply SphereTorus.quotientProjection_injOn_box (g x) (by norm_num) hyF hyg
  have he : quotientProjection 2 (F y) = quotientProjection 2 (f y) := by
    ext i
    change (f y i : AddCircle (1 : ℝ)) +
      ((g x - f x) i : AddCircle (1 : ℝ)) = _
    have hzi := congrFun hz i
    change ((g x - f x) i : AddCircle (1 : ℝ)) = 0 at hzi
    rw [hzi, add_zero]
    rfl
  exact he.trans hy

lemma angle_transition_germ {a b : Euclidean 2} {ε δ : ℝ}
    {e d : ModelChart 2 .euclidean (FlatTorus 2)}
    (he : IsAngleChart a ε e) (hd : IsAngleChart b δ d)
    (p : FlatTorus 2) (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    (fun q => (e q).val + ((d p).val - (e p).val)) =ᶠ[𝓝 p]
      (fun q => (d q).val) := by
  apply lift_difference_germ
    (continuous_subtype_val.continuousAt.comp (e.continuousAt hp))
    (continuous_subtype_val.continuousAt.comp (d.continuousAt hpd))
  filter_upwards [e.open_source.mem_nhds hp, d.open_source.mem_nhds hpd] with q hqe hqd
  exact (SphereTorus.angleChart_projection he hqe).trans
    (SphereTorus.angleChart_projection hd hqd).symm

/-- All quotient charts give identical intrinsic tangent coordinates. -/
lemma angle_coordinates_eq (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (K : FiberCoordinates Q) {a b : Euclidean 2} {ε δ : ℝ}
    {e d : ModelChart 2 .euclidean (FlatTorus 2)}
    (he : e ∈ Q.smoothStructure.val) (hd : d ∈ Q.smoothStructure.val)
    (heangle : IsAngleChart a ε e) (hdangle : IsAngleChart b δ d)
    (p : FlatTorus 2) (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (v : TangentSpace Q p) : K.equiv d hd p hpd v = K.equiv e he p hp v := by
  have h := TangentBundle.transition_jacobian Q K e d he hd p hp hpd
    univ (fun x => x + ((d p).val - (e p).val)) isOpen_univ (mem_univ _)
    (contDiff_id.add contDiff_const).contDiffOn
    (angle_transition_germ heangle hdangle p hp hpd) v
  simpa only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply] using h

/-- A fixed global coordinate is chosen from the quotient-chart cover. The
following equality proves that this choice has no mathematical effect. -/
def quotientCoordinates (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (K : FiberCoordinates Q) (p : FlatTorus 2) : TangentSpace Q p ≃ₗ[ℝ] Euclidean 2 := by
  classical
  let e := Classical.choose ((SphereTorus.angleAtlas_isContDiffAtlas 2).1 p)
  have he := Classical.choose_spec ((SphereTorus.angleAtlas_isContDiffAtlas 2).1 p)
  exact K.equiv e (by rw [hQ]; exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas 2) he.1) p he.2

lemma quotientCoordinates_eq (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (K : FiberCoordinates Q) {a : Euclidean 2} {ε : ℝ}
    {e : ModelChart 2 .euclidean (FlatTorus 2)} (he : e ∈ Q.smoothStructure.val)
    (hangle : IsAngleChart a ε e) (p : FlatTorus 2) (hp : p ∈ e.source)
    (v : TangentSpace Q p) :
    quotientCoordinates Q hQ K p v = K.equiv e he p hp v := by
  classical
  unfold quotientCoordinates
  obtain ⟨b, δ, _, _, hd⟩ :=
    (Classical.choose_spec ((SphereTorus.angleAtlas_isContDiffAtlas 2).1 p)).1
  exact angle_coordinates_eq Q K he _ hangle hd p hp _ v

/-- Shearing the ordinary basis gives the ordered frame (1,α),(0,1). -/
def slopeShear (α : ℝ) : Euclidean 2 ≃ₗ[ℝ] Euclidean 2 where
  toFun x := ![x 0, α * x 0 + x 1]
  invFun x := ![x 0, x 1 - α * x 0]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

lemma mem_slope_span (α : ℝ) (v : Euclidean 2) :
    v ∈ Submodule.span ℝ {(![1, α] : Euclidean 2)} ↔ v 1 = α * v 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    have h0 := congrFun hr 0
    have h1 := congrFun hr 1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, mul_one] at h0 h1
    rw [← h0, ← h1]
    ring
  · intro hv
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [hv, mul_comm]

/-- The actual intrinsic subspaces, defined without any smoothness certificate. -/
def slopeFiber (α : ℝ) (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (K : FiberCoordinates Q) (p : FlatTorus 2) : Submodule ℝ (TangentSpace Q p) :=
  (Submodule.span ℝ {(![1, α] : Euclidean 2)}).comap
    (quotientCoordinates Q hQ K p).toLinearMap

lemma slopeFiber_coordinates (α : ℝ) (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (K : FiberCoordinates Q) {a : Euclidean 2} {ε : ℝ}
    {e : ModelChart 2 .euclidean (FlatTorus 2)} (he : e ∈ Q.smoothStructure.val)
    (hangle : IsAngleChart a ε e) (p : FlatTorus 2) (hp : p ∈ e.source)
    (v : TangentSpace Q p) :
    v ∈ slopeFiber α Q hQ K p ↔ K.equiv e he p hp v ∈
      Submodule.span ℝ {(![1, α] : Euclidean 2)} := by
  change quotientCoordinates Q hQ K p v ∈
    Submodule.span ℝ {(![1, α] : Euclidean 2)} ↔ _
  rw [quotientCoordinates_eq Q hQ K he hangle p hp v]

/-- A smooth ambient frame in one quotient chart, on the original tangent
realization. The section coordinates are constant; smoothness is proved. -/
def angleSlopeFrame (α : ℝ) (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (C : CotangentBundle Q) (e : ModelChart 2 .euclidean (FlatTorus 2))
    (he : e ∈ Q.smoothStructure.val) :
    letI := C.realization.space.topology
    LocalFrame C.realization.space.bundle e.source e.open_source := by
  letI := C.realization.space.topology
  let E (p : e.source) := C.tangent.fiberCoordinates.equiv e he p.val p.property
  let b (p : e.source) := (Pi.basisFun ℝ (Fin 2)).map ((slopeShear α).trans (E p).symm)
  refine { section_ := fun j p => b p j
           basis := b
           basis_eq := fun _ _ => rfl
           smooth := ?_ }
  intro j p
  let i : TangentIndex Q := ⟨e, he⟩
  have hi : p.val ∈ C.realization.space.bundle.baseSet i := by
    rw [C.realization.baseSet]; exact p.property
  apply Frames.smoothAt_of_sectionCoordinates C.realization.space.bundle e.source
    e.open_source i (fun p => b p j) p hi
  apply (FrameData.VectorSmoothAt.const _ (slopeShear α (Pi.single j 1)) p).congr
  apply Eventually.of_forall
  intro q
  rw [Frames.sectionCoordinates, C.realization.coordinates i q.val q.property]
  simp [b, E, i, Module.Basis.map_apply, Pi.basisFun_apply]

lemma slopeFiber_smooth (α : ℝ) (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (C : CotangentBundle Q) :
    letI := C.realization.space.topology
    IsSmoothSubbundle C.realization.space.bundle 1 (slopeFiber α Q hQ C.tangent.fiberCoordinates) := by
  letI := C.realization.space.topology
  intro p
  obtain ⟨e, he, hp⟩ := (SphereTorus.angleAtlas_isContDiffAtlas 2).1 p
  have heQ : e ∈ Q.smoothStructure.val := by
    rw [hQ]; exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas 2) he
  obtain ⟨a, ε, _, _, hangle⟩ := he
  refine ⟨by norm_num, e.source, e.open_source, hp, angleSlopeFrame α Q C e heQ, ?_⟩
  intro q v
  rw [slopeFiber_coordinates α Q hQ C.tangent.fiberCoordinates heQ hangle q.val q.property v,
    mem_slope_span]
  change _ ↔ ∀ j : Fin 2, 1 ≤ j.val →
    ((Pi.basisFun ℝ (Fin 2)).map ((slopeShear α).trans
      (C.tangent.fiberCoordinates.equiv e heQ q.val q.property).symm)).equivFun v j = 0
  simp only [Module.Basis.map_equivFun, Pi.basisFun_equivFun,
    LinearEquiv.trans_apply, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.refl_apply]
  constructor
  · intro hv j hj
    have hj' : j = 1 := by omega
    subst j
    change (C.tangent.fiberCoordinates.equiv e heQ q.val q.property v) 1 -
      α * (C.tangent.fiberCoordinates.equiv e heQ q.val q.property v) 0 = 0
    exact sub_eq_zero.mpr hv
  · intro h
    have h1 := h 1 (by norm_num)
    exact sub_eq_zero.mp h1

/-- The descended constant distribution, with its actual subbundle proof. -/
def slopeDistribution (α : ℝ) (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (C : CotangentBundle Q) : SmoothDistribution C 1 where
  fiber := slopeFiber α Q hQ C.tangent.fiberCoordinates
  smooth := slopeFiber_smooth α Q hQ C

/-- Every smooth line distribution is involutive: an alternating two-form
vanishes on a one-dimensional space, so the annihilator criterion applies. -/
lemma rankOne_involutive (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (C : CotangentBundle Q) (D : SmoothDistribution C 1) : IsInvolutive D := by
  obtain ⟨B⟩ := ExteriorAlgebraResults.exists_formBundle C 1
  apply (DistributionTests.annihilator_test D B).mpr
  intro U hU θ η hθ hη hvan p hp v hv
  obtain ⟨V, hV, hpV, ⟨F⟩⟩ := DistributionTests.distribution_frame_exists D p
  apply DistributionTests.alternating_vanishesOn_basis (D.fiber p) (F.basis ⟨p, hpV⟩)
    (ExteriorData.evaluate (TangentSpace Q p) 2 (η p)) ?_ v hv
  intro w
  apply AlternatingMap.map_eq_zero_of_eq _ _ (i := (0 : Fin 2)) (j := 1)
  · exact congrArg (fun i => ((F.basis ⟨p, hpV⟩) i).val) (Subsingleton.elim _ _)
  · decide

lemma translated_continuous (α : ℝ) (p : FlatTorus 2) :
    Continuous (fun t => p + irrationalLine α t) :=
  continuous_const.add (IrrationalLine.continuous_line α)

/-- The local lift of every translated line has exactly the original slope
and scale. Translations change only the constant term of its local lift. -/
lemma translated_germ (α : ℝ) (p : FlatTorus 2) (t : ℝ)
    {a : Euclidean 2} {ε : ℝ} {d : ModelChart 2 .euclidean (FlatTorus 2)}
    (hd : IsAngleChart a ε d) (ht : p + irrationalLine α t ∈ d.source) :
    (fun s => lineLift α s + ((d (p + irrationalLine α t)).val - lineLift α t))
      =ᶠ[𝓝 t] (fun s => (d (p + irrationalLine α s)).val) := by
  obtain ⟨b, hb⟩ := (SphereTorus.quotientProjection_isOpenQuotientMap 2).surjective p
  have hf : Continuous (fun s : ℝ => b + lineLift α s) := by
    dsimp [lineLift]; fun_prop
  have hdcont : ContinuousAt (fun q : FlatTorus 2 => (d q).val)
      (p + irrationalLine α t) :=
    continuous_subtype_val.continuousAt.comp (d.continuousAt ht)
  have hg : ContinuousAt (fun s : ℝ => (d (p + irrationalLine α s)).val) t :=
    hdcont.comp (f := fun s : ℝ => p + irrationalLine α s)
      (translated_continuous α p).continuousAt
  have he := lift_difference_germ hf.continuousAt hg (show
      (fun s => quotientProjection 2 (b + lineLift α s)) =ᶠ[𝓝 t]
        (fun s => quotientProjection 2 (d (p + irrationalLine α s)).val) from by
    filter_upwards [(translated_continuous α p).continuousAt.preimage_mem_nhds
      (d.open_source.mem_nhds ht)] with s hs
    have hs' : p + irrationalLine α s ∈ d.source := hs
    have hadd : quotientProjection 2 (b + lineLift α s) =
        quotientProjection 2 b + irrationalLine α s := by
      ext i
      exact AddCircle.coe_add (1 : ℝ) (b i) (lineLift α s i)
    exact (hadd.trans (congrArg (fun q => q + irrationalLine α s) hb)).trans
      (SphereTorus.angleChart_projection hd hs').symm)
  filter_upwards [he] with s hs
  calc
    lineLift α s + ((d (p + irrationalLine α t)).val - lineLift α t) =
      b + lineLift α s + ((d (p + irrationalLine α t)).val - (b + lineLift α t)) := by abel
    _ = (d (p + irrationalLine α s)).val := hs

lemma translated_chart_smooth (α : ℝ) (p : FlatTorus 2) (t : ℝ)
    {a : Euclidean 2} {ε : ℝ} {d : ModelChart 2 .euclidean (FlatTorus 2)}
    (hd : IsAngleChart a ε d) (ht : p + irrationalLine α t ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) realChart d (fun s => p + irrationalLine α s) t := by
  let c := (d (p + irrationalLine α t)).val - lineLift α t
  refine ⟨univ, isOpen_univ, mem_univ _, fun x => lineLinear α x + c,
    ((lineLinear α).contDiff.add contDiff_const).contDiffOn, ?_⟩
  simpa [IrrationalLine.lineLinear_apply, IrrationalLineData.realChart,
    realCoordinates, lineLift, c] using translated_germ α p t hd ht

lemma translated_derivative (α : ℝ) (p : FlatTorus 2) (t : ℝ)
    {a : Euclidean 2} {ε : ℝ} {d : ModelChart 2 .euclidean (FlatTorus 2)}
    (hd : IsAngleChart a ε d) (ht : p + irrationalLine α t ∈ d.source) :
    chartDerivative realChart d (fun s => p + irrationalLine α s) t = lineLinear α := by
  apply FiniteRegularity.coordinateDerivative_eq realChart _ t (mem_univ _) (lineLinear α)
  refine ⟨fun x => lineLinear α x +
    ((d (p + irrationalLine α t)).val - lineLift α t), ?_, ?_⟩
  · exact (lineLinear α).hasFDerivAt.add_const _
  · simpa [IrrationalLine.lineLinear_apply, IrrationalLineData.realChart,
      realCoordinates, lineLift] using translated_germ α p t hd ht

lemma translated_smoothImmersion (α : ℝ)
    (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas)
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (p : FlatTorus 2) :
    IsSmoothMap S Q (fun t => p + irrationalLine α t) ∧
      MapClassData.IsImmersion S Q (fun t => p + irrationalLine α t) := by
  have hs : IsSmoothMap S Q (fun t => p + irrationalLine α t) := by
    change ManifoldContDiff (⊤ : ℕ∞) _ _ _
    rw [hS, hQ]
    apply (manifoldContDiff_maximalExtension_iff _ _ _ IrrationalLine.realAtlas_smooth
      (SphereTorus.angleAtlas_isContDiffAtlas 2) _).mpr
    intro t
    refine ⟨(translated_continuous α p).continuousAt, ?_⟩
    rintro e he d ⟨a, ε, _, _, hd⟩ _ ht
    have he' : e = realChart := mem_singleton_iff.mp he
    subst e
    exact translated_chart_smooth α p t hd ht
  refine ⟨hs, fun t => ?_⟩
  have hs1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ _ (by simp) hs
  obtain ⟨d, hd, ht⟩ := (SphereTorus.angleAtlas_isContDiffAtlas 2).1 (p + irrationalLine α t)
  have he : realChart ∈ S.smoothStructure.val := by
    rw [hS]; exact subset_maximalExtension IrrationalLine.realAtlas_smooth rfl
  have hd' : d ∈ Q.smoothStructure.val := by
    rw [hQ]; exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas 2) hd
  apply (MapClasses.chart_invariants S Q _ hs1 t realChart d he hd' (mem_univ _) ht).2.1.mpr
  obtain ⟨a, ε, _, _, hangle⟩ := hd
  rw [translated_derivative α p t hangle ht]
  exact IrrationalLine.lineLinear_injective α

/-- The derivative of the original real lift has precisely the desired span. -/
lemma lineLinear_range (α : ℝ) :
    LinearMap.range (lineLinear α).toLinearMap =
      Submodule.span ℝ {(![1, α] : Euclidean 2)} := by
  ext v
  rw [LinearMap.mem_range, mem_slope_span]
  constructor
  · rintro ⟨w, rfl⟩
    simp [IrrationalLine.lineLinear_apply]
  · intro hv
    refine ⟨fun _ => v 0, ?_⟩
    ext i
    fin_cases i <;> simp [IrrationalLine.lineLinear_apply, hv]

lemma translated_integral (α : ℝ) (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas)
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (C : CotangentBundle Q) (p : FlatTorus 2) :
    IsIntegralImmersion (slopeDistribution α Q hQ C) S
      (fun t : ℝ => p + irrationalLine α t) := by
  obtain ⟨hs, hi⟩ := translated_smoothImmersion α S Q hS hQ p
  let f : ℝ → FlatTorus 2 := fun t => p + irrationalLine α t
  let L := fun t => differential S Q f hs t
  have hL : ∀ t, IsDifferential S Q f t (L t) :=
    fun t => differential_spec S Q f hs t
  refine ⟨hs, hi, L, hL, ?_⟩
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  have he : realChart ∈ S.smoothStructure.val := by
    rw [hS]; exact subset_maximalExtension IrrationalLine.realAtlas_smooth rfl
  intro t
  obtain ⟨d, hd, ht⟩ := (SphereTorus.angleAtlas_isContDiffAtlas 2).1 (f t)
  have hdQ : d ∈ Q.smoothStructure.val := by
    rw [hQ]; exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas 2) hd
  obtain ⟨a, ε, _, _, hangle⟩ := hd
  let E := K.equiv realChart he t (mem_univ _)
  let F := C.tangent.fiberCoordinates.equiv d hdQ (f t) ht
  have hjac : ∀ v, F (L t v) = lineLinear α (E v) := by
    intro v
    have h := differential_jacobian S Q f hs t (L t) (hL t) realChart d he hdQ
      (mem_univ _) ht E F (K.isCoordinates realChart he t (mem_univ _))
      (C.tangent.fiberCoordinates.isCoordinates d hdQ (f t) ht)
      univ (fun x => lineLinear α x + ((d (f t)).val - lineLift α t))
      isOpen_univ (mem_univ _) ((lineLinear α).contDiff.add contDiff_const).contDiffOn
      (by simpa [IrrationalLine.lineLinear_apply, IrrationalLineData.realChart,
        realCoordinates, lineLift, f] using translated_germ α p t hangle ht) v
    simpa only [fderiv_add_const, ContinuousLinearMap.fderiv] using h
  ext v
  change v ∈ LinearMap.range (L t) ↔ v ∈ slopeFiber α Q hQ C.tangent.fiberCoordinates (f t)
  rw [slopeFiber_coordinates α Q hQ C.tangent.fiberCoordinates hdQ hangle (f t) ht v,
    ← lineLinear_range]
  change (∃ w, L t w = v) ↔ ∃ z, lineLinear α z = F v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨E w, (hjac w).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨E.symm z, F.injective ?_⟩
    rw [hjac, E.apply_symm_apply]
    exact hz

/-- The analytic construction for the irrational leaf example, with no
irrationality assumption needed for this half of the example. -/
theorem slope_distribution :
    Specs.SmoothManifolds.Ch08.IrrationalSlopeDistribution.slope_distributionType := by
  intro α S Q hS hQ
  obtain ⟨C⟩ := BundleOperations.exists_cotangent Q
  refine ⟨C, slopeDistribution α Q hQ C, rankOne_involutive Q C _, ?_, ?_⟩
  · intro a ε e he hangle p hp v
    exact slopeFiber_coordinates α Q hQ C.tangent.fiberCoordinates he hangle p hp v
  · exact translated_integral α S Q hS hQ C

end SmoothManifolds.IrrationalSlopeDistribution

