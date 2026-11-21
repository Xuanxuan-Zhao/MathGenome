import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.TensorLieDerivative

/-! Actual local-flow interpretation of the tensor Lie derivative at interior
points of manifolds with boundary. -/
set_option autoImplicit false

namespace SmoothManifolds.TensorLieDerivative
open ModelData AtlasData TangentData TangentBundleData VectorFieldData TensorLieData
open BoundaryData BoundaryFlowData MaximalFlowData Set Filter
open scoped Topology

universe u

/-- A time/state neighborhood for the local flow of a field. Only its short
time maps on this neighborhood are required to solve the ODE of the field. -/
structure InteriorLocalFlow {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    (X : SmoothField B) (F : CurveFamily M) (p : M) where
  time : D13Unified.OpenTimeInterval
  zero_mem : 0 ∈ time.carrier
  states : Set M
  isOpen_states : IsOpen states
  point_mem : p ∈ states
  states_interior : states ⊆ manifoldInterior S
  time_subset : ∀ q ∈ states, time.carrier ⊆ (F.interval q).carrier
  initial : ∀ q ∈ states, F.curve q 0 = q
  stays_interior : ∀ q ∈ states, ∀ t ∈ time.carrier, F.curve q t ∈ manifoldInterior S
  integral : ∀ q ∈ states, IsIntegralCurveOn X time.carrier (F.curve q)
  smooth : ∀ q ∈ states, ∀ t ∈ time.carrier, FlowSmoothAt S F (t, q)
  flow_law : ∀ q ∈ states, ∀ s ∈ time.carrier, ∀ t : ℝ, s + t ∈ time.carrier →
    F.curve (F.curve q s) t = F.curve q (s + t)

/-- Any other integral curve of the original field agrees with this local flow
on the common time interval. -/
theorem InteriorLocalFlow.agrees_with_integral_curve
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    {X : SmoothField B} {F : CurveFamily M} {p : M} (L : InteriorLocalFlow X F p)
    {q : M} (hq : q ∈ L.states) (J : D13Unified.OpenTimeInterval) (γ : ℝ → M)
    (h0 : 0 ∈ J.carrier) (hγ0 : γ 0 = q) (hγ : IsIntegralCurveOn X J.carrier γ) :
    EqOn (F.curve q) γ (L.time.carrier ∩ J.carrier) :=
  BoundaryTangentFlow.overlap_unique X L.time J (F.curve q) γ (L.integral q hq) hγ
    0 ⟨L.zero_mem, h0⟩ ((L.initial q hq).trans hγ0.symm)

/-- At an interior point the intrinsic tensor Lie derivative is obtained by
differentiating the actual local-flow pullback, for an arbitrary smooth field. -/
theorem tensor_interior_flow
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) (A Z : SmoothTensor B r s)
    (hZ : CoordinateLieDerivative B X A.val Z.val)
    (p : M) (hp : p ∈ manifoldInterior S) :
    ∃ F : CurveFamily M, Nonempty (InteriorLocalFlow X F p) ∧
      HasTensorFlowDerivative B F A.val Z.val p := by
  obtain ⟨Y, hY, heq⟩ := exists_tangent_field_eq_near_interior B X p hp
  obtain ⟨F, hF⟩ := BoundaryTangentFlow.maximal_family_exists S B Y hY
  have hreg := BoundaryTangentFlow.domain_open_smooth S B Y hY F hF
  have hlaw := BoundaryTangentFlow.lifespan_flow_law S B Y hY F hF
  have hnear : ∀ᶠ q in 𝓝 p, Y.val q = X.val q ∧ q ∈ manifoldInterior S :=
    inter_mem heq ((isOpen_manifoldInterior S).mem_nhds hp)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hnear
  have hzero : flow F (0, p) ∈ U := by
    change F.curve p 0 ∈ U
    rwa [(hF p).2.1]
  have hbox : ∀ᶠ z in 𝓝 (0, p), z ∈ flowDomain F ∧ flow F z ∈ U :=
    inter_mem (hreg.1.mem_nhds (show (0, p) ∈ flowDomain F from (hF p).1))
      ((hreg.2 (0, p) (hF p).1).1.preimage_mem_nhds (hU.mem_nhds hzero))
  obtain ⟨T, hT, V₀, hV₀, hTV⟩ := mem_nhds_prod_iff.mp hbox
  obtain ⟨l, u, hlu, hinterval⟩ := mem_nhds_iff_exists_Ioo_subset.mp hT
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp (inter_mem hV₀ (hU.mem_nhds hpU))
  let I := D13Unified.OpenTimeInterval.bounded l u (hlu.1.trans hlu.2)
  have hflow (q : M) (hq : q ∈ V) (t : ℝ) (ht : t ∈ I.carrier) :
      t ∈ (F.interval q).carrier ∧ F.curve q t ∈ U :=
    hTV (a := (t, q)) ⟨hinterval ht, (hVsub hq).1⟩
  have hsub (q : M) (hq : q ∈ V) : I.carrier ⊆ (F.interval q).carrier :=
    fun t ht => (hflow q hq t ht).1
  have hlocal : InteriorLocalFlow X F p := by
    refine ⟨I, hlu, V, hV, hpV, fun q hq => (hUsub (hVsub hq).2).2, hsub,
      fun q _ => (hF q).2.1, fun q hq t ht => (hUsub (hflow q hq t ht).2).2,
      ?_, fun q hq t ht => hreg.2 (t, q) (hsub q hq ht), ?_⟩
    · intro q hq
      have hcurve := (hF q).2.2.1
      refine ⟨hcurve.1.mono (hsub q hq), ?_⟩
      intro t ht e he hte
      rw [← (hUsub (hflow q hq t ht).2).1]
      exact hcurve.2 t (hsub q hq ht) e he hte
    · intro q hq s hs t ht
      exact (hlaw q s (hsub q hq hs)).2 t (hsub q hq ht)
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  refine ⟨F, ⟨hlocal⟩, tensor_flow_derivative_congr_value B F A.val
    (chartLieSection B Y A e he) Z.val p ?_ (chartLieSection_boundary_flow B Y hY A F hF p e he hpe)⟩
  rw [chartLieSection_eq_of_field_eq_near B Y X A e he p hpe heq]
  exact (coordinate_lie_eq_chart S B X A Z.val hZ e he p hpe).symm

end SmoothManifolds.TensorLieDerivative
