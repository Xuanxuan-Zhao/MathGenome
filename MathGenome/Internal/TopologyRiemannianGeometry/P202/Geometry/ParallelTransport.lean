import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ParallelTransport
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurveCovariantDerivative
import MathGenome.ODEDynamics.Topics.D13Unified.Ch07
import Mathlib.Analysis.Calculus.MeanValue

/-! Parallel transport for arbitrary smooth bundle connections (Theorem 6.4).
The construction uses continuous linear ODEs in local frames and glues fields
with the actual within derivatives on each original C¹ path piece. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

namespace P202.Geometry.ParallelTransport
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleMetricData
  P202.ConnectionData P202.CurveData P202.CurveConnectionData P202.ParallelData
open Set Filter
open scoped Topology
universe u v w

section LinearODE
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The compact-interval IVP uses an actual TimeInterval and its actual within
derivatives. In particular the initial time need not be an endpoint. -/
theorem linear_ode_on_compact {l q s : ℝ} (hlq : l ≤ q)
    (A : ℝ → F →L[ℝ] F) (hA : ContinuousOn A (Icc l q))
    (hs : s ∈ Icc l q) (ξ : F) :
    ∃ Y : ℝ → F, ContinuousOn Y (Icc l q) ∧ Y s = ξ ∧
      (∀ t ∈ Icc l q, HasDerivWithinAt Y (A t (Y t)) (Icc l q) t) ∧
      ContDiffOn ℝ 1 Y (Icc l q) ∧
      ∀ Z : ℝ → F, ContinuousOn Z (Icc l q) → Z s = ξ →
        (∀ t ∈ Icc l q, HasDerivWithinAt Z (A t (Z t)) (Icc l q) t) →
        EqOn Z Y (Icc l q) := by
  let I : D13Unified.TimeInterval := ⟨Icc l q, nonempty_Icc.mpr hlq, ordConnected_Icc⟩
  obtain ⟨Y, hc, hi, hd, _, hr, hu⟩ :=
    D13Unified.Ch07.LinearSystemExistence.existence I A s ξ hs hA
  exact ⟨Y, hc, hi, hd, hr, hu⟩

/-- A continuous coefficient on a compact interval has a continuous constant
extension. Solving that extended system supplies ambient C¹ representatives at
both endpoints, without requiring an extension of the manifold-valued path. -/
theorem linear_ode_c1_extension {l q s : ℝ} (hlq : l ≤ q)
    (A : ℝ → F →L[ℝ] F) (hA : ContinuousOn A (Icc l q))
    (hs : s ∈ Icc l q) (ξ : F) :
    ∃ Y : ℝ → F, ContDiff ℝ 1 Y ∧ Y s = ξ ∧
      (∀ t ∈ Icc l q, HasDerivWithinAt Y (A t (Y t)) (Icc l q) t) ∧
      ∀ Z : ℝ → F, ContinuousOn Z (Icc l q) → Z s = ξ →
        (∀ t ∈ Icc l q, HasDerivWithinAt Z (A t (Z t)) (Icc l q) t) →
        EqOn Z Y (Icc l q) := by
  let Aext : ℝ → F →L[ℝ] F := IccExtend hlq (fun t : Icc l q => A t)
  have hext : Continuous Aext := hA.domRestrict.Icc_extend'
  have hagree (t : ℝ) (ht : t ∈ Icc l q) : Aext t = A t :=
    IccExtend_of_mem hlq _ ht
  let I : D13Unified.TimeInterval := ⟨univ, univ_nonempty, ordConnected_univ⟩
  obtain ⟨Y, hc, hi, hd, _, hr, _⟩ :=
    D13Unified.Ch07.LinearSystemExistence.existence I Aext s ξ (mem_univ _) hext.continuousOn
  have hdY : ∀ t ∈ Icc l q, HasDerivWithinAt Y (A t (Y t)) (Icc l q) t := by
    intro t ht
    simpa only [hagree t ht] using (hd t (mem_univ t)).mono (subset_univ _)
  refine ⟨Y, contDiffOn_univ.mp hr, hi, hdY, ?_⟩
  obtain ⟨W, hW, hWs, hWd, _, hu⟩ := linear_ode_on_compact hlq A hA hs ξ
  intro Z hZ hZs hZd t ht
  exact (hu Z hZ hZs hZd ht).trans
    (hu Y (hc.mono (subset_univ _)) hi hdY ht).symm

end LinearODE

section BundleFields
variable {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  {B : SmoothVectorBundle S r ι E}

/-- The coefficient matrix along the actual one-sided velocity on J. -/
noncomputable def matrixAlong (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (c : ℝ → M) (J : Set ℝ) (t : ℝ) : Matrix (Fin r) (Fin r) ℝ := by
  classical
  exact if hp : c t ∈ U then
    connectionMatrix C b ⟨c t, hp⟩ (PiecewiseCurves.withinVelocity S c J t) else 0

/-- Linear evaluation expanded in any basis, including the empty basis. -/
theorem linear_coordinates {V : Type*} [AddCommGroup V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (lam : V →ₗ[ℝ] ℝ) (v : V) :
    lam v = ∑ j : Fin d, lam (e.symm (Pi.single j 1)) * e v j := by
  have he : v = ∑ j : Fin d, e v j • e.symm (Pi.single j 1) := by
    simpa only [map_sum, map_smul, LinearEquiv.symm_apply_apply,
      Pi.basisFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply] using
      (congrArg e.symm ((Pi.basisFun ℝ (Fin d)).sum_equivFun (e v))).symm
  conv_lhs => rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, mul_comm]

/-- Smooth connection one-forms evaluated on a C¹ path have continuous
coefficients, using the appropriate one-sided velocity on the whole piece. -/
theorem matrixAlong_continuousOn (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {J : Set ℝ} (hc1 : CoordinateC1On S c J)
    (hc : ContinuousOn c J) (hJ : UniqueDiffOn ℝ J) (hUcurve : MapsTo c J U) :
    ContinuousOn (matrixAlong C b c J) J := by
  classical
  intro t ht
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := hc1 t ht
  let k : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e, he⟩
  have hk : c t ∈ (tangentBundle S).baseSet k := by
    rw [(P202.MetricData.tangentRealization S).baseSet]
    exact hp
  let D := derivWithin (fun s => (e (c s)).val) J
  have hD : ContinuousWithinAt D J t :=
    PiecewiseCurves.coordinate_derivWithin_continuousWithinAt hJ ht hx heq
  apply continuousWithinAt_pi.mpr
  intro i
  apply continuousWithinAt_pi.mpr
  intro j
  let ω : (p : M) → Module.Dual ℝ (TangentSpace S p) :=
    SmoothManifolds.SectionExtension.totalSection (fun p : U => connectionForm C b p i j)
  let z : M → Euclidean n := fun p =>
    (((cotangentBundle S).trivialization k) ⟨p, ω p⟩).2
  have hω := ConnectionForms.connectionForm_smooth B C hU b i j (c t) (hUcurve ht)
  have hz : ContinuousAt z (c t) :=
    (SmoothManifolds.SectionExtension.coordinates_smoothAt (cotangentBundle S) k
      (by rw [(cotangentDual S).baseSet]; exact hk) hω).1
  have hz' : ContinuousWithinAt (fun s => z (c s)) J t :=
    hz.comp_continuousWithinAt (hc t ht)
  have hsum : ContinuousWithinAt (fun s => ∑ l : Fin n, z (c s) l * D s l) J t := by
    apply tendsto_finsetSum
    intro l _
    exact ((continuous_apply l).continuousAt.comp_continuousWithinAt hz').mul
      ((continuous_apply l).continuousAt.comp_continuousWithinAt hD)
  apply hsum.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [(hc t ht).eventually (e.open_source.mem_nhds hp),
    self_mem_nhdsWithin] with s hse hsJ
  have hsU := hUcurve hsJ
  have hsk : c s ∈ (tangentBundle S).baseSet k := by
    rw [(P202.MetricData.tangentRealization S).baseSet]
    exact hse
  have hv := PiecewiseCurves.withinVelocity_coordinates hc1 hc hJ hsJ e he hse
  symm
  rw [matrixAlong, dite_eq_left hsU]
  change (∑ l, z (c s) l * D s l) =
    connectionForm C b ⟨c s, hsU⟩ i j (PiecewiseCurves.withinVelocity S c J s)
  rw [linear_coordinates ((tangentBundle S).fiberCoordinates k (c s) hsk)]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  · dsimp only [z]
    rw [(cotangentDual S).coordinates k (c s) hsk (ω (c s)) l]
    dsimp only [ω]
    rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ _ hsU,
      SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]
  · rw [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply,
      (P202.MetricData.tangentRealization S).coordinates k (c s) hse]
    exact congrFun hv.symm l

@[simp] theorem coefficients_frameField {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (c : ℝ → M) (v : ℝ → Euclidean r)
    {t : ℝ} (ht : c t ∈ U) :
    coefficientsAlong b c (frameFieldAlong b c v) t = v t := by
  classical
  rw [CurveCovariantDerivative.coefficientsAlong_of_mem b c _ t ht]
  simp only [frameFieldAlong, dite_eq_left ht, LinearEquiv.apply_symm_apply]

theorem frameField_continuousOn {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) {c : ℝ → M} {v : ℝ → Euclidean r} {J : Set ℝ}
    (hc : ContinuousOn c J) (hv : ContinuousOn v J) (hUcurve : MapsTo c J U) :
    ContinuousOn (fun t => (⟨c t, frameFieldAlong b c v t⟩ :
      Bundle.TotalSpace (Euclidean r) E)) J := by
  intro t ht
  have hs := (SmoothManifolds.Frames.frameSynthesis_smooth B U hU b
    (c t, v t) ⟨hUcurve ht, mem_univ _⟩).1
  have h := hs.comp_continuousWithinAt (f := fun s : ℝ => (c s, v s))
    ((hc t ht).prodMk (hv t ht))
  exact h.congr_of_eventuallyEq_of_mem (Eventually.of_forall (fun s => rfl)) ht

theorem frameField_c1On {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) {c : ℝ → M} {v : ℝ → Euclidean r} {J : Set ℝ}
    (hc : ContinuousOn c J) (hv : ContDiff ℝ 1 v) (hUcurve : MapsTo c J U) :
    C1FieldOn (B := B) c (frameFieldAlong b c v) J := by
  intro t ht
  refine ⟨U, hU, b, hUcurve ht, v, hv.contDiffAt, coefficients_frameField b c v
    (hUcurve ht), ?_⟩
  filter_upwards [(hc t ht).eventually (hU.mem_nhds (hUcurve ht))] with s hs
  exact coefficients_frameField b c v hs

/-- Compactness gives an actual finite frame subdivision for every continuous
path piece. The path need not be an immersion and no positive rank is assumed. -/
theorem exists_frame_subdivision (B : SmoothVectorBundle S r ι E)
    {c : ℝ → M} {l q : ℝ} (hlq : l ≤ q) (hc : ContinuousOn c (Icc l q)) :
    ∃ (m : ℕ) (node : Fin (m + 1) → ℝ), Monotone node ∧
      node 0 = l ∧ node (Fin.last m) = q ∧
      ∀ i : Fin m, ∃ (U : Set M) (hU : IsOpen U) (b : LocalFrame B U hU),
        MapsTo c (Icc (node i.castSucc) (node i.succ)) U := by
  classical
  choose U hU hp hb using fun t : Icc l q =>
    SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
  let cover : Icc l q → Set (Icc l q) := fun j => (fun t : Icc l q => c t) ⁻¹' U j
  have hopen (j : Icc l q) : IsOpen (cover j) := (hU j).preimage hc.domRestrict
  have hcover : univ ⊆ ⋃ j, cover j := by
    intro t _
    exact mem_iUnion.mpr ⟨t, hp t⟩
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hlq hopen hcover
  let node : Fin (m + 1) → ℝ := fun i => (t i.val).val
  refine ⟨m, node, fun i j hij => hmono hij, ht0, hm m le_rfl, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := hsub i.val
  refine ⟨U j, hU j, Classical.choice (hb j), ?_⟩
  intro x hx
  have hxJ : x ∈ Icc l q :=
    ⟨(t i.val).property.1.trans hx.1, hx.2.trans (t (i.val + 1)).property.2⟩
  exact hj (show (⟨x, hxJ⟩ : Icc l q) ∈ Icc (t i.val) (t (i.val + 1)) from hx)

/-- Actual coefficient continuity follows from the continuity of the field in
the bundle total space, rather than being an extra hypothesis on a solution. -/
theorem coefficients_continuousOn {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) {c : ℝ → M} {f : (t : ℝ) → E (c t)} {J : Set ℝ}
    (hf : ContinuousOn (fun t => (⟨c t, f t⟩ :
      Bundle.TotalSpace (Euclidean r) E)) J) (hUcurve : MapsTo c J U) :
    ContinuousOn (coefficientsAlong b c f) J := by
  intro t ht
  have hs := (SmoothManifolds.Frames.frameAnalysis_smooth B U hU b
    ⟨c t, f t⟩ (hUcurve ht)).1
  have h := (continuous_snd.continuousAt.comp hs).comp_continuousWithinAt
    (f := fun s : ℝ => (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean r) E)) (hf t ht)
  exact h.congr_of_eventuallyEq_of_mem (Eventually.of_forall (fun s => rfl)) ht

/-- In an arbitrary local frame, parallelness is the actual coefficient ODE.
Frame independence is supplied by the proved local formula upstream. -/
theorem parallel_coefficients_derivative (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {J : Set ℝ}
    (hc1 : CoordinateC1On S c J) (hc : ContinuousOn c J)
    (hJ : UniqueDiffOn ℝ J) (hUcurve : MapsTo c J U)
    {t : ℝ} (ht : t ∈ J)
    (hf : HasCovariantDerivativeWithinAt C c f J t 0) :
    HasDerivWithinAt (coefficientsAlong b c f)
      (-((matrixAlong C b c J t).mulVec (coefficientsAlong b c f t))) J t := by
  classical
  obtain ⟨v', hv⟩ := CurveCovariantDerivative.exists_coefficients_deriv C ht hf b (hUcurve ht)
  have hV : HasVelocityWithinAt S c J t (PiecewiseCurves.withinVelocity S c J t) :=
    PiecewiseCurves.withinVelocity_spec hc1 hc ht
  have heq := CurveCovariantDerivative.local_formula C ht (hJ t ht) hf b (hUcurve ht) hV hv
  have hz := congrArg (b.basis ⟨c t, hUcurve ht⟩).equivFun heq
  simp only [map_zero, frameDerivative, LinearEquiv.apply_symm_apply] at hz
  have hv' : v' = -((matrixAlong C b c J t).mulVec (coefficientsAlong b c f t)) := by
    rw [matrixAlong, dite_eq_left (hUcurve ht)]
    exact eq_neg_iff_add_eq_zero.mpr hz.symm
  simpa only [hv'] using hv

/-- Existence and uniqueness in the original bundle fibers on every positive
compact path piece lying in one frame. Both endpoints use within derivatives. -/
theorem frame_parallel_exists_unique (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {l q s : ℝ} (hlq : l < q)
    (hc1 : CoordinateC1On S c (Icc l q)) (hc : ContinuousOn c (Icc l q))
    (hUcurve : MapsTo c (Icc l q) U) (hs : s ∈ Icc l q) (ξ : E (c s)) :
    ∃ f : (t : ℝ) → E (c t),
      ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc l q) ∧
      C1FieldOn (B := B) c f (Icc l q) ∧ f s = ξ ∧
      (∀ t ∈ Icc l q, HasCovariantDerivativeWithinAt C c f (Icc l q) t 0) ∧
      ∀ g : (t : ℝ) → E (c t),
        ContinuousOn (fun t => (⟨c t, g t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc l q) →
        g s = ξ →
        (∀ t ∈ Icc l q, HasCovariantDerivativeWithinAt C c g (Icc l q) t 0) →
        ∀ t ∈ Icc l q, g t = f t := by
  classical
  let A := matrixAlong C b c (Icc l q)
  let L : ℝ → Euclidean r →L[ℝ] Euclidean r := fun t =>
    -D13Unified.Ch07.LinearSystemExistence.vectorAction (A t)
  have hA := matrixAlong_continuousOn C b hc1 hc (uniqueDiffOn_Icc hlq) hUcurve
  have hL : ContinuousOn L (Icc l q) :=
    (D13Unified.Ch07.LinearSystemExistence.continuous_vectorAction.comp_continuousOn hA).neg
  obtain ⟨v, hv, hvs, hvd, hu⟩ := linear_ode_c1_extension hlq.le L hL hs
    ((b.basis ⟨c s, hUcurve hs⟩).equivFun ξ)
  let f := frameFieldAlong b c v
  have hfderiv : ∀ t ∈ Icc l q, HasCovariantDerivativeWithinAt C c f (Icc l q) t 0 := by
    intro t ht
    have hV : HasVelocityWithinAt S c (Icc l q) t
        (PiecewiseCurves.withinVelocity S c (Icc l q) t) :=
      PiecewiseCurves.withinVelocity_spec hc1 hc ht
    have hd := CurveCovariantDerivative.derivative_frame_expansion C b ht (hUcurve ht) hV (hvd t ht)
    have hzero : L t (v t) + (connectionMatrix C b ⟨c t, hUcurve ht⟩
        (PiecewiseCurves.withinVelocity S c (Icc l q) t)).mulVec (v t) = 0 := by
      simp only [L, neg_apply,
        D13Unified.Ch07.LinearSystemExistence.vectorAction_apply, A, matrixAlong,
        dite_eq_left (hUcurve ht), neg_add_cancel]
    simpa only [hzero, map_zero] using hd
  refine ⟨f, frameField_continuousOn b hc hv.continuous.continuousOn hUcurve,
    frameField_c1On b hc hv hUcurve, ?_, hfderiv, ?_⟩
  · simp only [f, frameFieldAlong, dite_eq_left (hUcurve hs), hvs,
      LinearEquiv.symm_apply_apply]
  · intro g hg hgs hgd t ht
    have hgcoef := coefficients_continuousOn b hg hUcurve
    have hginit : coefficientsAlong b c g s = (b.basis ⟨c s, hUcurve hs⟩).equivFun ξ := by
      rw [CurveCovariantDerivative.coefficientsAlong_of_mem b c g s (hUcurve hs), hgs]
    have hgode : ∀ t ∈ Icc l q,
        HasDerivWithinAt (coefficientsAlong b c g) (L t (coefficientsAlong b c g t)) (Icc l q) t := by
      intro t ht
      exact parallel_coefficients_derivative C b hc1 hc (uniqueDiffOn_Icc hlq)
        hUcurve ht (hgd t ht)
    have heq := hu (coefficientsAlong b c g) hgcoef hginit hgode ht
    apply (b.basis ⟨c t, hUcurve ht⟩).equivFun.injective
    rw [← CurveCovariantDerivative.coefficientsAlong_of_mem b c g t (hUcurve ht), heq]
    simp only [f, frameFieldAlong, dite_eq_left (hUcurve ht),
      LinearEquiv.apply_symm_apply]

theorem coefficientsAlong_congr {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) {c : ℝ → M} {f g : (t : ℝ) → E (c t)}
    {t : ℝ} (heq : f t = g t) : coefficientsAlong b c f t = coefficientsAlong b c g t := by
  classical
  simp only [coefficientsAlong]
  split_ifs <;> simp only [heq]

/-- Regularity of a field on a piece depends only on its values on that piece. -/
theorem c1FieldOn_congr {c : ℝ → M} {f g : (t : ℝ) → E (c t)} {J : Set ℝ}
    (hf : C1FieldOn (B := B) c f J) (heq : ∀ t ∈ J, g t = f t) :
    C1FieldOn (B := B) c g J := by
  intro t ht
  obtain ⟨U, hU, b, hp, v, hv, hval, he⟩ := hf t ht
  refine ⟨U, hU, b, hp, v, hv, (coefficientsAlong_congr b (heq t ht)).trans hval, ?_⟩
  apply EventuallyEq.trans _ he
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact coefficientsAlong_congr b (heq s hs)

/-- Within covariant derivatives are unchanged under equality on the closed
piece, including at an endpoint. No ambient agreement is required. -/
theorem covariantDerivative_congr {C : Connection B} {c : ℝ → M}
    {f g : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    {D : E (c t)} (hf : HasCovariantDerivativeWithinAt C c f J t D)
    (heq : ∀ t ∈ J, g t = f t) :
    HasCovariantDerivativeWithinAt C c g J t D := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, hval⟩ := hf
  refine ⟨V, hV, U, hU, b, hp, v', hv.congr_of_mem (fun s hs =>
    coefficientsAlong_congr b (heq s hs)) ht, ?_⟩
  simpa only [frameDerivative, coefficientsAlong_congr b (heq t ht)] using hval

/-- A dependent field glued at k. Its two derivatives at k belong to their
respective parameter sets and are never identified with one another. -/
noncomputable def fieldGlue {c : ℝ → M} (f g : (t : ℝ) → E (c t))
    (k t : ℝ) : E (c t) := if t ≤ k then f t else g t

theorem fieldGlue_left {c : ℝ → M} (f g : (t : ℝ) → E (c t))
    {k t : ℝ} (ht : t ≤ k) : fieldGlue f g k t = f t := ite_eq_left ht

theorem fieldGlue_right {c : ℝ → M} (f g : (t : ℝ) → E (c t))
    {k t : ℝ} (hmatch : f k = g k) (ht : k ≤ t) : fieldGlue f g k t = g t := by
  by_cases htk : t ≤ k
  · have heq : t = k := le_antisymm htk ht
    subst t
    exact (fieldGlue_left f g le_rfl).trans hmatch
  · exact ite_eq_right htk

/-- Continuous gluing only needs agreement of the fiber value at the common
endpoint. This applies even if one or both parameter intervals are singletons. -/
theorem fieldGlue_continuousOn {c : ℝ → M} (f g : (t : ℝ) → E (c t))
    {l k q : ℝ} (hlk : l ≤ k) (hkq : k ≤ q) (hmatch : f k = g k)
    (hf : ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc l k))
    (hg : ContinuousOn (fun t => (⟨c t, g t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc k q)) :
    ContinuousOn (fun t => (⟨c t, fieldGlue f g k t⟩ :
      Bundle.TotalSpace (Euclidean r) E)) (Icc l q) := by
  have hf' : ContinuousOn (fun t => (⟨c t, fieldGlue f g k t⟩ :
      Bundle.TotalSpace (Euclidean r) E)) (Icc l k) := hf.congr (fun t ht =>
        congrArg (Bundle.TotalSpace.mk (c t)) (fieldGlue_left f g ht.2))
  have hg' : ContinuousOn (fun t => (⟨c t, fieldGlue f g k t⟩ :
      Bundle.TotalSpace (Euclidean r) E)) (Icc k q) := hg.congr (fun t ht =>
        congrArg (Bundle.TotalSpace.mk (c t)) (fieldGlue_right f g hmatch ht.1))
  simpa only [Icc_union_Icc_eq_Icc hlk hkq] using hf'.union_of_isClosed hg' isClosed_Icc isClosed_Icc

/-- A within derivative restricts to any smaller parameter set. The velocity
is restricted too, so its actual one-sided interpretation is preserved. -/
theorem covariantDerivative_mono {C : Connection B} {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J K : Set ℝ} {t : ℝ} {D : E (c t)}
    (hf : HasCovariantDerivativeWithinAt C c f J t D) (hKJ : K ⊆ J) :
    HasCovariantDerivativeWithinAt C c f K t D := by
  obtain ⟨V, ⟨hc, e, he, hp, hd⟩, U, hU, b, hp', v', hv, hval⟩ := hf
  exact ⟨V, ⟨hc.mono hKJ, e, he, hp, hd.mono hKJ⟩,
    U, hU, b, hp', v', hv.mono hKJ, hval⟩

/-- Propagation on a finite ordered partition, with no strictness assumption
on its nodes. The starting point may lie anywhere in the interval. -/
theorem propagate_on_partition {m : ℕ} (node : Fin (m + 1) → ℝ)
    (hmono : Monotone node) (P : ℝ → Prop)
    (hpiece : ∀ i : Fin m, ∀ s ∈ Icc (node i.castSucc) (node i.succ),
      P s → ∀ t ∈ Icc (node i.castSucc) (node i.succ), P t)
    {s : ℝ} (hs : s ∈ Icc (node 0) (node (Fin.last m))) (hPs : P s) :
    ∀ t ∈ Icc (node 0) (node (Fin.last m)), P t := by
  induction m generalizing s with
  | zero =>
    intro t ht
    have hlast : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [hlast] at hs ht
    have hts : t = s := (le_antisymm ht.2 ht.1).trans (le_antisymm hs.2 hs.1).symm
    exact hts.symm ▸ hPs
  | succ m ih =>
    let initialNodes : Fin (m + 1) → ℝ := fun i => node i.castSucc
    have hpmono : Monotone initialNodes := fun i j hij => hmono hij
    have hppiece : ∀ i : Fin m, ∀ s ∈ Icc (initialNodes i.castSucc) (initialNodes i.succ),
        P s → ∀ t ∈ Icc (initialNodes i.castSucc) (initialNodes i.succ), P t := by
      intro i s hs hPs t ht
      exact hpiece i.castSucc s (by simpa only [initialNodes, Fin.succ_castSucc] using hs)
        hPs t (by simpa only [initialNodes, Fin.succ_castSucc] using ht)
    have hfirst : node 0 ≤ initialNodes (Fin.last m) := hmono (Fin.zero_le _)
    have hlast : initialNodes (Fin.last m) ≤ node (Fin.last (m + 1)) :=
      hmono (Fin.le_last _)
    have hPk : P (initialNodes (Fin.last m)) := by
      by_cases hsk : s ≤ initialNodes (Fin.last m)
      · exact ih initialNodes hpmono hppiece ⟨hs.1, hsk⟩ hPs _ ⟨hfirst, le_rfl⟩
      · exact hpiece (Fin.last m) s ⟨(lt_of_not_ge hsk).le, hs.2⟩ hPs _
          ⟨le_rfl, hlast⟩
    intro t ht
    by_cases htk : t ≤ initialNodes (Fin.last m)
    · exact ih initialNodes hpmono hppiece ⟨hfirst, le_rfl⟩ hPk t ⟨ht.1, htk⟩
    · exact hpiece (Fin.last m) _ ⟨le_rfl, hlast⟩ hPk t
        ⟨(lt_of_not_ge htk).le, ht.2⟩

/-- Uniqueness on a C¹ piece is global even when no single frame contains
its image. Only the competitors' continuity and actual parallel equations
are used. No existence assertion is a premise. -/
theorem parallel_unique_on_piece (C : Connection B) {c : ℝ → M}
    {l q s : ℝ} (hlq : l ≤ q)
    (hc1 : CoordinateC1On S c (Icc l q)) (hc : ContinuousOn c (Icc l q))
    {f g : (t : ℝ) → E (c t)}
    (hf : ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc l q))
    (hg : ContinuousOn (fun t => (⟨c t, g t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc l q))
    (hfd : ∀ t ∈ Icc l q, HasCovariantDerivativeWithinAt C c f (Icc l q) t 0)
    (hgd : ∀ t ∈ Icc l q, HasCovariantDerivativeWithinAt C c g (Icc l q) t 0)
    (hs : s ∈ Icc l q) (hinit : f s = g s) :
    ∀ t ∈ Icc l q, f t = g t := by
  obtain ⟨m, node, hmono, hfirst, hlast, hframe⟩ := exists_frame_subdivision B hlq hc
  have hsub (i : Fin m) : Icc (node i.castSucc) (node i.succ) ⊆ Icc l q := by
    intro t ht
    have hleft := hmono (Fin.zero_le i.castSucc)
    have hright := hmono (Fin.le_last i.succ)
    rw [hfirst] at hleft
    rw [hlast] at hright
    exact ⟨hleft.trans ht.1, ht.2.trans hright⟩
  have hprop : ∀ i : Fin m, ∀ s ∈ Icc (node i.castSucc) (node i.succ),
      f s = g s → ∀ t ∈ Icc (node i.castSucc) (node i.succ), f t = g t := by
    intro i s hs hinit t ht
    rcases lt_or_eq_of_le (hmono (Fin.castSucc_le_succ i)) with hpos | heq
    · obtain ⟨U, hU, b, hUcurve⟩ := hframe i
      obtain ⟨z, _, _, _, _, hu⟩ := frame_parallel_exists_unique C b hpos
        (PiecewiseCurves.CoordinateC1On.mono hc1 (hsub i)) (hc.mono (hsub i)) hUcurve hs (g s)
      exact (hu f (hf.mono (hsub i)) hinit
        (fun x hx => covariantDerivative_mono (hfd x (hsub i hx)) (hsub i)) t ht).trans
        (hu g (hg.mono (hsub i)) rfl
          (fun x hx => covariantDerivative_mono (hgd x (hsub i hx)) (hsub i)) t ht).symm
    · have hts : t = s := by rw [heq, Icc_self] at hs ht; exact ht.trans hs.symm
      exact hts.symm ▸ hinit
  simpa only [hfirst, hlast] using
    propagate_on_partition node hmono (fun t => f t = g t) hprop
      (show s ∈ Icc (node 0) (node (Fin.last m)) by simpa only [hfirst, hlast] using hs) hinit

/-- Global uniqueness along the original piecewise C¹ path. This includes
corners, repeated partition nodes, and an arbitrary initial time. -/
theorem parallel_ext (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {f g : (t : ℝ) → E (c t)} (hf : ParallelField C c f) (hg : ParallelField C c g)
    (s : Icc a b) (hinit : f s = g s) : ∀ t ∈ Icc a b, f t = g t := by
  have hsub (i : Fin c.pieces) :
      Icc (c.node i.castSucc) (c.node i.succ) ⊆ Icc a b := fun t ht =>
    ⟨(PiecewiseCurves.node_mem c i.castSucc).1.trans ht.1,
      ht.2.trans (PiecewiseCurves.node_mem c i.succ).2⟩
  have hprop : ∀ i : Fin c.pieces, ∀ s ∈ Icc (c.node i.castSucc) (c.node i.succ),
      f s = g s → ∀ t ∈ Icc (c.node i.castSucc) (c.node i.succ), f t = g t := by
    intro i s hs hinit
    rcases lt_or_eq_of_le (c.monotone_node (Fin.castSucc_le_succ i)) with hpos | heq
    · exact parallel_unique_on_piece C hpos.le (c.regular i) (c.continuousOn.mono (hsub i))
        (hf.1.mono (hsub i)) (hg.1.mono (hsub i)) (hf.2.2 i hpos) (hg.2.2 i hpos) hs hinit
    · intro t ht
      have hts : t = s := by rw [heq, Icc_self] at hs ht; exact ht.trans hs.symm
      exact hts.symm ▸ hinit
  simpa only [c.first_node, c.last_node] using
    propagate_on_partition c.node c.monotone_node (fun t => f t = g t) hprop
      (show s.val ∈ Icc (c.node 0) (c.node (Fin.last c.pieces)) by
        simpa only [c.first_node, c.last_node] using s.property) hinit

@[simp] theorem selectedField_initial (C : Connection B) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) (s : Icc a b) (ξ : E (c s)) :
    selectedField C c s ξ s = ξ := by
  classical
  unfold selectedField
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · simp only [seedField, dite_true]

/-- C¹ on a singleton needs no artificial derivative constraint. -/
theorem c1FieldOn_subsingleton {c : ℝ → M} (f : (t : ℝ) → E (c t))
    {J : Set ℝ} (hJ : J.Subsingleton) : C1FieldOn (B := B) c f J := by
  intro t ht
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
  refine ⟨U, hU, b, hp, fun _ => coefficientsAlong b c f t, contDiffAt_const, rfl, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hJ hs ht]

/-- Complete existence and uniqueness for a singleton parameter interval,
including partitions with no pieces or arbitrarily many repeated nodes. -/
theorem parallel_exists_unique_singleton (C : Connection B) {a : ℝ}
    (c : PiecewiseC1Curve S a a) (s : Icc a a) (ξ : E (c s)) :
    ∃ f : (t : ℝ) → E (c t), ParallelField C c f ∧ f s = ξ ∧
      ∀ g : (t : ℝ) → E (c t), ParallelField C c g → g s = ξ →
        ∀ t ∈ Icc a a, g t = f t := by
  classical
  let f := seedField c s ξ
  have hinit : f s = ξ := by simp only [f, seedField, dite_true]
  have hnode (i : Fin (c.pieces + 1)) : c.node i = a :=
    le_antisymm (PiecewiseCurves.node_mem c i).2 (PiecewiseCurves.node_mem c i).1
  refine ⟨f, ⟨?_, ?_, ?_⟩, hinit, ?_⟩
  · exact (show (Icc a a).Subsingleton by simp only [Icc_self]; exact subsingleton_singleton).continuousOn _
  · intro i
    rw [hnode, hnode]
    exact c1FieldOn_subsingleton f (show (Icc a a).Subsingleton by simp only [Icc_self]; exact subsingleton_singleton)
  · intro i hi
    simp only [hnode, lt_self_iff_false] at hi
  · intro g _ hgs t ht
    have hts : t = s.val := (show (Icc a a).Subsingleton by simp only [Icc_self]; exact subsingleton_singleton) ht s.property
    subst t
    exact hgs.trans hinit.symm

@[simp] theorem coefficientsAlong_zero {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (c : ℝ → M) (t : ℝ) :
    coefficientsAlong b c (fun _ => 0) t = 0 := by
  classical
  simp only [coefficientsAlong]
  split_ifs <;> simp only [map_zero]

/-- The zero field is parallel for every connection, on the original complete
partition. This also handles repeated nodes without any velocity identification. -/
theorem zero_parallelField (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b) :
    ParallelField C c (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (B.zero_smooth (c t)).1.comp_continuousWithinAt (f := (c : ℝ → M))
      (c.continuousOn t ht)
  · intro i t ht
    obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
    exact ⟨U, hU, b, hp, fun _ => 0, contDiffAt_const, coefficientsAlong_zero b c t,
      Eventually.of_forall (coefficientsAlong_zero b c)⟩
  · intro i _ t ht
    have hsub : Icc (c.node i.castSucc) (c.node i.succ) ⊆ Icc a b := fun _ hs =>
      ⟨(PiecewiseCurves.node_mem c i.castSucc).1.trans hs.1,
        hs.2.trans (PiecewiseCurves.node_mem c i.succ).2⟩
    obtain ⟨V, hV⟩ := PiecewiseCurves.CoordinateC1On.exists_withinVelocity
      (c.regular i) (c.continuousOn.mono hsub) ht
    obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
    refine ⟨V, hV, U, hU, b, hp, 0, ?_, ?_⟩
    · simpa only [funext (coefficientsAlong_zero b c)] using
        hasDerivWithinAt_const t (Icc (c.node i.castSucc) (c.node i.succ)) (0 : Euclidean r)
    · simp only [frameDerivative, coefficientsAlong_zero, Matrix.mulVec_zero, add_zero, map_zero]

/-- A rank-zero bundle has singleton actual fibers. -/
theorem fiber_subsingleton_of_rank_zero (B : SmoothVectorBundle S r ι E) (hr : r = 0) (p : M) : Subsingleton (E p) := by
  subst r
  obtain ⟨i, hi⟩ := B.covers p
  exact ⟨fun x y => (B.fiberCoordinates i p hi).injective (Subsingleton.elim _ _)⟩

/-- Complete global IVP for rank zero, without a nonconstant-path exclusion. -/
theorem parallel_exists_unique_rank_zero (hr : r = 0) (C : Connection B)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (s : Icc a b) (ξ : E (c s)) :
    ∃ f : (t : ℝ) → E (c t), ParallelField C c f ∧ f s = ξ ∧
      ∀ g : (t : ℝ) → E (c t), ParallelField C c g → g s = ξ →
        ∀ t ∈ Icc a b, g t = f t := by
  letI (p : M) : Subsingleton (E p) := fiber_subsingleton_of_rank_zero B hr p
  exact ⟨fun _ => 0, zero_parallelField C c, Subsingleton.elim _ _,
    fun g _ _ t _ => Subsingleton.elim _ _⟩

/-- Every relative neighborhood in a nondegenerate compact interval contains
an actual positive compact subinterval which is itself a relative neighborhood. -/
theorem exists_compact_subinterval {l q t : ℝ} (hlq : l < q)
    (ht : t ∈ Icc l q) {A : Set ℝ} (hA : A ∈ 𝓝[Icc l q] t) :
    ∃ l' q' : ℝ, l' < q' ∧ t ∈ Icc l' q' ∧
      Icc l' q' ⊆ Icc l q ∧ Icc l' q' ⊆ A ∧ Icc l' q' ∈ 𝓝[Icc l q] t := by
  obtain ⟨W, hW, hWA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
  obtain ⟨e, d, ⟨het, htd⟩, hedW⟩ := mem_nhds_iff_exists_Ioo_subset.mp hW
  let e' := (e + t) / 2
  let d' := (t + d) / 2
  have he't : e' < t := by dsimp [e']; linarith
  have htd' : t < d' := by dsimp [d']; linarith
  have hee' : e < e' := by dsimp [e']; linarith
  have hd'd : d' < d := by dsimp [d']; linarith
  have hpos : max l e' < min q d' := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hlq, ht.1.trans_lt htd'⟩, ⟨he't.trans_le ht.2, he't.trans htd'⟩⟩
  refine ⟨max l e', min q d', hpos,
    ⟨max_le ht.1 he't.le, le_min ht.2 htd'.le⟩, ?_, ?_, ?_⟩
  · exact Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  · intro x hx
    apply hWA
    exact ⟨hedW ⟨hee'.trans_le ((le_max_right _ _).trans hx.1),
        (hx.2.trans (min_le_right _ _)).trans_lt hd'd⟩,
      (le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩
  · filter_upwards [(show Ioo e' d' ∈ 𝓝[Icc l q] t from nhdsWithin_le_nhds (Ioo_mem_nhds he't htd')),
      self_mem_nhdsWithin] with x hx hxJ
    exact ⟨max_le hxJ.1 hx.1.le, le_min hxJ.2 hx.2.le⟩

/-- A continuous solution of the actual parallel equation is automatically C¹
in the precise coefficient-extension sense, including both endpoints. This
uses a local IVP and uniqueness, rather than assuming an ambient extension of
the manifold-valued curve. -/
theorem c1FieldOn_of_parallel_equation (C : Connection B) {c : ℝ → M}
    {l q : ℝ} (hlq : l < q) (hc1 : CoordinateC1On S c (Icc l q))
    (hc : ContinuousOn c (Icc l q)) {f : (t : ℝ) → E (c t)}
    (hf : ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc l q))
    (hfd : ∀ t ∈ Icc l q, HasCovariantDerivativeWithinAt C c f (Icc l q) t 0) :
    C1FieldOn (B := B) c f (Icc l q) := by
  intro t ht
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
  obtain ⟨l', q', hpos, htK, hKJ, hKU, hKn⟩ := exists_compact_subinterval hlq ht
    ((hc t ht).eventually (hU.mem_nhds hp))
  obtain ⟨z, hz, hz1, hzt, hzd, hu⟩ := frame_parallel_exists_unique C b hpos
    (PiecewiseCurves.CoordinateC1On.mono hc1 hKJ) (hc.mono hKJ) hKU htK (f t)
  have heq : ∀ x ∈ Icc l' q', f x = z x :=
    hu f (hf.mono hKJ) rfl (fun x hx => covariantDerivative_mono (hfd x (hKJ hx)) hKJ)
  obtain ⟨W, hW, b', hp', v, hv, hval, he⟩ := c1FieldOn_congr hz1 heq t htK
  refine ⟨W, hW, b', hp', v, hv, hval, ?_⟩
  have hfilters : 𝓝[Icc l' q'] t = 𝓝[Icc l q] t := by
    simpa only [inter_eq_left.mpr hKJ] using nhdsWithin_inter_of_mem hKn
  rwa [hfilters] at he

/-- Local coefficients of a continuous actual field are continuous wherever
the frame is defined. No global containment in the frame domain is needed. -/
theorem coefficients_continuousWithinAt {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) {c : ℝ → M} {f : (t : ℝ) → E (c t)}
    {J : Set ℝ} {t : ℝ} (hp : c t ∈ U)
    (hf : ContinuousWithinAt (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) J t) :
    ContinuousWithinAt (coefficientsAlong b c f) J t := by
  have hs := (SmoothManifolds.Frames.frameAnalysis_smooth B U hU b ⟨c t, f t⟩ hp).1
  have h := (continuous_snd.continuousAt.comp hs).comp_continuousWithinAt
    (f := fun s : ℝ => (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean r) E)) hf
  exact h

/-- Conversely, continuous local coefficients and a continuous base curve
give continuity of the field in the actual total space. -/
theorem field_continuousWithinAt_of_coefficients {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) {c : ℝ → M} {f : (t : ℝ) → E (c t)}
    {J : Set ℝ} {t : ℝ} (hp : c t ∈ U) (hc : ContinuousWithinAt c J t)
    (hf : ContinuousWithinAt (coefficientsAlong b c f) J t) :
    ContinuousWithinAt (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) J t := by
  have hs := (SmoothManifolds.Frames.frameSynthesis_smooth B U hU b
    (c t, coefficientsAlong b c f t) ⟨hp, mem_univ _⟩).1
  have h := hs.comp_continuousWithinAt
    (f := fun s : ℝ => (c s, coefficientsAlong b c f s)) (hc.prodMk hf)
  have heq : (fun s => SmoothManifolds.FrameData.frameSynthesis b
      (c s, coefficientsAlong b c f s)) =ᶠ[𝓝[J] t]
      (fun s => (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean r) E)) := by
    filter_upwards [hc.eventually (hU.mem_nhds hp)] with s hsU
    rw [SmoothManifolds.Frames.frameSynthesis_of_mem B U hU b
      (c s, coefficientsAlong b c f s) hsU]
    simp only [CurveCovariantDerivative.coefficientsAlong_of_mem b c f s hsU,
      SmoothManifolds.FrameData.frameLinearEquiv, LinearEquiv.symm_apply_apply]
  have hval : SmoothManifolds.FrameData.frameSynthesis b (c t, coefficientsAlong b c f t) =
      (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E) := by
    rw [SmoothManifolds.Frames.frameSynthesis_of_mem B U hU b
      (c t, coefficientsAlong b c f t) hp]
    simp only [CurveCovariantDerivative.coefficientsAlong_of_mem b c f t hp,
      SmoothManifolds.FrameData.frameLinearEquiv, LinearEquiv.symm_apply_apply]
  exact h.congr_of_eventuallyEq heq.symm hval.symm

include B in
/-- Superposition preserves actual total-space continuity. -/
theorem continuousOn_field_add {c : ℝ → M} {f g : (t : ℝ) → E (c t)} {J : Set ℝ}
    (hc : ContinuousOn c J)
    (hf : ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) J)
    (hg : ContinuousOn (fun t => (⟨c t, g t⟩ : Bundle.TotalSpace (Euclidean r) E)) J) :
    ContinuousOn (fun t => (⟨c t, f t + g t⟩ : Bundle.TotalSpace (Euclidean r) E)) J := by
  intro t ht
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
  apply field_continuousWithinAt_of_coefficients b hp (hc t ht)
  rw [CurveCovariantDerivative.coefficients_add]
  exact (coefficients_continuousWithinAt b hp (hf t ht)).add
    (coefficients_continuousWithinAt b hp (hg t ht))

include B in
theorem continuousOn_field_smul {c : ℝ → M} {f : (t : ℝ) → E (c t)} {J : Set ℝ}
    (hc : ContinuousOn c J)
    (hf : ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) J) (k : ℝ) :
    ContinuousOn (fun t => (⟨c t, k • f t⟩ : Bundle.TotalSpace (Euclidean r) E)) J := by
  intro t ht
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
  apply field_continuousWithinAt_of_coefficients b hp (hc t ht)
  rw [CurveCovariantDerivative.coefficients_smul]
  exact (coefficients_continuousWithinAt b hp (hf t ht)).const_smul k

/-- Parallel fields form a real vector space. At an original corner both
one-sided zero equations are retained separately. -/
theorem parallelField_add (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {f g : (t : ℝ) → E (c t)} (hf : ParallelField C c f) (hg : ParallelField C c g) :
    ParallelField C c (fun t => f t + g t) := by
  have hc := continuousOn_field_add (B := B) c.continuousOn hf.1 hg.1
  have hd : ∀ i : Fin c.pieces, c.node i.castSucc < c.node i.succ →
      ∀ t ∈ Icc (c.node i.castSucc) (c.node i.succ),
      HasCovariantDerivativeWithinAt C c (fun t => f t + g t)
        (Icc (c.node i.castSucc) (c.node i.succ)) t 0 := by
    intro i hi t ht
    simpa only [zero_add] using CurveCovariantDerivative.derivative_add C ht
      (uniqueDiffOn_Icc hi t ht) (hf.2.2 i hi t ht) (hg.2.2 i hi t ht)
  refine ⟨hc, ?_, hd⟩
  intro i
  rcases lt_or_eq_of_le (c.monotone_node (Fin.castSucc_le_succ i)) with hi | heq
  · have hsub : Icc (c.node i.castSucc) (c.node i.succ) ⊆ Icc a b := fun t ht =>
      ⟨(PiecewiseCurves.node_mem c i.castSucc).1.trans ht.1,
        ht.2.trans (PiecewiseCurves.node_mem c i.succ).2⟩
    exact c1FieldOn_of_parallel_equation C hi (c.regular i) (c.continuousOn.mono hsub)
      (hc.mono hsub) (hd i hi)
  · rw [heq, Icc_self]
    exact c1FieldOn_subsingleton _ (subsingleton_singleton)

theorem parallelField_smul (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {f : (t : ℝ) → E (c t)} (hf : ParallelField C c f) (k : ℝ) :
    ParallelField C c (fun t => k • f t) := by
  have hc := continuousOn_field_smul (B := B) c.continuousOn hf.1 k
  have hd : ∀ i : Fin c.pieces, c.node i.castSucc < c.node i.succ →
      ∀ t ∈ Icc (c.node i.castSucc) (c.node i.succ),
      HasCovariantDerivativeWithinAt C c (fun t => k • f t)
        (Icc (c.node i.castSucc) (c.node i.succ)) t 0 := by
    intro i hi t ht
    simpa only [zero_smul, smul_zero, zero_add] using
      CurveCovariantDerivative.derivative_smul C (hf.2.2 i hi t ht)
        (hasDerivWithinAt_const t (Icc (c.node i.castSucc) (c.node i.succ)) k)
  refine ⟨hc, ?_, hd⟩
  intro i
  rcases lt_or_eq_of_le (c.monotone_node (Fin.castSucc_le_succ i)) with hi | heq
  · have hsub : Icc (c.node i.castSucc) (c.node i.succ) ⊆ Icc a b := fun t ht =>
      ⟨(PiecewiseCurves.node_mem c i.castSucc).1.trans ht.1,
        ht.2.trans (PiecewiseCurves.node_mem c i.succ).2⟩
    exact c1FieldOn_of_parallel_equation C hi (c.regular i) (c.continuousOn.mono hsub)
      (hc.mono hsub) (hd i hi)
  · rw [heq, Icc_self]
    exact c1FieldOn_subsingleton _ (subsingleton_singleton)

theorem parallel_coefficients_derivative_velocity (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    (hf : HasCovariantDerivativeWithinAt C c f J t 0) :
    HasDerivWithinAt (coefficientsAlong b c f)
      (-((connectionMatrix C b ⟨c t, hp⟩ V).mulVec (coefficientsAlong b c f t))) J t := by
  obtain ⟨v', hv⟩ := CurveCovariantDerivative.exists_coefficients_deriv C ht hf b hp
  have heq := CurveCovariantDerivative.local_formula C ht hJ hf b hp hV hv
  have hz := congrArg (b.basis ⟨c t, hp⟩).equivFun heq
  simp only [map_zero, frameDerivative, LinearEquiv.apply_symm_apply] at hz
  have hv' : v' = -((connectionMatrix C b ⟨c t, hp⟩ V).mulVec
      (coefficientsAlong b c f t)) := eq_neg_iff_add_eq_zero.mpr hz.symm
  simpa only [hv'] using hv

theorem hasVelocityWithinAt_mono {c : ℝ → M} {J K : Set ℝ} {t : ℝ}
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    (hKJ : K ⊆ J) : HasVelocityWithinAt S c K t V := by
  obtain ⟨hc, e, he, hp, hd⟩ := hV
  exact ⟨hc.mono hKJ, e, he, hp, hd.mono hKJ⟩

theorem parallel_equation_union (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {l k q : ℝ}
    (hlk : l ≤ k) (hkq : k ≤ q) (hlq : l < q)
    (hc1 : CoordinateC1On S c (Icc l q)) (hc : ContinuousOn c (Icc l q))
    (hfd : l < k → ∀ t ∈ Icc l k, HasCovariantDerivativeWithinAt C c f (Icc l k) t 0)
    (hgd : k < q → ∀ t ∈ Icc k q, HasCovariantDerivativeWithinAt C c f (Icc k q) t 0) :
    ∀ t ∈ Icc l q, HasCovariantDerivativeWithinAt C c f (Icc l q) t 0 := by
  by_cases hlk' : l < k
  · by_cases hkq' : k < q
    · intro t ht
      have hV := PiecewiseCurves.withinVelocity_spec hc1 hc ht
      let V := PiecewiseCurves.withinVelocity S c (Icc l q) t
      obtain ⟨U, hU, hp, hb⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
      let b := Classical.choice hb
      let d := -((connectionMatrix C b ⟨c t, hp⟩ V).mulVec (coefficientsAlong b c f t))
      have hd (a b' : ℝ) (hab : a < b') (hsub : Icc a b' ⊆ Icc l q)
          (hdf : ∀ t ∈ Icc a b', HasCovariantDerivativeWithinAt C c f (Icc a b') t 0) :
          HasDerivWithinAt (coefficientsAlong b c f) d (Icc a b') t := by
        by_cases ht' : t ∈ Icc a b'
        · exact parallel_coefficients_derivative_velocity C b ht' (uniqueDiffOn_Icc hab t ht')
            hp (hasVelocityWithinAt_mono hV hsub) (hdf t ht')
        · apply HasFDerivWithinAt.of_notMem_closure
          simpa only [closure_Icc] using ht'
      have hd1 := hd l k hlk' (Icc_subset_Icc le_rfl hkq) (hfd hlk')
      have hd2 := hd k q hkq' (Icc_subset_Icc hlk le_rfl) (hgd hkq')
      have hd' : HasDerivWithinAt (coefficientsAlong b c f) d (Icc l q) t := by
        simpa only [Icc_union_Icc_eq_Icc hlk hkq] using hd1.union hd2
      refine ⟨V, hV, U, hU, b, hp, d, hd', ?_⟩
      simp only [frameDerivative, d, neg_add_cancel, map_zero]
    · have hkqeq : k = q := le_antisymm hkq (not_lt.mp hkq')
      subst q
      exact hfd hlk'
  · have hlkeq : l = k := le_antisymm hlk (not_lt.mp hlk')
    subst k
    exact hgd hlq
theorem parallel_equation_on_partition (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {m : ℕ} (node : Fin (m + 1) → ℝ)
    (hmono : Monotone node) (hpos : node 0 < node (Fin.last m))
    (hc1 : CoordinateC1On S c (Icc (node 0) (node (Fin.last m))))
    (hc : ContinuousOn c (Icc (node 0) (node (Fin.last m))))
    (hfd : ∀ i : Fin m, node i.castSucc < node i.succ →
      ∀ t ∈ Icc (node i.castSucc) (node i.succ),
        HasCovariantDerivativeWithinAt C c f (Icc (node i.castSucc) (node i.succ)) t 0) :
    ∀ t ∈ Icc (node 0) (node (Fin.last m)),
      HasCovariantDerivativeWithinAt C c f (Icc (node 0) (node (Fin.last m))) t 0 := by
  induction m with
  | zero => exact (lt_irrefl _ hpos).elim
  | succ m ih =>
    let initialNodes : Fin (m + 1) → ℝ := fun i => node i.castSucc
    have hpmono : Monotone initialNodes := fun i j hij => hmono hij
    have hfirst : node 0 ≤ initialNodes (Fin.last m) := hmono (Fin.zero_le _)
    have hlast : initialNodes (Fin.last m) ≤ node (Fin.last (m + 1)) :=
      hmono (Fin.le_last _)
    apply parallel_equation_union C hfirst hlast hpos hc1 hc
    · intro hpos'
      apply ih initialNodes hpmono hpos'
      · exact PiecewiseCurves.CoordinateC1On.mono hc1 (Icc_subset_Icc le_rfl hlast)
      · exact hc.mono (Icc_subset_Icc le_rfl hlast)
      · intro i hlt t ht
        exact hfd i.castSucc
          (by simpa only [initialNodes, Fin.succ_castSucc] using hlt) t
          (by simpa only [initialNodes, Fin.succ_castSucc] using ht)
    · intro hpos' t ht
      exact hfd (Fin.last m) hpos' t ht


/-- A scalar function with zero actual derivative on every positive closed
piece has one value throughout the finite partition. -/
theorem scalar_constant_on_partition {m : ℕ} (node : Fin (m + 1) → ℝ)
    (hmono : Monotone node) (φ : ℝ → ℝ)
    (hd : ∀ i : Fin m, node i.castSucc < node i.succ →
      ∀ t ∈ Icc (node i.castSucc) (node i.succ),
        HasDerivWithinAt φ 0 (Icc (node i.castSucc) (node i.succ)) t)
    (s : ℝ) (hs : s ∈ Icc (node 0) (node (Fin.last m))) :
    ∀ t ∈ Icc (node 0) (node (Fin.last m)), φ t = φ s := by
  apply propagate_on_partition node hmono (fun t => φ t = φ s) _ hs rfl
  intro i x hx hφx t ht
  rcases lt_or_eq_of_le (hmono (Fin.castSucc_le_succ i)) with hi | heq
  · have hc : ∀ y ∈ Icc (node i.castSucc) (node i.succ), φ y = φ (node i.castSucc) :=
      constant_of_derivWithin_zero (fun y hy => (hd i hi y hy).differentiableWithinAt)
        (fun y hy => (hd i hi y ⟨hy.1, hy.2.le⟩).derivWithin
          (uniqueDiffOn_Icc hi y ⟨hy.1, hy.2.le⟩))
    exact ((hc t ht).trans (hc x hx).symm).trans hφx
  · have htx : t = x := by rw [heq, Icc_self] at hx ht; exact ht.trans hx.symm
    exact htx.symm ▸ hφx

/-- Finite gluing of arbitrary interval-local field predicates, with arbitrary
initial time and repeated partition nodes. -/
theorem field_exists_on_partition {c : ℝ → M} {m : ℕ}
    (node : Fin (m + 1) → ℝ) (hmono : Monotone node)
    (R : ℝ → ℝ → ((t : ℝ) → E (c t)) → Prop)
    (hcongr : ∀ (l q : ℝ) (f g : (t : ℝ) → E (c t)),
      (∀ t ∈ Icc l q, g t = f t) → R l q f → R l q g)
    (hlocal : ∀ i : Fin m, ∀ s ∈ Icc (node i.castSucc) (node i.succ),
      ∀ ξ : E (c s), ∃ f : (t : ℝ) → E (c t),
        ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E))
          (Icc (node i.castSucc) (node i.succ)) ∧
        f s = ξ ∧ R (node i.castSucc) (node i.succ) f)
    (s : ℝ) (hs : s ∈ Icc (node 0) (node (Fin.last m))) (ξ : E (c s)) :
    ∃ f : (t : ℝ) → E (c t),
      ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E))
        (Icc (node 0) (node (Fin.last m))) ∧ f s = ξ ∧
      ∀ i : Fin m, R (node i.castSucc) (node i.succ) f := by
  classical
  induction m generalizing s with
  | zero =>
    let f : (t : ℝ) → E (c t) := fun t => if ht : t = s then ht.symm ▸ ξ else 0
    refine ⟨f, ?_, ?_, fun i => Fin.elim0 i⟩
    · exact (show (Icc (node 0) (node (Fin.last 0))).Subsingleton by
        change (Icc (node 0) (node 0)).Subsingleton
        simpa only [Icc_self] using subsingleton_singleton).continuousOn _
    · simp only [f, dite_true]
  | succ m ih =>
    let initialNodes : Fin (m + 1) → ℝ := fun i => node i.castSucc
    let k := initialNodes (Fin.last m)
    have hpmono : Monotone initialNodes := fun i j hij => hmono hij
    have hppiece : ∀ i : Fin m, ∀ s ∈ Icc (initialNodes i.castSucc) (initialNodes i.succ),
        ∀ ξ : E (c s), ∃ f : (t : ℝ) → E (c t),
          ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E))
            (Icc (initialNodes i.castSucc) (initialNodes i.succ)) ∧
          f s = ξ ∧ R (initialNodes i.castSucc) (initialNodes i.succ) f := by
      intro i s hs ξ
      simpa only [initialNodes, Fin.succ_castSucc] using
        hlocal i.castSucc s (by simpa only [initialNodes, Fin.succ_castSucc] using hs) ξ
    have hfirst : node 0 ≤ k := hmono (Fin.zero_le _)
    have hlast : k ≤ node (Fin.last (m + 1)) := hmono (Fin.le_last _)
    have hparts : ∃ f g : (t : ℝ) → E (c t),
        ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc (node 0) k) ∧
        ContinuousOn (fun t => (⟨c t, g t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc k (node (Fin.last (m + 1)))) ∧
        (∀ i : Fin m, R (initialNodes i.castSucc) (initialNodes i.succ) f) ∧
        R k (node (Fin.last (m + 1))) g ∧ f k = g k ∧ fieldGlue f g k s = ξ := by
      by_cases hsk : s ≤ k
      · obtain ⟨f, hf, hfs, hfR⟩ := ih initialNodes hpmono hppiece s ⟨hs.1, hsk⟩ ξ
        obtain ⟨g, hg, hgk, hgR⟩ := hlocal (Fin.last m) k ⟨le_rfl, hlast⟩ (f k)
        exact ⟨f, g, hf, hg, hfR, hgR, hgk.symm, (fieldGlue_left f g hsk).trans hfs⟩
      · obtain ⟨g, hg, hgs, hgR⟩ := hlocal (Fin.last m) s ⟨(lt_of_not_ge hsk).le, hs.2⟩ ξ
        obtain ⟨f, hf, hfk, hfR⟩ := ih initialNodes hpmono hppiece k ⟨hfirst, le_rfl⟩ (g k)
        exact ⟨f, g, hf, hg, hfR, hgR, hfk,
          (fieldGlue_right f g hfk (lt_of_not_ge hsk).le).trans hgs⟩
    obtain ⟨f, g, hf, hg, hfR, hgR, hmatch, hinit⟩ := hparts
    refine ⟨fieldGlue f g k, fieldGlue_continuousOn f g hfirst hlast hmatch hf hg, hinit, ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_)
    · exact hcongr k (node (Fin.last (m + 1))) g (fieldGlue f g k)
        (fun t ht => fieldGlue_right f g hmatch ht.1) hgR
    · apply hcongr _ _ f (fieldGlue f g k) _ (hfR i)
      intro t ht
      apply fieldGlue_left
      exact ht.2.trans (hpmono (Fin.le_last i.succ))


/-- Existence with parallel equations on an arbitrary finite subdivision
whose subpieces each lie in one frame. Repeated nodes carry no equation. -/
theorem frame_subdivision_parallel_exists (C : Connection B)
    {c : ℝ → M} {l q s : ℝ} (hlq : l ≤ q)
    (hc1 : CoordinateC1On S c (Icc l q)) (hc : ContinuousOn c (Icc l q))
    {m : ℕ} (node : Fin (m + 1) → ℝ) (hmono : Monotone node)
    (hfirst : node 0 = l) (hlast : node (Fin.last m) = q)
    (hframe : ∀ i : Fin m, ∃ (U : Set M) (hU : IsOpen U) (b : LocalFrame B U hU),
      MapsTo c (Icc (node i.castSucc) (node i.succ)) U)
    (hs : s ∈ Icc l q) (ξ : E (c s)) :
    ∃ f : (t : ℝ) → E (c t),
      ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc l q) ∧
      f s = ξ ∧ ∀ i : Fin m, node i.castSucc < node i.succ →
        ∀ t ∈ Icc (node i.castSucc) (node i.succ),
          HasCovariantDerivativeWithinAt C c f (Icc (node i.castSucc) (node i.succ)) t 0 := by
  classical
  let R : ℝ → ℝ → ((t : ℝ) → E (c t)) → Prop := fun x y f =>
    x < y → ∀ t ∈ Icc x y, HasCovariantDerivativeWithinAt C c f (Icc x y) t 0
  have hcongr : ∀ (x y : ℝ) (f g : (t : ℝ) → E (c t)),
      (∀ t ∈ Icc x y, g t = f t) → R x y f → R x y g := by
    intro x y f g heq hf hxy t ht
    exact covariantDerivative_congr ht (hf hxy t ht) heq
  have hsub (i : Fin m) : Icc (node i.castSucc) (node i.succ) ⊆ Icc l q := by
    intro t ht
    have hleft := hmono (Fin.zero_le i.castSucc)
    have hright := hmono (Fin.le_last i.succ)
    rw [hfirst] at hleft
    rw [hlast] at hright
    exact ⟨hleft.trans ht.1, ht.2.trans hright⟩
  have hlocal : ∀ i : Fin m, ∀ s ∈ Icc (node i.castSucc) (node i.succ),
      ∀ ξ : E (c s), ∃ f : (t : ℝ) → E (c t),
        ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E))
          (Icc (node i.castSucc) (node i.succ)) ∧
        f s = ξ ∧ R (node i.castSucc) (node i.succ) f := by
    intro i s hs ξ
    rcases lt_or_eq_of_le (hmono (Fin.castSucc_le_succ i)) with hpos | heq
    · obtain ⟨U, hU, b, hUcurve⟩ := hframe i
      obtain ⟨f, hf, _, hinit, hfd, _⟩ := frame_parallel_exists_unique C b hpos
        (PiecewiseCurves.CoordinateC1On.mono hc1 (hsub i)) (hc.mono (hsub i)) hUcurve hs ξ
      exact ⟨f, hf, hinit, fun _ => hfd⟩
    · let f : (t : ℝ) → E (c t) := fun t => if ht : t = s then ht.symm ▸ ξ else 0
      refine ⟨f, ?_, ?_, ?_⟩
      · exact (show (Icc (node i.castSucc) (node i.succ)).Subsingleton by
          rw [heq, Icc_self]; exact subsingleton_singleton).continuousOn _
      · simp only [f, dite_true]
      · intro hpos
        exact (lt_irrefl _ (heq ▸ hpos)).elim
  obtain ⟨f, hf, hinit, hfd⟩ := field_exists_on_partition node hmono R hcongr hlocal s
    (by simpa only [hfirst, hlast] using hs) ξ
  exact ⟨f, by simpa only [hfirst, hlast] using hf, hinit, hfd⟩

/-- A complete parallel IVP on a smooth compact path piece, without a
single-frame hypothesis. Artificial frame subdivision points impose no new
conditions on the original field regularity. -/
theorem parallel_exists_on_piece (C : Connection B)
    {c : ℝ → M} {l q s : ℝ} (hlq : l ≤ q)
    (hc1 : CoordinateC1On S c (Icc l q)) (hc : ContinuousOn c (Icc l q))
    (hs : s ∈ Icc l q) (ξ : E (c s)) :
    ∃ f : (t : ℝ) → E (c t),
      ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc l q) ∧
      C1FieldOn (B := B) c f (Icc l q) ∧ f s = ξ ∧
      (l < q → ∀ t ∈ Icc l q, HasCovariantDerivativeWithinAt C c f (Icc l q) t 0) := by
  obtain ⟨m, node, hmono, hfirst, hlast, hframe⟩ := exists_frame_subdivision B hlq hc
  obtain ⟨f, hf, hinit, hfd⟩ := frame_subdivision_parallel_exists C hlq hc1 hc
    node hmono hfirst hlast hframe hs ξ
  have hfdglobal : l < q → ∀ t ∈ Icc l q,
      HasCovariantDerivativeWithinAt C c f (Icc l q) t 0 := by
    intro hpos
    simpa only [hfirst, hlast] using parallel_equation_on_partition C node hmono
      (by simpa only [hfirst, hlast] using hpos)
      (by simpa only [hfirst, hlast] using hc1)
      (by simpa only [hfirst, hlast] using hc) hfd
  refine ⟨f, hf, ?_, hinit, hfdglobal⟩
  rcases lt_or_eq_of_le hlq with hpos | heq
  · exact c1FieldOn_of_parallel_equation C hpos hc1 hc hf (hfdglobal hpos)
  · apply c1FieldOn_subsingleton f
    rw [heq, Icc_self]
    exact subsingleton_singleton


/-- Global existence and uniqueness along the original piecewise C¹ path.
The two derivatives at a genuine corner are retained on their own pieces. -/
theorem parallel_ivp (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (s : Icc a b) (ξ : E (c s)) :
    ∃ f : (t : ℝ) → E (c t), ParallelField C c f ∧ f s = ξ ∧
      ∀ g : (t : ℝ) → E (c t), ParallelField C c g → g s = ξ →
        ∀ t ∈ Icc a b, g t = f t := by
  let R : ℝ → ℝ → ((t : ℝ) → E (c t)) → Prop := fun x y f =>
    C1FieldOn (B := B) c f (Icc x y) ∧
      (x < y → ∀ t ∈ Icc x y, HasCovariantDerivativeWithinAt C c f (Icc x y) t 0)
  have hcongr : ∀ (x y : ℝ) (f g : (t : ℝ) → E (c t)),
      (∀ t ∈ Icc x y, g t = f t) → R x y f → R x y g := by
    intro x y f g heq hf
    refine ⟨c1FieldOn_congr hf.1 heq, ?_⟩
    intro hpos t ht
    exact covariantDerivative_congr ht (hf.2 hpos t ht) heq
  have hsub (i : Fin c.pieces) :
      Icc (c.node i.castSucc) (c.node i.succ) ⊆ Icc a b := fun t ht =>
    ⟨(PiecewiseCurves.node_mem c i.castSucc).1.trans ht.1,
      ht.2.trans (PiecewiseCurves.node_mem c i.succ).2⟩
  have hlocal : ∀ i : Fin c.pieces, ∀ s ∈ Icc (c.node i.castSucc) (c.node i.succ),
      ∀ ξ : E (c s), ∃ f : (t : ℝ) → E (c t),
        ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E))
          (Icc (c.node i.castSucc) (c.node i.succ)) ∧
        f s = ξ ∧ R (c.node i.castSucc) (c.node i.succ) f := by
    intro i s hs ξ
    obtain ⟨f, hf, hf1, hinit, hfd⟩ := parallel_exists_on_piece C
      (c.monotone_node (Fin.castSucc_le_succ i)) (c.regular i)
      (c.continuousOn.mono (hsub i)) hs ξ
    exact ⟨f, hf, hinit, hf1, hfd⟩
  obtain ⟨f, hf, hinit, hR⟩ := field_exists_on_partition c.node c.monotone_node R
    hcongr hlocal s (by simpa only [c.first_node, c.last_node] using s.property) ξ
  have hparallel : ParallelField C c f := ⟨by simpa only [c.first_node, c.last_node] using hf,
    fun i => (hR i).1, fun i => (hR i).2⟩
  refine ⟨f, hparallel, hinit, ?_⟩
  intro g hg hgs
  exact parallel_ext C c hg hparallel s (hgs.trans hinit.symm)


/-- The choice defining transport realizes any supplied parallel IVP. -/
theorem selectedField_parallel_of_parallel_ivp
    (hExist : P202Specs.Geometry.ParallelTransport.parallel_exists_uniqueType.{u,v,w})
    (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (s : Icc a b) (ξ : E (c s)) :
    ParallelField C c (selectedField C c s ξ) := by
  classical
  obtain ⟨f, hf, hfs, _⟩ := hExist C c s ξ
  have hex : ∃ f : (t : ℝ) → E (c t), ParallelField C c f ∧ f s = ξ := ⟨f, hf, hfs⟩
  simp only [selectedField, dite_eq_left hex]
  exact (Classical.choose_spec hex).1

theorem parallel_ext_of_parallel_ivp
    (hExist : P202Specs.Geometry.ParallelTransport.parallel_exists_uniqueType.{u,v,w})
    (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {f g : (t : ℝ) → E (c t)} (hf : ParallelField C c f) (hg : ParallelField C c g)
    (s : Icc a b) (hinit : f s = g s) : ∀ t ∈ Icc a b, f t = g t := by
  obtain ⟨z, _, _, hu⟩ := hExist C c s (g s)
  intro t ht
  exact (hu f hf hinit t ht).trans (hu g hg rfl t ht).symm

/-- Superposition and uniqueness give the actual linearity of the selected
fiber maps once the global existence obligation is supplied. -/
theorem transport_linear_of_parallel_ivp
    (hExist : P202Specs.Geometry.ParallelTransport.parallel_exists_uniqueType.{u,v,w})
    (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b) (s t : Icc a b) :
    (∀ ξ η, transport C c s t (ξ + η) = transport C c s t ξ + transport C c s t η) ∧
    (∀ (k : ℝ) ξ, transport C c s t (k • ξ) = k • transport C c s t ξ) := by
  constructor
  · intro ξ η
    exact parallel_ext C c
      (selectedField_parallel_of_parallel_ivp hExist C c s (ξ + η))
      (parallelField_add C c
        (selectedField_parallel_of_parallel_ivp hExist C c s ξ)
        (selectedField_parallel_of_parallel_ivp hExist C c s η)) s
      (by simp only [selectedField_initial]) t t.property
  · intro k ξ
    exact parallel_ext C c
      (selectedField_parallel_of_parallel_ivp hExist C c s (k • ξ))
      (parallelField_smul C c
        (selectedField_parallel_of_parallel_ivp hExist C c s ξ) k) s
      (by simp only [selectedField_initial]) t t.property

theorem transport_comp_of_parallel_ivp
    (hExist : P202Specs.Geometry.ParallelTransport.parallel_exists_uniqueType.{u,v,w})
    (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (s t q : Icc a b) (ξ : E (c s)) :
    transport C c t q (transport C c s t ξ) = transport C c s q ξ := by
  apply parallel_ext_of_parallel_ivp hExist C c
    (selectedField_parallel_of_parallel_ivp hExist C c t (transport C c s t ξ))
    (selectedField_parallel_of_parallel_ivp hExist C c s ξ) t _ q q.property
  exact selectedField_initial C c t (transport C c s t ξ)

theorem transport_inverse_of_parallel_ivp
    (hExist : P202Specs.Geometry.ParallelTransport.parallel_exists_uniqueType.{u,v,w})
    (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b) (s t : Icc a b) :
    Function.LeftInverse (transport C c t s) (transport C c s t) ∧
    Function.RightInverse (transport C c t s) (transport C c s t) := by
  constructor
  · intro ξ
    exact (transport_comp_of_parallel_ivp hExist C c s t s ξ).trans (selectedField_initial C c s ξ)
  · intro η
    exact (transport_comp_of_parallel_ivp hExist C c t s t η).trans (selectedField_initial C c t η)

theorem transport_equiv_of_linear_parallel_ivp
    (hExist : P202Specs.Geometry.ParallelTransport.parallel_exists_uniqueType.{u,v,w})
    (hLinear : P202Specs.Geometry.ParallelTransport.transport_linearType.{u,v,w})
    (C : Connection B) {a b : ℝ} (c : PiecewiseC1Curve S a b) (s t : Icc a b) :
    ∃ L : E (c s) ≃ₗ[ℝ] E (c t),
      (∀ ξ, L ξ = transport C c s t ξ) ∧
      (∀ η, L.symm η = transport C c t s η) := by
  let L : E (c s) ≃ₗ[ℝ] E (c t) :=
    { toFun := transport C c s t
      invFun := transport C c t s
      left_inv := (transport_inverse_of_parallel_ivp hExist C c s t).1
      right_inv := (transport_inverse_of_parallel_ivp hExist C c s t).2
      map_add' := (hLinear C c s t).1
      map_smul' := (hLinear C c s t).2 }
  exact ⟨L, fun _ => rfl, fun _ => rfl⟩

section Metric
open SmoothManifolds.MapData SmoothManifolds.FrameData P202.MetricData

/-- A smooth fiber metric has smooth evaluation on arbitrary actual sections. -/
theorem metric_pairing_sections_smooth (h : SmoothFiberMetric B)
    (Y Z : Section B) (p : M) :
    VectorSmoothAt S.smoothStructure.val (fun q => h.form q (Y.val q) (Z.val q)) p := by
  obtain ⟨i, hi⟩ := B.covers p
  let cv : M → Euclidean r := fun q => ((B.trivialization i) ⟨q, Y.val q⟩).2
  let cw : M → Euclidean r := fun q => ((B.trivialization i) ⟨q, Z.val q⟩).2
  have hcv : VectorSmoothAt S.smoothStructure.val cv p :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨p, Y.val p⟩ hi).comp
      (g := fun q => (⟨q, Y.val q⟩ : Bundle.TotalSpace (Euclidean r) E))
      B.totalManifold.smoothStructure.property.1.1 (Y.property p)
  have hcw : VectorSmoothAt S.smoothStructure.val cw p :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨p, Z.val p⟩ hi).comp
      (g := fun q => (⟨q, Z.val q⟩ : Bundle.TotalSpace (Euclidean r) E))
      B.totalManifold.smoothStructure.property.1.1 (Z.property p)
  let gram : Fin r → Fin r → M → ℝ := fun j k q =>
    h.form q ((B.trivialization i).symm q (Pi.single j 1))
      ((B.trivialization i).symm q (Pi.single k 1))
  have hsum : VectorSmoothAt S.smoothStructure.val
      (fun q => ∑ j : Fin r, ∑ k : Fin r, cv q j * (cw q k * gram j k q)) p := by
    apply VectorSmoothAt.sum
    intro j
    apply VectorSmoothAt.sum
    intro k
    have hj := hcv.postcomp (ContinuousLinearMap.proj (R := ℝ) j).contDiff
    have hk := hcw.postcomp (ContinuousLinearMap.proj (R := ℝ) k).contDiff
    exact (hj.prod ((hk.prod (h.smooth i j k p hi)).postcomp
      (contDiff_fst.mul contDiff_snd))).postcomp (contDiff_fst.mul contDiff_snd)
  apply hsum.congr
  have hO : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  filter_upwards [hO.mem_nhds hi] with q hq
  exact (SmoothMetrics.bilinear_coordinates (B.fiberCoordinates i q hq)
    (h.form q) (Y.val q) (Z.val q)).symm

/-- Metric compatibility on global sections gives the pairing rule along an
arbitrary C¹ curve velocity, including a one-sided velocity. -/
theorem metric_pairing_section_deriv (C : Connection B) (h : SmoothFiberMetric B)
    (hmetric : IsMetricConnection C h) (Y Z : Section B)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c J t V) :
    HasDerivWithinAt (fun q => h.form (c q) (Y.val (c q)) (Z.val (c q)))
      (h.form (c t) (pointDerivative C Y.val (c t) V) (Z.val (c t)) +
        h.form (c t) (Y.val (c t)) (pointDerivative C Z.val (c t) V)) J t := by
  have hd := CurveCovariantDerivative.scalar_chain hV
    (fun q => h.form q (Y.val q) (Z.val q)) (metric_pairing_sections_smooth h Y Z (c t))
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  have heq := hmetric X Y Z (c t)
  rw [hX] at heq
  rw [heq] at hd
  simpa only [← hX, ConnectionForms.pointDerivative_global, Function.comp_def] using hd


/-- Covariant differentiation depends only on the trace germ of the field. -/
theorem derivative_field_congr (C : Connection B)
    {c : ℝ → M} {f g : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (heq : ∀ᶠ s in 𝓝[J] t, f s = g s) {D : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D) :
    HasCovariantDerivativeWithinAt C c g J t D := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, hd⟩ := hD
  have he : coefficientsAlong b c g =ᶠ[𝓝[J] t] coefficientsAlong b c f := by
    filter_upwards [heq] with s hs
    simp only [coefficientsAlong, hs]
  refine ⟨V, hV, U, hU, b, hp, v', hv.congr_of_eventuallyEq_of_mem he ht, ?_⟩
  rw [hd]
  simp only [frameDerivative, he.eq_of_nhdsWithin ht]

/-- Finite superposition, including the empty sum and zero rank. -/
theorem derivative_field_finset_sum (C : Connection B)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c J t V)
    {κ : Type*} (I : Finset κ) (f : κ → (s : ℝ) → E (c s))
    (D : κ → E (c t))
    (hD : ∀ i ∈ I, HasCovariantDerivativeWithinAt C c (f i) J t (D i)) :
    HasCovariantDerivativeWithinAt C c (fun s => ∑ i ∈ I, f i s) J t (∑ i ∈ I, D i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
    refine ⟨V, hV, U, hU, b, hp, 0, ?_, ?_⟩
    · have hz : coefficientsAlong b c (fun _ => 0) = fun _ => 0 := by
        funext s
        simp [coefficientsAlong]
      rw [hz]
      exact hasDerivWithinAt_const t J 0
    · simp [frameDerivative, coefficientsAlong, hp]
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact CurveCovariantDerivative.derivative_add C ht hJ (hD i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hD j (Finset.mem_insert_of_mem hj)))

/-- A C¹ scalar-column expansion in any finite family of smooth sections
satisfies the expected product formula. -/
theorem derivative_section_expansion (C : Connection B) (e : Fin r → Section B)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c J t V) {v : ℝ → Euclidean r} {v' : Euclidean r}
    (hv : HasDerivWithinAt v v' J t) :
    HasCovariantDerivativeWithinAt C c (fun s => ∑ j, v s j • (e j).val (c s)) J t
      (∑ j, (v' j • (e j).val (c t) +
        v t j • pointDerivative C (e j).val (c t) V)) := by
  exact derivative_field_finset_sum C ht hJ hV Finset.univ
    (fun j s => v s j • (e j).val (c s))
    (fun j => v' j • (e j).val (c t) + v t j • pointDerivative C (e j).val (c t) V)
    (fun j _ => CurveCovariantDerivative.derivative_smul C
      (CurveCovariantDerivative.derivative_section C (e j) ht hV)
      (hasDerivWithinAt_pi.mp hv j))


/-- Algebra underlying the metric product rule in a finite frame. -/
theorem pairing_expansion_algebra {F : Type*} [AddCommGroup F] [Module ℝ F]
    (H : LinearMap.BilinForm ℝ F) (e de : Fin r → F) (v w v' w' : Euclidean r) :
    (∑ j, ∑ k, (v' j * (w k * H (e j) (e k)) +
      v j * (w' k * H (e j) (e k) +
        w k * (H (de j) (e k) + H (e j) (de k))))) =
    H (∑ j, (v' j • e j + v j • de j)) (∑ k, w k • e k) +
      H (∑ j, v j • e j) (∑ k, (w' k • e k + w k • de k)) := by
  simp_rw [LinearMap.map_sum₂, map_sum,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring


/-- Metric differentiation for finite combinations of globally smooth sections
with arbitrary C¹ parameter coefficients. -/
theorem metric_pairing_expansion_deriv (C : Connection B) (h : SmoothFiberMetric B)
    (hmetric : IsMetricConnection C h) (e : Fin r → Section B)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c J t V)
    {v w : ℝ → Euclidean r} {v' w' : Euclidean r}
    (hv : HasDerivWithinAt v v' J t) (hw : HasDerivWithinAt w w' J t) :
    HasDerivWithinAt
      (fun s => h.form (c s) (∑ j, v s j • (e j).val (c s)) (∑ k, w s k • (e k).val (c s)))
      (h.form (c t)
          (∑ j, (v' j • (e j).val (c t) + v t j • pointDerivative C (e j).val (c t) V))
          (∑ k, w t k • (e k).val (c t)) +
        h.form (c t) (∑ j, v t j • (e j).val (c t))
          (∑ k, (w' k • (e k).val (c t) + w t k • pointDerivative C (e k).val (c t) V))) J t := by
  have hd := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivWithinAt_pi.mp hv j).mul
        ((hasDerivWithinAt_pi.mp hw k).mul
          (metric_pairing_section_deriv C h hmetric (e j) (e k) hV))))
  simp only [Pi.mul_apply] at hd
  rw [pairing_expansion_algebra] at hd
  have heq : (fun s => ∑ j, ∑ k, v s j *
      (w s k * h.form (c s) ((e j).val (c s)) ((e k).val (c s)))) =
      (fun s => h.form (c s) (∑ j, v s j • (e j).val (c s))
        (∑ k, w s k • (e k).val (c s))) := by
    funext s
    simp_rw [LinearMap.map_sum₂, map_sum,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rwa [heq] at hd

/-- One family of globally smooth sections represents a local frame along a
curve germ and expands every actual field, including when the rank is zero. -/
theorem local_frame_global_expansion
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (hp : c t ∈ U)
    (hc : ContinuousWithinAt c J t) :
    ∃ e : Fin r → Section B, ∀ f : (s : ℝ) → E (c s),
      ∀ᶠ s in 𝓝[J] t,
        f s = ∑ j, coefficientsAlong b c f s j • (e j).val (c s) := by
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨c t, hp⟩
  refine ⟨e, ?_⟩
  intro f
  have hcommon := hc.eventually (Filter.eventually_all.mpr he)
  filter_upwards [hc.eventually (hU.mem_nhds hp), hcommon] with s hsU hs
  rw [CurveCovariantDerivative.coefficientsAlong_of_mem b c f s hsU]
  have hee (j : Fin r) : (e j).val (c s) = b.basis ⟨c s, hsU⟩ j := by
    simpa only [SmoothManifolds.SectionExtension.totalSection_of_mem _ _ hsU,
      b.basis_eq] using hs j
  simp_rw [hee]
  exact ((b.basis ⟨c s, hsU⟩).sum_equivFun (f s)).symm


/-- The metric pairing rule for arbitrary C¹ fields along a curve, proved
from metric compatibility on actual globally smooth sections. -/
theorem metric_pairing_deriv (C : Connection B) (h : SmoothFiberMetric B)
    (hmetric : IsMetricConnection C h)
    {c : ℝ → M} {f g : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {Df Dg : E (c t)}
    (hDf : HasCovariantDerivativeWithinAt C c f J t Df)
    (hDg : HasCovariantDerivativeWithinAt C c g J t Dg) :
    HasDerivWithinAt (fun s => h.form (c s) (f s) (g s))
      (h.form (c t) Df (g t) + h.form (c t) (f t) Dg) J t := by
  have hDf_copy := hDf
  obtain ⟨V, hV, U, hU, b, hp, v', hv, _⟩ := hDf_copy
  obtain ⟨w', hw⟩ := CurveCovariantDerivative.exists_coefficients_deriv C ht hDg b hp
  obtain ⟨e, he⟩ := local_frame_global_expansion b hp hV.1
  have heDf := CurveCovariantDerivative.covariantDerivative_unique C ht hJ hDf
    (derivative_field_congr C ht ((he f).mono (fun _ hs => hs.symm))
      (derivative_section_expansion C e ht hJ hV hv))
  have heDg := CurveCovariantDerivative.covariantDerivative_unique C ht hJ hDg
    (derivative_field_congr C ht ((he g).mono (fun _ hs => hs.symm))
      (derivative_section_expansion C e ht hJ hV hw))
  have hd := metric_pairing_expansion_deriv C h hmetric e hV hv hw
  rw [← heDf, ← heDg, ← (he f).self_of_nhdsWithin ht, ← (he g).self_of_nhdsWithin ht] at hd
  apply hd.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [he f, he g] with s hfs hgs
  rw [hfs, hgs]


/-- The pairing of two parallel fields has one value on the entire path,
including all original corners and repeated partition nodes. -/
theorem parallel_pairing_constant (C : Connection B) (h : SmoothFiberMetric B)
    (hmetric : IsMetricConnection C h) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {f g : (t : ℝ) → E (c t)} (hf : ParallelField C c f) (hg : ParallelField C c g)
    (s t : Icc a b) :
    h.form (c t) (f t) (g t) = h.form (c s) (f s) (g s) := by
  have hd : ∀ i : Fin c.pieces, c.node i.castSucc < c.node i.succ →
      ∀ x ∈ Icc (c.node i.castSucc) (c.node i.succ),
        HasDerivWithinAt (fun y => h.form (c y) (f y) (g y)) 0
          (Icc (c.node i.castSucc) (c.node i.succ)) x := by
    intro i hi x hx
    simpa using metric_pairing_deriv C h hmetric hx (uniqueDiffOn_Icc hi x hx)
      (hf.2.2 i hi x hx) (hg.2.2 i hi x hx)
  exact scalar_constant_on_partition c.node c.monotone_node
    (fun y => h.form (c y) (f y) (g y)) hd s
    (by simpa only [c.first_node, c.last_node] using s.property) t
    (by simpa only [c.first_node, c.last_node] using t.property)

end Metric

/-- Transport at a single parameter value is the identity. -/
theorem transport_refl :
    P202Specs.Geometry.ParallelTransport.transport_reflType.{u,v,w} := by
  intro n r kind M _ S ι E _ _ _ B C a b c s ξ
  exact selectedField_initial C c s ξ

theorem parallel_exists_unique :
    P202Specs.Geometry.ParallelTransport.parallel_exists_uniqueType.{u,v,w} := by
  exact @parallel_ivp.{u,v,w}

theorem selectedField_parallel :
    P202Specs.Geometry.ParallelTransport.selectedField_parallelType.{u,v,w} := by
  intro n r kind M _ S ι E _ _ _ B C a b c s ξ
  exact ⟨selectedField_parallel_of_parallel_ivp (@parallel_ivp.{u,v,w}) C c s ξ,
    selectedField_initial C c s ξ⟩

theorem transport_linear :
    P202Specs.Geometry.ParallelTransport.transport_linearType.{u,v,w} := by
  intro n r kind M _ S ι E _ _ _ B C a b c s t
  exact transport_linear_of_parallel_ivp (@parallel_ivp.{u,v,w}) C c s t

theorem transport_comp :
    P202Specs.Geometry.ParallelTransport.transport_compType.{u,v,w} := by
  intro n r kind M _ S ι E _ _ _ B C a b c s t q ξ
  exact transport_comp_of_parallel_ivp (@parallel_ivp.{u,v,w}) C c s t q ξ

theorem transport_inverse :
    P202Specs.Geometry.ParallelTransport.transport_inverseType.{u,v,w} := by
  intro n r kind M _ S ι E _ _ _ B C a b c s t
  exact transport_inverse_of_parallel_ivp (@parallel_ivp.{u,v,w}) C c s t

theorem transport_equiv :
    P202Specs.Geometry.ParallelTransport.transport_equivType.{u,v,w} := by
  have hLinear : P202Specs.Geometry.ParallelTransport.transport_linearType.{u,v,w} := by
    intro n r kind M _ S ι E _ _ _ B C a b c s t
    exact transport_linear_of_parallel_ivp (@parallel_ivp.{u,v,w}) C c s t
  intro n r kind M _ S ι E _ _ _ B C a b c s t
  exact transport_equiv_of_linear_parallel_ivp (@parallel_ivp.{u,v,w}) hLinear C c s t

theorem transport_isometry :
    P202Specs.Geometry.ParallelTransport.transport_isometryType.{u,v,w} := by
  intro n r kind M _ S ι E _ _ _ B C h hmetric a b c s t ξ η
  simpa only [transport, selectedField_initial] using
    parallel_pairing_constant C h hmetric c
      (selectedField_parallel_of_parallel_ivp (@parallel_ivp.{u,v,w}) C c s ξ)
      (selectedField_parallel_of_parallel_ivp (@parallel_ivp.{u,v,w}) C c s η) s t

end BundleFields
end P202.Geometry.ParallelTransport
