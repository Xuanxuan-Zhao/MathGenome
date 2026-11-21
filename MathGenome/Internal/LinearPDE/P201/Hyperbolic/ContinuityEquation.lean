import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.ContinuityEquation
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.Flow
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.Liouville
import Mathlib.MeasureTheory.Function.Jacobian
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set MeasureTheory
open scoped ContDiff NNReal
namespace P201.Hyperbolic
open P201Specs P201Specs.Hyperbolic

/-- The actual spatial Jacobian, not a separately supplied scalar solution. -/
abbrev flowJacobian := @P201Specs.Hyperbolic.flowJacobian
/-- The explicit density representative in Eulerian coordinates. -/
abbrev transportedDensity := @P201Specs.Hyperbolic.transportedDensity

/-- The initial spatial map is the identity, hence its determinant is one. -/
lemma flowJacobian_initial {n : ℕ} {T : ℝ} {b : SlabField n T}
    {X : ℝ → ℝ → Space n → Space n} (hX : SlabFlowProperties b X)
    (hT : 0 ≤ T) (y : Space n) : flowJacobian X 0 y = 1 := by
  have he : X 0 0 = id := funext (hX.initial 0 ⟨le_rfl, hT⟩)
  simp [flowJacobian, P201Specs.Hyperbolic.flowJacobian, he, ContinuousLinearMap.det,
    LinearMap.det_id]

/-- The explicit density has the prescribed initial representative. -/
lemma transportedDensity_initial {n : ℕ} {T : ℝ} {b : SlabField n T}
    {X : ℝ → ℝ → Space n → Space n} (hX : SlabFlowProperties b X)
    (hT : 0 ≤ T) (g : Space n → ℝ) : transportedDensity X g 0 = g := by
  funext x
  change g (X 0 0 x) / flowJacobian X 0 (X 0 0 x) = g x
  rw [hX.initial 0 ⟨le_rfl, hT⟩, flowJacobian_initial hX hT, div_one]

/-- Composition with the forward flow recovers the characteristic formula.
This equality needs no smoothness or integrability assumption on g. -/
lemma transportedDensity_characteristic {n : ℕ} {T : ℝ} {b : SlabField n T}
    {X : ℝ → ℝ → Space n → Space n} (hX : SlabFlowProperties b X)
    (hT : 0 ≤ T) (g : Space n → ℝ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (y : Space n) :
    transportedDensity X g t (X t 0 y) = g y / flowJacobian X t y := by
  have hi : X 0 t (X t 0 y) = y :=
    (hX.composition 0 ⟨le_rfl, hT⟩ t ht 0 ⟨le_rfl, hT⟩ y).trans
      (hX.initial 0 ⟨le_rfl, hT⟩ y)
  simp only [transportedDensity, P201Specs.Hyperbolic.transportedDensity, hi]

section MatrixBridge
open scoped Matrix.Norms.Operator

/-- Matrix of a Euclidean operator in the canonical orthonormal basis. -/
def spatialOperatorMatrix {n : ℕ} (L : Space n →L[ℝ] Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis L.toLinearMap

/-- The coordinate representation is a continuous linear operation also for
the operator norm on matrices used by D13's Liouville theorem. -/
def spatialOperatorMatrixCLM (n : ℕ) :
    (Space n →L[ℝ] Space n) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ((LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).toLinearMap.comp
      (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

lemma spatialOperatorMatrixCLM_apply {n : ℕ} (L : Space n →L[ℝ] Space n) :
    spatialOperatorMatrixCLM n L = spatialOperatorMatrix L := rfl

lemma spatialOperatorMatrix_comp {n : ℕ} (A B : Space n →L[ℝ] Space n) :
    spatialOperatorMatrix (A.comp B) = spatialOperatorMatrix A * spatialOperatorMatrix B := by
  exact LinearMap.toMatrix_comp _ _ _ _ _

lemma spatialOperatorMatrix_det {n : ℕ} (A : Space n →L[ℝ] Space n) :
    (spatialOperatorMatrix A).det = A.det := by
  exact LinearMap.det_toMatrix _ _

/-- Matrix trace is exactly the shared coordinate definition of divergence. -/
lemma spatialOperatorMatrix_trace_fderiv {n : ℕ} {f : Space n → Space n}
    {x : Space n} (hf : DifferentiableAt ℝ f x) :
    (spatialOperatorMatrix (fderiv ℝ f x)).trace = divergence f x := by
  simp only [Matrix.trace, Matrix.diag, spatialOperatorMatrix, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, ContinuousLinearMap.coe_coe]
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  have hd := (EuclideanSpace.proj i).hasFDerivAt.comp x hf.hasFDerivAt
  have he := hd.fderiv
  change fderiv ℝ (fun y => f y i) x = _ at he
  rw [he]
  rfl

end MatrixBridge

open scoped Matrix.Norms.Operator
open D13Unified D13Unified.Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch04.MaximalSolutionMap
open private equation_eval equation_regular total_domain from MathGenome.Internal.LinearPDE.P201.Hyperbolic.Flow

/-- Liouville on the actual canonical solution of a globally defined bounded
C¹ field. Its operator derivative is the D13 state variation. -/
lemma global_localFlow_jacobian {n : ℕ} (c : LocalField n)
    (hU : c.domain = univ) (M : ℝ≥0) (hM : ∀ q, ‖c.velocity q‖ ≤ M)
    (s t : ℝ) (y : Space n) :
    (fderiv ℝ (P201Specs.Hyperbolic.localFlow c t s) y).det =
      Real.exp (∫ r in s..t,
        divergence (fun x => c.velocity (r, x)) (P201Specs.Hyperbolic.localFlow c r s y)) := by
  let F := c.equation
  have hF := equation_regular c
  have hfull := total_domain c hU M hM
  have hdom (r : ℝ) : (r, s, y) ∈ localFlowDomain c := hfull ▸ mem_univ _
  have hs : ((s, y), (0 : ℝ)) ∈ F.domain := by
    change (s, y) ∈ c.domain
    rw [hU]
    exact mem_univ _
  let I := parameterMaximalIntervalValue F s y 0
  let Y := stateVariation F s y 0
  let A := stateCoefficient F s y 0
  have hV := state_variation F hF s y 0 hs
  have hC := (continuousOn_coefficients F hF hs).1
  have hY : ContinuousOn Y I.carrier := fun r hr =>
    (hV.2.1 r hr).2.continuousAt.continuousWithinAt
  have hd (r : ℝ) (hr : r ∈ I.carrier) :
      HasDerivWithinAt (fun v => spatialOperatorMatrix (Y v))
        (spatialOperatorMatrix (A r) * spatialOperatorMatrix (Y r)) I.carrier r := by
    have h := (spatialOperatorMatrixCLM n).hasFDerivAt.comp_hasDerivAt r (hV.2.1 r hr).2
    exact (h.congr_deriv (spatialOperatorMatrix_comp _ _)).hasDerivWithinAt
  have hdet := D13Unified.Ch07.Liouville.det_eq_exp_trace_integral I.toTimeInterval
    (fun r => spatialOperatorMatrix (A r)) (fun r => spatialOperatorMatrix (Y r))
    ((spatialOperatorMatrixCLM n).continuous.comp_continuousOn hC)
    ((spatialOperatorMatrixCLM n).continuous.comp_continuousOn hY) hd
    (hdom s).2 (hdom t).2
  have hinit : (spatialOperatorMatrix (Y s)).det = 1 := by
    rw [show Y s = ContinuousLinearMap.id ℝ (Space n) from hV.1,
      spatialOperatorMatrix_det]
    exact LinearMap.det_id
  have heval (r : ℝ) : (fun x => parameterEvalValue F r x 0) =
      (fun x => c.velocity (r, x)) := by
    funext x
    exact equation_eval c (hU ▸ mem_univ (r, x))
  have htrace (r : ℝ) : (spatialOperatorMatrix (A r)).trace =
      divergence (fun x => c.velocity (r, x)) (P201Specs.Hyperbolic.localFlow c r s y) := by
    change (spatialOperatorMatrix (fderiv ℝ (fun x => parameterEvalValue F r x 0)
      (P201Specs.Hyperbolic.localFlow c r s y))).trace = _
    rw [heval]
    apply spatialOperatorMatrix_trace_fderiv
    have hc : ContDiff ℝ 1 c.velocity := contDiffOn_univ.mp (hU ▸ c.regular)
    exact (hc.comp (contDiff_const.prodMk contDiff_id)).differentiable_one.differentiableAt
  simp only [hinit, one_mul, spatialOperatorMatrix_det] at hdet
  rw [show (fun r => (spatialOperatorMatrix (A r)).trace) =
    (fun r => divergence (fun x => c.velocity (r, x))
      (P201Specs.Hyperbolic.localFlow c r s y)) from funext htrace] at hdet
  rw [← Real.exp_eq_exp_ℝ] at hdet
  exact hdet

/-- The closed-slab Jacobian identity, independent of any extension chosen
in its proof. Spatial maps agree everywhere on the slab, hence so do their
actual spatial derivatives. -/
theorem flowJacobian_formula : P201Specs.Hyperbolic.flowJacobianStatement := by
  intro n hn T hT b X hX t ht y
  change flowJacobian X t y = _ ∧ 0 < flowJacobian X t y
  by_cases hz : T = 0
  · subst T
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    rw [flowJacobian_initial hX le_rfl]
    simp
  · have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hz)
    obtain ⟨v, hv, he, hbound⟩ := bounded_slab_extension hpos b.regular b.bound
      (fun q hq => b.velocity_bound q.1 hq.1 q.2)
    let c : LocalField n := ⟨univ, isOpen_univ, v, hv.contDiffOn⟩
    have hc := localFlow n hn c
    have hfull := total_domain c rfl (3 * b.bound) (by
      intro q
      simpa using hbound q)
    have hdom (r s : ℝ) (z : Space n) : (r, s, z) ∈ localFlowDomain c :=
      hfull ▸ mem_univ _
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have hsol (z : Space n) : IsSlabSolution b
        (fun r => P201Specs.Hyperbolic.localFlow c r 0 z) := by
      refine ⟨?_, ?_⟩
      · intro r hr
        exact (hc.equation r 0 z (hdom r 0 z)).2.continuousAt.continuousWithinAt
      · intro r hr
        have hd := (hc.equation r 0 z (hdom r 0 z)).2.hasDerivWithinAt (s := Icc 0 T)
        change HasDerivWithinAt _ (v (r, P201Specs.Hyperbolic.localFlow c r 0 z)) _ r at hd
        rwa [he ⟨hr, mem_univ _⟩] at hd
    have hEq (r : ℝ) (hr : r ∈ Icc 0 T) :
        P201Specs.Hyperbolic.localFlow c r 0 = X r 0 := by
      funext z
      exact hX.unique 0 h0 z _ (hsol z) (hc.initial 0 z (mem_univ _)).2 hr
    have hj := global_localFlow_jacobian c rfl (3 * b.bound)
      (by intro q; simpa using hbound q) 0 t y
    rw [hEq t ht] at hj
    have hint : (∫ r in (0 : ℝ)..t,
        divergence (fun x => c.velocity (r, x)) (P201Specs.Hyperbolic.localFlow c r 0 y)) =
        ∫ r in (0 : ℝ)..t, divergence (fun x => b.velocity (r, x)) (X r 0 y) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hrT := uIcc_subset_Icc h0 ht hr
      have hev : (fun x => c.velocity (r, x)) = (fun x => b.velocity (r, x)) :=
        funext (fun x => he ⟨hrT, mem_univ x⟩)
      dsimp only
      rw [hev, hEq r hrT]
    rw [hint] at hj
    change flowJacobian X t y = _ at hj
    refine ⟨hj, ?_⟩
    rw [hj]
    exact Real.exp_pos _

/-- Every spatial slice has the derivative required by the change-of-variables theorem. -/
lemma flow_slice_differentiable {n : ℕ} {T : ℝ} {b : SlabField n T}
    {X : ℝ → ℝ → Space n → Space n} (hX : SlabFlowProperties b X)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    Differentiable ℝ (X t s) := by
  obtain ⟨e, he, _, hce, _⟩ := hX.diffeomorphism t ht s hs
  rw [← he]
  exact hce.differentiable_one

/-- Spatial change of variables identifies the density's action on arbitrary
weights. Its integrability is addressed separately; Mathlib's identity also
covers the totalized Bochner integral. -/
lemma integral_transportedDensity {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) (g ψ : Space n → ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x, transportedDensity X g t x * ψ x) = ∫ y, g y * ψ (X t 0 y) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  obtain ⟨e, he, _, _, _⟩ := hX.diffeomorphism t ht 0 h0
  have hsurj : X t 0 '' univ = univ := by
    rw [← he, image_univ]
    exact e.surjective.range_eq
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x (_ : x ∈ univ) => (flow_slice_differentiable hX ht h0 x).hasFDerivAt.hasFDerivWithinAt)
    (show InjOn (X t 0) univ by rw [← he]; exact e.injective.injOn)
    (fun x => transportedDensity X g t x * ψ x)
  rw [hsurj] at hcov
  simp only [Measure.restrict_univ] at hcov
  rw [hcov]
  apply integral_congr_ae
  filter_upwards [] with y
  have hp := (flowJacobian_formula n hn T hT b X hX t ht y).2
  change |flowJacobian X t y| • (transportedDensity X g t (X t 0 y) * ψ (X t 0 y)) = _
  rw [abs_of_pos hp, transportedDensity_characteristic hX hT g ht]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt hp]

/-- The corresponding equivalence proves integrability rather than relying
on the totalized integral equality. -/
lemma integrableOn_transportedDensity_image_iff {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) (g : Space n → ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 T) {K : Set (Space n)} (hK : MeasurableSet K) :
    IntegrableOn (transportedDensity X g t) (X t 0 '' K) volume ↔
      IntegrableOn g K volume := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  obtain ⟨e, he, _, _, _⟩ := hX.diffeomorphism t ht 0 h0
  have hcov := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hK
    (fun x (_ : x ∈ K) => (flow_slice_differentiable hX ht h0 x).hasFDerivAt.hasFDerivWithinAt)
    (show InjOn (X t 0) K by rw [← he]; exact e.injective.injOn)
    (transportedDensity X g t)
  have hf : (fun y => |(fderiv ℝ (X t 0) y).det| •
      transportedDensity X g t (X t 0 y)) = g := by
    funext y
    have hp := (flowJacobian_formula n hn T hT b X hX t ht y).2
    change |flowJacobian X t y| • transportedDensity X g t (X t 0 y) = _
    rw [abs_of_pos hp, transportedDensity_characteristic hX hT g ht]
    simp only [smul_eq_mul]
    exact mul_div_cancel₀ _ (ne_of_gt hp)
  rwa [hf] at hcov

/-- Every time slice is locally L¹, with no global L¹ assumption on g. -/
lemma transportedDensity_locallyIntegrable {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {g : Space n → ℝ} (hg : LocallyIntegrable g volume)
    {t : ℝ} (ht : t ∈ Icc 0 T) : LocallyIntegrable (transportedDensity X g t) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  obtain ⟨e, he, hi, _, _⟩ := hX.diffeomorphism t ht 0 h0
  have hL : IsCompact (X 0 t '' K) := by rw [← hi]; exact hK.image e.symm.continuous
  have hEq : X t 0 '' (X 0 t '' K) = K := by
    rw [← he, ← hi, ← image_comp]
    simp
  rw [← hEq]
  exact (integrableOn_transportedDensity_image_iff hn hT hX g ht hL.measurableSet).mpr
    (hg.integrableOn_isCompact hL)

/-- On a positive slab the spatial derivative is the spatial column of the
within derivative of the jointly C¹ map. -/
private lemma continuousOn_spatial_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T : ℝ} (hT : 0 < T) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ univ)) :
    ContinuousOn (fun q : ℝ × E => fderiv ℝ (fun y => f (q.1, y)) q.2)
      (Icc 0 T ×ˢ univ) := by
  let S : Set (ℝ × E) := Icc 0 T ×ˢ univ
  have hD := hf.continuousOn_fderivWithin
    ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) le_rfl
  have he (q : ℝ × E) (hq : q ∈ S) :
      fderiv ℝ (fun y => f (q.1, y)) q.2 =
        (fderivWithin ℝ f S q).comp ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) := by
    have hd := (hf.differentiableOn one_ne_zero q hq).hasFDerivWithinAt
    have hi : HasFDerivAt (fun y : E => (q.1, y))
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) q.2 :=
      (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
    exact (hd.comp_hasFDerivAt q.2 hi
      (Filter.Eventually.of_forall (fun y : E => show (q.1, y) ∈ S from ⟨hq.1, mem_univ y⟩))).fderiv
  exact (hD.clm_comp continuousOn_const).congr (fun q hq => he q hq)

lemma flowJacobian_continuousOn {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) :
    ContinuousOn (fun q : ℝ × Space n => flowJacobian X q.1 q.2)
      (Icc 0 T ×ˢ univ) := by
  by_cases hz : T = 0
  · subst T
    apply (continuousOn_const (c := (1 : ℝ))).congr
    intro q hq
    have hq0 : q.1 = 0 := le_antisymm hq.1.2 hq.1.1
    simpa [hq0] using flowJacobian_initial hX le_rfl q.2
  · have hp : 0 < T := lt_of_le_of_ne hT (Ne.symm hz)
    have hf : ContDiffOn ℝ 1 (fun q : ℝ × Space n => X q.1 0 q.2)
        (Icc 0 T ×ˢ univ) :=
      hX.regular.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
        (fun _ hq => ⟨hq.1, ⟨⟨le_rfl, hT⟩, mem_univ _⟩⟩)
    exact ContinuousLinearMap.continuous_det.comp_continuousOn (continuousOn_spatial_fderiv hp hf)

/-- A smooth spatial diffeomorphism preserves null sets in both directions;
this ensures a.e. initial representatives can legitimately be composed. -/
lemma flow_inverse_quasiMeasurePreserving {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {t : ℝ} (ht : t ∈ Icc 0 T) :
    QuasiMeasurePreserving (X 0 t) (volume : Measure (Space n)) volume := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  obtain ⟨e, he, hi, _, _⟩ := hX.diffeomorphism t ht 0 h0
  have hm : Measurable (X 0 t) := by rw [← hi]; exact e.symm.measurable
  refine ⟨hm, Measure.AbsolutelyContinuous.mk (fun N hN hnull => ?_)⟩
  rw [Measure.map_apply hm hN]
  have hEq : X 0 t ⁻¹' N = X t 0 '' N := by
    rw [← he, ← hi]
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  rw [hEq]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (flow_slice_differentiable hX ht h0).differentiableOn hnull

private def clampTime (T t : ℝ) : ℝ := max 0 (min T t)

private lemma clampTime_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampTime T t ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

private lemma clampTime_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : clampTime T t = t := by
  simp [clampTime, min_eq_right ht.2, max_eq_right ht.1]

/-- The inverse-time pullback is jointly nonsingular after clamping the time
coordinate to the slab. No measurability is imposed on ambient flow values
outside that slab. -/
private lemma clamped_inverse_quasiMeasurePreserving {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) :
    QuasiMeasurePreserving (fun q : ℝ × Space n => X 0 (clampTime T q.1) q.2)
      (volume.prod volume) volume := by
  have hc : Continuous (fun q : ℝ × Space n => X 0 (clampTime T q.1) q.2) := by
    apply hX.regular.continuousOn.comp_continuous
      (continuous_const.prodMk
        ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd))
    intro q
    exact ⟨⟨le_rfl, hT⟩, clampTime_mem hT q.1, mem_univ _⟩
  exact QuasiMeasurePreserving.prod_of_right hc.measurable
    (Filter.Eventually.of_forall (fun t => flow_inverse_quasiMeasurePreserving hT hX (clampTime_mem hT t)))

/-- Joint a.e. measurability follows from nonsingularity, so no special
Borel representative of the L¹_loc datum is assumed. -/
lemma transportedDensity_aestronglyMeasurable {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {g : Space n → ℝ} (hg : LocallyIntegrable g volume) :
    AEStronglyMeasurable (fun q : ℝ × Space n => transportedDensity X g q.1 q.2)
      ((volume.prod volume).restrict (Icc 0 T ×ˢ univ)) := by
  have hclamp : Continuous (fun t => clampTime T t) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hinv : Continuous (fun q : ℝ × Space n => X 0 (clampTime T q.1) q.2) := by
    apply hX.regular.continuousOn.comp_continuous
      (continuous_const.prodMk ((hclamp.comp continuous_fst).prodMk continuous_snd))
    intro q
    exact ⟨⟨le_rfl, hT⟩, clampTime_mem hT q.1, mem_univ _⟩
  have hJ : Continuous (fun q : ℝ × Space n =>
      flowJacobian X (clampTime T q.1) (X 0 (clampTime T q.1) q.2)) :=
    (flowJacobian_continuousOn hT hX).comp_continuous
      ((hclamp.comp continuous_fst).prodMk hinv)
      (fun q => ⟨clampTime_mem hT q.1, mem_univ _⟩)
  have hm := hg.aestronglyMeasurable.comp_quasiMeasurePreserving
    (clamped_inverse_quasiMeasurePreserving hT hX)
  have hr := (hm.div₀ hJ.aestronglyMeasurable).restrict (s := Icc 0 T ×ˢ univ)
  apply hr.congr
  filter_upwards [ae_restrict_mem (isClosed_Icc.prod isClosed_univ).measurableSet] with q hq
  change g (X 0 (clampTime T q.1) q.2) /
    flowJacobian X (clampTime T q.1) (X 0 (clampTime T q.1) q.2) = _
  rw [clampTime_eq hq.1]
  rfl

/-- Absolute integrals transform without any derivative of the initial datum. -/
lemma integral_norm_transportedDensity_image {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) (g : Space n → ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 T) {K : Set (Space n)} (hK : MeasurableSet K) :
    (∫ x in X t 0 '' K, ‖transportedDensity X g t x‖) = ∫ y in K, ‖g y‖ := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  obtain ⟨e, he, _, _, _⟩ := hX.diffeomorphism t ht 0 h0
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hK
    (fun x (_ : x ∈ K) => (flow_slice_differentiable hX ht h0 x).hasFDerivAt.hasFDerivWithinAt)
    (show InjOn (X t 0) K by rw [← he]; exact e.injective.injOn)]
  apply setIntegral_congr_fun hK
  intro y _
  have hp := (flowJacobian_formula n hn T hT b X hX t ht y).2
  change |flowJacobian X t y| • ‖transportedDensity X g t (X t 0 y)‖ = _
  rw [abs_of_pos hp, transportedDensity_characteristic hX hT g ht]
  simp only [norm_div, Real.norm_eq_abs, smul_eq_mul]
  change flowJacobian X t y * (|g y| / |flowJacobian X t y|) = |g y|
  rw [abs_of_pos (show 0 < flowJacobian X t y from hp)]
  exact mul_div_cancel₀ _ (ne_of_gt hp)

/-- A common compact set controls all pulled-back supports on the finite slab. -/
lemma compact_inverse_flow_image {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {K : Set (Space n)} (hK : IsCompact K) :
    IsCompact ((fun q : ℝ × Space n => X 0 q.1 q.2) '' (Icc 0 T ×ˢ K)) := by
  apply (isCompact_Icc.prod hK).image_of_continuousOn
  exact hX.regular.continuousOn.comp
    (continuousOn_const.prodMk (continuousOn_fst.prodMk continuousOn_snd))
    (fun _ hq => ⟨⟨le_rfl, hT⟩, hq.1, mem_univ _⟩)

/-- Integrability on compact spatial cylinders. This is the step where a
common compact pullback, not global L¹ integrability of g, is needed. -/
lemma transportedDensity_integrableOn_cylinder {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {g : Space n → ℝ} (hg : LocallyIntegrable g volume)
    {K : Set (Space n)} (hK : IsCompact K) :
    IntegrableOn (fun q : ℝ × Space n => transportedDensity X g q.1 q.2)
      (Icc 0 T ×ˢ K) (volume.prod volume) := by
  let L := (fun q : ℝ × Space n => X 0 q.1 q.2) '' (Icc 0 T ×ˢ K)
  have hL : IsCompact L := compact_inverse_flow_image hT hX hK
  have hgL := hg.integrableOn_isCompact hL
  have hm := transportedDensity_aestronglyMeasurable hT hX hg
  have hm' : AEStronglyMeasurable (fun q : ℝ × Space n => transportedDensity X g q.1 q.2)
      ((volume.restrict (Icc 0 T)).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict]
    exact hm.mono_measure (Measure.restrict_mono_set _
      (prod_mono Subset.rfl (subset_univ _)))
  rw [IntegrableOn, ← Measure.prod_restrict]
  apply (integrable_prod_iff hm').mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (transportedDensity_locallyIntegrable hn hT hX hg ht).integrableOn_isCompact hK
  · apply (integrableOn_const (C := ∫ y in L, ‖g y‖) (s := Icc (0 : ℝ) T) (hs := isCompact_Icc.measure_ne_top)).mono'
      hm'.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    let Lt := X 0 t '' K
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    obtain ⟨e, he, hi, _, _⟩ := hX.diffeomorphism t ht 0 h0
    have hLt : IsCompact Lt := by rw [show Lt = X 0 t '' K from rfl, ← hi]; exact hK.image e.symm.continuous
    have hforward : X t 0 '' Lt = K := by
      change X t 0 '' (X 0 t '' K) = K
      rw [← he, ← hi, ← image_comp]
      simp
    change (∫ x in K, ‖transportedDensity X g t x‖) ≤ ∫ y in L, ‖g y‖
    rw [← hforward, integral_norm_transportedDensity_image hn hT hX g ht hLt.measurableSet]
    apply setIntegral_mono_set hgL.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    apply Filter.Eventually.of_forall
    rintro y ⟨x, hx, rfl⟩
    exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩

/-- Joint local integrability, including neighborhoods of either endpoint. -/
lemma transportedDensity_locallyIntegrableOn_slab {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {g : Space n → ℝ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrableOn (fun q : ℝ × Space n => transportedDensity X g q.1 q.2)
      (Icc 0 T ×ˢ univ) (volume.prod volume) := by
  apply (locallyIntegrableOn_iff (isClosed_Icc.prod isClosed_univ).isLocallyClosed).mpr
  intro K hKS hK
  have hproj : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  exact (transportedDensity_integrableOn_cylinder hn hT hX hg hproj).mono_set
    (fun q hq => ⟨(hKS hq).1, ⟨q, hq, rfl⟩⟩)

/-- The displayed time-plus-space test operator is precisely the full
space-time differential applied to (1,b). -/
lemma continuityTestDerivative_eq_fderiv {n : ℕ} {T : ℝ} (b : SlabField n T)
    {φ : ℝ × Space n → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : Space n) :
    continuityTestDerivative b φ t x = fderiv ℝ φ (t, x) (1, b.velocity (t, x)) := by
  have ht := (hφ (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hx := (hφ (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  change HasDerivAt (fun r => φ (r, x)) _ t at ht
  change HasFDerivAt (fun y => φ (t, y)) _ x at hx
  unfold continuityTestDerivative
  rw [ht.deriv, hx.fderiv]
  change fderiv ℝ φ (t, x) (1, 0) + fderiv ℝ φ (t, x) (0, b.velocity (t, x)) = _
  rw [← map_add]
  simp

lemma continuityTestDerivative_continuousOn {n : ℕ} {T : ℝ} (b : SlabField n T)
    (φ : ContinuityTest n T) :
    ContinuousOn (fun q : ℝ × Space n => continuityTestDerivative b φ.toFun q.1 q.2)
      (Icc 0 T ×ˢ univ) := by
  have hd := φ.smooth.continuous_fderiv (by simp)
  apply (hd.continuousOn.clm_apply (continuousOn_const.prodMk b.regular.continuousOn)).congr
  intro q _
  exact continuityTestDerivative_eq_fderiv b (φ.smooth.differentiable (by simp)) q.1 q.2

lemma continuityTestDerivative_hasCompactSupport {n : ℕ} {T : ℝ} (b : SlabField n T)
    (φ : ContinuityTest n T) :
    HasCompactSupport (fun q : ℝ × Space n => continuityTestDerivative b φ.toFun q.1 q.2) := by
  apply HasCompactSupport.of_support_subset_isCompact φ.compact
  intro q hq
  by_contra hnot
  apply hq
  change continuityTestDerivative b φ.toFun q.1 q.2 = 0
  rw [continuityTestDerivative_eq_fderiv b (φ.smooth.differentiable (by simp))]
  rw [fderiv_of_notMem_tsupport ℝ hnot]
  rfl

/-- The test operator is integrable against the transported density on the
whole time slab, despite a possibly nonintegrable spatial tail of g. -/
lemma transportedDensity_test_integrable {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {g : Space n → ℝ} (hg : LocallyIntegrable g volume)
    (φ : ContinuityTest n T) :
    IntegrableOn (fun q : ℝ × Space n =>
      transportedDensity X g q.1 q.2 * continuityTestDerivative b φ.toFun q.1 q.2)
      (Icc 0 T ×ˢ univ) (volume.prod volume) := by
  let S : Set (ℝ × Space n) := Icc 0 T ×ˢ univ
  let D := fun q : ℝ × Space n => continuityTestDerivative b φ.toFun q.1 q.2
  have hlocal := (transportedDensity_locallyIntegrableOn_slab hn hT hX hg).mul_continuousOn
    (continuityTestDerivative_continuousOn b φ) (isClosed_Icc.prod isClosed_univ).isLocallyClosed
  have hK : IsCompact (S ∩ tsupport D) :=
    (continuityTestDerivative_hasCompactSupport b φ).inter_left (isClosed_Icc.prod isClosed_univ)
  have hi := hlocal.integrableOn_compact_subset inter_subset_left hK
  have he : (fun q : ℝ × Space n => transportedDensity X g q.1 q.2 * D q) =
      (tsupport D).indicator (fun q => transportedDensity X g q.1 q.2 * D q) := by
    funext q
    by_cases hq : q ∈ tsupport D
    · simp [hq]
    · simp [hq, image_eq_zero_of_notMem_tsupport hq]
  rw [he]
  rw [integrableOn_indicator_iff (isClosed_tsupport D).measurableSet.nullMeasurableSet]
  simpa only [inter_comm] using hi

/-- A locally L¹ function of space is locally L¹ on time-space. -/
private lemma locallyIntegrable_snd {n : ℕ} {g : Space n → ℝ}
    (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun q : ℝ × Space n => g q.2) (volume.prod volume) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hfst := hK.image continuous_fst
  have hsnd := hK.image continuous_snd
  let : IsFiniteMeasure (volume.restrict (Prod.fst '' K)) :=
    isFiniteMeasure_restrict.mpr hfst.measure_ne_top
  have hi : IntegrableOn (fun q : ℝ × Space n => g q.2)
      ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact (hg.integrableOn_isCompact hsnd).comp_snd _
  exact hi.mono_set (fun q hq => ⟨⟨q, hq, rfl⟩, ⟨q, hq, rfl⟩⟩)

private lemma integrableOn_of_zero_off_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} {μ : Measure (ℝ × Space n)} {f : ℝ × Space n → E}
    {S K : Set (ℝ × Space n)} (hS : MeasurableSet S) (hf : LocallyIntegrableOn f S μ)
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hzero : ∀ q ∈ S, q ∉ K → f q = 0) : IntegrableOn f S μ := by
  have hi := hf.integrableOn_compact_subset hKS hK
  have he : EqOn (K.indicator f) f S := by
    intro q hq
    by_cases hqK : q ∈ K
    · simp [hqK]
    · simp [hqK, hzero q hq hqK]
  have hfi : IntegrableOn (K.indicator f) S μ := by
    rw [integrableOn_indicator_iff hK.measurableSet.nullMeasurableSet]
    simpa only [inter_eq_left.mpr hKS] using hi
  exact hfi.congr_fun he hS

/-- The pullback test derivative is integrable against locally L¹ data. Its
support lies in one compact spatial set for every time in the slab. -/
lemma lagrangian_test_integrable {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {g : Space n → ℝ} (hg : LocallyIntegrable g volume)
    (φ : ContinuityTest n T) :
    IntegrableOn (fun q : ℝ × Space n =>
      g q.2 * continuityTestDerivative b φ.toFun q.1 (X q.1 0 q.2))
      (Icc 0 T ×ˢ univ) (volume.prod volume) := by
  let K := Prod.snd '' tsupport φ.toFun
  let L := (fun q : ℝ × Space n => X 0 q.1 q.2) '' (Icc 0 T ×ˢ K)
  have hK : IsCompact K := φ.compact.image continuous_snd
  have hL : IsCompact L := compact_inverse_flow_image hT hX hK
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hflow : ContinuousOn (fun q : ℝ × Space n => (q.1, X q.1 0 q.2))
      (Icc 0 T ×ˢ univ) :=
    continuousOn_fst.prodMk (hX.regular.continuousOn.comp
      (continuousOn_fst.prodMk (continuousOn_const.prodMk continuousOn_snd))
      (fun _ hq => ⟨hq.1, h0, mem_univ _⟩))
  have hD := (continuityTestDerivative_continuousOn b φ).comp hflow
    (fun _ hq => ⟨hq.1, mem_univ _⟩)
  have hlocal := ((locallyIntegrable_snd hg).locallyIntegrableOn (Icc 0 T ×ˢ univ)).mul_continuousOn
    hD (isClosed_Icc.prod isClosed_univ).isLocallyClosed
  apply integrableOn_of_zero_off_compact (measurableSet_Icc.prod MeasurableSet.univ) hlocal (isCompact_Icc.prod hL)
    (prod_mono Subset.rfl (subset_univ _))
  intro q hq hnot
  have hy : q.2 ∉ L := fun hy => hnot ⟨hq.1, hy⟩
  have hφnot : (q.1, X q.1 0 q.2) ∉ tsupport φ.toFun := by
    intro hmem
    apply hy
    refine ⟨(q.1, X q.1 0 q.2), ⟨hq.1, ⟨(q.1, X q.1 0 q.2), hmem, rfl⟩⟩, ?_⟩
    exact (hX.composition 0 h0 q.1 hq.1 0 h0 q.2).trans (hX.initial 0 h0 q.2)
  change g q.2 * continuityTestDerivative b φ.toFun q.1 (X q.1 0 q.2) = 0
  rw [continuityTestDerivative_eq_fderiv b (φ.smooth.differentiable (by simp)),
    fderiv_of_notMem_tsupport ℝ hφnot, zero_apply, mul_zero]

/-- Exact chain rule along each characteristic, with one-sided endpoint
interpretation inherited from the upstream flow. -/
lemma continuityTest_along_flow_hasDerivWithinAt {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) (φ : ContinuityTest n T) (y : Space n)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => φ.toFun (r, X r 0 y))
      (continuityTestDerivative b φ.toFun t (X t 0 y)) (Icc 0 T) t := by
  have hdX := (hX.solution 0 ⟨le_rfl, hT⟩ y).2 t ht
  have hprod : HasDerivWithinAt (fun r => (r, X r 0 y))
      (1, b.velocity (t, X t 0 y)) (Icc 0 T) t :=
    (hasDerivAt_id t).hasDerivWithinAt.prodMk hdX
  have hφ := (φ.smooth.differentiable (by simp) (t, X t 0 y)).hasFDerivAt
  have hd := hφ.comp_hasDerivWithinAt t hprod
  rw [continuityTestDerivative_eq_fderiv b (φ.smooth.differentiable (by simp))]
  exact hd

/-- The derivative of a pulled-back test integrates to its initial boundary
term. The terminal term is zero by the test's prescribed support condition. -/
lemma integral_continuityTest_along_flow {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) (φ : ContinuityTest n T) (y : Space n) :
    (∫ t in Icc 0 T, continuityTestDerivative b φ.toFun t (X t 0 y)) =
      -φ.toFun (0, y) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hx := hX.solution 0 h0 y
  have hpath : ContinuousOn (fun r => (r, X r 0 y)) (Icc 0 T) :=
    continuousOn_id.prodMk hx.1
  have hcont := φ.smooth.continuous.comp_continuousOn hpath
  have hD : ContinuousOn (fun r => continuityTestDerivative b φ.toFun r (X r 0 y))
      (Icc 0 T) :=
    (continuityTestDerivative_continuousOn b φ).comp hpath (fun r hr => ⟨hr, mem_univ _⟩)
  have hint : IntervalIntegrable (fun r => continuityTestDerivative b φ.toFun r (X r 0 y))
      volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hD.integrableOn_Icc
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hcont
    (fun t ht => (continuityTest_along_flow_hasDerivWithinAt hT hX φ y ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)) hint
  obtain ⟨ε, hε, hterminal⟩ := φ.terminal
  have hterm := hterminal T ⟨sub_le_self _ hε.le, le_rfl⟩ (X T 0 y)
  simp only [Function.comp_apply] at he
  rw [hterm, hX.initial 0 h0, zero_sub] at he
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at he
  exact he

lemma continuityTest_initial_integrable {n : ℕ} {T : ℝ}
    {g : Space n → ℝ} (hg : LocallyIntegrable g volume) (φ : ContinuityTest n T) :
    Integrable (fun x => g x * φ.toFun (0, x)) volume := by
  have hc : HasCompactSupport (fun x : Space n => φ.toFun (0, x)) := by
    apply HasCompactSupport.of_support_subset_isCompact (φ.compact.image continuous_snd)
    intro x hx
    exact ⟨(0, x), subset_tsupport _ hx, rfl⟩
  exact hg.integrable_smul_right_of_hasCompactSupport
    (φ.smooth.continuous.comp (continuous_const.prodMk continuous_id)) hc

/-- The weak continuity equation with initial density g. Only the smooth
test is differentiated; g remains an arbitrary locally integrable datum. -/
lemma transportedDensity_weak_identity {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) {b : SlabField n T} {X : ℝ → ℝ → Space n → Space n}
    (hX : SlabFlowProperties b X) {g : Space n → ℝ} (hg : LocallyIntegrable g volume)
    (φ : ContinuityTest n T) :
    (∫ t in Icc 0 T, ∫ x, transportedDensity X g t x * continuityTestDerivative b φ.toFun t x) =
      -(∫ x, g x * φ.toFun (0, x)) := by
  have hi := lagrangian_test_integrable hT hX hg φ
  have hp : Integrable (fun q : ℝ × Space n =>
      g q.2 * continuityTestDerivative b φ.toFun q.1 (X q.1 0 q.2))
      ((volume.restrict (Icc 0 T)).prod volume) := by
    change Integrable _ ((volume.prod volume).restrict (Icc 0 T ×ˢ univ)) at hi
    rw [← Measure.prod_restrict, Measure.restrict_univ] at hi
    exact hi
  calc
    _ = ∫ t in Icc 0 T, ∫ y, g y * continuityTestDerivative b φ.toFun t (X t 0 y) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact integral_transportedDensity hn hT hX g (fun x => continuityTestDerivative b φ.toFun t x) ht
    _ = ∫ y, ∫ t in Icc 0 T, g y * continuityTestDerivative b φ.toFun t (X t 0 y) :=
      integral_integral_swap hp
    _ = ∫ y, -(g y * φ.toFun (0, y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_const_mul, integral_continuityTest_along_flow hT hX φ y, mul_neg]
    _ = _ := integral_neg _

/-- The complete density construction, slice and space-time local L¹
regularity, and distributional initial-value continuity equation. -/
theorem transportedDensity_solution : P201Specs.Hyperbolic.transportedDensityStatement := by
  intro n hn T hT b X hX g hg
  refine ⟨?_, fun t ht y => transportedDensity_characteristic hX hT g ht y⟩
  refine ⟨transportedDensity_locallyIntegrableOn_slab hn hT hX hg,
    fun t ht => transportedDensity_locallyIntegrable hn hT hX hg ht,
    transportedDensity_initial hX hT g, ?_⟩
  intro φ
  have hi := transportedDensity_test_integrable hn hT hX hg φ
  have hp : Integrable (fun q : ℝ × Space n =>
      transportedDensity X g q.1 q.2 * continuityTestDerivative b φ.toFun q.1 q.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
    change Integrable _ ((volume.prod volume).restrict (Icc 0 T ×ˢ univ)) at hi
    rw [← Measure.prod_restrict, Measure.restrict_univ] at hi
    exact hi
  exact ⟨continuityTest_initial_integrable hg φ, hi, hp.integral_prod_left,
    transportedDensity_weak_identity hn hT hX hg φ⟩

/-- Construct a flow with every density conclusion from the coefficient
hypotheses alone, using the upstream flow-existence theorem. -/
theorem densityFlow : P201Specs.Hyperbolic.densityFlowStatement := by
  intro n hn T hT b
  obtain ⟨X, hX⟩ := slabFlow n hn T hT b
  exact ⟨X, hX, flowJacobian_formula n hn T hT b X hX,
    transportedDensity_solution n hn T hT b X hX⟩

/-- The assigned Jacobian and distributional-density assertions. -/
theorem continuityEquation : P201Specs.Hyperbolic.continuityEquationStatement :=
  ⟨flowJacobian_formula, transportedDensity_solution, densityFlow⟩

end P201.Hyperbolic
