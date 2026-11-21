import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.HomotopyOperator
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.Cartan
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The smooth homotopy operator on the intrinsic de Rham complex.
Local ambient extensions give smooth compact-parameter integrals, including on
boundary cylinder charts. The time-first contraction determines the signs, and
the degree-zero identity is proved separately. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SmoothManifolds.HomotopyData
open ModelData AtlasData MapData TangentData DifferentialData Set Filter
open scoped Topology
universe u

private theorem contDiff_snoc_const {n : ℕ} (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclidean n => (Fin.snoc x t : Euclidean (n+1))) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Euclidean n => t))
  · simpa using (contDiff_apply ℝ (fun _ : Fin n => ℝ) j :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclidean n => x j))

theorem IsSmoothHomotopy.slice_smooth {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F) (t : UnitInterval) :
    IsSmoothMap S T (fun p => F (p,t)) := by
  have hf : Continuous (fun p => F (p,t)) := hF.1.comp (continuous_id.prodMk continuous_const)
  intro p
  refine ⟨hf.continuousAt, ?_⟩
  intro c hc d hd hp hq
  let q : {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source} :=
    ⟨(p,t), hp, hq⟩
  obtain ⟨U,hU,hpU,G,hG,hagree⟩ := hF.2 c hc d hd q
  let e : Euclidean n → Euclidean (n+1) := fun x => Fin.snoc x t.val
  have he : ContDiff ℝ (⊤ : ℕ∞) e := contDiff_snoc_const t.val
  refine ⟨e ⁻¹' U, hU.preimage he.continuous, hpU, G ∘ e,
    hG.comp he.contDiffOn (fun _ h => h), ?_⟩
  have hccont : ContinuousAt (fun x => (c x).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  filter_upwards [c.open_source.mem_nhds hp,
    hf.continuousAt (d.open_source.mem_nhds hq),
    hccont (hU.preimage he.continuous |>.mem_nhds hpU)] with y hy hyq hyU
  exact hagree ⟨(y,t),hy,hyq⟩ hyU

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyData
open ModelData AtlasData MapData TangentData DifferentialData Set Filter
open scoped Topology
universe u

@[simp] theorem intervalTime_val_of_mem (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (intervalTime s).val = s := by
  simp only [intervalTime, min_eq_right hs.2, max_eq_right hs.1]

@[simp] theorem intervalTime_coe (t : UnitInterval) : intervalTime t.val = t := by
  apply Subtype.ext
  exact intervalTime_val_of_mem t.val t.property

private theorem continuous_intervalTime : Continuous intervalTime := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_const.min continuous_id)

private theorem contDiff_const_snoc {n : ℕ} (x : Euclidean n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (Fin.snoc x t : Euclidean (n+1))) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact contDiff_id
  · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => x j))

/-- Each target-chart expression of a time trace has a genuine derivative within
    the closed parameter interval, including either endpoint. -/
theorem IsSmoothHomotopy.time_chart_hasDeriv {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (p : M) (t : UnitInterval) (d : ModelChart m b N)
    (hd : d ∈ T.smoothStructure.val) (hpt : F (p,t) ∈ d.source) :
    ∃ v : Euclidean m,
      HasDerivWithinAt (fun s => (d (F (p,intervalTime s))).val) v (Icc 0 1) t.val := by
  obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p
  let q : {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source} :=
    ⟨(p,t),hp,hpt⟩
  obtain ⟨U,hU,hptU,G,hG,hagree⟩ := hF.2 c hc d hd q
  let e : ℝ → Euclidean (n+1) := fun s => Fin.snoc (c p).val s
  have he : ContDiff ℝ (⊤ : ℕ∞) e := contDiff_const_snoc (c p).val
  have hGd : DifferentiableAt ℝ G (e t.val) :=
    (hG.contDiffAt (hU.mem_nhds hptU)).differentiableAt (by simp)
  have hder := (hGd.comp t.val (he.differentiable (by simp) t.val)).hasDerivAt
  refine ⟨_, hder.hasDerivWithinAt.congr_of_eventuallyEq_of_mem ?_ t.property⟩
  have hf : Continuous (fun s => F (p,intervalTime s)) :=
    hF.1.comp (continuous_const.prodMk continuous_intervalTime)
  have hpt' : F (p,intervalTime t.val) ∈ d.source := by simpa using hpt
  have h1 : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t.val, F (p,intervalTime s) ∈ d.source :=
    nhdsWithin_le_nhds (hf.continuousAt (d.open_source.mem_nhds hpt'))
  have h2 : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t.val, e s ∈ U :=
    nhdsWithin_le_nhds (he.continuous.continuousAt (hU.mem_nhds hptU))
  filter_upwards [h1,h2,self_mem_nhdsWithin] with s hs hsU hsI
  symm
  simpa only [Function.comp_apply, e, intervalTime_val_of_mem s hsI] using
    hagree ⟨(p,intervalTime s),hp,hs⟩ (by
      simpa only [intervalTime_val_of_mem s hsI] using hsU)

/-- The interval trace differentiates every representative of a smooth germ. -/
theorem IsSmoothHomotopy.time_germ_hasDeriv {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (p : M) (t : UnitInterval) (g : SmoothGerm T (F (p,t))) :
    ∃ v : ℝ, ∀ r : N → ℝ, Germ.ofFun r = g.val →
      HasDerivWithinAt (fun s => r (F (p,intervalTime s))) v (Icc 0 1) t.val := by
  obtain ⟨d,hd,hpt⟩ := T.smoothStructure.property.1.1 (F (p,t))
  obtain ⟨v,hv⟩ := hF.time_chart_hasDeriv p t d hd hpt
  obtain ⟨G,⟨U,hU,hptU,hG⟩,hrep⟩ :=
    exists_germChartExtension T (F (p,t)) d hd hpt g
  have hGd : DifferentiableAt ℝ G (d (F (p,t))).val :=
    (hG.contDiffAt (hU.mem_nhds hptU)).differentiableAt (by simp)
  refine ⟨fderiv ℝ G (d (F (p,t))).val v, ?_⟩
  intro r hr
  have hder := hGd.hasFDerivAt.comp_hasDerivWithinAt_of_eq t.val hv
    (by simp only [intervalTime_coe])
  have hf : Continuous (fun s => F (p,intervalTime s)) :=
    hF.1.comp (continuous_const.prodMk continuous_intervalTime)
  have heq : (fun s => r (F (p,intervalTime s))) =ᶠ[𝓝[Icc (0 : ℝ) 1] t.val]
      (fun s => G (d (F (p,intervalTime s))).val) := by
    apply (Germ.coe_eq.mp (hr.trans hrep.symm)).comp_tendsto
    simpa only [ContinuousWithinAt, intervalTime_coe] using
      (hf.continuousAt.continuousWithinAt : ContinuousWithinAt
        (fun s => F (p,intervalTime s)) (Icc 0 1) t.val)
  exact hder.congr_of_eventuallyEq_of_mem heq t.property

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyData
open ModelData AtlasData MapData TangentData DifferentialData Set Filter
open scoped Topology
universe u

/-- Differentiation of the interval trace is intrinsically a point derivation. -/
theorem IsSmoothHomotopy.exists_time_velocity {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (p : M) (t : UnitInterval) :
    ∃ D : TangentSpace T (F (p,t)),
      ∀ (g : SmoothGerm T (F (p,t))) (r : N → ℝ), Germ.ofFun r = g.val →
        HasDerivWithinAt (fun s => r (F (p,intervalTime s))) (D.val g) (Icc 0 1) t.val := by
  classical
  choose d hd using hF.time_germ_hasDeriv p t
  have hu : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) t.val :=
    uniqueDiffOn_Icc_zero_one t.val t.property
  have rep (g : SmoothGerm T (F (p,t))) : ∃ r : N → ℝ, Germ.ofFun r = g.val := by
    obtain ⟨r,_,hr⟩ := (mem_smoothGermAlgebra_iff T (F (p,t)) _).mp g.property
    exact ⟨r,hr.symm⟩
  let L : SmoothGerm T (F (p,t)) →ₗ[ℝ] ℝ :=
    { toFun := d
      map_add' := by
        intro g h
        obtain ⟨r,hr⟩ := rep g
        obtain ⟨s,hs⟩ := rep h
        have hsum : Germ.ofFun (fun y => r y + s y) = (g+h).val := by
          change Germ.ofFun r + Germ.ofFun s = g.val + h.val
          rw [hr,hs]
        exact UniqueDiffWithinAt.eq_deriv _ hu (hd (g+h) _ hsum) ((hd g r hr).add (hd h s hs))
      map_smul' := by
        intro c g
        obtain ⟨r,hr⟩ := rep g
        have hsmul : Germ.ofFun (fun y => c * r y) = (c • g).val := by
          change c • Germ.ofFun r = c • g.val
          rw [hr]
        exact UniqueDiffWithinAt.eq_deriv _ hu (hd (c • g) _ hsmul) ((hd g r hr).const_mul c) }
  have hL : L ∈ pointDerivations (germEvaluation T (F (p,t))) := by
    intro g h
    obtain ⟨r,hr⟩ := rep g
    obtain ⟨s,hs⟩ := rep h
    have hprod : Germ.ofFun (fun y => r y * s y) = (g*h).val := by
      change Germ.ofFun r * Germ.ofFun s = g.val * h.val
      rw [hr,hs]
    have hrp : r (F (p,t)) = germEvaluation T (F (p,t)) g := congrArg Germ.value hr
    have hsp : s (F (p,t)) = germEvaluation T (F (p,t)) h := congrArg Germ.value hs
    have heq := UniqueDiffWithinAt.eq_deriv _ hu (hd (g*h) _ hprod) ((hd g r hr).mul (hd h s hs))
    change d (g*h) = _
    simp only [intervalTime_coe] at heq
    rw [hrp,hsp] at heq
    change d (g*h) = germEvaluation T (F (p,t)) g * d h +
      germEvaluation T (F (p,t)) h * d g
    exact heq.trans (by ring)
  exact ⟨⟨L,hL⟩,hd⟩

/-- Spatial and positive time derivatives are consequences of joint smoothness,
    with no additional regularity assumptions. -/
def IsSmoothHomotopy.differentials {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F) :
    HomotopyDifferentials S T F where
  spatial t p := differential S T (fun q => F (q,t)) (hF.slice_smooth t) p
  spatial_correct t p := differential_spec S T (fun q => F (q,t)) (hF.slice_smooth t) p
  velocity p t := (hF.exists_time_velocity p t).choose
  velocity_correct p t := (hF.exists_time_velocity p t).choose_spec

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyResults
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData HomotopyData Set Filter
open scoped Topology
universe u v

@[simp] theorem intervalTime_coe (t : UnitInterval) : intervalTime t.val = t := by
  apply Subtype.ext
  simp only [intervalTime, min_eq_right t.property.2, max_eq_right t.property.1]

/-- The coefficient equation of d(α+dt∧β), followed by FTC. Its hypotheses
are the precise local differential relation, not the desired endpoint identity. -/
theorem coefficient_endpoint_identity
    (α δ γ : ℝ → ℝ)
    (hα : ContinuousOn α (Icc 0 1))
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt α (δ t + γ t) t)
    (hδ : IntervalIntegrable δ MeasureTheory.volume 0 1)
    (hγ : IntervalIntegrable γ MeasureTheory.volume 0 1) :
    (∫ t in (0 : ℝ)..1, δ t) + (∫ t in (0 : ℝ)..1, γ t) = α 1 - α 0 := by
  rw [← intervalIntegral.integral_add hδ hγ]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hα hderiv
    (hδ.add hγ)

/-- The same coefficient formula in the sign convention γ=∂tα-d_Mβ. -/
theorem coefficient_endpoint_identity_sub
    (α α' δ : ℝ → ℝ)
    (hα : ContinuousOn α (Icc 0 1))
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt α (α' t) t)
    (hα' : IntervalIntegrable α' MeasureTheory.volume 0 1)
    (hδ : IntervalIntegrable δ MeasureTheory.volume 0 1) :
    (∫ t in (0 : ℝ)..1, δ t) + (∫ t in (0 : ℝ)..1, α' t - δ t) = α 1 - α 0 := by
  apply coefficient_endpoint_identity α δ (fun t => α' t - δ t) hα
  · intro t ht
    simpa only [add_sub_cancel] using hderiv t ht
  · exact hδ
  · exact hα'.sub hδ

/-- The finite list of coefficient integrals respects addition. -/
theorem coefficient_integral_add {ι : Type*} (f g : ℝ → ι → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun t => f t i) MeasureTheory.volume 0 1)
    (hg : ∀ i, IntervalIntegrable (fun t => g t i) MeasureTheory.volume 0 1) :
    (fun i => ∫ t in (0 : ℝ)..1, f t i + g t i) =
      (fun i => ∫ t in (0 : ℝ)..1, f t i) + (fun i => ∫ t in (0 : ℝ)..1, g t i) := by
  funext i
  exact intervalIntegral.integral_add (hf i) (hg i)

/-- Scalar linearity is valid even before integrability has been established. -/
theorem coefficient_integral_smul {ι : Type*} (r : ℝ) (f : ℝ → ι → ℝ) :
    (fun i => ∫ t in (0 : ℝ)..1, r * f t i) =
      r • (fun i => ∫ t in (0 : ℝ)..1, f t i) := by
  funext i
  exact intervalIntegral.integral_const_mul r (fun t => f t i)

/-- A multilinear alternating form has no term containing two multiples of
one fixed vector. This is the reason the cylinder decomposition has two parts. -/
theorem alternating_two_multiples {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [DecidableEq ι] (A : AlternatingMap ℝ V ℝ ι)
    (w : ι → V) (e : V) (i j : ι) (hij : i ≠ j) (r s : ℝ)
    (hi : w i = r • e) (hj : w j = s • e) : A w = 0 := by
  have hw : w = Function.update (Function.update w i (r • e)) j (s • e) := by
    rw [← hi, ← hj]
    simp
  rw [hw, A.map_update_smul, Function.update_comm hij, A.map_update_smul]
  have hz : A (Function.update (Function.update w j e) i e) = 0 := by
    apply A.map_eq_zero_of_eq _ (i := i) (j := j) _ hij
    simp [hij.symm]
  simp only [hz, smul_zero]

/-- The complete dt-first expansion, before passing to manifold fibers. -/
theorem alternating_spatial_time_expansion {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (A : AlternatingMap ℝ V ℝ (Fin (k+1)))
    (x : Fin (k+1) → V) (r : Fin (k+1) → ℝ) (e : V) :
    A (fun i => x i + r i • e) = A x +
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val * r i *
        A (Fin.cons e (fun j => x (i.succAbove j))) := by
  classical
  have h := A.toMultilinearMap.map_add_eq_map_add_linearDeriv_add x (fun i => r i • e)
  have hz : (∑ s : Finset (Fin (k+1)) with 2 ≤ s.card,
      A (s.piecewise (fun i => r i • e) x)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hcard : 1 < s.card := (Finset.mem_filter.mp hs).2
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
    apply alternating_two_multiples A _ e i j hij (r i) (r j)
    · exact Finset.piecewise_eq_of_mem s _ _ hi
    · exact Finset.piecewise_eq_of_mem s _ _ hj
  rw [MultilinearMap.linearDeriv_apply] at h
  change A (fun i => x i + r i • e) = (A x +
    (∑ i, A (Function.update x i (r i • e)))) + _ at h
  change (∑ s : Finset (Fin (k+1)) with 2 ≤ s.card,
    A.toMultilinearMap (s.piecewise (fun i => r i • e) x)) = 0 at hz
  rw [hz, add_zero] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [A.map_update_smul, ← Fin.insertNth_removeNth, A.map_insertNth]
  simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [mul_assoc, mul_left_comm]
  rfl

section FiberComponents
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

/-- The defined beta uses the time vector in its first slot, with no factorial
or orientation factor. -/
theorem evaluate_beta (C : CotangentBundle S) (D : HomotopyDifferentials S T F)
    {k : ℕ} (ω : Field T (k+1)) (t : UnitInterval) (p : M)
    (v : Fin k → TangentSpace S p) :
    evaluate (TangentSpace S p) k (beta C D ω t p) v =
      evaluate (TangentSpace T (F (p,t))) (k+1) (ω (F (p,t)))
        (Fin.cons (D.velocity p t) (fun j => D.spatial t p (v j))) := by
  change (CartanData.evaluationEquiv C.tangent.fiberCoordinates p k
    (beta C D ω t p)) v = _
  rw [beta, LinearEquiv.apply_symm_apply]
  rfl

/-- The dt-first decomposition exists for the actual pullback and contraction
on the shared exterior fibers, in every degree. -/
theorem dtFirstDecomposition_exists (C : CotangentBundle S)
    (D : HomotopyDifferentials S T F) {k : ℕ} (ω : Field T (k+1))
    (t : UnitInterval) (p : M) :
    HasDtFirstDecomposition C D ω t p (beta C D ω t p) := by
  intro z
  have h := alternating_spatial_time_expansion (k := k)
    (evaluate (TangentSpace T (F (p,t))) (k+1) (ω (F (p,t))))
    (fun i => D.spatial t p (z i).1) (fun i => (z i).2) (D.velocity p t)
  rw [h]
  congr 1
  · exact (FormPullbackResults.pullback_apply S T (fun q => F (q,t))
      (D.spatial t) (k+1) ω p (fun i => (z i).1)).symm
  · apply Finset.sum_congr rfl
    intro i _
    rw [evaluate_beta]

/-- Uniqueness follows by testing the decomposition on the time vector followed
by arbitrary spatial vectors, including the empty tuple in degree one. -/
theorem dtFirstDecomposition_unique (C : CotangentBundle S)
    (D : HomotopyDifferentials S T F) {k : ℕ} (ω : Field T (k+1))
    (t : UnitInterval) (p : M) (β : Fiber (TangentSpace S p) k)
    (hβ : HasDtFirstDecomposition C D ω t p β) : β = beta C D ω t p := by
  apply (CartanData.evaluationEquiv C.tangent.fiberCoordinates p k).injective
  change evaluate (TangentSpace S p) k β =
    evaluate (TangentSpace S p) k (beta C D ω t p)
  apply AlternatingMap.ext
  intro v
  rw [evaluate_beta]
  let z : Fin (k+1) → TangentSpace S p × ℝ :=
    Fin.cons (0, 1) (fun j => (v j, 0))
  have h := hβ z
  have hhor : evaluate (TangentSpace S p) (k+1) (alpha D ω t p)
      (fun i => (z i).1) = 0 := by
    apply AlternatingMap.map_coord_zero _ (0 : Fin (k+1))
    rfl
  rw [hhor, zero_add] at h
  have hz : (fun i => D.spatial t p (z i).1 + (z i).2 • D.velocity p t) =
      Fin.cons (D.velocity p t) (fun j => D.spatial t p (v j)) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [z]
  rw [hz] at h
  simp only [Fin.sum_univ_succ, z, Fin.cons_zero, Fin.cons_succ,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero] at h
  simpa using h.symm


/-- The dt-first component is linear on the original fields. -/
theorem beta_add (C : CotangentBundle S) (D : HomotopyDifferentials S T F)
    {k : ℕ} (ω η : Field T (k+1)) (t : UnitInterval) :
    beta C D (ω+η) t = beta C D ω t + beta C D η t := by
  funext p
  simp only [beta, Pi.add_apply, map_add, AlternatingMap.curryLeft_add,
    LinearMap.add_apply, AlternatingMap.add_compLinearMap]

theorem beta_smul (C : CotangentBundle S) (D : HomotopyDifferentials S T F)
    {k : ℕ} (r : ℝ) (ω : Field T (k+1)) (t : UnitInterval) :
    beta C D (r • ω) t = r • beta C D ω t := by
  funext p
  apply (CartanData.evaluationEquiv C.tangent.fiberCoordinates p k).injective
  change evaluate (TangentSpace S p) k (beta C D (r • ω) t p) =
    evaluate (TangentSpace S p) k (r • beta C D ω t p)
  apply AlternatingMap.ext
  intro v
  rw [evaluate_beta]
  simp only [Pi.smul_apply, map_smul, smul_apply]
  rw [evaluate_beta]

/-- If an operator is represented by the integrated coefficients in every chart,
that representation determines it uniquely. -/
theorem coefficientIntegral_unique {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (D : HomotopyDifferentials S T F)
    (op op' : ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k)
    (h : IsCoefficientIntegral K J D op) (h' : IsCoefficientIntegral K J D op') :
    op = op' := by
  funext k
  apply LinearMap.ext
  intro ω
  apply Subtype.ext
  funext p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  exact ExteriorAlgebraResults.coefficients_unique C k c hc (op k ω).val (op' k ω).val
    (fun q I => (h k ω c hc q I).2.trans (h' k ω c hc q I).2.symm) ⟨p,hp⟩

end FiberComponents

section AmbientIntegration
open Metric MeasureTheory
open scoped ContDiff
universe w
variable {E W : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace W] in
theorem integral_hasFDerivAt (F : E × ℝ → W) (G : E × ℝ → E →L[ℝ] W)
    (hF : Continuous F) (hG : Continuous G)
    (hD : ∀ x t, HasFDerivAt (fun y => F (y,t)) (G (x,t)) x) (x : E) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, F (y,t))
      (∫ t in (0 : ℝ)..1, G (x,t)) x := by
  obtain ⟨R, hR⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).exists_bound_of_continuousOn hG.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x 1) (bound := fun _ => R) (ball_mem_nhds x (by norm_num))
  · exact Eventually.of_forall fun y =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro t ht y hy
    apply hR (y,t)
    constructor
    · exact mem_closedBall.mpr (mem_ball.mp hy).le
    · simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc ht
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t _ y _ => hD y t

theorem contDiff_integral (n : ℕ) (F : E × ℝ → W) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) := by
  induction n generalizing W with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x t => F (x,t)) hF.continuous 0 1
  | succ n ih =>
    let G : E × ℝ → E →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hG : ContDiff ℝ n G := by
      exact (hF.fderiv_right (m := n) (by norm_cast)).clm_comp contDiff_const
    have hD : ∀ x t, HasFDerivAt (fun y => F (y,t)) (G (x,t)) x := by
      intro x t
      simpa only [G, Function.comp_def, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] using
        (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
          ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t))
    have hI := integral_hasFDerivAt F G hF.continuous hG.continuous hD
    have hfd : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) =
        fun x => ∫ t in (0 : ℝ)..1, G (x,t) := funext fun x => (hI x).fderiv
    rw [show (↑(n+1) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨fun x => (hI x).differentiableAt, ?_, ?_⟩
    · simp
    · rw [hfd]
      exact ih G hG

theorem smooth_integral (F : E × ℝ → W) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_integral n F (contDiff_infty.mp hF n)



/-- A common smooth ambient extension on a spatial tube gives exactly the local
extension required for the integrated coefficient, including on a source face. -/
theorem integral_hasLocalExtensionAt {n : ℕ} {D : Type*}
    (ι : D → Euclidean n) (f : D → UnitInterval → ℝ) (x : D)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hx : ι x ∈ U)
    (G : Euclidean n × ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hagree : ∀ y, ι y ∈ U → ∀ t : UnitInterval, G (ι y,t.val) = f y t) :
    HasLocalContDiffExtensionAt (⊤ : ℕ∞) ι
      (fun y => ∫ t in (0 : ℝ)..1, f y (intervalTime t)) x := by
  refine ⟨U, hU, hx, fun z => ∫ t in (0 : ℝ)..1, G (z,t),
    (smooth_integral G hG).contDiffOn, ?_⟩
  intro y hy
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  have heq : intervalTime t = (⟨t, ht'⟩ : UnitInterval) := intervalTime_coe ⟨t,ht'⟩
  change G (ι y,t) = f y (intervalTime t)
  rw [heq]
  exact hagree y hy ⟨t,ht'⟩

set_option backward.isDefEq.respectTransparency false
/-- Exterior differentiation commutes with compact-interval integration. -/
theorem extDeriv_integral {k : ℕ}
    (F : E × ℝ → E [⋀^Fin k]→L[ℝ] ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : E) :
    extDeriv (fun y => ∫ t in (0 : ℝ)..1, F (y,t)) x =
      ∫ t in (0 : ℝ)..1, extDeriv (fun y => F (y,t)) x := by
  let G : E × ℝ → E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ := fun z =>
    (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hG : Continuous G := by
    exact ((hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_comp
      contDiff_const).continuous
  have hD : ∀ y t, HasFDerivAt (fun z => F (z,t)) (G (y,t)) y := by
    intro y t
    simpa only [G, Function.comp_def, ContinuousLinearMap.inl_apply,
      Prod.mk_add_mk, add_zero, zero_add] using
      (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t))
  have hI := integral_hasFDerivAt F G hF.continuous hG hD x
  simp only [extDeriv, hI.fderiv, (hD x _).fderiv]
  letI : ENormedAddMonoid (E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) :=
    @NormedAddGroup.toENormedAddMonoid (E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) inferInstance
  have hgInt : IntervalIntegrable (fun t => G (x,t)) volume 0 1 :=
    @Continuous.intervalIntegrable (E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) inferInstance
      volume inferInstance (fun t => G (x,t))
      (hG.comp (continuous_const.prodMk continuous_id)) 0 1
  exact (ContinuousLinearMap.intervalIntegral_comp_comm
    (𝕜 := ℝ) (E := (E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ))
    (F := E [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ (n := k)) hgInt).symm


end AmbientIntegration

end SmoothManifolds.HomotopyResults

namespace UniformExtension
open Set Filter
open scoped Topology Manifold ContDiff

variable {E F D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finitely many local ambient germs along a compact set can be glued to one
ambient extension on a common neighborhood. No regularity or injectivity is
required of the parametrization `ι`. -/
theorem exists_smooth_extension_near_compact (ι : D → E) (f : D → F)
    (K : Set E) (hK : IsCompact K)
    (H : ∀ z ∈ K, ∃ U : Set E, IsOpen U ∧ z ∈ U ∧
      ∃ g : E → F, ContDiffOn ℝ (⊤ : ℕ∞) g U ∧
        ∀ y : D, ι y ∈ U → g (ι y) = f y) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧
      ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧
        ∀ y : D, ι y ∈ V → g (ι y) = f y := by
  classical
  choose U hU hk g hg hagree using fun z : K => H z.val z.property
  let O : Set E := ⋃ z : K, U z
  have hO : IsOpen O := isOpen_iUnion hU
  have hKO : K ⊆ O := by
    intro z hz
    exact mem_iUnion_of_mem ⟨z,hz⟩ (hk ⟨z,hz⟩)
  obtain ⟨V, hV, hKV, hVO⟩ := normal_exists_closure_subset hK.isClosed hO hKO
  let target : E → Set F := fun z =>
    ⋂ y : D, ⋂ (_ : ι y = z), ⋂ (_ : z ∈ closure V), {f y}
  have hconv : ∀ z, Convex ℝ (target z) := by
    intro z
    apply convex_iInter
    intro y
    apply convex_iInter
    intro heq
    apply convex_iInter
    intro hz
    exact convex_singleton (f y)
  have hlocal : ∀ z : E, ∃ W ∈ 𝓝 z, ∃ q : E → F,
      ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, F)) (⊤ : ℕ∞) q W ∧
        ∀ y ∈ W, q y ∈ target y := by
    intro z
    by_cases hz : z ∈ closure V
    · obtain ⟨k, hzk⟩ := mem_iUnion.mp (hVO hz)
      refine ⟨U k, (hU k).mem_nhds hzk, g k, (hg k).contMDiffOn, ?_⟩
      intro w hw
      simp only [target, mem_iInter, mem_singleton_iff]
      intro y heq _
      rw [← heq]
      exact hagree k y (heq.symm ▸ hw)
    · refine ⟨(closure V)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hz,
        fun _ => 0, contMDiffOn_const, ?_⟩
      intro w hw
      simp only [target, mem_iInter, mem_singleton_iff]
      intro y heq hw'
      exact (hw hw').elim
  obtain ⟨q, hq⟩ := exists_contMDiffMap_forall_mem_convex_of_local (𝓘(ℝ, E)) hconv hlocal
  refine ⟨V, hV, hKV, q, q.contMDiff.contDiff, ?_⟩
  intro y hy
  have Hq := hq (ι y)
  simp only [target, mem_iInter, mem_singleton_iff] at Hq
  exact Hq y rfl (subset_closure hy)

/-- Compactness in the time variable makes the ambient extension uniform in
space, including when `ι` parametrizes a boundary or corner face. -/
theorem exists_smooth_extension_on_tube (ι : D → E) (T : Set ℝ)
    (hT : IsCompact T) (f : D → T → F) (x : D)
    (H : ∀ t : T, ∃ W : Set (E × ℝ), IsOpen W ∧ (ι x, t.val) ∈ W ∧
      ∃ G : E × ℝ → F, ContDiffOn ℝ (⊤ : ℕ∞) G W ∧
        ∀ (y : D) (s : T), (ι y, s.val) ∈ W → G (ι y,s.val) = f y s) :
    ∃ U : Set E, IsOpen U ∧ ι x ∈ U ∧
      ∃ G : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) G ∧
        ∀ y : D, ι y ∈ U → ∀ t : T, G (ι y,t.val) = f y t := by
  let emb : D × T → E × ℝ := fun z => (ι z.1,z.2.val)
  let ff : D × T → F := fun z => f z.1 z.2
  have hlocal : ∀ z ∈ ({ι x} ×ˢ T),
      ∃ W : Set (E × ℝ), IsOpen W ∧ z ∈ W ∧
        ∃ G : E × ℝ → F, ContDiffOn ℝ (⊤ : ℕ∞) G W ∧
          ∀ y : D × T, emb y ∈ W → G (emb y) = ff y := by
    rintro ⟨a,t⟩ ⟨ha,ht⟩
    have ha' : a = ι x := ha
    subst a
    obtain ⟨W, hW, hxt, G, hG, hagree⟩ := H ⟨t,ht⟩
    exact ⟨W, hW, hxt, G, hG, fun y hy => hagree y.1 y.2 hy⟩
  obtain ⟨V, hV, hKV, G, hG, hagree⟩ :=
    exists_smooth_extension_near_compact emb ff ({ι x} ×ˢ T)
      (isCompact_singleton.prod hT) hlocal
  obtain ⟨U, J, hU, hJ, hxU, hTJ, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hT hV hKV
  refine ⟨U, hU, hxU (mem_singleton _), G, hG, ?_⟩
  intro y hy t
  exact hagree (y,t) (hUV ⟨hy,hTJ t.property⟩)

open SmoothManifolds.ModelData SmoothManifolds.HomotopyData

/-- The shared `Fin.snoc` ambient-cylinder convention supplies exactly the
uniform tube extension needed for parameter integration. -/
theorem exists_smooth_extension_on_tube_of_local {n : ℕ}
    (ι : D → Euclidean n) (f : D → UnitInterval → F) (x : D)
    (H : ∀ t : UnitInterval, HasLocalContDiffExtensionAt (⊤ : ℕ∞)
      (fun z : D × UnitInterval => Fin.snoc (ι z.1) z.2.val)
      (fun z => f z.1 z.2) (x,t)) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ ι x ∈ U ∧
      ∃ G : Euclidean n × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) G ∧
        ∀ y : D, ι y ∈ U → ∀ t : UnitInterval, G (ι y,t.val) = f y t := by
  let snoc : Euclidean n × ℝ → Euclidean (n+1) := fun z => Fin.snoc z.1 z.2
  have hs : ContDiff ℝ (⊤ : ℕ∞) snoc := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [snoc, Fin.snoc_last] using (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Euclidean n × ℝ => z.2))
    · simpa only [snoc, Fin.snoc_castSucc, Function.comp_def] using
        (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).comp (contDiff_fst : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : Euclidean n × ℝ => z.1))
  apply exists_smooth_extension_on_tube ι (Icc (0 : ℝ) 1) isCompact_Icc f x
  intro t
  obtain ⟨U, hU, hxU, g, hg, hagree⟩ := H t
  refine ⟨snoc ⁻¹' U, hU.preimage hs.continuous, hxU, g ∘ snoc,
    hg.comp hs.contDiffOn (by intro z hz; exact hz), ?_⟩
  intro y s hys
  exact hagree (y,s) hys

/-- Joint local ambient smoothness along a compact time fiber implies local
ambient smoothness of its coefficient integral. -/
theorem integral_hasLocalExtensionAt_of_local {n : ℕ}
    (ι : D → Euclidean n) (f : D → UnitInterval → ℝ) (x : D)
    (H : ∀ t : UnitInterval, HasLocalContDiffExtensionAt (⊤ : ℕ∞)
      (fun z : D × UnitInterval => Fin.snoc (ι z.1) z.2.val)
      (fun z => f z.1 z.2) (x,t)) :
    HasLocalContDiffExtensionAt (⊤ : ℕ∞) ι
      (fun y => ∫ t in (0 : ℝ)..1, f y (intervalTime t)) x := by
  obtain ⟨U, hU, hxU, G, hG, hagree⟩ :=
    exists_smooth_extension_on_tube_of_local ι f x H
  exact SmoothManifolds.HomotopyResults.integral_hasLocalExtensionAt
    ι f x U hU hxU G hG hagree

end UniformExtension

namespace SmoothManifolds.HomotopyIntegration
open MeasureTheory Module
open scoped BigOperators
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℝ V]
  {ι : Type v} [Fintype ι]

def basisIntegral (b : Basis ι ℝ V) (f : ℝ → V) : V :=
  ∑ i, (∫ t in (0 : ℝ)..1, b.repr (f t) i) • b i

theorem basisIntegral_map (b : Basis ι ℝ V) (f : ℝ → V)
    (hf : ∀ i, IntervalIntegrable (fun t => b.repr (f t) i) volume 0 1)
    (L : V →ₗ[ℝ] ℝ) :
    L (basisIntegral b f) = ∫ t in (0 : ℝ)..1, L (f t) := by
  classical
  have hexpand (t : ℝ) : L (f t) = ∑ i, b.repr (f t) i * L (b i) := by
    conv_lhs => rw [← b.sum_repr (f t)]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp only [basisIntegral, map_sum, map_smul, smul_eq_mul]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact (intervalIntegral.integral_mul_const (L (b i)) _).symm
  · intro i hi
    exact (hf i).mul_const _

theorem basisIntegral_add (b : Basis ι ℝ V) (f g : ℝ → V)
    (hf : ∀ i, IntervalIntegrable (fun t => b.repr (f t) i) volume 0 1)
    (hg : ∀ i, IntervalIntegrable (fun t => b.repr (g t) i) volume 0 1) :
    basisIntegral b (f + g) = basisIntegral b f + basisIntegral b g := by
  classical
  simp only [basisIntegral, Pi.add_apply, map_add, Finsupp.add_apply]
  simp_rw [intervalIntegral.integral_add (hf _) (hg _), add_smul]
  exact Finset.sum_add_distrib

theorem basisIntegral_smul (b : Basis ι ℝ V) (r : ℝ) (f : ℝ → V) :
    basisIntegral b (r • f) = r • basisIntegral b f := by
  classical
  simp only [basisIntegral, Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [intervalIntegral.integral_const_mul]
  simp only [mul_smul, Finset.smul_sum]

end SmoothManifolds.HomotopyIntegration

namespace SmoothManifolds.HomotopyIntegration
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData FrameData ExteriorData DeRhamData
open Module Set MeasureTheory
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

def pointChart (S : SmoothManifold n a M) (p : M) :
    { c : ModelChart n a M // c ∈ S.smoothStructure.val ∧ p ∈ c.source } := by
  let h := S.smoothStructure.property.1.1 p
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

def chartExteriorBasis (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    Basis (Index n k) ℝ (Fiber (TangentSpace S p.val) k) :=
  (((Pi.basisFun ℝ (Fin n)).map
    (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm).dualBasis).exteriorPower k

def pointExteriorBasis (C : CotangentBundle S) (k : ℕ) (p : M) :
    Basis (Index n k) ℝ (Fiber (TangentSpace S p) k) :=
  chartExteriorBasis C k (pointChart S p).val (pointChart S p).property.1
    ⟨p,(pointChart S p).property.2⟩

def CoefficientsIntervalIntegrable (C : CotangentBundle S) (k : ℕ)
    (f : ℝ → Field S k) : Prop :=
  ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n k),
    IntervalIntegrable (fun t => coefficients C k c hc (f t) p I) volume 0 1

def integralField (C : CotangentBundle S) (k : ℕ) (f : ℝ → Field S k) : Field S k :=
  fun p => basisIntegral (pointExteriorBasis C k p) (fun t => f t p)

theorem pointExteriorBasis_integrable (C : CotangentBundle S) (k : ℕ)
    (f : ℝ → Field S k) (hf : CoefficientsIntervalIntegrable C k f) (p : M) :
    ∀ I, IntervalIntegrable
      (fun t => (pointExteriorBasis C k p).repr (f t p) I) volume 0 1 :=
  hf (pointChart S p).val (pointChart S p).property.1 ⟨p,(pointChart S p).property.2⟩

theorem coefficients_integralField (C : CotangentBundle S) (k : ℕ)
    (f : ℝ → Field S k) (hf : CoefficientsIntervalIntegrable C k f)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n k) :
    coefficients C k c hc (integralField C k f) p I =
      ∫ t in (0 : ℝ)..1, coefficients C k c hc (f t) p I := by
  exact basisIntegral_map (pointExteriorBasis C k p.val) (fun t => f t p.val)
    (pointExteriorBasis_integrable C k f hf p.val) ((chartExteriorBasis C k c hc p).coord I)

theorem integralField_add (C : CotangentBundle S) (k : ℕ) (f g : ℝ → Field S k)
    (hf : CoefficientsIntervalIntegrable C k f) (hg : CoefficientsIntervalIntegrable C k g) :
    integralField C k (f+g) = integralField C k f + integralField C k g := by
  funext p
  exact basisIntegral_add (pointExteriorBasis C k p) (fun t => f t p) (fun t => g t p)
    (pointExteriorBasis_integrable C k f hf p) (pointExteriorBasis_integrable C k g hg p)

theorem integralField_smul (C : CotangentBundle S) (k : ℕ) (r : ℝ)
    (f : ℝ → Field S k) : integralField C k (r • f) = r • integralField C k f := by
  funext p
  exact basisIntegral_smul (pointExteriorBasis C k p) r (fun t => f t p)

theorem isForm_integralField (C : CotangentBundle S) (k : ℕ) (B : FormBundle C k)
    (f : ℝ → Field S k) (hf : CoefficientsIntervalIntegrable C k f)
    (hs : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
      VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
        (fun p => ∫ t in (0 : ℝ)..1, coefficients C k c hc (f t) p I)) :
    IsForm B (integralField C k f) := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C k B _).mpr
  intro c hc I
  have heq : (fun p => coefficients C k c hc (integralField C k f) p I) =
      (fun p => ∫ t in (0 : ℝ)..1, coefficients C k c hc (f t) p I) := by
    funext p
    exact coefficients_integralField C k f hf c hc p I
  rw [heq]
  exact hs c hc I

/-- Integration of a linear family, restricted to the actual smooth-form submodule. -/
def integralFormsLinearMap {V : Type u} [AddCommGroup V] [Module ℝ V]
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B) (k : ℕ)
    (f : V →ₗ[ℝ] (ℝ → Field S k))
    (hf : ∀ x, CoefficientsIntervalIntegrable C k (f x))
    (hs : ∀ x (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
      VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
        (fun p => ∫ t in (0 : ℝ)..1, coefficients C k c hc (f x t) p I)) :
    V →ₗ[ℝ] K.forms k where
  toFun x := ⟨integralField C k (f x),
    (K.mem_forms k _).mpr (isForm_integralField C k (B k) (f x) (hf x) (hs x))⟩
  map_add' x y := Subtype.ext (by
    change integralField C k (f (x+y)) = integralField C k (f x) + integralField C k (f y)
    rw [map_add]
    exact integralField_add C k (f x) (f y) (hf x) (hf y))
  map_smul' r x := Subtype.ext (by
    change integralField C k (f (r • x)) = r • integralField C k (f x)
    rw [map_smul]
    exact integralField_smul C k r (f x))

theorem coefficients_integralFormsLinearMap {V : Type u} [AddCommGroup V] [Module ℝ V]
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B) (k : ℕ)
    (f : V →ₗ[ℝ] (ℝ → Field S k))
    (hf : ∀ x, CoefficientsIntervalIntegrable C k (f x))
    (hs : ∀ x (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
      VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
        (fun p => ∫ t in (0 : ℝ)..1, coefficients C k c hc (f x t) p I))
    (x : V) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n k) :
    coefficients C k c hc ((integralFormsLinearMap K k f hf hs) x).val p I =
      ∫ t in (0 : ℝ)..1, coefficients C k c hc (f x t) p I :=
  coefficients_integralField C k (f x) (hf x) c hc p I

end SmoothManifolds.HomotopyIntegration

namespace SmoothManifolds.HomotopyResults
open ModelData AtlasData HomotopyData Set
open scoped Topology
universe u

 theorem cylinder_chart_neighborhood {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {N : Type u} [TopologicalSpace N]
    (c : ModelChart n a M) (F : M × UnitInterval → N) (hF : Continuous F)
    (O : Set N) (hO : IsOpen O) (p : c.source) (t : UnitInterval)
    (hpt : F (p.val,t) ∈ O) :
    ∃ V : Set (Euclidean (n+1)), IsOpen V ∧ Fin.snoc (c p.val).val t.val ∈ V ∧
      ∀ (q : c.source) (s : UnitInterval),
        Fin.snoc (c q.val).val s.val ∈ V → F (q.val,s) ∈ O := by
  let e : c.source × UnitInterval → Euclidean (n+1) :=
    fun z => Fin.snoc (c z.1.val).val z.2.val
  have hc : Topology.IsEmbedding (fun q : c.source => (c q.val).val) :=
    Topology.IsEmbedding.comp (Topology.IsEmbedding.subtypeVal)
      c.isEmbedding_restrict
  have hs : Topology.IsEmbedding (fun z : Euclidean n × ℝ =>
      (Fin.snoc z.1 z.2 : Euclidean (n+1))) := by
    apply Topology.IsEmbedding.of_leftInverse
      (f := fun z : Euclidean (n+1) => (Fin.init z, z (Fin.last n)))
    · intro z
      simp
    · exact (continuous_pi fun j => (continuous_apply j.castSucc)).prodMk
        (continuous_apply (Fin.last n))
    · apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using (continuous_snd : Continuous (fun z : Euclidean n × ℝ => z.2))
      · simpa only [Fin.snoc_castSucc, Function.comp_def] using (continuous_apply j).comp
          (continuous_fst : Continuous (fun z : Euclidean n × ℝ => z.1))
  have he : Topology.IsEmbedding e := hs.comp (hc.prodMap Topology.IsEmbedding.subtypeVal)
  have hfo : IsOpen (fun z : c.source × UnitInterval => F (z.1.val,z.2) ∈ O) :=
    hO.preimage (hF.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  obtain ⟨V,hV,hpre⟩ := he.isInducing.isOpen_iff.mp hfo
  refine ⟨V,hV,?_,?_⟩
  · change (p,t) ∈ e ⁻¹' V
    rw [hpre]
    exact hpt
  · intro q s hqs
    change (q,s) ∈ {z : c.source × UnitInterval | F (z.1.val,z.2) ∈ O}
    rw [← hpre]
    exact hqs
end SmoothManifolds.HomotopyResults

namespace UniformExtension
open SmoothManifolds.ModelData SmoothManifolds.HomotopyData Set MeasureTheory
open scoped Topology
variable {D : Type*}

theorem intervalIntegrable_of_local {n : ℕ}
    (ι : D → Euclidean n) (f : D → UnitInterval → ℝ) (x : D)
    (H : ∀ t : UnitInterval, HasLocalContDiffExtensionAt (⊤ : ℕ∞)
      (fun z : D × UnitInterval => Fin.snoc (ι z.1) z.2.val)
      (fun z => f z.1 z.2) (x,t)) :
    IntervalIntegrable (fun t => f x (intervalTime t)) volume 0 1 := by
  obtain ⟨U, hU, hxU, G, hG, hagree⟩ :=
    exists_smooth_extension_on_tube_of_local ι f x H
  have hGI : IntervalIntegrable (fun t => G (ι x,t)) volume 0 1 :=
    (hG.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  apply hGI.congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc ht
  have heq : intervalTime t = (⟨t, ht'⟩ : UnitInterval) :=
    SmoothManifolds.HomotopyResults.intervalTime_coe ⟨t,ht'⟩
  change G (ι x,t) = f x (intervalTime t)
  rw [heq]
  exact hagree x hxU ⟨t,ht'⟩
end UniformExtension

namespace SmoothManifolds.HomotopyIntegration
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  FrameData ExteriorData DeRhamData HomotopyData Set MeasureTheory
open scoped Topology
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

/-- Simultaneous local ambient smoothness of every source-chart coefficient on
its actual cylinder, with the time coordinate appended last. -/
def JointSmoothCoefficients (C : CotangentBundle S) (k : ℕ)
    (f : UnitInterval → Field S k) : Prop :=
  ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
    LocallyContDiffAlong (⊤ : ℕ∞)
      (fun z : c.source × UnitInterval => Fin.snoc (c z.1.val).val z.2.val)
      (fun z => coefficients C k c hc (f z.2) z.1 I)

theorem jointSmooth_coefficientsIntervalIntegrable (C : CotangentBundle S) (k : ℕ)
    (f : UnitInterval → Field S k) (hf : JointSmoothCoefficients C k f) :
    CoefficientsIntervalIntegrable C k (fun t => f (intervalTime t)) := by
  intro c hc p I
  exact UniformExtension.intervalIntegrable_of_local
    (fun q : c.source => (c q.val).val)
    (fun q t => coefficients C k c hc (f t) q I) p
    (fun t => hf c hc I (p,t))

theorem jointSmooth_integral_coefficients (C : CotangentBundle S) (k : ℕ)
    (f : UnitInterval → Field S k) (hf : JointSmoothCoefficients C k f)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p => ∫ t in (0 : ℝ)..1, coefficients C k c hc (f (intervalTime t)) p I) := by
  apply (ExteriorDerivativeResults.locallySmoothAlong_chart_iff c hc _).mp
  intro p
  exact UniformExtension.integral_hasLocalExtensionAt_of_local
    (fun q : c.source => (c q.val).val)
    (fun q t => coefficients C k c hc (f t) q I) p
    (fun t => hf c hc I (p,t))

theorem isForm_integralField_of_jointSmooth (C : CotangentBundle S) (k : ℕ)
    (B : FormBundle C k) (f : UnitInterval → Field S k)
    (hf : JointSmoothCoefficients C k f) :
    IsForm B (integralField C k (fun t => f (intervalTime t))) :=
  isForm_integralField C k B _
    (jointSmooth_coefficientsIntervalIntegrable C k f hf)
    (jointSmooth_integral_coefficients C k f hf)

/-- The beta coefficients depend linearly on the original smooth input form. -/
def betaFamilyLinearMap {C : CotangentBundle S}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (D : HomotopyDifferentials S T F) (k : ℕ) :
    J.forms (k+1) →ₗ[ℝ] (ℝ → Field S k) where
  toFun eta t := beta C D eta.val (intervalTime t)
  map_add' eta η := by
    funext t
    exact HomotopyResults.beta_add C D eta.val η.val (intervalTime t)
  map_smul' r eta := by
    funext t
    exact HomotopyResults.beta_smul C D r eta.val (intervalTime t)

/-- Integrating the genuine beta family lands in the original smooth-form
submodule once its actual chart coefficients are jointly smooth. -/
def betaIntegralOperator {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (D : HomotopyDifferentials S T F)
    (hbeta : ∀ k (eta : J.forms (k+1)),
      JointSmoothCoefficients C k (fun t => beta C D eta.val t)) :
    ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k :=
  fun k => by
    let bm : J.forms (k+1) →ₗ[ℝ] (ℝ → Field S k) := betaFamilyLinearMap (C := C) J D k
    have hbint (eta : J.forms (k+1)) : CoefficientsIntervalIntegrable C k (bm eta) := by
      change CoefficientsIntervalIntegrable C k (fun t => beta C D eta.val (intervalTime t))
      exact jointSmooth_coefficientsIntervalIntegrable C k _ (hbeta k eta)
    have hbs (eta : J.forms (k+1)) :
        ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
          VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
            (fun p => ∫ t in (0 : ℝ)..1, coefficients C k c hc (bm eta t) p I) := by
      intro c hc I
      change VectorSmooth _ (fun p => ∫ t in (0 : ℝ)..1,
        coefficients C k c hc (beta C D eta.val (intervalTime t)) p I)
      exact jointSmooth_integral_coefficients C k _ (hbeta k eta) c hc I
    exact integralFormsLinearMap (V := J.forms (k+1)) K k bm hbint hbs

theorem betaIntegralOperator_isCoefficientIntegral
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (D : HomotopyDifferentials S T F)
    (hbeta : ∀ k (eta : J.forms (k+1)),
      JointSmoothCoefficients C k (fun t => beta C D eta.val t)) :
    IsCoefficientIntegral K J D (betaIntegralOperator K J D hbeta) := by
  intro k eta c hc p I
  refine ⟨jointSmooth_coefficientsIntervalIntegrable C k _ (hbeta k eta) c hc p I, ?_⟩
  change coefficients C k c hc
    (integralField C k (fun t => beta C D eta.val (intervalTime t))) p I = _
  exact coefficients_integralField C k _
    (jointSmooth_coefficientsIntervalIntegrable C k _ (hbeta k eta)) c hc p I

end SmoothManifolds.HomotopyIntegration

namespace SmoothManifolds.AmbientHomotopy
set_option backward.isDefEq.respectTransparency false
open ContinuousAlternatingMap MeasureTheory Set Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sliceL (k : ℕ) : ((E × ℝ) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) :=
  compContinuousLinearMapCLM (ContinuousLinearMap.inl ℝ E ℝ)

def contractL (k : ℕ) : ((E × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ) →L[ℝ]
    ((E × ℝ) [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousLinearMap.apply ℝ _ ((0,1) : E × ℝ)).comp
    (curryLeftLI (𝕜 := ℝ) (E := E × ℝ) (F := ℝ) (n := k)).toContinuousLinearMap

def alpha {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (t : ℝ) (x : E) : E [⋀^Fin k]→L[ℝ] ℝ := sliceL k (Ω (x,t))

def beta {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (z : E × ℝ) : E [⋀^Fin k]→L[ℝ] ℝ := sliceL k (contractL k (Ω z))

theorem beta_smooth {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω) : ContDiff ℝ (⊤ : ℕ∞) (beta Ω) := by
  exact (sliceL k).contDiff.comp ((contractL k).contDiff.comp hΩ)

theorem extDeriv_smooth {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω) : ContDiff ℝ (⊤ : ℕ∞) (extDeriv Ω) := by
  exact (alternatizeUncurryFinCLM ℝ (E × ℝ) ℝ).contDiff.comp
    (hΩ.fderiv_right (m := (⊤ : ℕ∞)) (by simp))

theorem extDeriv_alpha {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (hΩ : Differentiable ℝ Ω) (t : ℝ) (x : E) :
    extDeriv (alpha Ω t) x = alpha (extDeriv Ω) t x := by
  let f : E → E × ℝ := fun y => (y,t)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_id.prodMk contDiff_const
  have hdf (y : E) : fderiv ℝ f y = ContinuousLinearMap.inl ℝ E ℝ := by
    simpa only [f, id_eq, ContinuousLinearMap.inl] using
      ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y)).fderiv
  have h := extDeriv_pullback (hΩ (f x)) hf.contDiffAt (by simp)
  change extDeriv (fun y => (Ω (y,t)).compContinuousLinearMap
    (ContinuousLinearMap.inl ℝ E ℝ)) x = _
  simpa only [hdf, alpha, sliceL, compContinuousLinearMapCLM_apply, f] using h

theorem alpha_hasDerivAt {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (hΩ : Differentiable ℝ Ω) (x : E) (t : ℝ) :
    HasDerivAt (fun s => alpha Ω s x)
      (sliceL k (fderiv ℝ Ω (x,t) (0,1))) t := by
  exact (sliceL k).hasFDerivAt.comp_hasDerivAt t
    ((hΩ (x,t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t)))

theorem local_chain_identity {k : ℕ}
    (Ω : E × ℝ → (E × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω) (x : E) (t : ℝ) :
    extDeriv (fun y => beta Ω (y,t)) x + beta (extDeriv Ω) (x,t) =
      sliceL (k+1) (fderiv ℝ Ω (x,t) (0,1)) := by
  let κ : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ := fun z => contractL k (Ω z)
  have hκ : ContDiff ℝ (⊤ : ℕ∞) κ := by
    exact ((contractL (E := E) k).contDiff.comp hΩ :
      ContDiff ℝ (⊤ : ℕ∞) ((contractL (E := E) k) ∘ Ω))
  have hslice := extDeriv_alpha κ (hκ.differentiable (by simp)) t x
  change extDeriv (fun y => beta Ω (y,t)) x =
    sliceL (k+1) (extDeriv κ (x,t)) at hslice
  rw [hslice]
  apply ContinuousAlternatingMap.ext
  intro v
  have h := CartanResults.model_cartan_evaluation
    ((hΩ.differentiable (by simp)) (x,t))
    (differentiableAt_const ((0,1) : E × ℝ))
    ((hκ.differentiable (by simp)) (x,t))
    (fun i => (v i,0))
  have hsum : (∑ i : Fin (k+1), Ω (x,t)
      (Function.update (fun i => (v i,0)) i
        (fderiv ℝ (fun _ : E × ℝ => ((0,1) : E × ℝ)) (x,t) (v i,0)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply (Ω (x,t)).map_coord_zero i
    simp
  rw [hsum, add_zero] at h
  simpa only [Function.comp_def, Matrix.vecCons, ContinuousAlternatingMap.add_apply, sliceL,
    compContinuousLinearMapCLM_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.inl_apply, beta, contractL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, LinearIsometry.coe_toContinuousLinearMap,
    curryLeftLI_apply, curryLeft_apply_apply, κ] using h

section Integration
variable [FiniteDimensional ℝ E]

def operator {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (x : E) : E [⋀^Fin k]→L[ℝ] ℝ := ∫ t in (0 : ℝ)..1, beta Ω (x,t)

theorem chain_identity {k : ℕ}
    (Ω : E × ℝ → (E × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω) (x : E) :
    extDeriv (operator Ω) x + operator (extDeriv Ω) x = alpha Ω 1 x - alpha Ω 0 x := by
  have hβ := beta_smooth Ω hΩ
  have hδβ := beta_smooth (extDeriv Ω) (extDeriv_smooth Ω hΩ)
  have hInt₂ : IntervalIntegrable (fun t => beta (extDeriv Ω) (x,t)) volume 0 1 :=
    (hδβ.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  let κ : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ := fun z => contractL k (Ω z)
  have hκ : ContDiff ℝ (⊤ : ℕ∞) κ := by
    exact ((contractL (E := E) k).contDiff.comp hΩ :
      ContDiff ℝ (⊤ : ℕ∞) ((contractL (E := E) k) ∘ Ω))
  have hEq : (fun t => extDeriv (fun y => beta Ω (y,t)) x) =
      (fun t => sliceL (k+1) (extDeriv κ (x,t))) := by
    funext t
    exact extDeriv_alpha κ (hκ.differentiable (by simp)) t x
  have hInt₁ : IntervalIntegrable
      (fun t => extDeriv (fun y => beta Ω (y,t)) x) volume 0 1 := by
    rw [hEq]
    exact ((sliceL (E := E) (k+1)).continuous.comp
      ((extDeriv_smooth κ hκ).continuous.comp
        (continuous_const.prodMk continuous_id))).intervalIntegrable 0 1
  have hTime : Continuous
      (fun t => sliceL (k+1) (fderiv ℝ Ω (x,t) (0,1))) := by
    exact (sliceL (E := E) (k+1)).continuous.comp
      (((hΩ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp
        (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
  change extDeriv (fun y => ∫ t in (0 : ℝ)..1, beta Ω (y,t)) x +
      (∫ t in (0 : ℝ)..1, beta (extDeriv Ω) (x,t)) = _
  rw [HomotopyResults.extDeriv_integral (beta Ω) hβ x]
  rw [← intervalIntegral.integral_add hInt₁ hInt₂]
  have hIntEq : (∫ t in (0 : ℝ)..1,
      extDeriv (fun y => beta Ω (y,t)) x + beta (extDeriv Ω) (x,t)) =
      ∫ t in (0 : ℝ)..1, sliceL (k+1) (fderiv ℝ Ω (x,t) (0,1)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact local_chain_identity Ω hΩ x t
  rw [hIntEq]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => alpha_hasDerivAt Ω (hΩ.differentiable (by simp)) x t)
    (hTime.intervalIntegrable 0 1)

end Integration
end SmoothManifolds.AmbientHomotopy

namespace SmoothManifolds.HomotopyResults
set_option backward.isDefEq.respectTransparency false
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData HomotopyData Set
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

theorem field_eq_of_coefficients (C : CotangentBundle S) {k : ℕ}
    (ω η : Field S k)
    (h : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source) (I : Index n k),
      coefficients C k c hc ω p I = coefficients C k c hc η p I) : ω = η := by
  funext p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  exact ExteriorAlgebraResults.coefficients_unique C k c hc ω η
    (h c hc) ⟨p,hp⟩

theorem isChainHomotopy_of_coefficients
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (D : HomotopyDifferentials S T F)
    (op : ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k)
    (hint : IsCoefficientIntegral K J D op)
    (hpos : ∀ k (ω : J.forms (k+1))
      (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source) (I : Index n (k+1)),
      ContinuousOn
        (fun t => coefficients C (k+1) c hc (alpha D ω.val (intervalTime t)) p I)
        (Icc 0 1) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun t => coefficients C (k+1) c hc (alpha D ω.val (intervalTime t)) p I)
          (coefficients C (k+1) c hc (K.D k (beta C D ω.val (intervalTime t))) p I +
            coefficients C (k+1) c hc
              (beta C D (J.d (k+1) ω).val (intervalTime t)) p I) t)
    (hcommute : ∀ k (ω : J.forms (k+1))
      (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source) (I : Index n (k+1)),
      IntervalIntegrable
        (fun t => coefficients C (k+1) c hc
          (K.D k (beta C D ω.val (intervalTime t))) p I) MeasureTheory.volume 0 1 ∧
      coefficients C (k+1) c hc (K.d k (op k ω)).val p I =
        ∫ t in (0 : ℝ)..1, coefficients C (k+1) c hc
          (K.D k (beta C D ω.val (intervalTime t))) p I)
    (hzero : ∀ (ω : J.forms 0)
      (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source) (I : Index n 0),
      ContinuousOn
        (fun t => coefficients C 0 c hc (alpha D ω.val (intervalTime t)) p I)
        (Icc 0 1) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun t => coefficients C 0 c hc (alpha D ω.val (intervalTime t)) p I)
          (coefficients C 0 c hc (beta C D (J.d 0 ω).val (intervalTime t)) p I) t) :
    IsChainHomotopy K J D op := by
  constructor
  · intro k ω
    apply field_eq_of_coefficients C
    intro c hc p I
    have hδ := hcommute k ω c hc p I
    have hγ := hint (k+1) (J.d (k+1) ω) c hc p I
    have ha := hpos k ω c hc p I
    have hftc := coefficient_endpoint_identity _ _ _ ha.1 ha.2 hδ.1 hγ.1
    change coefficients C (k+1) c hc
      ((K.d k (op k ω)).val + (op (k+1) (J.d (k+1) ω)).val) p I = _
    have hadd (ξ ζ : Field S (k+1)) :
        coefficients C (k+1) c hc (ξ+ζ) p I =
          coefficients C (k+1) c hc ξ p I + coefficients C (k+1) c hc ζ p I := by
      simp only [coefficients, Pi.add_apply, Pi.sub_apply, map_add, map_sub,
        Finsupp.add_apply, Finsupp.sub_apply]
    have hsub (ξ ζ : Field S (k+1)) :
        coefficients C (k+1) c hc (ξ-ζ) p I =
          coefficients C (k+1) c hc ξ p I - coefficients C (k+1) c hc ζ p I := by
      simp only [coefficients, Pi.add_apply, Pi.sub_apply, map_add, map_sub,
        Finsupp.add_apply, Finsupp.sub_apply]
    rw [hadd, hsub, hδ.2, hγ.2]
    have hi : intervalTime (0 : ℝ) = initialTime := by
      apply Subtype.ext
      norm_num [intervalTime, initialTime]
    have hf : intervalTime (1 : ℝ) = finalTime := by
      apply Subtype.ext
      norm_num [intervalTime, finalTime]
    simpa only [hi,hf] using hftc
  · intro ω
    apply field_eq_of_coefficients C
    intro c hc p I
    have hγ := hint 0 (J.d 0 ω) c hc p I
    have ha := hzero ω c hc p I
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show (0 : ℝ) ≤ 1 by norm_num) ha.1 ha.2 hγ.1
    have hsub (ξ ζ : Field S 0) :
        coefficients C 0 c hc (ξ-ζ) p I =
          coefficients C 0 c hc ξ p I - coefficients C 0 c hc ζ p I := by
      simp only [coefficients, Pi.add_apply, Pi.sub_apply, map_add, map_sub,
        Finsupp.add_apply, Finsupp.sub_apply]
    rw [hsub, hγ.2]
    have hi : intervalTime (0 : ℝ) = initialTime := by
      apply Subtype.ext
      norm_num [intervalTime, initialTime]
    have hf : intervalTime (1 : ℝ) = finalTime := by
      apply Subtype.ext
      norm_num [intervalTime, finalTime]
    simpa only [hi,hf] using hftc
end SmoothManifolds.HomotopyResults

namespace SmoothManifolds.HomotopyData
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData Set Filter
open scoped Topology
universe u

/-- The time derivative in any intrinsic target chart is determined by the
scalar derivative condition in `HomotopyDifferentials`. -/
theorem HomotopyDifferentials.velocity_coordinates {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (D : HomotopyDifferentials S T F)
    (p : M) (t : UnitInterval) (d : ModelChart m b N)
    (hd : d ∈ T.smoothStructure.val) (hpt : F (p,t) ∈ d.source)
    (Q : FiberCoordinates T) (v : Euclidean m)
    (hv : HasDerivWithinAt (fun s => (d (F (p,intervalTime s))).val) v (Icc 0 1) t.val) :
    Q.equiv d hd (F (p,t)) hpt (D.velocity p t) = v := by
  obtain ⟨g,hg,hQ⟩ := Q.isCoordinates d hd (F (p,t)) hpt
  ext j
  rw [hQ]
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc_zero_one t.val t.property)
    (D.velocity_correct p t (g j) (fun y => (d y).val j) (hg j).symm)
    (hasDerivWithinAt_pi.mp hv j)

private theorem hasDerivAt_snoc_time {n : ℕ} (x : Euclidean n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (Fin.snoc x s : Euclidean (n+1)))
      (Pi.single (Fin.last n) 1) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, Pi.single_eq_same]
    exact hasDerivAt_id t
  · simpa only [Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)] using
      (hasDerivAt_const t (x j))

/-- A joint ambient representative computes the time column of the genuine
homotopy differential, at endpoints as well as interior times. -/
theorem HomotopyDifferentials.velocity_jacobian {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (D : HomotopyDifferentials S T F)
    (c : ModelChart n a M) (d : ModelChart m b N)
    (hd : d ∈ T.smoothStructure.val) (Q : FiberCoordinates T)
    (U : Set (Euclidean (n+1))) (hU : IsOpen U)
    (G : Euclidean (n+1) → Euclidean m) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hagree : ∀ q : {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source},
      Fin.snoc (c q.val.1).val q.val.2.val ∈ U →
        G (Fin.snoc (c q.val.1).val q.val.2.val) = (d (F q.val)).val)
    (p : M) (hp : p ∈ c.source) (t : UnitInterval)
    (hpt : F (p,t) ∈ d.source) (hpU : Fin.snoc (c p).val t.val ∈ U) :
    Q.equiv d hd (F (p,t)) hpt (D.velocity p t) =
      fderiv ℝ G (Fin.snoc (c p).val t.val) (Pi.single (Fin.last n) 1) := by
  apply D.velocity_coordinates p t d hd hpt Q
  let e : ℝ → Euclidean (n+1) := fun s => Fin.snoc (c p).val s
  have he := hasDerivAt_snoc_time (c p).val t.val
  have hdG := (hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hder := hdG.hasFDerivAt.comp_hasDerivAt t.val he
  apply hder.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ t.property
  have hf : Continuous (fun s => F (p,intervalTime s)) :=
    hF.1.comp (continuous_const.prodMk (by
      apply Continuous.subtype_mk
      exact continuous_const.max (continuous_const.min continuous_id)))
  have hpt' : F (p,intervalTime t.val) ∈ d.source := by simpa using hpt
  have h1 : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t.val, F (p,intervalTime s) ∈ d.source :=
    nhdsWithin_le_nhds (hf.continuousAt (d.open_source.mem_nhds hpt'))
  have h2 : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t.val, e s ∈ U :=
    nhdsWithin_le_nhds (he.continuousAt (hU.mem_nhds hpU))
  filter_upwards [h1,h2,self_mem_nhdsWithin] with s hs hsU hsI
  symm
  simpa only [Function.comp_apply, e, intervalTime_val_of_mem s hsI] using
    hagree ⟨(p,intervalTime s),hp,hs⟩ (by
      simpa only [intervalTime_val_of_mem s hsI] using hsU)


private def snocSpatialLinear (n : ℕ) : Euclidean n →L[ℝ] Euclidean (n+1) :=
  ContinuousLinearMap.pi (fun i => Fin.lastCases 0 (fun j => ContinuousLinearMap.proj j) i)

private theorem snocSpatialLinear_apply {n : ℕ} (x : Euclidean n) :
    snocSpatialLinear n x = Fin.snoc x 0 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [snocSpatialLinear]

private theorem hasFDerivAt_snoc_space {n : ℕ} (t : ℝ) (x : Euclidean n) :
    HasFDerivAt (fun y : Euclidean n => (Fin.snoc y t : Euclidean (n+1)))
      (snocSpatialLinear n) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, snocSpatialLinear, ContinuousLinearMap.proj_pi,
      Fin.lastCases_last]
    exact hasFDerivAt_const t x
  · simp only [Fin.snoc_castSucc, snocSpatialLinear, ContinuousLinearMap.proj_pi,
      Fin.lastCases_castSucc]
    exact (ContinuousLinearMap.proj j : Euclidean n →L[ℝ] ℝ).hasFDerivAt

/-- A joint ambient representative computes every spatial column. -/
theorem HomotopyDifferentials.spatial_jacobian {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (D : HomotopyDifferentials S T F)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (P : FiberCoordinates S) (Q : FiberCoordinates T)
    (U : Set (Euclidean (n+1))) (hU : IsOpen U)
    (G : Euclidean (n+1) → Euclidean m) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hagree : ∀ q : {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source},
      Fin.snoc (c q.val.1).val q.val.2.val ∈ U →
        G (Fin.snoc (c q.val.1).val q.val.2.val) = (d (F q.val)).val)
    (p : M) (hp : p ∈ c.source) (t : UnitInterval)
    (hpt : F (p,t) ∈ d.source) (hpU : Fin.snoc (c p).val t.val ∈ U)
    (v : TangentSpace S p) :
    Q.equiv d hd (F (p,t)) hpt (D.spatial t p v) =
      fderiv ℝ G (Fin.snoc (c p).val t.val)
        (Fin.snoc (P.equiv c hc p hp v) 0) := by
  let e : Euclidean n → Euclidean (n+1) := fun x => Fin.snoc x t.val
  have he : ContDiff ℝ (⊤ : ℕ∞) e := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [e, Fin.snoc_last] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Euclidean n => t.val))
    · simpa only [e, Fin.snoc_castSucc] using (contDiff_apply ℝ (fun _ : Fin n => ℝ) j :
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclidean n => x j))
  have hf : Continuous (fun p => F (p,t)) := hF.1.comp (continuous_id.prodMk continuous_const)
  have hccont : ContinuousAt (fun x => (c x).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  have hagree' : (fun y => (G ∘ e) (c y).val) =ᶠ[𝓝 p] (fun y => (d (F (y,t))).val) := by
    filter_upwards [c.open_source.mem_nhds hp,
      hf.continuousAt (d.open_source.mem_nhds hpt),
      hccont (hU.preimage he.continuous |>.mem_nhds hpU)] with y hy hyq hyU
    exact hagree ⟨(y,t),hy,hyq⟩ hyU
  rw [differential_jacobian S T (fun y => F (y,t)) (hF.slice_smooth t) p
    (D.spatial t p) (D.spatial_correct t p) c d hc hd hp hpt
    (P.equiv c hc p hp) (Q.equiv d hd (F (p,t)) hpt)
    (P.isCoordinates c hc p hp) (Q.isCoordinates d hd (F (p,t)) hpt)
    (e ⁻¹' U) (G ∘ e) (hU.preimage he.continuous) hpU
    (hG.comp he.contDiffOn (fun _ h => h)) hagree']
  have hdG := (hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  rw [(hdG.hasFDerivAt.comp (c p).val (hasFDerivAt_snoc_space t.val (c p).val)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, snocSpatialLinear_apply]


/-- The coefficient formula in one cylinder chart: time column first. -/
def ambientBetaCoefficients (n m k : ℕ)
    (G : Euclidean (n+1) → Euclidean m)
    (W : Euclidean m → Index m (k+1) → ℝ) :
    Euclidean (n+1) → Index n k → ℝ :=
  fun z I => ∑ J : Index m (k+1), W (G z) J *
    (Matrix.of (fun i j : Fin (k+1) =>
      fderiv ℝ G z
        (Fin.cases (Pi.single (Fin.last n) 1)
          (fun l => Pi.single (Set.powersetCard.ofFinEmbEquiv.symm I l).castSucc 1) j)
        (Set.powersetCard.ofFinEmbEquiv.symm J i))).det

/-- This finite determinant expression is jointly smooth on an ambient open set. -/
theorem ambientBetaCoefficients_contDiffOn {n m k : ℕ}
    (G : Euclidean (n+1) → Euclidean m)
    (W : Euclidean m → Index m (k+1) → ℝ)
    (U : Set (Euclidean (n+1))) (hU : IsOpen U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => W (G z)) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ambientBetaCoefficients n m k G W) U := by
  classical
  apply contDiffOn_pi.mpr
  intro I
  apply ContDiffOn.sum
  intro J hJ
  apply (contDiffOn_pi.mp hW J).mul
  simp only [Matrix.det_apply]
  apply ContDiffOn.sum
  intro σ hσ
  apply ContDiffOn.const_smul
  apply contDiffOn_prod
  intro i hi
  apply contDiffOn_pi.mp
    ((hG.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const)


private theorem snoc_single {n : ℕ} (i : Fin n) :
    Fin.snoc (Pi.single i (1 : ℝ)) 0 = (Pi.single i.castSucc 1 : Euclidean (n+1)) := by
  ext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simp
  · simp [Pi.single_apply, Fin.castSucc_inj]

/-- Actual beta coefficients agree with the jointly smooth determinant expression. -/
theorem beta_coefficients_eq_ambient {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T (k+1))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (U : Set (Euclidean (n+1))) (hU : IsOpen U)
    (G : Euclidean (n+1) → Euclidean m) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hagree : ∀ q : {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source},
      Fin.snoc (c q.val.1).val q.val.2.val ∈ U →
        G (Fin.snoc (c q.val.1).val q.val.2.val) = (d (F q.val)).val)
    (W : Euclidean m → Index m (k+1) → ℝ)
    (p : M) (hp : p ∈ c.source) (t : UnitInterval)
    (hpt : F (p,t) ∈ d.source) (hpU : Fin.snoc (c p).val t.val ∈ U)
    (hW : W (G (Fin.snoc (c p).val t.val)) =
      fun J => coefficients A (k+1) d hd ω ⟨F (p,t),hpt⟩ J) :
    (fun I => coefficients C k c hc (beta C D ω t) ⟨p,hp⟩ I) =
      ambientBetaCoefficients n m k G W (Fin.snoc (c p).val t.val) := by
  classical
  ext I
  rw [CartanResults.coefficients_eq_evaluate]
  change (CartanData.evaluationEquiv C.tangent.fiberCoordinates p k
    (beta C D ω t p)) _ = _
  rw [beta, LinearEquiv.apply_symm_apply]
  change evaluate (TangentSpace T (F (p,t))) (k+1) (ω (F (p,t)))
    (Fin.cons (D.velocity p t) (fun j => D.spatial t p
      (coordinateVector C.tangent.fiberCoordinates c hc p hp
        (Set.powersetCard.ofFinEmbEquiv.symm I j)))) = _
  rw [ExteriorAlgebraResults.coefficient_expansion A (k+1) d hd ω ⟨F (p,t),hpt⟩]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  unfold ambientBetaCoefficients
  rw [hW]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  rw [ExteriorAlgebraResults.determinant_normalization]
  congr 1
  ext i j
  change coordinateCovector A.tangent.fiberCoordinates d hd (F (p,t)) hpt
    (Set.powersetCard.ofFinEmbEquiv.symm J i)
      ((Fin.cons (D.velocity p t) (fun l => D.spatial t p
        (coordinateVector C.tangent.fiberCoordinates c hc p hp
          (Set.powersetCard.ofFinEmbEquiv.symm I l))) : Fin (k+1) →
          TangentSpace T (F (p,t))) j) = _
  refine Fin.cases ?_ (fun l => ?_) j
  · simp only [Fin.cons_zero, Fin.cases_zero, coordinateCovector, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearEquiv.coe_coe]
    rw [D.velocity_jacobian hF c d hd A.tangent.fiberCoordinates U hU G hG hagree p hp t hpt hpU]
    rfl
  · simp only [Fin.cons_succ, Fin.cases_succ, coordinateCovector, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearEquiv.coe_coe]
    rw [D.spatial_jacobian hF c hc d hd C.tangent.fiberCoordinates A.tangent.fiberCoordinates
      U hU G hG hagree p hp t hpt hpU]
    simp only [coordinateVector, LinearEquiv.apply_symm_apply, snoc_single]
    rfl

/-- The actual coefficients of beta are jointly smooth in all spatial and time
variables with local ambient extensions, including every boundary face. -/
theorem beta_coefficients_locally_smooth {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T (k+1))
    (B : FormBundle A (k+1)) (hω : IsForm B ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    LocallyContDiffAlong (⊤ : ℕ∞)
      (fun q : c.source × UnitInterval => Fin.snoc (c q.1.val).val q.2.val)
      (fun q => fun I => coefficients C k c hc (beta C D ω q.2) q.1 I) := by
  intro q
  obtain ⟨d,hd,hqd⟩ := T.smoothStructure.property.1.1 (F (q.1.val,q.2))
  obtain ⟨U,hU,hqU,G,hG,heG⟩ := hF.2 c hc d hd ⟨(q.1.val,q.2),q.1.property,hqd⟩
  obtain ⟨V,hV,hqV,W,hW,heW⟩ :=
    ((ExteriorDerivativeResults.smooth_coefficients A (k+1) B ω).mp hω) d hd
      ⟨F (q.1.val,q.2),hqd⟩
  obtain ⟨O,hO,hqO,heO⟩ := HomotopyResults.cylinder_chart_neighborhood c F hF.1
    d.source d.open_source q.1 q.2 hqd
  have hGq : G (Fin.snoc (c q.1.val).val q.2.val) = (d (F (q.1.val,q.2))).val :=
    heG ⟨(q.1.val,q.2),q.1.property,hqd⟩ hqU
  have hGV : G (Fin.snoc (c q.1.val).val q.2.val) ∈ V := by
    rw [hGq]
    exact hqV
  obtain ⟨P,hPV,hP,hqP⟩ := mem_nhds_iff.mp
    ((hG.contDiffAt (hU.mem_nhds hqU)).continuousAt (hV.mem_nhds hGV))
  let Z := (U ∩ P) ∩ O
  have hZ : IsOpen Z := (hU.inter hP).inter hO
  have hqZ : Fin.snoc (c q.1.val).val q.2.val ∈ Z := ⟨⟨hqU,hqP⟩,hqO⟩
  have hGZ : ContDiffOn ℝ (⊤ : ℕ∞) G Z := hG.mono (fun z hz => hz.1.1)
  have hWZ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => W (G z)) Z :=
    hW.comp hGZ (fun z hz => hPV hz.1.2)
  refine ⟨Z,hZ,hqZ,ambientBetaCoefficients n m k G W,
    ambientBetaCoefficients_contDiffOn G W Z hZ hGZ hWZ, ?_⟩
  intro y hy
  have hyd : F (y.1.val,y.2) ∈ d.source := heO y.1 y.2 hy.2
  have hGy : G (Fin.snoc (c y.1.val).val y.2.val) = (d (F (y.1.val,y.2))).val :=
    heG ⟨(y.1.val,y.2),y.1.property,hyd⟩ hy.1.1
  have hWy : W (G (Fin.snoc (c y.1.val).val y.2.val)) =
      fun J => coefficients A (k+1) d hd ω ⟨F (y.1.val,y.2),hyd⟩ J := by
    rw [hGy]
    apply heW ⟨F (y.1.val,y.2),hyd⟩
    change (d (F (y.1.val,y.2))).val ∈ V
    rw [← hGy]
    exact hPV hy.1.2
  exact (beta_coefficients_eq_ambient hF C A D ω c hc d hd U hU G hG heG W
    y.1.val y.1.property y.2 hyd hy.1.1 hWy).symm



end SmoothManifolds.HomotopyData

namespace SmoothManifolds.AmbientHomotopy
set_option backward.isDefEq.respectTransparency false
open ContinuousAlternatingMap MeasureTheory Set Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem extDeriv_alpha_at {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (t : ℝ) (x : E) (hΩ : DifferentiableAt ℝ Ω (x,t)) :
    extDeriv (alpha Ω t) x = alpha (extDeriv Ω) t x := by
  let f : E → E × ℝ := fun y => (y,t)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_id.prodMk contDiff_const
  have hdf (y : E) : fderiv ℝ f y = ContinuousLinearMap.inl ℝ E ℝ := by
    simpa only [f, id_eq, ContinuousLinearMap.inl] using
      ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y)).fderiv
  have h := extDeriv_pullback (f := f) (x := x) hΩ hf.contDiffAt (by simp)
  change extDeriv (fun y => (Ω (y,t)).compContinuousLinearMap
    (ContinuousLinearMap.inl ℝ E ℝ)) x = _
  simpa only [hdf, alpha, sliceL, compContinuousLinearMapCLM_apply, f] using h


theorem alpha_hasDerivAt_at {k : ℕ} (Ω : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (x : E) (t : ℝ) (hΩ : DifferentiableAt ℝ Ω (x,t)) :
    HasDerivAt (fun s => alpha Ω s x)
      (sliceL k (fderiv ℝ Ω (x,t) (0,1))) t := by
  exact (sliceL k).hasFDerivAt.comp_hasDerivAt t
    (hΩ.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t)))


theorem local_chain_identity_at {k : ℕ}
    (Ω : E × ℝ → (E × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (x : E) (t : ℝ) (hΩ : DifferentiableAt ℝ Ω (x,t)) :
    extDeriv (fun y => beta Ω (y,t)) x + beta (extDeriv Ω) (x,t) =
      sliceL (k+1) (fderiv ℝ Ω (x,t) (0,1)) := by
  let κ : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ := fun z => contractL k (Ω z)
  have hκ : DifferentiableAt ℝ κ (x,t) := by
    exact ((contractL (E := E) k).differentiableAt.comp (x,t) hΩ :
      DifferentiableAt ℝ ((contractL (E := E) k) ∘ Ω) (x,t))
  have hslice := extDeriv_alpha_at κ t x hκ
  change extDeriv (fun y => beta Ω (y,t)) x =
    sliceL (k+1) (extDeriv κ (x,t)) at hslice
  rw [hslice]
  apply ContinuousAlternatingMap.ext
  intro v
  have h := CartanResults.model_cartan_evaluation
    hΩ
    (differentiableAt_const ((0,1) : E × ℝ))
    hκ
    (fun i => (v i,0))
  have hsum : (∑ i : Fin (k+1), Ω (x,t)
      (Function.update (fun i => (v i,0)) i
        (fderiv ℝ (fun _ : E × ℝ => ((0,1) : E × ℝ)) (x,t) (v i,0)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply (Ω (x,t)).map_coord_zero i
    simp
  rw [hsum, add_zero] at h
  simpa only [Function.comp_def, Matrix.vecCons, ContinuousAlternatingMap.add_apply, sliceL,
    compContinuousLinearMapCLM_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.inl_apply, beta, contractL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, LinearIsometry.coe_toContinuousLinearMap,
    curryLeftLI_apply, curryLeft_apply_apply, κ] using h


theorem local_zero_identity
    (Ω : E × ℝ → (E × ℝ) [⋀^Fin 0]→L[ℝ] ℝ) (z : E × ℝ) :
    beta (extDeriv Ω) z = sliceL 0 (fderiv ℝ Ω z (0,1)) := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [beta, sliceL, contractL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, LinearIsometry.coe_toContinuousLinearMap,
    curryLeftLI_apply, compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, curryLeft_apply_apply,
    extDeriv, alternatizeUncurryFin_apply, Fin.sum_univ_succ, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, Fin.val_zero, pow_zero, one_smul, Matrix.vecCons,
    Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons]



end SmoothManifolds.AmbientHomotopy

namespace SmoothManifolds.HomotopyResults
open ModelData AtlasData MapData TangentData TangentBundleData BundleOperationsData
  CovectorData ExteriorData ExteriorDerivativeData DeRhamData HomotopyData Set Filter
open scoped Topology
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

theorem degreeZero_coefficient_relation
    {C : CotangentBundle S} {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (hF : IsSmoothHomotopy S T F)
    (D : HomotopyDifferentials S T F) (ω : J.forms 0)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n 0) :
    ContinuousOn
      (fun t => coefficients C 0 c hc (alpha D ω.val (intervalTime t)) p I)
      (Icc 0 1) ∧
    ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt
        (fun t => coefficients C 0 c hc (alpha D ω.val (intervalTime t)) p I)
        (coefficients C 0 c hc (beta C D (J.d 0 ω).val (intervalTime t)) p I) t := by
  let f : N → ℝ := fun q => exteriorPower.zeroEquiv ℝ
    (Module.Dual ℝ (TangentSpace T q)) (ω.val q)
  have hf : PartitionData.ScalarSmooth T.smoothStructure.val f := by
    let Y : Fin 0 → VectorFieldData.SmoothField A.tangent := fun i => Fin.elim0 i
    have h := CartanResults.fieldEvaluation_smooth A E 0 ω.val Y
      ((J.mem_forms 0 ω.val).mp ω.property)
    have he : CartanData.fieldEvaluation 0 ω.val (fun i => (Y i).val) = f := by
      funext q
      change evaluate (TangentSpace T q) 0 (ω.val q) (fun i => (Y i).val q) = _
      exact CartanResults.evaluate_degree_zero (V := TangentSpace T q) (ω.val q) _
    rw [he] at h
    exact h
  have hscalar : FormPullbackData.scalarField T f = ω.val := by
    funext q
    exact (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm_apply_apply _
  have ha (s : UnitInterval) :
      coefficients C 0 c hc (alpha D ω.val s) p I = f (F (p.val,s)) := by
    rw [alpha, ← hscalar, FormPullbackResults.pullback_zero,
      ExteriorDerivativeResults.scalarField_coefficient]
    rfl
  have hb (s : UnitInterval) :
      coefficients C 0 c hc (beta C D (J.d 0 ω).val s) p I =
        (D.velocity p.val s).val (functionGerm T f hf (F (p.val,s))) := by
    rw [CartanResults.coefficients_eq_evaluate, evaluate_beta,
      CartanResults.evaluate_degree_one]
    change exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T (F (p.val,s))))
      (J.D 0 ω.val (F (p.val,s))) (D.velocity p.val s) = _
    rw [← hscalar, J.axioms.function_rule f hf]
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have htime (s : UnitInterval) : HasDerivWithinAt
      (fun t => f (F (p.val,intervalTime t)))
      ((D.velocity p.val s).val (functionGerm T f hf (F (p.val,s))))
      (Icc 0 1) s.val := D.velocity_correct p.val s _ f rfl
  have heq : (fun t => coefficients C 0 c hc (alpha D ω.val (intervalTime t)) p I) =
      (fun t => f (F (p.val,intervalTime t))) := funext fun t => ha (intervalTime t)
  rw [heq]
  constructor
  · intro t ht
    exact (htime ⟨t,ht⟩).continuousWithinAt
  · intro t ht
    rw [hb]
    simpa only [intervalTime_val_of_mem t ⟨ht.1.le,ht.2.le⟩] using
      (htime (intervalTime t)).hasDerivAt
        (by simpa only [intervalTime_val_of_mem t ⟨ht.1.le,ht.2.le⟩] using
          Icc_mem_nhds ht.1 ht.2)

end SmoothManifolds.HomotopyResults

namespace UniformExtension
open SmoothManifolds.ModelData Set
open scoped Topology
variable {D : Type*} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι]

theorem hasLocalContDiffExtensionAt_pi {n : ℕ} (emb : D → Euclidean n)
    (f : D → ι → F) (x : D)
    (H : ∀ i, HasLocalContDiffExtensionAt (⊤ : ℕ∞) emb (fun y => f y i) x) :
    HasLocalContDiffExtensionAt (⊤ : ℕ∞) emb f x := by
  classical
  choose U hU hx g hg he using H
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, mem_iInter.mpr hx,
    (fun z i => g i z), contDiffOn_pi.mpr (fun i => (hg i).mono (iInter_subset U i)), ?_⟩
  intro y hy
  funext i
  exact he i y (mem_iInter.mp hy i)
end UniformExtension

namespace SmoothManifolds.HomotopyIntegration
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  FrameData ExteriorData ExteriorDerivativeData DeRhamData HomotopyData Set MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem jointSmooth_exists_coefficient_tube (C : CotangentBundle S) (k : ℕ)
    (f : UnitInterval → Field S k) (hf : JointSmoothCoefficients C k f)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ (c p.val).val ∈ U ∧
      ∃ G : Euclidean n × ℝ → (Index n k → ℝ), ContDiff ℝ (⊤ : ℕ∞) G ∧
        ∀ q : c.source, (c q.val).val ∈ U → ∀ t : UnitInterval,
          G ((c q.val).val,t.val) = coefficients C k c hc (f t) q := by
  apply UniformExtension.exists_smooth_extension_on_tube_of_local
    (fun q : c.source => (c q.val).val) (fun q t => coefficients C k c hc (f t) q) p
  intro t
  exact UniformExtension.hasLocalContDiffExtensionAt_pi _ _ (p,t)
    (fun I => hf c hc I (p,t))

theorem jointSmooth_isForm (C : CotangentBundle S) (k : ℕ)
    (B : FormBundle C k) (f : UnitInterval → Field S k)
    (hf : JointSmoothCoefficients C k f) (t : UnitInterval) : IsForm B (f t) := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C k B (f t)).mpr
  intro c hc I
  apply (ExteriorDerivativeResults.locallySmoothAlong_chart_iff c hc _).mp
  intro p
  obtain ⟨U,hU,hpU,G,hG,he⟩ := jointSmooth_exists_coefficient_tube C k f hf c hc p
  refine ⟨U,hU,hpU,(fun z => G (z,t.val) I), ?_, ?_⟩
  · exact ((contDiff_apply ℝ (fun _ : Index n k => ℝ) I).comp
      (hG.comp (contDiff_id.prodMk contDiff_const))).contDiffOn
  · intro q hq
    exact congrFun (he q hq t) I

/-- In any chart, the coefficients of the actual derivative are obtained by the
fixed coefficient derivative map from any local ambient coefficient extension. -/
theorem coefficients_derivative_of_extension {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (f : Field S k) (hf : IsForm (B k) f)
    (U : Set (Euclidean n)) (hU : IsOpen U)
    (G : Euclidean n → (Index n k → ℝ)) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (he : ∀ q : c.source, (c q.val).val ∈ U → G (c q.val).val = coefficients C k c hc f q)
    (p : c.source) (hpU : (c p.val).val ∈ U) :
    coefficients C (k+1) c hc (K.D k f) p =
      ExteriorDerivativeResults.coefficientDerivativeMap n k
        (fun I => fderiv ℝ (fun z => G z I) (c p.val).val) := by
  have hd := K.coordinates k f hf c hc p.val p.property
  have hform := ExteriorDerivativeResults.coordinate_formula_extension C k c hc f p.val
    p.property U (fun I z => G z I) hU hpU
    (fun I => (contDiffOn_pi.mp hG I).of_le (by simp))
    (by
      intro z hz hzU I
      have hh := congrFun (he ⟨c.symm z,c.map_target hz⟩
        (by simpa only [c.right_inv hz] using hzU)) I
      simpa only [c.right_inv hz] using hh)
  rw [hform] at hd
  change ((((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm).dualBasis.exteriorPower
        (k+1)).equivFun (K.D k f p.val)) = _
  rw [hd]
  exact ExteriorDerivativeResults.coordinateExpression_coefficients C k c hc p.val p.property _

/-- Spatial derivatives of a jointly smooth coefficient vector, retaining time
as a parameter. -/
def spatialCoefficientDerivative (k : ℕ)
    (G : Euclidean n × ℝ → (Index n k → ℝ)) (z : Euclidean n × ℝ) :
    Index n k → Euclidean n →L[ℝ] ℝ :=
  fun I => (fderiv ℝ (fun w => G w I) z).comp (ContinuousLinearMap.inl ℝ (Euclidean n) ℝ)

theorem spatialCoefficientDerivative_smooth (k : ℕ)
    (G : Euclidean n × ℝ → (Index n k → ℝ)) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialCoefficientDerivative k G) := by
  apply contDiff_pi.mpr
  intro I
  exact ((contDiff_pi.mp hG I).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_comp contDiff_const

theorem spatialCoefficientDerivative_correct (k : ℕ)
    (G : Euclidean n × ℝ → (Index n k → ℝ)) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (x : Euclidean n) (t : ℝ) (I : Index n k) :
    HasFDerivAt (fun y => G (y,t) I) (spatialCoefficientDerivative k G (x,t) I) x := by
  simpa only [spatialCoefficientDerivative, Function.comp_def, ContinuousLinearMap.inl_apply,
      Prod.mk_add_mk, add_zero, zero_add] using
    ((contDiff_pi.mp hG I).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
      ((ContinuousLinearMap.inl ℝ (Euclidean n) ℝ).hasFDerivAt.add_const (0,t))

theorem coefficients_derivative_on_tube {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B) (k : ℕ)
    (f : UnitInterval → Field S k) (hf : JointSmoothCoefficients C k f)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (U : Set (Euclidean n)) (hU : IsOpen U)
    (G : Euclidean n × ℝ → (Index n k → ℝ)) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (he : ∀ q : c.source, (c q.val).val ∈ U → ∀ t : UnitInterval,
      G ((c q.val).val,t.val) = coefficients C k c hc (f t) q)
    (p : c.source) (hpU : (c p.val).val ∈ U) (t : UnitInterval) :
    coefficients C (k+1) c hc (K.D k (f t)) p =
      ExteriorDerivativeResults.coefficientDerivativeMap n k
        (spatialCoefficientDerivative k G ((c p.val).val,t.val)) := by
  have hh := coefficients_derivative_of_extension K k c hc (f t)
    (jointSmooth_isForm C k (B k) f hf t) U hU (fun z => G (z,t.val))
    (hG.comp (contDiff_id.prodMk contDiff_const)).contDiffOn
    (fun q hq => he q hq t) p hpU
  simpa only [(spatialCoefficientDerivative_correct k G hG _ _ _).fderiv] using hh

theorem jointSmooth_derivative_coefficientsIntervalIntegrable {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B) (k : ℕ)
    (f : UnitInterval → Field S k) (hf : JointSmoothCoefficients C k f) :
    CoefficientsIntervalIntegrable C (k+1) (fun t => K.D k (f (intervalTime t))) := by
  intro c hc p I
  obtain ⟨U,hU,hpU,G,hG,he⟩ := jointSmooth_exists_coefficient_tube C k f hf c hc p
  let DG := spatialCoefficientDerivative k G
  have hDG : Continuous DG := (spatialCoefficientDerivative_smooth k G hG).continuous
  let L := ExteriorDerivativeResults.coefficientDerivativeMap n k
  have hLI : Continuous (fun t : ℝ => L (DG ((c p.val).val,t)) I) :=
    (continuous_apply I).comp (L.continuous.comp (hDG.comp
      (continuous_const.prodMk continuous_id)))
  apply (hLI.intervalIntegrable (a := (0 : ℝ)) (b := 1)).congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc ht
  have heq : intervalTime t = (⟨t,ht'⟩ : UnitInterval) :=
    HomotopyResults.intervalTime_coe ⟨t,ht'⟩
  change L (DG ((c p.val).val,t)) I = coefficients C (k+1) c hc (K.D k (f (intervalTime t))) p I
  rw [heq]
  exact congrFun (coefficients_derivative_on_tube K k f hf c hc U hU G hG he p hpU ⟨t,ht'⟩).symm I

/-- Chart coefficients of exterior differentiation commute with integrating a
jointly smooth family over the fixed compact time interval. -/
theorem derivative_integralField_coefficients {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B) (k : ℕ)
    (f : UnitInterval → Field S k) (hf : JointSmoothCoefficients C k f)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n (k+1)) :
    coefficients C (k+1) c hc
      (K.D k (integralField C k (fun t => f (intervalTime t)))) p I =
    coefficients C (k+1) c hc
      (integralField C (k+1) (fun t => K.D k (f (intervalTime t)))) p I := by
  obtain ⟨U,hU,hpU,G,hG,he⟩ := jointSmooth_exists_coefficient_tube C k f hf c hc p
  let H : Euclidean n → (Index n k → ℝ) := fun x J => ∫ t in (0 : ℝ)..1, G (x,t) J
  let DG := spatialCoefficientDerivative k G
  let L := ExteriorDerivativeResults.coefficientDerivativeMap n k
  have hDG : Continuous DG := (spatialCoefficientDerivative_smooth k G hG).continuous
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    contDiff_pi.mpr (fun J => HomotopyResults.smooth_integral _ (contDiff_pi.mp hG J))
  have hfint := jointSmooth_coefficientsIntervalIntegrable C k f hf
  have hfdint := jointSmooth_derivative_coefficientsIntervalIntegrable K k f hf
  have heH : ∀ q : c.source, (c q.val).val ∈ U →
      H (c q.val).val = coefficients C k c hc
        (integralField C k (fun t => f (intervalTime t))) q := by
    intro q hq
    funext J
    rw [coefficients_integralField C k _ hfint c hc q J]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have heq : intervalTime t = (⟨t,ht'⟩ : UnitInterval) := HomotopyResults.intervalTime_coe ⟨t,ht'⟩
    change G ((c q.val).val,t) J = coefficients C k c hc (f (intervalTime t)) q J
    rw [heq]
    exact congrFun (he q hq ⟨t,ht'⟩) J
  have hform := coefficients_derivative_of_extension K k c hc _
    (isForm_integralField_of_jointSmooth C k (B k) f hf) U hU H hH.contDiffOn heH p hpU
  have hHder (J : Index n k) :
      fderiv ℝ (fun z => H z J) (c p.val).val =
        ∫ t in (0 : ℝ)..1, DG ((c p.val).val,t) J := by
    exact (HomotopyResults.integral_hasFDerivAt (fun z => G z J) (fun z => DG z J)
      (contDiff_pi.mp hG J).continuous ((continuous_apply J).comp hDG)
      (fun x t => spatialCoefficientDerivative_correct k G hG x t J) (c p.val).val).fderiv
  have hDGint : IntervalIntegrable (fun t => DG ((c p.val).val,t)) volume 0 1 :=
    (hDG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have hpi : (fun J => ∫ t in (0 : ℝ)..1, DG ((c p.val).val,t) J) =
      ∫ t in (0 : ℝ)..1, DG ((c p.val).val,t) := by
    funext J
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index n k => Euclidean n →L[ℝ] ℝ) J).intervalIntegral_comp_comm hDGint
  let LI := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index n (k+1) => ℝ) I).comp L
  calc
    _ = L (fun J => fderiv ℝ (fun z => H z J) (c p.val).val) I := congrFun hform I
    _ = L (fun J => ∫ t in (0 : ℝ)..1, DG ((c p.val).val,t) J) I := by simp only [hHder]
    _ = ∫ t in (0 : ℝ)..1, L (DG ((c p.val).val,t)) I := by
      rw [hpi]
      exact (LI.intervalIntegral_comp_comm hDGint).symm
    _ = ∫ t in (0 : ℝ)..1, coefficients C (k+1) c hc (K.D k (f (intervalTime t))) p I := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
      have heq : intervalTime t = (⟨t,ht'⟩ : UnitInterval) := HomotopyResults.intervalTime_coe ⟨t,ht'⟩
      change L (DG ((c p.val).val,t)) I =
        coefficients C (k+1) c hc (K.D k (f (intervalTime t))) p I
      rw [heq]
      exact congrFun (coefficients_derivative_on_tube K k f hf c hc U hU G hG he p hpU ⟨t,ht'⟩).symm I
    _ = _ := (coefficients_integralField C (k+1) _ hfdint c hc p I).symm

/-- Exterior differentiation of the genuine intrinsic smooth-form field commutes
with coefficient integration, including at boundary and corner chart points. -/
theorem derivative_integralField {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B) (k : ℕ)
    (f : UnitInterval → Field S k) (hf : JointSmoothCoefficients C k f) :
    K.D k (integralField C k (fun t => f (intervalTime t))) =
      integralField C (k+1) (fun t => K.D k (f (intervalTime t))) := by
  funext p
  obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p
  exact ExteriorAlgebraResults.coefficients_unique C (k+1) c hc _ _
    (fun q I => derivative_integralField_coefficients K k f hf c hc q I) ⟨p,hp⟩

end SmoothManifolds.HomotopyIntegration

namespace SmoothManifolds.HomotopyIntegration
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  FrameData ExteriorData ExteriorDerivativeData DeRhamData HomotopyData Set MeasureTheory
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

@[simp] theorem betaIntegralOperator_val
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (D : HomotopyDifferentials S T F)
    (hbeta : ∀ k (eta : J.forms (k+1)),
      JointSmoothCoefficients C k (fun t => beta C D eta.val t))
    (k : ℕ) (eta : J.forms (k+1)) :
    (betaIntegralOperator K J D hbeta k eta).val =
      integralField C k (fun t => beta C D eta.val (intervalTime t)) := rfl

/-- The dK term is represented by the integral of the genuine spatial exterior
derivative of beta. -/
theorem derivative_betaIntegralOperator
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (D : HomotopyDifferentials S T F)
    (hbeta : ∀ k (eta : J.forms (k+1)),
      JointSmoothCoefficients C k (fun t => beta C D eta.val t))
    (k : ℕ) (eta : J.forms (k+1)) :
    (K.d k (betaIntegralOperator K J D hbeta k eta)).val =
      integralField C (k+1) (fun t => K.D k (beta C D eta.val (intervalTime t))) := by
  change K.D k (integralField C k (fun t => beta C D eta.val (intervalTime t))) = _
  exact derivative_integralField K k _ (hbeta k eta)

end SmoothManifolds.HomotopyIntegration

namespace SmoothManifolds.HomotopyIntegration
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData HomotopyData Set
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

theorem beta_jointSmooth (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) {k : ℕ} (ω : Field T (k+1))
    (B : FormBundle A (k+1)) (hω : IsForm B ω) :
    JointSmoothCoefficients C k (fun t => beta C D ω t) := by
  intro c hc I q
  obtain ⟨U,hU,hqU,G,hG,he⟩ := beta_coefficients_locally_smooth hF C A D ω B hω c hc q
  exact ⟨U,hU,hqU,(fun z => G z I),contDiffOn_pi.mp hG I,
    fun y hy => congrFun (he y hy) I⟩

end SmoothManifolds.HomotopyIntegration

namespace SmoothManifolds.HomotopyResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData HomotopyData HomotopyIntegration Set
universe u

theorem smooth_homotopy_integral_exists
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (A : CotangentBundle T) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (F : M × UnitInterval → N) (hF : IsSmoothHomotopy S T F) :
    ∃ (D : HomotopyDifferentials S T F)
      (op : ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k),
      IsCoefficientIntegral K J D op ∧
      ∀ k (ω : J.forms (k+1)) (t : UnitInterval) (p : M),
        HasDtFirstDecomposition C D ω.val t p (beta C D ω.val t p) ∧
        ∀ β : Fiber (TangentSpace S p) k,
          HasDtFirstDecomposition C D ω.val t p β → β = beta C D ω.val t p := by
  let D := hF.differentials
  have hbeta : ∀ k (ω : J.forms (k+1)),
      JointSmoothCoefficients C k (fun t => beta C D ω.val t) := by
    intro k ω
    exact beta_jointSmooth hF C A D ω.val (E (k+1)) ((J.mem_forms _ _).mp ω.property)
  refine ⟨D,betaIntegralOperator K J D hbeta,
    betaIntegralOperator_isCoefficientIntegral K J D hbeta,?_⟩
  intro k ω t p
  exact ⟨dtFirstDecomposition_exists C D ω.val t p,
    fun β hβ => dtFirstDecomposition_unique C D ω.val t p β hβ⟩
end SmoothManifolds.HomotopyResults

namespace SmoothManifolds.HomotopyData
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData Set Filter
open scoped Topology
universe u

def ambientAlphaCoefficients (n m k : ℕ)
    (G : Euclidean (n+1) → Euclidean m)
    (W : Euclidean m → Index m k → ℝ) :
    Euclidean (n+1) → Index n k → ℝ :=
  fun z I => ∑ J : Index m k, W (G z) J *
    (Matrix.of (fun i j : Fin k =>
      fderiv ℝ G z
        (Pi.single (Set.powersetCard.ofFinEmbEquiv.symm I j).castSucc 1)
        (Set.powersetCard.ofFinEmbEquiv.symm J i))).det

theorem ambientAlphaCoefficients_contDiffOn {n m k : ℕ}
    (G : Euclidean (n+1) → Euclidean m)
    (W : Euclidean m → Index m k → ℝ)
    (U : Set (Euclidean (n+1))) (hU : IsOpen U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => W (G z)) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ambientAlphaCoefficients n m k G W) U := by
  classical
  apply contDiffOn_pi.mpr
  intro I
  apply ContDiffOn.sum
  intro J hJ
  apply (contDiffOn_pi.mp hW J).mul
  simp only [Matrix.det_apply]
  apply ContDiffOn.sum
  intro σ hσ
  apply ContDiffOn.const_smul
  apply contDiffOn_prod
  intro i hi
  apply contDiffOn_pi.mp
    ((hG.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const)

private theorem snoc_standard_basis {n : ℕ} (i : Fin n) :
    Fin.snoc (Pi.single i (1 : ℝ)) 0 = (Pi.single i.castSucc 1 : Euclidean (n+1)) := by
  ext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simp
  · simp [Pi.single_apply, Fin.castSucc_inj]

theorem alpha_coefficients_eq_ambient {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T k)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (U : Set (Euclidean (n+1))) (hU : IsOpen U)
    (G : Euclidean (n+1) → Euclidean m) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hagree : ∀ q : {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source},
      Fin.snoc (c q.val.1).val q.val.2.val ∈ U →
        G (Fin.snoc (c q.val.1).val q.val.2.val) = (d (F q.val)).val)
    (W : Euclidean m → Index m k → ℝ)
    (p : M) (hp : p ∈ c.source) (t : UnitInterval)
    (hpt : F (p,t) ∈ d.source) (hpU : Fin.snoc (c p).val t.val ∈ U)
    (hW : W (G (Fin.snoc (c p).val t.val)) =
      fun J => coefficients A k d hd ω ⟨F (p,t),hpt⟩ J) :
    (fun I => coefficients C k c hc (alpha D ω t) ⟨p,hp⟩ I) =
      ambientAlphaCoefficients n m k G W (Fin.snoc (c p).val t.val) := by
  classical
  ext I
  rw [CartanResults.coefficients_eq_evaluate]
  rw [alpha, FormPullbackResults.pullback_apply]
  rw [ExteriorAlgebraResults.coefficient_expansion A k d hd ω ⟨F (p,t),hpt⟩]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  unfold ambientAlphaCoefficients
  rw [hW]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  rw [ExteriorAlgebraResults.determinant_normalization]
  congr 1
  ext i j
  change coordinateCovector A.tangent.fiberCoordinates d hd (F (p,t)) hpt
    (Set.powersetCard.ofFinEmbEquiv.symm J i)
      (D.spatial t p (coordinateVector C.tangent.fiberCoordinates c hc p hp
        (Set.powersetCard.ofFinEmbEquiv.symm I j))) = _
  simp only [coordinateCovector, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  rw [D.spatial_jacobian hF c hc d hd C.tangent.fiberCoordinates A.tangent.fiberCoordinates
    U hU G hG hagree p hp t hpt hpU]
  simp only [coordinateVector, LinearEquiv.apply_symm_apply, snoc_standard_basis]
  rfl

theorem alpha_coefficients_locally_smooth {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T k)
    (B : FormBundle A k) (hω : IsForm B ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    LocallyContDiffAlong (⊤ : ℕ∞)
      (fun q : c.source × UnitInterval => Fin.snoc (c q.1.val).val q.2.val)
      (fun q => fun I => coefficients C k c hc (alpha D ω q.2) q.1 I) := by
  intro q
  obtain ⟨d,hd,hqd⟩ := T.smoothStructure.property.1.1 (F (q.1.val,q.2))
  obtain ⟨U,hU,hqU,G,hG,heG⟩ := hF.2 c hc d hd ⟨(q.1.val,q.2),q.1.property,hqd⟩
  obtain ⟨V,hV,hqV,W,hW,heW⟩ :=
    ((ExteriorDerivativeResults.smooth_coefficients A k B ω).mp hω) d hd
      ⟨F (q.1.val,q.2),hqd⟩
  obtain ⟨O,hO,hqO,heO⟩ := HomotopyResults.cylinder_chart_neighborhood c F hF.1
    d.source d.open_source q.1 q.2 hqd
  have hGq : G (Fin.snoc (c q.1.val).val q.2.val) = (d (F (q.1.val,q.2))).val :=
    heG ⟨(q.1.val,q.2),q.1.property,hqd⟩ hqU
  have hGV : G (Fin.snoc (c q.1.val).val q.2.val) ∈ V := by
    rw [hGq]
    exact hqV
  obtain ⟨P,hPV,hP,hqP⟩ := mem_nhds_iff.mp
    ((hG.contDiffAt (hU.mem_nhds hqU)).continuousAt (hV.mem_nhds hGV))
  let Z := (U ∩ P) ∩ O
  have hZ : IsOpen Z := (hU.inter hP).inter hO
  have hqZ : Fin.snoc (c q.1.val).val q.2.val ∈ Z := ⟨⟨hqU,hqP⟩,hqO⟩
  have hGZ : ContDiffOn ℝ (⊤ : ℕ∞) G Z := hG.mono (fun z hz => hz.1.1)
  have hWZ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => W (G z)) Z :=
    hW.comp hGZ (fun z hz => hPV hz.1.2)
  refine ⟨Z,hZ,hqZ,ambientAlphaCoefficients n m k G W,
    ambientAlphaCoefficients_contDiffOn G W Z hZ hGZ hWZ, ?_⟩
  intro y hy
  have hyd : F (y.1.val,y.2) ∈ d.source := heO y.1 y.2 hy.2
  have hGy : G (Fin.snoc (c y.1.val).val y.2.val) = (d (F (y.1.val,y.2))).val :=
    heG ⟨(y.1.val,y.2),y.1.property,hyd⟩ hy.1.1
  have hWy : W (G (Fin.snoc (c y.1.val).val y.2.val)) =
      fun J => coefficients A k d hd ω ⟨F (y.1.val,y.2),hyd⟩ J := by
    rw [hGy]
    apply heW ⟨F (y.1.val,y.2),hyd⟩
    change (d (F (y.1.val,y.2))).val ∈ V
    rw [← hGy]
    exact hPV hy.1.2
  exact (alpha_coefficients_eq_ambient hF C A D ω c hc d hd U hU G hG heG W
    y.1.val y.1.property y.2 hyd hy.1.1 hWy).symm

/-- Each genuine horizontal pullback coefficient is continuous in the actual
closed time interval, in every degree including zero. -/
theorem alpha_coefficients_continuous_time {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T k)
    (B : FormBundle A k) (hω : IsForm B ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n k) :
    Continuous (fun t : UnitInterval => coefficients C k c hc (alpha D ω t) p I) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨U,hU,htU,G,hG,heG⟩ :=
    alpha_coefficients_locally_smooth hF C A D ω B hω c hc (p,t)
  let e : UnitInterval → Euclidean (n+1) := fun s => Fin.snoc (c p.val).val s.val
  have he : Continuous e := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [e,Fin.snoc_last] using continuous_subtype_val
    · simpa only [e,Fin.snoc_castSucc] using
        (continuous_const : Continuous (fun _ : UnitInterval => (c p.val).val j))
  have hC : ContinuousAt (fun s => G (e s) I) t :=
    (continuous_apply I).continuousAt.comp (f := fun s : UnitInterval => G (e s))
      ((hG.contDiffAt (hU.mem_nhds htU)).continuousAt.comp (f := e) he.continuousAt)
  apply hC.congr_of_eventuallyEq
  filter_upwards [he.continuousAt (hU.mem_nhds htU)] with s hs
  exact congrFun (heG (p,s) hs).symm I

/-- The total time parametrization used by FTC preserves this continuity on the
closed unit interval. -/
theorem alpha_coefficients_continuousOn {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T k)
    (B : FormBundle A k) (hω : IsForm B ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n k) :
    ContinuousOn (fun t : ℝ => coefficients C k c hc (alpha D ω (intervalTime t)) p I)
      (Icc (0 : ℝ) 1) := by
  have hclamp : Continuous intervalTime := by
    apply Continuous.subtype_mk
    exact continuous_const.max (continuous_const.min continuous_id)
  exact ((alpha_coefficients_continuous_time hF C A D ω B hω c hc p I).comp hclamp).continuousOn

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData HomotopyData HomotopyIntegration Set
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

theorem betaIntegralOperator_isChainHomotopy_of_coefficients
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (hF : IsSmoothHomotopy S T F)
    (D : HomotopyDifferentials S T F)
    (hbeta : ∀ k (eta : J.forms (k+1)),
      JointSmoothCoefficients C k (fun t => beta C D eta.val t))
    (hpos : ∀ k (ω : J.forms (k+1))
      (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source) (I : Index n (k+1)),
      ContinuousOn
        (fun t => coefficients C (k+1) c hc (alpha D ω.val (intervalTime t)) p I)
        (Icc 0 1) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun t => coefficients C (k+1) c hc (alpha D ω.val (intervalTime t)) p I)
          (coefficients C (k+1) c hc (K.D k (beta C D ω.val (intervalTime t))) p I +
            coefficients C (k+1) c hc
              (beta C D (J.d (k+1) ω).val (intervalTime t)) p I) t) :
    IsChainHomotopy K J D (betaIntegralOperator K J D hbeta) := by
  apply isChainHomotopy_of_coefficients K J D (betaIntegralOperator K J D hbeta)
    (betaIntegralOperator_isCoefficientIntegral K J D hbeta) hpos
  · intro k ω c hc p I
    have hint := jointSmooth_derivative_coefficientsIntervalIntegrable K k _ (hbeta k ω)
    refine ⟨hint c hc p I, ?_⟩
    rw [derivative_betaIntegralOperator]
    exact coefficients_integralField C (k+1) _ hint c hc p I
  · intro ω c hc p I
    exact degreeZero_coefficient_relation J hF D ω c hc p I
end SmoothManifolds.HomotopyResults

namespace SmoothManifolds.AmbientHomotopy
set_option backward.isDefEq.respectTransparency false
open ContinuousAlternatingMap MeasureTheory Set Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem alpha_evaluation_hasDerivAt_at {k : ℕ}
    (Ω : E × ℝ → (E × ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (x : E) (t : ℝ) (hΩ : DifferentiableAt ℝ Ω (x,t)) (v : Fin k → E) :
    HasDerivAt (fun s => alpha Ω s x v)
      (sliceL k (fderiv ℝ Ω (x,t) (0,1)) v) t := by
  have h := (alpha_hasDerivAt_at Ω x t hΩ).hasFDerivAt.continuousAlternatingMap_apply
    (fun i => hasFDerivAt_const (v i) t)
  simpa using h.hasDerivAt

theorem alpha_chain_hasDerivAt_at {k : ℕ}
    (Ω : E × ℝ → (E × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (x : E) (t : ℝ) (hΩ : DifferentiableAt ℝ Ω (x,t)) (v : Fin (k+1) → E) :
    HasDerivAt (fun s => alpha Ω s x v)
      (extDeriv (fun y => beta Ω (y,t)) x v + beta (extDeriv Ω) (x,t) v) t := by
  have h := alpha_evaluation_hasDerivAt_at Ω x t hΩ v
  rw [← local_chain_identity_at Ω x t hΩ] at h
  exact h


section AlgebraicPullback
universe v
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem alpha_pullback {k : ℕ} (F : E × ℝ → W)
    (Ω : W → W [⋀^Fin k]→L[ℝ] ℝ) (J : E × ℝ → (E × ℝ) →L[ℝ] W)
    (t : ℝ) (x : E) :
    alpha (fun z => (Ω (F z)).compContinuousLinearMap (J z)) t x =
      (Ω (F (x,t))).compContinuousLinearMap
        ((J (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) := by
  apply ContinuousAlternatingMap.ext
  intro v
  rfl

theorem beta_pullback {k : ℕ} (F : E × ℝ → W)
    (Ω : W → W [⋀^Fin (k+1)]→L[ℝ] ℝ) (J : E × ℝ → (E × ℝ) →L[ℝ] W)
    (x : E) (t : ℝ) :
    beta (fun z => (Ω (F z)).compContinuousLinearMap (J z)) (x,t) =
      ((Ω (F (x,t))).curryLeft (J (x,t) (0,1))).compContinuousLinearMap
        ((J (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) := by
  apply ContinuousAlternatingMap.ext
  intro v
  change Ω (F (x,t)) (fun i => J (x,t)
      ((Fin.cons ((0,1) : E × ℝ) (fun j => (v j,0)) : Fin (k+1) → E × ℝ) i)) =
    Ω (F (x,t)) (Fin.cons (J (x,t) (0,1)) (fun j => J (x,t) (v j,0)))
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end AlgebraicPullback

end SmoothManifolds.AmbientHomotopy

namespace SmoothManifolds.AmbientHomotopy
set_option backward.isDefEq.respectTransparency false
open Set ContinuousAlternatingMap
universe u v
variable {E : Type u} {W : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem pullback_contDiffOn {k : ℕ} {U : Set E} {V : Set W}
    (F : E → W) (Ω : W → W [⋀^Fin k]→L[ℝ] ℝ)
    (hU : IsOpen U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω V) (hmaps : MapsTo F U V) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (Ω (F z)).compContinuousLinearMap (fderiv ℝ F z)) U := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hO : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Ω (F z)) U := hΩ.comp hF hmaps
  have hC : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (compContinuousLinearMapCLM (fderiv ℝ F z) :
        (W [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ))) U := by
    exact (cpolynomialOn_compContinuousLinearMapCLM (𝕜 := ℝ)
      (E := E) (F := W) (G := ℝ) (ι := Fin k) Set.univ).contDiffOn.comp hD
        (mapsTo_univ _ _)
  exact hC.clm_apply hO

end SmoothManifolds.AmbientHomotopy

namespace SmoothManifolds.HomotopyData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData DeRhamData Set Filter
open scoped Topology
universe u

def coefficientModel {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (p : c.source) : (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ :=
  ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k
    (fun I => coefficients C k c hc ω p I)

theorem coefficientModel_apply {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (p : c.source) (v : Fin k → Euclidean n) :
    coefficientModel (k := k) C c hc ω p v =
      evaluate (TangentSpace S p.val) k (ω p.val)
        (fun i => (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm (v i)) := by
  have h := CartanResults.evaluate_model_coefficients C k ω c hc p
    (fun i => (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm (v i))
    (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k)
    (fun _ _ => rfl)
  simpa only [coefficientModel, LinearEquiv.apply_symm_apply] using h.symm

/-- Scalar-valued evaluation of an intrinsic exterior derivative through any
strong ambient coefficient representative. -/
theorem exteriorDerivative_evaluate_extension {n k : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (ω : Field S k) (η : Field S (k+1))
    (hη : HasExteriorDerivative C ω η)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (U : Set (Euclidean n)) (hU : IsOpen U)
    (hpU : (c p).val ∈ U) (W : Euclidean n → Index n k → ℝ)
    (hW : ContDiffOn ℝ 1 W U)
    (heW : ∀ q : c.source, (c q.val).val ∈ U → W (c q.val).val =
      fun I => coefficients C k c hc ω q I)
    (v : Fin (k+1) → TangentSpace S p) :
    evaluate (TangentSpace S p) (k+1) (η p) v =
      extDeriv (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (W z))
        (c p).val (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)) := by
  rw [hη c hc p hp]
  have h := ExteriorDerivativeResults.coordinateDerivative_evaluate_extension C k c hc ω
    p hp U hU hpU W hW heW
    (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i))
  simpa only [LinearEquiv.symm_apply_apply] using h


theorem coefficientModel_alpha_of_coordinates {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T k)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : c.source) (t : UnitInterval) (hpt : F (p.val,t) ∈ d.source)
    (L : Euclidean n →L[ℝ] Euclidean m)
    (hL : ∀ v : TangentSpace S p.val,
      A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt (D.spatial t p.val v) =
        L (C.tangent.fiberCoordinates.equiv c hc p.val p.property v)) :
    coefficientModel (k := k) C c hc (alpha D ω t) p =
      (coefficientModel (k := k) A d hd ω ⟨F (p.val,t),hpt⟩).compContinuousLinearMap L := by
  exact ExteriorDerivativeResults.coefficient_pullback_of_jacobian S T C A
    (fun q => F (q,t)) (D.spatial t) c hc d hd p.val p.property hpt L hL k ω

theorem coefficientModel_beta_of_coordinates {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T (k+1))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : c.source) (t : UnitInterval) (hpt : F (p.val,t) ∈ d.source)
    (L : Euclidean n →L[ℝ] Euclidean m) (vtime : Euclidean m)
    (hL : ∀ v : TangentSpace S p.val,
      A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt (D.spatial t p.val v) =
        L (C.tangent.fiberCoordinates.equiv c hc p.val p.property v))
    (hvtime : A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt (D.velocity p.val t) = vtime) :
    coefficientModel (k := k) C c hc (beta C D ω t) p =
      ((coefficientModel (k := k+1) A d hd ω ⟨F (p.val,t),hpt⟩).curryLeft vtime).compContinuousLinearMap L := by
  ext v
  rw [coefficientModel_apply]
  change (CartanData.evaluationEquiv C.tangent.fiberCoordinates p.val k
    (beta C D ω t p.val)) _ = _
  rw [beta, LinearEquiv.apply_symm_apply]
  change evaluate (TangentSpace T (F (p.val,t))) (k+1) (ω (F (p.val,t)))
    (Fin.cons (D.velocity p.val t) (fun i => D.spatial t p.val
      ((C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm (v i)))) =
    coefficientModel (k := k+1) A d hd ω ⟨F (p.val,t),hpt⟩ (Fin.cons vtime (fun i => L (v i)))
  rw [coefficientModel_apply]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact (LinearEquiv.eq_symm_apply _).mpr hvtime
  · simp only [Fin.cons_succ]
    apply (A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt).injective
    rw [hL, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The cylinder's joint coordinate map is continuous and linear. -/
def cylinderCoordinateLinear (n : ℕ) : Euclidean n × ℝ →L[ℝ] Euclidean (n+1) :=
  ContinuousLinearMap.pi (fun i => Fin.lastCases (ContinuousLinearMap.snd ℝ (Euclidean n) ℝ)
    (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Euclidean n) ℝ)) i)

@[simp] theorem cylinderCoordinateLinear_apply {n : ℕ} (z : Euclidean n × ℝ) :
    cylinderCoordinateLinear n z = Fin.snoc z.1 z.2 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [cylinderCoordinateLinear]

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData DeRhamData Set Filter
open scoped Topology
universe u

def cylinderPullbackModel {n m k : ℕ}
    (H : Euclidean n × ℝ → Euclidean m) (W : Euclidean m → Index m k → ℝ) :
    Euclidean n × ℝ → (Euclidean n × ℝ) [⋀^Fin k]→L[ℝ] ℝ :=
  fun z => (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv m k (W (H z))).compContinuousLinearMap
    (fderiv ℝ H z)

theorem coefficientModel_alpha_pullback {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T k)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : c.source) (t : UnitInterval) (hpt : F (p.val,t) ∈ d.source)
    (H : Euclidean n × ℝ → Euclidean m) (W : Euclidean m → Index m k → ℝ)
    (hW : W (H ((c p.val).val,t.val)) = coefficients A k d hd ω ⟨F (p.val,t),hpt⟩)
    (hL : ∀ v : TangentSpace S p.val,
      A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt (D.spatial t p.val v) =
        fderiv ℝ H ((c p.val).val,t.val)
          (C.tangent.fiberCoordinates.equiv c hc p.val p.property v,0)) :
    coefficientModel (k := k) C c hc (alpha D ω t) p =
      AmbientHomotopy.alpha (cylinderPullbackModel (k := k) H W) t.val (c p.val).val := by
  rw [coefficientModel_alpha_of_coordinates C A D ω c hc d hd p t hpt
    ((fderiv ℝ H ((c p.val).val,t.val)).comp
      (ContinuousLinearMap.inl ℝ (Euclidean n) ℝ)) hL]
  unfold cylinderPullbackModel
  rw [AmbientHomotopy.alpha_pullback H
    (fun y => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv m k (W y))
    (fderiv ℝ H) t.val (c p.val).val]
  rw [hW]
  rfl

theorem coefficientModel_beta_pullback {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T (k+1))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : c.source) (t : UnitInterval) (hpt : F (p.val,t) ∈ d.source)
    (H : Euclidean n × ℝ → Euclidean m) (W : Euclidean m → Index m (k+1) → ℝ)
    (hW : W (H ((c p.val).val,t.val)) = coefficients A (k+1) d hd ω ⟨F (p.val,t),hpt⟩)
    (hL : ∀ v : TangentSpace S p.val,
      A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt (D.spatial t p.val v) =
        fderiv ℝ H ((c p.val).val,t.val)
          (C.tangent.fiberCoordinates.equiv c hc p.val p.property v,0))
    (hv : A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt (D.velocity p.val t) =
      fderiv ℝ H ((c p.val).val,t.val) (0,1)) :
    coefficientModel (k := k) C c hc (beta C D ω t) p =
      AmbientHomotopy.beta (cylinderPullbackModel (k := k+1) H W) ((c p.val).val,t.val) := by
  rw [coefficientModel_beta_of_coordinates C A D ω c hc d hd p t hpt
    ((fderiv ℝ H ((c p.val).val,t.val)).comp
      (ContinuousLinearMap.inl ℝ (Euclidean n) ℝ)) _ hL hv]
  unfold cylinderPullbackModel
  rw [AmbientHomotopy.beta_pullback H
    (fun y => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv m (k+1) (W y))
    (fderiv ℝ H) (c p.val).val t.val]
  rw [hW]
  rfl
end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData DeRhamData Set Filter
open scoped Topology
universe u

theorem coefficientModel_exteriorDerivative_extension {n k : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (ω : Field S k) (η : Field S (k+1))
    (hη : HasExteriorDerivative C ω η)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (U : Set (Euclidean n)) (hU : IsOpen U)
    (hpU : (c p.val).val ∈ U) (W : Euclidean n → Index n k → ℝ)
    (hW : ContDiffOn ℝ 1 W U)
    (heW : ∀ q : c.source, (c q.val).val ∈ U → W (c q.val).val =
      fun I => coefficients C k c hc ω q I) :
    coefficientModel (k := k+1) C c hc η p =
      extDeriv (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (W z))
        (c p.val).val := by
  ext v
  rw [coefficientModel_apply (k := k+1)]
  have h := exteriorDerivative_evaluate_extension (k := k) C ω η hη c hc p.val p.property
    U hU hpU W hW heW
    (fun i => (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm (v i))
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- The time contraction of the exterior derivative of a local cylinder
pullback represents beta applied to the actual intrinsic target derivative. -/
theorem coefficientModel_beta_exteriorDerivative_pullback
    {n m k : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T (k+1)) (η : Field T (k+2))
    (hη : HasExteriorDerivative A ω η)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : c.source) (t : UnitInterval) (hpt : F (p.val,t) ∈ d.source)
    (V : Set (Euclidean m)) (hV : IsOpen V) (hptV : (d (F (p.val,t))).val ∈ V)
    (W : Euclidean m → Index m (k+1) → ℝ) (hW : ContDiffOn ℝ 1 W V)
    (heW : ∀ q : d.source, (d q.val).val ∈ V → W (d q.val).val =
      fun I => coefficients A (k+1) d hd ω q I)
    (G : Euclidean n × ℝ → Euclidean m)
    (hG : ContDiffAt ℝ (⊤ : ℕ∞) G ((c p.val).val,t.val))
    (hGp : G ((c p.val).val,t.val) = (d (F (p.val,t))).val)
    (hL : ∀ v : TangentSpace S p.val,
      A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt (D.spatial t p.val v) =
        (fderiv ℝ G ((c p.val).val,t.val))
          (C.tangent.fiberCoordinates.equiv c hc p.val p.property v,0))
    (hv : A.tangent.fiberCoordinates.equiv d hd (F (p.val,t)) hpt (D.velocity p.val t) =
      (fderiv ℝ G ((c p.val).val,t.val)) (0,1)) :
    AmbientHomotopy.beta
      (extDeriv (fun z =>
        (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv m (k+1) (W (G z))).compContinuousLinearMap (fderiv ℝ G z))) ((c p.val).val,t.val) =
      coefficientModel (k := k+1) C c hc (beta C D η t) p := by
  let Ω : Euclidean m → (Euclidean m) [⋀^Fin (k+1)]→L[ℝ] ℝ := fun y =>
    ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv m (k+1) (W y)
  have hΩ : DifferentiableAt ℝ Ω (G ((c p.val).val,t.val)) := by
    rw [hGp]
    exact (((ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv m (k+1)).contDiff.comp_contDiffOn hW).contDiffAt (hV.mem_nhds hptV)).differentiableAt (by norm_num)
  have hNat := extDeriv_pullback (f := G) (x := ((c p.val).val,t.val)) hΩ hG (by simp)
  change AmbientHomotopy.sliceL (k+1) (AmbientHomotopy.contractL (k+1)
    (extDeriv (fun z => (Ω (G z)).compContinuousLinearMap (fderiv ℝ G z))
      ((c p.val).val,t.val))) = _
  rw [hNat]
  change AmbientHomotopy.beta
    (fun z => (extDeriv Ω (G z)).compContinuousLinearMap (fderiv ℝ G z))
      ((c p.val).val,t.val) = _
  rw [AmbientHomotopy.beta_pullback]
  rw [coefficientModel_beta_of_coordinates (k := k+1) C A D η c hc d hd p t hpt
    ((fderiv ℝ G ((c p.val).val,t.val)).comp (ContinuousLinearMap.inl ℝ (Euclidean n) ℝ))
    ((fderiv ℝ G ((c p.val).val,t.val)) (0,1)) hL hv]
  rw [coefficientModel_exteriorDerivative_extension (k := k+1) A ω η hη d hd
    ⟨F (p.val,t),hpt⟩ V hV hptV W hW heW]
  rw [hGp]

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData DeRhamData Set Filter
open scoped Topology
universe u

theorem coefficientModel_on_basis {n k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (p : c.source) (I : Index n k) :
    coefficientModel (k := k) C c hc ω p
      (fun j => Pi.single (Set.powersetCard.ofFinEmbEquiv.symm I j) 1) =
        coefficients C k c hc ω p I := by
  rw [coefficientModel_apply, CartanResults.coefficients_eq_evaluate]
  rfl

/-- Local cylinder representatives imply the actual coefficient differential
relation used in the homotopy formula. -/
theorem positive_relation_of_ambient {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N}
    (C : CotangentBundle S) (D : HomotopyDifferentials S T F)
    (ω : Field T (k+1)) (η : Field T (k+2))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (t : UnitInterval) (ht : t.val ∈ Ioo (0 : ℝ) 1)
    (δ : Field S (k+1)) (hδ : HasExteriorDerivative C (beta C D ω t) δ)
    (Ω : Euclidean n × ℝ → (Euclidean n × ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (U : Set (Euclidean n × ℝ)) (hU : IsOpen U) (hptU : ((c p.val).val,t.val) ∈ U)
    (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω U)
    (hA : ∀ (q : c.source) (s : UnitInterval), ((c q.val).val,s.val) ∈ U →
      coefficientModel (k := k+1) C c hc (alpha D ω s) q =
        AmbientHomotopy.alpha Ω s.val (c q.val).val)
    (hB : ∀ (q : c.source) (s : UnitInterval), ((c q.val).val,s.val) ∈ U →
      coefficientModel (k := k) C c hc (beta C D ω s) q =
        AmbientHomotopy.beta Ω ((c q.val).val,s.val))
    (hη : coefficientModel (k := k+1) C c hc (beta C D η t) p =
      AmbientHomotopy.beta (extDeriv Ω) ((c p.val).val,t.val))
    (I : Index n (k+1)) :
    HasDerivAt (fun s => coefficients C (k+1) c hc (alpha D ω (intervalTime s)) p I)
      (coefficients C (k+1) c hc δ p I +
        coefficients C (k+1) c hc (beta C D η t) p I) t.val := by
  let E := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k
  let Ψ : Euclidean n → Index n k → ℝ :=
    fun x => E.symm (AmbientHomotopy.beta Ω (x,t.val))
  let V : Set (Euclidean n) := (fun x : Euclidean n => (x,t.val)) ⁻¹' U
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclidean n => (x,t.val)) :=
    contDiff_id.prodMk contDiff_const
  have hV : IsOpen V := hU.preimage hs.continuous
  have hpV : (c p.val).val ∈ V := hptU
  have hΩs : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Euclidean n => Ω (x,t.val)) V :=
    hΩ.comp hs.contDiffOn (fun _ h => h)
  have hβs : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Euclidean n => AmbientHomotopy.beta Ω (x,t.val)) V :=
    by
      simpa only [AmbientHomotopy.beta, Function.comp_def] using
        (AmbientHomotopy.sliceL (E := Euclidean n) k).contDiff.comp_contDiffOn
          ((AmbientHomotopy.contractL (E := Euclidean n) k).contDiff.comp_contDiffOn hΩs)
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ V := E.symm.contDiff.comp_contDiffOn hβs
  have heΨ : ∀ q : c.source, (c q.val).val ∈ V → Ψ (c q.val).val =
      fun J => coefficients C k c hc (beta C D ω t) q J := by
    intro q hq
    change E.symm (AmbientHomotopy.beta Ω ((c q.val).val,t.val)) = _
    rw [← hB q t hq]
    exact E.symm_apply_apply _
  let v : Fin (k+1) → Euclidean n :=
    fun j => Pi.single (Set.powersetCard.ofFinEmbEquiv.symm I j) 1
  have hδcoeff : coefficients C (k+1) c hc δ p I =
      extDeriv (fun y => AmbientHomotopy.beta Ω (y,t.val)) (c p.val).val v := by
    rw [CartanResults.coefficients_eq_evaluate]
    have h := exteriorDerivative_evaluate_extension C (beta C D ω t) δ hδ c hc
      p.val p.property V hV hpV Ψ (hΨ.of_le (by norm_num)) heΨ
      (fun j => coordinateVector C.tangent.fiberCoordinates c hc p.val p.property
        (Set.powersetCard.ofFinEmbEquiv.symm I j))
    have hEΨ : (fun z => E (Ψ z)) = (fun y => AmbientHomotopy.beta Ω (y,t.val)) := by
      funext z
      exact E.apply_symm_apply _
    change evaluate (TangentSpace S p.val) (k+1) (δ p.val) _ =
      extDeriv (fun z => E (Ψ z)) (c p.val).val _ at h
    rw [hEΨ] at h
    simpa only [coordinateVector, LinearEquiv.apply_symm_apply] using h
  have hηcoeff : coefficients C (k+1) c hc (beta C D η t) p I =
      AmbientHomotopy.beta (extDeriv Ω) ((c p.val).val,t.val) v := by
    have h := congrArg (fun A => A v) hη
    simpa only [v, coefficientModel_on_basis] using h
  have hder := AmbientHomotopy.alpha_chain_hasDerivAt_at Ω (c p.val).val t.val
    ((hΩ.contDiffAt (hU.mem_nhds hptU)).differentiableAt (by simp)) v
  rw [← hδcoeff, ← hηcoeff] at hder
  apply hder.congr_of_eventuallyEq
  have htime : Continuous (fun s : ℝ => ((c p.val).val,s)) :=
    continuous_const.prodMk continuous_id
  filter_upwards [Ioo_mem_nhds ht.1 ht.2,
    htime.continuousAt (hU.mem_nhds hptU)] with s hs hsU
  have hsIcc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2.le⟩
  have h := congrArg (fun A => A v) (hA p (intervalTime s) (by
    rw [intervalTime_val_of_mem s hsIcc]
    exact hsU))
  simpa only [v, coefficientModel_on_basis, intervalTime_val_of_mem s hsIcc] using h

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyData
open ModelData
@[simp] theorem cylinderCoordinateLinear_time (n : ℕ) :
    cylinderCoordinateLinear n ((0 : Euclidean n),1) = Pi.single (Fin.last n) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem fderiv_comp_cylinderCoordinateLinear {n m : ℕ}
    (G : Euclidean (n+1) → Euclidean m) (x : Euclidean n) (t : ℝ)
    (hG : DifferentiableAt ℝ G (Fin.snoc x t)) (w : Euclidean n × ℝ) :
    fderiv ℝ (G ∘ cylinderCoordinateLinear n) (x,t) w =
      fderiv ℝ G (Fin.snoc x t) (Fin.snoc w.1 w.2) := by
  have hG' : HasFDerivAt G (fderiv ℝ G (Fin.snoc x t)) (cylinderCoordinateLinear n (x,t)) := by
    simpa only [cylinderCoordinateLinear_apply] using hG.hasFDerivAt
  rw [(hG'.comp (x,t) (cylinderCoordinateLinear n).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, cylinderCoordinateLinear_apply]

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData DeRhamData Set Filter
open scoped Topology
universe u

/-- The positive-degree differential relation for the actual homotopy, proved
from its joint ambient smoothness and the two intrinsic exterior derivatives. -/
theorem positive_coefficient_relation {n m k : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M × UnitInterval → N} (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) (ω : Field T (k+1)) (η : Field T (k+2))
    (B : FormBundle A (k+1)) (hω : IsForm B ω) (hη : HasExteriorDerivative A ω η)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (t : UnitInterval) (ht : t.val ∈ Ioo (0 : ℝ) 1)
    (δ : Field S (k+1)) (hδ : HasExteriorDerivative C (beta C D ω t) δ)
    (I : Index n (k+1)) :
    HasDerivAt (fun s => coefficients C (k+1) c hc (alpha D ω (intervalTime s)) p I)
      (coefficients C (k+1) c hc δ p I +
        coefficients C (k+1) c hc (beta C D η t) p I) t.val := by
  obtain ⟨d,hd,hpd⟩ := T.smoothStructure.property.1.1 (F (p.val,t))
  obtain ⟨U,hU,hpU,G,hG,heG⟩ := hF.2 c hc d hd ⟨(p.val,t),p.property,hpd⟩
  obtain ⟨V,hV,hpV,W,hW,heW⟩ :=
    ((ExteriorDerivativeResults.smooth_coefficients A (k+1) B ω).mp hω) d hd
      ⟨F (p.val,t),hpd⟩
  obtain ⟨O,hO,hpO,heO⟩ := HomotopyResults.cylinder_chart_neighborhood c F hF.1
    d.source d.open_source p t hpd
  have hGp : G (Fin.snoc (c p.val).val t.val) = (d (F (p.val,t))).val :=
    heG ⟨(p.val,t),p.property,hpd⟩ hpU
  have hGV : G (Fin.snoc (c p.val).val t.val) ∈ V := by rw [hGp]; exact hpV
  obtain ⟨P,hPV,hP,hpP⟩ := mem_nhds_iff.mp
    ((hG.contDiffAt (hU.mem_nhds hpU)).continuousAt (hV.mem_nhds hGV))
  let Z := (U ∩ P) ∩ O
  have hZ : IsOpen Z := (hU.inter hP).inter hO
  let Q := (cylinderCoordinateLinear n) ⁻¹' Z
  have hQ : IsOpen Q := hZ.preimage (cylinderCoordinateLinear n).continuous
  have hpQ : ((c p.val).val,t.val) ∈ Q := by
    change cylinderCoordinateLinear n ((c p.val).val,t.val) ∈ Z
    simpa only [cylinderCoordinateLinear_apply] using (show Fin.snoc (c p.val).val t.val ∈ Z from ⟨⟨hpU,hpP⟩,hpO⟩)
  let H : Euclidean n × ℝ → Euclidean m := G ∘ cylinderCoordinateLinear n
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H Q :=
    (hG.mono (fun z (hz : z ∈ Z) => hz.1.1)).comp (cylinderCoordinateLinear n).contDiff.contDiffOn
      (fun _ h => h)
  have hHV : MapsTo H Q V := fun z hz => hPV hz.1.2
  have hZqs (q : c.source) (s : UnitInterval) (hqs : ((c q.val).val,s.val) ∈ Q) :
      Fin.snoc (c q.val).val s.val ∈ Z := by
    change cylinderCoordinateLinear n ((c q.val).val,s.val) ∈ Z at hqs
    simpa only [cylinderCoordinateLinear_apply] using hqs
  have hHpoint (q : c.source) (s : UnitInterval) (hqs : ((c q.val).val,s.val) ∈ Q)
      (hqd : F (q.val,s) ∈ d.source) : H ((c q.val).val,s.val) = (d (F (q.val,s))).val := by
    simpa only [H, Function.comp_apply, cylinderCoordinateLinear_apply] using
      heG ⟨(q.val,s),q.property,hqd⟩ (hZqs q s hqs).1.1
  have hWpoint (q : c.source) (s : UnitInterval) (hqs : ((c q.val).val,s.val) ∈ Q)
      (hqd : F (q.val,s) ∈ d.source) :
      W (H ((c q.val).val,s.val)) = fun J => coefficients A (k+1) d hd ω ⟨F (q.val,s),hqd⟩ J := by
    rw [hHpoint q s hqs hqd]
    apply heW ⟨F (q.val,s),hqd⟩
    change (d (F (q.val,s))).val ∈ V
    rw [← hHpoint q s hqs hqd]
    exact hHV hqs
  have hsp (q : c.source) (s : UnitInterval) (hqs : ((c q.val).val,s.val) ∈ Q)
      (hqd : F (q.val,s) ∈ d.source) (v : TangentSpace S q.val) :
      A.tangent.fiberCoordinates.equiv d hd (F (q.val,s)) hqd (D.spatial s q.val v) =
        fderiv ℝ H ((c q.val).val,s.val)
          (C.tangent.fiberCoordinates.equiv c hc q.val q.property v,0) := by
    change _ = fderiv ℝ (G ∘ cylinderCoordinateLinear n) _ _
    rw [fderiv_comp_cylinderCoordinateLinear G _ _
      ((hG.contDiffAt (hU.mem_nhds (hZqs q s hqs).1.1)).differentiableAt (by simp))]
    exact D.spatial_jacobian hF c hc d hd C.tangent.fiberCoordinates A.tangent.fiberCoordinates
      U hU G hG heG q.val q.property s hqd (hZqs q s hqs).1.1 v
  have hvel (q : c.source) (s : UnitInterval) (hqs : ((c q.val).val,s.val) ∈ Q)
      (hqd : F (q.val,s) ∈ d.source) :
      A.tangent.fiberCoordinates.equiv d hd (F (q.val,s)) hqd (D.velocity q.val s) =
        fderiv ℝ H ((c q.val).val,s.val) (0,1) := by
    change _ = fderiv ℝ (G ∘ cylinderCoordinateLinear n) _ _
    rw [fderiv_comp_cylinderCoordinateLinear G _ _
      ((hG.contDiffAt (hU.mem_nhds (hZqs q s hqs).1.1)).differentiableAt (by simp))]
    have hs : (Fin.snoc (0 : Euclidean n) 1 : Euclidean (n+1)) = Pi.single (Fin.last n) 1 :=
      (cylinderCoordinateLinear_apply ((0 : Euclidean n),1)).symm.trans (cylinderCoordinateLinear_time n)
    rw [hs]
    exact D.velocity_jacobian hF c d hd A.tangent.fiberCoordinates U hU G hG heG
      q.val q.property s hqd (hZqs q s hqs).1.1
  let Ω := cylinderPullbackModel (k := k+1) H W
  have hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω Q := AmbientHomotopy.pullback_contDiffOn H
    (fun y => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv m (k+1) (W y))
    hQ hH ((ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv m (k+1)).contDiff.comp_contDiffOn hW) hHV
  refine positive_relation_of_ambient C D ω η c hc p t ht δ hδ Ω Q hQ hpQ hΩ ?_ ?_ ?_ I
  · intro q s hqs
    let hqd := heO q s (hZqs q s hqs).2
    exact coefficientModel_alpha_pullback C A D ω c hc d hd q s hqd H W
      (hWpoint q s hqs hqd) (hsp q s hqs hqd)
  · intro q s hqs
    let hqd := heO q s (hZqs q s hqs).2
    exact coefficientModel_beta_pullback C A D ω c hc d hd q s hqd H W
      (hWpoint q s hqs hqd) (hsp q s hqs hqd) (hvel q s hqs hqd)
  · exact (coefficientModel_beta_exteriorDerivative_pullback C A D ω η hη c hc d hd p t hpd
      V hV hpV W (hW.of_le (by norm_num)) heW H (hH.contDiffAt (hQ.mem_nhds hpQ))
      (hHpoint p t hpQ hpd) (hsp p t hpQ hpd) (hvel p t hpQ hpd)).symm

end SmoothManifolds.HomotopyData

namespace SmoothManifolds.HomotopyResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData HomotopyData HomotopyIntegration Set
universe u

/-- The smooth homotopy operator, obtained by integrating the unique dt-first
component, satisfies the intrinsic chain identity in every degree. -/
theorem homotopy_operator :
    Specs.SmoothManifolds.DeRham.HomotopyOperator.homotopy_operatorType.{u} := by
  intro n m a b M N _ _ S T C B A E K J F hF
  let D := hF.differentials
  have hbeta : ∀ k (ω : J.forms (k+1)),
      JointSmoothCoefficients C k (fun t => beta C D ω.val t) := by
    intro k ω
    exact beta_jointSmooth hF C A D ω.val (E (k+1)) ((J.mem_forms _ _).mp ω.property)
  refine ⟨D,betaIntegralOperator K J D hbeta,
    betaIntegralOperator_isCoefficientIntegral K J D hbeta, ?_, ?_⟩
  · apply betaIntegralOperator_isChainHomotopy_of_coefficients K J hF D hbeta
    intro k ω c hc p I
    have hω : IsForm (E (k+1)) ω.val := (J.mem_forms _ _).mp ω.property
    refine ⟨alpha_coefficients_continuousOn hF C A D ω.val (E (k+1)) hω c hc p I, ?_⟩
    intro s hs
    let t : UnitInterval := ⟨s, hs.1.le, hs.2.le⟩
    have hclamp : intervalTime s = t := HomotopyData.intervalTime_coe t
    have hβ : IsForm (B k) (beta C D ω.val t) :=
      jointSmooth_isForm C k (B k) _ (hbeta k ω) t
    have hδ := K.coordinates k (beta C D ω.val t) hβ
    have hη := J.coordinates (k+1) ω.val hω
    have hder := positive_coefficient_relation hF C A D ω.val
      (J.d (k+1) ω).val (E (k+1)) hω hη c hc p t hs
      (K.D k (beta C D ω.val t)) hδ I
    simpa only [hclamp] using hder
  · intro k ω t p
    exact ⟨dtFirstDecomposition_exists C D ω.val t p,
      fun β hβ => dtFirstDecomposition_unique C D ω.val t p β hβ⟩
end SmoothManifolds.HomotopyResults
