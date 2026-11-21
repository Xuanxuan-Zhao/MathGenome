import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.Boundaries
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OperatorTopology.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint

/-! Composition and adjunction at the boundaries of the operator topologies.
The net indices retain every finite-dimensional subspace and every positive
integer, with the manuscript's literal n and 1/n factors. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace ENNReal
namespace ExpandedFA.OperatorTopology.Boundaries
universe u v
open ExpandedFA.OperatorTopology.Boundaries.Spec

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A finite-dimensional proper subspace has a unit orthogonal vector. -/
theorem exists_unit_orthogonal [CompleteSpace H] (hH : ¬ FiniteDimensional 𝕜 H)
    (M : FiniteSubspace 𝕜 H) : ∃ z : H, ‖z‖ = 1 ∧ z ∈ M.val.orthogonal := by
  let := M.property
  have htop : M.val ≠ ⊤ := by
    intro h
    apply hH
    exact Module.Finite.of_surjective M.val.subtype (by
      intro x
      exact ⟨⟨x, by rw [h]; trivial⟩, rfl⟩)
  have hbot : M.val.orthogonal ≠ ⊥ := by
    exact fun h => htop (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨((‖x‖ : 𝕜)⁻¹) • x, ?_, M.val.orthogonal.smul_mem _ hx⟩
  rw [norm_smul, norm_inv, RCLike.norm_coe_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]

theorem unit_vectors_exist : Spec.UnitVectorsExist.{u,v} := by
  intro 𝕜 H _ _ _ _ hH
  choose u hu using exists_unit_orthogonal hH
  exact ⟨u ⟨⊥, inferInstance⟩, (hu _).1, u, hu⟩

theorem net_identities : Spec.NetIdentities.{u,v} := by
  intro 𝕜 H _ _ _ e u he hu i
  have hn : (((i.2 : ℕ) : 𝕜)) ≠ 0 := by exact_mod_cast i.2.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · simp [netS, norm_smul, norm_inv, (hu i.1).1, he]
  · simp [netT, norm_smul, (hu i.1).1, he]
  · simp only [netS, netT, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, InnerProductSpace.rankOne_comp_rankOne,
      inner_self_eq_norm_sq_to_K, (hu i.1).1, one_pow, RCLike.ofReal_one,
      one_smul, smul_smul, inv_mul_cancel₀ hn]

theorem netS_tendsto (e : H) (u : FiniteSubspace 𝕜 H → H)
    (he : ‖e‖ = 1) (hu : UnitOrthogonalFamily u) :
    Tendsto (netS e u) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsnd : Tendsto (fun i : NetIndex 𝕜 H => i.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_PNat_val_atTop_atTop.comp hsnd)
  exact ht.congr fun i => (net_identities 𝕜 H e u he hu i).1.symm

theorem netT_eventually_zero (e : H) (u : FiniteSubspace 𝕜 H → H)
    (hu : UnitOrthogonalFamily u) (x : H) :
    ∀ᶠ i : NetIndex 𝕜 H in atTop, netT e u i x = 0 := by
  let M : FiniteSubspace 𝕜 H := ⟨𝕜 ∙ x, inferInstance⟩
  apply eventually_atTop.mpr
  refine ⟨(M, 1), fun i hi => ?_⟩
  have hx : x ∈ i.1.val := hi.1 (Submodule.mem_span_singleton_self x)
  have hzero : ⟪u i.1, x⟫_𝕜 = 0 :=
    (inner_eq_zero_symm).mp ((Submodule.mem_orthogonal _ _).mp (hu i.1).2 x hx)
  simp [netT, hzero]

theorem netT_tendsto (e : H) (u : FiniteSubspace 𝕜 H → H)
    (hu : UnitOrthogonalFamily u) :
    Tendsto (netT e u) atTop
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 H H) 0) := by
  apply (strong_tendsto_iff 𝕜 H H _ _ _ _).mpr
  intro x
  exact tendsto_const_nhds.congr' ((netT_eventually_zero e u hu x).mono fun _ h => h.symm)

theorem net_product_not_tendsto (e : H) (u : FiniteSubspace 𝕜 H → H)
    (he : ‖e‖ = 1) (hu : UnitOrthogonalFamily u) :
    ¬ Tendsto (fun i => (netT e u i).comp (netS e u i)) atTop
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 H H) 0) := by
  intro h
  have hlim := (strong_tendsto_iff 𝕜 H H _ _ _ _).mp h e
  have hconst : (fun i : NetIndex 𝕜 H => (netT e u i).comp (netS e u i) e) =
      fun _ => e := by
    funext i
    rw [(net_identities 𝕜 H e u he hu i).2.2]
    simp [he]
  rw [hconst] at hlim
  have he0 : e = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  simp [he0] at he

theorem net_convergence : Spec.NetConvergence.{u,v} := by
  intro 𝕜 H _ _ _ e u he hu
  exact ⟨netS_tendsto e u he hu, netT_tendsto e u hu,
    net_product_not_tendsto e u he hu⟩

/-- Norm convergence implies SOT convergence on the SAME bounded operators. -/
theorem strong_of_norm {α : Type*} {l : Filter α} {f : α → H →L[𝕜] H}
    {T : H →L[𝕜] H} (h : Tendsto f l (𝓝 T)) :
    Tendsto f l (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 H H) T) := by
  apply (strong_tendsto_iff 𝕜 H H _ _ _ _).mpr
  intro x
  exact ((ContinuousLinearMap.apply 𝕜 H x).continuous.tendsto T).comp h

theorem strong_composition_not_continuous : Spec.StrongCompositionNotContinuous.{u,v} := by
  intro 𝕜 H _ _ _ _ hH hcont
  obtain ⟨e, he, u, hu⟩ := unit_vectors_exist 𝕜 H hH
  have hS := strong_of_norm (netS_tendsto e u he hu)
  have hT := netT_tendsto e u hu
  let := OperatorTopology.Spec.StrongTopologyValue 𝕜 H H
  have hp := hT.prodMk_nhds hS
  have hc := hcont.tendsto (0, 0) |>.comp hp
  apply net_product_not_tendsto e u he hu
  simpa only [Function.comp_def, ContinuousLinearMap.zero_comp] using hc

theorem adjoint_wot_continuous : Spec.AdjointWOTContinuous.{u,v} := by
  intro 𝕜 H _ _ _ _
  let := OperatorTopology.Spec.WeakTopologyValue 𝕜 H H
  apply continuous_iff_continuousAt.mpr
  intro T
  apply (hilbert_tendsto_iff 𝕜 H H _ _ _ _).mpr
  intro x y
  have ht := (hilbert_tendsto_iff 𝕜 H H _ _ _ _).mp
    (tendsto_id : Tendsto (id : (H →L[𝕜] H) → _) (𝓝 T) (𝓝 T)) y x
  simpa only [id_eq, ContinuousLinearMap.adjoint_inner_right,
    RCLike.star_def, inner_conj_symm] using ht.star


/-- The literal unilateral shift on the canonical ℓ² model, over either field. -/
abbrev unilateralShift : Spec.ShiftType.{u} := Spec.ShiftValue

@[simp] theorem shift_zero (𝕜 : Type u) [RCLike 𝕜] (x : SequenceHilbert 𝕜) :
    unilateralShift 𝕜 x 0 = 0 := rfl

@[simp] theorem shift_succ (𝕜 : Type u) [RCLike 𝕜] (x : SequenceHilbert 𝕜) (n : ℕ) :
    unilateralShift 𝕜 x (n + 1) = x n := rfl

theorem shift_single (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (a : 𝕜) :
    unilateralShift 𝕜 (lp.single 2 n a) = lp.single 2 (n + 1) a := by
  apply lp.ext; funext m
  cases m with
  | zero => simp
  | succ m => simp [lp.single_apply, Pi.single_apply]

@[simp] theorem shift_adjoint_apply (𝕜 : Type u) [RCLike 𝕜]
    (x : SequenceHilbert 𝕜) (n : ℕ) :
    (unilateralShift 𝕜).adjoint x n = x (n + 1) := by
  have h := ContinuousLinearMap.adjoint_inner_right (unilateralShift 𝕜)
    (lp.single 2 n (1 : 𝕜)) x
  rw [shift_single] at h
  simpa [lp.inner_single_left, RCLike.inner_apply'] using h

theorem shift_coordinates : Spec.ShiftCoordinates.{u} := by
  intro 𝕜 _ x
  exact ⟨rfl, fun _ => rfl, shift_adjoint_apply 𝕜 x⟩

/-- Compatibility with the accepted scalar ℓᵖ operators, with no change of norm. -/
theorem shift_complex_identification : Spec.ShiftComplexIdentification := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext; funext n
    cases n <;> rfl
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext; funext n
    exact shift_adjoint_apply ℂ x n

@[simp] theorem shift_adjoint_shift (𝕜 : Type u) [RCLike 𝕜] (x : SequenceHilbert 𝕜) :
    (unilateralShift 𝕜).adjoint (unilateralShift 𝕜 x) = x := by
  apply lp.ext; funext n
  simp

theorem shift_norm (𝕜 : Type u) [RCLike 𝕜] (x : SequenceHilbert 𝕜) :
    ‖unilateralShift 𝕜 x‖ = ‖x‖ := by
  have hs : Summable (fun n => ‖Spec.shiftSequence x n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp (unilateralShift 𝕜 x)).summable (by norm_num)
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  change (∑' n, ‖Spec.shiftSequence x n‖ ^ (2 : ℝ≥0∞).toReal) = _
  rw [hs.tsum_eq_zero_add]
  simp [Spec.shiftSequence]

theorem shift_pow_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (x : SequenceHilbert 𝕜) :
    ‖(unilateralShift 𝕜 ^ n) x‖ = ‖x‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, shift_norm, ih]

@[simp] theorem adjoint_pow (T : H →L[𝕜] H) [CompleteSpace H] (n : ℕ) :
    (T ^ n).adjoint = T.adjoint ^ n := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using star_pow T n

theorem backward_pow_apply (𝕜 : Type u) [RCLike 𝕜]
    (n : ℕ) (x : SequenceHilbert 𝕜) (k : ℕ) :
    ((unilateralShift 𝕜).adjoint ^ n) x k = x (k + n) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, shift_adjoint_apply, ih]
    exact congrArg (fun k : ℕ => x k) (by omega)

theorem shift_pow_product (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ((unilateralShift 𝕜).adjoint ^ n).comp (unilateralShift 𝕜 ^ n) =
      ContinuousLinearMap.id 𝕜 (SequenceHilbert 𝕜) := by
  ext x
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ (unilateralShift 𝕜).adjoint, pow_succ' (unilateralShift 𝕜),
      ContinuousLinearMap.comp_apply, mul_apply_eq_comp,
      shift_adjoint_shift] at *
    exact ih

/-- The squared norm is the tail of a summable nonnegative series. -/
theorem backward_strong (𝕜 : Type u) [RCLike 𝕜] :
    Tendsto (fun n : ℕ => (unilateralShift 𝕜).adjoint ^ n) atTop
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 _ _) 0) := by
  apply (strong_tendsto_iff 𝕜 _ _ _ _ _ _).mpr
  intro x
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs (n : ℕ) : ‖((unilateralShift 𝕜).adjoint ^ n) x‖ ^ 2 =
      ∑' k, ‖x (k + n)‖ ^ 2 := by
    simpa only [backward_pow_apply, ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
        (((unilateralShift 𝕜).adjoint ^ n) x)
  have ht : Tendsto (fun n => ‖((unilateralShift 𝕜).adjoint ^ n) x‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) :=
    (tendsto_sum_nat_add (fun k => ‖x k‖ ^ 2)).congr fun n => (hs n).symm
  have ht' := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht'

/-- SOT convergence implies WOT convergence with the original norm dual. -/
theorem weak_of_strong {α : Type*} {l : Filter α} {f : α → H →L[𝕜] H}
    {T : H →L[𝕜] H}
    (h : Tendsto f l (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 H H) T)) :
    Tendsto f l (@nhds _ (OperatorTopology.Spec.WeakTopologyValue 𝕜 H H) T) := by
  apply (weak_tendsto_iff 𝕜 H H _ _ _ _).mpr
  intro x g
  exact g.continuous.continuousAt.tendsto.comp
    ((strong_tendsto_iff 𝕜 H H _ _ _ _).mp h x)

theorem forward_weak (𝕜 : Type u) [RCLike 𝕜] :
    Tendsto (fun n : ℕ => unilateralShift 𝕜 ^ n) atTop
      (@nhds _ (OperatorTopology.Spec.WeakTopologyValue 𝕜 _ _) 0) := by
  apply (hilbert_tendsto_iff 𝕜 _ _ _ _ _ _).mpr
  intro x y
  have hy := (strong_tendsto_iff 𝕜 _ _ _ _ _ _).mp (backward_strong 𝕜) y
  have hi := hy.inner (𝕜 := 𝕜) (tendsto_const_nhds (x := x))
  simpa only [← adjoint_pow, ContinuousLinearMap.adjoint_inner_left, inner_zero_left,
    zero_apply, inner_zero_right] using hi

theorem forward_not_strong (𝕜 : Type u) [RCLike 𝕜] :
    ¬ Tendsto (fun n : ℕ => unilateralShift 𝕜 ^ n) atTop
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 _ _) 0) := by
  intro h
  let e : SequenceHilbert 𝕜 := lp.single 2 0 1
  have hn := ((strong_tendsto_iff 𝕜 _ _ _ _ _ _).mp h e).norm
  simp only [shift_pow_norm, zero_apply, norm_zero] at hn
  have he : ‖e‖ = 1 := by simp [e, lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]
  rw [he] at hn
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
  norm_num at this

theorem shift_product_not_weak (𝕜 : Type u) [RCLike 𝕜] :
    ¬ Tendsto (fun n : ℕ => ((unilateralShift 𝕜).adjoint ^ n).comp
      (unilateralShift 𝕜 ^ n)) atTop
      (@nhds _ (OperatorTopology.Spec.WeakTopologyValue 𝕜 _ _) 0) := by
  intro h
  let e : SequenceHilbert 𝕜 := lp.single 2 0 1
  have hi := (hilbert_tendsto_iff 𝕜 _ _ _ _ _ _).mp h e e
  have hi' : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 (0 : 𝕜)) := by
    simpa only [shift_pow_product, ContinuousLinearMap.id_apply,
      zero_apply, inner_zero_right, e, lp.inner_single_left,
      lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞)), inner_self_eq_norm_sq_to_K, norm_one, one_pow,
      RCLike.ofReal_one] using hi
  have : (1 : 𝕜) = 0 := tendsto_nhds_unique tendsto_const_nhds hi'
  exact one_ne_zero this

theorem shift_limits : Spec.ShiftLimits.{u} := by
  intro 𝕜 _
  exact ⟨forward_weak 𝕜, weak_of_strong (backward_strong 𝕜), backward_strong 𝕜,
    forward_not_strong 𝕜, shift_pow_product 𝕜, shift_product_not_weak 𝕜⟩

theorem weak_composition_not_continuous : Spec.WeakCompositionNotContinuous.{u} := by
  intro 𝕜 _ hcont
  have hT := weak_of_strong (backward_strong 𝕜)
  have hS := forward_weak 𝕜
  let := OperatorTopology.Spec.WeakTopologyValue 𝕜 (SequenceHilbert 𝕜) (SequenceHilbert 𝕜)
  have hc := hcont.tendsto (0, 0) |>.comp (hT.prodMk_nhds hS)
  apply shift_product_not_weak 𝕜
  simpa only [Function.comp_def, ContinuousLinearMap.zero_comp] using hc

theorem adjoint_sot_not_continuous : Spec.AdjointSOTNotContinuous.{u} := by
  intro 𝕜 _ hcont
  have hb := backward_strong 𝕜
  let := OperatorTopology.Spec.StrongTopologyValue 𝕜 (SequenceHilbert 𝕜) (SequenceHilbert 𝕜)
  have hc := hcont.tendsto 0 |>.comp hb
  apply forward_not_strong 𝕜
  simpa only [Function.comp_def, adjoint_pow, ContinuousLinearMap.adjoint_adjoint,
    map_zero] using hc

end ExpandedFA.OperatorTopology.Boundaries
