import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.FirstIntegrals
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.InnerTimeVariation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace VariationalNotes.Classical.FirstIntegrals
open InnerTime

@[simp] theorem momentumField_on_interval {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (t : I.Points) :
    momentumField L u t = momentum L u t := by
  simp [momentumField, momentum, stateField, velocityField, extendState, t.property]

@[simp] theorem stateGradientField_on_interval {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (t : I.Points) :
    stateGradientField L u t = stateGradient L u t := by
  simp [stateGradientField, stateGradient, stateField, velocityField, extendState, t.property]

theorem momentumField_pairing {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : ℝ) (w : State m) :
    inner ℝ (momentumField L u t) w =
      fderiv ℝ (fun v => L.value (t, stateField I m u t, v)) (velocityField I m u t) w :=
  InnerProductSpace.toDual_symm_apply

theorem stateGradientField_pairing {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : ℝ) (w : State m) :
    inner ℝ (stateGradientField L u t) w =
      fderiv ℝ (fun z => L.value (t, z, velocityField I m u t)) (stateField I m u t) w :=
  InnerProductSpace.toDual_symm_apply

theorem statePartial_eq_full {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : ℝ) (w : State m)
    (hL : DifferentiableAt ℝ L.value (t, stateField I m u t, velocityField I m u t)) :
    fderiv ℝ (fun z => L.value (t, z, velocityField I m u t)) (stateField I m u t) w =
      fderiv ℝ L.value (t, stateField I m u t, velocityField I m u t) (0, w, 0) := by
  have h := (hL.hasFDerivAt.comp (stateField I m u t)
    ((hasFDerivAt_const (𝕜 := ℝ) t (stateField I m u t)).prodMk
      ((hasFDerivAt_id (stateField I m u t)).prodMk
        (hasFDerivAt_const (velocityField I m u t) (stateField I m u t))))).fderiv
  exact congrArg (fun D => D w) h

theorem velocityPartial_apply_eq_full {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : ℝ) (w : State m)
    (hL : DifferentiableAt ℝ L.value (t, stateField I m u t, velocityField I m u t)) :
    fderiv ℝ (fun v => L.value (t, stateField I m u t, v)) (velocityField I m u t) w =
      fderiv ℝ L.value (t, stateField I m u t, velocityField I m u t) (0, 0, w) := by
  have h := (hL.hasFDerivAt.comp (velocityField I m u t)
    ((hasFDerivAt_const (𝕜 := ℝ) t (velocityField I m u t)).prodMk
      ((hasFDerivAt_const (stateField I m u t) (velocityField I m u t)).prodMk
        (hasFDerivAt_id (velocityField I m u t))))).fderiv
  exact congrArg (fun D => D w) h

theorem lagrangian_differentiable {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) (t : ℝ) (ht : t ∈ Icc I.a I.b) :
    DifferentiableAt ℝ L.value (t, stateField I m u t, velocityField I m u t) := by
  obtain ⟨U, hU, hg, _, hL⟩ := hreg
  have h := (hL.differentiableOn_one _ (hg ⟨t, ht⟩)).differentiableAt
    (hU.mem_nhds (hg ⟨t, ht⟩))
  simpa [graphPoint, stateField, velocityField, extendState, ht] using h

/-- C² of the state gives C¹ of the actual jet velocity, including endpoints. -/
theorem velocity_contDiffOn {I : Interval} {m : ℕ} (u : C1Curve I m)
    (h : ContDiffOn ℝ 2 (stateField I m u) (Icc I.a I.b)) :
    ContDiffOn ℝ 1 (velocityField I m u) (Icc I.a I.b) := by
  have hd : ContDiffOn ℝ 1 (derivWithin (stateField I m u) (Icc I.a I.b)) (Icc I.a I.b) :=
    h.derivWithin (uniqueDiffOn_Icc I.increasing) (by norm_num)
  apply hd.congr
  intro t ht
  have he := VariationSpaces.velocity_eq_derivWithin I m u ⟨t, ht⟩
  simpa [velocityField, extendState, ht] using he

theorem energy_derivative_C2 {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) (hel : EulerLagrange L u)
    (hu : ContDiffOn ℝ 2 (stateField I m u) (Icc I.a I.b))
    (t : ℝ) (ht : t ∈ Ioo I.a I.b) :
    HasDerivAt (energy L u) (timePartial L u t) t := by
  have hmem : Icc I.a I.b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hz : HasDerivAt (stateField I m u) (velocityField I m u t) t := by
    rw [show velocityField I m u t = u.velocity ⟨t, Ioo_subset_Icc_self ht⟩ by
      simp [velocityField, extendState, Ioo_subset_Icc_self ht]]
    exact (u.property ⟨t, Ioo_subset_Icc_self ht⟩).hasDerivAt hmem
  have hv := ((velocity_contDiffOn u hu).differentiableOn_one t
    (Ioo_subset_Icc_self ht)).differentiableAt hmem |>.hasDerivAt
  have hL := lagrangian_differentiable L u hreg t (Ioo_subset_Icc_self ht)
  have hg := (hasDerivAt_id t).prodMk (hz.prodMk hv)
  have hval := hL.hasFDerivAt.comp_hasDerivAt t hg
  have hpair := (hel.2 t ht).inner ℝ hv
  have hsub := hval.sub hpair
  have heq : (fun r => L.value (r, stateField I m u r, velocityField I m u r) -
      inner ℝ (momentumField L u r) (velocityField I m u r)) = energy L u := by
    funext r
    simp [energy, momentumField_pairing]
  change HasDerivAt (fun r => L.value (r, stateField I m u r, velocityField I m u r) -
    inner ℝ (momentumField L u r) (velocityField I m u r)) _ t at hsub
  rw [heq] at hsub
  convert hsub using 1
  let D := fderiv ℝ L.value (t, stateField I m u t, velocityField I m u t)
  have hvect : ((1 : ℝ), velocityField I m u t, deriv (velocityField I m u) t) =
      (1, (0 : State m), (0 : State m)) + (0, velocityField I m u t, 0) +
      (0, 0, deriv (velocityField I m u) t) := by ext <;> simp
  rw [timePartial_eq_full L u t hL, stateGradientField_pairing,
    statePartial_eq_full L u t _ hL, momentumField_pairing,
    velocityPartial_apply_eq_full L u t _ hL]
  change D (1, 0, 0) = D (1, velocityField I m u t, deriv (velocityField I m u) t) -
    (D (0, 0, deriv (velocityField I m u) t) + D (0, velocityField I m u t, 0))
  rw [hvect, map_add, map_add]
  ring

theorem energyIdentity : Specs.VariationalNotes.Classical.FirstIntegrals.energyIdentity := by
  intro I m L u hreg hel hbranch
  rcases hbranch with hu | hs
  · exact InnerTime.closedIntervalRegularity I.increasing (energy L u) (timePartial L u)
      (InnerTime.fieldsContinuous I m L u hreg).1
      (InnerTime.fieldsContinuous I m L u hreg).2
      (energy_derivative_C2 L u hreg hel hu)
  · exact InnerTime.energyRegularity I m L u hreg hs

/-- The canonical energy is exactly L - p · u′, also for the ambient field representation. -/
theorem energy_eq_pairing {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : ℝ) :
    energy L u t = L.value (t, stateField I m u t, velocityField I m u t) -
      inner ℝ (momentumField L u t) (velocityField I m u t) := by
  simp [energy, momentumField_pairing]

theorem graph_mem_domain {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) (t : ℝ) (ht : t ∈ Icc I.a I.b) :
    (t, stateField I m u t, velocityField I m u t) ∈ L.domain := by
  obtain ⟨U, _, hg, hUd, _⟩ := hreg
  simpa [graphPoint, stateField, velocityField, extendState, ht] using hUd (hg ⟨t, ht⟩)

theorem autonomous_timePartial_zero {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) (ha : Autonomous L)
    (t : ℝ) (ht : t ∈ Icc I.a I.b) : timePartial L u t = 0 := by
  have hx := graph_mem_domain L u hreg t ht
  have hnear : ∀ᶠ r in 𝓝 t,
      (r, stateField I m u t, velocityField I m u t) ∈ L.domain :=
    (L.isOpen_domain.preimage
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))).mem_nhds hx
  have hd : HasDerivAt
      (fun r => L.value (r, stateField I m u t, velocityField I m u t)) 0 t :=
    (hasDerivAt_const t (L.value (t, stateField I m u t, velocityField I m u t))).congr_of_eventuallyEq
      (hnear.mono (fun r hr => ha t r _ _ hx hr))
  exact hd.deriv

theorem autonomousEnergyConstant :
    Specs.VariationalNotes.Classical.FirstIntegrals.autonomousEnergyConstant := by
  intro I m L u hreg hel hbranch ha
  have he := energyIdentity I m L u hreg hel hbranch
  apply constant_of_derivWithin_zero (he.1.differentiableOn_one)
  intro t ht
  rw [(he.2.1 t (Ico_subset_Icc_self ht)).derivWithin
    (uniqueDiffOn_Icc I.increasing t (Ico_subset_Icc_self ht))]
  exact autonomous_timePartial_zero L u hreg ha t (Ico_subset_Icc_self ht)

/-- Independence of a state coordinate forces that coordinate of L_z to vanish. -/
theorem ignorable_stateGradient_zero {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) (i : Fin m)
    (hi : IgnorableCoordinate L i) (t : ℝ) (ht : t ∈ Icc I.a I.b) :
    stateGradientField L u t i = 0 := by
  let e : State m := EuclideanSpace.single i 1
  let z := stateField I m u t
  let v := velocityField I m u t
  have hx : (t, z, v) ∈ L.domain := graph_mem_domain L u hreg t ht
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), (t, z + s • e, v) ∈ L.domain := by
    have hc : Continuous (fun s : ℝ => (t, z + s • e, v)) :=
      continuous_const.prodMk ((continuous_const.add
        (continuous_id.smul continuous_const)).prodMk continuous_const)
    apply (L.isOpen_domain.preimage hc).mem_nhds
    simpa using hx
  have hzero : HasDerivAt (fun s : ℝ => L.value (t, z + s • e, v)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (L.value (t, z, v))).congr_of_eventuallyEq
      (hnear.mono (fun s hs => hi t z v s hx hs))
  have hz : HasDerivAt (fun s : ℝ => z + s • e) e 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have hg : HasDerivAt (fun s : ℝ => (t, z + s • e, v)) (0, e, 0) 0 :=
    (hasDerivAt_const (0 : ℝ) t).prodMk (hz.prodMk (hasDerivAt_const (0 : ℝ) v))
  have hd := lagrangian_differentiable L u hreg t ht
  have hd0 : DifferentiableAt ℝ L.value (t, z + (0 : ℝ) • e, v) := by
    simpa [z, v] using hd
  have hchain := hd0.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
  simp only [zero_smul, add_zero] at hchain
  have heq : fderiv ℝ L.value (t, z, v) (0, e, 0) = 0 := hchain.unique hzero
  rw [← statePartial_eq_full L u t e hd, ← stateGradientField_pairing] at heq
  simpa [e, EuclideanSpace.inner_single_right] using heq

theorem ignorableMomentumConstant :
    Specs.VariationalNotes.Classical.FirstIntegrals.ignorableMomentumConstant := by
  intro I m L u hreg hel i hi
  have hp : ContinuousOn (fun t => momentumField L u t i) (Icc I.a I.b) :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn hel.1.continuousOn
  have hd : ∀ t ∈ Ioo I.a I.b, HasDerivAt (fun t => momentumField L u t i) 0 t := by
    intro t ht
    have h := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t (hel.2 t ht)
    change HasDerivAt (fun t => momentumField L u t i) (stateGradientField L u t i) t at h
    rw [ignorable_stateGradient_zero L u hreg i hi t (Ioo_subset_Icc_self ht)] at h
    exact h
  have hr := InnerTime.closedIntervalRegularity I.increasing
    (fun t => momentumField L u t i) (fun _ => 0) hp continuousOn_const hd
  apply constant_of_derivWithin_zero hr.1.differentiableOn_one
  intro t ht
  exact (hr.2.1 t (Ico_subset_Icc_self ht)).derivWithin
    (uniqueDiffOn_Icc I.increasing t (Ico_subset_Icc_self ht))

end VariationalNotes.Classical.FirstIntegrals
