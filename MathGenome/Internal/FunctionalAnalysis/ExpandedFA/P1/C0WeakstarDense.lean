import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C0WeakstarDense
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06DoubleAnnihilator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals

/-! The c₀ weak-star-density example, using coordinate tests and double
annihilation. Uniform approximation proves norm closedness directly, and the
constant sequence one witnesses properness. -/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C0WeakstarDense
open C01SequenceSpaces
open ExpandedFA.FunctionSpaces.SequenceDuals

variable {𝕜 : Type u} [RCLike 𝕜]

@[simp] theorem l1Duality_mem_c0 (a : SequenceLInfinity 𝕜) :
    (l1Duality (𝕜 := 𝕜)) a ∈ c0L1DualSubmodule 𝕜 ↔ a ∈ sequenceC0Submodule 𝕜 := by
  change Tendsto (fun n => l1Pairing a (lp.single 1 n (1 : 𝕜))) atTop (𝓝 0) ↔ _
  simp only [l1Pairing_single]
  rfl

theorem c0_l1_dual_image (𝕜 : Type u) [RCLike 𝕜] :
    (sequenceC0Submodule 𝕜).map (l1Duality (𝕜 := 𝕜)).toLinearEquiv.toLinearMap =
      c0L1DualSubmodule 𝕜 := by
  ext f
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (l1Duality_mem_c0 a).mpr ha
  · intro hf
    refine ⟨(l1Duality (𝕜 := 𝕜)).symm f, ?_, (l1Duality (𝕜 := 𝕜)).apply_symm_apply f⟩
    exact (l1Duality_mem_c0 _).mp (by simpa using hf)

theorem c0_dual_coordinate_identification : Spec.CoordinateIdentification.{u} := by
  intro 𝕜 _
  exact ⟨l1Duality, (fun _ _ => rfl), (fun _ _ => rfl), c0_l1_dual_image 𝕜⟩

/-- A coordinate vector on the left recovers the matching coordinate of x. -/
theorem l1Pairing_coordinate_left (x : SequenceLp 𝕜 1) (j : ℕ) :
    l1Pairing (lp.single ∞ j (1 : 𝕜)) x = x j := by
  classical
  rw [l1Pairing_apply, tsum_eq_single j]
  · simp
  · intro n hn
    rw [lp.single_apply_ne _ _ _ hn, zero_mul]

theorem c0_preannihilator_zero : Spec.PreannihilatorZero.{u} := by
  intro 𝕜 _
  apply le_antisymm
  · intro x hx
    change x = 0
    apply lp.ext
    funext j
    change x j = 0
    let e := c0Coordinate 𝕜 j
    have hf : l1Pairing e.val ∈ c0L1DualSubmodule 𝕜 :=
      (l1Duality_mem_c0 e.val).mpr e.property
    have hz := hx (l1Pairing e.val) hf
    exact (l1Pairing_coordinate_left x j).symm.trans hz
  · exact bot_le

theorem c0_weakstar_dense : Spec.WeakStarDensity.{u} := by
  intro 𝕜 _
  have h := C06DoubleAnnihilator.double_annihilator_dual
    𝕜 (SequenceLp 𝕜 1) (c0L1DualSubmodule 𝕜)
  rw [c0_preannihilator_zero 𝕜] at h
  have hd : @closure (SequenceLp 𝕜 1 →L[𝕜] 𝕜) (l1WeakstarTopology 𝕜)
      (c0L1DualSubmodule 𝕜 : Set (SequenceLp 𝕜 1 →L[𝕜] 𝕜)) = Set.univ := by
    rw [← h]
    ext f
    change (∀ x, x ∈ (⊥ : Submodule 𝕜 (SequenceLp 𝕜 1)) → f x = 0) ↔ True
    simp
  refine ⟨hd, l1Duality, (fun _ _ => rfl), ?_⟩
  have hi : (l1Duality (𝕜 := 𝕜)) ''
      (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) =
      (c0L1DualSubmodule 𝕜 : Set (SequenceLp 𝕜 1 →L[𝕜] 𝕜)) :=
    congrArg (fun M : Submodule 𝕜 (SequenceLp 𝕜 1 →L[𝕜] 𝕜) =>
      (M : Set (SequenceLp 𝕜 1 →L[𝕜] 𝕜))) (c0_l1_dual_image 𝕜)
  apply Set.eq_univ_of_forall
  intro a
  apply (closure_induced (t := l1WeakstarTopology 𝕜)).mpr
  rw [hi, hd]
  trivial

/-- A supremum-norm limit of null sequences is again a null sequence. -/
theorem isClosed_sequenceC0 (𝕜 : Type u) [RCLike 𝕜] :
    IsClosed (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun n => x n) atTop (𝓝 0)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hcoord := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (x - y) n
  have htail := hN n hn
  rw [dist_eq_norm] at hxy
  simp only [dist_zero_right] at htail ⊢
  have hsum := norm_add_le (x n - y n) (y n)
  simp only [sub_add_cancel] at hsum
  change ‖x n - y n‖ ≤ ‖x - y‖ at hcoord
  linarith

theorem one_not_mem_sequenceC0 (𝕜 : Type u) [RCLike 𝕜] :
    (1 : SequenceLInfinity 𝕜) ∉ sequenceC0Submodule 𝕜 := by
  intro hm
  change Tendsto (fun n => (1 : SequenceLInfinity 𝕜) n) atTop (𝓝 0) at hm
  have ht : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 0) := by
    simpa only [lp.infty_coeFn_one, Pi.one_apply] using hm
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

theorem sequenceC0_proper (𝕜 : Type u) [RCLike 𝕜] : sequenceC0Submodule 𝕜 < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  apply one_not_mem_sequenceC0 𝕜
  rw [htop]
  trivial

theorem c0_norm_closed_proper : Spec.NormClosedProper.{u} := by
  intro 𝕜 _
  refine ⟨⟨isClosed_sequenceC0 𝕜, sequenceC0_proper 𝕜⟩, ?_, ?_⟩
  · have heq : (c0L1DualSubmodule 𝕜 : Set (SequenceLp 𝕜 1 →L[𝕜] 𝕜)) =
        (l1Duality (𝕜 := 𝕜)).symm ⁻¹'
          (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) := by
      ext f
      simpa using (l1Duality_mem_c0 ((l1Duality (𝕜 := 𝕜)).symm f))
    rw [heq]
    exact (isClosed_sequenceC0 𝕜).preimage (l1Duality (𝕜 := 𝕜)).symm.continuous
  · apply lt_top_iff_ne_top.mpr
    intro htop
    have hm : (l1Duality (𝕜 := 𝕜)) (1 : SequenceLInfinity 𝕜) ∈ c0L1DualSubmodule 𝕜 := by
      rw [htop]
      trivial
    exact one_not_mem_sequenceC0 𝕜 ((l1Duality_mem_c0 _).mp hm)

end ExpandedFA.P1.C0WeakstarDense
