import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology
namespace P102.Fractional

variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
variable {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}

/-- Independence of representatives for the original double integral. -/
theorem energy_congr {u v : Domain d → 𝕜} (h : u =ᵐ[domainMeasure G] v) :
    energy G s p u = energy G s p v := by
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  apply lintegral_congr_ae
  filter_upwards [h] with y hy
  simp only [hx, hy]

theorem kernel_measurable : Measurable (kernel d s p) := by
  unfold kernel
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
  fun_prop

theorem increment_aestronglyMeasurable_prod {u : Domain d → 𝕜}
    (hu : AEStronglyMeasurable u (domainMeasure G)) :
    AEStronglyMeasurable (increment u) ((domainMeasure G).prod (domainMeasure G)) :=
  (hu.comp_quasiMeasurePreserving quasiMeasurePreserving_fst).sub
    (hu.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)

theorem increment_aestronglyMeasurable {u : Domain d → 𝕜}
    (hu : AEStronglyMeasurable u (domainMeasure G)) :
    AEStronglyMeasurable (increment u) (pairMeasure G s p) :=
  (increment_aestronglyMeasurable_prod hu).mono_ac (withDensity_absolutelyContinuous _ _)

/-- This is the exact bridge between the weighted Lp construction and the
original iterated integral, including the assigned diagonal value. -/
theorem integral_increment_eq_energy {u : Domain d → 𝕜}
    (hu : AEStronglyMeasurable u (domainMeasure G)) :
    (∫⁻ z, ‖increment u z‖ₑ ^ p.toReal ∂pairMeasure G s p) = energy G s p u := by
  rw [pairMeasure, lintegral_withDensity_eq_lintegral_mul₀
    kernel_measurable.aemeasurable
    ((increment_aestronglyMeasurable_prod hu).enorm.pow_const _)]
  rw [lintegral_prod _ (kernel_measurable.aemeasurable.mul
    ((increment_aestronglyMeasurable_prod hu).enorm.pow_const _))]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  simp only [Pi.mul_apply, kernel, increment]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- The weighted Lp norm is exactly the Gagliardo seminorm. -/
theorem eLpNorm_increment_eq_seminorm {u : Domain d → 𝕜}
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) (hu : AEStronglyMeasurable u (domainMeasure G)) :
    eLpNorm (increment u) p (pairMeasure G s p) = seminorm G s p u := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (increment_aestronglyMeasurable hu),
    integral_increment_eq_energy hu]
  rfl

/-- Finiteness in the graph is precisely finiteness of the original integral. -/
theorem memLp_increment_iff {u : Domain d → 𝕜} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hu : AEStronglyMeasurable u (domainMeasure G)) :
    MemLp (increment u) p (pairMeasure G s p) ↔ energy G s p u < ∞ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt
    (increment_aestronglyMeasurable hu), integral_increment_eq_energy hu]

/-- The graph is closed: extract a pointwise a.e. subsequence from the first
Lp limit, then a further subsequence from the second. Absolute continuity of
the weighted pair measure carries the first limit to almost every pair. -/
theorem graph_isClosed [Fact (1 ≤ p)] : IsClosed (graph 𝕜 G s p : Set (Ambient d 𝕜 G s p)) := by
  apply IsSeqClosed.isClosed
  intro f z hf hz
  have hu : Tendsto (fun i => (f i).fst) atTop (𝓝 z.fst) :=
    ((WithLp.continuous_fst 1 _ _).tendsto z).comp hz
  have hv : Tendsto (fun i => (f i).snd) atTop (𝓝 z.snd) :=
    ((WithLp.continuous_snd 1 _ _).tendsto z).comp hz
  obtain ⟨n, hn, hnu⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  obtain ⟨m, hm, hmv⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hv.comp hn.tendsto_atTop)).exists_seq_tendsto_ae
  have hi : ∀ᵐ q ∂pairMeasure G s p,
      Tendsto (fun k => increment ((f (n (m k))).fst : Domain d → 𝕜) q)
        atTop (𝓝 (increment (z.fst : Domain d → 𝕜) q)) := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [quasiMeasurePreserving_fst.ae hnu,
      quasiMeasurePreserving_snd.ae hnu] with q hq1 hq2
    exact (hq1.comp hm.tendsto_atTop).sub (hq2.comp hm.tendsto_atTop)
  have heq : ∀ᵐ q ∂pairMeasure G s p, ∀ k,
      (f (n (m k))).snd q = increment ((f (n (m k))).fst : Domain d → 𝕜) q :=
    ae_all_iff.mpr (fun k => hf (n (m k)))
  filter_upwards [hi, hmv, heq] with q hqi hqv hqe
  exact tendsto_nhds_unique hqv (hqi.congr' (Eventually.of_forall fun k => (hqe k).symm))

/-- Banach completeness for the stated sum norm. -/
instance spaceCompleteSpace [Fact (1 ≤ p)] : CompleteSpace (Space 𝕜 G s p) :=
  graph_isClosed.isComplete.completeSpace_coe

/-- The graph realization has exactly one point above each underlying class. -/
theorem firstProjection_injective [Fact (1 ≤ p)] :
    Function.Injective (@firstProjection d 𝕜 _ G s p _) := by
  intro u v huv
  apply Subtype.ext
  apply (WithLp.ofLp_injective 1)
  apply Prod.ext
  · exact huv
  · apply Lp.ext
    have hu : (u.val.snd : (Domain d × Domain d) → 𝕜) =ᵐ[pairMeasure G s p]
      increment (u.val.fst : Domain d → 𝕜) := u.property
    have hv : (v.val.snd : (Domain d × Domain d) → 𝕜) =ᵐ[pairMeasure G s p]
      increment (v.val.fst : Domain d → 𝕜) := v.property
    change u.val.fst = v.val.fst at huv
    rw [huv] at hu
    exact hu.trans hv.symm

/-- Every finite-energy Lp class, and only such a class, is represented in W. -/
theorem firstProjection_range [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (u : Lp 𝕜 p (domainMeasure G)) :
    (∃ v : Space 𝕜 G s p, firstProjection v = u) ↔ energy G s p u < ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  constructor
  · rintro ⟨v, rfl⟩
    apply (memLp_increment_iff hp0 hpt (Lp.aestronglyMeasurable _)).mp
    exact (memLp_congr_ae v.property).mp (Lp.memLp v.val.snd)
  · intro hu
    have hi := (memLp_increment_iff hp0 hpt (Lp.aestronglyMeasurable u)).mpr hu
    exact ⟨⟨WithLp.toLp 1 (u, hi.toLp (increment u)), hi.coeFn_toLp⟩, rfl⟩

/-- Membership may equivalently be tested with the finite seminorm, exactly
as in the source definition. -/
theorem firstProjection_range_seminorm [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (u : Lp 𝕜 p (domainMeasure G)) :
    (∃ v : Space 𝕜 G s p, firstProjection v = u) ↔ seminorm G s p u < ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  rw [firstProjection_range hpt]
  rw [← eLpNorm_increment_eq_seminorm hp0 hpt (Lp.aestronglyMeasurable u)]
  exact (memLp_increment_iff hp0 hpt (Lp.aestronglyMeasurable u)).symm

theorem seminorm_congr {u v : Domain d → 𝕜} (h : u =ᵐ[domainMeasure G] v) :
    seminorm G s p u = seminorm G s p v := by
  unfold seminorm
  rw [energy_congr h]

/-- The inherited norm is the manuscript's exact sum norm. -/
theorem space_norm [Fact (1 ≤ p)] (hpt : p ≠ ∞) (u : Space 𝕜 G s p) :
    ‖u‖ = ‖firstProjection u‖ + (seminorm G s p (firstProjection u)).toReal := by
  change ‖u.val‖ = _
  rw [WithLp.prod_norm_eq_of_L1, Lp.norm_def u.val.snd,
    eLpNorm_congr_ae u.property,
    eLpNorm_increment_eq_seminorm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpt
      (Lp.aestronglyMeasurable _)]
  rfl

/-- Empty open domains give the zero space. -/
theorem space_empty_subsingleton [Fact (1 ≤ p)] :
    Subsingleton (Space 𝕜 (∅ : Set (Domain d)) s p) := by
  constructor
  intro u v
  apply firstProjection_injective
  apply Lp.ext
  simp [domainMeasure, Filter.EventuallyEq]

end P102.Fractional

namespace P102.Fractional

/-- The definition bindings expose the shared canonical objects. -/
def gagliardoEnergy : Specs.P102.Fractional.energyType := @energy
def gagliardoSeminorm : Specs.P102.Fractional.seminormType := @seminorm
def gagliardoSpace : Specs.P102.Fractional.spaceType := @Space

end P102.Fractional
