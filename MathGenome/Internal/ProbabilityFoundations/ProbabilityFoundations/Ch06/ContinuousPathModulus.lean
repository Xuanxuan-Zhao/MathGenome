import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuousPathModulus
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.ContinuousPathGeometry
import Mathlib.Tactic.Linarith

open Filter Topology

namespace ProbabilityFoundations.Ch06

noncomputable def pathModulus : Specs.PathModulus := @Specs.modulus

open Specs

private theorem increments_bdd {T : ℝ} {d : ℕ} (x : Specs.Path T d) (δ : ℝ) :
    BddAbove (increments x δ) := by
  refine ⟨2 * ‖x‖, ?_⟩
  rintro r ⟨s, t, _, rfl⟩
  simpa only [dist_eq_norm] using x.dist_le_two_norm s t

private theorem increments_nonempty {T : ℝ} (hT : 0 < T) {d : ℕ}
    (x : Specs.Path T d) {δ : ℝ} (hδ : 0 ≤ δ) : (increments x δ).Nonempty := by
  let t : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  exact ⟨0, t, t, by simpa using hδ, by simp⟩

theorem modulus_finite : Specs.ModulusFinite := by
  intro T hT d x δ hδ
  have hz : 0 ∈ increments x δ := by
    let t : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
    exact ⟨t, t, by simpa using hδ, by simp⟩
  refine ⟨increments_bdd x δ, le_csSup (increments_bdd x δ) hz,
    csSup_le (increments_nonempty hT x hδ) ?_, ?_⟩
  · rintro r ⟨s, t, _, rfl⟩
    simpa only [dist_eq_norm] using x.dist_le_two_norm s t
  · intro s t hst
    exact le_csSup (increments_bdd x δ) ⟨s, t, hst, rfl⟩

private theorem modulus_le_add {T : ℝ} (hT : 0 < T) {d : ℕ}
    {δ : ℝ} (hδ : 0 ≤ δ) (x y : Specs.Path T d) :
    modulus x δ ≤ modulus y δ + 2 * ‖x - y‖ := by
  apply csSup_le (increments_nonempty hT x hδ)
  rintro r ⟨s, t, hst, rfl⟩
  have hs := ContinuousMap.dist_apply_le_dist (f := x) (g := y) s
  have ht := ContinuousMap.dist_apply_le_dist (f := x) (g := y) t
  have hy := (modulus_finite T hT d y δ hδ).2.2.2 s t hst
  have htri := dist_triangle4 (x s) (y s) (y t) (x t)
  rw [dist_comm (y t) (x t)] at htri
  simp only [dist_eq_norm] at hs ht htri
  linarith

theorem modulus_lipschitz : Specs.ModulusLipschitz := by
  intro T hT d δ hδ x y
  apply abs_le.mpr
  have hxy := modulus_le_add hT hδ x y
  have hyx := modulus_le_add hT hδ y x
  rw [norm_sub_rev y x] at hyx
  constructor <;> linarith

theorem modulus_continuous : Specs.ModulusContinuous := by
  intro T hT d δ hδ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, dist_eq_norm, NNReal.coe_ofNat, Real.norm_eq_abs] using
    modulus_lipschitz T hT d δ hδ x y

theorem modulus_events : Specs.ModulusEvents := by
  intro T hT d δ hδ η
  let : MeasurableSpace (Specs.Path T d) := borel _
  let : BorelSpace (Specs.Path T d) := ⟨rfl⟩
  have hc := (modulus_continuous T hT d δ hδ).continuous
  exact ⟨(isOpen_lt continuous_const hc).measurableSet, isClosed_le hc continuous_const⟩

theorem modulus_tendsto_zero : Specs.ModulusTendstoZero := by
  intro T hT d x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a, ha, h⟩ := Metric.uniformContinuous_iff_le.mp
    (CompactSpace.uniformContinuous_of_continuous x.continuous) (ε / 2) (by linarith)
  have hevent : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < a :=
    (eventually_lt_nhds ha).filter_mono inf_le_left
  filter_upwards [hevent, self_mem_nhdsWithin] with δ hδ hpos
  have hnonneg := (modulus_finite T hT d x δ (le_of_lt hpos)).2.1
  have hbound : modulus x δ ≤ ε / 2 := by
    apply csSup_le (increments_nonempty hT x (le_of_lt hpos))
    rintro r ⟨s, t, hst, rfl⟩
    have hdist : dist s t ≤ a := by
      simpa only [Subtype.dist_eq, Real.dist_eq] using hst.trans hδ.le
    simpa only [dist_eq_norm] using h hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

theorem zero_dimensional_modulus : Specs.ZeroDimensionalModulus := by
  intro T hT x δ hδ
  apply le_antisymm _ (modulus_finite T hT 0 x δ hδ).2.1
  apply csSup_le (increments_nonempty hT x hδ)
  rintro r ⟨s, t, _, rfl⟩
  rw [Subsingleton.elim (x s) (x t), sub_self, norm_zero]

theorem pathSpace_geometry : Specs.PathSpaceGeometry := by
  intro T hT d
  exact ⟨Ch05.pathSpace_separable _ T hT, Ch05.pathSpace_complete _ T hT⟩

end ProbabilityFoundations.Ch06
