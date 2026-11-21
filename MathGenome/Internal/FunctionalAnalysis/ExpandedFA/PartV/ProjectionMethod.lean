import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ProjectionMethod
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
The discrete inverse is bounded by finite dimension, including dimension zero.
It fixes trial vectors after composition with A. Subtracting a trial vector
therefore gives the estimate, and taking the infimum gives the exact constant.
Uniform boundedness proves necessity on the Banach domain. No bound on the
data-to-solution maps is inferred from a bound on their compositions with A.
-/

open Filter
open scoped Topology

noncomputable section

namespace ExpandedFA.PartV.ProjectionMethod

universe u v w

variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

/-- Operator norms are unchanged by the isometric subspace inclusion, also
for the zero subspace (whose inclusion has norm zero, not one). -/
theorem norm_subtype_comp (V : Submodule 𝕜 X) (T : Y →L[𝕜] V) :
    ‖V.subtypeL.comp T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro y
    exact T.le_opNorm y
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (V.subtypeL.comp T))
    intro y
    exact (V.subtypeL.comp T).le_opNorm y

theorem norm_identification : Spec.NormIdentification := by
  intro 𝕜 X Y _ _ _ _ _ S A n h
  classical
  simp only [dataMap, exactMap, dite_eq_left h, ContinuousLinearMap.comp_assoc]
  exact ⟨norm_subtype_comp _ _, norm_subtype_comp _ _⟩

theorem discrete_solution : Spec.DiscreteSolution := by
  intro 𝕜 X Y _ _ _ _ _ S A n h f
  classical
  let e := discreteEquiv S A n h
  have hd : dataMap S A n f = ((e.symm (S.projection n f) : S.trial n) : X) := by
    simp only [dataMap, dite_eq_left h, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, Submodule.subtypeL_apply, e]
  have he (v : S.trial n) : e v = S.projection n (A v) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hd]
    exact (e.symm (S.projection n f)).property
  · rw [hd, ← he, e.apply_symm_apply]
  · intro v hv
    rw [hd]
    apply congrArg Subtype.val
    apply e.injective
    rw [e.apply_symm_apply]
    exact hv

theorem dataMap_mem (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ) (f : Y) :
    dataMap S A n f ∈ S.trial n := by
  classical
  by_cases h : Function.Bijective (discreteMap S A n)
  · exact (discrete_solution 𝕜 X Y S A n h f).1
  · simp [dataMap, h]

theorem zero_dimensional_stages : Spec.ZeroDimensionalStages := by
  intro 𝕜 X Y _ _ _ _ _ S A n hz
  have : Subsingleton (S.trial n) := Module.finrank_zero_iff.mp hz
  have : Subsingleton (S.test n) :=
    Module.finrank_zero_iff.mp ((S.equal_dimension n).symm.trans hz)
  have hinv : Function.Bijective (discreteMap S A n) :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩
  have hd : dataMap S A n = 0 := by
    ext f
    have hmem := dataMap_mem S A n f
    rw [Submodule.finrank_eq_zero.mp hz] at hmem
    exact hmem
  exact ⟨hinv, hd, by simp [exactMap, hd]⟩

/-- The exact-data operator is the identity on the current trial space. -/
theorem exactMap_eq_self (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ)
    (h : Function.Bijective (discreteMap S A n)) {v : X} (hv : v ∈ S.trial n) :
    exactMap S A n v = v := by
  exact ((discrete_solution 𝕜 X Y S A n h (A v)).2.2 ⟨v, hv⟩ rfl).symm

theorem best_approximation : Spec.BestApproximation := by
  intro 𝕜 X Y _ _ _ _ _ S A n h M hM hbound x
  have hC : 0 < 1 + M := by linarith
  have hpoint (v : X) (hv : v ∈ S.trial n) :
      ‖exactMap S A n x - x‖ ≤ (1 + M) * dist x v := by
    have hid : exactMap S A n x - x = exactMap S A n (x - v) - (x - v) := by
      rw [map_sub, exactMap_eq_self S A n h hv]
      abel
    calc
      ‖exactMap S A n x - x‖ = ‖exactMap S A n (x - v) - (x - v)‖ := congrArg norm hid
      _ ≤ ‖exactMap S A n (x - v)‖ + ‖x - v‖ := norm_sub_le _ _
      _ ≤ M * ‖x - v‖ + ‖x - v‖ :=
        add_le_add ((exactMap S A n).le_of_opNorm_le hbound _) le_rfl
      _ = (1 + M) * dist x v := by rw [dist_eq_norm]; ring
  have hinf : ‖exactMap S A n x - x‖ / (1 + M) ≤
      Metric.infDist x (S.trial n : Set X) := by
    apply (Metric.le_infDist ⟨0, (S.trial n).zero_mem⟩).2
    intro v hv
    exact (div_le_iff₀ hC).2 (by simpa [mul_comm] using hpoint v hv)
  exact (div_le_iff₀ hC).1 hinf |>.trans_eq (mul_comm _ _)

theorem projection_criterion : Spec.ProjectionCriterion := by
  intro 𝕜 X Y _ _ _ _ _ _ _ S A _ happrox N hinv
  constructor
  · intro hconv
    have hpoint : ∀ x : X, ∃ C : ℝ, ∀ n : ℕ, ‖exactMap S A n x‖ ≤ C := by
      intro x
      obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1
        (Metric.isBounded_range_of_tendsto (fun n => exactMap S A n x) (hconv x))
      exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩
    obtain ⟨M, hM, hbound⟩ :=
      ExpandedFA.P1.C07UniformBoundedness.uniform_boundedness
        𝕜 X X ℕ (exactMap S A) hpoint
    exact ⟨M, hM, fun n _ => hbound n⟩
  · rintro ⟨M, hM, hbound⟩ x
    have herr : ∀ᶠ n in atTop, ‖exactMap S A n x - x‖ ≤
        (1 + M) * Metric.infDist x (S.trial n : Set X) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact best_approximation 𝕜 X Y S A n (hinv n hn) M hM (hbound n hn) x
    have hz : Tendsto (fun n => (1 + M) * Metric.infDist x (S.trial n : Set X))
        atTop (𝓝 0) := by
      simpa using (happrox x).const_mul (1 + M)
    have hnorm : Tendsto (fun n => ‖exactMap S A n x - x‖) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) herr hz
    exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm

theorem supremum_best_approximation : Spec.SupremumBestApproximation := by
  intro 𝕜 X Y _ _ _ _ _ S A N hinv hbound
  obtain ⟨M, _, hM⟩ := hbound
  have hb : BddAbove (Set.range fun n : {n : ℕ // N ≤ n} => ‖exactMap S A n‖) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hM n n.property
  have hle (n : ℕ) (hn : N ≤ n) : ‖exactMap S A n‖ ≤ tailNormSup S A N :=
    le_csSup hb (Set.mem_range.mpr ⟨⟨n, hn⟩, rfl⟩)
  have hnonneg : 0 ≤ tailNormSup S A N := (norm_nonneg _).trans (hle N le_rfl)
  exact ⟨hnonneg, fun n hn =>
    best_approximation 𝕜 X Y S A n (hinv n hn) _ hnonneg (hle n hn)⟩

theorem noisy_data_stability : Spec.NoisyDataStability := by
  intro 𝕜 X Y _ _ _ _ _ S A N
  constructor
  · rintro ⟨L, hL, hb⟩
    refine ⟨L, hL, fun n hn f g => ?_⟩
    rw [← map_sub]
    exact (dataMap S A n).le_of_opNorm_le (hb n hn) _
  · rintro ⟨L, hL, hb⟩
    refine ⟨L, hL, fun n hn => ?_⟩
    apply ContinuousLinearMap.opNorm_le_bound _ hL
    intro f
    simpa only [map_zero, sub_zero] using hb n hn f 0

theorem noisy_error_estimate : Spec.NoisyErrorEstimate := by
  intro 𝕜 X Y _ _ _ _ _ S A n hinv M L hM hbM _ hbL x f
  have herr := best_approximation 𝕜 X Y S A n hinv M hM hbM x
  have hnoise : ‖dataMap S A n f - dataMap S A n (A x)‖ ≤ L * ‖f - A x‖ := by
    rw [← map_sub]
    exact (dataMap S A n).le_of_opNorm_le hbL _
  calc
    ‖dataMap S A n f - x‖ ≤
        ‖dataMap S A n f - exactMap S A n x‖ + ‖exactMap S A n x - x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L * ‖f - A x‖ + (1 + M) * Metric.infDist x (S.trial n : Set X) :=
      add_le_add hnoise herr
    _ = _ := add_comm _ _

end ExpandedFA.PartV.ProjectionMethod
