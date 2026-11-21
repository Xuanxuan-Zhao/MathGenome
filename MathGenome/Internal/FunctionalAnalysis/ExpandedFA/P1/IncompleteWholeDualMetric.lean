import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.IncompleteWholeDualMetric
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Coordinate metrization of the whole dual of finite-support ℓ² sequences. -/

noncomputable section
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.IncompleteWholeDualMetric

theorem c00L2_realization : Spec.Realization.{u} := by
  intro 𝕜 _
  refine ⟨⟨?_, ?_⟩, fun _ _ => rfl,
    fun _ => rfl, ?_⟩
  · intro a b h
    apply Finsupp.ext
    intro n
    exact congrArg (fun x : C00L2 𝕜 => x.val n) h
  · intro x
    obtain ⟨a, ha⟩ := x.property
    exact ⟨a, Subtype.ext ha⟩
  · intro n j
    change (Finsupp.single n (1 : 𝕜)) j = _
    simp [Finsupp.single_apply, eq_comm]

theorem c00_dual_evaluation_formula : Spec.EvaluationFormula.{u} := by
  intro 𝕜 _ a f
  classical
  have ha : (∑ n ∈ a.support, a n • Finsupp.single n (1 : 𝕜)) = a := by
    simpa only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one] using a.sum_single
  calc
    f (c00L2Inclusion 𝕜 a) =
        f (c00L2Inclusion 𝕜 (∑ n ∈ a.support, a n • Finsupp.single n 1)) := by rw [ha]
    _ = _ := by
      change _ = ∑ n ∈ a.support, a n * f (c00L2Inclusion 𝕜 (Finsupp.single n 1))
      simp only [map_sum, map_smul, smul_eq_mul]

/-- Every vector of c₀₀ is the image of a finitely supported coefficient vector. -/
private theorem all_evaluations_continuous (𝕜 : Type u) [RCLike 𝕜] :
    let t := ⨅ n : ℕ, TopologicalSpace.induced
      (fun f : C00L2Dual 𝕜 => c00DualCoordinates 𝕜 f n) inferInstance
    ∀ x : C00L2 𝕜, @Continuous (C00L2Dual 𝕜) 𝕜 t inferInstance (fun f => f x) := by
  dsimp only
  let t := ⨅ n : ℕ, TopologicalSpace.induced
    (fun f : C00L2Dual 𝕜 => c00DualCoordinates 𝕜 f n) inferInstance
  let : TopologicalSpace (C00L2Dual 𝕜) := t
  have hc (n : ℕ) : Continuous (fun f : C00L2Dual 𝕜 => c00DualCoordinates 𝕜 f n) :=
    continuous_iff_le_induced.mpr (iInf_le _ n)
  intro x
  obtain ⟨a, rfl⟩ := (c00L2_realization 𝕜).1.2 x
  have heq : (fun f : C00L2Dual 𝕜 => f (c00L2Inclusion 𝕜 a)) =
      (fun f => ∑ n ∈ a.support, a n * c00DualCoordinates 𝕜 f n) :=
    funext fun f => c00_dual_evaluation_formula 𝕜 a f
  rw [heq]
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (hc n)

theorem c00_dual_coordinate_initial : Spec.CoordinateInitial.{u} := by
  intro 𝕜 _
  apply le_antisymm
  · rw [c00DualWeakStar, C12WeakStar.weakStarTopology_evaluations 𝕜 (C00L2 𝕜)]
    exact le_iInf fun n => iInf_le _ (c00L2Unit 𝕜 n)
  · exact (C12WeakStar.weakStarTopology_evaluation_coarsest 𝕜 (C00L2 𝕜) _).mp
      (all_evaluations_continuous 𝕜)

theorem c00_dual_coordinate_embedding : Spec.CoordinateEmbedding.{u} := by
  intro 𝕜 _
  let : TopologicalSpace (C00L2Dual 𝕜) := c00DualWeakStar 𝕜
  change Topology.IsEmbedding (c00DualCoordinates 𝕜)
  refine ⟨⟨?_⟩, ?_⟩
  · rw [induced_to_pi]
    exact c00_dual_coordinate_initial 𝕜
  · intro f g h
    apply ContinuousLinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := (c00L2_realization 𝕜).1.2 x
    rw [c00_dual_evaluation_formula 𝕜 a f, c00_dual_evaluation_formula 𝕜 a g]
    apply Finset.sum_congr rfl
    intro n _
    rw [congrFun h n]

theorem c00_whole_dual_metrizable : Spec.WholeDualMetrizable.{u} := by
  intro 𝕜 _
  let : TopologicalSpace (C00L2Dual 𝕜) := c00DualWeakStar 𝕜
  exact (c00_dual_coordinate_embedding 𝕜).metrizableSpace

/-- Coordinate vectors keep their unit ℓ² norms in the finite-support subspace. -/
theorem c00L2Unit_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ‖c00L2Unit 𝕜 n‖ = 1 := by
  change ‖C01SequenceSpaces.Spec.C00ToLpValue 𝕜 2 (Finsupp.single n 1)‖ = 1
  have hsingle : C01SequenceSpaces.Spec.C00ToLpValue 𝕜 2 (Finsupp.single n 1) =
      lp.single 2 n (1 : 𝕜) := by
    apply lp.ext
    funext j
    change (Finsupp.single n (1 : 𝕜)) j = (Pi.single n (1 : 𝕜) : ℕ → 𝕜) j
    by_cases hj : j = n <;> simp [hj, Pi.single]
  rw [hsingle, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact norm_one

/-- Absolute convergence of a geometric series of coordinate vectors would give
an element having infinitely many nonzero coordinates, which c₀₀ cannot contain. -/
theorem c00L2_incomplete_infiniteDimensional :
    Spec.IncompleteInfiniteDimensional.{u} := by
  intro 𝕜 _
  constructor
  · intro h
    let := h
    let := FiniteDimensional.of_injective (c00L2Inclusion 𝕜) (c00L2_realization 𝕜).1.1
    let : Finite ℕ := Module.Finite.finite_basis (Finsupp.basisSingleOne (R := 𝕜) (ι := ℕ))
    exact not_finite ℕ
  · intro h
    let := h
    let v : ℕ → C00L2 𝕜 := fun n => (1 / 2 : 𝕜) ^ n • c00L2Unit 𝕜 n
    have hv : Summable v := by
      apply Summable.of_norm
      simpa only [v, norm_smul, norm_pow, c00L2Unit_norm, mul_one, norm_div,
        norm_one, RCLike.norm_ofNat] using
        (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    let x : C00L2 𝕜 := ∑' n, v n
    have hx (n : ℕ) : x.val n = (1 / 2 : 𝕜) ^ n := by
      let ev : C00L2 𝕜 →L[𝕜] 𝕜 :=
        (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 n).comp
          (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 2).range.subtypeL
      change ev (∑' i, v i) = _
      rw [ev.map_tsum hv]
      have he (i : ℕ) : ev (v i) =
          (1 / 2 : 𝕜) ^ i * (if n = i then 1 else 0) := by
        change ((1 / 2 : 𝕜) ^ i • c00L2Unit 𝕜 i).val n = _
        change (1 / 2 : 𝕜) ^ i * (c00L2Unit 𝕜 i).val n = _
        rw [(c00L2_realization 𝕜).2.2.2]
      simp_rw [he]
      rw [tsum_eq_single n (fun i hi => by simp [Ne.symm hi])]
      simp
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset a.support
    have hz : x.val n = 0 := by
      rw [← ha]
      exact Finsupp.notMem_support_iff.mp hn
    exact (pow_ne_zero n (by norm_num : (1 / 2 : 𝕜) ≠ 0)) ((hx n).symm.trans hz)

end ExpandedFA.P1.IncompleteWholeDualMetric
