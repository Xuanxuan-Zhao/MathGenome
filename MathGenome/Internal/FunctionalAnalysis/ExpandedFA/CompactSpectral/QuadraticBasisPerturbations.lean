import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.QuadraticBasisPerturbations
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.OrthonormalExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NeumannResolvent
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr

noncomputable section
open scoped InnerProductSpace lp
open Filter Topology

namespace ExpandedFA.CompactSpectral.QuadraticBasisPerturbations
universe u v w
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {ι : Type w} {e : ι → H}

/-- Cauchy--Schwarz and Bessel give a bound uniform over finite subsets. -/
lemma finite_coefficient_bound (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) (x : H) (s : Finset ι) :
    ∑ i ∈ s, ‖⟪e i, x⟫_𝕜 • d i‖ ≤
      ‖x‖ * Real.sqrt (∑' i, ‖d i‖ ^ 2) := by
  simp_rw [norm_smul]
  calc
    _ ≤ Real.sqrt (∑ i ∈ s, ‖⟪e i, x⟫_𝕜‖ ^ 2) *
        Real.sqrt (∑ i ∈ s, ‖d i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ Real.sqrt (‖x‖ ^ 2) * Real.sqrt (∑' i, ‖d i‖ ^ 2) := by
      gcongr
      · exact he.sum_inner_products_le x
      · exact hd.sum_le_tsum s (fun _ _ => sq_nonneg _)
    _ = _ := by rw [Real.sqrt_sq (norm_nonneg x)]

lemma coefficient_norm_summable (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) (x : H) :
    Summable (fun i => ‖⟪e i, x⟫_𝕜 • d i‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (finite_coefficient_bound he d hd x)

lemma coefficient_tsum_bound (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) (x : H) :
    ‖∑' i, ⟪e i, x⟫_𝕜 • d i‖ ≤ ‖x‖ * Real.sqrt (∑' i, ‖d i‖ ^ 2) := by
  exact (norm_tsum_le_tsum_norm (coefficient_norm_summable he d hd x)).trans
    ((coefficient_norm_summable he d hd x).tsum_le_of_sum_le
      (finite_coefficient_bound he d hd x))

/-- The compact defect is constructed from the square-summable errors. -/
def perturbation (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) : H →L[𝕜] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, ⟪e i, x⟫_𝕜 • d i
      map_add' := by
        intro x z
        simp_rw [inner_add_right, add_smul]
        exact ((coefficient_norm_summable he d hd x).of_norm.tsum_add
          (coefficient_norm_summable he d hd z).of_norm)
      map_smul' := by
        intro a x
        simp_rw [inner_smul_right, mul_smul]
        exact (coefficient_norm_summable he d hd x).of_norm.tsum_const_smul a }
    (Real.sqrt (∑' i, ‖d i‖ ^ 2))
    (fun x => by
      change ‖∑' i, ⟪e i, x⟫_𝕜 • d i‖ ≤ _
      simpa only [mul_comm] using coefficient_tsum_bound he d hd x)

lemma perturbation_apply (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) (x : H) :
    perturbation he d hd x = ∑' i, ⟪e i, x⟫_𝕜 • d i := rfl

lemma perturbation_norm_le (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) :
    ‖perturbation he d hd‖ ≤ Real.sqrt (∑' i, ‖d i‖ ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  rw [perturbation_apply]
  simpa only [mul_comm] using coefficient_tsum_bound he d hd x


/-- Finite sums of rank-one operators approximate the defect. -/
def partialDefect (e d : ι → H) (s : Finset ι) : H →L[𝕜] H :=
  ∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (d i) (e i)

lemma partialDefect_apply (e d : ι → H) (s : Finset ι) (x : H) :
    partialDefect (𝕜 := 𝕜) e d s x = ∑ i ∈ s, ⟪e i, x⟫_𝕜 • d i := by
  simp [partialDefect]

lemma partialDefect_compact (e d : ι → H) (s : Finset ι) :
    IsCompactOperator (partialDefect (𝕜 := 𝕜) e d s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [partialDefect] using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
  | @insert i s hi hs =>
    have hr : IsCompactOperator (InnerProductSpace.rankOne 𝕜 (d i) (e i)) := by
      rw [InnerProductSpace.rankOne_def']
      exact (isCompactOperator_of_locallyCompactSpace_rng
        (ContinuousLinearMap.toSpanSingleton 𝕜 (d i))).comp_clm (innerSL 𝕜 (e i))
    simpa [partialDefect, Finset.sum_insert hi] using hr.add hs

lemma defect_tail_bound (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) (s : Finset ι) :
    ‖perturbation he d hd - partialDefect e d s‖ ≤
      Real.sqrt (∑' i : {i // i ∉ s}, ‖d i‖ ^ 2) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  rw [sub_apply, partialDefect_apply, perturbation_apply,
    ← (coefficient_norm_summable he d hd x).of_norm.sum_add_tsum_subtype_compl s,
    add_sub_cancel_left]
  have he' := he.comp (fun i : {i // i ∉ s} => (i : ι)) Subtype.val_injective
  simpa only [mul_comm, Function.comp_def] using
    coefficient_tsum_bound he' (fun i : {i // i ∉ s} => d i) (hd.subtype _) x

lemma partialDefect_tendsto (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) :
    Tendsto (partialDefect (𝕜 := 𝕜) e d) atTop (𝓝 (perturbation he d hd)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun s : Finset ι => Real.sqrt (∑' i : {i // i ∉ s}, ‖d i‖ ^ 2))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_tsum_compl_atTop_zero (fun i => ‖d i‖ ^ 2))
  apply squeeze_zero (fun s => norm_nonneg _) _ ht
  intro s
  rw [norm_sub_rev]
  exact defect_tail_bound he d hd s

lemma perturbation_compact (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) :
    IsCompactOperator (perturbation he d hd) := by
  exact isCompactOperator_of_tendsto (partialDefect_tendsto he d hd)
    (Filter.Eventually.of_forall (partialDefect_compact e d))


lemma perturbation_basis (he : Orthonormal 𝕜 e) (d : ι → H)
    (hd : Summable (fun i => ‖d i‖ ^ 2)) (i : ι) :
    perturbation he d hd (e i) = d i := by
  classical
  rw [perturbation_apply]
  simp [orthonormal_iff_ite.mp he]

/-- Riesz--Schauder applies to the negative of the compact defect. -/
lemma compact_perturbation_equiv (K : H →L[𝕜] H) (hK : IsCompactOperator K)
    (hinj : Function.Injective (ContinuousLinearMap.id 𝕜 H + K)) :
    ∃ U : H ≃L[𝕜] H, U.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 H + K := by
  have hc : ExpandedFA.Compactness.IsCompactLinearMap (-K).toLinearMap :=
    (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr hK.neg
  have hi : Function.Injective (ContinuousLinearMap.id 𝕜 H - -K) := by
    simpa only [sub_neg_eq_add] using hinj
  have hs := (ExpandedFA.Fredholm.riesz_schauder_alternative (-K) hc).mp hi
  obtain ⟨U, hU⟩ := ExpandedFA.Fredholm.riesz_schauder_bounded_inverse (-K) hc ⟨hi, hs⟩
  refine ⟨U, ?_⟩
  ext x
  change U x = _
  simpa only [sub_neg_eq_add] using hU x

/-- A bounded isomorphism carrying the given basis gives unique infinite ℓ²
expansions. The inverse is applied to the whole convergent series. -/
lemma riesz_conclusion (e : HilbertBasis ι 𝕜 H) (y : ι → H)
    (B : H →L[𝕜] H) (hBy : ∀ i, B (e i) = y i)
    (hs : ∀ c : ℓ²(ι, 𝕜), HasSum (fun i => c i • y i) (B (e.repr.symm c)))
    (hU : ∃ U : H ≃L[𝕜] H, U.toContinuousLinearMap = B) :
    Spec.RieszConclusion e y B := by
  obtain ⟨U, hUB⟩ := hU
  have hU (z : H) : U z = B z := congrArg (fun f : H →L[𝕜] H => f z) hUB
  refine ⟨⟨U, hUB⟩, ⟨U, fun i => (hU (e i)).trans (hBy i)⟩, ?_⟩
  intro x
  refine ⟨e.repr (U.symm x), ?_, ?_⟩
  · simpa only [LinearIsometryEquiv.symm_apply_apply, ← hU, U.apply_symm_apply]
      using hs (e.repr (U.symm x))
  · intro c hc
    apply e.repr.symm.injective
    apply U.injective
    calc
      U (e.repr.symm c) = B (e.repr.symm c) := hU _
      _ = x := (hs c).unique hc
      _ = U (e.repr.symm (e.repr (U.symm x))) := by simp

/-- Quadratically summable errors construct the coefficient map rather than
assuming its boundedness. The zero-kernel and small-sum cases share this map. -/
theorem quadratic_perturbations : Spec.QuadraticPerturbations.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ e y hd
  classical
  let d : ι → H := fun i => y i - e i
  let K := perturbation e.orthonormal d hd
  let B : H →L[𝕜] H := ContinuousLinearMap.id 𝕜 H + K
  have hBy (i : ι) : B (e i) = y i := by
    change e i + perturbation e.orthonormal d hd (e i) = y i
    rw [perturbation_basis]
    dsimp [d]
    abel
  have hs (c : ℓ²(ι, 𝕜)) : HasSum (fun i => c i • y i) (B (e.repr.symm c)) := by
    simpa only [Function.comp_def, map_smul, hBy] using
      B.hasSum (e.hasSum_repr_symm c)
  have hK := perturbation_compact e.orthonormal d hd
  have hnorm : ‖K‖ ≤ Real.sqrt (∑' i, ‖y i - e i‖ ^ 2) :=
    perturbation_norm_le e.orthonormal d hd
  have heq : B - ContinuousLinearMap.id 𝕜 H = K := by dsimp [B]; abel
  have hcriterion : Function.Injective B ↔
      ∀ c : ℓ²(ι, 𝕜), HasSum (fun i => c i • y i) 0 → c = 0 := by
    constructor
    · intro hi c hc
      have hz : e.repr.symm c = 0 := hi ((hs c).unique hc |>.trans B.map_zero.symm)
      apply e.repr.symm.injective
      simpa using hz
    · intro hc
      apply LinearMap.ker_eq_bot.mp
      apply bot_unique
      intro x hx
      change B x = 0 at hx
      have hc0 : e.repr x = 0 := hc (e.repr x) (by simpa [hx] using hs (e.repr x))
      have hx0 := congrArg e.repr.symm hc0
      simpa using hx0
  have hcon (hi : Function.Injective B) : Spec.RieszConclusion e y B :=
    riesz_conclusion e y B hBy hs (compact_perturbation_equiv K hK hi)
  refine ⟨B, hBy, hs, heq ▸ hK, ?_, hcriterion, hcon, ?_⟩
  · rw [heq]
    exact hnorm
  · intro hsmall
    have hk : ‖K‖ < 1 := hnorm.trans_lt ((Real.sqrt_lt' zero_lt_one).mpr (by simpa using hsmall))
    have hu : IsUnit B := by
      have h := isUnit_one_sub_of_norm_lt_one (show ‖-K‖ < 1 by simpa using hk)
      simpa only [sub_neg_eq_add, ContinuousLinearMap.one_def] using h
    exact hcon (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1

end ExpandedFA.CompactSpectral.QuadraticBasisPerturbations
