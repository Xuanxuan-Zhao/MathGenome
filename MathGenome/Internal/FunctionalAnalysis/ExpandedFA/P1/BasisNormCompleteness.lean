import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15Basis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BasisNormCompleteness
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.BasisNormCompleteness

open ExpandedFA.P1.C15Basis

abbrev partialSumSupNorm := @Spec.partialSumSupNorm

namespace BasisNormProof
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A convergent sequence, with its limit at the added point, is a continuous
function on the compact space ℕ ∪ {∞}. -/
def extension (P : ℕ → E →ₗ[𝕜] E)
    (hP : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x)) :
    E →ₗ[𝕜] C(OnePoint ℕ, E) where
  toFun x := ⟨fun z => z.elim x (fun N => P N x), by
    apply (OnePoint.continuous_iff_from_discrete _).2
    simpa only [Nat.cofinite_eq_atTop, OnePoint.elim_some, OnePoint.elim_infty] using hP x⟩
  map_add' x y := by
    ext z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe N => exact (P N).map_add x y
  map_smul' c x := by
    ext z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe N => exact (P N).map_smul c x

@[simp] theorem extension_nat (P : ℕ → E →ₗ[𝕜] E) (hP) (x : E) (N : ℕ) :
    extension P hP x (N : OnePoint ℕ) = P N x := rfl
@[simp] theorem extension_infty (P : ℕ → E →ₗ[𝕜] E) (hP) (x : E) :
    extension P hP x OnePoint.infty = x := rfl

/-- Including the limit at ∞ does not increase the supremum. -/
theorem extension_norm (P : ℕ → E →ₗ[𝕜] E)
    (hP : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x)) (x : E) :
    ‖extension P hP x‖ = partialSumSupNorm (fun N x => P N x) x := by
  have hb : BddAbove (Set.range (fun N => ‖P N x‖)) :=
    ⟨‖extension P hP x‖, by rintro _ ⟨N, rfl⟩; exact (extension P hP x).norm_coe_le_norm N⟩
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ ?_).2
    · intro z
      induction z using OnePoint.rec with
      | infty =>
        exact le_of_tendsto (hP x).norm (Filter.Eventually.of_forall
          (fun N => le_ciSup hb N))
      | coe N => exact le_ciSup hb N
    · exact (norm_nonneg (P 0 x)).trans (le_ciSup hb 0)
  · exact ciSup_le fun N => (extension P hP x).norm_coe_le_norm N

/-- Closedness of the sequence model is the only completeness obligation. -/
theorem complete_of_closed_range [CompleteSpace E] (P : ℕ → E →ₗ[𝕜] E)
    (hP : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x))
    (hc : IsClosed (Set.range (extension P hP))) :
    Spec.CompleteSupremumNorm (𝕜 := 𝕜) (fun N x => P N x) := by
  let T := extension P hP
  have hn (x : E) : ‖T x‖ = Spec.partialSumSupNorm (fun N x => P N x) x :=
    extension_norm P hP x
  have hi : Function.Injective T := by
    intro x y he
    exact congrArg (fun f : C(OnePoint ℕ, E) => f OnePoint.infty) he
  constructor
  · intro x
    exact ⟨‖T x‖, fun N => (T x).norm_coe_le_norm N⟩
  · intro x
    rw [← hn]
    exact norm_nonneg _
  · intro x
    rw [← hn, norm_eq_zero, ← T.map_zero, hi.eq_iff]
  · intro x y
    simp only [← hn, T.map_add]
    exact norm_add_le _ _
  · intro c x
    simp only [← hn, T.map_smul, norm_smul]
  · intro x
    rw [← hn]
    exact (T x).norm_coe_le_norm OnePoint.infty
  · intro s hs
    let S := T.range
    have hS : IsClosed (S : Set C(OnePoint ℕ, E)) := hc
    have : CompleteSpace S := hS.completeSpace_coe
    let t : ℕ → S := fun n => ⟨T (s n), LinearMap.mem_range_self _ _⟩
    have ht : CauchySeq t := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨J, hJ⟩ := hs ε hε
      refine ⟨J, fun j hj k hk => ?_⟩
      change dist (T (s j)) (T (s k)) < ε
      rw [dist_eq_norm, ← T.map_sub, hn]
      exact hJ j hj k hk
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete ht
    obtain ⟨x, hx⟩ := z.property
    refine ⟨x, fun ε hε => ?_⟩
    obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hz) ε hε
    refine ⟨J, fun j hj => ?_⟩
    have he := hJ j hj
    change dist (T (s j)) z.val < ε at he
    rw [← hx, dist_eq_norm, ← T.map_sub, hn] at he
    exact he

/-- The successor difference of the raw partial sums is the single basis term. -/
theorem raw_increment {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e)
    (x : E) (n : ℕ) :
    rawPartialSum h (n + 1) x - rawPartialSum h n x = rawCoordinates h x n • e n := by
  simp [rawPartialSum, ExpandedFA.P1.C15Basis.Spec.rawPartialSum, ExpandedFA.P1.C15Basis.Spec.orderedPartialSum,
    Finset.sum_range_succ]

/-- Admissible sequences start at zero and have their nth increment in 𝕜 eₙ.
Both constraints are closed in the uniform norm. -/
def admissible (e : ℕ → E) : Set C(OnePoint ℕ, E) :=
  {q | q (0 : ℕ) = 0 ∧ ∀ n : ℕ,
    q (n + 1 : ℕ) - q (n : OnePoint ℕ) ∈ Submodule.span 𝕜 {e n}}

theorem admissible_closed (e : ℕ → E) : IsClosed (admissible (𝕜 := 𝕜) e) := by
  have hz : IsClosed {q : C(OnePoint ℕ, E) | q (0 : ℕ) = 0} :=
    isClosed_eq (continuous_eval_const _) continuous_const
  have hd (n : ℕ) : IsClosed {q : C(OnePoint ℕ, E) |
      q (n + 1 : ℕ) - q (n : OnePoint ℕ) ∈ Submodule.span 𝕜 {e n}} :=
    (Submodule.span 𝕜 {e n}).closed_of_finiteDimensional.preimage
      ((continuous_eval_const _).sub (continuous_eval_const _))
  simpa only [admissible, Set.ofPred_and, Set.ofPred_forall] using
    hz.inter (isClosed_iInter hd)

theorem raw_extension_range {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e) :
    Set.range (extension (rawPartialSumLinearMap h) (rawPartialSum_tendsto h)) =
      admissible (𝕜 := 𝕜) e := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨rawPartialSum_zero h x, fun n => ?_⟩
    change rawPartialSum h (n + 1) x - rawPartialSum h n x ∈ _
    rw [raw_increment]
    exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
  · intro hq
    have hd (n : ℕ) := Submodule.mem_span_singleton.mp (hq.2 n)
    choose a ha using hd
    have hs (n : ℕ) : orderedPartialSum e a n = q (n : OnePoint ℕ) := by
      induction n with
      | zero => simpa [orderedPartialSum, ExpandedFA.P1.C15Basis.Spec.orderedPartialSum] using hq.1.symm
      | succ n ih =>
        change (∑ i ∈ Finset.range (n + 1), a i • e i) = _
        rw [Finset.sum_range_succ]
        change orderedPartialSum e a n + a n • e n = _
        rw [ih, ha n]
        abel
    have hq_lim : Tendsto (fun n : ℕ => q (n : OnePoint ℕ)) atTop
        (𝓝 (q OnePoint.infty)) := by
      simpa only [Nat.cofinite_eq_atTop] using
        (OnePoint.continuous_iff_from_discrete q).mp q.continuous
    have ha_lim : Tendsto (orderedPartialSum e a) atTop (𝓝 (q OnePoint.infty)) := by
      exact hq_lim.congr' (Filter.Eventually.of_forall fun n => (hs n).symm)
    have hac := rawCoordinates_unique h (q OnePoint.infty) a ha_lim
    refine ⟨q OnePoint.infty, ?_⟩
    ext z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe n =>
      change orderedPartialSum e (rawCoordinates h (q OnePoint.infty)) n = _
      rw [← hac, hs]

end BasisNormProof

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Completeness precedes every use of the bounded inverse theorem or of
continuity of the coordinate functionals. -/
theorem raw_basis_complete {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e) :
    Spec.CompleteSupremumNorm (𝕜 := 𝕜) (rawPartialSum h) := by
  apply BasisNormProof.complete_of_closed_range (rawPartialSumLinearMap h)
    (rawPartialSum_tendsto h)
  rw [BasisNormProof.raw_extension_range h]
  exact BasisNormProof.admissible_closed e

/-- The same supremum norm for a finite list, including a list of length zero. -/
theorem finite_basis_complete {d : ℕ} {e : Fin d → E}
    (h : IsRawFiniteBasis (𝕜 := 𝕜) e) :
    Spec.CompleteSupremumNorm (𝕜 := 𝕜) (finitePartialSum h) := by
  let A : (Fin d → 𝕜) →ₗ[𝕜] E :=
    { toFun := finiteSynthesis e
      map_add' := by
        intro a b
        simp [finiteSynthesis, ExpandedFA.P1.C15Basis.Spec.finiteSynthesis, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [finiteSynthesis, ExpandedFA.P1.C15Basis.Spec.finiteSynthesis, mul_smul, Finset.smul_sum] }
  have hA : Function.Surjective A := fun x =>
    ⟨finiteCoordinates h x, finiteCoordinates_expansion h x⟩
  have : FiniteDimensional 𝕜 E := FiniteDimensional.of_surjective A hA
  have hP (x : E) : Tendsto (fun N => finitePartialSumLinearMap h N x) atTop (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop d] with N hN
    exact (finitePartialSum_of_le h N hN x).symm
  apply BasisNormProof.complete_of_closed_range (finitePartialSumLinearMap h) hP
  exact (BasisNormProof.extension (finitePartialSumLinearMap h) hP).range.closed_of_finiteDimensional

omit [CompleteSpace E] in
/-- For an empty expansion every partial sum, and hence the basis norm, is zero. -/
theorem empty_basis_norm
    (h : IsRawFiniteBasis (𝕜 := 𝕜) (emptyFamily (E := E))) (x : E) :
    partialSumSupNorm (finitePartialSum h) x = 0 := by
  simp [partialSumSupNorm, Spec.partialSumSupNorm, emptyPartialSum_eq_zero]

end ExpandedFA.P1.BasisNormCompleteness
