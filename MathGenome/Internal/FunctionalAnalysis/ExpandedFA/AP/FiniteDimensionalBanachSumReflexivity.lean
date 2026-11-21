import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.FiniteDimensionalBanachSumReflexivity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.EnfloSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Stability
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option maxSynthPendingDepth 5
set_option synthInstance.maxSize 512
noncomputable section
open scoped ENNReal BigOperators Classical
namespace ExpandedFA.AP.FiniteDimensionalBanachSumReflexivity

section General
variable {I : Type*} [DecidableEq I] (E : I → Type*) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

/-- Compactness of the unit ball gives a norming vector, including for the
zero functional and the zero space. The rescaling avoids a nontriviality assumption. -/
theorem exists_norming_vector {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : V →L[ℝ] ℝ) :
    ∃ x : V, ‖x‖ ≤ ‖f‖ ∧ f x = ‖f‖ ^ 2 := by
  let := FiniteDimensional.proper_rclike ℝ V
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : V) 1).exists_isMaxOn
    (by exact ⟨0, by simp⟩) f.continuous.norm.continuousOn
  have hn : ‖f z‖ = ‖f‖ := by
    apply le_antisymm
    · exact f.unit_le_opNorm z (by simpa using hz)
    · by_contra h
      obtain ⟨w, hw, hfw⟩ := f.exists_lt_apply_of_lt_opNorm (lt_of_not_ge h)
      exact (not_lt_of_ge (hmax (by simpa using hw.le))) hfw
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  by_cases hfz : 0 ≤ f z
  · refine ⟨‖f‖ • z, ?_, ?_⟩
    · simpa [norm_smul, abs_of_nonneg (norm_nonneg f)] using
        mul_le_mul_of_nonneg_left hz' (norm_nonneg f)
    · simp only [map_smul, smul_eq_mul]
      rw [Real.norm_eq_abs, abs_of_nonneg hfz] at hn
      rw [hn]; ring
  · refine ⟨-(‖f‖ • z), ?_, ?_⟩
    · simpa [norm_smul, abs_of_nonneg (norm_nonneg f)] using
        mul_le_mul_of_nonneg_left hz' (norm_nonneg f)
    · simp only [map_neg, map_smul, smul_eq_mul]
      rw [Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hfz)] at hn
      nlinarith

abbrev blockRestriction (F : lp E 2 →L[ℝ] ℝ) (i : I) : E i →L[ℝ] ℝ :=
  F.comp (lp.singleContinuousLinearMap ℝ E 2 i)

/-- The finite-coordinate test proves the sharp square bound. It uses norm
attainment in each block, never an inner product on the original blocks. -/
theorem restriction_square_bound (F : lp E 2 →L[ℝ] ℝ) (A : Finset I) :
    ∑ i ∈ A, ‖blockRestriction E F i‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  classical
  choose x hx hfx using fun i => exists_norming_vector (blockRestriction E F i)
  let y : lp E 2 := ∑ i ∈ A, lp.single 2 i (x i)
  let S : ℝ := ∑ i ∈ A, ‖blockRestriction E F i‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hy : ‖y‖ ^ 2 ≤ S := by
    have h := lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x A
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [h]
    exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
  have hFy : F y = S := by
    simp only [y, map_sum, S]
    exact Finset.sum_congr rfl fun i _ => by
      simpa only [blockRestriction, ContinuousLinearMap.comp_apply,
        lp.singleContinuousLinearMap_apply] using hfx i
  have hbound : S ≤ ‖F‖ * ‖y‖ := by
    rw [← hFy]
    exact (le_abs_self _).trans (F.le_opNorm y)
  have hsquare : S ^ 2 ≤ ‖F‖ ^ 2 * ‖y‖ ^ 2 := by
    calc
      S ^ 2 ≤ (‖F‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ hS hbound 2
      _ = _ := by ring
  have hprod := mul_le_mul_of_nonneg_left hy (sq_nonneg ‖F‖)
  dsimp [S] at *
  nlinarith

/-- The restrictions are an actual square-summable family. -/
def restriction (F : lp E 2 →L[ℝ] ℝ) : lp (fun i => E i →L[ℝ] ℝ) 2 :=
  ⟨blockRestriction E F, memℓp_gen' (by
    intro A
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using restriction_square_bound E F A)⟩

theorem norm_restriction_le (F : lp E 2 →L[ℝ] ℝ) : ‖restriction E F‖ ≤ ‖F‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (norm_nonneg F)
  intro A
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, restriction] using restriction_square_bound E F A

/-- Hölder's inequality supplies the functional with the exact series formula. -/
def pairing : lp (fun i => E i →L[ℝ] ℝ) 2 →L[ℝ] (lp E 2 →L[ℝ] ℝ) :=
  lp.dualPairing 2 2 (fun i => ContinuousLinearMap.id ℝ (E i →L[ℝ] ℝ))
    (K := 1) (fun _ => ContinuousLinearMap.norm_id_le)

omit [∀ i, FiniteDimensional ℝ (E i)] [DecidableEq I] in
theorem pairing_apply (f : lp (fun i => E i →L[ℝ] ℝ) 2) (y : lp E 2) :
    pairing E f y = ∑' i, f i (y i) := rfl

omit [∀ i, FiniteDimensional ℝ (E i)] [DecidableEq I] in
/-- The pairing is given by a convergent scalar series. -/
theorem pairing_hasSum (f : lp (fun i => E i →L[ℝ] ℝ) 2) (y : lp E 2) :
    HasSum (fun i => f i (y i)) (pairing E f y) := by
  have h : Memℓp (fun i => f i (y i)) 1 :=
    (lp.memℓp f).holder 1 (lp.memℓp y)
      (fun i => ContinuousLinearMap.id ℝ (E i →L[ℝ] ℝ))
      (K := 1) (fun _ => ContinuousLinearMap.norm_id_le)
  exact h.summable_of_one.hasSum

omit [∀ i, FiniteDimensional ℝ (E i)] [DecidableEq I] in
theorem norm_pairing_le (f : lp (fun i => E i →L[ℝ] ℝ) 2) :
    ‖pairing E f‖ ≤ ‖f‖ := by
  simpa using (pairing E).le_of_opNorm_le
    (lp.norm_dualPairing (p := 2) (q := 2)
      (fun i => ContinuousLinearMap.id ℝ (E i →L[ℝ] ℝ))
      (K := 1) (fun _ => ContinuousLinearMap.norm_id_le)) f

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem pairing_single_right (f : lp (fun i => E i →L[ℝ] ℝ) 2) (i : I) (x : E i) :
    pairing E f (lp.single 2 i x) = f i x := by
  classical
  rw [pairing_apply, tsum_eq_single i]
  · simp
  · intro j hj
    simp [Pi.single_eq_of_ne hj]

theorem restriction_pairing (f : lp (fun i => E i →L[ℝ] ℝ) 2) :
    restriction E (pairing E f) = f := by
  ext i x
  exact pairing_single_right E f i x

theorem pairing_restriction (F : lp E 2 →L[ℝ] ℝ) : pairing E (restriction E F) = F := by
  ext y
  have hsum := lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ∞) y
  have hF := F.hasSum hsum
  simpa only [pairing_apply, restriction, blockRestriction, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply] using hF.tsum_eq

/-- Isometric dual identification for real finite-dimensional normed blocks. -/
def dualEquiv : lp (fun i => E i →L[ℝ] ℝ) 2 ≃ₗᵢ[ℝ] (lp E 2 →L[ℝ] ℝ) :=
  { (pairing E).toLinearMap with
    invFun := restriction E
    left_inv := restriction_pairing E
    right_inv := pairing_restriction E
    norm_map' := fun f => by
      change ‖pairing E f‖ = ‖f‖
      exact le_antisymm (norm_pairing_le E f) (by
        simpa only [restriction_pairing] using norm_restriction_le E (pairing E f)) }

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem pairing_single_left (i : I) (f : E i →L[ℝ] ℝ) (y : lp E 2) :
    pairing E (lp.single 2 i f) y = f (y i) := by
  classical
  rw [pairing_apply, tsum_eq_single i]
  · simp
  · intro j hj
    simp [Pi.single_eq_of_ne hj]

/-- Transport of functionals across an isometric equivalence is isometric. -/
def dualTransport {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃ₗᵢ[ℝ] W) :
    (W →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (V →L[ℝ] ℝ) where
  toFun B := B.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  invFun H := H.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  left_inv B := by ext f; simp
  right_inv H := by ext x; simp
  map_add' B C := by ext x; rfl
  map_smul' a B := by ext x; rfl
  norm_map' B := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
      intro x
      simpa using B.le_opNorm (e x)
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro y
      have h := (B.comp e.toContinuousLinearEquiv.toContinuousLinearMap).le_opNorm (e.symm y)
      simpa using h

/-- The bidual is identified with the square sum of the block biduals. -/
def bidualEquiv : ((lp E 2 →L[ℝ] ℝ) →L[ℝ] ℝ) ≃ₗᵢ[ℝ]
    lp (fun i => (E i →L[ℝ] ℝ) →L[ℝ] ℝ) 2 :=
  (dualTransport (dualEquiv E)).trans (dualEquiv (fun i => E i →L[ℝ] ℝ)).symm

theorem bidualEquiv_apply (B : (lp E 2 →L[ℝ] ℝ) →L[ℝ] ℝ) (i : I)
    (f : E i →L[ℝ] ℝ) :
    bidualEquiv E B i f = B (dualEquiv E (lp.single 2 i f)) := rfl

theorem bidualEquiv_canonical (y : lp E 2) (i : I) :
    bidualEquiv E (NormedSpace.inclusionInDoubleDual ℝ (lp E 2) y) i =
      NormedSpace.inclusionInDoubleDual ℝ (E i) (y i) := by
  ext f
  exact pairing_single_left E i f y

theorem finrank_continuousDual {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : Module.finrank ℝ (V →L[ℝ] ℝ) = Module.finrank ℝ V := by
  rw [← (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- In finite dimension the isometric canonical injection is onto, since
continuous and algebraic duals have the same dimension. -/
def finiteBidualEquiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : V ≃ₗᵢ[ℝ] ((V →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  (NormedSpace.inclusionInDoubleDualLi ℝ).toLinearIsometryEquiv (by
    change Module.finrank ℝ V = Module.finrank ℝ ((V →L[ℝ] ℝ) →L[ℝ] ℝ)
    rw [finrank_continuousDual, finrank_continuousDual])

/-- Surjectivity of the canonical map follows from the componentwise formula,
using the original norm to check square summability of the preimages. -/
theorem sum_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (lp E 2)) := by
  intro B
  let z := bidualEquiv E B
  let y : lp E 2 := ⟨fun i => (finiteBidualEquiv (V := E i)).symm (z i), by
    apply Memℓp.of_norm
    simpa only [LinearIsometryEquiv.norm_map] using (lp.memℓp z).norm⟩
  refine ⟨y, (bidualEquiv E).injective ?_⟩
  ext i f
  rw [bidualEquiv_canonical]
  change finiteBidualEquiv (V := E i) ((finiteBidualEquiv (V := E i)).symm (z i)) f = z i f
  rw [LinearIsometryEquiv.apply_symm_apply]

end General

open EnfloSpace

theorem dual_and_bidual_identification : Spec.DualAndBidualIdentification := by
  intro D
  refine ⟨dualEquiv (Summand D), ?_, ?_, bidualEquiv (Summand D), ?_, ?_⟩
  · exact pairing_hasSum (Summand D)
  · intro F m x
    rfl
  · exact bidualEquiv_apply (Summand D)
  · exact bidualEquiv_canonical (Summand D)

theorem ambient_reflexive : Spec.AmbientReflexive := by
  intro D
  exact sum_reflexive (Summand D)

theorem closed_span_reflexive : Spec.ClosedSpanReflexive := by
  intro D
  let : CompleteSpace (Y D) := ambient_complete D
  exact ((ExpandedFA.P1.C14Stability.reflexivity_stability ℝ (Y D)
    (closedSpan D) (closed_span_closed D)).1 (ambient_reflexive D)).1

end ExpandedFA.AP.FiniteDimensionalBanachSumReflexivity
