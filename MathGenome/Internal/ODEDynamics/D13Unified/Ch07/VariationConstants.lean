import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.VariationConstants
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.EvolutionMatrix
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Operator

namespace D13Unified.Ch07.VariationConstants
open EvolutionMatrix
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

/-- Matrix action as a real continuous linear map, with the original values. -/
private def actionMap : Matrix (Fin n) (Fin n) 𝕂 →L[ℝ]
    ((Fin n → 𝕂) →L[ℝ] (Fin n → 𝕂)) :=
  LinearSystemExistence.matrixOperatorInMap (ContinuousLinearEquiv.refl ℝ (Fin n → 𝕂))

private lemma actionMap_apply (M : Matrix (Fin n) (Fin n) 𝕂) (v : Fin n → 𝕂) :
    (actionMap (𝕂 := 𝕂) (n := n)) M v = M *ᵥ v := rfl

lemma continuousOn_mulVec {J : Set ℝ} {M : ℝ → Matrix (Fin n) (Fin n) 𝕂}
    {v : ℝ → Fin n → 𝕂} (hM : ContinuousOn M J) (hv : ContinuousOn v J) :
    ContinuousOn (fun t => M t *ᵥ v t) J :=
  ((actionMap (𝕂 := 𝕂) (n := n)).continuous.comp_continuousOn hM).clm_apply hv

private lemma deriv_comp_linear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) {J : Set ℝ} {v : ℝ → E} {v' : E} {t : ℝ}
    (hv : HasDerivWithinAt v v' J t) :
    HasDerivWithinAt (fun r => T (v r)) (T v') J t := by
  exact T.hasFDerivAt.comp_hasDerivWithinAt t hv

set_option backward.isDefEq.respectTransparency false in
lemma hasDerivWithinAt_mulVec {J : Set ℝ} {M : ℝ → Matrix (Fin n) (Fin n) 𝕂}
    {v : ℝ → Fin n → 𝕂} {t : ℝ} {M' : Matrix (Fin n) (Fin n) 𝕂}
    {v' : Fin n → 𝕂} (hM : HasDerivWithinAt M M' J t)
    (hv : HasDerivWithinAt v v' J t) :
    HasDerivWithinAt (fun r => M r *ᵥ v r) (M' *ᵥ v t + M t *ᵥ v') J t := by
  let T := actionMap (𝕂 := 𝕂) (n := n)
  have hd : HasDerivWithinAt (fun r => T (M r)) (T M') J t :=
    deriv_comp_linear (E := Matrix (Fin n) (Fin n) 𝕂)
      (F := ((Fin n → 𝕂) →L[ℝ] (Fin n → 𝕂))) T hM
  exact hd.clm_apply hv

lemma integral_mulVec (M : Matrix (Fin n) (Fin n) 𝕂) {v : ℝ → Fin n → 𝕂}
    {s t : ℝ} (hv : IntervalIntegrable v volume s t) :
    (∫ r in s..t, M *ᵥ v r) = M *ᵥ (∫ r in s..t, v r) :=
  ((actionMap (𝕂 := 𝕂) (n := n)) M).intervalIntegral_comp_comm hv



/-- The unique inhomogeneous IVP solution on the entire actual interval,
with oriented integrals and the formula for every fundamental matrix. -/
theorem variation_of_constants :
    Specs.D13Unified.Ch07.VariationConstants.VariationOfConstants := by
  have hcomp := EvolutionMatrix.composition
  have hevol := EvolutionMatrix.evolution
  have hchar := EvolutionMatrix.fundamental_characterization
  have hinv := EvolutionMatrix.inverse
  have hstart := EvolutionMatrix.starting_time_derivative
  intro 𝕂 _ n I A b s x₀ hs hA hb
  let P := fun t => U I A t s
  let Q := fun t => U I A s t
  let g := fun t => Q t *ᵥ b t
  let q := fun t => ∫ r in s..t, g r
  let w := fun t => P t *ᵥ (x₀ + q t)
  let x := fun t => U I A t s *ᵥ x₀ + ∫ r in s..t, U I A t r *ᵥ b r
  obtain ⟨hP, hPs, hdP, _, _, _⟩ := hevol 𝕂 n I A s hs hA
  have hQd : ∀ t ∈ I.carrier,
      HasDerivWithinAt Q (-Q t * A t) I.carrier t :=
    fun t ht => hstart 𝕂 n I A hA s hs t ht
  have hQ : ContinuousOn Q I.carrier :=
    fun t ht => (hQd t ht).continuousWithinAt
  have hg : ContinuousOn g I.carrier := continuousOn_mulVec hQ hb
  have hqd : ∀ t ∈ I.carrier, HasDerivWithinAt q (g t) I.carrier t :=
    fun t ht => hasDerivWithinAt_integral_on_interval I.ordConnected hg hs ht
  have hq : ContinuousOn q I.carrier := fun t ht => (hqd t ht).continuousWithinAt
  have hPQ (t : ℝ) (ht : t ∈ I.carrier) : P t * Q t = 1 := by
    rw [hcomp 𝕂 n I A hA s hs t ht t ht]
    exact (hevol 𝕂 n I A t ht hA).2.1
  have hw : ContinuousOn w I.carrier :=
    continuousOn_mulVec hP (continuousOn_const.add hq)
  have hwEq : EqOn x w I.carrier := by
    intro t ht
    dsimp [x, w, q, g]
    rw [Matrix.mulVec_add, ← integral_mulVec (P t)
      ((hg.mono (I.ordConnected.uIcc_subset hs ht)).intervalIntegrable)]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp [P, Q]
    rw [Matrix.mulVec_mulVec, hcomp 𝕂 n I A hA s hs r
      (I.ordConnected.uIcc_subset hs ht hr) t ht]
  have hwd : ∀ t ∈ I.carrier,
      HasDerivWithinAt w (A t *ᵥ w t + b t) I.carrier t := by
    intro t ht
    have hd := hasDerivWithinAt_mulVec (hdP t ht) ((hqd t ht).const_add x₀)
    have heq : (A t * P t) *ᵥ (x₀ + q t) + P t *ᵥ g t =
        A t *ᵥ w t + b t := by
      dsimp [w, g]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPQ t ht, Matrix.one_mulVec]
    exact heq ▸ hd
  have hxc : ContinuousOn x I.carrier := hw.congr hwEq
  have hxd : ∀ t ∈ I.carrier,
      HasDerivWithinAt x (A t *ᵥ x t + b t) I.carrier t := by
    intro t ht
    rw [hwEq ht]
    exact (hwd t ht).congr_of_mem hwEq ht
  refine ⟨hxc, ?_, hxd, ?_, ?_, ?_⟩
  · dsimp [x]
    simp only [hPs, Matrix.one_mulVec, intervalIntegral.integral_same, add_zero]
  · exact LinearSystemExistence.regularity ((continuousOn_mulVec hA hxc).add hb) hxd
  · intro y hy hys hyd t ht
    let v := fun r => Q r *ᵥ y r
    have hv : ContinuousOn v I.carrier := continuousOn_mulVec hQ hy
    have hvd : ∀ r ∈ I.carrier, HasDerivWithinAt v (g r) I.carrier r := by
      intro r hr
      have hd := hasDerivWithinAt_mulVec (hQd r hr) (hyd r hr)
      have heq : (-Q r * A r) *ᵥ y r + Q r *ᵥ (A r *ᵥ y r + b r) = g r := by
        simp only [Matrix.neg_mul, Matrix.neg_mulVec, Matrix.mulVec_add,
          Matrix.mulVec_mulVec, g]
        abel
      exact heq ▸ hd
    have hint := integral_eq_sub_on_interval I.ordConnected hv hg hvd hs ht
    have hvs : v s = x₀ := by dsimp [v, Q]; rw [hPs, hys, Matrix.one_mulVec]
    have hvt : v t = x₀ + q t := by dsimp [q]; rw [hint, hvs]; abel
    calc
      y t = P t *ᵥ v t := by
        dsimp [v]
        rw [Matrix.mulVec_mulVec, hPQ t ht, Matrix.one_mulVec]
      _ = w t := by rw [hvt]
      _ = x t := (hwEq ht).symm
  · intro X hX t ht
    obtain ⟨C, ⟨hC, hXC⟩, _⟩ := (hchar 𝕂 n I A hA s hs X).mp hX
    have hCs : X s = C := by simpa only [hPs, Matrix.one_mul] using hXC hs
    have hXi : ∀ r ∈ I.carrier, (X r)⁻¹ = C⁻¹ * Q r := by
      intro r hr
      rw [hXC hr, Matrix.mul_inv_rev, (hinv 𝕂 n I A hA s hs r hr).2]
    have hCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC)
    have hXinvb : ContinuousOn (fun r => (X r)⁻¹ *ᵥ b r) I.carrier := by
      apply (continuousOn_mulVec
        ((continuousOn_const : ContinuousOn (fun _ : ℝ => C⁻¹) I.carrier).mul hQ) hb).congr
      intro r hr
      dsimp only
      rw [hXi r hr]
      rfl
    rw [Matrix.mulVec_add, ← integral_mulVec (X t)
      ((hXinvb.mono (I.ordConnected.uIcc_subset hs ht)).intervalIntegrable)]
    dsimp [x]
    congr 1
    · rw [Matrix.mulVec_mulVec, hCs, hXC ht, Matrix.mul_assoc, hCi, Matrix.mul_one]
    · apply intervalIntegral.integral_congr
      intro r hr
      have hrI := I.ordConnected.uIcc_subset hs ht hr
      dsimp only
      rw [Matrix.mulVec_mulVec, hXC ht, hXi r hrI, ← Matrix.mul_assoc,
        Matrix.mul_assoc (U I A t s) C C⁻¹, hCi, Matrix.mul_one,
        hcomp 𝕂 n I A hA s hs r hrI t ht]

end D13Unified.Ch07.VariationConstants
