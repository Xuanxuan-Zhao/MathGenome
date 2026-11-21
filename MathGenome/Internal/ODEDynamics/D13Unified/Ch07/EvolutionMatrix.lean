import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.EvolutionMatrix
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.LinearSystemExistence
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch07.EvolutionMatrix
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

/-- Verify the defining formula of the shared canonical evolution matrix. -/
theorem U_definition : Specs.D13Unified.Ch07.EvolutionMatrix.UDefinition := rfl

/-- Verify the defining formula of the shared fundamental-matrix predicate. -/
theorem fundamental_definition :
    Specs.D13Unified.Ch07.EvolutionMatrix.FundamentalDefinition := rfl

lemma normalized_solution (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ)
    (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier) :
    NormalizedSolution I A s (fun t => U I A t s) := by
  change NormalizedSolution I A s (Classical.epsilon (NormalizedSolution I A s))
  apply Classical.epsilon_spec
  obtain ⟨Y, hc, hi, hd, _⟩ := LinearSystemExistence.evolution_existence 𝕂 n I A s hs hA
  exact ⟨Y, hc, hi, hd⟩

/-- Uniqueness is pointwise on I, without requiring agreement of ambient
representatives outside their actual domains. -/
lemma solution_unique (I : TimeInterval)
    (A X Y : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ)
    (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier)
    (hX : ContinuousOn X I.carrier) (hY : ContinuousOn Y I.carrier)
    (hi : X s = Y s)
    (hdX : ∀ t ∈ I.carrier, HasDerivWithinAt X (A t * X t) I.carrier t)
    (hdY : ∀ t ∈ I.carrier, HasDerivWithinAt Y (A t * Y t) I.carrier t) :
    EqOn X Y I.carrier := by
  obtain ⟨Z, _, _, _, _, hu⟩ := LinearSystemExistence.matrix_existence 𝕂 n n I A s (Y s) hs hA
  intro t ht
  exact (hu X hX hi hdX ht).trans (hu Y hY rfl hdY ht).symm

/-- The chosen normalized solution inherits the entire upstream existence and
norm theorem by uniqueness. -/
theorem evolution : Specs.D13Unified.Ch07.EvolutionMatrix.Evolution := by
  intro 𝕂 _ n I A s hs hA
  obtain ⟨hc, hi, hd⟩ := normalized_solution I A s hs hA
  obtain ⟨Y, hY, hYs, hYd, hb, hreg, hu⟩ :=
    LinearSystemExistence.evolution_existence 𝕂 n I A s hs hA
  have heq : EqOn (fun t => U I A t s) Y I.carrier := hu _ hc hi hd
  refine ⟨hc, hi, hd, ?_, hreg.congr heq, ?_⟩
  · intro t ht
    have het : U I A t s = Y t := heq ht
    rw [het]
    exact hb t ht
  · intro V hV hVs hVd
    exact solution_unique I A V (fun t => U I A t s) s hs hA hV hc
      (hVs.trans hi.symm) hVd hd

theorem norm_bound_in : Specs.D13Unified.Ch07.EvolutionMatrix.NormBoundIn := by
  intro 𝕂 _ n E _ _ _ e I A s hs hA
  obtain ⟨Y, hc, hi, hd, hb, _, hu⟩ :=
    LinearSystemExistence.matrix_evolution_in 𝕂 n e I A s hs hA
  obtain ⟨hUc, hUi, hUd⟩ := normalized_solution I A s hs hA
  have heq := hu (fun t => U I A t s) hUc hUi hUd
  intro t ht
  have het : U I A t s = Y t := heq ht
  rw [het]
  exact hb t ht

lemma continuousOn_U (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (s : ℝ) (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier) :
    ContinuousOn (fun t => U I A t s) I.carrier :=
  (normalized_solution I A s hs hA).1

lemma U_self (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (s : ℝ) (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier) : U I A s s = 1 :=
  (normalized_solution I A s hs hA).2.1

lemma hasDerivWithinAt_U (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (s : ℝ) (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier)
    (t : ℝ) (ht : t ∈ I.carrier) :
    HasDerivWithinAt (fun r => U I A r s) (A t * U I A t s) I.carrier t :=
  (normalized_solution I A s hs hA).2.2 t ht

lemma contDiffOn_U (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (s : ℝ) (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier) :
    ContDiffOn ℝ 1 (fun t => U I A t s) I.carrier :=
  (evolution 𝕂 n I A s hs hA).2.2.2.2.1

/-- Constant right multiplication preserves the same homogeneous equation. -/
lemma hasDerivWithinAt_U_mul (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ)
    (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier)
    (C : Matrix (Fin n) (Fin n) 𝕂) (t : ℝ) (ht : t ∈ I.carrier) :
    HasDerivWithinAt (fun r => U I A r s * C) (A t * (U I A t s * C)) I.carrier t := by
  convert! (hasDerivWithinAt_U I A s hs hA t ht).mul_const C using 1
  simp only [mul_assoc]

theorem composition : Specs.D13Unified.Ch07.EvolutionMatrix.Composition := by
  intro 𝕂 _ n I A hA r hr s hs t ht
  have heq := solution_unique I A
    (fun v => U I A v r * U I A r s) (fun v => U I A v s) r hr hA
    ((continuousOn_U I A r hr hA).mul continuousOn_const)
    (continuousOn_U I A s hs hA)
    (by rw [U_self I A r hr hA, one_mul])
    (hasDerivWithinAt_U_mul I A r hr hA (U I A r s))
    (hasDerivWithinAt_U I A s hs hA)
  exact heq ht

theorem inverse : Specs.D13Unified.Ch07.EvolutionMatrix.Inverse := by
  intro 𝕂 _ n I A hA s hs t ht
  have hright : U I A t s * U I A s t = 1 :=
    (composition 𝕂 n I A hA s hs t ht t ht).trans (U_self I A t ht hA)
  have hleft : U I A s t * U I A t s = 1 :=
    (composition 𝕂 n I A hA t ht s hs s hs).trans (U_self I A s hs hA)
  exact ⟨⟨⟨U I A t s, U I A s t, hright, hleft⟩, rfl⟩,
    Matrix.inv_eq_right_inv hright⟩

/-- Inversion is differentiated in the real matrix algebra. The reverse-time
composition identities cancel the factors on the correct sides. -/
theorem starting_time_derivative :
    Specs.D13Unified.Ch07.EvolutionMatrix.StartingTimeDerivative := by
  intro 𝕂 _ n I A hA t ht s hs
  have hright : U I A s t * U I A t s = 1 :=
    (composition 𝕂 n I A hA t ht s hs s hs).trans (U_self I A s hs hA)
  have hleft : U I A t s * U I A s t = 1 :=
    (composition 𝕂 n I A hA s hs t ht t ht).trans (U_self I A t ht hA)
  let v : (Matrix (Fin n) (Fin n) 𝕂)ˣ :=
    ⟨U I A s t, U I A t s, hright, hleft⟩
  have hd : HasDerivWithinAt (fun r => Ring.inverse (U I A r t))
      (-(U I A t s * (A s * U I A s t) * U I A t s)) I.carrier s := by
    convert! (hasFDerivAt_ringInverse (𝕜 := ℝ) v).comp_hasDerivWithinAt s
      (hasDerivWithinAt_U I A t ht hA s hs) using 1
  have heq : EqOn (fun r => U I A t r)
      (fun r => Ring.inverse (U I A r t)) I.carrier := by
    intro r hr
    change U I A t r = Ring.inverse (U I A r t)
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    exact (inverse 𝕂 n I A hA t ht r hr).2.symm
  have hderiv : -(U I A t s * (A s * U I A s t) * U I A t s) =
      -U I A t s * A s := by
    simp only [mul_assoc, hright, mul_one, neg_mul]
  rw [hderiv] at hd
  exact hd.congr_of_mem heq hs

/-- Every invertible constant gives a fundamental matrix, on all of I. -/
lemma fundamental_mul (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ)
    (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier)
    (C : Matrix (Fin n) (Fin n) 𝕂) (hC : IsUnit C) :
    IsFundamentalMatrixOn I A (fun t => U I A t s * C) := by
  refine ⟨(contDiffOn_U I A s hs hA).mul contDiffOn_const,
    hasDerivWithinAt_U_mul I A s hs hA C, ?_⟩
  intro t ht
  exact ((inverse 𝕂 n I A hA s hs t ht).1).mul hC

/-- Evaluation at the normalization time identifies every representation
constant, not only constants already assumed equal to X(s). -/
lemma fundamental_constant (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ)
    (hs : s ∈ I.carrier) (hA : ContinuousOn A I.carrier)
    (X : ℝ → Matrix (Fin n) (Fin n) 𝕂) (C : Matrix (Fin n) (Fin n) 𝕂)
    (heq : EqOn X (fun t => U I A t s * C) I.carrier) : C = X s := by
  have hi : X s = U I A s s * C := heq hs
  simpa only [U_self I A s hs hA, one_mul] using hi.symm

theorem fundamental_characterization :
    Specs.D13Unified.Ch07.EvolutionMatrix.FundamentalCharacterization := by
  intro 𝕂 _ n I A hA s hs X
  constructor
  · intro hX
    have heq : EqOn X (fun t => U I A t s * X s) I.carrier :=
      solution_unique I A X (fun t => U I A t s * X s) s hs hA
        hX.1.continuousOn ((continuousOn_U I A s hs hA).mul continuousOn_const)
        (by rw [U_self I A s hs hA, one_mul]) hX.2.1
        (hasDerivWithinAt_U_mul I A s hs hA (X s))
    exact ⟨X s, ⟨hX.2.2 s hs, heq⟩,
      fun C hC => fundamental_constant I A s hs hA X C hC.2⟩
  · rintro ⟨C, ⟨hC, heq⟩, _⟩
    have hY := fundamental_mul I A s hs hA C hC
    refine ⟨hY.1.congr heq, ?_, ?_⟩
    · intro t ht
      have het : X t = U I A t s * C := heq ht
      rw [het]
      exact (hY.2.1 t ht).congr_of_mem heq ht
    · intro t ht
      rw [heq ht]
      exact hY.2.2 t ht

end D13Unified.Ch07.EvolutionMatrix
