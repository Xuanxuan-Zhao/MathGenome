import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.PeriodicForcing
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.Monodromy
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.VariationConstants

noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch08.PeriodicForcing
open Ch07.EvolutionMatrix Ch07.VariationConstants Ch08.Monodromy
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

/-- The variation-of-constants solution with initial value at time zero. -/
def solution : Specs.D13Unified.Ch08.PeriodicForcing.SolutionType :=
  Specs.D13Unified.Ch08.PeriodicForcing.solutionValue

lemma solution_ivp (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂)
    (hA : Continuous A) (hb : Continuous b) (v : Fin n → 𝕂) :
    IsSolution A b (solution A b v) ∧ solution A b v 0 = v ∧
    ∀ x, IsSolution A b x → x 0 = v → x = solution A b v := by
  obtain ⟨hc, hi, hd, hr, hu, _⟩ := variation_of_constants 𝕂 n wholeTime A b 0 v
    (wholeTime_mem 0) hA.continuousOn hb.continuousOn
  refine ⟨⟨contDiffOn_univ.mp hr, fun t => ?_⟩, hi, ?_⟩
  · exact (hd t (wholeTime_mem t)).hasDerivAt (by simp [wholeTime])
  · intro x hx hv
    funext t
    exact hu x hx.1.continuous.continuousOn hv
      (fun r _ => (hx.2 r).hasDerivWithinAt) (wholeTime_mem t)

lemma solution_unique (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂)
    (hA : Continuous A) (hb : Continuous b) {x y : ℝ → Fin n → 𝕂}
    (hx : IsSolution A b x) (hy : IsSolution A b y) (hi : x 0 = y 0) : x = y := by
  obtain ⟨_, _, hu⟩ := solution_ivp A b hA hb (y 0)
  exact (hu x hx hi).trans (hu y hy rfl).symm

lemma periodic_iff_return (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (b : ℝ → Fin n → 𝕂) (hA : Continuous A) (hb : Continuous b)
    (T : ℝ) (hAp : Function.Periodic A T) (hbp : Function.Periodic b T)
    {x : ℝ → Fin n → 𝕂} (hx : IsSolution A b x) :
    Function.Periodic x T ↔ x T = x 0 := by
  constructor
  · intro hp
    simpa using hp 0
  · intro hi
    have hs : IsSolution A b (fun t => x (t + T)) := by
      refine ⟨hx.1.comp (contDiff_id.add contDiff_const), fun t => ?_⟩
      have hd := (hx.2 (t + T)).scomp t ((hasDerivAt_id t).add_const T)
      convert! hd using 1
      simp only [hAp t, hbp t, one_smul]
    have heq := solution_unique A b hA hb hs hx (by simpa using hi)
    exact fun t => congrFun heq t

lemma solution_endpoint (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (b : ℝ → Fin n → 𝕂) (hA : Continuous A) (hb : Continuous b)
    (v : Fin n → 𝕂) (T : ℝ) :
    solution A b v T = monodromy A T *ᵥ
      (v + ∫ r in (0 : ℝ)..T, (principalMatrix A r)⁻¹ *ᵥ b r) := by
  have hf : IsFundamentalMatrixOn wholeTime A (principalMatrix A) :=
    ⟨contDiffOn_U wholeTime A 0 (wholeTime_mem 0) hA.continuousOn,
      fun t _ => (hasDerivAt_U A hA 0 t).hasDerivWithinAt,
      fun t _ => (principal_properties 𝕂 n A hA).2 t⟩
  have hh := (variation_of_constants 𝕂 n wholeTime A b 0 v
    (wholeTime_mem 0) hA.continuousOn hb.continuousOn).2.2.2.2.2
    (principalMatrix A) hf T (wholeTime_mem T)
  have h0 : principalMatrix A 0 = 1 := (principal_properties 𝕂 n A hA).1
  simpa only [solution, Specs.D13Unified.Ch08.PeriodicForcing.solutionValue,
    monodromy, h0, inv_one, Matrix.one_mulVec] using hh

lemma compatible_iff_return (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (b : ℝ → Fin n → 𝕂) (hA : Continuous A) (hb : Continuous b)
    (v : Fin n → 𝕂) (T : ℝ) :
    Specs.D13Unified.Ch08.PeriodicForcing.Compatible A b T v ↔ solution A b v T = v := by
  rw [solution_endpoint A b hA hb v T]
  change (1 - monodromy A T) *ᵥ v = _ ↔ _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add]
  exact sub_eq_iff_eq_add' |>.trans eq_comm

open Specs.D13Unified.Ch08.PeriodicForcing

theorem classical_bridge : ClassicalBridge := by
  intro 𝕂 _ n A b hA hb x
  have heval (t : ℝ) (v : Fin n → 𝕂) :
      (equation A b hA hb).eval t v = A t *ᵥ v + b t := by
    simp [ODE.eval, equation]
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨hc.contDiffOn, fun _ _ => mem_univ _, fun t _ => ?_⟩
    rw [heval]
    exact hd t
  · rintro ⟨hc, _, hd⟩
    refine ⟨contDiffOn_univ.mp hc, fun t => ?_⟩
    simpa only [heval] using hd t (mem_univ t)

theorem initial_value_characterization : InitialValueCharacterization := by
  intro 𝕂 _ n A b T hA hb _ hAp hbp v
  obtain ⟨hs, hi, hu⟩ := solution_ivp A b hA hb v
  refine ⟨hs, hi, ?_, hu⟩
  change Function.Periodic (solution A b v) T ↔ Compatible A b T v
  rw [periodic_iff_return A b hA hb T hAp hbp hs, hi]
  exact (compatible_iff_return A b hA hb v T).symm

theorem periodic_characterization : PeriodicCharacterization := by
  intro 𝕂 _ n A b T hA hb hT hAp hbp x hx
  have hc := initial_value_characterization 𝕂 n A b T hA hb hT hAp hbp (x 0)
  have heq := hc.2.2.2 x hx rfl
  rw [heq]
  simpa only [hc.2.1] using hc.2.2.1

theorem forced_solvability : ForcedSolvability := by
  intro 𝕂 _ n A b T hA hb hT hAp hbp
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x 0, (periodic_characterization 𝕂 n A b T hA hb hT hAp hbp x hx).mp hp⟩
  · rintro ⟨v, hv⟩
    have hc := initial_value_characterization 𝕂 n A b T hA hb hT hAp hbp v
    exact ⟨solution A b v, hc.1, hc.2.2.1.mpr hv⟩

lemma solution_zero (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) : solution A 0 0 = 0 := by
  funext t
  simp [solution, solutionValue]

lemma compatible_zero (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (T : ℝ) (v : Fin n → 𝕂) : Compatible A 0 T v ↔ monodromy A T *ᵥ v = v := by
  change (1 - monodromy A T) *ᵥ v = monodromy A T *ᵥ (∫ r in (0 : ℝ)..T,
    (principalMatrix A r)⁻¹ *ᵥ (0 : ℝ → Fin n → 𝕂) r) ↔ _
  simp only [Pi.zero_apply, Matrix.mulVec_zero, intervalIntegral.integral_zero,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  exact eq_comm

/-- The full homogeneous solution criterion over the original field. -/
lemma homogeneous_fixed (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (T : ℝ) (hA : Continuous A) (hT : 0 < T) (hAp : Function.Periodic A T) :
    (∃ x : ℝ → Fin n → 𝕂, x ≠ 0 ∧ IsSolution A 0 x ∧ Function.Periodic x T) ↔
      ∃ v : Fin n → 𝕂, v ≠ 0 ∧ monodromy A T *ᵥ v = v := by
  constructor
  · rintro ⟨x, hn, hs, hp⟩
    refine ⟨x 0, ?_, (compatible_zero A T (x 0)).mp ?_⟩
    · intro hz
      have heq := (solution_ivp A 0 hA continuous_const 0).2.2 x hs hz
      exact hn (heq.trans (solution_zero A))
    · exact (periodic_characterization 𝕂 n A 0 T hA continuous_const hT hAp
        (fun _ => rfl) x hs).mp hp
  · rintro ⟨v, hn, hv⟩
    have hc := initial_value_characterization 𝕂 n A 0 T hA continuous_const hT hAp
      (fun _ => rfl) v
    refine ⟨solution A 0 v, ?_, hc.1, hc.2.2.1.mpr ((compatible_zero A T v).mpr hv)⟩
    intro hz
    apply hn
    exact hc.2.1.symm.trans (congrFun hz 0)

theorem homogeneous_complex : HomogeneousComplex := by
  intro n A T hA hT hAp
  rw [homogeneous_fixed A T hA hT hAp]
  simpa only [one_smul, monodromy, principalMatrix,
    Specs.D13Unified.Ch08.Monodromy.monodromyValue,
    Specs.D13Unified.Ch08.Monodromy.principalMatrixValue] using
    (multiplier_eigenvalues.1 n A T 1).symm

/-- A real matrix has a nonzero complex fixed vector iff it has a real one.
Projection onto real and imaginary parts ensures a real witness. -/
lemma complex_fixed_iff_real_fixed (M : Matrix (Fin n) (Fin n) ℝ) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ complexify M *ᵥ v = v) ↔
      ∃ v : Fin n → ℝ, v ≠ 0 ∧ M *ᵥ v = v := by
  constructor
  · rintro ⟨v, hn, hv⟩
    have hre : M *ᵥ (fun i => (v i).re) = fun i => (v i).re := by
      ext i
      have h := congrArg Complex.re (congrFun hv i)
      simpa [Matrix.mulVec, dotProduct, complexify, Complex.mul_re] using h
    have him : M *ᵥ (fun i => (v i).im) = fun i => (v i).im := by
      ext i
      have h := congrArg Complex.im (congrFun hv i)
      simpa [Matrix.mulVec, dotProduct, complexify, Complex.mul_im] using h
    by_cases hr : (fun i => (v i).re) = 0
    · refine ⟨fun i => (v i).im, ?_, him⟩
      intro hi
      apply hn
      ext i
      apply Complex.ext
      · exact congrFun hr i
      · exact congrFun hi i
    · exact ⟨_, hr, hre⟩
  · rintro ⟨v, hn, hv⟩
    refine ⟨fun i => (v i : ℂ), ?_, ?_⟩
    · intro hz
      apply hn
      funext i
      exact Complex.ofReal_injective (congrFun hz i)
    · ext i
      have h := congrArg Complex.ofReal (congrFun hv i)
      simpa [Matrix.mulVec, dotProduct, complexify] using h

theorem homogeneous_real : HomogeneousReal := by
  intro n A T hA hT hAp
  rw [homogeneous_fixed A T hA hT hAp]
  have hm : (1 : ℂ) ∈ Specs.D13Unified.Ch08.Monodromy.realFloquetMultipliersValue A T ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧ complexify (monodromy A T) *ᵥ v = v := by
    simpa only [one_smul, complexify, monodromy, principalMatrix,
      Specs.D13Unified.Ch08.Monodromy.complexifyValue,
      Specs.D13Unified.Ch08.Monodromy.monodromyValue,
      Specs.D13Unified.Ch08.Monodromy.principalMatrixValue] using
      (multiplier_eigenvalues.2 n A T 1)
  exact (hm.trans (complex_fixed_iff_real_fixed (monodromy A T))).symm

/-- Nonresonance makes the compatibility equation bijective over the original
field; no complex-valued initial value is introduced for a real equation. -/
lemma unique_of_no_fixed (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (b : ℝ → Fin n → 𝕂) (T : ℝ) (hA : Continuous A) (hb : Continuous b)
    (hT : 0 < T) (hAp : Function.Periodic A T) (hbp : Function.Periodic b T)
    (hno : ¬ ∃ v : Fin n → 𝕂, v ≠ 0 ∧ monodromy A T *ᵥ v = v) :
    ∃! x, IsSolution A b x ∧ Function.Periodic x T := by
  let L : Matrix (Fin n) (Fin n) 𝕂 := 1 - monodromy A T
  have hinj : Function.Injective L.mulVec := by
    intro v w hvw
    have hz : L *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
    have hf : monodromy A T *ᵥ (v - w) = v - w := by
      change (1 - monodromy A T) *ᵥ (v - w) = 0 at hz
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
      exact hz.symm
    have hzero : v - w = 0 := by
      by_contra hn
      exact hno ⟨v - w, hn, hf⟩
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective L.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨v, hv⟩ := hsurj (monodromy A T *ᵥ
    (∫ r in (0 : ℝ)..T, (principalMatrix A r)⁻¹ *ᵥ b r))
  have hv' : Compatible A b T v := hv
  have hc := initial_value_characterization 𝕂 n A b T hA hb hT hAp hbp v
  refine ⟨solution A b v, ⟨hc.1, hc.2.2.1.mpr hv'⟩, ?_⟩
  rintro y ⟨hy, hyp⟩
  have hyc := (periodic_characterization 𝕂 n A b T hA hb hT hAp hbp y hy).mp hyp
  have hi : y 0 = v := hinj (hyc.trans hv'.symm)
  exact hc.2.2.2 y hy hi

theorem unique_complex : UniqueComplex := by
  intro n A b T hA hb hT hAp hbp hno
  apply unique_of_no_fixed A b T hA hb hT hAp hbp
  rintro ⟨v, hn, hv⟩
  apply hno
  exact (multiplier_eigenvalues.1 n A T 1).mpr ⟨v, hn, by
    simpa only [one_smul, complexify, monodromy, principalMatrix,
      Specs.D13Unified.Ch08.Monodromy.complexifyValue,
      Specs.D13Unified.Ch08.Monodromy.monodromyValue,
      Specs.D13Unified.Ch08.Monodromy.principalMatrixValue] using hv⟩

theorem unique_real : UniqueReal := by
  intro n A b T hA hb hT hAp hbp hno
  apply unique_of_no_fixed A b T hA hb hT hAp hbp
  intro hfixed
  obtain ⟨v, hn, hv⟩ := (complex_fixed_iff_real_fixed (monodromy A T)).mpr hfixed
  apply hno
  exact (multiplier_eigenvalues.2 n A T 1).mpr ⟨v, hn, by
    simpa only [one_smul, complexify, monodromy, principalMatrix,
      Specs.D13Unified.Ch08.Monodromy.complexifyValue,
      Specs.D13Unified.Ch08.Monodromy.monodromyValue,
      Specs.D13Unified.Ch08.Monodromy.principalMatrixValue] using hv⟩

end D13Unified.Ch08.PeriodicForcing
