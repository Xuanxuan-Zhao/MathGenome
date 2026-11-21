import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.QuadraticForms
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.LaxMilgram
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate InnerProductSpace
open MeasureTheory TopologicalSpace
universe u v
namespace VariationalNotes.Flux

/-- The same complete gradient structure and topology equivalence already
constructed on the canonical H¹₀ type. -/
theorem gradient_hilbert : QuadraticSpecs.GradientHilbert := Sobolev.slab_hilbert

theorem full_form : QuadraticSpecs.FullForm.{u,v} := Existence.laxMilgram

/-- Derivative of the real quadratic polynomial used on every line. -/
private theorem quadratic_polynomial_derivative (c d e : ℝ) :
    HasDerivAt (fun t : ℝ => c + t * d + t ^ 2 / 2 * e) d 0 := by
  have hid := hasDerivAt_id (0 : ℝ)
  have h := ((hasDerivAt_const (0 : ℝ) c).add (hid.mul_const d)).add
    (((hid.mul hid).div_const 2).mul_const e)
  convert h using 1 <;> simp [sq]
  funext t
  rfl

/-- Riesz in a specified complete inner product structure, with the datum
presented as a function and its linearity and continuity proofs. -/
private theorem riesz_for_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℝ) x, f (c • x) = c • f x) (hcont : Continuous f) :
    ∃! u : E, ∀ v, inner ℝ u v = f v := by
  let L : E →L[ℝ] ℝ :=
    { toFun := f
      map_add' := hadd
      map_smul' := hsmul
      cont := hcont }
  let u := (InnerProductSpace.toDual ℝ E).symm L
  have hu (v : E) : inner ℝ u v = f v :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨u, hu, ?_⟩
  intro w hw
  apply (InnerProductSpace.toDual ℝ E).injective
  apply ContinuousLinearMap.ext
  intro v
  change inner ℝ w v = inner ℝ u v
  rw [hw, hu]

section Forms
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Bundle the Hermitian part using the conjugate transpose bridge from
Lax–Milgram. Boundedness is preserved by addition and scalar multiplication. -/
def hermitianPartForm (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) : H →L⋆[𝕜] H →L[𝕜] 𝕜 :=
  (1 / 2 : 𝕜) • (a + Existence.laxMilgramTestFirst a)

@[simp] theorem hermitianPartForm_apply (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (u v : H) :
    hermitianPartForm a u v = QuadraticSpecs.hermitianPart a u v := by
  simp [hermitianPartForm, QuadraticSpecs.hermitianPart, div_eq_mul_inv, mul_comm]
  ring

theorem hermitianPartForm_hermitian (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (x y : H) :
    hermitianPartForm a x y = conj (hermitianPartForm a y x) := by
  simp [QuadraticSpecs.hermitianPart, map_add, add_comm, RCLike.conj_ofNat]

@[simp] theorem hermitianPartForm_diagonal_re (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (x : H) :
    RCLike.re (hermitianPartForm a x x) = RCLike.re (a x x) := by
  rw [hermitianPartForm_apply, QuadraticSpecs.hermitianPart, ← RCLike.re_eq_add_conj]
  exact RCLike.ofReal_re _

@[simp] theorem hermitianPartForm_energy (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ℓ : H →L[𝕜] 𝕜) (x : H) :
    Existence.Specs.laxMilgramEnergy (hermitianPartForm a) ℓ x =
      Existence.Specs.laxMilgramEnergy a ℓ x := by
  unfold Existence.Specs.laxMilgramEnergy
  rw [hermitianPartForm_diagonal_re]

/-- The energy restricted to a real affine line is an exact quadratic
polynomial. The cross coefficient is the Hermitian part even without symmetry. -/
theorem energy_line (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ℓ : H →L[𝕜] 𝕜)
    (u v : H) (t : ℝ) :
    Existence.Specs.laxMilgramEnergy a ℓ (u + (t : 𝕜) • v) =
      Existence.Specs.laxMilgramEnergy a ℓ u +
        t * RCLike.re (QuadraticSpecs.hermitianPart a u v - ℓ v) +
        t ^ 2 / 2 * RCLike.re (a v v) := by
  have hdiv (z : 𝕜) : RCLike.re (z / 2) = RCLike.re z / 2 := by
    rw [← RCLike.ofReal_ofNat 2, RCLike.div_re_ofReal]
  simp [Existence.Specs.laxMilgramEnergy, QuadraticSpecs.hermitianPart, hdiv,
    map_add, map_smul, add_apply, smul_apply, RCLike.conj_ofReal,
    RCLike.mul_re, RCLike.smul_re]
  ring

/-- A linear test functional vanishes when its real part vanishes on every
test. Scaling a test by the conjugate residual proves this over either field. -/
theorem stationary_iff (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ℓ : H →L[𝕜] 𝕜) (u : H) :
    (∀ v, RCLike.re (QuadraticSpecs.hermitianPart a u v - ℓ v) = 0) ↔
      ∀ v, QuadraticSpecs.hermitianPart a u v = ℓ v := by
  let L := hermitianPartForm a u - ℓ
  have hL (v : H) : L v = QuadraticSpecs.hermitianPart a u v - ℓ v := by
    simp [L]
  constructor
  · intro h v
    have hz := h (conj (L v) • v)
    rw [← hL, L.map_smul, smul_eq_mul, RCLike.conj_mul,
      ← RCLike.ofReal_pow, RCLike.ofReal_re] at hz
    have he : L v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    exact sub_eq_zero.mp ((hL v).symm.trans he)
  · intro h v
    simp [h v]

end Forms

theorem directional_derivative : QuadraticSpecs.DirectionalDerivative.{u,v} := by
  intro 𝕜 H _ _ _ a ℓ u v
  have h := quadratic_polynomial_derivative (Existence.Specs.laxMilgramEnergy a ℓ u)
    (RCLike.re (QuadraticSpecs.hermitianPart a u v - ℓ v)) (RCLike.re (a v v))
  simpa only [energy_line] using h

theorem real_derivative : QuadraticSpecs.RealDerivative.{v} := by
  intro H _ _ a ℓ u v
  simpa [Existence.Specs.laxMilgramEnergy, QuadraticSpecs.hermitianPart] using
    directional_derivative ℝ H a ℓ u v

theorem complex_tests : QuadraticSpecs.ComplexTests.{v} := by
  intro H _ _ a ℓ u v
  have hscale : QuadraticSpecs.hermitianPart a u (Complex.I • v) - ℓ (Complex.I • v) =
      Complex.I * (QuadraticSpecs.hermitianPart a u v - ℓ v) := by
    rw [← hermitianPartForm_apply, ← hermitianPartForm_apply]
    simp [mul_sub]
  rw [hscale, Complex.mul_re]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  constructor
  · rintro ⟨hr, hi⟩
    apply sub_eq_zero.mp
    apply Complex.ext
    · simpa only [Complex.sub_re, Complex.zero_re] using hr
    · simp only [Complex.sub_im, Complex.zero_im] at hi ⊢
      linarith
  · intro h
    simp [h]

theorem part_energy : QuadraticSpecs.PartEnergy.{u,v} := by
  intro 𝕜 H _ _ _ _ a α hα hc ℓ
  have hc' (w : H) : α * ‖w‖ ^ 2 ≤ RCLike.re (hermitianPartForm a w w) := by
    simpa only [hermitianPartForm_diagonal_re] using hc w
  obtain ⟨u, hu, hn, huniq, he⟩ :=
    Existence.laxMilgram 𝕜 H (hermitianPartForm a) α hα hc' ℓ
  obtain ⟨hdiag, hiff, hex⟩ := he (hermitianPartForm_hermitian a)
  refine ⟨?_, ?_, stationary_iff a ℓ⟩
  · intro w
    simpa only [hermitianPartForm_apply, hermitianPartForm_energy] using (hiff w).symm
  · simpa only [hermitianPartForm_energy] using hex

/-- A bounded positive-dimensional domain lies in a coordinate strip, with
no boundary regularity or nonemptiness assumption. -/
theorem bounded_coordinate_strip {n : ℕ} (Ω : Opens (Sobolev.Domain (n+1)))
    (hΩ : Bornology.IsBounded (Ω : Set (Sobolev.Domain (n+1)))) :
    ∃ a b : ℝ, a < b ∧ Sobolev.InCoordinateStrip Ω 0 a b := by
  obtain ⟨R, hR, hbound⟩ := hΩ.exists_pos_norm_lt
  refine ⟨-R, R, by linarith, ?_⟩
  intro x hx
  have hb := (PiLp.norm_apply_le x (0 : Fin (n+1))).trans_lt (hbound x hx)
  rw [Real.norm_eq_abs, abs_lt] at hb
  exact hb

/-- Riesz representation for the gradient inner product. The new norm and
inner product are exactly an upstream slab_hilbert witness; its topology
identity transports the original continuous datum. -/
theorem gradient_riesz : QuadraticSpecs.GradientRiesz := by
  intro n m Ω hΩ ℓ
  let f : Sobolev.H1Zero Ω m → ℝ := ℓ
  have hfadd (x y : Sobolev.H1Zero Ω m) : f (x + y) = f x + f y := ℓ.map_add x y
  have hfsmul (c : ℝ) (x : Sobolev.H1Zero Ω m) : f (c • x) = c • f x := ℓ.map_smul c x
  have hfcont : Continuous f := ℓ.continuous
  obtain ⟨a, b, hab, hs⟩ := bounded_coordinate_strip Ω hΩ
  obtain ⟨N, I, hAdd, hsmul, hcomplete, htop, hnorm, hinner⟩ :=
    Sobolev.slab_hilbert Ω 0 a b hab hs
  have hnewadd (x y : Sobolev.H1Zero Ω m) :
      f (@Add.add _ N.toAdd x y) = f x + f y := by
    have hxy := congrArg (fun S : AddCommGroup (Sobolev.H1Zero Ω m) =>
      @Add.add _ S.toAdd x y) hAdd
    rw [hxy]
    exact hfadd x y
  have hnewsmul (c : ℝ) (x : Sobolev.H1Zero Ω m) :
      f (@SMul.smul _ _ I.toSMul c x) = c • f x := by
    rw [hsmul]
    exact hfsmul c x
  have hnewcont : @Continuous _ ℝ N.toUniformSpace.toTopologicalSpace _ f := by
    rw [htop]
    exact hfcont
  have hr := @riesz_for_inner (Sobolev.H1Zero Ω m) N I hcomplete f hnewadd hnewsmul hnewcont
  simpa only [hinner, QuadraticSpecs.gradientPairing] using hr

end VariationalNotes.Flux
