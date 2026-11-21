import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClosedMatrixGroups
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Commutator
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Topology Filter
open scoped Manifold ContDiff

namespace LieAlgebrasAndRepresentations.ClosedMatrixGroups

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

@[simp] theorem coe_expUnit (X : A) : (expUnit X : A) = NormedSpace.exp X := rfl

@[simp] theorem expUnit_zero : expUnit (0 : A) = 1 := by
  apply Units.ext
  exact NormedSpace.exp_zero

@[simp] theorem coe_expUnit_inv (X : A) :
    ((expUnit X)⁻¹ : Aˣ).val = NormedSpace.exp (-X) := by
  letI := NormedSpace.invertibleExp X
  change ⅟(NormedSpace.exp X) = _
  exact NormedSpace.invOf_exp X

theorem continuous_expUnit : Continuous (expUnit : A → Aˣ) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact NormedSpace.exp_continuous
  · exact NormedSpace.exp_continuous.comp continuous_neg

@[simp] theorem zero_mem_velocities (H : Subgroup Aˣ) : (0 : A) ∈ velocities H := by
  intro t
  simp only [smul_zero, expUnit_zero, H.one_mem]

theorem smul_mem_velocities (H : Subgroup Aˣ) {X : A}
    (hX : X ∈ velocities H) (c : ℝ) : c • X ∈ velocities H := by
  intro t
  simpa only [smul_smul] using hX (t * c)

theorem neg_mem_velocities (H : Subgroup Aˣ) {X : A}
    (hX : X ∈ velocities H) : -X ∈ velocities H := by
  simpa only [neg_one_smul] using smul_mem_velocities H hX (-1)

theorem velocities_closed (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) :
    IsClosed (velocities H) := by
  have heq : velocities H = ⋂ t : ℝ, (fun X : A => expUnit (t • X)) ⁻¹' (H : Set Aˣ) := by
    ext X
    simp [velocities]
  rw [heq]
  exact isClosed_iInter fun t => hH.preimage
    (continuous_expUnit.comp (continuous_const_smul t))

theorem expUnit_add_of_commute {X Y : A} (hXY : Commute X Y) :
    expUnit (X + Y) = expUnit X * expUnit Y := by
  apply Units.ext
  exact NormedSpace.exp_add_of_commute hXY

theorem add_mem_velocities_of_commute (H : Subgroup Aˣ) {X Y : A}
    (hX : X ∈ velocities H) (hY : Y ∈ velocities H) (hXY : Commute X Y) :
    X + Y ∈ velocities H := by
  intro t
  rw [smul_add, expUnit_add_of_commute ((hXY.smul_left t).smul_right t)]
  exact H.mul_mem (hX t) (hY t)

theorem expUnit_conj (g : Aˣ) (X : A) :
    expUnit ((g : A) * X * (g⁻¹ : Aˣ)) = g * expUnit X * g⁻¹ := by
  apply Units.ext
  exact NormedSpace.exp_units_conj g X

theorem conj_mem_velocities (H : Subgroup Aˣ) {X : A}
    (hX : X ∈ velocities H) (g : H) :
    (g.val : A) * X * (g.val⁻¹ : Aˣ) ∈ velocities H := by
  intro t
  have heq : t • ((g.val : A) * X * (g.val⁻¹ : Aˣ)) =
      (g.val : A) * (t • X) * (g.val⁻¹ : Aˣ) := by
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [heq, expUnit_conj]
  exact H.mul_mem (H.mul_mem g.property (hX t)) (H.inv_mem g.property)

theorem hasDerivAt_exp_smul_zero (X : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
  have hexp : HasFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) ((0 : ℝ) • X) := by
    simpa using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
  simpa [Function.comp_def] using
    hexp.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const X)

/-- Exponentiation converts natural scalar multiples to powers. -/
theorem expUnit_nsmul (n : ℕ) (X : A) : expUnit (n • X) = expUnit X ^ n := by
  apply Units.ext
  exact NormedSpace.exp_nsmul n X

/-- The exponential has identity strict derivative at zero, in the form
needed by the inverse function theorem. -/
private theorem exp_strict_deriv :
    HasStrictFDerivAt (NormedSpace.exp : A → A)
      (ContinuousLinearEquiv.refl ℝ A : A →L[ℝ] A) 0 := by
  exact hasStrictFDerivAt_exp_zero

/-- A local logarithm, defined using the Banach inverse function theorem.
Only its germ at one is used. -/
def localLog : A → A :=
  exp_strict_deriv.localInverse NormedSpace.exp (ContinuousLinearEquiv.refl ℝ A) 0

@[simp] theorem localLog_one : localLog (1 : A) = 0 := by
  unfold localLog
  convert (exp_strict_deriv (A := A)).localInverse_apply_image using 1 <;>
    simp only [NormedSpace.exp_zero]

theorem hasFDerivAt_localLog_one :
    HasFDerivAt (localLog : A → A) (1 : A →L[ℝ] A) 1 := by
  unfold localLog
  convert (exp_strict_deriv (A := A)).to_localInverse.hasFDerivAt using 1 <;>
    first | rfl | simp only [NormedSpace.exp_zero]

theorem eventually_expUnit_localLog :
    ∀ᶠ g : Aˣ in 𝓝 1, expUnit (localLog (g : A)) = g := by
  have h := (exp_strict_deriv (A := A)).eventually_right_inverse
  rw [NormedSpace.exp_zero] at h
  have hc : Tendsto (fun g : Aˣ => (g : A)) (𝓝 1) (𝓝 (1 : A)) :=
    Units.continuous_val.continuousAt
  filter_upwards [hc.eventually h] with g hg
  exact Units.ext hg

/-- Smooth exponential coordinates at the identity, with an ambient
smooth extension of the forward coordinates. The inverse is the actual
matrix exponential, including outside the chart target. -/
structure ExponentialChart (H : Subgroup Aˣ) (S : LieSubalgebra ℝ A) where
  chart : OpenPartialHomeomorph H S
  one_mem : (1 : H) ∈ chart.source
  chart_one : chart 1 = 0
  coordinateExtension : A → S
  coordinate_eq : ∀ h ∈ chart.source, chart h = coordinateExtension ((h : Aˣ) : A)
  coordinate_smooth : ∀ h ∈ chart.source,
    ContDiffAt ℝ ∞ coordinateExtension ((h : Aˣ) : A)
  inverse_eq : ∀ X : S, (((chart.symm X : H) : Aˣ) : A) = NormedSpace.exp (X : A)

theorem analyticAt_localLog_one : AnalyticAt ℝ (localLog : A → A) 1 := by
  let E := (exp_strict_deriv (A := A)).toOpenPartialHomeomorph NormedSpace.exp
  have h := E.analyticAt_symm'
    (exp_strict_deriv (A := A)).mem_toOpenPartialHomeomorph_source
    (NormedSpace.exp_analytic (𝕂 := ℝ) (0 : A))
    (exp_strict_deriv (A := A)).hasFDerivAt.fderiv
  change AnalyticAt ℝ localLog (NormedSpace.exp (0 : A)) at h
  simpa only [NormedSpace.exp_zero] using h

/-- Every differentiable curve through one has its exponential as its
Euler power limit. This proves the product formula without estimates of
noncommutative remainders. -/
theorem tendsto_curve_pow_expUnit (f : ℝ → Aˣ) (X : A) (hf0 : f 0 = 1)
    (hf : HasDerivAt (fun t => (f t : A)) X 0)
    (hfc : ContinuousAt f 0) :
    Filter.Tendsto (fun n : ℕ => f ((n + 1 : ℝ)⁻¹) ^ (n + 1))
      Filter.atTop (𝓝 (expUnit X)) := by
  have hd : HasDerivAt (fun t => localLog (f t : A)) X 0 := by
    have hL := hasFDerivAt_localLog_one (A := A)
    have hf0val : (f 0 : A) = 1 := by rw [hf0, Units.val_one]
    rw [← hf0val] at hL
    simpa only [Function.comp_def, one_apply_eq_self] using hL.comp_hasDerivAt 0 hf
  have hn : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹)
      Filter.atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
        tendsto_const_nhds)
    · exact Filter.Eventually.of_forall (fun n => inv_ne_zero (by positivity))
  have hs := hd.tendsto_slope_zero.comp hn
  have he : Filter.Tendsto
      (fun n : ℕ => expUnit ((n + 1) • localLog (f ((n + 1 : ℝ)⁻¹) : A)))
      Filter.atTop (𝓝 (expUnit X)) := by
    have he := continuous_expUnit.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, hf0, Units.val_one, localLog_one, sub_zero, zero_add,
      inv_inv, ← Nat.cast_add_one, Nat.cast_smul_eq_nsmul] using he
  have hfn : Filter.Tendsto (fun n : ℕ => f ((n + 1 : ℝ)⁻¹))
      Filter.atTop (𝓝 (1 : Aˣ)) := by
    rw [← hf0]
    exact hfc.tendsto.comp (hn.mono_right nhdsWithin_le_nhds)
  apply he.congr'
  filter_upwards [hfn.eventually eventually_expUnit_localLog] with n hn
  rw [expUnit_nsmul, hn]

/-- The Lie product formula in a real Banach algebra. -/
theorem tendsto_expUnit_add (X Y : A) :
    Filter.Tendsto
      (fun n : ℕ => (expUnit ((n + 1 : ℝ)⁻¹ • X) *
        expUnit ((n + 1 : ℝ)⁻¹ • Y)) ^ (n + 1))
      Filter.atTop (𝓝 (expUnit (X + Y))) := by
  apply tendsto_curve_pow_expUnit (fun t => expUnit (t • X) * expUnit (t • Y))
  · simp
  · convert (hasDerivAt_exp_smul_zero X).mul (hasDerivAt_exp_smul_zero Y) using 1 <;>
      simp only [Units.val_mul, coe_expUnit, zero_smul, NormedSpace.exp_zero, mul_one, one_mul]
    rfl
  · exact ((continuous_expUnit.comp (continuous_id.smul continuous_const)).mul
      (continuous_expUnit.comp (continuous_id.smul continuous_const))).continuousAt

/-- Closedness of the subgroup supplies the passage to the product limit. -/
theorem add_mem_velocities (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ))
    {X Y : A} (hX : X ∈ velocities H) (hY : Y ∈ velocities H) :
    X + Y ∈ velocities H := by
  intro t
  rw [smul_add]
  apply hH.mem_of_tendsto (tendsto_expUnit_add (t • X) (t • Y))
  exact Filter.Eventually.of_forall fun n => H.pow_mem
    (H.mul_mem (by simpa only [smul_smul] using hX ((n + 1 : ℝ)⁻¹ * t))
      (by simpa only [smul_smul] using hY ((n + 1 : ℝ)⁻¹ * t))) (n + 1)

/-- Bracket closure follows from addition closure using conjugation and
closedness. This avoids a separate second-order commutator product limit. -/
theorem lie_mem_velocities_of_add (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ))
    (hadd : ∀ X ∈ velocities H, ∀ Y ∈ velocities H, X + Y ∈ velocities H)
    {X Y : A} (hX : X ∈ velocities H) (hY : Y ∈ velocities H) :
    ⁅X, Y⁆ ∈ velocities H := by
  let F : ℝ → A := fun t =>
    NormedSpace.exp (t • X) * Y * NormedSpace.exp (t • (-X))
  have hF (t : ℝ) : F t ∈ velocities H := by
    have hc := conj_mem_velocities H hY (⟨expUnit (t • X), hX t⟩ : H)
    simpa only [F, coe_expUnit, coe_expUnit_inv, smul_neg] using hc
  have hd : HasDerivAt F ⁅X, Y⁆ 0 := by
    have hd := ((hasDerivAt_exp_smul_zero X).mul_const Y).mul
      (hasDerivAt_exp_smul_zero (-X))
    convert hd using 1 <;>
      simp [F, NormedSpace.exp_zero, LieRing.of_associative_ring_bracket,
        sub_eq_add_neg]
  apply (velocities_closed H hH).mem_of_tendsto hd.tendsto_slope_zero
  exact Filter.Eventually.of_forall fun t => smul_mem_velocities H
    (by simpa only [sub_eq_add_neg] using
      hadd (F (0 + t)) (hF (0 + t)) (-F 0) (neg_mem_velocities H (hF 0))) t⁻¹

/-- Once the noncommutative addition limit is established, all remaining
Lie subalgebra axioms are discharged by the proved lemmas above. -/
def lieSubalgebraOfAdd (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ))
    (hadd : ∀ X ∈ velocities H, ∀ Y ∈ velocities H, X + Y ∈ velocities H) :
    LieSubalgebra ℝ A where
  carrier := velocities H
  zero_mem' := zero_mem_velocities H
  add_mem' := fun hX hY => hadd _ hX _ hY
  smul_mem' := fun c _ hX => smul_mem_velocities H hX c
  lie_mem' := fun hX hY => lie_mem_velocities_of_add H hH hadd hX hY

/-- The velocity set itself, with no additional algebraic hypotheses. -/
def velocityLieSubalgebra (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) :
    LieSubalgebra ℝ A :=
  lieSubalgebraOfAdd H hH (fun _ hX _ hY => add_mem_velocities H hH hX hY)

@[simp] theorem coe_velocityLieSubalgebra (H : Subgroup Aˣ)
    (hH : IsClosed (H : Set Aˣ)) :
    (velocityLieSubalgebra H hH : Set A) = velocities H := rfl

theorem velocities_lieSubalgebra (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) :
    ∃ S : LieSubalgebra ℝ A, (S : Set A) = velocities H ∧ IsClosed (S : Set A) :=
  ⟨velocityLieSubalgebra H hH, rfl, velocities_closed H hH⟩

/-- Every tangent vector of a differentiable curve in H is a velocity.
Only membership near zero is required. -/
theorem tangent_mem_velocities (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ))
    (f : ℝ → Aˣ) (X : A) (hf0 : f 0 = 1)
    (hf : HasDerivAt (fun t => (f t : A)) X 0)
    (hfc : ContinuousAt f 0) (hmem : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ H) :
    X ∈ velocities H := by
  intro t
  let g : ℝ → Aˣ := fun s => f (s * t)
  have hg0 : g 0 = 1 := by simpa only [g, zero_mul] using hf0
  have hgd : HasDerivAt (fun s => (g s : A)) (t • X) 0 := by
    have hd := hf.scomp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).mul_const t) (by simp)
    simpa only [Function.comp_def, id_eq, one_mul, g] using hd
  have hgc : ContinuousAt g 0 := by
    exact hfc.comp_of_eq ((continuousAt_id).mul continuousAt_const) (by simp)
  have hgmem : ∀ᶠ s in 𝓝 (0 : ℝ), g s ∈ H := by
    have hm : ContinuousAt (fun s : ℝ => s * t) 0 := continuousAt_id.mul continuousAt_const
    have hm' : Tendsto (fun s : ℝ => s * t) (𝓝 0) (𝓝 0) := by simpa using hm.tendsto
    exact hm'.eventually hmem
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  exact hH.mem_of_tendsto (tendsto_curve_pow_expUnit g (t • X) hg0 hgd hgc)
    ((hn.eventually hgmem).mono fun n hn => H.pow_mem hn (n + 1))

/-- Limits of normalized small logarithms are velocities. This is the
compactness input for the exclusion of transverse subgroup elements. -/
theorem normalized_limit_mem_velocities (H : Subgroup Aˣ)
    (hH : IsClosed (H : Set Aˣ)) (Z : ℕ → A) (Y : A)
    (hZ0 : ∀ n, Z n ≠ 0) (hZ : Tendsto Z atTop (𝓝 0))
    (hm : ∀ n, expUnit (Z n) ∈ H)
    (hY : Tendsto (fun n => ‖Z n‖⁻¹ • Z n) atTop (𝓝 Y)) :
    Y ∈ velocities H := by
  have hnorm : Tendsto (fun n => ‖Z n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hZ.norm
  have hpos (n : ℕ) : 0 < ‖Z n‖ := norm_pos_iff.mpr (hZ0 n)
  have hnonneg (t : ℝ) (ht : 0 ≤ t) : expUnit (t • Y) ∈ H := by
    let m : ℕ → ℕ := fun n => ⌊t / ‖Z n‖⌋₊
    have hscale : Tendsto (fun n => (m n : ℝ) * ‖Z n‖) atTop (𝓝 t) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (show Tendsto (fun n => t - ‖Z n‖) atTop (𝓝 t) by
          simpa only [sub_zero] using tendsto_const_nhds.sub hnorm) tendsto_const_nhds
      · exact Eventually.of_forall fun n => by
          have hfloor := Nat.lt_floor_add_one (t / ‖Z n‖)
          have hdiv : t / ‖Z n‖ * ‖Z n‖ = t := div_mul_cancel₀ _ (hpos n).ne'
          have := (mul_lt_mul_of_pos_right hfloor (hpos n)).le
          dsimp [m]
          nlinarith
      · exact Eventually.of_forall fun n => by
          have hfloor := Nat.floor_le (div_nonneg ht (hpos n).le)
          exact (le_div_iff₀ (hpos n)).mp hfloor
    have hsmul : Tendsto (fun n => (m n) • Z n) atTop (𝓝 (t • Y)) := by
      convert hscale.smul hY using 1
      ext n
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hpos n).ne', mul_one,
        Nat.cast_smul_eq_nsmul]
    apply hH.mem_of_tendsto (continuous_expUnit.continuousAt.tendsto.comp hsmul)
    exact Eventually.of_forall fun n => by
      change expUnit (m n • Z n) ∈ H
      rw [expUnit_nsmul]
      exact H.pow_mem (hm n) (m n)
  intro t
  rcases le_total 0 t with ht | ht
  · exact hnonneg t ht
  · have h := H.inv_mem (hnonneg (-t) (neg_nonneg.mpr ht))
    convert h using 1
    apply Units.ext
    simp only [coe_expUnit, coe_expUnit_inv, neg_smul, neg_neg]

/-- A transverse vector subspace has no arbitrarily small nonzero
vectors whose exponentials lie in H. -/
theorem exists_exponential_transverse_radius [FiniteDimensional ℝ A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) (M : Submodule ℝ A)
    (hM : Disjoint (velocityLieSubalgebra H hH).toSubmodule M) :
    ∃ r : ℝ, 0 < r ∧ ∀ Y : M, ‖Y‖ < r → expUnit (Y : A) ∈ H → Y = 0 := by
  by_contra h
  push_neg at h
  choose Z hZn hZH hZ0 using fun n : ℕ => h ((n + 1 : ℝ)⁻¹) (by positivity)
  have hZ : Tendsto Z atTop (𝓝 (0 : M)) := by
    apply squeeze_zero_norm (fun n => (hZn n).le)
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hunit (n : ℕ) : ‖Z n‖⁻¹ • Z n ∈ Metric.sphere (0 : M) 1 := by
    rw [mem_sphere_zero_iff_norm]
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hZ0 n))]
  obtain ⟨Y, hYn, φ, hφ, hlim⟩ := (isCompact_sphere (0 : M) 1).tendsto_subseq hunit
  have hY : (Y : A) ∈ velocities H := by
    apply normalized_limit_mem_velocities H hH (fun n => (Z (φ n) : A)) (Y : A)
    · intro n
      exact Subtype.coe_ne_coe.mpr (hZ0 (φ n))
    · exact (continuous_subtype_val.tendsto (0 : M)).comp (hZ.comp hφ.tendsto_atTop)
    · exact fun n => hZH (φ n)
    · exact (continuous_subtype_val.tendsto Y).comp hlim
  have hzero : Y = 0 := (Submodule.mem_left_iff_eq_zero_of_disjoint hM).mp hY
  simpa [hzero] using hYn

/-- The product-exponential map has invertible derivative along any
pair of complementary real subspaces. -/
theorem hasStrictFDerivAt_exp_mul [FiniteDimensional ℝ A]
    (S M : Submodule ℝ A) (hSM : IsCompl S M) :
    HasStrictFDerivAt
      (fun p : S × M => NormedSpace.exp (p.1 : A) * NormedSpace.exp (p.2 : A))
      ((S.prodEquivOfIsCompl M hSM).toContinuousLinearEquiv : (S × M) →L[ℝ] A) 0 := by
  let L₁ : (S × M) →L[ℝ] A := S.subtypeL.comp (ContinuousLinearMap.fst ℝ S M)
  let L₂ : (S × M) →L[ℝ] A := M.subtypeL.comp (ContinuousLinearMap.snd ℝ S M)
  have h₁ : HasStrictFDerivAt (fun p : S × M => NormedSpace.exp (p.1 : A)) L₁ 0 := by
    convert (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)).comp 0 L₁.hasStrictFDerivAt using 1 <;>
      simp [L₁]
    apply ContinuousLinearMap.ext
    intro p
    rfl
  have h₂ : HasStrictFDerivAt (fun p : S × M => NormedSpace.exp (p.2 : A)) L₂ 0 := by
    convert (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)).comp 0 L₂.hasStrictFDerivAt using 1 <;>
      simp [L₂]
    apply ContinuousLinearMap.ext
    intro p
    rfl
  convert h₁.mul' h₂ using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [L₁, L₂, add_comm, Submodule.coe_prodEquivOfIsCompl']

/-- The exponentials of velocities contain an identity neighborhood in H.
This is proved in the original subgroup topology. -/
theorem exponential_image_mem_nhds [FiniteDimensional ℝ A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ))
    (U : Set (velocityLieSubalgebra H hH)) (hU : U ∈ 𝓝 0) :
    (expIn H) '' U ∈ 𝓝 (1 : H) := by
  let S := (velocityLieSubalgebra H hH).toSubmodule
  obtain ⟨M, hSM⟩ := S.exists_isCompl
  obtain ⟨r, hr, hMr⟩ := exists_exponential_transverse_radius H hH M hSM.disjoint
  let F : (S × M) → A := fun p => NormedSpace.exp (p.1 : A) * NormedSpace.exp (p.2 : A)
  let e : (S × M) ≃L[ℝ] A := (S.prodEquivOfIsCompl M hSM).toContinuousLinearEquiv
  have hd : HasStrictFDerivAt F (e : (S × M) →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_mul S M hSM
  let G := hd.localInverse F e 0
  have hF0 : F 0 = 1 := by simp [F]
  have hG1 : G 1 = 0 := by
    simpa only [hF0] using hd.localInverse_apply_image
  have hGi : ∀ᶠ g in 𝓝 (1 : A), F (G g) = g := by
    simpa only [hF0] using hd.eventually_right_inverse
  have hGc : ContinuousAt G (1 : A) := by
    simpa only [hF0] using hd.localInverse_continuousAt
  have hGr : ∀ᶠ g in 𝓝 (1 : A), ‖(G g).2‖ < r := by
    have hc := hGc.snd.norm
    have hm : Set.Iio r ∈ 𝓝 ‖(G 1).2‖ := by simpa [hG1] using Iio_mem_nhds hr
    exact hc.tendsto.eventually hm
  have hGU : ∀ᶠ g in 𝓝 (1 : A), (G g).1 ∈ U := by
    have hc := hGc.fst
    have hm : U ∈ 𝓝 (G 1).1 := by simpa only [hG1, Prod.fst_zero] using hU
    exact hc.tendsto.eventually hm
  have hval : Tendsto (fun g : H => ((g : Aˣ) : A)) (𝓝 (1 : H)) (𝓝 (1 : A)) :=
    (Units.continuous_val.comp continuous_subtype_val).continuousAt
  filter_upwards [hval.eventually hGi, hval.eventually hGr, hval.eventually hGU] with g hgi hgr hgu
  let p := G ((g : Aˣ) : A)
  have hX : expUnit (p.1 : A) ∈ H := by
    simpa only [one_smul] using (p.1.property : (p.1 : A) ∈ velocities H) (1 : ℝ)
  have hp : expUnit (p.1 : A) * expUnit (p.2 : A) = (g : Aˣ) := by
    apply Units.ext
    exact hgi
  have hY : expUnit (p.2 : A) ∈ H := by
    apply (H.mul_mem_cancel_left hX).mp
    rw [hp]
    exact g.property
  have hp2 : p.2 = 0 := hMr p.2 hgr hY
  refine ⟨⟨(p.1 : A), p.1.property⟩, hgu, ?_⟩
  apply Subtype.ext
  change expUnit (p.1 : A) = (g : Aˣ)
  simpa only [hp2, Submodule.coe_zero, expUnit_zero, mul_one] using hp

theorem exponential_range_mem_nhds [FiniteDimensional ℝ A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) :
    Set.range (expIn H) ∈ 𝓝 (1 : H) := by
  simpa only [Set.image_univ] using exponential_image_mem_nhds H hH Set.univ (by simp)

theorem eventually_localLog_mem_velocities [FiniteDimensional ℝ A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) :
    ∀ᶠ h : H in 𝓝 1, localLog ((h : Aˣ) : A) ∈ velocities H := by
  let E := (exp_strict_deriv (A := A)).toOpenPartialHomeomorph NormedSpace.exp
  let S := velocityLieSubalgebra H hH
  let U : Set S := (fun X : S => (X : A)) ⁻¹' E.source
  have hU : U ∈ 𝓝 (0 : S) := by
    apply continuous_subtype_val.continuousAt.preimage_mem_nhds
    exact E.open_source.mem_nhds (exp_strict_deriv (A := A)).mem_toOpenPartialHomeomorph_source
  filter_upwards [exponential_image_mem_nhds H hH U hU] with h hh
  obtain ⟨X, hX, rfl⟩ := hh
  have hi : localLog (NormedSpace.exp (X : A)) = (X : A) := E.left_inv hX
  change localLog (NormedSpace.exp (X : A)) ∈ velocities H
  rw [hi]
  exact X.property

/-- The source's local exponential coordinates in the inherited topology. -/
theorem nonempty_exponentialChart [FiniteDimensional ℝ A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) :
    Nonempty (ExponentialChart H (velocityLieSubalgebra H hH)) := by
  let S := velocityLieSubalgebra H hH
  obtain ⟨M, hSM⟩ := S.toSubmodule.exists_isCompl
  let e := (S.toSubmodule.prodEquivOfIsCompl M hSM).toContinuousLinearEquiv
  let P : A →L[ℝ] S := (ContinuousLinearMap.fst ℝ S M).comp e.symm.toContinuousLinearMap
  have hP (X : S) : P (X : A) = X := by
    change ((S.toSubmodule.prodEquivOfIsCompl M hSM).symm (X : A)).1 = X
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  let q : A → S := fun a => P (localLog a)
  let E := (exp_strict_deriv (A := A)).toOpenPartialHomeomorph NormedSpace.exp
  have hval : Tendsto (fun h : H => ((h : Aˣ) : A)) (𝓝 (1 : H)) (𝓝 (1 : A)) :=
    (Units.continuous_val.comp continuous_subtype_val).continuousAt
  have htarget : E.target ∈ 𝓝 (1 : A) := by
    apply E.open_target.mem_nhds
    simpa only [NormedSpace.exp_zero] using
      (exp_strict_deriv (A := A)).image_mem_toOpenPartialHomeomorph_target
  have hnear : ∀ᶠ h : H in 𝓝 1,
      ((h : Aˣ) : A) ∈ E.target ∧
      localLog ((h : Aˣ) : A) ∈ velocities H ∧
      AnalyticAt ℝ (localLog : A → A) ((h : Aˣ) : A) :=
    (hval.eventually htarget).and ((eventually_localLog_mem_velocities H hH).and
      (hval.eventually (analyticAt_localLog_one (A := A)).eventually_analyticAt))
  obtain ⟨W, hW, hoW, h1W⟩ := mem_nhds_iff.mp hnear
  have hlog (h : H) (hh : h ∈ W) : (q ((h : Aˣ) : A) : A) = localLog ((h : Aˣ) : A) := by
    let X : S := ⟨localLog ((h : Aˣ) : A), (hW hh).2.1⟩
    exact congrArg Subtype.val (hP X)
  have hleft (h : H) (hh : h ∈ W) : expIn H (q ((h : Aˣ) : A)) = h := by
    apply Subtype.ext
    apply Units.ext
    change NormedSpace.exp (q ((h : Aˣ) : A) : A) = ((h : Aˣ) : A)
    rw [hlog h hh]
    exact E.right_inv (hW hh).1
  let U : Set S := {X | (X : A) ∈ E.source ∧ expIn H X ∈ W}
  have hright (X : S) (hX : X ∈ U) : q (((expIn H X : H) : Aˣ) : A) = X := by
    change P (localLog (NormedSpace.exp (X : A))) = X
    rw [show localLog (NormedSpace.exp (X : A)) = (X : A) from E.left_inv hX.1, hP]
  let c : OpenPartialHomeomorph H S :=
    { toFun := fun h => q ((h : Aˣ) : A)
      invFun := expIn H
      source := W
      target := U
      map_source' := by
        intro h hh
        exact ⟨by rw [hlog h hh]; exact E.map_target (hW hh).1, by rw [hleft h hh]; exact hh⟩
      map_target' := fun X hX => hX.2
      left_inv' := hleft
      right_inv' := hright
      open_source := hoW
      open_target := (E.open_source.preimage continuous_subtype_val).inter
        (hoW.preimage (by
          apply Continuous.subtype_mk
          exact continuous_expUnit.comp continuous_subtype_val))
      continuousOn_toFun := by
        intro h hh
        have hcq : ContinuousAt q ((h : Aˣ) : A) :=
          P.continuous.continuousAt.comp (hW hh).2.2.continuousAt
        have hcc0 : ContinuousAt (fun h : H => ((h : Aˣ) : A)) h :=
          (Units.continuous_val.comp continuous_subtype_val).continuousAt
        have hcc : ContinuousAt (fun h : H => q ((h : Aˣ) : A)) h :=
          ContinuousAt.comp (f := fun h : H => ((h : Aˣ) : A)) (x := h) hcq hcc0
        exact hcc.continuousWithinAt
      continuousOn_invFun := by
        apply Continuous.continuousOn
        apply Continuous.subtype_mk
        exact continuous_expUnit.comp continuous_subtype_val }
  apply Nonempty.intro
  refine {
    chart := c
    one_mem := h1W
    chart_one := ?_
    coordinateExtension := q
    coordinate_eq := fun _ _ => rfl
    coordinate_smooth := ?_
    inverse_eq := fun _ => rfl }
  · change P (localLog (1 : A)) = 0
    rw [localLog_one, map_zero]
  · intro h hh
    exact P.contDiff.contDiffAt.comp _ (hW hh).2.2.contDiffAt

private instance ambientContMDiffMul : ContMDiffMul 𝓘(ℝ, A) ∞ A := by
  constructor
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact contDiff_mul.contMDiff

namespace ExponentialChart

variable {H : Subgroup Aˣ} {S : LieSubalgebra ℝ A} (C : ExponentialChart H S)

/-- Translate the exponential chart by left multiplication. -/
def translated (g : H) : OpenPartialHomeomorph H S :=
  (Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph.trans C.chart

theorem translated_apply (g h : H) : C.translated g h = C.chart (g⁻¹ * h) := rfl

theorem translated_symm_coe (g : H) (X : S) :
    ((((C.translated g).symm X : H) : Aˣ) : A) =
      ((g : Aˣ) : A) * NormedSpace.exp (X : A) := by
  change (((g * C.chart.symm X : H) : Aˣ) : A) = _
  rw [Subgroup.coe_mul, Units.val_mul, C.inverse_eq]

/-- The translated charts use the topology already present on H. -/
def chartedSpace : ChartedSpace S H where
  atlas := Set.range C.translated
  chartAt := C.translated
  mem_chart_source g := by
    change g ∈ Set.univ ∧ g⁻¹ * g ∈ C.chart.source
    simpa only [Set.mem_univ, inv_mul_cancel, true_and] using C.one_mem
  chart_mem_atlas g := ⟨g, rfl⟩

theorem chart_self (g : H) : C.translated g g = 0 := by
  rw [C.translated_apply, inv_mul_cancel, C.chart_one]

/-- Smoothness of the changes of exponential coordinates. -/
theorem isManifold : letI := C.chartedSpace; IsManifold 𝓘(ℝ, S) ∞ H := by
  letI := C.chartedSpace
  apply isManifold_of_contDiffOn 𝓘(ℝ, S) ∞ H
  rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
  simp only [modelWithCornersSelf_coe, Function.id_comp, Function.comp_id,
    Set.preimage_id, Set.range_id, Set.inter_univ]
  intro X hX
  have hX' : X ∈ (C.translated g).target ∧
      (C.translated g).symm X ∈ (C.translated h).source := hX
  let f : S → H := fun Z => h⁻¹ * (C.translated g).symm Z
  have hfc : ContinuousAt f X := continuousAt_const.mul
    ((C.translated g).continuousAt_symm hX'.1)
  have hfmem : f X ∈ C.chart.source := hX'.2.2
  have hfv : (fun Z : S => ((f Z : Aˣ) : A)) =
      fun Z : S => ((h⁻¹ : H) : Aˣ).val * (((g : Aˣ) : A) * NormedSpace.exp (Z : A)) := by
    funext Z
    change (((h⁻¹ * (C.translated g).symm Z : H) : Aˣ) : A) = _
    rw [Subgroup.coe_mul, Units.val_mul, C.translated_symm_coe]
  have hfs : ContDiff ℝ ∞ (fun Z : S => ((f Z : Aˣ) : A)) := by
    rw [hfv]
    exact contDiff_const.mul (contDiff_const.mul
      (contDiff_iff_contDiffAt.mpr (fun Z : S =>
        (NormedSpace.exp_analytic (𝕂 := ℝ) (Z : A)).contDiffAt.comp Z
          S.toSubmodule.subtypeL.contDiff.contDiffAt)))
  have hs := (C.coordinate_smooth (f X) hfmem).comp X hfs.contDiffAt
  apply ContDiffAt.contDiffWithinAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [hfc.preimage_mem_nhds (C.chart.open_source.mem_nhds hfmem)] with Z hZ
  exact C.coordinate_eq (f Z) hZ

/-- The inclusion is smooth in the translated exponential atlas. -/
theorem inclusion_smooth : letI := C.chartedSpace;
    ContMDiff 𝓘(ℝ, S) 𝓘(ℝ, A) ∞ (fun h : H => ((h : Aˣ) : A)) := by
  letI := C.chartedSpace
  intro g
  rw [contMDiffAt_iff]
  refine ⟨(Units.continuous_val.comp continuous_subtype_val).continuousAt, ?_⟩
  simp only [ModelWithCorners.range_eq_univ, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.id_comp, contDiffWithinAt_univ]
  change ContDiffAt ℝ ∞
    (fun X : S => ((((C.translated g).symm X : H) : Aˣ) : A)) (C.translated g g)
  have he : ContDiff ℝ ∞ (fun X : S => NormedSpace.exp (X : A)) :=
    contDiff_iff_contDiffAt.mpr fun X : S =>
      (NormedSpace.exp_analytic (𝕂 := ℝ) (X : A)).contDiffAt.comp X
        S.toSubmodule.subtypeL.contDiff.contDiffAt
  simpa only [C.translated_symm_coe] using (contDiff_const.mul he).contDiffAt

/-- A continuous map into H is smooth whenever its ambient matrix map
is smooth. The coordinate extension proves this locally at every point. -/
theorem contMDiffAt_of_ambient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Type*} [TopologicalSpace B] {I : ModelWithCorners ℝ E B}
    {N : Type*} [TopologicalSpace N] [ChartedSpace B N]
    (f : N → H) (x : N) (hc : ContinuousAt f x) :
    letI := C.chartedSpace
    ContMDiffAt I 𝓘(ℝ, A) ∞ (fun y => ((f y : Aˣ) : A)) x →
      ContMDiffAt I 𝓘(ℝ, S) ∞ f x := by
  letI := C.chartedSpace
  intro hf
  rw [contMDiffAt_iff_target]
  refine ⟨hc, ?_⟩
  let g : N → H := fun y => (f x)⁻¹ * f y
  have hg : ContinuousAt g x := continuousAt_const.mul hc
  have hgx : g x = 1 := inv_mul_cancel (f x)
  have hgv : ContMDiffAt I 𝓘(ℝ, A) ∞ (fun y => ((g y : Aˣ) : A)) x := by
    change ContMDiffAt I 𝓘(ℝ, A) ∞
      (fun y => (((f x)⁻¹ : H) : Aˣ).val * ((f y : Aˣ) : A)) x
    exact contMDiffAt_const.mul hf
  have hq : ContMDiffAt 𝓘(ℝ, A) 𝓘(ℝ, S) ∞ C.coordinateExtension ((g x : Aˣ) : A) := by
    rw [hgx]
    exact (C.coordinate_smooth 1 C.one_mem).contMDiffAt
  apply (hq.comp x hgv).congr_of_eventuallyEq
  have hmem : ∀ᶠ y in 𝓝 x, g y ∈ C.chart.source :=
    hg.preimage_mem_nhds (by simpa only [hgx] using C.chart.open_source.mem_nhds C.one_mem)
  filter_upwards [hmem] with y hy
  change C.chart (g y) = C.coordinateExtension ((g y : Aˣ) : A)
  exact C.coordinate_eq (g y) hy

/-- Multiplication and inversion inherit smoothness from the matrix group. -/
theorem lieGroup : letI := C.chartedSpace; LieGroup 𝓘(ℝ, S) ∞ H := by
  letI := C.chartedSpace
  letI := C.isManifold
  have hi := C.inclusion_smooth
  have hu : ContMDiff 𝓘(ℝ, S) 𝓘(ℝ, A) ∞ (fun h : H => (h : Aˣ)) := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    exact hi
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · intro p
    apply C.contMDiffAt_of_ambient (fun p : H × H => p.1 * p.2) p continuous_mul.continuousAt
    change ContMDiffAt (𝓘(ℝ, S).prod 𝓘(ℝ, S)) 𝓘(ℝ, A) ∞
      (fun p : H × H => ((p.1 : Aˣ) : A) * ((p.2 : Aˣ) : A)) p
    exact ((hi.comp contMDiff_fst).mul (hi.comp contMDiff_snd)) p
  · intro h
    apply C.contMDiffAt_of_ambient (fun h : H => h⁻¹) h continuous_inv.continuousAt
    have hinv : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ (fun g : Aˣ => g⁻¹) :=
      LieGroup.contMDiff_inv
    exact (Units.contMDiff_val.comp (hinv.comp hu)) h

/-- In exponential coordinates the derivative of the inclusion is the
subspace inclusion, so its image is precisely the given Lie subalgebra. -/
theorem tangent_inclusion : letI := C.chartedSpace;
    mfderiv 𝓘(ℝ, S) 𝓘(ℝ, A) (fun h : H => ((h : Aˣ) : A)) 1 =
      S.toSubmodule.subtypeL := by
  letI := C.chartedSpace
  have hw : writtenInExtChartAt 𝓘(ℝ, S) 𝓘(ℝ, A) (1 : H)
      (fun h : H => ((h : Aˣ) : A)) = fun X : S => NormedSpace.exp (X : A) := by
    funext X
    change ((((C.translated 1).symm X : H) : Aˣ) : A) = NormedSpace.exp (X : A)
    rw [C.translated_symm_coe]
    simp only [Subgroup.coe_one, Units.val_one, one_mul]
  have hd : HasMFDerivAt 𝓘(ℝ, S) 𝓘(ℝ, A)
      (fun h : H => ((h : Aˣ) : A)) 1 S.toSubmodule.subtypeL := by
    refine ⟨(Units.continuous_val.comp continuous_subtype_val).continuousAt, ?_⟩
    rw [hw, ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ]
    change HasFDerivAt (fun X : S => NormedSpace.exp (X : A))
      ((tangentSpaceCastModel 𝓘(ℝ, A) (1 : A)).toContinuousLinearMap.comp
        (S.toSubmodule.subtypeL.comp
          (tangentSpaceCastModel 𝓘(ℝ, S) (1 : H)).symm.toContinuousLinearMap))
      (C.translated 1 1)
    rw [C.chart_self]
    convert (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)).comp (0 : S)
      S.toSubmodule.subtypeL.hasFDerivAt using 1
    all_goals first | rfl | (apply ContinuousLinearMap.ext; intro X; rfl)
  exact hd.mfderiv

theorem tangent_range : letI := C.chartedSpace;
    LinearMap.range
      (mfderiv 𝓘(ℝ, S) 𝓘(ℝ, A) (fun h : H => ((h : Aˣ) : A)) 1).toLinearMap
      = S.toSubmodule := by
  letI := C.chartedSpace
  rw [C.tangent_inclusion]
  exact S.toSubmodule.range_subtype

/-- The coordinate extension is a left inverse to the tangent inclusion. -/
theorem coordinate_deriv_one (X : S) : fderiv ℝ C.coordinateExtension 1 (X : A) = X := by
  have ht : C.chart.target ∈ 𝓝 (0 : S) := by
    rw [← C.chart_one]
    exact C.chart.open_target.mem_nhds (C.chart.map_source C.one_mem)
  have heq : (fun Z : S => C.coordinateExtension (NormedSpace.exp (Z : A))) =ᶠ[𝓝 0] id := by
    filter_upwards [ht] with Z hZ
    rw [← C.inverse_eq Z, ← C.coordinate_eq (C.chart.symm Z) (C.chart.map_target hZ)]
    exact C.chart.right_inv hZ
  have he : HasFDerivAt (fun Z : S => NormedSpace.exp (Z : A)) S.toSubmodule.subtypeL 0 := by
    convert (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)).comp (0 : S)
      S.toSubmodule.subtypeL.hasFDerivAt using 1
    all_goals first | rfl | (ext Z; rfl)
  have hq : DifferentiableAt ℝ C.coordinateExtension (NormedSpace.exp ((0 : S) : A)) := by
    convert (C.coordinate_smooth 1 C.one_mem).differentiableAt (by simp) using 1 <;>
      simp only [Submodule.coe_zero, NormedSpace.exp_zero, Subgroup.coe_one, Units.val_one]
  have hcomp := hq.hasFDerivAt.comp (0 : S) he
  have hid := (hasFDerivAt_id (𝕜 := ℝ) (0 : S)).congr_of_eventuallyEq heq
  have hder := hcomp.unique hid
  have hv := congrArg (fun L : S →L[ℝ] S => L X) hder
  change (fderiv ℝ C.coordinateExtension (NormedSpace.exp ((0 : S) : A))) (X : A) = X at hv
  convert hv using 1 <;> simp only [Submodule.coe_zero, NormedSpace.exp_zero]

/-- The coordinate derivative sends invariant tangent vectors to the
ambient derivative of the coordinate extension. -/
theorem coordinate_deriv_invariant (g : H) (hg : g ∈ C.chart.source) (X : S) :
    letI := C.chartedSpace
    letI := C.lieGroup
    mfderiv 𝓘(ℝ, S) 𝓘(ℝ, S) (C.translated (1 : H)) g
      (mulInvariantVectorField X g) =
    fderiv ℝ C.coordinateExtension ((g : Aˣ) : A) (((g : Aˣ) : A) * (X : A)) := by
  letI := C.chartedSpace
  letI := C.lieGroup
  let i : H → A := fun h => ((h : Aˣ) : A)
  have heq : (C.translated (1 : H) : H → S) =ᶠ[𝓝 g] (C.coordinateExtension ∘ i) := by
    filter_upwards [C.chart.open_source.mem_nhds hg] with h hh
    simpa only [C.translated_apply, inv_one, one_mul, Function.comp_apply, i] using C.coordinate_eq h hh
  have hq := (C.coordinate_smooth g hg).contMDiffAt.mdifferentiableAt (by simp)
  have hi := C.inclusion_smooth.mdifferentiableAt (x := g) (by simp)
  have hder := congrArg (fun L => L (mulInvariantVectorField X g))
    (heq.mfderiv_eq (I := 𝓘(ℝ, S)) (I' := 𝓘(ℝ, S)))
  change mfderiv 𝓘(ℝ, S) 𝓘(ℝ, S) (C.translated (1 : H)) g
      (mulInvariantVectorField X g) =
    mfderiv 𝓘(ℝ, S) 𝓘(ℝ, S) (C.coordinateExtension ∘ i) g
      (mulInvariantVectorField X g) at hder
  rw [hder, mfderiv_comp (I' := 𝓘(ℝ, A)) g hq hi]
  change mfderiv 𝓘(ℝ, A) 𝓘(ℝ, S) C.coordinateExtension ((g : Aˣ) : A)
      (mfderiv 𝓘(ℝ, S) 𝓘(ℝ, A) i g (mulInvariantVectorField X g)) = _
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ C.coordinateExtension ((g : Aˣ) : A)
      (mfderiv 𝓘(ℝ, S) 𝓘(ℝ, A) i g (mulInvariantVectorField X g)) = _
  congr 1
  change mfderiv 𝓘(ℝ, S) 𝓘(ℝ, A) i g
    (mfderiv 𝓘(ℝ, S) 𝓘(ℝ, S) (fun h : H => g * h) 1 X) = _
  have hL := (contMDiff_mul_left (I := 𝓘(ℝ, S)) (n := ∞) (a := g)).mdifferentiableAt
    (x := (1 : H)) (by simp)
  have hi' : MDifferentiableAt 𝓘(ℝ, S) 𝓘(ℝ, A) i (g * 1) := by simpa only [mul_one] using hi
  have hcomp := mfderiv_comp_apply_of_eq (I' := 𝓘(ℝ, S))
    (x := (1 : H)) hi hL (mul_one g) X
  rw [← hcomp]
  have heq' : i ∘ (fun h : H => g * h) = (fun a : A => ((g : Aˣ) : A) * a) ∘ i := rfl
  rw [heq', mfderiv_comp (I' := 𝓘(ℝ, A)) 1]
  · rw [C.tangent_inclusion, mfderiv_eq_fderiv]
    change fderiv ℝ (fun a : A => ((g : Aˣ) : A) * a) 1 (X : A) = _
    exact congrArg (fun L : A →L[ℝ] A => L (X : A))
      ((hasFDerivAt_id (1 : A)).const_mul ((g : Aˣ) : A)).fderiv
  · have hm : ContDiff ℝ ∞ (fun a : A => ((g : Aˣ) : A) * a) :=
      contDiff_const.mul contDiff_id
    exact hm.contDiffAt.contMDiffAt.mdifferentiableAt (by simp)
  · exact C.inclusion_smooth.mdifferentiableAt (by simp)

/-- Ambient expression for an invariant vector field in coordinates. -/
def coordinateField (X : S) (a : A) : S :=
  fderiv ℝ C.coordinateExtension a (a * (X : A))

theorem differentiableAt_coordinateField_one (X : S) :
    DifferentiableAt ℝ (C.coordinateField X) 1 := by
  apply DifferentiableAt.clm_apply
  · exact ((C.coordinate_smooth 1 C.one_mem).fderiv_right (m := 1) (by simp)).differentiableAt
      one_ne_zero
  · exact differentiableAt_id.mul_const (X : A)

/-- The coordinate expression of an invariant field is the pullback of
its ambient expression along the exponential. -/
theorem pullback_invariant_eventually (X : S) :
    letI := C.chartedSpace
    letI := C.lieGroup
    VectorField.mpullbackWithin 𝓘(ℝ, S) 𝓘(ℝ, S)
      (extChartAt 𝓘(ℝ, S) (1 : H)).symm (mulInvariantVectorField X)
      (Set.range 𝓘(ℝ, S)) =ᶠ[𝓝 (0 : S)]
      (fun Z : S => C.coordinateField X (NormedSpace.exp (Z : A))) := by
  letI := C.chartedSpace
  letI := C.lieGroup
  let φ := extChartAt 𝓘(ℝ, S) (1 : H)
  have hφ0 : φ 1 = 0 := C.chart_self 1
  have ht : φ.target ∈ 𝓝 (0 : S) := by
    rw [← hφ0]
    exact extChartAt_target_mem_nhds (I := 𝓘(ℝ, S)) (1 : H)
  filter_upwards [ht] with Z hZ
  have hinv : (mfderivWithin 𝓘(ℝ, S) 𝓘(ℝ, S) φ.symm (Set.range 𝓘(ℝ, S)) Z).inverse =
      mfderiv 𝓘(ℝ, S) 𝓘(ℝ, S) φ (φ.symm Z) :=
    ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ, S)) hZ)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, S)) hZ)
  rw [VectorField.mpullbackWithin_apply, hinv]
  have hg : φ.symm Z ∈ C.chart.source := by
    have h := φ.map_target hZ
    rw [show φ.source = (C.translated (1 : H)).source by
      exact extChartAt_source 𝓘(ℝ, S) (1 : H)] at h
    change (φ.symm Z) ∈ Set.univ ∧ (1 : H)⁻¹ * φ.symm Z ∈ C.chart.source at h
    simpa only [inv_one, one_mul] using h.2
  have hc := C.coordinate_deriv_invariant (φ.symm Z) hg X
  have hφ : (φ : H → S) = C.translated (1 : H) := by
    simp only [φ, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
    rfl
  have hφsymm : (φ.symm : S → H) = (C.translated (1 : H)).symm := by
    simp only [φ, extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id]
    rfl
  have hv : (((φ.symm Z : H) : Aˣ) : A) = NormedSpace.exp (Z : A) := by
    simpa only [hφsymm, Subgroup.coe_one, Units.val_one, one_mul] using C.translated_symm_coe 1 Z
  change mfderiv 𝓘(ℝ, S) 𝓘(ℝ, S) φ (φ.symm Z)
      (mulInvariantVectorField X (φ.symm Z)) = _
  rw [hφ]
  simpa only [hv, coordinateField] using hc

/-- The derivative of the coordinate extension preserves the bracket of the
ambient left invariant vector fields. -/
theorem coordinateField_bracket (X Y : S) :
    fderiv ℝ (C.coordinateField Y) 1 (X : A) -
      fderiv ℝ (C.coordinateField X) 1 (Y : A) = ⁅X, Y⁆ := by
  have hq := C.coordinate_smooth 1 C.one_mem
  have hmul (Z W : A) : fderiv ℝ (fun a : A => a * Z) 1 W = W * Z := by
    have hd := (hasFDerivAt_id (𝕜 := ℝ) (1 : A)).mul_const' Z
    simpa using congrArg (fun L : A →L[ℝ] A => L W) hd.fderiv
  have heq : VectorField.lieBracket ℝ (fun a : A => a * (X : A))
      (fun a : A => a * (Y : A)) 1 = (X : A) * (Y : A) - (Y : A) * (X : A) := by
    simp only [VectorField.lieBracket, hmul, one_mul]
  have hc := VectorField.fderiv_apply_lieBracket hq (by simp)
    (differentiableAt_id.mul_const (Y : A)) (differentiableAt_id.mul_const (X : A))
  simp only [id_eq, Subgroup.coe_one, Units.val_one] at hc
  rw [heq] at hc
  have hh : (X : A) * (Y : A) - (Y : A) * (X : A) = ((⁅X, Y⁆ : S) : A) := rfl
  rw [hh, C.coordinate_deriv_one] at hc
  unfold coordinateField
  simpa only [one_mul] using hc.symm

theorem coordinateField_exp_bracket (X Y : S) :
    VectorField.lieBracket ℝ
      (fun Z : S => C.coordinateField X (NormedSpace.exp (Z : A)))
      (fun Z : S => C.coordinateField Y (NormedSpace.exp (Z : A))) 0 = ⁅X, Y⁆ := by
  have he : HasFDerivAt (fun Z : S => NormedSpace.exp (Z : A))
      S.toSubmodule.subtypeL 0 := by
    convert (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)).comp (0 : S)
      S.toSubmodule.subtypeL.hasFDerivAt using 1
    all_goals first | rfl | (apply ContinuousLinearMap.ext; intro Z; rfl)
  have hvalue (Z : S) : C.coordinateField Z (NormedSpace.exp ((0 : S) : A)) = Z := by
    simp only [Submodule.coe_zero, NormedSpace.exp_zero, coordinateField, one_mul,
      C.coordinate_deriv_one]
  have hderiv (Z W : S) :
      fderiv ℝ (fun U : S => C.coordinateField Z (NormedSpace.exp (U : A))) 0 W =
        fderiv ℝ (C.coordinateField Z) 1 (W : A) := by
    have hd := (C.differentiableAt_coordinateField_one Z).hasFDerivAt
    have hd' : HasFDerivAt (C.coordinateField Z) (fderiv ℝ (C.coordinateField Z) 1)
        (NormedSpace.exp ((0 : S) : A)) := by simpa using hd
    have hh : HasFDerivAt (fun U : S => C.coordinateField Z (NormedSpace.exp (U : A)))
        ((fderiv ℝ (C.coordinateField Z) 1).comp S.toSubmodule.subtypeL) 0 := by
      exact hd'.comp (0 : S) he
    exact congrArg (fun L : S →L[ℝ] S => L W) hh.fderiv
  simp only [VectorField.lieBracket, hvalue, hderiv]
  exact C.coordinateField_bracket X Y


/-- The manifold bracket is the bracket of its local coordinate fields. -/
theorem mlieBracket_eq_coordinate (X Y : S) :
    letI := C.chartedSpace
    letI := C.lieGroup
    VectorField.mlieBracket 𝓘(ℝ, S)
      (mulInvariantVectorField (I := 𝓘(ℝ, S)) (G := H) X)
      (mulInvariantVectorField (I := 𝓘(ℝ, S)) (G := H) Y) (1 : H) =
    VectorField.lieBracket ℝ
      (fun Z : S => C.coordinateField X (NormedSpace.exp (Z : A)))
      (fun Z : S => C.coordinateField Y (NormedSpace.exp (Z : A))) 0 := by
  letI := C.chartedSpace
  letI := C.isManifold
  letI := C.lieGroup
  rw [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply,
    mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id]
  change VectorField.lieBracketWithin (E := S) ℝ _ _ _ _ = _
  simp only [Set.preimage_univ, Set.univ_inter, ModelWithCorners.range_eq_univ,
    VectorField.lieBracketWithin_univ]
  have h0 : extChartAt 𝓘(ℝ, S) (1 : H) 1 = 0 := by
    simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id_eq]
    exact C.chart_self 1
  rw [h0]
  simpa only [ModelWithCorners.range_eq_univ] using
    (C.pullback_invariant_eventually X).lieBracket_vectorField_eq (𝕜 := ℝ)
      (C.pullback_invariant_eventually Y)

/-- Assemble the smooth matrix subgroup and its tangent identification. -/
def embeddedLieGroup : EmbeddedLieGroup H S where
  charts := C.chartedSpace
  manifold := C.isManifold
  group_smooth := C.lieGroup
  inclusion_smooth := C.inclusion_smooth
  tangent_inclusion := C.tangent_inclusion
  tangent_bracket := by
    letI := C.chartedSpace
    letI := C.lieGroup
    intro X Y
    rw [C.tangent_inclusion, C.mlieBracket_eq_coordinate, C.coordinateField_exp_bracket]
    rfl
  tangent_range := C.tangent_range

end ExponentialChart

/-- A one-parameter exponential, with its codomain restricted to H. -/
def expCurve (H : Subgroup Aˣ) (X : velocities H) (t : ℝ) : H :=
  ⟨expUnit (t • X.val), X.property t⟩

theorem continuous_expCurve (H : Subgroup Aˣ) (X : velocities H) :
    Continuous (expCurve H X) := by
  apply Continuous.subtype_mk
  exact continuous_expUnit.comp (continuous_id.smul continuous_const)

@[simp] theorem expCurve_zero (H : Subgroup Aˣ) (X : velocities H) :
    expCurve H X 0 = 1 := by
  apply Subtype.ext
  simp [expCurve]

@[simp] theorem expCurve_one (H : Subgroup Aˣ) (X : velocities H) :
    expCurve H X 1 = expIn H X := by
  apply Subtype.ext
  simp [expCurve, expIn]

/-- This direction requires no closedness assumption on H. -/
theorem expIn_mem_identityComponent (H : Subgroup Aˣ) (X : velocities H) :
    expIn H X ∈ Subgroup.connectedComponentOfOne H := by
  have h := (continuous_expCurve H X).mapsTo_connectedComponent (0 : ℝ)
  have h1 : (1 : ℝ) ∈ connectedComponent (0 : ℝ) := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  change expIn H X ∈ connectedComponent (1 : H)
  simpa only [expCurve_zero, expCurve_one] using h h1

theorem exponentialSubgroup_le_identityComponent (H : Subgroup Aˣ) :
    exponentialSubgroup H ≤ Subgroup.connectedComponentOfOne H := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨X, rfl⟩
  exact expIn_mem_identityComponent H X

/-- The remaining topological step once local exponential coordinates
show that the generated subgroup contains an identity neighborhood. -/
theorem exponentialSubgroup_eq_identityComponent_of_nhds (H : Subgroup Aˣ)
    (h : (exponentialSubgroup H : Set H) ∈ 𝓝 (1 : H)) :
    exponentialSubgroup H = Subgroup.connectedComponentOfOne H := by
  apply le_antisymm (exponentialSubgroup_le_identityComponent H)
  have hopen := (exponentialSubgroup H).isOpen_of_mem_nhds h
  have hclosed := (exponentialSubgroup H).isClosed_of_isOpen hopen
  have hclopen : IsClopen (exponentialSubgroup H : Set H) := ⟨hclosed, hopen⟩
  exact hclopen.connectedComponent_subset (exponentialSubgroup H).one_mem

/-- The identity component is generated algebraically by exponentials;
no closure is taken in this subgroup generation. -/
theorem exponentialSubgroup_eq_identityComponent [FiniteDimensional ℝ A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) :
    exponentialSubgroup H = Subgroup.connectedComponentOfOne H := by
  apply exponentialSubgroup_eq_identityComponent_of_nhds H
  exact Filter.mem_of_superset (exponential_range_mem_nhds H hH)
    (Subgroup.subset_closure)

/-- The closed matrix subgroup theorem, including the inherited topology,
its infinitesimal commutator algebra, and identity-component generation. -/
theorem closed_matrix_group :
    Specs.LieAlgebrasAndRepresentations.ClosedMatrixGroups.closed_matrix_group_type := by
  intro V _ _ _ H hH
  let S := velocityLieSubalgebra H hH
  refine ⟨S, rfl, velocities_closed H hH, inferInstance, ?_,
    exponentialSubgroup_eq_identityComponent H hH⟩
  obtain ⟨C⟩ := nonempty_exponentialChart H hH
  exact ⟨C.embeddedLieGroup⟩

end LieAlgebrasAndRepresentations.ClosedMatrixGroups
