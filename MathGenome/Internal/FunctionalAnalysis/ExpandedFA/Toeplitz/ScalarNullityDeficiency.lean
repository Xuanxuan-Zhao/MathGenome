import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.ScalarNullityDeficiency
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Toeplitz.ScalarIndex

/-! Coburn's alternative in the Fredholm case, using the Toeplitz shift identity
and finite-dimensionality of the kernel. This avoids products of boundary H²
functions. All shifts act on the canonical upstream coefficient space. -/
noncomputable section
open MeasureTheory
open scoped Real ENNReal InnerProductSpace ComplexConjugate
namespace ExpandedFA.Toeplitz.ScalarNullityDeficiency
open ExpandedFA.Toeplitz.Definitions
open ExpandedFA.Toeplitz.HankelCompactness
open ExpandedFA.Fredholm

local notation "S" => ExpandedFA.PartIV.HardyDisk.shift.toContinuousLinearMap
local notation "B" => ExpandedFA.PartIV.HardyDisk.boundary

@[simp] theorem shift_adjoint_apply (f : H2) (k : ℕ) :
    (S).adjoint f k = f (k + 1) := by
  have he : S = (ScalarIndex.forwardShift 1).toContinuousLinearMap := by
    rw [← coordinate_toeplitz, ← ScalarIndex.positive_toeplitz_eq_shift]
    norm_num
  rw [he, ScalarIndex.forwardShift_adjoint_apply]

/-- The zeroth coordinate and the backward shift reconstruct every vector. -/
theorem shift_adjoint_decomposition (f : H2) :
    S ((S).adjoint f) = f - lp.single 2 0 (f 0) := by
  apply lp.ext
  funext k
  cases k with
  | zero => simp [ExpandedFA.PartIV.HardyDisk.shift_zero, lp.single_apply]
  | succ k =>
    simp [ExpandedFA.PartIV.HardyDisk.shift_succ, shift_adjoint_apply, lp.single_apply]

/-- Multiplication by the coordinate cancels from both slots of the form. -/
theorem coordinate_form (φ : ScalarSymbol) (f g : BoundaryL2) :
    let Z := multiplication (continuousSymbol (fourier (T := 2 * π) 1))
    ⟪Z f, multiplication φ (Z g)⟫_ℂ = ⟪f, multiplication φ g⟫_ℂ := by
  dsimp only
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplication_values (continuousSymbol (fourier (T := 2 * π) 1)) f,
    multiplication_values (continuousSymbol (fourier (T := 2 * π) 1)) g,
    multiplication_values φ (multiplication (continuousSymbol (fourier (T := 2 * π) 1)) g),
    multiplication_values φ g,
    continuous_symbol_values (fourier (T := 2 * π) 1)] with t hf hg hm hn hz
  rw [hf, hm, hn, hg, hz, fourier_one]
  simp only [RCLike.inner_apply, map_mul]
  calc
    _ = (φ t * g t * conj (f t)) *
        (conj ((AddCircle.toCircle t : _root_.Circle) : ℂ) *
          ((AddCircle.toCircle t : _root_.Circle) : ℂ)) := by ring
    _ = _ := by rw [Complex.conj_mul', Circle.norm_coe, Complex.ofReal_one, one_pow, mul_one]

/-- The Brown–Halmos shift identity for the actual compressed multiplier. -/
theorem toeplitz_shift_identity (φ : ScalarSymbol) :
    (S).adjoint.comp ((toeplitz φ).comp S) = toeplitz φ := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  change ⟪f, (S).adjoint (toeplitz φ (S g))⟫_ℂ = ⟪f, toeplitz φ g⟫_ℂ
  rw [(S).adjoint_inner_right]
  change ⟪S f, boundaryInclusion.adjoint (multiplication φ (B (S g)))⟫_ℂ =
    ⟪f, boundaryInclusion.adjoint (multiplication φ (B g))⟫_ℂ
  rw [boundaryInclusion.adjoint_inner_right, boundaryInclusion.adjoint_inner_right]
  change ⟪B (ExpandedFA.PartIV.HardyDisk.shift f),
    multiplication φ (B (ExpandedFA.PartIV.HardyDisk.shift g))⟫_ℂ =
      ⟪B f, multiplication φ (B g)⟫_ℂ
  rw [← coordinate_multiplication_boundary, ← coordinate_multiplication_boundary]
  exact coordinate_form φ (B f) (B g)

/-- A Toeplitz kernel whose vectors have zero constant term must vanish:
backward shifting preserves that kernel and exposes every coefficient. -/
theorem kernel_eq_bot_of_constant_zero (T : H2 →L[ℂ] H2)
    (hT : (S).adjoint.comp (T.comp S) = T)
    (hzero : ∀ f : H2, T f = 0 → f 0 = 0) : T.ker = ⊥ := by
  have hall (n : ℕ) : ∀ f : H2, T f = 0 → f n = 0 := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      intro f hf
      have hs : S ((S).adjoint f) = f := by
        rw [shift_adjoint_decomposition, hzero f hf]
        simp
      have hk : T ((S).adjoint f) = 0 := by
        rw [← hT]
        change (S).adjoint (T (S ((S).adjoint f))) = 0
        rw [hs, hf, map_zero]
      simpa only [shift_adjoint_apply] using ih ((S).adjoint f) hk
  apply LinearMap.ker_eq_bot.mpr
  intro f g hfg
  have hf : T (f - g) = 0 := by
    simp only [map_sub]
    exact sub_eq_zero.mpr hfg
  have hz : f - g = 0 := by
    apply lp.ext
    funext n
    exact hall n (f - g) hf
  exact sub_eq_zero.mp hz

/-- The forward shift has no nonzero finite-dimensional invariant subspace. -/
theorem finite_shift_invariant_eq_bot (N : Submodule ℂ H2)
    [FiniteDimensional ℂ N] (hN : ∀ f ∈ N, S f ∈ N) : N = ⊥ := by
  let R : N →ₗ[ℂ] N :=
    { toFun := fun f => ⟨S f, hN f f.property⟩
      map_add' := fun f g => Subtype.ext (map_add S f.val g.val)
      map_smul' := fun c f => Subtype.ext (map_smul S c f.val) }
  have hR : Function.Surjective R := LinearMap.surjective_of_injective (by
    intro f g he
    exact Subtype.ext (ExpandedFA.PartIV.HardyDisk.shift.injective
      (congrArg Subtype.val he)))
  have hall (n : ℕ) : ∀ f : N, f.val n = 0 := by
    induction n with
    | zero =>
      intro f
      obtain ⟨g, hg⟩ := hR f
      have he : S g = f.val := congrArg Subtype.val hg
      rw [← he]
      exact ExpandedFA.PartIV.HardyDisk.shift_zero g
    | succ n ih =>
      intro f
      obtain ⟨g, hg⟩ := hR f
      have he : S g = f.val := congrArg Subtype.val hg
      rw [← he]
      exact (ExpandedFA.PartIV.HardyDisk.shift_succ g n).trans (ih g)
  apply le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  apply lp.ext
  funext n
  exact hall n ⟨f, hf⟩

/-- Coburn's argument for any Fredholm scalar Toeplitz matrix.
Only finite-dimensionality of its kernel is used at this stage. -/
theorem coburn_of_shift_identity (T : H2 →L[ℂ] H2)
    [FiniteDimensional ℂ T.ker]
    (hT : (S).adjoint.comp (T.comp S) = T) :
    T.ker = ⊥ ∨ T.adjoint.ker = ⊥ := by
  classical
  by_cases hk : T.adjoint.ker = ⊥
  · exact Or.inr hk
  left
  have hstar : (S).adjoint.comp (T.adjoint.comp S) = T.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hT
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc] using h
  obtain ⟨g, hg, hg0⟩ : ∃ g : H2, T.adjoint g = 0 ∧ g 0 ≠ 0 := by
    by_contra! h
    exact hk (kernel_eq_bot_of_constant_zero T.adjoint hstar h)
  apply finite_shift_invariant_eq_bot
  intro f hf
  change T (S f) = 0
  have hf' : T f = 0 := hf
  have hv : (S).adjoint (T (S f)) = 0 := by
    have h := congrArg (fun A : H2 →L[ℂ] H2 => A f) hT
    exact h.trans hf'
  have he : T (S f) = lp.single 2 0 (T (S f) 0) := by
    have h := shift_adjoint_decomposition (T (S f))
    rw [hv, map_zero] at h
    exact (sub_eq_zero.mp h.symm)
  have hi : ⟪g, T (S f)⟫_ℂ = 0 := by
    rw [← T.adjoint_inner_left, hg, inner_zero_left]
  rw [he, lp.inner_single_right, RCLike.inner_apply] at hi
  have hc : T (S f) 0 = 0 := (mul_eq_zero.mp hi).resolve_right (by simpa using hg0)
  rw [he, hc]
  simp

/-- For a nowhere zero continuous symbol, one of the two actual kernels vanishes. -/
theorem coburn_alternative : Spec.CoburnAlternative := by
  intro φ
  letI := (ScalarIndex.fredholm_symbols φ).2.1
  exact coburn_of_shift_identity _ (toeplitz_shift_identity _)

/-- The separate dimensions require Coburn's alternative in addition to the index. -/
theorem nullity_deficiency : Spec.NullityDeficiency := by
  intro φ
  obtain ⟨hF, hi⟩ := ScalarIndex.scalar_index φ
  change (Module.finrank ℂ (toeplitz (continuousSymbol φ.val)).ker : ℤ) -
      Module.finrank ℂ (H2 ⧸ (toeplitz (continuousSymbol φ.val)).range) = -winding φ at hi
  have arithmetic (a b : ℕ) (w : ℤ) (hi : (a : ℤ) - b = -w)
      (hz : a = 0 ∨ b = 0) :
      a = (max 0 (-w)).toNat ∧ b = (max 0 w).toNat := by omega
  apply arithmetic _ _ _ hi
  rcases coburn_alternative φ with hk | hk
  · have ha : Module.finrank ℂ (toeplitz (continuousSymbol φ.val)).ker = 0 := by
      rw [hk]
      simp
    exact Or.inl ha
  · have hb : Module.finrank ℂ (H2 ⧸ (toeplitz (continuousSymbol φ.val)).range) = 0 := by
      rw [(cokernelEquivAdjointKer _ hF.1).finrank_eq, hk]
      simp
    exact Or.inr hb

/-- All conclusions of the source theorem, with compactness for every continuous symbol. -/
theorem scalar_toeplitz_theorem : Spec.ScalarToeplitzTheorem := by
  refine ⟨hankel_compact, ?_⟩
  intro φ
  obtain ⟨hF, hi⟩ := ScalarIndex.scalar_index φ
  exact ⟨hF, hi, nullity_deficiency φ⟩

end ExpandedFA.Toeplitz.ScalarNullityDeficiency
