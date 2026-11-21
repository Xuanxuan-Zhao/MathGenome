import MathGenome.Internal.RealAnalysis.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveFunctionalBound
import Mathlib.Tactic.Linarith

/-! Compact-support bounds use a cutoff and positivity alone.
For complex scalars, restriction to real functions commutes with real parts;
a unit scalar rotates the functional value to its norm. -/

namespace D11.Ch19
universe u

section Real
variable {X : Type u} [TopologicalSpace X]

/-- Positivity implies monotonicity without a continuity assumption. -/
lemma positive_functional_mono (I : Cc X ℝ →ₗ[ℝ] ℝ)
    (hI : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f)
    {f g : Cc X ℝ} (hfg : ∀ x, f x ≤ g x) : I f ≤ I g := by
  have h := hI (g - f) (fun x => sub_nonneg.mpr (hfg x))
  simpa only [map_sub, sub_nonneg] using h

/-- The upper half of the cutoff estimate, for any pointwise norm bound. -/
lemma positive_functional_le_cutoff (I : Cc X ℝ →ₗ[ℝ] ℝ)
    (hI : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f)
    (K : Set X) (h : Cc X ℝ) (hh : ∀ x, 0 ≤ h x)
    (hK : ∀ x ∈ K, h x = 1) (f : Cc X ℝ)
    (hf : tsupport f ⊆ K) (A : ℝ) (hA : 0 ≤ A)
    (hAf : ∀ x, f x ≤ A) : I f ≤ A * I h := by
  have hle : ∀ x, f x ≤ (A • h) x := by
    intro x
    by_cases hx : x ∈ K
    · simpa [CompactlySupportedContinuousMap.smul_apply, hK x hx] using hAf x
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hf hs))
      simpa [CompactlySupportedContinuousMap.smul_apply, hz] using mul_nonneg hA (hh x)
  simpa only [map_smul, smul_eq_mul] using positive_functional_mono I hI hle

/-- Real positive functionals have a finite bound on every compact support. -/
theorem positive_functional_bound (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (I : Cc X ℝ →ₗ[ℝ] ℝ)
    (hI : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f)
    (K : Set X) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Cc X ℝ,
      closure {x | f x ≠ 0} ⊆ K →
        |I f| ≤ C * ‖f.toBoundedContinuousFunction‖ := by
  obtain ⟨h, hh, hhK, _, _⟩ :=
    D11.Ch18.compact_cutoff X K Set.univ hK isOpen_univ (Set.subset_univ K)
  refine ⟨I h, hI h (fun x => (hh x).1), ?_⟩
  intro f hf
  apply abs_le.mpr
  have hu := positive_functional_le_cutoff I hI K h (fun x => (hh x).1) hhK
    f hf _ (norm_nonneg _) (fun x => f.toBoundedContinuousFunction.apply_le_norm x)
  have hl := positive_functional_le_cutoff I hI K h (fun x => (hh x).1) hhK
    (-f) (by
      change tsupport (-(f : X → ℝ)) ⊆ K
      rw [tsupport_neg]
      exact hf) ‖f.toBoundedContinuousFunction‖ (norm_nonneg _)
    (fun x => by
      simpa using neg_le_neg (f.toBoundedContinuousFunction.neg_norm_le_apply x))
  simp only [map_neg] at hl
  constructor <;> nlinarith
end Real

noncomputable section Complex
variable {X : Type u} [TopologicalSpace X]

/-- The real-to-complex inclusion in the canonical compact-support spaces. -/
def ccOfReal : Cc X ℝ →ₗ[ℝ] Cc X ℂ where
  toFun f := ⟨⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
    f.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)⟩
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

@[simp] lemma ccOfReal_apply (f : Cc X ℝ) (x : X) : ccOfReal f x = (f x : ℂ) := rfl

/-- Pointwise real part retains compact support. -/
def ccRe (f : Cc X ℂ) : Cc X ℝ :=
  ⟨⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩,
    f.hasCompactSupport.comp_left (g := Complex.re) (by simp)⟩

/-- Pointwise imaginary part retains compact support. -/
def ccIm (f : Cc X ℂ) : Cc X ℝ :=
  ⟨⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩,
    f.hasCompactSupport.comp_left (g := Complex.im) (by simp)⟩

@[simp] lemma ccRe_apply (f : Cc X ℂ) (x : X) : ccRe f x = (f x).re := rfl
@[simp] lemma ccIm_apply (f : Cc X ℂ) (x : X) : ccIm f x = (f x).im := rfl

variable (I : Cc X ℂ →ₗ[ℂ] ℂ)
    (hI : ∀ f, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (I f).re ∧ (I f).im = 0)

/-- Restriction of a complex functional to real functions, taking real parts. -/
def realRestriction : Cc X ℝ →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((I.restrictScalars ℝ).comp ccOfReal)

@[simp] lemma realRestriction_apply (f : Cc X ℝ) :
    realRestriction I f = (I (ccOfReal f)).re := rfl

include hI

lemma realRestriction_nonneg (f : Cc X ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ realRestriction I f :=
  (hI (ccOfReal f) (fun x => by simpa using hf x)).1

/-- Positive-negative decomposition shows real functions have real images. -/
lemma positive_functional_ofReal_im (f : Cc X ℝ) : (I (ccOfReal f)).im = 0 := by
  have hp := (hI (ccOfReal (f ⊔ 0)) (fun x => by simp)).2
  have hn := (hI (ccOfReal ((-f) ⊔ 0)) (fun x => by simp)).2
  have heq : ccOfReal f = ccOfReal (f ⊔ 0) - ccOfReal ((-f) ⊔ 0) := by
    rw [← map_sub]
    congr 1
    ext x
    simp only [CompactlySupportedContinuousMap.coe_sub, Pi.sub_apply,
      CompactlySupportedContinuousMap.coe_sup, Pi.sup_apply,
      CompactlySupportedContinuousMap.coe_zero, Pi.zero_apply,
      CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply]
    exact (max_zero_sub_max_neg_zero_eq_self (f x)).symm
  rw [heq, map_sub, Complex.sub_im, hp, hn, sub_self]

lemma realRestriction_re (f : Cc X ℂ) : realRestriction I (ccRe f) = (I f).re := by
  have heq : f = ccOfReal (ccRe f) + Complex.I • ccOfReal (ccIm f) := by
    ext x
    simpa [CompactlySupportedContinuousMap.smul_apply, mul_comm] using (Complex.re_add_im (f x)).symm
  conv_rhs => rw [heq, map_add, map_smul]
  simp only [realRestriction_apply, Complex.add_re, smul_eq_mul, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul,
    positive_functional_ofReal_im I hI, sub_self, add_zero]

omit hI

/-- Complex positive functionals satisfy the same local uniform-norm estimate. -/
theorem complex_positive_functional_bound (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (I : Cc X ℂ →ₗ[ℂ] ℂ)
    (hI : ∀ f, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (I f).re ∧ (I f).im = 0)
    (K : Set X) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Cc X ℂ,
      closure {x | f x ≠ 0} ⊆ K →
        ‖I f‖ ≤ C * ‖f.toBoundedContinuousFunction‖ := by
  obtain ⟨h, hh, hhK, _, _⟩ :=
    D11.Ch18.compact_cutoff X K Set.univ hK isOpen_univ (Set.subset_univ K)
  let J := realRestriction I
  have hJ := realRestriction_nonneg I hI
  refine ⟨J h, hJ h (fun x => (hh x).1), ?_⟩
  intro f hf
  obtain ⟨z, hz, heq⟩ := Complex.exists_norm_eq_mul_self (I f)
  have hsupport : tsupport (ccRe (z • f)) ⊆ K := by
    apply closure_minimal _ isClosed_closure |>.trans hf
    intro x hx
    apply subset_closure
    contrapose! hx
    change ¬ ccRe (z • f) x ≠ 0
    have hfx : f x = 0 := by simpa using hx
    simp [hfx]
  have hpoint : ∀ x, ccRe (z • f) x ≤ ‖f.toBoundedContinuousFunction‖ := by
    intro x
    calc
      ccRe (z • f) x ≤ ‖(z • f) x‖ := Complex.re_le_norm _
      _ = ‖f x‖ := by simp [CompactlySupportedContinuousMap.smul_apply, hz]
      _ ≤ ‖f.toBoundedContinuousFunction‖ :=
        f.toBoundedContinuousFunction.norm_coe_le_norm x
  have hle := positive_functional_le_cutoff J hJ K h (fun x => (hh x).1) hhK
    (ccRe (z • f)) hsupport _ (norm_nonneg _) hpoint
  have heq' : J (ccRe (z • f)) = ‖I f‖ := by
    rw [realRestriction_re I hI, map_smul]
    exact congrArg Complex.re heq.symm
  rw [heq'] at hle
  simpa only [mul_comm] using hle
end Complex
end D11.Ch19
