import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.GeneralBipolar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.CompatibleConvexClosedSets
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Tactic.FieldSimp

/-!
The general bipolar theorem for the bilinear dual pair `B y x`.

The hull consists of finite sums with total coefficient modulus at most one.
Its weak closure is real-convex and balanced. A point outside it has a weakly
continuous separator; the weak representation theorem realizes that separator
in Y. Balance converts its real-part bound into a modulus bound. The positive
separating threshold permits scaling even when the hull's support value is zero.
Applying the result to algebraic spans proves both annihilator identities.
-/

namespace ExpandedFA.P1.GeneralBipolar

universe u v w
open scoped ComplexConjugate
noncomputable section

variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]

theorem zero_mem_aconv (A : Set X) : (0 : X) ∈ aconv 𝕜 A :=
  ⟨0, Fin.elim0, Fin.elim0, (fun i => i.elim0), by simp, by simp⟩

theorem subset_aconv (A : Set X) : A ⊆ aconv 𝕜 A := by
  intro x hx
  exact ⟨1, (fun _ => 1), (fun _ => x), (fun _ => hx), by simp, by simp⟩

@[simp]
theorem aconv_empty : aconv 𝕜 (∅ : Set X) = {0} := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, c, y, hy, _, hs⟩
    cases n with
    | zero => simpa using hs.symm
    | succ n => exact (hy 0).elim
  · rintro x (rfl : x = 0)
    exact zero_mem_aconv ∅

theorem aconv_balanced (A : Set X) : Balanced 𝕜 (aconv 𝕜 A) := by
  apply balanced_iff_smul_mem.mpr
  rintro a ha u ⟨n, c, x, hx, hc, rfl⟩
  refine ⟨n, (fun i => a * c i), x, hx, ?_, ?_⟩
  · simp only [norm_mul, ← Finset.mul_sum]
    calc
      ‖a‖ * (∑ i, ‖c i‖) ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ ≤ 1 := by simpa using ha
  · simp only [mul_smul, Finset.smul_sum]

theorem aconv_convex (A : Set X) :
    letI := Module.restrictScalars ℝ 𝕜 X
    Convex ℝ (aconv 𝕜 A) := by
  let := Module.restrictScalars ℝ 𝕜 X
  let := IsScalarTower.restrictScalars ℝ 𝕜 X
  rintro u ⟨n, c, x, hx, hc, rfl⟩ v ⟨m, d, y, hy, hd, rfl⟩ a b ha hb hab
  refine ⟨n + m, Fin.append (fun i => (a : 𝕜) * c i) (fun i => (b : 𝕜) * d i),
    Fin.append x y, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hx j
    · simpa using hy j
  · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      norm_mul, RCLike.norm_ofReal, abs_of_nonneg ha, abs_of_nonneg hb,
      ← Finset.mul_sum]
    calc
      a * (∑ i, ‖c i‖) + b * (∑ i, ‖d i‖) ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hc ha) (mul_le_mul_of_nonneg_left hd hb)
      _ = 1 := by simpa using hab
  · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      mul_smul, ← Finset.smul_sum, RCLike.real_smul_eq_coe_smul (K := 𝕜)]

/-- On a balanced set, a real-part upper bound also bounds the modulus. -/
theorem norm_le_of_re_le_on_balanced {C : Set X} (hC : Balanced 𝕜 C)
    (f : X →ₗ[𝕜] 𝕜) {s : ℝ} (hs : 0 ≤ s)
    (hf : ∀ c ∈ C, RCLike.re (f c) ≤ s) : ∀ c ∈ C, ‖f c‖ ≤ s := by
  intro c hc
  by_cases hz : f c = 0
  · simpa [hz] using hs
  let a : 𝕜 := (‖f c‖ : 𝕜)⁻¹ * conj (f c)
  have ha : ‖a‖ ≤ 1 := by
    simp [a, norm_mul, norm_inv, norm_ne_zero_iff.mpr hz]
  have hb := hf (a • c) (hC.smul_mem ha hc)
  have heq : RCLike.re (f (a • c)) = ‖f c‖ := by
    rw [map_smul, smul_eq_mul]
    dsimp only [a]
    rw [mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_inv, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul, RCLike.ofReal_re]
    field_simp
  rwa [heq] at hb

/-- A scalar modulus bound passes to every finite absolute convex combination. -/
theorem norm_le_one_on_aconv (f : X →ₗ[𝕜] 𝕜) (A : Set X)
    (hf : ∀ a ∈ A, ‖f a‖ ≤ 1) : ∀ x ∈ aconv 𝕜 A, ‖f x‖ ≤ 1 := by
  rintro x ⟨n, c, y, hy, hc, rfl⟩
  calc
    ‖f (∑ i, c i • y i)‖ = ‖∑ i, c i * f (y i)‖ := by simp
    _ ≤ ∑ i, ‖c i * f (y i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hf _ (hy i))
    _ ≤ 1 := hc

/-- The bipolar identity in the native weak topology. In fact separation of
the pairing is unnecessary for this identity. -/
theorem bipolar_weak (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (A : Set X) :
    B.polar (B.flip.polar A) =
      @closure X (WeakBilin.instTopologicalSpace B.flip) (aconv 𝕜 A) := by
  let := Module.restrictScalars ℝ 𝕜 X
  let := IsScalarTower.restrictScalars ℝ 𝕜 X
  let : TopologicalSpace X := WeakBilin.instTopologicalSpace B.flip
  let : IsTopologicalAddGroup X :=
    inferInstanceAs (IsTopologicalAddGroup (WeakBilin B.flip))
  let : ContinuousSMul 𝕜 X :=
    inferInstanceAs (ContinuousSMul 𝕜 (WeakBilin B.flip))
  let : ContinuousSMul ℝ X := IsScalarTower.continuousSMul 𝕜
  let : LocallyConvexSpace ℝ X :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin B.flip))
  apply Set.Subset.antisymm
  · intro x hx
    by_contra houtside
    obtain ⟨f, c, hf, hfx⟩ := RCLike.geometric_hahn_banach_closed_point
      (𝕜 := 𝕜) (aconv_convex A).closure isClosed_closure houtside
    have hc : 0 < c := by
      simpa using hf 0 (subset_closure (zero_mem_aconv A))
    have hbound : ∀ z ∈ closure (aconv 𝕜 A), ‖f z‖ ≤ c :=
      norm_le_of_re_le_on_balanced (aconv_balanced A).closure f.toLinearMap hc.le
        (fun z hz => (hf z hz).le)
    let g : X →L[𝕜] 𝕜 := (c : 𝕜)⁻¹ • f
    obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective B.flip g
    have heval (z : X) : B y z = g z :=
      congrArg (fun L : StrongDual 𝕜 (WeakBilin B.flip) => L z) hy
    have hyg : y ∈ B.flip.polar A := by
      intro a ha
      change ‖B y a‖ ≤ 1
      rw [heval]
      change ‖(c : 𝕜)⁻¹ * f a‖ ≤ 1
      rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hc]
      apply (inv_mul_le_iff₀ hc).mpr
      simpa using hbound a (subset_closure (subset_aconv A ha))
    have hgx := hx y hyg
    change ‖B y x‖ ≤ 1 at hgx
    rw [heval] at hgx
    change ‖(c : 𝕜)⁻¹ * f x‖ ≤ 1 at hgx
    rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hc] at hgx
    have hnorm : ‖f x‖ ≤ c := by
      simpa using (inv_mul_le_iff₀ hc).mp hgx
    exact (hfx.trans_le ((RCLike.re_le_norm (f x)).trans hnorm)).false
  · intro x hx y hy
    have hcont : Continuous (B y) := WeakBilin.eval_continuous B.flip y
    exact closure_minimal (norm_le_one_on_aconv (B y) A hy)
      (isClosed_le hcont.norm continuous_const) hx

/-- The manuscript's identity on the original vector carrier, with the
accepted initial pairing topology and both separation hypotheses. -/
theorem bipolar_theorem : Spec.Bipolar := by
  intro 𝕜 X Y _ _ _ _ _ B _ _ A
  change B.polar (B.flip.polar A) =
    @closure (WeakBilin B.flip)
      (TopologicalSpace.induced id (WeakBilin.instTopologicalSpace B.flip)) _
  rw [induced_id]
  exact bipolar_weak B A

theorem aconv_submodule (M : Submodule 𝕜 X) : aconv 𝕜 (M : Set X) = M := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, c, y, hy, _, rfl⟩
    exact M.sum_mem fun i _ => M.smul_mem _ (hy i)
  · exact subset_aconv _

/-- Taking the polar of an algebraic span is exactly annihilation of its
generators: the polar bound on a whole scalar line forces value zero. -/
theorem polar_span_eq_annihilator (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (A : Set X) :
    B.flip.polar (Submodule.span 𝕜 A : Set X) = annihilator B A := by
  rw [B.flip.polar_subMulAction (Submodule.span 𝕜 A)]
  ext y
  change (∀ x ∈ Submodule.span 𝕜 A, B y x = 0) ↔ ∀ x ∈ A, B y x = 0
  constructor
  · intro h x hx
    exact h x (Submodule.subset_span hx)
  · intro h x hx
    have hk : Submodule.span 𝕜 A ≤ (B y).ker := Submodule.span_le.mpr h
    exact hk hx

/-- An annihilator is itself a submodule, so its polar is its annihilator. -/
theorem polar_annihilator (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (A : Set X) :
    B.polar (annihilator B A) = annihilator B.flip (annihilator B A) := by
  let N : Submodule 𝕜 Y := ⨅ x ∈ A, (B.flip x).ker
  have hN : (N : Set Y) = annihilator B A := by
    ext y
    simp [N, annihilator]
  rw [← hN, B.polar_subMulAction N]
  rfl

theorem double_annihilator : Spec.DoubleAnnihilator := by
  intro 𝕜 X Y _ _ _ _ _ B hl hr A
  have h := bipolar_theorem 𝕜 X Y B hl hr (Submodule.span 𝕜 A : Set X)
  rw [aconv_submodule, polar_span_eq_annihilator, polar_annihilator] at h
  exact h

theorem double_annihilator_flip : Spec.DoubleAnnihilatorFlip := by
  intro 𝕜 X Y _ _ _ _ _ B hl hr D
  exact double_annihilator 𝕜 Y X B.flip
    (LinearMap.flip_separatingLeft.mpr hr) (LinearMap.flip_separatingRight.mpr hl) D

/-- Reuse the independently established compatible-topology theorem. -/
theorem compatible_closed_convex_sets : Spec.CompatibleClosedConvex :=
  ExpandedFA.P1.compatible_convex_closed_sets

end
end ExpandedFA.P1.GeneralBipolar
