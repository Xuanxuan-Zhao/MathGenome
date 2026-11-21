import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.DualRegularizerFiniteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.DualSystems
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactDefectStabilization
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace ExpandedFA.Fredholm
noncomputable section
universe u₁ v₁ u₂ v₂
open Module
variable {𝕂 : Type*} [RCLike 𝕂]

/-- A finite family of algebraic functionals supplies all functionals
annihilating any subspace containing their common kernel. -/
lemma annihilator_le_pairing_range {X : Type u₁} {Y : Type v₁}
    [AddCommGroup X] [Module 𝕂 X] [AddCommGroup Y] [Module 𝕂 Y]
    (C : Y →ₗ[𝕂] Module.Dual 𝕂 X) (P : Submodule 𝕂 X) (N : Submodule 𝕂 Y)
    [FiniteDimensional 𝕂 N]
    (h : (C.comp N.subtype).flip.ker ≤ P) : P.dualAnnihilator ≤ C.range := by
  have hle := (Subspace.dualAnnihilator_le_dualAnnihilator_iff).mpr h
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip] at hle
  intro φ hφ
  obtain ⟨y, hy⟩ := hle hφ
  exact ⟨y.val, hy⟩

variable {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
  [NormedAddCommGroup X₁] [NormedSpace 𝕂 X₁]
  [NormedAddCommGroup Y₁] [NormedSpace 𝕂 Y₁]
  [NormedAddCommGroup X₂] [NormedSpace 𝕂 X₂]
  [NormedAddCommGroup Y₂] [NormedSpace 𝕂 Y₂]

/-- If all algebraic functionals vanishing on the range are represented by
the given pairing, the paired kernel is precisely the dual of the cokernel. -/
lemma paired_range_duality (C₁ : Y₁ →ₗ[𝕂] X₁ →ₗ[𝕂] 𝕂) (C₂ : Y₂ →ₗ[𝕂] X₂ →ₗ[𝕂] 𝕂)
    (h₁ : ∀ y, (∀ x, C₁ y x = 0) → y = 0)
    (h₂ : ∀ y, (∀ f, C₂ y f = 0) → y = 0)
    (T : X₁ →L[𝕂] X₂) (U : Y₂ →L[𝕂] Y₁)
    (hpair : ∀ x y, C₂ y (T x) = C₁ (U y) x)
    [FiniteDimensional 𝕂 U.toLinearMap.ker]
    (hrep : T.toLinearMap.range.dualAnnihilator ≤ C₂.range) :
    FiniteDimensional 𝕂 (X₂ ⧸ T.toLinearMap.range) ∧
    (∀ f : X₂, f ∈ T.toLinearMap.range ↔
      ∀ y : Y₂, y ∈ U.toLinearMap.ker → C₂ y f = 0) ∧
    finrank 𝕂 (X₂ ⧸ T.toLinearMap.range) = finrank 𝕂 U.toLinearMap.ker := by
  let P := T.toLinearMap.range
  have hann (y : Y₂) : C₂ y ∈ P.dualAnnihilator ↔ U y = 0 := by
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hy
      apply h₁
      intro x
      exact (hpair x y).symm.trans (hy (T x) ⟨x, rfl⟩)
    · intro hy f hf
      obtain ⟨x, rfl⟩ := hf
      change C₂ y (T x) = 0
      rw [hpair, hy, map_zero, LinearMap.zero_apply]
  let j : U.toLinearMap.ker →ₗ[𝕂] P.dualAnnihilator := {
    toFun := fun y => ⟨C₂ y, (hann y).mpr y.property⟩
    map_add' := fun y z => Subtype.ext (C₂.map_add y z)
    map_smul' := fun c y => Subtype.ext (C₂.map_smul c y) }
  have hj : Function.Bijective j := by
    constructor
    · intro y z heq
      apply Subtype.ext
      have hz : (y : Y₂) - z = 0 := h₂ _ (fun f => by
        have hf := LinearMap.congr_fun (congrArg Subtype.val heq) f
        change C₂ (y : Y₂) f = C₂ (z : Y₂) f at hf
        simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using hf)
      exact sub_eq_zero.mp hz
    · intro φ
      obtain ⟨y, hy⟩ := hrep φ.property
      refine ⟨⟨y, (hann y).mp ?_⟩, Subtype.ext hy⟩
      rw [hy]
      exact φ.property
  let e := LinearEquiv.ofBijective j hj
  have : FiniteDimensional 𝕂 P.dualAnnihilator := e.finiteDimensional
  have hfinite : FiniteDimensional 𝕂 (X₂ ⧸ P) := Submodule.finite_dualAnnihilator_iff.mp inferInstance
  refine ⟨hfinite, ?_, ?_⟩
  · intro f
    constructor
    · rintro ⟨x, rfl⟩ y hy
      change C₂ y (T x) = 0
      rw [hpair, show U y = 0 from hy, map_zero, LinearMap.zero_apply]
    · intro hf
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff P f).mp
      intro φ hφ
      obtain ⟨y, hy⟩ := hj.surjective ⟨φ, hφ⟩
      have heq : C₂ y = φ := congrArg Subtype.val hy
      rw [← heq]
      exact hf y y.property
  · calc
      finrank 𝕂 (X₂ ⧸ P) = finrank 𝕂 (Module.Dual 𝕂 (X₂ ⧸ P)) :=
        (Subspace.dual_finrank_eq).symm
      _ = finrank 𝕂 P.dualAnnihilator := P.dualQuotEquivDualAnnihilator.finrank_eq
      _ = finrank 𝕂 U.toLinearMap.ker := e.finrank_eq.symm


/-- The bilinear adjoint equation propagates to powers over either scalar field. -/
lemma bilinear_paired_power {E : Type u₁} {F : Type v₁}
    [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
    (C : F →ₗ[𝕂] E →ₗ[𝕂] 𝕂) (a : E →ₗ[𝕂] E) (b : F →ₗ[𝕂] F)
    (hab : ∀ x y, C y (a x) = C (b y) x) (p : ℕ) (x : E) (y : F) :
    C y ((a ^ p) x) = C ((b ^ p) y) x := by
  induction p generalizing y with
  | zero => rfl
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply, hab, ih, pow_succ, Module.End.mul_apply]

/-- Complementary power kernels and ranges force a vector annihilating the
paired power kernel to belong to the original range. This argument uses
nondegeneracy and algebraic splittings, without continuity of the pairing. -/
lemma annihilator_power_kernel_le_range {E : Type u₁} {F : Type v₁}
    [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
    (C : F →ₗ[𝕂] E →ₗ[𝕂] 𝕂)
    (hE : ∀ x, (∀ y, C y x = 0) → x = 0)
    (a : E →ₗ[𝕂] E) (b : F →ₗ[𝕂] F)
    (hab : ∀ x y, C y (a x) = C (b y) x) (p : ℕ) (hp : 1 ≤ p)
    (hEa : IsCompl (a ^ p).ker (a ^ p).range)
    (hFb : IsCompl (b ^ p).ker (b ^ p).range) :
    (C.comp (b ^ p).ker.subtype).flip.ker ≤ a.range := by
  intro f hf
  obtain ⟨n, r, hn, hr, hnr⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp hEa.codisjoint f
  have hnann (y : (b ^ p).ker) : C y n = 0 := by
    have heq := LinearMap.congr_fun hf y
    change C y f = 0 at heq
    obtain ⟨z, hz⟩ := hr
    have hrann : C y r = 0 := by
      rw [← hz, bilinear_paired_power C a b hab, y.property, map_zero, LinearMap.zero_apply]
    rw [← hnr, map_add, hrann, add_zero] at heq
    exact heq
  have hnzero : n = 0 := by
    apply hE
    intro y
    obtain ⟨s, t, hs, ht, hst⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hFb.codisjoint y
    obtain ⟨z, rfl⟩ := ht
    rw [← hst, map_add, LinearMap.add_apply, hnann ⟨s, hs⟩, zero_add,
      ← bilinear_paired_power C a b hab, show (a ^ p) n = 0 from hn, map_zero]
  have hrf : r = f := by simpa only [hnzero, zero_add] using hnr
  obtain ⟨z, hz⟩ := hr
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  refine ⟨(a ^ q) z, ?_⟩
  rw [hq, pow_succ', Module.End.mul_apply] at hz
  exact hz.trans hrf

/-- Two compact defects on the target dual system suffice for the range
and the paired kernel. Riesz splittings are valid in the original normed
spaces; their finite-dimensional parts supply the needed algebraic duals. -/
lemma right_regularizer_range_finiteness
    (C₁ : Y₁ →ₗ[𝕂] X₁ →ₗ[𝕂] 𝕂) (C₂ : Y₂ →ₗ[𝕂] X₂ →ₗ[𝕂] 𝕂)
    (h₁ : ∀ y, (∀ x, C₁ y x = 0) → y = 0)
    (h₂X : ∀ f, (∀ y, C₂ y f = 0) → f = 0)
    (h₂Y : ∀ y, (∀ f, C₂ y f = 0) → y = 0)
    (T : X₁ →L[𝕂] X₂) (U : Y₂ →L[𝕂] Y₁)
    (R : X₂ →L[𝕂] X₁) (V : Y₁ →L[𝕂] Y₂)
    (hT : ∀ x y, C₂ y (T x) = C₁ (U y) x)
    (hR : ∀ f g, C₁ g (R f) = C₂ (V g) f)
    (hX : Compactness.IsCompactLinearMap
      (ContinuousLinearMap.id 𝕂 X₂ - T.comp R).toLinearMap)
    (hY : Compactness.IsCompactLinearMap
      (ContinuousLinearMap.id 𝕂 Y₂ - V.comp U).toLinearMap) :
    FiniteDimensional 𝕂 U.toLinearMap.ker ∧
    IsClosed (T.toLinearMap.range : Set X₂) ∧
    FiniteDimensional 𝕂 (X₂ ⧸ T.toLinearMap.range) ∧
    (∀ f : X₂, f ∈ T.toLinearMap.range ↔
      ∀ y : Y₂, y ∈ U.toLinearMap.ker → C₂ y f = 0) ∧
    finrank 𝕂 (X₂ ⧸ T.toLinearMap.range) = finrank 𝕂 U.toLinearMap.ker := by
  let A := T.comp R
  let B := V.comp U
  let K := ContinuousLinearMap.id 𝕂 X₂ - A
  let L := ContinuousLinearMap.id 𝕂 Y₂ - B
  have hAB (f : X₂) (y : Y₂) : C₂ y (A f) = C₂ (B y) f :=
    (hT (R f) y).trans (hR f (U y))
  have hAe : LinearMap.id - K.toLinearMap = A.toLinearMap := sub_sub_cancel _ _
  have hBe : LinearMap.id - L.toLinearMap = B.toLinearMap := sub_sub_cancel _ _
  have hAclm : ContinuousLinearMap.id 𝕂 X₂ - K = A := sub_sub_cancel _ _
  have hBclm : ContinuousLinearMap.id 𝕂 Y₂ - L = B := sub_sub_cancel _ _
  obtain ⟨q, hq, hq'⟩ := riesz_decomposition K hX
  obtain ⟨r, hr, hr'⟩ := riesz_decomposition L hY
  let p := max q r
  have hp : 1 ≤ p := hq.trans (le_max_left q r)
  have dK := (hq' p (le_max_left q r)).2.2
  have dL := (hr' p (le_max_right q r)).2.2
  have hEa : IsCompl (A.toLinearMap ^ p).ker (A.toLinearMap ^ p).range := by
    simpa only [CompactDefectStabilizationSpec.kernelChain,
      CompactDefectStabilizationSpec.rangeChain, hAclm] using dK.1.isCompl
  have hFb : IsCompl (B.toLinearMap ^ p).ker (B.toLinearMap ^ p).range := by
    simpa only [CompactDefectStabilizationSpec.kernelChain,
      CompactDefectStabilizationSpec.rangeChain, hBclm] using dL.1.isCompl
  have : FiniteDimensional 𝕂 (B.toLinearMap ^ p).ker := by
    have h := dL.2.2.1
    change FiniteDimensional 𝕂 ((ContinuousLinearMap.id 𝕂 Y₂ - L).toLinearMap ^ p).ker at h
    rw [hBclm] at h
    exact h
  have hrepA : A.toLinearMap.range.dualAnnihilator ≤ C₂.range :=
    annihilator_le_pairing_range C₂ A.toLinearMap.range (B.toLinearMap ^ p).ker
      (annihilator_power_kernel_le_range C₂ h₂X A.toLinearMap B.toLinearMap hAB p hp hEa hFb)
  have : FiniteDimensional 𝕂 B.toLinearMap.ker := by
    have h := (identity_sub_compact_kernel_closed_finite_dimensional L hY).2
    rwa [hBe] at h
  have hdualA := paired_range_duality C₂ C₂ h₂Y h₂Y A B hAB hrepA
  have : FiniteDimensional 𝕂 (X₂ ⧸ A.toLinearMap.range) := hdualA.1
  have hsmall : A.toLinearMap.range ≤ T.toLinearMap.range := by
    rintro f ⟨z, rfl⟩
    exact ⟨R z, rfl⟩
  have hclosedA : IsClosed (A.toLinearMap.range : Set X₂) := by
    have h := identity_sub_compact_closed_range K hX
    change IsClosed ((LinearMap.id - K.toLinearMap).range : Set X₂) at h
    rwa [hAe] at h
  have hclosed := Submodule.isClosed_mono_of_finiteDimensional_quotient hclosedA hsmall
  have hker : U.toLinearMap.ker ≤ B.toLinearMap.ker := by
    intro y hy
    change V (U y) = 0
    rw [show U y = 0 from hy, map_zero]
  have : FiniteDimensional 𝕂 U.toLinearMap.ker := Submodule.finiteDimensional_of_le hker
  have hrep : T.toLinearMap.range.dualAnnihilator ≤ C₂.range :=
    ((Subspace.dualAnnihilator_le_dualAnnihilator_iff).mpr hsmall).trans hrepA
  have hd := paired_range_duality C₁ C₂ h₁ h₂Y T U hT hrep
  exact ⟨inferInstance, hclosed, hd⟩

/-- The real-or-complex form under the global scalar convention of the source. -/
theorem bilinear_regularizer_finiteness :
    DualRegularizerFinitenessSpec.BilinearRegularizerFiniteness
      (𝕂 := 𝕂) (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂) := by
  intro C₁ C₂ T U R V h₁X h₁Y h₂X h₂Y hT hR hX₁ hX₂ hY₁ hY₂
  obtain ⟨hUker, hTrange, hTcoker, hTann, hTdim⟩ :=
    right_regularizer_range_finiteness C₁ C₂ h₁Y h₂X h₂Y T U R V hT hR hX₂ hY₂
  obtain ⟨hTker, hUrange, hUcoker, hUann, hUdim⟩ :=
    right_regularizer_range_finiteness C₂.flip C₁.flip h₂X h₁Y h₁X
      U T V R (fun y x => (hT x y).symm) (fun g f => (hR f g).symm) hY₁ hX₁
  exact ⟨hTker, hUker, hTrange, hUrange, hTcoker, hUcoker, hTann, hUann, hTdim, hUdim⟩

end
end ExpandedFA.Fredholm

namespace ExpandedFA.Fredholm
universe u₁ v₁ u₂ v₂

/-- The shared complex dual-system interface is the direct specialization
of the scalar-general theorem. -/
theorem dual_regularizer_finiteness
    {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
    [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂] :
    DualRegularizerFinitenessSpec.RegularizerFiniteness
      (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂) := by
  intro D₁ D₂ T U R V hT hR hX₁ hX₂ hY₁ hY₂
  exact bilinear_regularizer_finiteness D₁.pairing D₂.pairing T U R V
    D₁.separatesLeft D₁.separatesRight D₂.separatesLeft D₂.separatesRight
    hT hR hX₁ hX₂ hY₁ hY₂

end ExpandedFA.Fredholm
