import MathGenome.Internal.LinearPDE.P201Specs.Integral.Fredholm
import MathGenome.Internal.LinearPDE.P201.Integral.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.DualFredholm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.AtkinsonParametrices
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.FredholmKernel

noncomputable section
universe u
namespace P201.Integral.Fredholm
open ExpandedFA

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The evaluation pairing with the continuous dual is nondegenerate by
Hahn–Banach, including on the zero space. -/
def evaluationDualSystem : ExpandedFA.Fredholm.DualSystem E (StrongDual ℂ E) where
  pairing := ContinuousLinearMap.coeLM ℂ
  separatesLeft := by
    intro x hx
    by_contra hn
    obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hn
    exact hℓ (hx ℓ)
  separatesRight := by
    intro ℓ hℓ
    ext x
    exact hℓ x

/-- The continuous dual of the closed cokernel is precisely the transpose
kernel, by pullback along the quotient map. -/
def quotientDualEquivTransposeKernel (F : E →L[ℂ] E) :
    StrongDual ℂ (E ⧸ F.range) ≃ₗ[ℂ] (Spec.transpose F).ker := by
  let j : StrongDual ℂ (E ⧸ F.range) →ₗ[ℂ] (Spec.transpose F).ker := {
    toFun := fun ℓ => ⟨ℓ.comp F.range.mkQL, by
      ext x
      change ℓ (F.range.mkQ (F x)) = 0
      rw [show F.range.mkQ (F x) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero]⟩
    map_add' := by intro f g; rfl
    map_smul' := by intro a f; rfl }
  apply LinearEquiv.ofBijective j
  constructor
  · intro f g hfg
    ext z
    obtain ⟨y, rfl⟩ := F.range.mkQ_surjective z
    exact congrArg (fun ℓ => (ℓ.val : StrongDual ℂ E) y) hfg
  · intro ℓ
    have hvan : F.range ≤ ℓ.val.ker := by
      rintro y ⟨x, rfl⟩
      exact DFunLike.congr_fun ℓ.property x
    refine ⟨F.range.liftQL ℓ.val hvan, ?_⟩
    apply Subtype.ext
    ext x
    rfl

/-- Cokernel dimension equals transpose-kernel dimension. The closedness
hypothesis ensures the quotient is Hausdorff before identifying its dual. -/
lemma cokernel_finrank (F : E →L[ℂ] E)
    (hc : IsClosed (F.range : Set E))
    [FiniteDimensional ℂ (E ⧸ F.range)] :
    Module.finrank ℂ (E ⧸ F.range) = Module.finrank ℂ (Spec.transpose F).ker := by
  let : IsClosed (F.range : Set E) := hc
  calc
    Module.finrank ℂ (E ⧸ F.range) =
        Module.finrank ℂ (Module.Dual ℂ (E ⧸ F.range)) := Subspace.dual_finrank_eq.symm
    _ = Module.finrank ℂ (StrongDual ℂ (E ⧸ F.range)) :=
      (LinearMap.toContinuousLinearMap :
        Module.Dual ℂ (E ⧸ F.range) ≃ₗ[ℂ] StrongDual ℂ (E ⧸ F.range)).finrank_eq
    _ = Module.finrank ℂ (Spec.transpose F).ker :=
      (quotientDualEquivTransposeKernel F).finrank_eq

/-- The full Fredholm bridge for a compact operator on a complex Banach
space. Normalization is used only in the proof: the conclusion concerns zI−T. -/
theorem compact_fredholm_conclusion [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsCompactOperator T) (z : ℂ) (hz : z ≠ 0) :
    Spec.Conclusion T z := by
  let S := z⁻¹ • T
  let A := ContinuousLinearMap.id ℂ E - S
  let B := ContinuousLinearMap.id ℂ (StrongDual ℂ E) - Spec.transpose S
  let F := Spec.fredholmMap T z
  have hS : Compactness.IsCompactLinearMap S.toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr (hT.smul z⁻¹)
  have hSt : Compactness.IsCompactLinearMap (Spec.transpose S).toLinearMap :=
    Compactness.SchauderAdjoints.compact_banachTranspose ℂ E E S hS
  obtain ⟨hfinA, hfinB, hdim, halt, _, _⟩ :=
    ExpandedFA.Fredholm.dual_fredholm_bounded evaluationDualSystem S
      (Spec.transpose S) hS hSt (fun _ _ => rfl)
  have hfac : F = z • A := by
    ext x
    simp [F, Spec.fredholmMap, A, S, smul_sub, smul_smul, hz]
  have htfac : Spec.transpose F = z • B := by
    ext ℓ x
    change ℓ (F x) = z • (ℓ x - ℓ (S x))
    rw [hfac]
    simp [A, map_sub]
  have hker : F.ker = A.ker := by
    rw [hfac]
    exact LinearMap.ker_smul A.toLinearMap z hz
  have hrange : F.range = A.range := by
    rw [hfac]
    exact LinearMap.range_smul A.toLinearMap z hz
  have htker : (Spec.transpose F).ker = B.ker := by
    rw [htfac]
    exact LinearMap.ker_smul B.toLinearMap z hz
  have hc : IsClosed (F.range : Set E) := by
    rw [hrange]
    exact (ExpandedFA.Fredholm.riesz_schauder S hS).2.1
  have hf : FiniteDimensional ℂ F.ker := hker.symm ▸ hfinA
  have hft : FiniteDimensional ℂ (Spec.transpose F).ker := htker.symm ▸ hfinB
  let : FiniteDimensional ℂ
      (P1.C04Annihilators.banachTranspose ℂ E E F).ker := hft
  have hq : FiniteDimensional ℂ (E ⧸ F.range) :=
    ExpandedFA.Fredholm.finiteDimensional_cokernel_of_transpose_kernel F hc
  let := hq
  have hdimFT : Module.finrank ℂ F.ker = Module.finrank ℂ (Spec.transpose F).ker := by
    rw [hker, htker]
    exact hdim
  have hdimQ := cokernel_finrank F hc
  refine ⟨?_, hc, hf, hq, hft, hdimFT.trans hdimQ.symm, hdimQ, ?_, ?_, ?_⟩
  · ext ℓ x
    change ℓ (z • x - T x) = z • ℓ x - ℓ (T x)
    simp only [map_sub, map_smul]
  · intro g
    exact PartV.FredholmKernel.solvable_iff_transpose F hc g
  · intro g f₀ hf₀ f
    constructor
    · intro h
      refine ⟨f - f₀, ?_, by abel⟩
      change F (f - f₀) = 0
      rw [map_sub, h, hf₀, sub_self]
    · rintro ⟨v, hv, rfl⟩
      change F v = 0 at hv
      rw [map_add, hv, add_zero, hf₀]
  · rcases halt with hb | hp
    · have hbij : Function.Bijective F := by
        rw [hfac]
        refine ⟨?_, ?_⟩
        · intro x y hxy
          apply hb.1.1
          exact (smul_right_injective _ hz) hxy
        · intro y
          obtain ⟨x, hx⟩ := hb.1.2 (z⁻¹ • y)
          refine ⟨x, ?_⟩
          change A x = z⁻¹ • y at hx
          change z • A x = y
          rw [hx, smul_inv_smul₀ hz]
      exact Or.inl ⟨ContinuousLinearEquiv.ofBijective F
        (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), fun _ => rfl⟩
    · apply Or.inr
      change 0 < Module.finrank ℂ F.ker ∧
        0 < Module.finrank ℂ (Spec.transpose F).ker
      rw [hker, htker]
      exact hp

/-- The source theorem for the actual continuous-kernel operator on C(K,ℂ),
with no restrictions on the compact Hausdorff space beyond those stated. -/
theorem fredholm_kernel_theorem : Spec.FullTheorem.{u} := by
  refine ⟨ContinuousKernel.continuous_kernel_theorem, ?_⟩
  intro K _ _ _ _ _ μ _ k z hz
  apply compact_fredholm_conclusion _ _ z hz
  exact (ContinuousKernel.continuous_kernel_theorem K μ k).2.2.2.1

end P201.Integral.Fredholm
