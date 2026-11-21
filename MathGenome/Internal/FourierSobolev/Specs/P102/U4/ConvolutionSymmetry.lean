import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionConvolution

/-! Independent statements for the interchange and full convolution theorem of
paper.tex:1392–1410. Pairings are bilinear, over either real or complex scalars.
Neither interchange nor symmetry is included among the assumptions here. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions Pointwise
namespace P102.U4

abbrev ProductTests (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :=
  TestFunction (⊤ : Opens (Space d × Space d)) 𝕜 ⊤

/-- Restricting a compactly supported two-variable test to a vertical slice. -/
def productRightSlice {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Φ : ProductTests d 𝕜) (x : Space d) : WholeTests d 𝕜 where
  toFun y := Φ (x, y)
  contDiff' := Φ.contDiff.comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport' := HasCompactSupport.intro
    (Φ.hasCompactSupport.image continuous_snd) (by
      intro y hy
      by_contra h
      exact hy ⟨(x, y), subset_tsupport Φ h, rfl⟩)
  tsupport_subset' := subset_univ _

/-- The horizontal slice; the order of the two arguments is preserved. -/
def productLeftSlice {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Φ : ProductTests d 𝕜) (y : Space d) : WholeTests d 𝕜 where
  toFun x := Φ (x, y)
  contDiff' := Φ.contDiff.comp (contDiff_id.prodMk contDiff_const)
  hasCompactSupport' := HasCompactSupport.intro
    (Φ.hasCompactSupport.image continuous_fst) (by
      intro x hx
      by_contra h
      exact hx ⟨(x, y), subset_tsupport Φ h, rfl⟩)
  tsupport_subset' := subset_univ _

abbrev ConvolutionFamily (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :=
  (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) →
    (IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) →
    DistributionSpace 𝕜 (⊤ : Opens (Space d))

/-- The complete preceding convolution conclusion for one specified operation. -/
def ConvolutionLaws {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (C : ConvolutionFamily d 𝕜) : Prop :=
  (∀ T S hS φ,
        ∃ ψ : WholeTests d 𝕜, (∀ x, ψ x = convolutionInner S φ x) ∧
          C T S (Or.inr hS) φ = T ψ) ∧
      (∀ T S h, relativeSupport (C T S h) ⊆ relativeSupport T + relativeSupport S) ∧
      (∀ (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
          (hS : IsCompact (relativeSupport S)) (α : MultiIndex d),
        (∃ hα : IsCompact (relativeSupport (distributionPartial α S)),
          distributionPartial α (C T S (Or.inr hS)) =
            C T (distributionPartial α S) (Or.inr hα)) ∧
        distributionPartial α (C T S (Or.inr hS)) =
          C (distributionPartial α T) S (Or.inr hS)) ∧
      (∀ (T : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (ρ : WholeTests d 𝕜),
        ∃ hρ : IsCompact (relativeSupport (regularDistribution ⊤ ρ)),
          C T (regularDistribution ⊤ ρ) (Or.inr hρ) =
            regularDistribution ⊤ (localConvolution T ρ)) ∧
      (∀ (f g : Space d → 𝕜),
        LocallyIntegrable f volume → LocallyIntegrable g volume →
        (HasCompactEssentialSupport f ∨ HasCompactEssentialSupport g) →
        (∀ᵐ x ∂volume, Integrable (fun y => f (x - y) * g y) volume) ∧
        LocallyIntegrable (functionConvolution f g) volume ∧
        ∃ h : IsCompact (relativeSupport (regularDistribution ⊤ f)) ∨
              IsCompact (relativeSupport (regularDistribution ⊤ g)),
          C (regularDistribution ⊤ f) (regularDistribution ⊤ g) h =
            regularDistribution ⊤ (functionConvolution f g))

/-- Both derivative identities, including when only the first factor is compact.
The witnesses certify that every convolution on the right is defined. -/
def ConvolutionDerivativeLaws {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (C : ConvolutionFamily d 𝕜) : Prop :=
  ∀ (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (h : IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) (α : MultiIndex d),
    (∃ hTα : IsCompact (relativeSupport (distributionPartial α T)) ∨ IsCompact (relativeSupport S),
      distributionPartial α (C T S h) = C (distributionPartial α T) S hTα) ∧
    (∃ hSα : IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport (distributionPartial α S)),
      distributionPartial α (C T S h) = C T (distributionPartial α S) hSα)

/-- Equality with one on an open neighborhood of a specified set. -/
def IsOneNear {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (η : WholeTests d 𝕜) (A : Set (Space d)) : Prop :=
  ∃ U : Opens (Space d), A ⊆ U ∧ ∀ x ∈ U, η x = 1

namespace ConvolutionSymmetryExpected

/-- Both inner pairings are actual tests and their outer pairings agree.
The distributions are arbitrary: neither needs compact support. -/
def Interchange : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (Φ : ProductTests d 𝕜),
    ∃ ψ θ : WholeTests d 𝕜,
      (∀ x, ψ x = S (productRightSlice Φ x)) ∧
      (∀ y, θ y = T (productLeftSlice Φ y)) ∧ T ψ = S θ

/-- Full U4-04, including both orders when only one factor is compact.
The last clause specifies both orders with arbitrary requisite cutoffs, so their
values are independent of these cutoffs. -/
def Convolution : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜],
    ∃ C : ConvolutionFamily d 𝕜,
      ConvolutionLaws C ∧ ConvolutionDerivativeLaws C ∧
      (∀ T S h, C T S h = C S T h.symm) ∧
      (∀ (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))),
        IsCompact (relativeSupport S) → ∀ φ : WholeTests d 𝕜,
        ∃ χ η : WholeTests d 𝕜,
          IsSupportCutoff S χ ∧ IsOneNear η (tsupport φ - relativeSupport S)) ∧
      (∀ (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
        (hS : IsCompact (relativeSupport S)) (φ χ η : WholeTests d 𝕜),
        IsSupportCutoff S χ → IsOneNear η (tsupport φ - relativeSupport S) →
        ∃ ψ θ : WholeTests d 𝕜,
          (∀ x, ∃ σ : WholeTests d 𝕜,
            (∀ y, σ y = η x * χ y * φ (x + y)) ∧ ψ x = S σ) ∧
          (∀ y, ∃ τ : WholeTests d 𝕜,
            (∀ x, τ x = η x * χ y * φ (x + y)) ∧ θ y = T τ) ∧
          C T S (Or.inr hS) φ = T ψ ∧ T ψ = S θ)

end ConvolutionSymmetryExpected
end P102.U4
