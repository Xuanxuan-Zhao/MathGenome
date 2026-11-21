import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Conjugates

/-! The definitions for the full-cone infimal-convolution chapter. All
extended-real conventions and the continuous real dual are inherited from
the shared foundations. These definitions impose no affine-minorant or
proper-conjugate assumption. -/
namespace ExpandedFA.InfimalConvolution.Definitions

open ExpandedFA.P1
open ExtendedConvexFunctions

/-- The finite domain D(φ), reusing the canonical shared definition. -/
abbrev finiteDomain : Spec.FiniteDomainType := ExtendedConvexFunctions.finiteDomain

/-- Cost of the split f=(f−g)+g, with both conjugates taken against E′. -/
noncomputable def conjugateSplitCost (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (φ ψ : ExtendedFunction E)
    (f g : C04Dual.ContinuousDual ℝ E) : EReal :=
  C06Conjugates.convexConjugate E φ (f - g) + C06Conjugates.convexConjugate E ψ g

/-- h(f) = inf_g [φ*(f−g)+ψ*(g)], as a full extended-real infimum. -/
noncomputable def infimalConvolution (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (φ ψ : ExtendedFunction E)
    (f : C04Dual.ContinuousDual ℝ E) : EReal :=
  ⨅ g : C04Dual.ContinuousDual ℝ E, conjugateSplitCost E φ ψ f g

/-- The nonnegative scaling union of differences of finite-domain points. -/
def domainDifferenceCone (E : Type*) [AddCommGroup E] [Module ℝ E]
    (φ ψ : ExtendedFunction E) : Set E :=
  ⋃ (a : ℝ) (_ : 0 ≤ a),
    (fun p : E × E => a • (p.1 - p.2)) '' (finiteDomain E φ ×ˢ finiteDomain E ψ)

theorem mem_finiteDomain : Spec.MemFiniteDomain := by
  intro E φ x
  change φ x ≠ ⊤ ↔ ∃ r : ℝ, φ x = (r : WithTop ℝ)
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
    exact ⟨r, hr.symm⟩
  · rintro ⟨r, hr⟩
    rw [hr]
    exact WithTop.coe_ne_top

theorem infimalConvolution_isGLB : Spec.InfimalConvolutionIsGLB := by
  intro E _ _ φ ψ f
  exact isGLB_iInf

theorem mem_domainDifferenceCone : Spec.MemDomainDifferenceCone := by
  intro E _ _ φ ψ z
  constructor
  · intro hz
    obtain ⟨a, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨ha, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hz
    exact ⟨a, ha, x, y, hx, hy, hxy.symm⟩
  · rintro ⟨a, ha, x, y, hx, hy, hxy⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
      ⟨ha, ⟨(x, y), ⟨hx, hy⟩, hxy.symm⟩⟩⟩

theorem zero_mem_domainDifferenceCone : Spec.ZeroMemDomainDifferenceCone := by
  intro E _ _ φ ψ h
  obtain ⟨x, hx, hy⟩ := h
  exact (mem_domainDifferenceCone E φ ψ 0).mpr
    ⟨0, le_refl 0, x, x, hx, hy, (zero_smul ℝ (x - x)).symm⟩

end ExpandedFA.InfimalConvolution.Definitions
