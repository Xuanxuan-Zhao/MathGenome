import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyDualBMORepresentation

/-! The full duality of paper.tex, fa2:p4:hardy-bmo-dual. Scalars are real or
complex and dimension zero is retained. `Represents` means the actual integral
on finite atomic sums; its continuous extension need not be a global Lebesgue
product integral. -/
noncomputable section
open MeasureTheory
namespace ExpandedFA.Hardy.HardyBMODualitySpec
open HardyDualBMORepresentationSpec BMOQuotientSpec

/-- Every BMO function gives a unique continuous scalar-linear extension. -/
def BMOExtension : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (g : BMOFunctionValue d 𝕜),
    ∃ L : H1 d 𝕜 →L[𝕜] 𝕜,
      Represents L g.val ∧ ‖L‖ ≤ 4 * (BMOENormValue g.val).toReal ∧
      ∀ L' : H1 d 𝕜 →L[𝕜] 𝕜, Represents L' g.val → L' = L

/-- Both directions, uniqueness modulo constants, and equivalent norms with
one upper constant depending only on dimension. -/
def Duality : Prop :=
  BMOExtension ∧
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (𝕜 : Type) [RCLike 𝕜],
    (∀ L : H1 d 𝕜 →L[𝕜] 𝕜, ∃ g : BMOFunctionValue d 𝕜, Represents L g.val) ∧
    (∀ (g : BMOFunctionValue d 𝕜) (L : H1 d 𝕜 →L[𝕜] 𝕜), Represents L g.val →
      ‖L‖ ≤ 4 * (BMOENormValue g.val).toReal ∧
      (BMOENormValue g.val).toReal ≤ C * ‖L‖ ∧
      ∀ g' : BMOFunctionValue d 𝕜,
        Represents L g'.val ↔ ModConstantsValue g' g)
end ExpandedFA.Hardy.HardyBMODualitySpec
