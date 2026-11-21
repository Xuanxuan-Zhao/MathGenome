import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SplittingField.Construction

/-! Concrete counterexamples in K07.12.normal_characterizations, paper.tex:3856–3858.
All fields are generated fields with the usual rational embeddings. The middle
field is represented inside the fourth-root field, so its scalar action on the
top field is the canonical inclusion. Its image in ℝ is explicitly identified
with ℚ(√2). The splitting field in the cubic example is the abstract polynomial
splitting field; no algebraically closed ambient field is assumed. -/

noncomputable section
namespace Specs.D07.Ch12.NormalCharacterizationsNonnormalTowers

open Polynomial IntermediateField

def cubeRoot : ℝ := (2 : ℝ) ^ (3⁻¹ : ℝ)
def fourthRoot : ℝ := Real.sqrt (Real.sqrt 2)
def cubicPolynomial : ℚ[X] := X ^ 3 - C 2
def quarticPolynomial : ℚ[X] := X ^ 4 - C 2
def Cubic : IntermediateField ℚ ℝ := adjoin ℚ {cubeRoot}
def Quartic : IntermediateField ℚ ℝ := adjoin ℚ {fourthRoot}
def Square : IntermediateField ℚ ℝ := adjoin ℚ {Real.sqrt 2}
def fourthGenerator : Quartic := ⟨fourthRoot, mem_adjoin_simple_self ℚ fourthRoot⟩
def Middle : IntermediateField ℚ Quartic := adjoin ℚ {fourthGenerator ^ 2}
abbrev CubicSplittingField := cubicPolynomial.SplittingField

/-- The cubic root field embeds in a normal splitting field but is not normal. -/
def CubicCounterexample : Prop :=
  cubeRoot ^ 3 = 2 ∧
  Module.finrank ℚ Cubic = 3 ∧ ¬ Normal ℚ Cubic ∧
  Polynomial.IsSplittingField ℚ CubicSplittingField cubicPolynomial ∧
  Normal ℚ CubicSplittingField ∧ Nonempty (Cubic →ₐ[ℚ] CubicSplittingField)

/-- The two steps are normal quadratic extensions, while the real total field
misses a nonreal root of its irreducible quartic and is not normal. -/
def TowerCounterexample : Prop :=
  fourthRoot ^ 2 = Real.sqrt 2 ∧ fourthRoot ^ 4 = 2 ∧
  Middle.map Quartic.val = Square ∧
  Module.finrank ℚ Middle = 2 ∧ Module.finrank Middle Quartic = 2 ∧
  Module.finrank ℚ Quartic = 4 ∧
  Normal ℚ Middle ∧ Normal Middle Quartic ∧ ¬ Normal ℚ Quartic ∧
  ∃ z : ℂ, aeval z quarticPolynomial = 0 ∧ z.im ≠ 0 ∧
    ∀ x : Quartic, ((x : ℝ) : ℂ) ≠ z

end Specs.D07.Ch12.NormalCharacterizationsNonnormalTowers
