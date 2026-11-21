import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyDisk
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Independent statements for the commutant assertion in
`paper.tex`, Proposition `fa2:p4:hardy-divisibility`, first sentence.
The symbols are all bounded holomorphic functions on the open disk, and
the operators act on the canonical coefficient Hilbert space. -/
noncomputable section
open scoped ComplexConjugate

namespace ExpandedFA.PartIV.HardyCommutantSpec
open HardyDiskSpec

def CommutesWithShift (T : H2 →L[ℂ] H2) : Prop :=
  ∀ f : H2, T (shift f) = shift (T f)

def IsMultiplication (T : H2 →L[ℂ] H2) (b : HInfinity) : Prop :=
  ∀ (f : H2) (z : Disk), eval (T f) z = b.val z * eval f z

def ReproducingKernel : Prop := ∀ z : Disk, ∃ k : H2,
  (∀ n : ℕ, k n = (conj z.val) ^ n) ∧
  (∀ f : H2, inner ℂ k f = eval f z) ∧
  ‖k‖ = (Real.sqrt (1 - ‖z.val‖ ^ 2))⁻¹

def KernelTest : Prop := ∀ (T : H2 →L[ℂ] H2) (b : HInfinity),
  IsMultiplication T b → ∀ z : Disk, ∃ k : H2,
    (∀ n : ℕ, k n = (conj z.val) ^ n) ∧ k ≠ 0 ∧
    T.adjoint k = conj (b.val z) • k

def PolynomialAction : Prop := ∀ (T : H2 →L[ℂ] H2), CommutesWithShift T →
  ∀ f ∈ Submodule.span ℂ
    (Set.range (fun n : ℕ => lp.single 2 n (1 : ℂ))), ∀ z : Disk,
    eval (T f) z = eval (T (lp.single 2 0 (1 : ℂ))) z * eval f z

def ExtensionFromPolynomials : Prop := ∀ (T : H2 →L[ℂ] H2), CommutesWithShift T →
  ∀ (f : H2) (z : Disk),
    eval (T f) z = eval (T (lp.single 2 0 (1 : ℂ))) z * eval f z

def PointwiseNormBound : Prop := ∀ (T : H2 →L[ℂ] H2) (b : HInfinity),
  IsMultiplication T b → ∀ z : Disk, ‖b.val z‖ ≤ ‖T‖

def MultiplierNormUpper : Prop := ∀ b : HInfinity, ∃ M : H2 →L[ℂ] H2,
  IsMultiplication M b ∧ ‖M‖ ≤ infinityNorm b

def MultiplierNormLower : Prop := ∀ (T : H2 →L[ℂ] H2) (b : HInfinity),
  IsMultiplication T b → infinityNorm b ≤ ‖T‖

def MultiplierNorm : Prop := ∀ (T : H2 →L[ℂ] H2) (b : HInfinity),
  IsMultiplication T b → ‖T‖ = infinityNorm b

def ShiftCommutant : Prop := ∀ T : H2 →L[ℂ] H2, CommutesWithShift T →
  ∃! b : HInfinity, IsMultiplication T b ∧ ‖T‖ = infinityNorm b

def MultiplierCommutes : Prop := ∀ (T : H2 →L[ℂ] H2) (b : HInfinity),
  IsMultiplication T b → CommutesWithShift T

end ExpandedFA.PartIV.HardyCommutantSpec
