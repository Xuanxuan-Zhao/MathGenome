import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.ProfiniteIntegers.ResidueModel
import Mathlib.GroupTheory.Index

/-! FT-E08A: projection kernels in the positive-divisibility residue model.
Multiplication by n is repeated addition on the entire compatible-family group.
The closure statements specify the integer multiples inside that same group. -/
namespace Specs.AdvancedFieldTheory.ProjectionKernels

open AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem

def ProjectionSurjective : Prop :=
  ∀ n : ℕ+, Function.Surjective (coordinate n)

def IntegerMultiplesClosure : Prop :=
  ∀ n : ℕ+, closure (Set.range (fun z : ℤ => integerResidues ((n : ℕ) • z))) =
    ((coordinate n).ker : Set ResidueFamily)

def MultiplicationImageClosure : Prop :=
  ∀ n : ℕ+, Set.range (fun a : ResidueFamily => (n : ℕ) • a) =
    closure (Set.range (fun z : ℤ => integerResidues ((n : ℕ) • z)))

def KernelMultiples : Prop :=
  ∀ n : ℕ+, (coordinate n).ker = (nsmulAddMonoidHom (α := ResidueFamily) (n : ℕ)).range

def KernelClopen : Prop :=
  ∀ n : ℕ+, IsClopen ((coordinate n).ker : Set ResidueFamily)

def KernelIndex : Prop :=
  ∀ n : ℕ+, (coordinate n).ker.index = (n : ℕ)

end Specs.AdvancedFieldTheory.ProjectionKernels
