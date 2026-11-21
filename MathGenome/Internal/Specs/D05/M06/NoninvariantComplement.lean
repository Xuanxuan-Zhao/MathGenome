import MathGenome.Internal.Specs.D05.M06.Invariant
import MathGenome.Internal.Specs.D05.M06.DirectSum
import Mathlib.LinearAlgebra.Prod

/-!
Independent statements for K05.06.noninvariant_complement, paper.tex:1003–1004.
The coordinate plane is `K × K`, with its usual componentwise vector-space
structure. The subspaces are the actual spans of the two standard vectors.
Binary internal direct sums use the upstream unique-decomposition convention.
All statements quantify over every field, including characteristic two.
-/

namespace Specs.D05.M06.NoninvariantComplement

universe u

def e1 (K : Type u) [Field K] : K × K := (1, 0)

def e2 (K : Type u) [Field K] : K × K := (0, 1)

/-- The operator specified by `N(e₁) = 0` and `N(e₂) = e₁`. -/
def nilpotentMap (K : Type u) [Field K] : (K × K) →ₗ[K] (K × K) where
  toFun x := (x.2, 0)
  map_add' x y := by simp
  map_smul' a x := by simp

def line (K : Type u) [Field K] : Submodule K (K × K) :=
  Submodule.span K {e1 K}

def transverseLine (K : Type u) [Field K] : Submodule K (K × K) :=
  Submodule.span K {e2 K}

def operator_values : Prop :=
  ∀ (K : Type u) [Field K],
    nilpotentMap K (e1 K) = 0 ∧ nilpotentMap K (e2 K) = e1 K

def operator_formula : Prop :=
  ∀ (K : Type u) [Field K] (a b : K),
    nilpotentMap K (a • e1 K + b • e2 K) = b • e1 K

def square_zero : Prop :=
  ∀ (K : Type u) [Field K], (nilpotentMap K).comp (nilpotentMap K) = 0

def invariant_line : Prop :=
  ∀ (K : Type u) [Field K],
    Specs.D05.M06.Invariant.invariant_value K (K × K) (line K) (nilpotentMap K)

/-- The second coordinate line is an ordinary vector-space complement. -/
def ordinary_complement : Prop :=
  ∀ (K : Type u) [Field K],
    Specs.D05.M06.DirectSum.UniqueDecomposition
      (fun b : Bool => if b then transverseLine K else line K)

/-- No complement of the first coordinate line is preserved by `N`. -/
def no_invariant_complement : Prop :=
  ∀ (K : Type u) [Field K],
    ¬ ∃ W : Submodule K (K × K),
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then W else line K) ∧
      Specs.D05.M06.Invariant.invariant_value K (K × K) W (nilpotentMap K)

end Specs.D05.M06.NoninvariantComplement
