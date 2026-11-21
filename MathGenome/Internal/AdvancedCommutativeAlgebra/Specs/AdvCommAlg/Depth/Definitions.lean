import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions
import Mathlib.Data.ENat.Lattice

/-! Independent specifications for the definitions in paper.tex, DP-01.
The same formulas make sense for arbitrary commutative rings and modules;
in particular they apply to the source's Noetherian rings and finite modules.
`I • ⊤ = ⊤` expresses `IM = M`. Regularity is proper regularity, including
nonvanishing of the terminal quotient, as in RK-01. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.Depth.Specs

def gradeType := ∀ {R : Type u} [CommRing R], Ideal R →
  (M : Type v) → [AddCommGroup M] → [Module R M] → ℕ∞

noncomputable def gradeValue : gradeType.{u, v} := by
  classical
  exact fun {R} _ I M _ _ =>
    if I • (⊤ : Submodule R M) = ⊤ then ⊤ else
      sSup {(x.length : ℕ∞) | (x : List R)
        (_ : RingTheory.Sequence.IsRegular M x) (_ : ∀ a ∈ x, a ∈ I)}

def depthType := ∀ (R : Type u) [CommRing R] [IsLocalRing R],
  (M : Type v) → [AddCommGroup M] → [Module R M] → ℕ∞

noncomputable def depthValue : depthType.{u, v} :=
  fun R _ _ M _ _ => gradeValue (IsLocalRing.maximalIdeal R) M

def grade_of_smul_eq_topType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M],
    I • (⊤ : Submodule R M) = ⊤ → gradeValue I M = ⊤

def grade_of_smul_ne_topType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M],
    I • (⊤ : Submodule R M) ≠ ⊤ → gradeValue I M =
      sSup {(x.length : ℕ∞) | (x : List R)
        (_ : RingTheory.Sequence.IsRegular M x) (_ : ∀ a ∈ x, a ∈ I)}

def depth_eq_gradeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (M : Type v)
    [AddCommGroup M] [Module R M],
    depthValue R M = gradeValue (IsLocalRing.maximalIdeal R) M

def grade_eq_top_of_subsingletonType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Subsingleton M], gradeValue I M = ⊤

def depth_eq_top_of_subsingletonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (M : Type v)
    [AddCommGroup M] [Module R M] [Subsingleton M], depthValue R M = ⊤

end AdvCommAlg.Depth.Specs
