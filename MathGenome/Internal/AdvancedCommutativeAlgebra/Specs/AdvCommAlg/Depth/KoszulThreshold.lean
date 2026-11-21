import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.SelfDuality

/-! DP-09, paper.tex:2925–2972. Both thresholds use the canonical
Koszul complexes. The homological expression is guarded against an empty
nonvanishing set: in that case its value is infinity, including n = 0.
All modules can be put in a common universe; no nonzero hypothesis is imposed. -/

noncomputable section
open scoped Pointwise
universe u
namespace AdvCommAlg.Depth

namespace Specs


def koszulCohomologyThresholdType := ∀ {R : Type u} [CommRing R]
  (M : Type u) [AddCommGroup M] [Module R M], List R → ℕ∞
def koszulCohomologyThresholdValue {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (a : List R) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : Nontrivial (Koszul.SelfDuality.cohomology M a i)), (i : ℕ∞)

def koszulHomologyThresholdType := ∀ {R : Type u} [CommRing R]
  (M : Type u) [AddCommGroup M] [Module R M], List R → ℕ∞
def koszulHomologyThresholdValue {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (a : List R) : ℕ∞ := by
  classical
  exact if ∃ j : ℕ, Nontrivial (Koszul.homology M a j) then
    (a.length : ℕ∞) - ⨆ (j : ℕ) (_ : Nontrivial (Koszul.homology M a j)), (j : ℕ∞)
  else ⊤

def grade_eq_koszulCohomologyThresholdType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R), Koszul.listIdeal a = I →
      gradeValue I M = koszulCohomologyThresholdValue M a

def koszulThreshold_selfDualityType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (a : List R),
    koszulCohomologyThresholdValue M a = koszulHomologyThresholdValue M a

def grade_eq_koszulHomologyThresholdType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R), Koszul.listIdeal a = I →
      gradeValue I M = koszulHomologyThresholdValue M a

def grade_le_generating_lengthType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R), Koszul.listIdeal a = I →
      I • (⊤ : Submodule R M) ≠ ⊤ → gradeValue I M ≤ a.length

def koszulThreshold_independentType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a b : List R), Koszul.listIdeal a = Koszul.listIdeal b →
      koszulCohomologyThresholdValue M a = koszulCohomologyThresholdValue M b

def koszul_acyclic_of_smul_eq_topType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R), Koszul.listIdeal a • (⊤ : Submodule R M) = ⊤ →
      (∀ q, Subsingleton (Koszul.homology M a q)) ∧
      (∀ q, Subsingleton (Koszul.SelfDuality.cohomology M a q))

/-- Infinite thresholds include IM=M, even if I is proper. -/
def koszulThreshold_of_smul_eq_topType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R), Koszul.listIdeal a • (⊤ : Submodule R M) = ⊤ →
      koszulCohomologyThresholdValue M a = ⊤ ∧ koszulHomologyThresholdValue M a = ⊤

def koszulThreshold_subsingletonType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Subsingleton M] (a : List R),
    koszulCohomologyThresholdValue M a = ⊤ ∧ koszulHomologyThresholdValue M a = ⊤

def koszulThreshold_emptyType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Nontrivial M],
    koszulCohomologyThresholdValue M ([] : List R) = 0 ∧
      koszulHomologyThresholdValue M ([] : List R) = 0

def koszulThreshold_unitIdealType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R), Koszul.listIdeal a = ⊤ →
      koszulCohomologyThresholdValue M a = ⊤ ∧ koszulHomologyThresholdValue M a = ⊤

end Specs
end AdvCommAlg.Depth
