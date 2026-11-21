import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftSpaces
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Tuple.Basic

/-! Canonical separated Cantor set and its finite cylinder geometry, from
paper.tex, `d13:17:affine-horseshoe` and `d13:18:cantor-dimension`.
The coding domain has the already fixed native binary product topology.
All statements retain precisely the range `0 < r < 1/2`, including level zero.
-/
namespace Specs.D13Unified.Ch17.CantorGeometry
open Set
open Specs.D13Unified.Ch17.ShiftSpaces
noncomputable section

def coding (r : ℝ) (s : OneSided) : ℝ :=
  (1 - r) * ∑' j : ℕ, ((s j).val : ℝ) * r ^ j

def cantorSet (r : ℝ) : Set ℝ := Set.range (coding r)

def branch (r : ℝ) (a : Binary) (x : ℝ) : ℝ :=
  r * x + (1 - r) * (a.val : ℝ)

/-- Composition in the order `b_(w 0) ∘ ... ∘ b_(w (n-1))`. -/
def wordMap (r : ℝ) : {n : ℕ} → (Fin n → Binary) → ℝ → ℝ
  | 0, _, x => x
  | _n + 1, w, x => branch r (w 0) (wordMap r (Fin.tail w) x)

def levelInterval (r : ℝ) {n : ℕ} (w : Fin n → Binary) : Set ℝ :=
  Icc (wordMap r w 0) (wordMap r w 1)

/-- The family of all level-n intervals, without duplicate intervals. -/
def levelIntervals (r : ℝ) (n : ℕ) : Finset (Set ℝ) :=
  Finset.univ.image (fun w : Fin n → Binary => levelInterval r w)

def codingType := ℝ → OneSided → ℝ
def cantorSetType := ℝ → Set ℝ
def branchType := ℝ → Binary → ℝ → ℝ
def wordMapType := ℝ → {n : ℕ} → (Fin n → Binary) → ℝ → ℝ
def levelIntervalType := ℝ → {n : ℕ} → (Fin n → Binary) → Set ℝ
def levelIntervalsType := ℝ → ℕ → Finset (Set ℝ)

def series_summableStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ s : OneSided,
    Summable (fun j : ℕ => ((s j).val : ℝ) * r ^ j)
/-- Uniform convergence of the unscaled digit series (the scalar factor is fixed). -/
def series_uniformStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 →
    TendstoUniformly (fun n (s : OneSided) => ∑ j ∈ Finset.range n, ((s j).val : ℝ) * r^j)
      (fun s => ∑' j : ℕ, ((s j).val : ℝ) * r^j) Filter.atTop
def coding_continuousStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → Continuous (coding r)
def coding_injectiveStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → Function.Injective (coding r)
def cantor_subset_unitStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → cantorSet r ⊆ Icc 0 1
def cantor_compactStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → IsCompact (cantorSet r)
def coding_homeomorphStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∃ h : OneSided ≃ₜ cantorSet r,
    ∀ s, (h s).val = coding r s

def branch_zeroStatement : Prop := ∀ r x : ℝ, branch r 0 x = r * x
def branch_oneStatement : Prop := ∀ r x : ℝ, branch r 1 x = r * x + 1 - r

def wordMap_affineStatement : Prop :=
  ∀ r : ℝ, ∀ n : ℕ, ∀ w : Fin n → Binary, ∀ x : ℝ,
    wordMap r w x = wordMap r w 0 + r^n * x

def levelInterval_imageStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ, ∀ w : Fin n → Binary,
    levelInterval r w = wordMap r w '' Icc 0 1

def levelInterval_lengthStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ, ∀ w : Fin n → Binary,
    wordMap r w 1 - wordMap r w 0 = r^n

def level_coverStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ,
    cantorSet r ⊆ ⋃ w : Fin n → Binary, levelInterval r w

/-- The geometric cylinders agree exactly with symbolic prefix cylinders. -/
def coding_mem_level_iffStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ, ∀ w : Fin n → Binary,
    ∀ s : OneSided, coding r s ∈ levelInterval r w ↔ ∀ i : Fin n, s i = w i

def level_gapStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ, 1 ≤ n →
    ∀ u v : Fin n → Binary, u ≠ v →
      ∀ x ∈ levelInterval r u, ∀ y ∈ levelInterval r v,
        (1 - 2*r) * r^(n-1) ≤ |x-y|

def level_disjointStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ,
    Pairwise (fun u v : Fin n → Binary => Disjoint (levelInterval r u) (levelInterval r v))

def level_cardStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ, (levelIntervals r n).card = 2^n

end
end Specs.D13Unified.Ch17.CantorGeometry
