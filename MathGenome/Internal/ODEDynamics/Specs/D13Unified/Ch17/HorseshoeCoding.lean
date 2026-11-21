import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.CantorGeometry

/-! Independent specification of the two-sided series coding in
`paper.tex`, Theorem `d13:17:affine-horseshoe`.
The past starts at symbol -1, while the future starts at symbol 0.
Only the local affine strip formula is used; no extension over the gap
and no maximal-full-orbit classification is assumed here. -/
namespace Specs.D13Unified.Ch17.HorseshoeCoding
open Set
open Specs.D13Unified.Ch17.ShiftSpaces
noncomputable section
open scoped Classical

def future (s : TwoSided) : OneSided := fun j => s (j : ℤ)
def past (s : TwoSided) : OneSided := fun j => s (-((j : ℤ) + 1))

/-- The pair of series in the paper, reusing the canonical one-sided coding. -/
def coding (r : ℝ) (s : TwoSided) : ℝ × ℝ :=
  (CantorGeometry.coding r (future s), CantorGeometry.coding r (past s))

/-- These are exactly V₀ and V₁, including all boundary points. -/
def verticalStrip (r : ℝ) (a : Binary) : Set (ℝ × ℝ) :=
  if a = 0 then Icc 0 r ×ˢ Icc 0 1 else Icc (1-r) 1 ×ˢ Icc 0 1

/-- The affine formula on the branch with symbol a. -/
def affineBranch (r : ℝ) (a : Binary) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 - (1-r) * (a.val : ℝ)) / r, r * p.2 + (1-r) * (a.val : ℝ))

/-- The actual local map has just the union of the two vertical strips as
its domain. No values in the middle gap are supplied. -/
def stripMap (r : ℝ) (p : ↥(verticalStrip r 0 ∪ verticalStrip r 1)) : ℝ × ℝ :=
  if p.val ∈ verticalStrip r 0 then affineBranch r 0 p.val else affineBranch r 1 p.val

def stripMapType := (r : ℝ) → ↥(verticalStrip r 0 ∪ verticalStrip r 1) → ℝ × ℝ

def futureType := TwoSided → OneSided
def pastType := TwoSided → OneSided
def codingType := ℝ → TwoSided → ℝ × ℝ
def verticalStripType := ℝ → Binary → Set (ℝ × ℝ)
def affineBranchType := ℝ → Binary → (ℝ × ℝ) → ℝ × ℝ

/-- Explicit bridge to the printed future and past sums (j in the past is
reindexed as j+1, so its exponent is j). -/
def coding_seriesStatement : Prop :=
  ∀ r s, coding r s =
    ((1-r) * ∑' j : ℕ, ((s (j : ℤ)).val : ℝ) * r^j,
     (1-r) * ∑' j : ℕ, ((s (-((j : ℤ)+1))).val : ℝ) * r^j)

def series_summableStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ s : TwoSided,
    Summable (fun j : ℕ => ((s (j : ℤ)).val : ℝ) * r^j) ∧
    Summable (fun j : ℕ => ((s (-((j : ℤ)+1))).val : ℝ) * r^j)

def coding_homeomorphStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 →
    ∃ h : TwoSided ≃ₜ (CantorGeometry.cantorSet r × CantorGeometry.cantorSet r),
      ∀ s, ((h s).1.val, (h s).2.val) = coding r s

def coding_mem_stripStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ s : TwoSided,
    coding r s ∈ verticalStrip r (s 0)

def affine_intertwiningStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ s : TwoSided,
    affineBranch r (s 0) (coding r s) = coding r (shift s)

def stripMap_branchStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ a : Binary, ∀ p : ℝ × ℝ,
    ∀ hp : p ∈ verticalStrip r a,
    ∀ hd : p ∈ verticalStrip r 0 ∪ verticalStrip r 1,
      stripMap r ⟨p, hd⟩ = affineBranch r a p

/-- The unconditional intertwining equation for the local strip map. The
existential proof term records that every coded point belongs to its domain. -/
def coding_strip_mapStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ s : TwoSided,
    ∃ hp : coding r s ∈ verticalStrip r 0 ∪ verticalStrip r 1,
      stripMap r ⟨coding r s, hp⟩ = coding r (shift s)

/-- This version applies to any map with the prescribed local strip values;
its values elsewhere play no role. It states the full symbolic conjugacy
using the same homeomorphism onto C_r × C_r. -/
def strip_conjugacyStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ H : (ℝ × ℝ) → ℝ × ℝ,
    (∀ a p, p ∈ verticalStrip r a → H p = affineBranch r a p) →
    ∃ h : TwoSided ≃ₜ (CantorGeometry.cantorSet r × CantorGeometry.cantorSet r),
      (∀ s, ((h s).1.val, (h s).2.val) = coding r s) ∧
      ∀ s, H ((h s).1.val, (h s).2.val) =
        ((h (shift s)).1.val, (h (shift s)).2.val)

end
end Specs.D13Unified.Ch17.HorseshoeCoding
