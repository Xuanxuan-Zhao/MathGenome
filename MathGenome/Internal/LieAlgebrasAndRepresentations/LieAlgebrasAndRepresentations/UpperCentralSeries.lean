import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DerivedLowerSeries
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.UpperCentralSeries
import Lean.Elab.Tactic.Omega

/-! The upper central series and its comparison with the lower central series,
for arbitrary fields and Lie algebras. Source: res:A02, lines 205–252. -/

universe u v
namespace LieAlgebrasAndRepresentations

variable (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]

/-- The ascending central series. The successor theorem below identifies this
iterated normalizer construction with the inverse image of the quotient center. -/
def upperCentralSeries (n : ℕ) : LieIdeal k L :=
  (⊥ : LieIdeal k L).ucs n

variable {k L}

theorem upperCentralSeries_zero : upperCentralSeries k L 0 = ⊥ := rfl

/-- Precisely the inverse-image description Zₙ₊₁ = π⁻¹(Z(L/Zₙ)). -/
theorem upperCentralSeries_succ (n : ℕ) (x : L) :
    x ∈ upperCentralSeries k L (n + 1) ↔
      (LieSubmodule.Quotient.mk x : L ⧸ upperCentralSeries k L n) ∈
        LieAlgebra.center k (L ⧸ upperCentralSeries k L n) := by
  change x ∈ ((⊥ : LieIdeal k L).ucs (n + 1)) ↔ _
  rw [LieSubmodule.ucs_succ, LieSubmodule.mem_normalizer]
  change (∀ y : L, ⁅y, x⁆ ∈ upperCentralSeries k L n) ↔
    ∀ y : L ⧸ upperCentralSeries k L n,
      ⁅y, (LieSubmodule.Quotient.mk x : L ⧸ upperCentralSeries k L n)⁆ = 0
  constructor
  · intro h y
    induction y using Quotient.inductionOn' with
    | h y =>
      exact (LieSubmodule.Quotient.mk_eq_zero').mpr (h y)
  · intro h y
    exact (LieSubmodule.Quotient.mk_eq_zero').mp (h (LieSubmodule.Quotient.mk y))

theorem upperCentralSeries_mono : Monotone (upperCentralSeries k L) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [upperCentralSeries, LieSubmodule.ucs_succ] using
    ((⊥ : LieIdeal k L).ucs n).le_normalizer

/-- The equivalence holds with the same c, including c = 0. -/
theorem upperCentralSeries_eq_top_iff (c : ℕ) :
    upperCentralSeries k L c = ⊤ ↔ lowerCentralSeries k L (c + 1) = ⊥ := by
  simp only [upperCentralSeries, lowerCentralSeries, Nat.add_sub_cancel,
    LieSubmodule.ucs_eq_top_iff, le_bot_iff]

theorem upperCentralSeries_reaches_iff :
    (∃ c, upperCentralSeries k L c = ⊤) ↔
      ∃ c, lowerCentralSeries k L (c + 1) = ⊥ :=
  exists_congr fun c => upperCentralSeries_eq_top_iff c

theorem upperCentralSeries_nilpotent_iff :
    (∃ c, upperCentralSeries k L c = ⊤) ↔ LieRing.IsNilpotent L := by
  exact (LieModule.isNilpotent_iff_exists_ucs_eq_top k).symm

/-- Vanishing propagates along the descending lower central series. -/
private theorem lowerCentralSeries_vanishes_after (c n : ℕ)
    (h : lowerCentralSeries k L (c + 1) = ⊥) (hn : c ≤ n) :
    LieModule.lowerCentralSeries k L L n ≤ ⊥ := by
  change LieModule.lowerCentralSeries k L L c = ⊥ at h
  exact (LieModule.antitone_lowerCentralSeries k L L hn).trans (le_of_eq h)

/-- The comparison also holds for r > c, using the accepted convention γ₀ = L. -/
theorem lower_le_upper_of_lower_eq_bot (c r : ℕ)
    (h : lowerCentralSeries k L (c + 1) = ⊥) :
    lowerCentralSeries k L (c + 1 - r) ≤ upperCentralSeries k L r := by
  have hind : (c + 1 - r) - 1 = c - r := by omega
  change LieSubmodule.lcs ((c + 1 - r) - 1) (⊤ : LieIdeal k L) ≤
    (⊥ : LieIdeal k L).ucs r
  rw [hind, ← LieSubmodule.lcs_add_le_iff]
  exact lowerCentralSeries_vanishes_after c (c - r + r) h (by omega)

theorem lower_le_upper_of_upper_eq_top (c r : ℕ)
    (h : upperCentralSeries k L c = ⊤) :
    lowerCentralSeries k L (r + 1) ≤ upperCentralSeries k L (c - r) := by
  change LieSubmodule.lcs r (⊤ : LieIdeal k L) ≤ (⊥ : LieIdeal k L).ucs (c - r)
  rw [← LieSubmodule.lcs_add_le_iff]
  exact lowerCentralSeries_vanishes_after c (r + (c - r))
    ((upperCentralSeries_eq_top_iff c).mp h) (by omega)

end LieAlgebrasAndRepresentations
