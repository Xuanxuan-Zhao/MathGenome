import MathGenome.Internal.Specs.D07.Ch18.CentralSeries
import Mathlib.Order.OrderIsoNat

/-!
Upper and lower central series, `K07.18.central_series`.
The upper series is constructed in Mathlib with characteristicity in the
recursion, before any quotient by a term is used. The lower sequence here
has the paper's indexing, and its bridge is proved by induction.
-/

namespace D07.Ch18.CentralSeries

open Specs.D07.Ch18.CentralSeries

universe u

abbrev upperSeries (G : Type u) [Group G] : ℕ → Subgroup G := upperValue G

def lowerSeries (G : Type u) [Group G] : ℕ → Subgroup G := lowerValue G

theorem upper_zero (G : Type u) [Group G] : upperSeries G 0 = ⊥ := rfl

theorem lower_one (G : Type u) [Group G] : lowerSeries G 1 = ⊤ := rfl

theorem lower_successor (G : Type u) [Group G] (n : ℕ) :
    lowerSeries G (n + 2) = ⁅lowerSeries G (n + 1), (⊤ : Subgroup G)⁆ := rfl

theorem lower_indexing (G : Type u) [Group G] (n : ℕ) :
    lowerSeries G (n + 1) = (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show n.succ + 1 = n + 2 from rfl,
      lower_successor, Subgroup.lowerCentralSeries_succ, ih]

theorem upper_characteristic (G : Type u) [Group G] (n : ℕ) :
    (upperSeries G n).Characteristic := by
  change (Subgroup.upperCentralSeries G n).Characteristic
  infer_instance

theorem lower_characteristic (G : Type u) [Group G] (n : ℕ) :
    (lowerSeries G (n + 1)).Characteristic := by
  rw [lower_indexing]
  infer_instance

theorem upper_normal (G : Type u) [Group G] (n : ℕ) :
    (upperSeries G n).Normal := by
  let := upper_characteristic G n
  infer_instance

theorem lower_normal (G : Type u) [Group G] (n : ℕ) :
    (lowerSeries G (n + 1)).Normal := by
  let := lower_characteristic G n
  infer_instance

theorem upper_successor (G : Type u) [Group G] (n : ℕ) :
    upperSeries G (n + 1) =
      (Subgroup.center (G ⧸ upperSeries G n)).comap (QuotientGroup.mk' (upperSeries G n)) :=
  Subgroup.upperCentralSeriesStep_eq_comap_center (Subgroup.upperCentralSeries G n)

theorem upper_quotient_center (G : Type u) [Group G] (n : ℕ) :
    (upperSeries G (n + 1)).map (QuotientGroup.mk' (upperSeries G n)) =
      Subgroup.center (G ⧸ upperSeries G n) := by
  rw [upper_successor]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _ ) _

theorem upper_monotone (G : Type u) [Group G] : Monotone (upperSeries G) :=
  Subgroup.upperCentralSeries_mono G

theorem lower_antitone (G : Type u) [Group G] :
    Antitone (fun n => lowerSeries G (n + 1)) := by
  simpa only [lower_indexing] using (⊤ : Subgroup G).lowerCentralSeries_antitone

theorem upper_commutator (G : Type u) [Group G] (n : ℕ) :
    ⁅(⊤ : Subgroup G), upperSeries G (n + 1)⁆ ≤ upperSeries G n := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_upperCentralSeries_top_le G n

theorem upper_equality_iff_trivial_center (G : Type u) [Group G] (n : ℕ) :
    upperSeries G n = upperSeries G (n + 1) ↔
      Subgroup.center (G ⧸ upperSeries G n) = ⊥ := by
  rw [eq_comm, upper_successor]
  simpa only [QuotientGroup.ker_mk', upperSeries] using
    (Subgroup.comap_eq_ker_of_surjective
      (f := QuotientGroup.mk' (upperSeries G n)) (QuotientGroup.mk'_surjective _))

theorem upper_stabilizes_of_equality (G : Type u) [Group G] (n : ℕ)
    (h : upperSeries G n = upperSeries G (n + 1))
    (m : ℕ) (hm : n ≤ m) : upperSeries G m = upperSeries G n :=
  (Subgroup.upperCentralSeries.eq_ge_of_eq_succ hm h).symm

theorem lower_stabilizes_of_equality (G : Type u) [Group G] (n : ℕ)
    (h : lowerSeries G (n + 1) = lowerSeries G (n + 2))
    (m : ℕ) (hm : n ≤ m) : lowerSeries G (m + 1) = lowerSeries G (n + 1) := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [show m.succ + 1 = m + 2 from rfl,
      lower_successor, ih, ← lower_successor, ← h]

theorem finite_upper_stabilizes (G : Type u) [Group G] [Finite G] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → upperSeries G m = upperSeries G n := by
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition
    (⟨upperSeries G, upper_monotone G⟩ : ℕ →o Subgroup G)
  exact ⟨n, fun m hm => (hn m hm).symm⟩

theorem finite_lower_stabilizes (G : Type u) [Group G] [Finite G] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → lowerSeries G (m + 1) = lowerSeries G (n + 1) := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (lower_antitone G)
  exact ⟨n, fun m hm => (hn m hm).symm⟩

end D07.Ch18.CentralSeries
