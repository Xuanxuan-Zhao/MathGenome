import MathGenome.Internal.Specs.D07.Ch18.NilpotenceCriteria
import MathGenome.Internal.D07.Ch18.CentralSeries
import MathGenome.Internal.D07.Ch18.MixedCommutators
import Lean.Elab.Tactic.Omega

/-!
Nilpotence criteria and finite central-chain comparison, paper.tex:4997–5029.
The finite comparisons are proved with bounded induction, so the unspecified
tail of a finite chain is never used. The lower series keeps γ₁ = G throughout.
-/

namespace D07.Ch18.NilpotenceCriteria

open Specs.D07.Ch18.CentralSeries
open Specs.D07.Ch18.NilpotenceCriteria
open scoped commutatorElement

universe u

abbrev ClassAtMost (G : Type u) [Group G] (c : ℕ) : Prop := classAtMostValue G c

abbrev HasClass (G : Type u) [Group G] (c : ℕ) : Prop := hasClassValue G c

abbrev CentralChain (G : Type u) [Group G] (c : ℕ) (C : ℕ → Subgroup G) : Prop :=
  centralChainValue G c C

theorem classAtMost_iff_upper (G : Type u) [Group G] (c : ℕ) :
    ClassAtMost G c ↔ upperValue G c = ⊤ := Iff.rfl

theorem classAtMost_iff_lower (G : Type u) [Group G] (c : ℕ) :
    ClassAtMost G c ↔ lowerValue G (c + 1) = ⊥ := by
  change Subgroup.upperCentralSeries G c = ⊤ ↔ _
  change _ ↔ CentralSeries.lowerSeries G (c + 1) = ⊥
  rw [CentralSeries.lower_indexing]
  exact Subgroup.lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top.symm

theorem chain_monotone (G : Type u) [Group G] (c : ℕ) (C : ℕ → Subgroup G)
    (hC : CentralChain G c C) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ c) : C i ≤ C j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hC.2.2.2.1 j (by omega))

theorem chain_le_upper (G : Type u) [Group G] (c : ℕ) (C : ℕ → Subgroup G)
    (hC : CentralChain G c C) (i : ℕ) (hi : i ≤ c) : C i ≤ upperValue G i := by
  induction i with
  | zero => rw [hC.1]; exact bot_le
  | succ i ih =>
    intro x hx
    apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
    intro g
    apply ih (by omega)
    apply hC.2.2.2.2 i (by omega)
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)

theorem lower_le_chain (G : Type u) [Group G] (c : ℕ) (C : ℕ → Subgroup G)
    (hC : CentralChain G c C) (j : ℕ) (hj : 1 ≤ j) (hjc : j ≤ c + 1) :
    lowerValue G j ≤ C (c + 1 - j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  induction n with
  | zero => simpa only [Nat.add_sub_cancel_right, lowerValue] using hC.2.1.ge
  | succ n ih =>
    change ⁅lowerValue G (n + 1), (⊤ : Subgroup G)⁆ ≤ C (c + 1 - (n + 2))
    have hn : n + 1 ≤ c + 1 := by omega
    have hbound := ih (by omega) hn
    have heq : c + 1 - (n + 1) = (c + 1 - (n + 2)) + 1 := by omega
    calc
      ⁅lowerValue G (n + 1), (⊤ : Subgroup G)⁆
          ≤ ⁅C (c + 1 - (n + 1)), (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mono hbound le_rfl
      _ = ⁅(⊤ : Subgroup G), C ((c + 1 - (n + 2)) + 1)⁆ := by
        rw [heq, Subgroup.commutator_comm]
      _ ≤ C (c + 1 - (n + 2)) := hC.2.2.2.2 _ (by omega)

theorem upper_is_centralChain (G : Type u) [Group G] (c : ℕ)
    (hc : ClassAtMost G c) : CentralChain G c (upperValue G) := by
  refine ⟨rfl, hc, ?_, ?_, ?_⟩
  · intro i _; exact CentralSeries.upper_normal G i
  · intro i _; exact CentralSeries.upper_monotone G (by omega)
  · intro i _; exact CentralSeries.upper_commutator G i

theorem reversed_lower_is_centralChain (G : Type u) [Group G] (c : ℕ)
    (hc : lowerValue G (c + 1) = ⊥) :
    CentralChain G c (fun i => lowerValue G (c + 1 - i)) := by
  refine ⟨by simpa using hc, ?_, ?_, ?_, ?_⟩
  · simp only [show c + 1 - c = 1 by omega, lowerValue]
  · intro i hi
    dsimp only
    have heq : c + 1 - i = (c - i) + 1 := by omega
    rw [heq]
    exact CentralSeries.lower_normal G (c - i)
  · intro i hi
    dsimp only
    have heq₁ : c + 1 - i = (c - i) + 1 := by omega
    have heq₂ : c + 1 - (i + 1) = (c - (i + 1)) + 1 := by omega
    rw [heq₁, heq₂]
    exact CentralSeries.lower_antitone G (by omega)
  · intro i hi
    dsimp only
    have heq₁ : c + 1 - i = (c - (i + 1)) + 2 := by omega
    have heq₂ : c + 1 - (i + 1) = (c - (i + 1)) + 1 := by omega
    rw [heq₁, heq₂]
    change ⁅(⊤ : Subgroup G), CentralSeries.lowerSeries G ((c - (i + 1)) + 1)⁆ ≤
      CentralSeries.lowerSeries G ((c - (i + 1)) + 2)
    rw [CentralSeries.lower_successor, Subgroup.commutator_comm]

theorem classAtMost_iff_centralChain (G : Type u) [Group G] (c : ℕ) :
    ClassAtMost G c ↔ ∃ C : ℕ → Subgroup G, CentralChain G c C := by
  constructor
  · intro hc; exact ⟨upperValue G, upper_is_centralChain G c hc⟩
  · rintro ⟨C, hC⟩
    exact top_le_iff.mp (hC.2.1 ▸ chain_le_upper G c C hC c le_rfl)

theorem lower_le_upper (G : Type u) [Group G] (c : ℕ) (hc : ClassAtMost G c)
    (i : ℕ) (hi : i ≤ c) : lowerValue G (c + 1 - i) ≤ upperValue G i := by
  have h := lower_le_chain G c (upperValue G) (upper_is_centralChain G c hc)
    (c + 1 - i) (by omega) (by omega)
  simpa only [show c + 1 - (c + 1 - i) = i by omega] using h

theorem nilpotent_iff_exists_bound (G : Type u) [Group G] :
    Group.IsNilpotent G ↔ ∃ c : ℕ, ClassAtMost G c :=
  ⟨fun h => h.nilpotent, fun h => ⟨h⟩⟩

theorem hasClass_exists_iff_nilpotent (G : Type u) [Group G] :
    (∃ c : ℕ, HasClass G c) ↔ Group.IsNilpotent G := by
  classical
  constructor
  · rintro ⟨c, hc, _⟩; exact (nilpotent_iff_exists_bound G).mpr ⟨c, hc⟩
  · intro hG
    have h := (nilpotent_iff_exists_bound G).mp hG
    exact ⟨Nat.find h, Nat.find_spec h, fun _ hd => Nat.find_le hd⟩

theorem hasClass_unique (G : Type u) [Group G] (c d : ℕ)
    (hc : HasClass G c) (hd : HasClass G d) : c = d :=
  le_antisymm (hc.2 d hd.1) (hd.2 c hc.1)

theorem hasClass_iff_libraryClass (G : Type u) [Group G] (c : ℕ) :
    HasClass G c ↔ Group.IsNilpotent G ∧ Group.nilpotencyClass G = c := by
  constructor
  · intro hc
    have hG := (nilpotent_iff_exists_bound G).mpr ⟨c, hc.1⟩
    let := hG
    refine ⟨hG, le_antisymm ?_ ?_⟩
    · exact Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp hc.1
    · exact hc.2 _ (Subgroup.upperCentralSeries_nilpotencyClass (G := G))
  · rintro ⟨hG, hc⟩
    let := hG
    constructor
    · exact hc ▸ Subgroup.upperCentralSeries_nilpotencyClass (G := G)
    · intro d hd
      rw [← hc]
      exact Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp hd

theorem hasClass_iff_least_lower_length (G : Type u) [Group G] (c : ℕ) :
    HasClass G c ↔
      lowerValue G (c + 1) = ⊥ ∧ ∀ d : ℕ, lowerValue G (d + 1) = ⊥ → c ≤ d := by
  simp only [HasClass, hasClassValue, ← classAtMost_iff_lower G]

theorem least_termination_lengths_agree (G : Type u) [Group G] (c d : ℕ)
    (hc : HasClass G c)
    (hd : lowerValue G (d + 1) = ⊥ ∧
      ∀ e : ℕ, lowerValue G (e + 1) = ⊥ → d ≤ e) : c = d :=
  hasClass_unique G c d hc ((hasClass_iff_least_lower_length G d).mpr hd)

theorem class_zero_iff_subsingleton (G : Type u) [Group G] :
    HasClass G 0 ↔ Subsingleton G := by
  constructor
  · intro hc
    have : Group.IsNilpotent G := (hasClass_iff_libraryClass G 0).mp hc |>.1
    exact Group.nilpotencyClass_zero_iff_subsingleton.mp
      ((hasClass_iff_libraryClass G 0).mp hc).2
  · intro hG
    let := hG
    exact (hasClass_iff_libraryClass G 0).mpr
      ⟨inferInstance, Group.nilpotencyClass_zero_iff_subsingleton.mpr hG⟩

theorem class_one_iff_nontrivial_abelian (G : Type u) [Group G] :
    HasClass G 1 ↔ Nontrivial G ∧ ∀ x y : G, x * y = y * x := by
  constructor
  · intro hc
    have hcomm : IsMulCommutative G := Subgroup.upperCentralSeries_one_eq_top_iff.mp hc.1
    constructor
    · by_contra hnt
      have hs : Subsingleton G := not_nontrivial_iff_subsingleton.mp hnt
      have hzero := (class_zero_iff_subsingleton G).mpr hs
      have := hasClass_unique G 1 0 hc hzero
      omega
    · exact hcomm.is_comm.comm
  · rintro ⟨hnt, hcomm⟩
    let := hnt
    have hc : ClassAtMost G 1 := Subgroup.upperCentralSeries_one_eq_top_iff.mpr
      ⟨⟨hcomm⟩⟩
    refine ⟨hc, fun d hd => ?_⟩
    by_contra hle
    have hd0 : d = 0 := by omega
    have hzero : HasClass G 0 := ⟨hd0 ▸ hd, fun _ _ => Nat.zero_le _⟩
    have : Subsingleton G := (class_zero_iff_subsingleton G).mp hzero
    exact not_nontrivial G hnt

end D07.Ch18.NilpotenceCriteria
