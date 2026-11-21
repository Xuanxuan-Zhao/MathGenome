import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.SummationTree
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.Operations
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.GammaProducts

noncomputable section
namespace NumAnalysis206.Rounding
namespace AddTree

/-- The recursive quantities are exactly the sums over the ordered leaves. -/
theorem exact_quantities {α : Type} (t : AddTree α) (value : α → ℝ) :
    t.exactSum value = (t.leaves.map value).sum ∧
    t.mass value = (t.leaves.map (fun a => |value a|)).sum := by
  induction t with
  | empty => simp [exactSum, mass, leaves]
  | leaf a => simp [exactSum, mass, leaves]
  | branch l r hl hr =>
      simp [exactSum, mass, leaves, List.map_append, List.sum_append, hl.1, hl.2, hr.1, hr.2]

theorem mass_nonneg {α : Type} (t : AddTree α) (value : α → ℝ) :
    0 ≤ t.mass value := by
  induction t with
  | empty => exact le_rfl
  | leaf a => exact abs_nonneg _
  | branch l r hl hr => exact add_nonneg hl hr

theorem abs_exactSum_le {α : Type} (t : AddTree α) (value : α → ℝ) :
    |t.exactSum value| ≤ t.mass value := by
  induction t with
  | empty => simp [exactSum, mass]
  | leaf a => exact le_rfl
  | branch l r hl hr => exact (abs_add_le _ _).trans (add_le_add hl hr)

theorem allLeaves_of_forall {α : Type} (p : α → Prop) (h : ∀ a, p a) (t : AddTree α) :
    t.AllLeaves p := by
  induction t with
  | empty => trivial
  | leaf a => exact h a
  | branch l r hl hr => exact ⟨hl, hr⟩

theorem allLeaves_mono {α : Type} {p q : α → Prop}
    (h : ∀ a, p a → q a) (t : AddTree α) : t.AllLeaves p → t.AllLeaves q := by
  induction t with
  | empty => exact fun _ => trivial
  | leaf a => exact h a
  | branch l r hl hr => exact fun hp => ⟨hl hp.1, hr hp.2⟩

end AddTree

/-- One additional relative perturbation consumes one unit of path budget. -/
theorem gamma_step {n : ℕ} {u : ℝ} (hu : BudgetDomain (n + 1) u) :
    (1 + u) * gamma n u + u ≤ gamma (n + 1) u := by
  have hn := budgetDomain_mono (Nat.le_succ n) hu
  have h0 : 0 < 1 - (n : ℝ) * u := by linarith [hn.2.2]
  have h1 : 0 < 1 - ((n : ℝ) + 1) * u := by exact_mod_cast (sub_pos.mpr hu.2.2)
  have heq : (1 + u) * gamma n u + u = ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    apply (eq_div_iff (ne_of_gt h0)).2
    unfold gamma
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ (ne_of_gt h0)]
    ring
  rw [heq]
  unfold gamma
  push_cast
  apply (div_le_div_iff₀ h0 h1).2
  have hu0 := hu.1
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg u]

private theorem perturbation_error {z s δ u g w : ℝ}
    (_hu : 0 ≤ u) (hg : 0 ≤ g) (hw : 0 ≤ w)
    (hd : |δ| ≤ u) (he : |z - s| ≤ g * w) (hs : |s| ≤ w) :
    |z * (1 + δ) - s| ≤ ((1 + u) * g + u) * w := by
  have hf : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hd 1
  calc
    |z * (1 + δ) - s| = |(z - s) * (1 + δ) + s * δ| := by congr 1; ring
    _ ≤ |(z - s) * (1 + δ)| + |s * δ| := abs_add_le _ _
    _ = |z - s| * |1 + δ| + |s| * |δ| := by rw [abs_mul, abs_mul]
    _ ≤ (g * w) * (1 + u) + w * u := by
      exact add_le_add
        (mul_le_mul he hf (abs_nonneg _) (mul_nonneg hg hw))
        (mul_le_mul hs hd (abs_nonneg _) hw)
    _ = ((1 + u) * g + u) * w := by ring

/-- General induction allowing an initial independent leaf-rounding budget. -/
theorem tree_error_with_leaf_budget {α : Type} (round : ℝ → ℝ) (u : ℝ)
    (D : Set ℝ) (value stored : α → ℝ) (b : ℕ)
    (hmodel : RelativeModel round u D) (t : AddTree α)
    (hu : BudgetDomain (t.depth + b) u)
    (hsafe : t.Safe round D stored)
    (hleaf : t.AllLeaves (fun a => |stored a - value a| ≤ gamma b u * |value a|)) :
    |t.eval round stored - t.exactSum value| ≤ gamma (t.depth + b) u * t.mass value := by
  induction t with
  | empty => simp [AddTree.eval, AddTree.exactSum, AddTree.mass]
  | leaf a => simpa [AddTree.eval, AddTree.exactSum, AddTree.depth, AddTree.mass, AddTree.AllLeaves] using hleaf
  | branch l r hl hr =>
    let m := max l.depth r.depth + b
    have hm : BudgetDomain (m + 1) u := by
      simpa [m, AddTree.depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu
    have hmb := budgetDomain_mono (Nat.le_succ m) hm
    have hld : l.depth + b ≤ m := Nat.add_le_add_right (Nat.le_max_left _ _) b
    have hrd : r.depth + b ≤ m := Nat.add_le_add_right (Nat.le_max_right _ _) b
    have el := hl (budgetDomain_mono hld hmb) hsafe.1 hleaf.1
    have er := hr (budgetDomain_mono hrd hmb) hsafe.2.1 hleaf.2
    have el' : |l.eval round stored - l.exactSum value| ≤ gamma m u * l.mass value :=
      el.trans (mul_le_mul_of_nonneg_right (gamma_mono hld hmb) (l.mass_nonneg value))
    have er' : |r.eval round stored - r.exactSum value| ≤ gamma m u * r.mass value :=
      er.trans (mul_le_mul_of_nonneg_right (gamma_mono hrd hmb) (r.mass_nonneg value))
    have he : |(l.eval round stored + r.eval round stored) -
        (l.exactSum value + r.exactSum value)| ≤ gamma m u * (l.mass value + r.mass value) := by
      calc
        _ = |(l.eval round stored - l.exactSum value) +
              (r.eval round stored - r.exactSum value)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ gamma m u * l.mass value + gamma m u * r.mass value := add_le_add el' er'
        _ = _ := by ring
    obtain ⟨δ, hδ, hδu⟩ := relativeModel_error round u D hmodel _ hsafe.2.2
    have hs : |l.exactSum value + r.exactSum value| ≤ l.mass value + r.mass value :=
      (abs_add_le _ _).trans (add_le_add (l.abs_exactSum_le value) (r.abs_exactSum_le value))
    have hw : 0 ≤ l.mass value + r.mass value := add_nonneg (l.mass_nonneg value) (r.mass_nonneg value)
    have hp := perturbation_error hm.1 (gamma_nonneg hmb) hw hδu he hs
    change |round _ - _| ≤ _
    rw [hδ]
    apply hp.trans
    have := mul_le_mul_of_nonneg_right (gamma_step hm) hw
    simpa [m, AddTree.mass, AddTree.depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

namespace AddTree

theorem sum_error (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (t : AddTree ℝ) (d : ℕ) (hmodel : RelativeModel round u D)
    (hu : BudgetDomain d u) (hd : t.depth ≤ d) (hsafe : t.Safe round D id) :
    |t.eval round id - t.exactSum id| ≤ gamma d u * t.mass id := by
  have hl : t.AllLeaves (fun a => |id a - id a| ≤ gamma 0 u * |id a|) :=
    allLeaves_of_forall _ (by intro a; simp [gamma]) t
  have h := tree_error_with_leaf_budget round u D id id 0 hmodel t
    (by simpa using budgetDomain_mono hd hu) hsafe hl
  simp only [Nat.add_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (gamma_mono hd hu) (t.mass_nonneg id))

theorem product_error (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (t : AddTree (ℝ × ℝ)) (d : ℕ) (hmodel : RelativeModel round u D)
    (hu : BudgetDomain (d + 1) u) (hd : t.depth ≤ d)
    (hp : t.AllLeaves (fun a => a.1 * a.2 ∈ D))
    (hsafe : t.Safe round D (fun a => round (a.1 * a.2))) :
    |t.eval round (fun a => round (a.1 * a.2)) - t.exactSum (fun a => a.1 * a.2)| ≤
      gamma (d + 1) u * t.mass (fun a => a.1 * a.2) := by
  have hb := budgetDomain_mono (show 1 ≤ d + 1 by omega) hu
  have hug : u ≤ gamma 1 u := by
    have := gamma_step (n := 0) (by simpa using hb)
    simpa [gamma] using this
  have hl : t.AllLeaves (fun a => |round (a.1 * a.2) - a.1 * a.2| ≤
      gamma 1 u * |a.1 * a.2|) := by
    apply allLeaves_mono (p := fun a : ℝ × ℝ => a.1 * a.2 ∈ D) ?_ t hp
    intro a ha
    obtain ⟨δ, hδ, hdδ⟩ := relativeModel_error round u D hmodel _ ha
    rw [hδ]
    calc
      |a.1 * a.2 * (1 + δ) - a.1 * a.2| = |δ| * |a.1 * a.2| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ u * |a.1 * a.2| := mul_le_mul_of_nonneg_right hdδ (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hug (abs_nonneg _)
  have hd' := Nat.add_le_add_right hd 1
  have h := tree_error_with_leaf_budget round u D (fun a : ℝ × ℝ => a.1 * a.2)
    (fun a => round (a.1 * a.2)) 1 hmodel t (budgetDomain_mono hd' hu) hsafe hl
  exact h.trans (mul_le_mul_of_nonneg_right (gamma_mono hd' hu) (t.mass_nonneg _))

/-- Splitting the ordered list into floor/ceiling halves constructs a balanced
binary tree at every admissible height. No zero-padding leaves are introduced. -/
theorem exists_balanced_of_length_le_pow {α : Type} (d : ℕ) (xs : List α)
    (hpos : 0 < xs.length) (hsize : xs.length ≤ 2 ^ d) :
    ∃ t : AddTree α, t.leaves = xs ∧ t.Balanced ∧ t.depth ≤ d := by
  induction d generalizing xs with
  | zero =>
    have hlen : xs.length = 1 := by simp only [pow_zero] at hsize; omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨.leaf x, rfl, trivial, Nat.zero_le _⟩
  | succ d ih =>
    by_cases hsingle : xs.length = 1
    · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hsingle
      exact ⟨.leaf x, rfl, trivial, Nat.zero_le _⟩
    let k := xs.length / 2
    have hk : k ≤ xs.length := Nat.div_le_self _ _
    have hleft : (xs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
    have hright : (xs.drop k).length = xs.length - k := List.length_drop
    have hsz : xs.length ≤ 2 ^ d * 2 := by simpa [pow_succ] using hsize
    have hlpos : 0 < (xs.take k).length := by rw [hleft]; dsimp [k]; omega
    have hrpos : 0 < (xs.drop k).length := by rw [hright]; dsimp [k]; omega
    have hls : (xs.take k).length ≤ 2 ^ d := by rw [hleft]; dsimp [k]; omega
    have hrs : (xs.drop k).length ≤ 2 ^ d := by rw [hright]; dsimp [k]; omega
    obtain ⟨l, hl, hbl, hdl⟩ := ih (xs.take k) hlpos hls
    obtain ⟨r, hr, hbr, hdr⟩ := ih (xs.drop k) hrpos hrs
    refine ⟨.branch l r, ?_, ?_, ?_⟩
    · simp [leaves, hl, hr]
    · refine ⟨hbl, hbr, ?_, ?_⟩
      · rw [hl, hr, hleft, hright]; dsimp [k]; omega
      · rw [hl, hr, hleft, hright]; dsimp [k]; omega
    · change max l.depth r.depth + 1 ≤ d + 1
      exact Nat.add_le_add_right (max_le hdl hdr) 1

/-- `Nat.clog` is the least integer d with n ≤ 2^d, hence ceiling log₂ n. -/
theorem exists_balanced {α : Type} (xs : List α) (hpos : 0 < xs.length) :
    ∃ t : AddTree α, t.leaves = xs ∧ t.Balanced ∧ t.depth ≤ Nat.clog 2 xs.length :=
  exists_balanced_of_length_le_pow _ xs hpos (Nat.le_pow_clog (by decide) _)

theorem balanced_existence (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∃ t : AddTree ℝ, t.leaves = List.ofFn x ∧ t.Balanced ∧
      t.depth ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ := by
  obtain ⟨t, ht, hb, hd⟩ := exists_balanced (List.ofFn x) (by simp only [List.length_ofFn]; omega)
  refine ⟨t, ht, hb, ?_⟩
  change t.depth ≤ ⌈Real.logb ((2 : ℕ) : ℝ) (n : ℝ)⌉₊
  rw [Real.natCeil_logb_natCast]
  simpa only [List.length_ofFn] using hd

theorem empty_sum (round : ℝ → ℝ) :
    (AddTree.empty : AddTree ℝ).eval round id = 0 ∧
    (AddTree.empty : AddTree (ℝ × ℝ)).eval round (fun a => round (a.1 * a.2)) = 0 :=
  ⟨rfl, rfl⟩

theorem leaf_copy (round : ℝ → ℝ) (x : ℝ) :
    (AddTree.leaf x).eval round id = x ∧ (AddTree.leaf x).depth = 0 := ⟨rfl, rfl⟩

end AddTree
end NumAnalysis206.Rounding
