import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.LatticeRank
import Mathlib.Order.JordanHolder
import Mathlib.Order.Atoms.Finite
import Lean.Elab.Tactic.Omega

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {L : Type u}

noncomputable def latticeIntervalLength [PartialOrder L] (x y : L) : ℕ :=
  Expected.latticeIntervalLength x y

noncomputable def latticeHeight [PartialOrder L] [OrderBot L] (x : L) : ℕ :=
  Expected.latticeHeight x

section Lattice
variable [Lattice L] [IsUpperModularLattice L]

/-- The meet in the unequal case is the bottom endpoint of the cover. -/
theorem latticeJoinCover {x y : L} (h : x ⋖ y) (b : L) :
    x ⊔ b = y ⊔ b ∨ (x ⊔ b) ⋖ (y ⊔ b) := by
  by_cases he : x ⊔ b = y ⊔ b
  · exact Or.inl he
  right
  have hm : y ⊓ (x ⊔ b) = x := by
    rcases h.eq_or_eq (le_inf h.le le_sup_left) inf_le_left with hm | hm
    · exact hm
    · have hy : y ≤ x ⊔ b := by rw [← hm]; exact inf_le_right
      exact (he (le_antisymm (sup_le_sup_right h.le b)
        (sup_le hy le_sup_right))).elim
  have hc : y ⊓ (x ⊔ b) ⋖ y := by rw [hm]; exact h
  simpa only [← sup_assoc, sup_eq_left.mpr h.le] using hc.sup_of_inf_left

/-- Reverse chains into the dual lattice, which is weakly lower modular.
The general Jordan–Hölder theorem then gives equality of lengths. -/
theorem latticeChainsEqualLength (s t : SaturatedChain L)
    (hh : s.head = t.head) (hl : s.last = t.last) : s.length = t.length := by
  let sd : CompositionSeries Lᵒᵈ := s.reverse.ofLE (fun {_} h => CovBy.toDual h)
  let td : CompositionSeries Lᵒᵈ := t.reverse.ofLE (fun {_} h => CovBy.toDual h)
  have hd := CompositionSeries.jordan_holder sd td
    (by
      change s.reverse.head = t.reverse.head
      simpa only [RelSeries.head_reverse] using hl)
    (by
      change s.reverse.last = t.reverse.last
      simpa only [RelSeries.last_reverse] using hh)
  exact hd.length_eq

theorem latticeIntervalLengthOfChain (s : SaturatedChain L) :
    latticeIntervalLength s.head s.last = s.length := by
  unfold latticeIntervalLength Expected.latticeIntervalLength
  have he : {n | ∃ t : SaturatedChain L,
      t.head = s.head ∧ t.last = s.last ∧ t.length = n} = {s.length} := by
    ext n
    constructor
    · rintro ⟨t, hh, hl, rfl⟩
      exact latticeChainsEqualLength t s hh hl
    · rintro rfl
      exact ⟨s, rfl, rfl, rfl⟩
  rw [he, csSup_singleton]

theorem latticeIntervalLengthSelf (x : L) : latticeIntervalLength x x = 0 :=
  latticeIntervalLengthOfChain (RelSeries.singleton _ x)

end Lattice

/-- Finite intervals admit saturated chains, including the singleton case. -/
theorem latticeChainExists [Lattice L] [Finite L] (x y : L) (h : x ≤ y) :
    ∃ s : SaturatedChain L, s.head = x ∧ s.last = y := by
  obtain ⟨f, hf, n, hn, hs⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le h
  exact ⟨⟨n, (fun i => f i), (fun i => hs i i.isLt)⟩, hf, hn⟩

/-- Maximality by inclusion forces any saturated refinement to have the
same elements. This identifies ordinary maximal chains with the saturated
series used to define interval length. -/
theorem latticeMaximalChainLength [Lattice L] [Finite L] [IsUpperModularLattice L]
    (x y : L) [Fact (x ≤ y)] (s : LTSeries (Set.Icc x y))
    (hmax : IsMaxChain (· ≤ ·) (Set.range s)) :
    s.length = latticeIntervalLength x y := by
  obtain ⟨t, i, hit, _, _⟩ := s.exists_relSeries_covBy
  let tt : LTSeries (Set.Icc x y) := t.ofLE (fun {_} h => h.lt)
  have hchain : IsChain (· ≤ ·) (Set.range t) := by
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _
    exact (le_total j k).imp (fun h => tt.monotone h) (fun h => tt.monotone h)
  have hsub : Set.range s ⊆ Set.range t := by
    rintro _ ⟨j, rfl⟩
    exact ⟨i j, congrFun hit j⟩
  have he := hmax.2 hchain hsub
  have hlen : s.length = t.length := by
    have hc := congrArg Set.ncard he
    have htinj : Function.Injective t := tt.strictMono.injective
    rw [Set.ncard_range_of_injective s.strictMono.injective,
      Set.ncard_range_of_injective htinj] at hc
    simpa only [Nat.card_fin, Nat.add_right_cancel_iff] using hc
  have htbot : t.head = (⊥ : Set.Icc x y) := by
    obtain ⟨j, hj⟩ := he ▸ hmax.bot_mem
    apply le_bot_iff.mp
    exact hj ▸ tt.head_le j
  have httop : t.last = (⊤ : Set.Icc x y) := by
    obtain ⟨j, hj⟩ := he ▸ hmax.top_mem
    apply top_le_iff.mp
    exact hj ▸ tt.monotone (Fin.le_last j)
  let u : SaturatedChain L :=
    { length := t.length
      toFun := fun j => (t j).1
      step := fun j => by
        have hc := t.step j
        refine ⟨hc.lt, ?_⟩
        intro z hz1 hz2
        exact hc.2 (c := ⟨z, (t j.castSucc).2.1.trans hz1.le,
          hz2.le.trans (t j.succ).2.2⟩) hz1 hz2 }
  have hubot : u.head = x := by
    change t.head.val = x
    rw [htbot]
    rfl
  have hutop : u.last = y := by
    change t.last.val = y
    rw [httop]
    rfl
  have hu := latticeIntervalLengthOfChain u
  rw [hubot, hutop] at hu
  exact hlen.trans hu.symm

section Rank
variable [Lattice L] [OrderBot L] [IsUpperModularLattice L]

theorem latticeHeightBot : latticeHeight (⊥ : L) = 0 :=
  latticeIntervalLengthSelf ⊥

variable [Finite L]

theorem latticeChainHeight (s : SaturatedChain L) :
    latticeHeight s.last = latticeHeight s.head + s.length := by
  obtain ⟨t, ht, hl⟩ := latticeChainExists (⊥ : L) s.head bot_le
  have he := latticeIntervalLengthOfChain (t.smash s hl)
  have htlen := latticeIntervalLengthOfChain t
  have he' : latticeIntervalLength ⊥ s.last = t.length + s.length := by
    simpa only [RelSeries.head_smash, RelSeries.last_smash, RelSeries.smash_length, ht] using he
  have htlen' : latticeIntervalLength ⊥ s.head = t.length := by
    simpa only [ht, hl] using htlen
  change latticeIntervalLength ⊥ s.last = latticeIntervalLength ⊥ s.head + s.length
  rw [he', htlen']

theorem latticeIntervalHeight (x y : L) (h : x ≤ y) :
    latticeIntervalLength x y = latticeHeight y - latticeHeight x ∧
    (latticeIntervalLength x y : ℤ) = (latticeHeight y : ℤ) - (latticeHeight x : ℤ) := by
  obtain ⟨s, hs, ht⟩ := latticeChainExists x y h
  have hr := latticeChainHeight s
  have hl := latticeIntervalLengthOfChain s
  rw [hs, ht] at hr hl
  constructor <;> omega

theorem latticeHeightMonotone : Monotone (latticeHeight (L := L)) := by
  intro x y h
  obtain ⟨s, hs, ht⟩ := latticeChainExists x y h
  have hr := latticeChainHeight s
  rw [hs, ht] at hr
  omega

theorem latticeHeightCover {x y : L} (h : x ⋖ y) :
    latticeHeight y = latticeHeight x + 1 := by
  exact latticeChainHeight ((RelSeries.singleton _ x).snoc y h)

theorem latticeHeightStrictMono : StrictMono (latticeHeight (L := L)) := by
  intro x y h
  obtain ⟨z, hz, hzy⟩ := exists_covBy_le_of_lt h
  have h1 := latticeHeightCover hz
  have h2 := latticeHeightMonotone hzy
  omega

/-- Lift a saturated chain by joining with b. Each step contributes at most
one to height, even when the lifted step collapses. -/
theorem latticeJoinChainBound (s : SaturatedChain L) (b : L) :
    latticeHeight (s.last ⊔ b) + latticeHeight s.head ≤
      latticeHeight (s.head ⊔ b) + latticeHeight s.last := by
  induction s using RelSeries.inductionOn' with
  | singleton x => simp
  | snoc s x hx ih =>
    have hr := latticeHeightCover hx
    have hstep : latticeHeight (x ⊔ b) ≤ latticeHeight (s.last ⊔ b) + 1 := by
      rcases latticeJoinCover hx b with he | hc
      · rw [he]
        omega
      · rw [latticeHeightCover hc]
    simpa only [RelSeries.head_snoc, RelSeries.last_snoc] using
      (show latticeHeight (x ⊔ b) + latticeHeight s.head ≤
        latticeHeight (s.head ⊔ b) + latticeHeight x by omega)

theorem latticeHeightSubmodular (x y : L) :
    latticeHeight (x ⊔ y) + latticeHeight (x ⊓ y) ≤
      latticeHeight x + latticeHeight y := by
  obtain ⟨s, hs, ht⟩ := latticeChainExists (x ⊓ y) x inf_le_left
  have h := latticeJoinChainBound s y
  rw [hs, ht] at h
  rw [sup_eq_right.mpr (show x ⊓ y ≤ y from inf_le_right)] at h
  omega

theorem latticeAtomIncrement (x a : L) (ha : IsAtom a) :
    0 ≤ (latticeHeight (x ⊔ a) : ℤ) - (latticeHeight x : ℤ) ∧
    (latticeHeight (x ⊔ a) : ℤ) - (latticeHeight x : ℤ) ≤ 1 := by
  have h := latticeJoinCover ha.bot_covBy x
  simp only [bot_sup_eq, sup_comm a x] at h
  rcases h with he | hc
  · rw [← he]
    simp
  · have hr := latticeHeightCover hc
    omega

end Rank
end FiniteCombinatorics.Matroid
