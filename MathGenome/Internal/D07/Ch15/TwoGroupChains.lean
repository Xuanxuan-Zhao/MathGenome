import MathGenome.Internal.Specs.D07.Ch15.TwoGroupChains
import Mathlib.GroupTheory.Sylow

/-!
The subgroup-relative 2-group chain lemma (paper.tex:4505–4513).

The prime-power subgroup extension theorem in Mathlib supplies an
increasing chain of all orders 2^0, ..., 2^a which contains the given H.
Its proof uses the normalizer quotient and Cauchy's theorem, just as the
source's argument. We retain the suffix starting at H. Cardinality
2^a forces its last subgroup to be G; consecutive cardinalities and
Lagrange's relative-index formula give index exactly two.
-/

namespace D07.Ch15.TwoGroupChains

universe u

theorem two_group_chains (G : Type u) [Group G] [Finite G]
    (hG : ∃ a : ℕ, Nat.card G = 2 ^ a) (H : Subgroup G) :
    ∃ (s : ℕ) (C : Fin (s + 1) → Subgroup G),
      C 0 = H ∧ C (Fin.last s) = ⊤ ∧ StrictMono C ∧
        ∀ i : Fin s, (C i.castSucc).relIndex (C i.succ) = 2 := by
  classical
  obtain ⟨a, ha⟩ := hG
  obtain ⟨f, hfH, hfcard⟩ := Sylow.exists_orderEmbedding_of_isChain
    (G := G) (p := 2) (n := a) Nat.prime_two (ha ▸ dvd_refl _)
    (s := {H}) (IsChain.singleton) (by
      intro K hK
      have hKH : K = H := Set.mem_singleton_iff.mp hK
      rw [hKH, ← ha]
      exact Subgroup.card_subgroup_dvd_card H)
  obtain ⟨m, hm⟩ := hfH (Set.mem_singleton H)
  let s := a - m.val
  let C : Fin (s + 1) → Subgroup G := fun i =>
    f ⟨m.val + i.val, by dsimp [s] at *; omega⟩
  have hCcard (i : Fin (s + 1)) : Nat.card (C i) = 2 ^ (m.val + i.val) :=
    hfcard _
  have hCmono : StrictMono C := by
    intro i j hij
    apply f.strictMono
    change m.val + i.val < m.val + j.val
    exact Nat.add_lt_add_left hij m.val
  refine ⟨s, C, ?_, ?_, hCmono, ?_⟩
  · change f ⟨m.val + 0, _⟩ = H
    simpa only [Nat.add_zero] using hm
  · apply Subgroup.eq_top_of_card_eq
    rw [hCcard, ha]
    congr 1
    dsimp [s]
    have := m.isLt
    omega
  · intro i
    have hmul := (C i.castSucc).relIndex_mul_card (C i.succ)
    rw [inf_eq_left.mpr (hCmono.monotone (Fin.castSucc_le_succ i)),
      hCcard, hCcard] at hmul
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ (m.val + i.val) by positivity)
    calc
      (C i.castSucc).relIndex (C i.succ) * 2 ^ (m.val + i.val) =
          2 ^ (m.val + (i.val + 1)) := hmul
      _ = 2 * 2 ^ (m.val + i.val) := by rw [← Nat.add_assoc, pow_succ']

end D07.Ch15.TwoGroupChains
