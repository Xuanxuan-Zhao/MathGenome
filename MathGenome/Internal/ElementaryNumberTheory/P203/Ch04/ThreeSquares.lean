import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.ThreeSquares
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.ThreeSquaresReduction
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.ThreeSquaresAuxiliaryPrime
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.ThreeSquaresLattice
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.ThreeSquaresRecognition

namespace P203.Ch04
open P203Specs.Ch04

/-- Assemble the auxiliary prime, the particular lattice, and the recognition
of its remaining norm as two integer squares. -/
theorem squarefree_threeSquares (n : ℕ) (hsf : Squarefree n)
    (hn : 1 < n) (hf : ¬Forbidden n) : ThreeSquares n := by
  have hres : ThreeSquaresResidue n := (squarefreeResidues n hsf).mp hf
  obtain ⟨k, m, ell, q, a, u, v, h⟩ :=
    threeSquaresAuxiliaryPrime n hsf hn hres
  let b : ℕ := 2 ^ ell * q
  have hb : 0 < b := Nat.mul_pos (by positivity) h.prime.pos
  have hc : b.Coprime n := by
    have hcZ : Int.gcd (b : ℤ) (n : ℤ) = 1 := by
      simpa [b] using h.coprime
    simpa only [Int.gcd_natCast_natCast] using hcZ
  have hu : (b : ℤ) ∣ u ^ 2 + n := by
    have hd : (b : ℤ) ∣ (4 : ℤ) ^ ell * q := by
      dsimp only [b]
      push_cast
      exact mul_dvd_mul_right (pow_dvd_pow_of_dvd (by norm_num : (2 : ℤ) ∣ 4) ell) _
    convert dvd_neg.mpr (hd.trans h.root_u.dvd) using 1; ring
  have hv : (n : ℤ) ∣ (b : ℤ) * v ^ 2 + 1 := by
    convert dvd_neg.mpr h.root_v.dvd using 1; simp [b]
  have hell : ell = 0 ∨ ell = 1 := by
    rw [h.ell_eq]
    split <;> simp
  have hqodd : Odd q := Nat.odd_iff.mpr (by have := h.mod_four; omega)
  have hlocal : ∀ p : ℕ, p.Prime → Odd p → p ∣ n →
      IsSquare (-(b : ℤ) : ZMod p) ∧ (-(b : ℤ) : ZMod p) ≠ 0 := by
    intro p hp hpodd hpn
    have hp2 : p ≠ 2 := by
      rintro rfl
      have := Nat.odd_iff.mp hpodd
      omega
    have hpm : p ∣ m := by
      rw [h.decomposition] at hpn
      apply (hp.dvd_mul.mp hpn).resolve_left
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow hd))
    obtain ⟨hnot, x, hx⟩ := h.local_squares p hp hp2 hpm
    have hnot' : ¬(p : ℤ) ∣ -(b : ℤ) := by simpa [b] using hnot
    refine ⟨⟨(x : ZMod p), ?_⟩, ?_⟩
    · have hx' : x ^ 2 ≡ -(b : ℤ) [ZMOD (p : ℤ)] := by simpa [b] using hx
      have hz := (ZMod.intCast_eq_intCast_iff (x ^ 2) (-(b : ℤ)) p).mpr hx'
      simpa [pow_two] using hz.symm
    · intro hz
      apply hnot'
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by
        simpa only [Int.cast_neg] using hz)
  obtain ⟨r, s, t, hout⟩ := threeSquares_lattice n b u v (by omega) hb hc.symm hu hv
  obtain ⟨_, _, _, _, _, _, _, _, heq, hS, hSn, hrel⟩ := hout
  obtain ⟨y, z, hyz⟩ := threeSquaresRecognition n ell q hn hsf hell h.prime hqodd h.gt
    hc hlocal (latticeX n b u v r s t) (latticeW b u r s) s
    (latticeS n b u r s) hS hSn heq hrel
  exact ⟨latticeX n b u v r s t, y, z, by rw [← heq, hyz]; ring⟩

/-- Legendre's complete three-square criterion, including all square factors. -/
theorem threeSquares_iff : ThreeSquaresTheorem := by
  intro n hn
  constructor
  · intro hs hf
    exact forbiddenObstruction n hf hs
  · intro hf
    obtain ⟨d, n₀, _, hn₀, hsf, _, hforbid, hscale⟩ := squarefreeReduction n hn
    apply hscale
    by_cases hone : n₀ = 1
    · rw [hone]
      exact threeSquaresOne
    · exact squarefree_threeSquares n₀ hsf (by omega) (fun h => hf (hforbid.mpr h))

theorem threeSquares_zero : ThreeSquaresAtZero := threeSquaresZero

end P203.Ch04
