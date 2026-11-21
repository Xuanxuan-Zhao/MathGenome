import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.DenseProperCyclicSubgroup
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.ProfiniteIntegers.IntegerDensity
import Mathlib.Algebra.Order.Group.Unbundled.Int

noncomputable section
universe u v
namespace AdvancedFieldTheory
namespace ProfiniteIntegers

private def twoPower (s : ℕ) : ℕ+ := ⟨2 ^ s, pow_pos (by decide) s⟩

/-- Compactness assembles compatible residues which vanish at every power of
2 but equal 1 modulo 3. Each finite requirement is supplied by CRT. -/
private theorem exists_noninteger_residue : ∃ a : Zhat, a ∉ Set.range ι := by
  let C (s : ℕ) : Set Zhat := {a | π (twoPower s) a = 0 ∧ π 3 a = 1}
  have hclosed (s : ℕ) : IsClosed (C s) :=
    (isClosed_eq (continuous_π _) continuous_const).inter
      (isClosed_eq (continuous_π _) continuous_const)
  have hnonempty (s : ℕ) : (C s).Nonempty := by
    let z := Nat.chineseRemainder ((by decide : Nat.Coprime 2 3).pow_left s) 0 1
    refine ⟨ι (z : ℕ), ?_, ?_⟩
    · change (((z : ℕ) : ℤ) : ZMod (2 ^ s)) = 0
      simpa only [Int.cast_natCast, Nat.cast_zero] using
        (ZMod.natCast_eq_natCast_iff (z : ℕ) 0 (2 ^ s)).mpr z.property.1
    · change (((z : ℕ) : ℤ) : ZMod 3) = 1
      simpa only [Int.cast_natCast, Nat.cast_one] using
        (ZMod.natCast_eq_natCast_iff (z : ℕ) 1 3).mpr z.property.2
  have hmono {s t : ℕ} (hst : s ≤ t) : C t ⊆ C s := by
    intro a ha
    refine ⟨?_, ha.2⟩
    have h := coordinate_compatibility a (twoPower s) (twoPower t)
      (pow_dvd_pow 2 hst)
    change reduce (twoPower s) (twoPower t) _ (π (twoPower t) a) =
      π (twoPower s) a at h
    rw [ha.1, map_zero] at h
    exact h.symm
  have hd : Directed (· ⊇ ·) C :=
    fun s t => ⟨max s t, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hd hnonempty (fun s => (hclosed s).isCompact) hclosed
  refine ⟨a, ?_⟩
  rintro ⟨z, rfl⟩
  have hz (s : ℕ) : ((2 ^ s : ℕ) : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z (2 ^ s)).mp (Set.mem_iInter.mp ha s).1
  have hz0 : z = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hz z.natAbs)
    simpa using (Nat.lt_two_pow_self (n := z.natAbs))
  have h3 := (Set.mem_iInter.mp ha 0).2
  change (z : ZMod 3) = 1 at h3
  rw [hz0, Int.cast_zero] at h3
  exact zero_ne_one h3

/-- The canonical integer subgroup of the profinite integers is proper. -/
theorem integer_image_proper :
    Specs.AdvancedFieldTheory.DenseProperCyclicSubgroup.IntegerImageProper := by
  change Set.range ι ⊂ (Set.univ : Set Zhat)
  obtain ⟨a, ha⟩ := exists_noninteger_residue
  exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, by
    intro h
    apply ha
    rw [h]
    trivial⟩

end ProfiniteIntegers

/-- Dense, proper, and with fixed field exactly the base finite field. -/
theorem frobenius_dense_proper_fixedField :
    Specs.AdvancedFieldTheory.DenseProperCyclicSubgroup.FrobeniusDenseProperFixedField.{u, v} := by
  intro k Ω _ _ _ _ _
  refine ⟨frobenius_cyclic_dense k Ω, ?_, frobenius_cyclic_fixedField k Ω⟩
  obtain ⟨coords, hc, e, he, hu⟩ := AbsoluteGalois.absoluteGaloisGroup k Ω
  intro htop
  change Subgroup.zpowers (globalFrobenius k Ω) = ⊤ at htop
  have hsurj : Function.Surjective ProfiniteIntegers.ι := by
    intro a
    have hmem : e.symm (Multiplicative.ofAdd a) ∈
        Subgroup.zpowers (globalFrobenius k Ω) := by rw [htop]; trivial
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨z, ?_⟩
    have h := congrArg e hz
    rw [frobenius_zpow_residues k Ω e he.2, e.apply_symm_apply] at h
    exact congrArg Multiplicative.toAdd h
  have hp := ProfiniteIntegers.integer_image_proper
  exact hp.ne (Set.range_eq_univ.mpr hsurj)

end AdvancedFieldTheory
