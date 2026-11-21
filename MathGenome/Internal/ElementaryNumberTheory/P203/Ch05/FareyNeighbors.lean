import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.FareyNeighbors
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.FareyMediants
import Mathlib.Data.Finset.Max

namespace P203.Ch05
open P203Specs.Ch05

/-- A determinant-one predecessor with the largest allowed denominator in
its residue class. This also covers the right endpoint 1/1. -/
lemma bounded_predecessor (N c d : ℤ) (hd : 0 < d) (hc : 0 < c)
    (hcd : c ≤ d) (hdN : d ≤ N) (hg : Int.gcd c d = 1) :
    ∃ a b : ℤ, (a,b) ∈ P203Specs.Ch05.farey N ∧
      b*c-a*d = 1 ∧ N < b+d := by
  let u := Int.gcdA c d
  let v := Int.gcdB c d
  have hbez : c*u+d*v = 1 := by
    have h := Int.gcd_eq_gcd_ab c d
    rw [hg] at h
    simpa [u, v] using h.symm
  let k := (N-u) / d
  let b := u+k*d
  let a := -v+k*c
  have hmod : N = b + (N-u)%d := by
    have h := Int.emod_add_mul_ediv (N-u) d
    dsimp [b, k]
    nlinarith [h]
  have hr0 := Int.emod_nonneg (N-u) (ne_of_gt hd)
  have hrd := Int.emod_lt_of_pos (N-u) hd
  have hb : 0 < b := by omega
  have hbN : b ≤ N := by omega
  have hsum : N < b+d := by omega
  have hdet : b*c-a*d = 1 := by dsimp [a, b]; nlinarith [hbez]
  have ha : 0 ≤ a := by
    by_contra h
    have : a ≤ -1 := by omega
    nlinarith [mul_pos hb hc]
  have hab : a ≤ b := by
    have : b*c ≤ b*d := mul_le_mul_of_nonneg_left hcd hb.le
    nlinarith
  have hred : Reduced (a,b) := by
    refine ⟨hb, ?_⟩
    have hdiv : (Int.gcd a b : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub
        (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) c)
        (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) d)
    exact Nat.dvd_one.mp (by exact_mod_cast hdiv)
  refine ⟨a, b, ?_, hdet, hsum⟩
  apply (fareyMembership N _).mpr
  refine ⟨hred, ?_, ?_, hbN⟩
  · exact div_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb.le)
  · have hb' : (0 : ℚ) < b := by exact_mod_cast hb
    change (a : ℚ) / b ≤ 1
    rw [div_le_one hb']
    exact_mod_cast hab

/-- Coordinate bounds of a Farey member. -/
lemma farey_coordinates {N : ℤ} {x : Fraction}
    (hx : x ∈ P203Specs.Ch05.farey N) :
    0 ≤ x.1 ∧ x.1 ≤ x.2 ∧ 0 < x.2 ∧ x.2 ≤ N ∧ Int.gcd x.1 x.2 = 1 := by
  have h := Finset.mem_filter.mp hx
  have hp := Finset.mem_product.mp h.1
  have ha := Finset.mem_Icc.mp hp.1
  have hb := Finset.mem_Icc.mp hp.2
  exact ⟨ha.1, h.2.1, by omega, hb.2, h.2.2⟩

theorem neighborProperties : NeighborProperties := by
  intro N hN x y hxy
  obtain ⟨hx, hy, hlt, hgap⟩ := hxy
  have hxc := farey_coordinates hx
  have hyc := farey_coordinates hy
  have hcross := (fraction_lt_iff hxc.2.2.1 hyc.2.2.1).mp hlt
  have hc : 0 < y.1 := by
    have : 0 ≤ x.1*y.2 := mul_nonneg hxc.1 hyc.2.2.1.le
    have : 0 < y.1*x.2 := lt_of_le_of_lt this hcross
    by_contra h
    have hy0 : y.1 ≤ 0 := by omega
    have := mul_nonpos_of_nonpos_of_nonneg hy0 hxc.2.2.1.le
    omega
  obtain ⟨a, b, hab, hdet, hsum⟩ := bounded_predecessor N y.1 y.2
    hyc.2.2.1 hc hyc.2.1 hyc.2.2.2.1 hyc.2.2.2.2
  have habc := farey_coordinates hab
  have hpred : fractionValue (a,b) < fractionValue y := by
    rw [fraction_lt_iff habc.2.2.1 hyc.2.2.1]
    nlinarith
  have heq : fractionValue x = fractionValue (a,b) := by
    apply le_antisymm
    · by_contra h
      have hax : fractionValue (a,b) < fractionValue x := lt_of_not_ge h
      have hbound := (interiorDenominator a b y.1 y.2 x.1 x.2
        habc.2.2.1 hyc.2.2.1 hxc.2.2.1 hdet hax hlt).1
      omega
    · by_contra h
      exact hgap (a,b) hab ⟨lt_of_not_ge h, hpred⟩
  have hxred := ((fareyMembership N x).mp hx).1
  have hared := ((fareyMembership N (a,b)).mp hab).1
  have hxeq := reducedInjectivity x (a,b) hxred hared heq
  subst x
  exact ⟨hdet, hsum⟩

theorem fareyInitial : FareyInitial := by
  apply Finset.ext
  rintro ⟨a,b⟩
  constructor
  · intro h
    have hc := farey_coordinates h
    have hb : b = 1 := by dsimp at hc; omega
    have ha : a = 0 ∨ a = 1 := by dsimp at hc; omega
    rcases ha with rfl | rfl <;> simp [hb]
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h <;> cases h
    · exact (fareyEndpoints 1 (by omega)).1
    · exact (fareyEndpoints 1 (by omega)).2

theorem neighborUniqueMinimum : NeighborUniqueMinimum := by
  intro N hN x y hxy z
  have hx := ((fareyMembership N x).mp hxy.1).1
  have hy := ((fareyMembership N y).mp hxy.2.1).1
  have hdet := (neighborProperties N hN x y hxy).1
  have hred := mediantReduced x.1 x.2 y.1 y.2 hx.1 hy.1 hdet
  have hint := mediantInterior x.1 x.2 y.1 y.2 hx.1 hy.1 hdet
  constructor
  · intro hz
    have hbound := interiorDenominator x.1 x.2 y.1 y.2 z.1 z.2
      hx.1 hy.1 hz.1.1 hdet hz.2.1 hz.2.2.1
    have hden : z.2 = x.2+y.2 :=
      le_antisymm (hz.2.2.2 _ hred hint.1 hint.2) hbound.1
    exact Prod.ext (hbound.2.mp hden).1 hden
  · rintro rfl
    refine ⟨hred, hint.1, hint.2, ?_⟩
    intro w hw hwl hwr
    exact (interiorDenominator x.1 x.2 y.1 y.2 w.1 w.2
      hx.1 hy.1 hw.1 hdet hwl hwr).1

theorem intervalInsertion : IntervalInsertion := by
  intro N hN x y hxy z
  have hxm := (fareyMembership N x).mp hxy.1
  have hym := (fareyMembership N y).mp hxy.2.1
  have hprops := neighborProperties N hN x y hxy
  constructor
  · rintro ⟨hz, hzl, hzr⟩
    have hzm := (fareyMembership (N+1) z).mp hz
    have hbound := interiorDenominator x.1 x.2 y.1 y.2 z.1 z.2
      hxm.1.1 hym.1.1 hzm.1.1 hprops.1 hzl hzr
    have hsum : x.2+y.2 = N+1 := by omega
    have hden : z.2 = x.2+y.2 := by omega
    have hnum := (hbound.2.mp hden).1
    exact ⟨hsum, Prod.ext hnum hden⟩
  · rintro ⟨hsum, rfl⟩
    have hint := mediantInterior x.1 x.2 y.1 y.2 hxm.1.1 hym.1.1 hprops.1
    refine ⟨(fareyMembership (N+1) _).mpr ?_, hint⟩
    exact ⟨mediantReduced x.1 x.2 y.1 y.2 hxm.1.1 hym.1.1 hprops.1,
      le_trans hxm.2.1 hint.1.le, le_trans hint.2.le hym.2.2.1, hsum.le⟩

/-- Farey sets increase with the order. -/
lemma farey_mono {N M : ℤ} (hNM : N ≤ M) {z : Fraction}
    (hz : z ∈ P203Specs.Ch05.farey N) : z ∈ P203Specs.Ch05.farey M := by
  obtain ⟨hred, hlo, hhi, hden⟩ := (fareyMembership N z).mp hz
  exact (fareyMembership M z).mpr ⟨hred, hlo, hhi, le_trans hden hNM⟩

/-- Every new member lies strictly inside a neighboring interval of the old
finite set. Both endpoints are old, so there are no boundary exceptions. -/
lemma new_member_interval {N : ℤ} (hN : 1 ≤ N) {z : Fraction}
    (hz : z ∈ P203Specs.Ch05.farey (N+1)) (hnew : z ∉ P203Specs.Ch05.farey N) :
    ∃ x y : Fraction, P203Specs.Ch05.orderedNeighbors N x y ∧
      fractionValue x < fractionValue z ∧ fractionValue z < fractionValue y := by
  have hzm := (fareyMembership (N+1) z).mp hz
  have hends := fareyEndpoints N hN
  have hz0 : (0 : ℚ) < fractionValue z := by
    have hne : fractionValue z ≠ fractionValue (0,1) := by
      intro heq
      have he := reducedInjectivity z (0,1) hzm.1
        ((fareyMembership N _).mp hends.1).1 heq
      exact hnew (he ▸ hends.1)
    have hne' : fractionValue z ≠ (0 : ℚ) := by simpa [fractionValue] using hne
    exact lt_of_le_of_ne hzm.2.1 hne'.symm
  have hz1 : fractionValue z < (1 : ℚ) := by
    have hne : fractionValue z ≠ fractionValue (1,1) := by
      intro heq
      have he := reducedInjectivity z (1,1) hzm.1
        ((fareyMembership N _).mp hends.2).1 heq
      exact hnew (he ▸ hends.2)
    have hne' : fractionValue z ≠ (1 : ℚ) := by simpa [fractionValue] using hne
    exact lt_of_le_of_ne hzm.2.2.1 hne'
  let left := (P203Specs.Ch05.farey N).filter (fun w => fractionValue w < fractionValue z)
  let right := (P203Specs.Ch05.farey N).filter (fun w => fractionValue z < fractionValue w)
  have hlne : left.Nonempty := by
    refine ⟨(0,1), Finset.mem_filter.mpr ⟨hends.1, ?_⟩⟩
    simpa [fractionValue] using hz0
  have hrne : right.Nonempty := by
    refine ⟨(1,1), Finset.mem_filter.mpr ⟨hends.2, ?_⟩⟩
    simpa [fractionValue] using hz1
  obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image left fractionValue hlne
  obtain ⟨y, hy, hymin⟩ := Finset.exists_min_image right fractionValue hrne
  obtain ⟨hxmem, hxlt⟩ := Finset.mem_filter.mp hx
  obtain ⟨hymem, hylt⟩ := Finset.mem_filter.mp hy
  refine ⟨x, y, ⟨hxmem, hymem, lt_trans hxlt hylt, ?_⟩, hxlt, hylt⟩
  intro w hw hwint
  rcases lt_trichotomy (fractionValue w) (fractionValue z) with hwz | hwz | hwz
  · have := hxmax w (Finset.mem_filter.mpr ⟨hw, hwz⟩)
    exact (not_lt_of_ge this) hwint.1
  · have he := reducedInjectivity z w hzm.1 ((fareyMembership N w).mp hw).1 hwz.symm
    exact hnew (he ▸ hw)
  · have := hymin w (Finset.mem_filter.mpr ⟨hw, hwz⟩)
    exact (not_lt_of_ge this) hwint.2

theorem fareyInsertion : FareyInsertion := by
  intro N hN z
  constructor
  · intro hz
    by_cases hold : z ∈ P203Specs.Ch05.farey N
    · exact Or.inl hold
    · obtain ⟨x, y, hxy, hzl, hzr⟩ := new_member_interval hN hz hold
      have hi := (intervalInsertion N hN x y hxy z).mp ⟨hz, hzl, hzr⟩
      exact Or.inr ⟨x, y, hxy, hi⟩
  · rintro (hz | ⟨x, y, hxy, hsum, heq⟩)
    · exact farey_mono (by omega) hz
    · exact ((intervalInsertion N hN x y hxy z).mpr ⟨hsum, heq⟩).1

end P203.Ch05
