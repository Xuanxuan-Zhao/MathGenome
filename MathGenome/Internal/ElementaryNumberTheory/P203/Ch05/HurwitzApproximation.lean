import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.HurwitzApproximation
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.FareyNeighbors
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Finite.Lemmas

namespace P203.Ch05
open P203Specs.Ch05

private lemma ratio_bounds (s : ℚ)
    (h : (s : ℝ)^2 + 1 ≤ Real.sqrt 5 * (s : ℝ)) :
    Real.goldenRatio - 1 < (s : ℝ) ∧ (s : ℝ) < Real.goldenRatio := by
  have hg := Real.goldenRatio_sq
  have hg1 := Real.one_lt_goldenRatio
  have ht : Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
    dsimp [Real.goldenRatio]; ring
  rw [ht] at h
  have hu : (s : ℝ) ≤ Real.goldenRatio := by
    by_contra hn
    have hp : 0 < ((s : ℝ) - Real.goldenRatio) *
        ((s : ℝ) - Real.goldenRatio + 1) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hl : Real.goldenRatio - 1 ≤ (s : ℝ) := by
    by_contra hn
    have hp : 0 < (Real.goldenRatio - (s : ℝ)) *
        (Real.goldenRatio - 1 - (s : ℝ)) := mul_pos (by linarith) (by linarith)
    nlinarith
  refine ⟨lt_of_le_of_ne hl ?_, lt_of_le_of_ne hu ?_⟩
  · simpa only [Int.cast_one] using (Real.goldenRatio_irrational.sub_intCast 1).ne_rat s
  · exact (Real.goldenRatio_irrational.ne_rat s).symm

/-- The gap comparison for any determinant-one pair bracketing the input. -/
private lemma failed_pair_ratio (a b c d : ℤ) (hb : 0 < b) (hd : 0 < d)
    (hdet : b*c-a*d = 1) (x : ℝ)
    (hl : (a : ℝ)/b < x) (hr : x < (c : ℝ)/d)
    (hleft : ¬ |x-(a : ℝ)/b| < 1/(Real.sqrt 5*(b : ℝ)^2))
    (hright : ¬ |x-(c : ℝ)/d| < 1/(Real.sqrt 5*(d : ℝ)^2)) :
    Real.goldenRatio - 1 < (d : ℝ)/(b : ℝ) ∧
      (d : ℝ)/(b : ℝ) < Real.goldenRatio := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hdet' : (b : ℝ)*c-a*d = 1 := by exact_mod_cast hdet
  have hgap : (c : ℝ)/d - (a : ℝ)/b = 1/((b : ℝ)*d) := by
    field_simp
    nlinarith
  have hsum : 1/(Real.sqrt 5*(b : ℝ)^2) +
      1/(Real.sqrt 5*(d : ℝ)^2) ≤ 1/((b : ℝ)*d) := by
    rw [abs_of_pos (sub_pos.mpr hl)] at hleft
    rw [abs_of_neg (sub_neg.mpr hr)] at hright
    linarith [le_of_not_gt hleft, le_of_not_gt hright]
  have hsum' : ((b : ℝ)^2+(d : ℝ)^2)/((b : ℝ)*d) ≤ Real.sqrt 5 := by
    calc
      _ = Real.sqrt 5 * (1/(Real.sqrt 5*(b : ℝ)^2) +
          1/(Real.sqrt 5*(d : ℝ)^2)) * ((b : ℝ)*d) := by
        field_simp; ring
      _ ≤ Real.sqrt 5 * (1/((b : ℝ)*d)) * ((b : ℝ)*d) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum ht.le)
          (mul_pos hb' hd').le
      _ = _ := by field_simp
  have hcross : (b : ℝ)^2+(d : ℝ)^2 ≤ Real.sqrt 5*((b : ℝ)*d) :=
    (div_le_iff₀ (mul_pos hb' hd')).mp hsum'
  have hratio : ((d : ℝ)/(b : ℝ))^2+1 ≤ Real.sqrt 5*((d : ℝ)/(b : ℝ)) := by
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hb')).mpr at hcross
    convert hcross using 1 <;> field_simp; ring
  convert ratio_bounds ((d : ℚ)/(b : ℚ)) (by exact_mod_cast hratio) using 1 <;> push_cast <;> rfl

/-- One of the endpoints and the mediant satisfies Hurwitz's strict bound. -/
private lemma three_candidates (a b c d : ℤ)
    (hab : Reduced (a,b)) (hcd : Reduced (c,d)) (hdet : b*c-a*d = 1)
    (x : ℝ) (hx : Irrational x)
    (hl : (a : ℝ)/b < x) (hr : x < (c : ℝ)/d) :
    ∃ v : Fraction, Reduced v ∧
      (a : ℝ)/b ≤ (v.1 : ℝ)/v.2 ∧ (v.1 : ℝ)/v.2 ≤ (c : ℝ)/d ∧
      |x-(v.1 : ℝ)/v.2| < 1/(Real.sqrt 5*(v.2 : ℝ)^2) := by
  have hb := hab.1
  have hd := hcd.1
  have hm := mediantReduced a b c d hb hd hdet
  have hmi := mediantInterior a b c d hb hd hdet
  dsimp [fractionValue] at hmi
  have hml : (a : ℝ)/b < ((a+c : ℤ) : ℝ)/(b+d : ℤ) := by
    exact_mod_cast hmi.1
  have hmr : ((a+c : ℤ) : ℝ)/(b+d : ℤ) < (c : ℝ)/d := by
    exact_mod_cast hmi.2
  by_cases ha : |x-(a : ℝ)/b| < 1/(Real.sqrt 5*(b : ℝ)^2)
  · exact ⟨(a,b), hab, le_rfl, (lt_trans hl hr).le, ha⟩
  by_cases hc : |x-(c : ℝ)/d| < 1/(Real.sqrt 5*(d : ℝ)^2)
  · exact ⟨(c,d), hcd, (lt_trans hl hr).le, le_rfl, hc⟩
  refine ⟨(a+c,b+d), hm, hml.le, hmr.le, ?_⟩
  by_contra hfail
  have hratio := failed_pair_ratio a b c d hb hd hdet x hl hr ha hc
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hbd' : (0 : ℝ) < (b+d : ℤ) := by exact_mod_cast hm.1
  have hne := hx.ne_rational (a+c) (b+d)
  rcases lt_or_gt_of_ne hne with hxm | hmx
  · have hn := failed_pair_ratio a b (a+c) (b+d) hb hm.1
      (mediantDeterminants a b c d hdet).1 x hl hxm ha hfail
    have heq : ((b+d : ℤ) : ℝ)/(b : ℝ) = 1+(d : ℝ)/(b : ℝ) := by
      push_cast; field_simp
    rw [heq] at hn
    linarith [hratio.1, hn.2]
  · have hn := failed_pair_ratio (a+c) (b+d) c d hm.1 hd
      (mediantDeterminants a b c d hdet).2 x hmx hr hfail hc
    have h1 := (div_lt_iff₀ hb').mp hratio.2
    have h2 := (lt_div_iff₀ hbd').mp hn.1
    have hg := Real.goldenRatio_sq
    have hgb := congrArg (fun z : ℝ => z*(b : ℝ)) hg
    have h3 := mul_lt_mul_of_pos_left h1
      (sub_pos.mpr Real.goldenRatio_lt_two)
    push_cast at h2
    nlinarith

/-- Any irrational in the open unit interval has Farey neighbors on each side. -/
private lemma bracketing_neighbors (N : ℤ) (hN : 1 ≤ N)
    (x : ℝ) (hx : Irrational x) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ u v : Fraction, P203Specs.Ch05.orderedNeighbors N u v ∧
      (fractionValue u : ℝ) < x ∧ x < (fractionValue v : ℝ) := by
  classical
  have hends := fareyEndpoints N hN
  let left := (P203Specs.Ch05.farey N).filter (fun w => (fractionValue w : ℝ) < x)
  let right := (P203Specs.Ch05.farey N).filter (fun w => x < (fractionValue w : ℝ))
  have hlne : left.Nonempty := by
    refine ⟨(0,1), Finset.mem_filter.mpr ⟨hends.1, ?_⟩⟩
    simpa [fractionValue] using hx0
  have hrne : right.Nonempty := by
    refine ⟨(1,1), Finset.mem_filter.mpr ⟨hends.2, ?_⟩⟩
    simpa [fractionValue] using hx1
  obtain ⟨u, hu, humax⟩ := Finset.exists_max_image left fractionValue hlne
  obtain ⟨v, hv, hvmin⟩ := Finset.exists_min_image right fractionValue hrne
  obtain ⟨humem, hult⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvmem, hvlt⟩ := Finset.mem_filter.mp hv
  refine ⟨u, v, ⟨humem, hvmem, ?_, ?_⟩, hult, hvlt⟩
  · exact_mod_cast lt_trans hult hvlt
  · intro w hw hwint
    rcases lt_or_gt_of_ne (hx.ne_rat (fractionValue w)).symm with hwx | hxw
    · have := humax w (Finset.mem_filter.mpr ⟨hw, hwx⟩)
      exact (not_lt_of_ge this) hwint.1
    · have := hvmin w (Finset.mem_filter.mpr ⟨hw, hxw⟩)
      exact (not_lt_of_ge this) hwint.2

/-- The successful candidate at order N has error at most 1/N. -/
private lemma close_success (x : ℝ) (hx : Irrational x) (hx0 : 0 < x) (hx1 : x < 1)
    (N : ℕ) (hN : 0 < N) :
    ∃ v : Fraction, Reduced v ∧
      |x-(v.1 : ℝ)/v.2| < 1/(Real.sqrt 5*(v.2 : ℝ)^2) ∧
      |x-(v.1 : ℝ)/v.2| ≤ 1/(N : ℝ) := by
  obtain ⟨u, v, huv, hul, hvr⟩ := bracketing_neighbors N (by omega) x hx hx0 hx1
  have hu := ((fareyMembership N u).mp huv.1).1
  have hv := ((fareyMembership N v).mp huv.2.1).1
  have hprops := neighborProperties N (by omega) u v huv
  have hul' : (u.1 : ℝ)/u.2 < x := by simpa [fractionValue] using hul
  have hvr' : x < (v.1 : ℝ)/v.2 := by simpa [fractionValue] using hvr
  obtain ⟨w, hwred, hwl, hwr, hwgood⟩ := three_candidates u.1 u.2 v.1 v.2 hu hv hprops.1
    x hx hul' hvr'
  refine ⟨w, hwred, hwgood, ?_⟩
  have hb : (0 : ℝ) < u.2 := by exact_mod_cast hu.1
  have hd : (0 : ℝ) < v.2 := by exact_mod_cast hv.1
  have hdet : (u.2 : ℝ)*v.1-u.1*v.2 = 1 := by exact_mod_cast hprops.1
  have hgap : (v.1 : ℝ)/v.2 - (u.1 : ℝ)/u.2 = 1/((u.2 : ℝ)*v.2) := by
    field_simp; nlinarith
  have hu0 : 0 < u.2 := hu.1
  have hv0 : 0 < v.2 := hv.1
  have hprod : (N : ℤ) ≤ u.2*v.2 := by
    have hp := mul_nonneg (show 0 ≤ u.2-1 by omega) (show 0 ≤ v.2-1 by omega)
    nlinarith [hprops.2]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod' : (N : ℝ) ≤ (u.2 : ℝ)*v.2 := by exact_mod_cast hprod
  calc
    _ ≤ 1/((u.2 : ℝ)*v.2) := by
      apply abs_le.mpr
      constructor <;> linarith
    _ ≤ _ := one_div_le_one_div_of_le hN' hprod'

/-- Infinitude follows from the arbitrarily small errors, not merely from
having a successful candidate at every order. -/
private theorem unit_hurwitz (x : ℝ) (hx : Irrational x) (hx0 : 0 < x) (hx1 : x < 1) :
    {v : Fraction | Reduced v ∧
      |x-(v.1 : ℝ)/v.2| < 1/(Real.sqrt 5*(v.2 : ℝ)^2)}.Infinite := by
  classical
  let S := {v : Fraction | Reduced v ∧
      |x-(v.1 : ℝ)/v.2| < 1/(Real.sqrt 5*(v.2 : ℝ)^2)}
  refine Or.resolve_left (Set.finite_or_infinite S) fun hfin => ?_
  obtain ⟨w, hwred, hwgood, _⟩ := close_success x hx hx0 hx1 1 (by omega)
  obtain ⟨v, hv, hvmin⟩ := Set.exists_min_image S
    (fun v => |x-(v.1 : ℝ)/v.2|) hfin ⟨w, hwred, hwgood⟩
  have hdist : 0 < |x-(v.1 : ℝ)/v.2| :=
    abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rational v.1 v.2))
  obtain ⟨N, hN⟩ := exists_nat_gt (1/|x-(v.1 : ℝ)/v.2|)
  have hN' : (0 : ℝ) < N := lt_trans (one_div_pos.mpr hdist) hN
  obtain ⟨z, hzred, hzgood, hzclose⟩ := close_success x hx hx0 hx1 N (by exact_mod_cast hN')
  have hzmin := hvmin z ⟨hzred, hzgood⟩
  have hsmall : 1/(N : ℝ) < |x-(v.1 : ℝ)/v.2| := (one_div_lt hN' hdist).mpr hN
  linarith

/-- Hurwitz approximation for every irrational real, using the integer
translation of its fractional part; this preserves the denominator, gcd,
approximation error, and distinctness of the reduced fractions. -/
theorem hurwitzApproximation : P203Specs.Ch05.HurwitzApproximation := by
  intro x hx
  let k : ℤ := ⌊x⌋
  have hxi : Irrational (x-(k : ℝ)) := hx.sub_intCast k
  have hx0 : 0 < x-(k : ℝ) := by
    exact Int.fract_pos.mpr (hx.ne_int k)
  have hx1 : x-(k : ℝ) < 1 := Int.fract_lt_one x
  have hi := unit_hurwitz (x-(k : ℝ)) hxi hx0 hx1
  let f : Fraction → Fraction := fun v => (v.1+k*v.2,v.2)
  have hinj : Function.Injective f := by
    intro u v he
    have hden := congrArg Prod.snd he
    have hnum := congrArg Prod.fst he
    dsimp [f] at hden hnum
    exact Prod.ext (by rw [hden] at hnum; omega) hden
  apply (hi.image hinj.injOn).mono
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨hvred, hvgood⟩ := hv
  refine ⟨⟨hvred.1, ?_⟩, ?_⟩
  · simpa only [f, Int.gcd_add_mul_right_left] using hvred.2
  · have hd : (0 : ℝ) < v.2 := by exact_mod_cast hvred.1
    have he : x-((v.1+k*v.2 : ℤ) : ℝ)/(v.2 : ℝ) =
        (x-(k : ℝ))-(v.1 : ℝ)/v.2 := by
      push_cast
      field_simp
      ring
    change |x-((v.1+k*v.2 : ℤ) : ℝ)/(v.2 : ℝ)| < _
    rw [he]
    exact hvgood

end P203.Ch05
