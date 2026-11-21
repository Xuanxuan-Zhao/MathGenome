import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.FundamentalPellSolution
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch06.PellUnits

namespace P203.Ch06.FundamentalPellSolution
open P203Specs.Ch06.PellUnits
open P203Specs.Ch06.FundamentalPellSolution

/-- Real evaluation on the norm-one group. -/
noncomputable def pellValue (D : ℤ) (hD : 0 < D) : Pell.Solution₁ D →* ℝ where
  toFun a := realValue D (a : IntegralQuadratic D)
  map_one' := (realEmbedding D hD).map_one
  map_mul' _ _ := (realEmbedding D hD).map_mul _ _

/-- A norm-one element, viewed in the standard Pell group. -/
def asPell {D : ℤ} (u : IntegralQuadratic D) (hu : norm u = 1) : Pell.Solution₁ D :=
  ⟨u, Zsqrtd.norm_eq_one_iff_mem_unitary.mp hu⟩

lemma pell_norm {D : ℤ} (a : Pell.Solution₁ D) :
    norm (a : IntegralQuadratic D) = 1 :=
  (P203.Ch06.PellUnits.pell_correspondence D).1 a

lemma least_of_fundamental {D : ℤ} (hD : 0 < D) {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) : LeastPositive D (a : IntegralQuadratic D) := by
  have hau : IsUnit (a : IntegralQuadratic D) :=
    (P203.Ch06.PellUnits.unit_criterion D _).mpr (Or.inl (pell_norm a))
  refine ⟨pell_norm a, (P203.Ch06.PellUnits.positive_coordinates D hD _ hau).mpr
    ⟨ha.x_pos, ha.2.1⟩, ?_⟩
  intro v hv hvpos
  have hvu := (P203.Ch06.PellUnits.unit_criterion D v).mpr (Or.inl hv)
  obtain ⟨hx, hy⟩ := (P203.Ch06.PellUnits.positive_coordinates D hD v hvu).mp hvpos
  let b := asPell v hv
  have hbx : 1 < b.x := by
    have hp := b.prop
    change 0 < b.x at hx
    change 0 < b.y at hy
    nlinarith [mul_pos hD (sq_pos_of_pos hy)]
  have hxx : (a.x : ℝ) ≤ b.x := by exact_mod_cast ha.x_le_x hbx
  have hyy : (a.y : ℝ) ≤ b.y := by exact_mod_cast ha.y_le_y hbx hy
  have hs := Real.sqrt_nonneg (D : ℝ)
  change (a.x : ℝ) + a.y * Real.sqrt (D : ℝ) ≤
    (b.x : ℝ) + b.y * Real.sqrt (D : ℝ)
  exact add_le_add hxx (mul_le_mul_of_nonneg_right hyy hs)

lemma least_unique {D : ℤ} (hD : 0 < D) (hns : ¬IsSquare D)
    {u v : IntegralQuadratic D} (hu : LeastPositive D u) (hv : LeastPositive D v) :
    u = v := by
  apply (P203.Ch06.PellUnits.real_model D hD hns).1
  exact le_antisymm (hu.2.2 v hv.1 hv.2.1) (hv.2.2 u hu.1 hu.2.1)

theorem fundamental_bridge : FundamentalBridge := by
  intro D hD hns a
  refine ⟨least_of_fundamental hD, ?_⟩
  intro ha
  obtain ⟨b, hb⟩ := Pell.IsFundamental.exists_of_not_isSquare hD hns
  have hab := least_unique hD hns ha (least_of_fundamental hD hb)
  have : a = b := Subtype.ext hab
  rwa [this]

theorem fundamental_exists : FundamentalExists := by
  intro D hD hns
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hD hns
  refine ⟨a, least_of_fundamental hD ha, ?_⟩
  intro b hb
  exact least_unique hD hns hb (least_of_fundamental hD ha)

theorem least_coordinates : LeastCoordinates := by
  intro D hD u hu
  have hi := (P203.Ch06.PellUnits.unit_criterion D u).mpr (Or.inl hu.1)
  exact ⟨hi, (P203.Ch06.PellUnits.positive_coordinates D hD u hi).mp hu.2.1⟩

/-- Positivity of the coordinates removes the zero exponent in Mathlib's
nonnegative-power parametrization. Strict increase gives uniqueness. -/
theorem positive_parametrization : PositiveParametrization := by
  intro D hD hns u hu x y hx hy hxy
  let a := asPell u hu.1
  have ha : Pell.IsFundamental a := (fundamental_bridge D hD hns a).mpr hu
  let b := Pell.Solution₁.mk x y hxy
  obtain ⟨n, hn⟩ := ha.eq_pow_of_nonneg (a := b) hx hy.le
  have hnpos : 1 ≤ n := by
    by_contra hnpos
    have hnzero : n = 0 := by omega
    have hby := congrArg Pell.Solution₁.y hn
    change y = (a ^ n).y at hby
    simp only [hnzero, pow_zero, Pell.Solution₁.y_one] at hby
    omega
  have heval : realValue D (⟨x, y⟩ : IntegralQuadratic D) = (realValue D u) ^ n := by
    change pellValue D hD b = (pellValue D hD a) ^ n
    rw [hn, map_pow]
  refine ⟨n, ⟨hnpos, heval⟩, ?_⟩
  intro m hm
  exact (pow_right_strictMono₀ hu.2.1).injective (hm.2.symm.trans heval)

theorem positive_powers : PositivePowers := by
  intro D hD hns u hu j hj
  let a := asPell u hu.1
  have ha : Pell.IsFundamental a := (fundamental_bridge D hD hns a).mpr hu
  have hc : ((a ^ j : Pell.Solution₁ D) : IntegralQuadratic D) = u ^ j :=
    SubmonoidClass.coe_pow a j
  rw [← hc]
  refine ⟨pell_norm (a ^ j), Pell.Solution₁.x_pow_pos ha.x_pos j, ?_, ?_⟩
  · change 0 < (a ^ j).y
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact Pell.Solution₁.y_pow_succ_pos ha.x_pos ha.2.1 k
  · exact (pellValue D hD).map_pow a j

lemma pellValue_neg (D : ℤ) (hD : 0 < D) (a : Pell.Solution₁ D) :
    pellValue D hD (-a) = -pellValue D hD a :=
  (realEmbedding D hD).map_neg (a : IntegralQuadratic D)

/-- Positive real value removes the common minus sign from the Pell group
classification, even for units whose imaginary coordinate is negative. -/
theorem integer_parametrization : IntegerParametrization := by
  intro D hD hns u hu v hv hvpos
  let a := asPell u hu.1
  let b := asPell v hv
  have ha : Pell.IsFundamental a := (fundamental_bridge D hD hns a).mpr hu
  obtain ⟨j, hj | hj⟩ := ha.eq_zpow_or_neg_zpow b
  · have heval : realValue D v = (realValue D u) ^ j := by
      change pellValue D hD b = (pellValue D hD a) ^ j
      rw [hj, map_zpow]
    refine ⟨j, heval, ?_⟩
    intro k hk
    exact (zpow_right_strictMono₀ hu.2.1).injective (hk.symm.trans heval)
  · have heval : realValue D v = -(realValue D u) ^ j := by
      change pellValue D hD b = -(pellValue D hD a) ^ j
      rw [hj, pellValue_neg, map_zpow]
    have hp := zpow_pos (lt_trans zero_lt_one hu.2.1) j
    linarith

theorem integer_powers : IntegerPowers := by
  intro D hD hns u hu j
  let a := asPell u hu.1
  have ha : Pell.IsFundamental a := (fundamental_bridge D hD hns a).mpr hu
  let v : IntegralQuadratic D := (a ^ j : Pell.Solution₁ D)
  have hn : norm v = 1 := pell_norm (a ^ j)
  have hi := (P203.Ch06.PellUnits.unit_criterion D v).mpr (Or.inl hn)
  have heval : realValue D v = (realValue D u) ^ j := (pellValue D hD).map_zpow a j
  refine ⟨v, hn, hi, heval, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heval]
    exact zpow_pos (lt_trans zero_lt_one hu.2.1) j
  · constructor
    · intro hv
      exact (ha.zpow_eq_one_iff j).mp (Subtype.ext hv)
    · rintro rfl
      rfl
  · rw [heval]
    exact zpow_lt_one_iff_right₀ hu.2.1
  · rw [heval]
    exact zpow_eq_one_iff_right₀ (le_of_lt (lt_trans zero_lt_one hu.2.1)) (ne_of_gt hu.2.1)
  · rw [heval]
    exact one_lt_zpow_iff_right₀ hu.2.1

end P203.Ch06.FundamentalPellSolution
