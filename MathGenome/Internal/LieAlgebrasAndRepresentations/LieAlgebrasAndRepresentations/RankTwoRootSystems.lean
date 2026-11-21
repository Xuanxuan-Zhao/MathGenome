import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RankTwoRootSystems
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootSystems
import Mathlib.Order.Interval.Set.OrdConnectedLinear
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
namespace LieAlgebrasAndRepresentations
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma rootCartan_mul_self (a b : E) :
    rootCartan b a * inner ℝ a a = 2 * inner ℝ b a := by
  by_cases ha : a = 0
  · simp [ha, rootCartan]
  · exact div_mul_cancel₀ _ (inner_self_ne_zero ha)

lemma strict_inner_sq_of_independent {a b : E} (ha : a ≠ 0)
    (hli : LinearIndependent ℝ ![a, b]) :
    inner ℝ a b ^ 2 < inner ℝ a a * inner ℝ b b := by
  have hA := (real_inner_self_pos.mpr ha)
  let t : ℝ := inner ℝ a b / inner ℝ a a
  have ht : t * inner ℝ a a = inner ℝ a b := div_mul_cancel₀ _ hA.ne'
  have hw : b - t • a ≠ 0 := by
    intro h
    exact (LinearIndependent.pair_iff' ha).mp hli t (sub_eq_zero.mp h).symm
  have hpos := real_inner_self_pos.mpr hw
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right] at hpos
  simp only [real_inner_comm a b] at hpos
  have heq : inner ℝ a a * (inner ℝ b b - t * inner ℝ a b -
      (t * inner ℝ a b - t * (t * inner ℝ a a))) =
      inner ℝ a a * inner ℝ b b - inner ℝ a b ^ 2 := by
    calc _ = inner ℝ a a * inner ℝ b b -
        2 * (t * inner ℝ a a) * inner ℝ a b + (t * inner ℝ a a)^2 := by ring
      _ = _ := by rw [ht]; ring
  have hp := mul_pos hA hpos
  rw [heq] at hp
  linarith

lemma independent_of_roots_not_parallel {R : Set E} (hR : RootAxioms R)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R) (h₁ : a ≠ b) (h₂ : a ≠ -b) :
    LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff' (hR.nonzero a ha)]
  intro t ht
  have hs : b ∈ Submodule.span ℝ ({a} : Set E) := by
    rw [← ht]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  rcases hR.reduced a ha b hb hs with h | h
  · exact h₁ h.symm
  · exact h₂ (by rw [h, neg_neg])

lemma cartan_integer_product_bounds {R : Set E} (hR : RootAxioms R)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R)
    (hli : LinearIndependent ℝ ![a, b]) :
    ∃ m n : ℤ, rootCartan a b = m ∧ rootCartan b a = n ∧
      0 ≤ m * n ∧ m * n < 4 ∧ (m = 0 ↔ n = 0) := by
  obtain ⟨m, hm⟩ := hR.integral b hb a ha
  obtain ⟨n, hn⟩ := hR.integral a ha b hb
  change rootCartan a b = (m : ℝ) at hm
  change rootCartan b a = (n : ℝ) at hn
  have hA := real_inner_self_pos.mpr (hR.nonzero a ha)
  have hB := real_inner_self_pos.mpr (hR.nonzero b hb)
  have hAB := mul_pos hA hB
  have hstrict := strict_inner_sq_of_independent (hR.nonzero a ha) hli
  have hma : (m : ℝ) * inner ℝ b b = 2 * inner ℝ a b := by
    rw [← hm]; exact rootCartan_mul_self b a
  have hnb : (n : ℝ) * inner ℝ a a = 2 * inner ℝ a b := by
    rw [← hn, rootCartan_mul_self, real_inner_comm]
  have hp : ((m * n : ℤ) : ℝ) * (inner ℝ a a * inner ℝ b b) =
      4 * inner ℝ a b ^ 2 := by
    rw [Int.cast_mul]
    calc (m : ℝ) * n * (inner ℝ a a * inner ℝ b b) =
        ((m : ℝ) * inner ℝ b b) * ((n : ℝ) * inner ℝ a a) := by ring
      _ = _ := by rw [hma, hnb]; ring
  refine ⟨m, n, hm, hn, ?_, ?_, ?_⟩
  · have : (0 : ℝ) ≤ (m * n : ℤ) := by nlinarith [sq_nonneg (inner ℝ a b)]
    exact_mod_cast this
  · have : ((m * n : ℤ) : ℝ) < 4 := by nlinarith
    exact_mod_cast this
  · constructor
    · intro hm0
      have : (n : ℝ) = 0 := by simp only [hm0, Int.cast_zero, zero_mul] at hma; nlinarith
      exact_mod_cast this
    · intro hn0
      have : (m : ℝ) = 0 := by simp only [hn0, Int.cast_zero, zero_mul] at hnb; nlinarith
      exact_mod_cast this

theorem cartan_restrictions : RankTwoSpecs.cartanRestrictionsType := by
  intro E _ _ R hR a ha b hb hli
  obtain ⟨m, n, hm, hn, hp₀, hp₄, hz⟩ := cartan_integer_product_bounds hR ha hb hli
  have hp : m * n ∈ ({0, 1, 2, 3, 4} : Set ℤ) := by
    simp only [mem_insert_iff, mem_singleton_iff]
    omega
  have hmn := (Int.mul_mem_zero_one_two_three_four_iff hz).mp hp
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hmn ⊢
  rcases hmn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> simp_all


lemma cartan_product_cos {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    rootCartan a b * rootCartan b a =
      4 * Real.cos (InnerProductGeometry.angle a b) ^ 2 := by
  have hnA := norm_ne_zero_iff.mpr ha
  have hnB := norm_ne_zero_iff.mpr hb
  rw [InnerProductGeometry.cos_angle]
  simp only [rootCartan, real_inner_self_eq_norm_sq, real_inner_comm a b]
  field_simp
  <;> ring

theorem angle_restriction : RankTwoSpecs.angleRestrictionType := by
  intro E _ _ R hR a ha b hb hli
  have hp := cartan_product_cos (hR.nonzero a ha) (hR.nonzero b hb)
  have hr := cartan_restrictions R hR a ha b hb hli
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hr ⊢
  rcases hr with h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨h₁, h₂⟩ <;> rw [h₁, h₂] at hp
  all_goals first
    | left; linarith
    | right; first
      | left; linarith
      | right; left; linarith
      | right; right; linarith

theorem length_restriction : RankTwoSpecs.lengthRestrictionType := by
  intro E _ _ R hR a ha b hb hip
  by_cases h₁ : a = b
  · exact Or.inl (by rw [h₁])
  by_cases h₂ : a = -b
  · exact Or.inl (by rw [h₂, inner_neg_neg])
  have hr := cartan_restrictions R hR a ha b hb
    (independent_of_roots_not_parallel hR ha hb h₁ h₂)
  have hm := rootCartan_mul_self b a
  have hn := rootCartan_mul_self a b
  simp only [real_inner_comm a b] at hn
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨h₁, h₂⟩ <;> rw [h₁] at hm <;> rw [h₂] at hn
  all_goals first
    | exact False.elim (hip (by linarith))
    | left; linarith
    | right; left; linarith
    | right; right; left; linarith
    | right; right; right; left; linarith
    | right; right; right; right; linarith

theorem difference_root : RankTwoSpecs.differenceRootType := by
  intro E _ _ R hR a ha b hb hne hip
  have hn : a ≠ -b := by
    intro heq
    have hn := real_inner_self_nonneg (x := b)
    rw [heq, inner_neg_left] at hip
    linarith
  have hr := cartan_restrictions R hR a ha b hb
    (independent_of_roots_not_parallel hR ha hb hne hn)
  have hc : 0 < rootCartan a b :=
    div_pos (mul_pos two_pos hip) (real_inner_self_pos.mpr (hR.nonzero b hb))
  have hor : rootCartan a b = 1 ∨ rootCartan b a = 1 := by
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨h₁, h₂⟩
    all_goals first
      | exact Or.inl h₁
      | exact Or.inr h₂
      | rw [h₁] at hc; norm_num at hc
  rcases hor with h | h
  · have hh := hR.reflection_mem b hb a ha
    change a - rootCartan a b • b ∈ R at hh
    simpa only [h, one_smul] using hh
  · have hh := hR.reflection_mem a ha b hb
    change b - rootCartan b a • a ∈ R at hh
    rw [h, one_smul] at hh
    simpa only [neg_sub] using hR.neg_mem hh

theorem sum_root : RankTwoSpecs.sumRootType := by
  intro E _ _ R hR a ha b hb hne hip
  have hp : 0 < inner ℝ a (-b) := by simpa using neg_pos.mpr hip
  simpa using difference_root R hR a ha (-b) (hR.neg_mem hb) hne hp

/-- Shifting along an independent root never reaches its line. -/
lemma root_shift_not_smul {a b : E} (ha : a ≠ 0)
    (hli : LinearIndependent ℝ ![a, b]) (z : ℤ) (t : ℝ) :
    b + z • a ≠ t • a := by
  intro h
  apply (LinearIndependent.pair_iff' ha).mp hli (t - z)
  rw [sub_smul, ← h, Int.cast_smul_eq_zsmul]
  abel

lemma rootCartan_shift {a : E} (ha : a ≠ 0) (b : E) (z : ℤ) :
    rootCartan (b + z • a) a = rootCartan b a + 2 * (z : ℝ) := by
  have hn := inner_self_ne_zero ha
  simp only [rootCartan, inner_add_left, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left]
  field_simp

lemma root_string_ordConnected {R : Set E} (hR : RootAxioms R)
    {a b : E} (ha : a ∈ R) (hli : LinearIndependent ℝ ![a, b]) :
    Set.OrdConnected {z : ℤ | b + z • a ∈ R} := by
  rw [Set.ordConnected_iff_disjoint_Ioo_empty]
  intro m hm n hn hgap
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hmn : m + 1 < n := by
    have := hz.1
    have := hz.2
    omega
  have hm0 : 0 ≤ inner ℝ (b + m • a) a := by
    by_contra h
    have hr := sum_root R hR (b + m • a) hm a ha
      (by simpa using root_shift_not_smul (hR.nonzero a ha) hli m (-1))
      (lt_of_not_ge h)
    have he : b + m • a + a = b + (m + 1) • a := by
      simp only [add_zsmul, one_zsmul]; abel
    rw [he] at hr
    exact Set.disjoint_left.mp hgap (by constructor <;> omega) hr
  have hn0 : inner ℝ (b + n • a) a ≤ 0 := by
    by_contra h
    have hr := difference_root R hR (b + n • a) hn a ha
      (by simpa using root_shift_not_smul (hR.nonzero a ha) hli n 1)
      (lt_of_not_ge h)
    have he : b + n • a - a = b + (n - 1) • a := by
      simp only [sub_zsmul, one_zsmul]; abel
    rw [he] at hr
    exact Set.disjoint_left.mp hgap (by constructor <;> omega) hr
  have hA := real_inner_self_pos.mpr (hR.nonzero a ha)
  simp only [inner_add_left, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left] at hm0 hn0
  have hmn' : (m : ℝ) < n := by exact_mod_cast (show m < n by omega)
  nlinarith

theorem root_string : RankTwoSpecs.rootStringType := by
  intro E _ _ R hR a ha b hb hli
  let S : Set ℤ := {z | b + z • a ∈ R}
  have hinj : Function.Injective (fun z : ℤ => b + z • a) := by
    intro m n h
    have he : (m : ℝ) • a = (n : ℝ) • a := by
      simpa only [Int.cast_smul_eq_zsmul] using add_left_cancel h
    exact_mod_cast smul_left_injective ℝ (hR.nonzero a ha) he
  have hS : S.Finite := hR.finite.preimage hinj.injOn
  have h0 : 0 ∈ S := by simpa [S] using hb
  have hne : S.Nonempty := ⟨0, h0⟩
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image S id hS hne
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image S id hS hne
  change ∀ z ∈ S, m ≤ z at hmin
  change ∀ z ∈ S, z ≤ n at hmax
  have hm0 := hmin 0 h0
  have hn0 := hmax 0 h0
  have hmroot : b + m • a ∈ R := hm
  have hnroot : b + n • a ∈ R := hn
  obtain ⟨c, hc⟩ := hR.integral a ha b hb
  change rootCartan b a = (c : ℝ) at hc
  have hreflect (z : ℤ) (hz : z ∈ S) : -c - z ∈ S := by
    have hr := hR.reflection_mem a ha (b + z • a) hz
    change b + z • a - rootCartan (b + z • a) a • a ∈ R at hr
    rw [rootCartan_shift (hR.nonzero a ha), hc] at hr
    have he : b + z • a - ((c : ℝ) + 2 * (z : ℝ)) • a =
        b + (-c - z) • a := by
      simp only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_sub, Int.cast_neg]
      module
    rw [he] at hr
    exact hr
  have hcmn : c = -m - n := by
    have h₁ := hmax _ (hreflect m hm)
    have h₂ := hmin _ (hreflect n hn)
    omega
  have hbound (z : ℤ) (hz : z ∈ S) :
      -3 ≤ rootCartan (b + z • a) a ∧ rootCartan (b + z • a) a ≤ 3 := by
    have hi : LinearIndependent ℝ ![a, b + z • a] := by
      rw [LinearIndependent.pair_iff' (hR.nonzero a ha)]
      intro t ht
      exact root_shift_not_smul (hR.nonzero a ha) hli z t ht.symm
    have hr := cartan_restrictions R hR (b + z • a) hz a ha (LinearIndependent.pair_symm_iff.mpr hi)
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨h₁, h₂⟩ <;> rw [h₁] <;> norm_num
  have hmb := (hbound m hm).1
  have hnb := (hbound n hn).2
  rw [rootCartan_shift (hR.nonzero a ha)] at hmb hnb
  have hlen : n - m ≤ 3 := by
    have : (n : ℝ) - m ≤ 3 := by linarith
    exact_mod_cast this
  have hp : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have hq : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
  refine ⟨n.toNat, (-m).toNat, ?_, ?_, ?_⟩
  · omega
  · rw [hc]
    have he : (c : ℝ) = (-m : ℤ) - n := by exact_mod_cast hcmn
    rw [he]
    exact_mod_cast (show (-m : ℤ) - n = ((-m).toNat : ℤ) - n.toNat by omega)
  · intro z
    change z ∈ S ↔ _
    rw [hp, hq, neg_neg]
    constructor
    · intro hz
      exact ⟨hmin z hz, hmax z hz⟩
    · intro hz
      exact (root_string_ordConnected hR ha hli).out hm hn hz

lemma pair_coefficient_injective {a b : E} (hli : LinearIndependent ℝ ![a,b]) :
    Function.Injective (fun p : ℤ × ℤ => p.1 • a + p.2 • b) := by
  intro p q he
  have hh : ((p.1 : ℝ) - q.1) • a + ((p.2 : ℝ) - q.2) • b = 0 := by
    simp only [sub_smul, Int.cast_smul_eq_zsmul]
    calc _ = (p.1 • a + p.2 • b) - (q.1 • a + q.2 • b) := by abel
      _ = 0 := sub_eq_zero.mpr he
  obtain ⟨h₁, h₂⟩ := (LinearIndependent.pair_iff.mp hli) _ _ hh
  apply Prod.ext <;> apply Int.cast_injective (α := ℝ) <;> linarith

theorem rank_two_root_count : RankTwoSpecs.rootCountType := by
  intro E _ _ R k h
  obtain ⟨a, ha, b, hb, hli, hs, hg, rfl⟩ := h
  rw [rankTwoRootSet, Set.ncard_image_of_injective _ (pair_coefficient_injective hli),
    Set.ncard_coe_finset]
  cases k <;> norm_num [rankTwoCoefficients, rankTwoCount]

lemma eq_of_inner_pair {a b x y : E}
    (hs : Submodule.span ℝ ({a,b} : Set E) = ⊤)
    (ha : inner ℝ x a = inner ℝ y a) (hb : inner ℝ x b = inner ℝ y b) : x = y := by
  have hd : x - y ∈ Submodule.span ℝ ({a,b} : Set E) := by rw [hs]; trivial
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hd
  apply sub_eq_zero.mp
  apply (_root_.inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [← hst]
  have h₁ : inner ℝ (s • a + t • b) a = 0 := by rw [hst, inner_sub_left, ha, sub_self]
  have h₂ : inner ℝ (s • a + t • b) b = 0 := by rw [hst, inner_sub_left, hb, sub_self]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, h₁, h₂]
  ring

/-- Coordinate inversion and the norm equation for the rank-two Gram matrix.
Here `a` is short and `b` is long, with squared-length ratio `k`. -/
lemma rank_two_coordinates {a b c : E} (k : ℝ) (hk : k ≠ 4) (hk0 : k ≠ 0)
    (ha : a ≠ 0) (hs : Submodule.span ℝ ({a,b} : Set E) = ⊤)
    (hB : inner ℝ b b = k * inner ℝ a a)
    (hab : 2 * inner ℝ a b = -inner ℝ b b)
    (m n : ℝ) (hm : m * inner ℝ a a = 2 * inner ℝ c a)
    (hn : n * inner ℝ b b = 2 * inner ℝ c b) :
    c = ((2*m + k*n)/(4-k)) • a + ((m+2*n)/(4-k)) • b ∧
      (4-k) * inner ℝ c c = (m^2+k*m*n+k*n^2) * inner ℝ a a := by
  have hA := inner_self_ne_zero ha
  have hab' : inner ℝ a b = -k * inner ℝ a a / 2 := by rw [hB] at hab; linarith
  have hba' : inner ℝ b a = -k * inner ℝ a a / 2 := by rw [real_inner_comm]; exact hab'
  have hc : c ∈ Submodule.span ℝ ({a,b} : Set E) := by rw [hs]; trivial
  obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.mp hc
  simp only [inner_add_left, real_inner_smul_left, hB, hab', hba'] at hm hn
  have hx : 2*x-k*y = m := by
    apply mul_right_cancel₀ hA
    nlinarith only [hm]
  have hy : -x+2*y = n := by
    apply mul_right_cancel₀ (mul_ne_zero hk0 hA)
    nlinarith only [hn]
  have hx' : x = (2*m+k*n)/(4-k) := by
    apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hk))).mpr
    rw [← hx, ← hy]
    ring
  have hy' : y = (m+2*n)/(4-k) := by
    apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hk))).mpr
    rw [← hx, ← hy]
    ring
  refine ⟨by rw [← hx', ← hy'], ?_⟩
  rw [← hx, ← hy]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hB, hab', hba']
  ring

private def cartanPairSet : Set (ℝ × ℝ) :=
  {(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1),
    (1, 3), (3, 1), (-1, -3), (-3, -1)}

private def rankTwoPairingCandidates : ℕ → Set (ℝ × ℝ)
  | 1 => {(1,1), (-1,-1)}
  | 2 => {(0,1), (0,-1), (2,0), (-2,0), (0,2), (0,-2), (1,0), (-1,0)}
  | _ => {(0,1), (0,-1), (1,0), (-1,0), (1,-1), (-1,1), (3,-1), (-3,1)}

set_option maxHeartbeats 2000000 in
/-- The finite arithmetic step in rank-two exhaustion. The two exceptional
pairs in type B₂ are eliminated subsequently using reducedness. -/
private lemma rank_two_pairing_candidates (k : ℕ) (hk : k=1 ∨ k=2 ∨ k=3)
    (A C m r n s : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hpairA : (m,r) ∈ cartanPairSet) (hpairB : (n,s) ∈ cartanPairSet)
    (hmaxA : m*r ≤ k) (hmaxB : n*s ≤ k)
    (hrelA : m*A = r*C) (hrelB : n*(k*A) = s*C)
    (hnorm : (4-k)*C = (m^2+k*m*n+k*n^2)*A) :
    (m,n) ∈ rankTwoPairingCandidates k := by
  have htestA : (4-k)*m = r*(m^2+k*m*n+k*n^2) := by
    apply mul_right_cancel₀ hA.ne'
    calc
      (4-k)*m*A = (4-k)*(m*A) := by ring
      _ = (4-k)*(r*C) := by rw [hrelA]
      _ = r*((4-k)*C) := by ring
      _ = (r*(m^2+k*m*n+k*n^2))*A := by rw [hnorm]; ring
  have htestB : k*(4-k)*n = s*(m^2+k*m*n+k*n^2) := by
    apply mul_right_cancel₀ hA.ne'
    calc
      k*(4-k)*n*A = (4-k)*(n*(k*A)) := by ring
      _ = (4-k)*(s*C) := by rw [hrelB]
      _ = s*((4-k)*C) := by ring
      _ = (s*(m^2+k*m*n+k*n^2))*A := by rw [hnorm]; ring
  simp only [cartanPairSet, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
    at hpairA hpairB
  rcases hk with rfl | rfl | rfl <;>
    rcases hpairA with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hpairB with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    (try norm_num at hmaxA) <;> (try norm_num at hmaxB) <;>
    (try norm_num at htestA) <;> (try norm_num at htestB) <;>
    norm_num [rankTwoPairingCandidates]
  all_goals norm_num at hnorm
  all_goals linarith

lemma rootCartan_add (a b c : E) :
    rootCartan (a+b) c = rootCartan a c + rootCartan b c := by
  simp only [rootCartan, inner_add_left, mul_add, add_div]

lemma rootCartan_zsmul (a b : E) (z : ℤ) :
    rootCartan (z • a) b = (z : ℝ) * rootCartan a b := by
  simp only [rootCartan, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left]
  ring

lemma rootCartan_self {a : E} (ha : a ≠ 0) : rootCartan a a = 2 := by
  rw [rootCartan]
  exact (div_eq_iff (inner_self_ne_zero ha)).mpr (by ring)

lemma root_scalar_eq_one_or_neg_one {R : Set E} (hR : RootAxioms R)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R) {t : ℝ} (he : b = t • a) :
    t = 1 ∨ t = -1 := by
  have hs : b ∈ Submodule.span ℝ ({a} : Set E) := by
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  rcases hR.reduced a ha b hb hs with h | h
  · left
    apply smul_left_injective ℝ (hR.nonzero a ha)
    change t • a = (1 : ℝ) • a
    rw [← he, h, one_smul]
  · right
    apply smul_left_injective ℝ (hR.nonzero a ha)
    change t • a = (-1 : ℝ) • a
    rw [← he, h, neg_one_smul]

private def rankTwoKindOf : ℕ → RankTwoKind
  | 1 => .A₂
  | 2 => .B₂
  | _ => .G₂

lemma root_string_forward {R : Set E} (hR : RootAxioms R)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R)
    (hli : LinearIndependent ℝ ![a,b]) (k : ℕ)
    (hc : rootCartan b a = -(k : ℝ)) (j : ℕ) (hj : j ≤ k) :
    (j : ℤ) • a + b ∈ R := by
  obtain ⟨p, q, hlen, hcart, hstring⟩ := root_string R hR a ha b hb hli
  have he : (p : ℝ) = q + k := by rw [hc] at hcart; linarith
  have hk : k ≤ p := by
    have : (k : ℝ) ≤ p := by linarith [Nat.cast_nonneg (α := ℝ) q]
    exact_mod_cast this
  have hr := (hstring (j : ℤ)).mpr (by constructor <;> omega)
  simpa [add_comm] using hr

private lemma rank_two_generated_roots {R : Set E} (hR : RootAxioms R)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R)
    (hli : LinearIndependent ℝ ![a,b]) (k : ℕ) (hk : k=1 ∨ k=2 ∨ k=3)
    (hca : rootCartan b a = -(k : ℝ)) (hcb : rootCartan a b = -1) :
    rankTwoRootSet (rankTwoKindOf k) a b ⊆ R := by
  have h₁ := root_string_forward hR ha hb hli k hca 1 (by rcases hk with rfl | rfl | rfl <;> omega)
  have h₂ (h : 2 ≤ k) := root_string_forward hR ha hb hli k hca 2 h
  have h₃ (h : 3 ≤ k) := root_string_forward hR ha hb hli k hca 3 h
  have h₄ (h : k = 3) : (3 : ℤ) • a + (2 : ℤ) • b ∈ R := by
    have hu := h₃ (by omega)
    have hv := hR.reflection_mem b hb _ hu
    change (3 : ℤ) • a + b - rootCartan ((3 : ℤ) • a + b) b • b ∈ R at hv
    rw [rootCartan_add, rootCartan_zsmul, hcb, rootCartan_self (hR.nonzero b hb)] at hv
    norm_num at hv
    convert hv using 1 <;> simp only [← Int.cast_smul_eq_zsmul ℝ] <;> module
  rintro c ⟨p, hp, rfl⟩
  rcases hk with rfl | rfl | rfl
  · simp only [rankTwoKindOf, rankTwoCoefficients, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa using ha
      | simpa using hR.neg_mem ha
      | simpa using hb
      | simpa using hR.neg_mem hb
      | simpa using h₁
      | simpa [neg_add, add_comm] using hR.neg_mem h₁
  · have h₂ := h₂ (by omega)
    simp only [rankTwoKindOf, rankTwoCoefficients, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa using ha
      | simpa using hR.neg_mem ha
      | simpa using hb
      | simpa using hR.neg_mem hb
      | simpa using h₁
      | simpa [neg_add, add_comm] using hR.neg_mem h₁
      | simpa using h₂
      | simpa [neg_add, add_comm] using hR.neg_mem h₂
  · have h₂ := h₂ (by omega)
    have h₃ := h₃ (by omega)
    have h₄ := h₄ rfl
    simp only [rankTwoKindOf, rankTwoCoefficients, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa using ha
      | simpa using hR.neg_mem ha
      | simpa using hb
      | simpa using hR.neg_mem hb
      | simpa using h₁
      | simpa [neg_add, add_comm] using hR.neg_mem h₁
      | simpa using h₂
      | simpa [neg_add, add_comm] using hR.neg_mem h₂
      | simpa using h₃
      | simpa [neg_add, add_comm] using hR.neg_mem h₃
      | simpa using h₄
      | simpa [neg_add, add_comm] using hR.neg_mem h₄

private lemma rank_two_exhaustion {R : Set E} (hR : RootAxioms R)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R)
    (hli : LinearIndependent ℝ ![a,b])
    (hs : Submodule.span ℝ ({a,b} : Set E) = ⊤)
    (k : ℕ) (hk : k=1 ∨ k=2 ∨ k=3)
    (hca : rootCartan b a = -(k : ℝ)) (hcb : rootCartan a b = -1)
    (hmax : ∀ x ∈ R, ∀ y ∈ R, LinearIndependent ℝ ![x,y] →
      rootCartan x y * rootCartan y x ≤ k) :
    R = rankTwoRootSet (rankTwoKindOf k) a b := by
  apply Set.Subset.antisymm _ (rank_two_generated_roots hR ha hb hli k hk hca hcb)
  intro c hc
  by_cases h₁ : c = a
  · subst c
    refine ⟨(1,0), ?_, by simp⟩
    rcases hk with rfl | rfl | rfl <;> norm_num [rankTwoKindOf, rankTwoCoefficients]
  by_cases h₂ : c = -a
  · subst c
    refine ⟨(-1,0), ?_, by simp⟩
    rcases hk with rfl | rfl | rfl <;> norm_num [rankTwoKindOf, rankTwoCoefficients]
  by_cases h₃ : c = b
  · subst c
    refine ⟨(0,1), ?_, by simp⟩
    rcases hk with rfl | rfl | rfl <;> norm_num [rankTwoKindOf, rankTwoCoefficients]
  by_cases h₄ : c = -b
  · subst c
    refine ⟨(0,-1), ?_, by simp⟩
    rcases hk with rfl | rfl | rfl <;> norm_num [rankTwoKindOf, rankTwoCoefficients]
  have hliA := independent_of_roots_not_parallel hR hc ha h₁ h₂
  have hliB := independent_of_roots_not_parallel hR hc hb h₃ h₄
  have hA := real_inner_self_pos.mpr (hR.nonzero a ha)
  have hC := real_inner_self_pos.mpr (hR.nonzero c hc)
  have hab : 2 * inner ℝ a b = -inner ℝ b b := by
    have ht := rootCartan_mul_self b a
    rw [hcb] at ht
    linarith
  have hB : inner ℝ b b = (k : ℝ) * inner ℝ a a := by
    have ht := rootCartan_mul_self a b
    rw [hca, real_inner_comm a b] at ht
    linarith
  let m := rootCartan c a
  let r := rootCartan a c
  let n := rootCartan c b
  let s := rootCartan b c
  have hpairA : (m,r) ∈ cartanPairSet := cartan_restrictions R hR c hc a ha hliA
  have hpairB : (n,s) ∈ cartanPairSet := cartan_restrictions R hR c hc b hb hliB
  have hmaxA : m*r ≤ k := hmax c hc a ha hliA
  have hmaxB : n*s ≤ k := hmax c hc b hb hliB
  have hrelA : m * inner ℝ a a = r * inner ℝ c c := by
    dsimp [m,r]
    rw [rootCartan_mul_self, rootCartan_mul_self, real_inner_comm c a]
  have hrelB : n * ((k : ℝ) * inner ℝ a a) = s * inner ℝ c c := by
    rw [← hB]
    dsimp [n,s]
    rw [rootCartan_mul_self, rootCartan_mul_self, real_inner_comm c b]
  obtain ⟨heq, hnorm⟩ := rank_two_coordinates (k : ℝ)
    (by rcases hk with rfl | rfl | rfl <;> norm_num)
    (by rcases hk with rfl | rfl | rfl <;> norm_num)
    (hR.nonzero a ha) hs hB hab m n (rootCartan_mul_self a c) (rootCartan_mul_self b c)
  have hcan := rank_two_pairing_candidates k hk _ _ m r n s hA hC
    hpairA hpairB hmaxA hmaxB hrelA hrelB hnorm
  rcases hk with rfl | rfl | rfl
  · simp only [rankTwoPairingCandidates, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hcan
    rcases hcan with ⟨hm,hn⟩ | ⟨hm,hn⟩
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(1,1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(-1,-1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
  · simp only [rankTwoPairingCandidates, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hcan
    rcases hcan with ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(1,1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(-1,-1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(2,1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(-2,-1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      have hu := root_string_forward hR ha hb hli 2 hca 1 (by omega)
      have he : c = (2 : ℝ) • ((1 : ℤ) • a + b) := by
        rw [heq]
        simp only [← Int.cast_smul_eq_zsmul ℝ]
        norm_num <;> module
      have ht := root_scalar_eq_one_or_neg_one hR hu hc he
      norm_num at ht
    · rw [hm,hn] at heq
      norm_num at heq
      have hu := root_string_forward hR ha hb hli 2 hca 1 (by omega)
      have he : c = (-2 : ℝ) • ((1 : ℤ) • a + b) := by
        rw [heq]
        simp only [← Int.cast_smul_eq_zsmul ℝ]
        norm_num <;> module
      have ht := root_scalar_eq_one_or_neg_one hR hu hc he
      norm_num at ht
    · rw [hm,hn] at heq
      norm_num at heq
      have hu := root_string_forward hR ha hb hli 2 hca 2 (by omega)
      have he : c = ((1/2) : ℝ) • ((2 : ℤ) • a + b) := by
        rw [heq]
        simp only [← Int.cast_smul_eq_zsmul ℝ]
        norm_num <;> module
      have ht := root_scalar_eq_one_or_neg_one hR hu hc he
      norm_num at ht
    · rw [hm,hn] at heq
      norm_num at heq
      have hu := root_string_forward hR ha hb hli 2 hca 2 (by omega)
      have he : c = ((-1/2) : ℝ) • ((2 : ℤ) • a + b) := by
        rw [heq]
        simp only [← Int.cast_smul_eq_zsmul ℝ]
        norm_num <;> module
      have ht := root_scalar_eq_one_or_neg_one hR hu hc he
      norm_num at ht
  · simp only [rankTwoPairingCandidates, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hcan
    rcases hcan with ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(3,2), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(-3,-2), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(2,1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(-2,-1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(-1,-1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(1,1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(3,1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module
    · rw [hm,hn] at heq
      norm_num at heq
      refine ⟨(-3,-1), by norm_num [rankTwoKindOf, rankTwoCoefficients], ?_⟩
      rw [heq]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
      norm_num <;> module

lemma rank_two_pair_spans (hd : Module.finrank ℝ E = 2) {a b : E}
    (hli : LinearIndependent ℝ ![a,b]) :
    Submodule.span ℝ ({a,b} : Set E) = ⊤ := by
  simpa only [Matrix.range_cons_cons_empty] using
    hli.span_eq_top_of_card_eq_finrank (by simp [hd])

lemma root_pair_exists {R : Set E} (hR : IsRootSystem R)
    (hd : Module.finrank ℝ E = 2) :
    ∃ a ∈ R, ∃ b ∈ R, LinearIndependent ℝ ![a,b] := by
  have hne : R.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hr := congrArg (fun P : Submodule ℝ E => Module.finrank ℝ P) hR.span_eq_top
    rw [he, Submodule.span_empty, finrank_bot, finrank_top, hd] at hr
    omega
  obtain ⟨a, ha⟩ := hne
  have hproper : Submodule.span ℝ ({a} : Set E) ≠ ⊤ := by
    intro he
    have hr := congrArg (fun P : Submodule ℝ E => Module.finrank ℝ P) he
    rw [finrank_span_singleton (hR.nonzero a ha), finrank_top, hd] at hr
    omega
  have hex : ∃ b ∈ R, b ∉ Submodule.span ℝ ({a} : Set E) := by
    by_contra h
    push Not at h
    have hs := Submodule.span_le.mpr h
    rw [hR.span_eq_top] at hs
    exact hproper (top_unique hs)
  obtain ⟨b, hb, hba⟩ := hex
  refine ⟨a, ha, b, hb, (LinearIndependent.pair_iff' (hR.nonzero a ha)).mpr ?_⟩
  intro t ht
  apply hba
  rw [← ht]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

lemma rootCartan_neg_left (a b : E) : rootCartan (-a) b = -rootCartan a b := by
  simp only [rootCartan, inner_neg_left, mul_neg, neg_div]

lemma rootCartan_neg_right (a b : E) : rootCartan a (-b) = -rootCartan a b := by
  simp only [rootCartan, inner_neg_left, inner_neg_right, neg_neg, mul_neg, neg_div]

lemma cartan_product_values {R : Set E} (hR : RootAxioms R) {a b : E}
    (ha : a ∈ R) (hb : b ∈ R) (hli : LinearIndependent ℝ ![a,b]) :
    rootCartan a b * rootCartan b a = 0 ∨
    rootCartan a b * rootCartan b a = 1 ∨
    rootCartan a b * rootCartan b a = 2 ∨
    rootCartan a b * rootCartan b a = 3 := by
  have hr := cartan_restrictions R hR a ha b hb hli
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨h₁,h₂⟩ <;> rw [h₁,h₂] <;> norm_num

private lemma orient_root_pair {R : Set E} (hR : RootAxioms R)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R) (hli : LinearIndependent ℝ ![a,b])
    (k : ℕ) (hk : 0 < k) (hp : rootCartan a b * rootCartan b a = k) :
    ∃ x ∈ R, ∃ y ∈ R, LinearIndependent ℝ ![x,y] ∧
      rootCartan y x = -(k : ℝ) ∧ rootCartan x y = -1 := by
  have hr := cartan_restrictions R hR a ha b hb hli
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hor : rootCartan a b = 1 ∨ rootCartan b a = 1 ∨
      rootCartan a b = -1 ∨ rootCartan b a = -1 := by
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨h₁,h₂⟩
    all_goals first
      | exact Or.inl h₁
      | exact Or.inr (Or.inl h₂)
      | exact Or.inr (Or.inr (Or.inl h₁))
      | exact Or.inr (Or.inr (Or.inr h₂))
      | rw [h₁,h₂] at hp; norm_num at hp; linarith
  rcases hor with h | h | h | h
  · refine ⟨a,ha,-b,hR.neg_mem hb, by simpa using hli, ?_, ?_⟩
    · rw [rootCartan_neg_left]
      rw [h] at hp
      linarith
    · rw [rootCartan_neg_right,h]
  · refine ⟨b,hb,-a,hR.neg_mem ha, ?_, ?_, ?_⟩
    · simpa using (LinearIndependent.pair_symm_iff.mp hli)
    · rw [rootCartan_neg_left]
      rw [h] at hp
      linarith
    · rw [rootCartan_neg_right,h]
  · refine ⟨a,ha,b,hb,hli,?_,h⟩
    rw [h] at hp
    linarith
  · refine ⟨b,hb,a,ha,LinearIndependent.pair_symm_iff.mp hli,?_,h⟩
    rw [h] at hp
    linarith

private def HasCartanProduct (R : Set E) (k : ℕ) : Prop :=
  ∃ a ∈ R, ∃ b ∈ R, LinearIndependent ℝ ![a,b] ∧
    rootCartan a b * rootCartan b a = k

private lemma rank_two_model_of_max {R : Set E} (hR : IsRootSystem R)
    (hd : Module.finrank ℝ E = 2) (k : ℕ) (hk : k=1 ∨ k=2 ∨ k=3)
    (hex : HasCartanProduct R k)
    (hmax : ∀ x ∈ R, ∀ y ∈ R, LinearIndependent ℝ ![x,y] →
      rootCartan x y * rootCartan y x ≤ k) : RankTwoModel R (rankTwoKindOf k) := by
  obtain ⟨u,hu,v,hv,hli,hp⟩ := hex
  obtain ⟨a,ha,b,hb,hli,hca,hcb⟩ := orient_root_pair hR.toRootAxioms hu hv hli k
    (by rcases hk with rfl | rfl | rfl <;> omega) hp
  have hs := rank_two_pair_spans hd hli
  have hab : 2 * inner ℝ a b = -inner ℝ b b := by
    have ht := rootCartan_mul_self b a
    rw [hcb] at ht
    linarith
  have hB : inner ℝ b b = (k : ℝ) * inner ℝ a a := by
    have ht := rootCartan_mul_self a b
    rw [hca, real_inner_comm a b] at ht
    linarith
  refine ⟨a,ha,b,hb,hli,hs,?_,
    rank_two_exhaustion hR.toRootAxioms ha hb hli hs k hk hca hcb hmax⟩
  rcases hk with rfl | rfl | rfl <;>
    exact ⟨by simpa using hB, hab⟩

lemma inner_eq_zero_of_cartan_product_zero {a b : E}
    (hp : rootCartan a b * rootCartan b a = 0) : inner ℝ a b = 0 := by
  rcases mul_eq_zero.mp hp with h | h
  · have ht := rootCartan_mul_self b a
    rw [h] at ht
    linarith
  · have ht := rootCartan_mul_self a b
    rw [h, real_inner_comm a b] at ht
    linarith

private lemma rank_two_orthogonal_model {R : Set E} (hR : IsRootSystem R)
    (hd : Module.finrank ℝ E = 2)
    (hzero : ∀ x ∈ R, ∀ y ∈ R, LinearIndependent ℝ ![x,y] →
      rootCartan x y * rootCartan y x = 0) : RankTwoModel R .A₁A₁ := by
  obtain ⟨a,ha,b,hb,hli⟩ := root_pair_exists hR hd
  have hs := rank_two_pair_spans hd hli
  refine ⟨a,ha,b,hb,hli,hs,inner_eq_zero_of_cartan_product_zero (hzero a ha b hb hli),?_⟩
  apply Set.Subset.antisymm
  · intro c hc
    by_cases h₁ : c = a
    · exact ⟨(1,0), by norm_num [rankTwoCoefficients], by simp [h₁]⟩
    by_cases h₂ : c = -a
    · exact ⟨(-1,0), by norm_num [rankTwoCoefficients], by simp [h₂]⟩
    by_cases h₃ : c = b
    · exact ⟨(0,1), by norm_num [rankTwoCoefficients], by simp [h₃]⟩
    by_cases h₄ : c = -b
    · exact ⟨(0,-1), by norm_num [rankTwoCoefficients], by simp [h₄]⟩
    have hca := inner_eq_zero_of_cartan_product_zero
      (hzero c hc a ha (independent_of_roots_not_parallel hR.toRootAxioms hc ha h₁ h₂))
    have hcb := inner_eq_zero_of_cartan_product_zero
      (hzero c hc b hb (independent_of_roots_not_parallel hR.toRootAxioms hc hb h₃ h₄))
    have hc0 : c = 0 := eq_of_inner_pair hs (by simpa using hca) (by simpa using hcb)
    exact False.elim (hR.nonzero c hc hc0)
  · rintro c ⟨p,hp,rfl⟩
    simp only [rankTwoCoefficients, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals first
      | simpa using ha
      | simpa using hR.toRootAxioms.neg_mem ha
      | simpa using hb
      | simpa using hR.toRootAxioms.neg_mem hb

theorem rank_two_classification : RankTwoSpecs.classificationType := by
  intro E _ _ R hR hd
  have hex : ∃ k : RankTwoKind, RankTwoModel R k := by
    by_cases h₃ : HasCartanProduct R 3
    · refine ⟨.G₂, rank_two_model_of_max hR hd 3 (by simp) h₃ ?_⟩
      intro a ha b hb hli
      norm_num only [Nat.cast_ofNat, Nat.cast_one] at ⊢
      rcases cartan_product_values hR.toRootAxioms ha hb hli with h | h | h | h <;> linarith
    by_cases h₂ : HasCartanProduct R 2
    · refine ⟨.B₂, rank_two_model_of_max hR hd 2 (by simp) h₂ ?_⟩
      intro a ha b hb hli
      norm_num only [Nat.cast_ofNat, Nat.cast_one] at ⊢
      rcases cartan_product_values hR.toRootAxioms ha hb hli with h | h | h | h
      all_goals first
        | linarith
        | exact False.elim (h₃ ⟨a,ha,b,hb,hli,by simpa using h⟩)
    by_cases h₁ : HasCartanProduct R 1
    · refine ⟨.A₂, rank_two_model_of_max hR hd 1 (by simp) h₁ ?_⟩
      intro a ha b hb hli
      norm_num only [Nat.cast_ofNat, Nat.cast_one] at ⊢
      rcases cartan_product_values hR.toRootAxioms ha hb hli with h | h | h | h
      all_goals first
        | linarith
        | exact False.elim (h₂ ⟨a,ha,b,hb,hli,by simpa using h⟩)
        | exact False.elim (h₃ ⟨a,ha,b,hb,hli,by simpa using h⟩)
    · refine ⟨.A₁A₁, rank_two_orthogonal_model hR hd ?_⟩
      intro a ha b hb hli
      norm_num only [Nat.cast_ofNat, Nat.cast_one] at ⊢
      rcases cartan_product_values hR.toRootAxioms ha hb hli with h | h | h | h
      · exact h
      · exact False.elim (h₁ ⟨a,ha,b,hb,hli,by simpa using h⟩)
      · exact False.elim (h₂ ⟨a,ha,b,hb,hli,by simpa using h⟩)
      · exact False.elim (h₃ ⟨a,ha,b,hb,hli,by simpa using h⟩)
  obtain ⟨k,hk⟩ := hex
  refine ⟨k,hk,?_⟩
  intro l hl
  have he := (rank_two_root_count R l hl).symm.trans (rank_two_root_count R k hk)
  cases k <;> cases l <;> (try norm_num [rankTwoCount] at he) <;> rfl

private lemma rank_two_gram_scales {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (k : RankTwoKind) {a b : E} {u v : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (hg : rankTwoGram k a b) (hg' : rankTwoGram k u v) :
    (k ≠ .A₁A₁ → inner ℝ u u / inner ℝ a a = inner ℝ v v / inner ℝ b b) ∧
    inner ℝ u v = (inner ℝ u u / inner ℝ a a) * inner ℝ a b := by
  have hA := inner_self_ne_zero ha
  have hB := inner_self_ne_zero hb
  have hscale := div_mul_cancel₀ (inner ℝ u u) hA
  cases k
  case A₁A₁ =>
    change inner ℝ a b = 0 at hg
    change inner ℝ u v = 0 at hg'
    exact ⟨fun h => (h rfl).elim, by rw [hg,hg',mul_zero]⟩
  all_goals
    rcases hg with ⟨hbb,hab⟩
    rcases hg' with ⟨hvv,huv⟩
    constructor
    · intro _
      rw [hbb,hvv] <;> field_simp <;> ring
    · have he := congrArg (fun x : ℝ => (inner ℝ u u / inner ℝ a a) * x) hab
      rw [hbb] at he
      rw [hvv] at huv
      nlinarith only [he,huv,hscale]

theorem rank_two_metric_equivalence : RankTwoSpecs.metricEquivalenceType := by
  intro E F _ _ _ _ R S k hR hS
  obtain ⟨a,ha,b,hb,hli,hs,hg,hroots⟩ := hR
  obtain ⟨u,hu,v,hv,hli',hs',hg',hroots'⟩ := hS
  let B : Module.Basis (Fin 2) ℝ E := Module.Basis.mk hli (by simpa only [Matrix.range_cons_cons_empty] using hs.ge)
  let C : Module.Basis (Fin 2) ℝ F := Module.Basis.mk hli' (by simpa only [Matrix.range_cons_cons_empty] using hs'.ge)
  let f : E ≃ₗ[ℝ] F := B.equiv C (Equiv.refl (Fin 2))
  have hfa : f a = u := by
    have he := B.equiv_apply 0 C (Equiv.refl (Fin 2))
    simpa [B,C] using he
  have hfb : f b = v := by
    have he := B.equiv_apply 1 C (Equiv.refl (Fin 2))
    simpa [B,C] using he
  have hma : a ≠ 0 := hli.ne_zero 0
  have hmb : b ≠ 0 := hli.ne_zero 1
  have hmu : u ≠ 0 := hli'.ne_zero 0
  have hmv : v ≠ 0 := hli'.ne_zero 1
  have himage : f '' R = S := by
    rw [hroots,hroots']
    change f '' ((fun p : ℤ × ℤ => p.1 • a + p.2 • b) '' _) =
      (fun p : ℤ × ℤ => p.1 • u + p.2 • v) '' _
    rw [Set.image_image]
    congr 1
    funext p
    simp [hfa,hfb]
  obtain ⟨hscales,hcross⟩ := rank_two_gram_scales k hma hmb hg hg'
  refine ⟨f,a,b,inner ℝ u u / inner ℝ a a,inner ℝ v v / inner ℝ b b,
    ha,hb,hli,hs,hg,himage,
    div_pos (real_inner_self_pos.mpr hmu) (real_inner_self_pos.mpr hma),
    div_pos (real_inner_self_pos.mpr hmv) (real_inner_self_pos.mpr hmb),hscales,?_,?_,?_⟩
  · rw [hfa,div_mul_cancel₀ _ (inner_self_ne_zero hma)]
  · rw [hfb,div_mul_cancel₀ _ (inner_self_ne_zero hmb)]
  · rw [hfa,hfb]
    exact hcross

end LieAlgebrasAndRepresentations
