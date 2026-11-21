import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.DyadicHolderExtension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.WLOG

universe u

open Set Filter
open scoped Topology NNReal ENNReal
namespace ProbabilityFoundations.Ch05.Dyadic

lemma mesh_pos {T : ℝ} (hT : 0 < T) (n : ℕ) : 0 < mesh T n :=
  div_pos hT (pow_pos (by norm_num) _)

lemma mesh_add (T : ℝ) (n k : ℕ) : mesh T (n + k) = mesh T n / (2 : ℝ) ^ k := by
  simp [mesh, pow_add, div_div]

lemma mesh_succ (T : ℝ) (n : ℕ) : mesh T (n + 1) = mesh T n / 2 := by
  simpa using mesh_add T n 1

lemma mesh_rpow_add {T : ℝ} (hT : 0 < T) (γ : ℝ) (n k : ℕ) :
    mesh T (n + k) ^ γ = mesh T n ^ γ * ((2 : ℝ) ^ (-γ)) ^ k := by
  rw [mesh_add, Real.div_rpow (le_of_lt (mesh_pos hT n)) (by positivity),
    ← Real.rpow_pow_comm (by norm_num), Real.rpow_neg (by norm_num), inv_pow, div_eq_mul_inv]

/-- A sequence of coherent finite grids admits a finite chaining bound.
Only the grid values are used; no ambient continuity is assumed. -/
lemma finite_chaining {S : Type*} [MetricSpace S] {T γ A : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A)
    (u : ℕ → ℕ → S)
    (hcoh : ∀ n j, j ≤ 2 ^ n → u (n + 1) (2 * j) = u n j)
    (hadj : ∀ n j, j < 2 ^ n → dist (u n j) (u n (j + 1)) ≤ A * mesh T n ^ γ)
    (n k i j : ℕ) (hi : i ≤ 2 ^ (n + k)) (hj : j ≤ 2 ^ (n + k))
    (hij : i ≤ j) (hclose : j ≤ i + 2 ^ k) :
    dist (u (n + k) i) (u (n + k) j) ≤
      A * mesh T n ^ γ * (1 + 2 * ∑ l ∈ Finset.range k, ((2 : ℝ) ^ (-γ)) ^ (l + 1)) := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty,
      mul_zero, add_zero, mul_one] at *
    by_cases he : i = j
    · subst j
      simpa using mul_nonneg hA (Real.rpow_nonneg (mesh_pos hT n).le γ)
    · have he : j = i + 1 := by omega
      subst j
      exact hadj n i (by omega)
  | succ k ih =>
    have hp : 2 ^ (n + (k + 1)) = 2 * 2 ^ (n + k) := by
      rw [show n + (k + 1) = (n + k) + 1 by omega, pow_succ, Nat.mul_comm]
    have hi' : i / 2 ≤ 2 ^ (n + k) := by omega
    have hj' : j / 2 ≤ 2 ^ (n + k) := by omega
    have hc : j / 2 ≤ i / 2 + 2 ^ k := by
      rw [pow_succ] at hclose
      omega
    have hbase := ih (i / 2) (j / 2) hi' hj' (by omega) hc
    have hedge (a : ℕ) (ha : a ≤ 2 ^ (n + (k + 1))) :
        dist (u (n + (k + 1)) a) (u (n + k) (a / 2)) ≤
          A * mesh T (n + (k + 1)) ^ γ := by
      rw [← hcoh (n + k) (a / 2) (by omega)]
      have hrem := Nat.mod_lt a (by norm_num : 0 < 2)
      have hdiv := Nat.mod_add_div a 2
      by_cases he : a = 2 * (a / 2)
      · have heq : u (n + (k + 1)) a = u (n + (k + 1)) (2 * (a / 2)) :=
          congrArg _ he
        rw [show n + (k + 1) = n + k + 1 by omega] at heq ⊢
        rw [heq, dist_self]
        exact mul_nonneg hA (Real.rpow_nonneg (mesh_pos hT _).le γ)
      · have he' : a = 2 * (a / 2) + 1 := by omega
        have hb := hadj (n + k + 1) (2 * (a / 2)) (by omega)
        rw [← he'] at hb
        simpa only [show n + (k + 1) = n + k + 1 by omega, dist_comm] using hb
    calc
      dist (u (n + (k + 1)) i) (u (n + (k + 1)) j) ≤
          dist (u (n + (k + 1)) i) (u (n + k) (i / 2)) +
          dist (u (n + k) (i / 2)) (u (n + k) (j / 2)) +
          dist (u (n + k) (j / 2)) (u (n + (k + 1)) j) :=
        dist_triangle4 _ _ _ _
      _ ≤ A * mesh T (n + (k + 1)) ^ γ +
          A * mesh T n ^ γ *
            (1 + 2 * ∑ l ∈ Finset.range k, ((2 : ℝ) ^ (-γ)) ^ (l + 1)) +
          A * mesh T (n + (k + 1)) ^ γ := by
        exact add_le_add (add_le_add (hedge i hi) hbase)
          (by simpa only [dist_comm] using hedge j hj)
      _ = _ := by
        rw [Finset.sum_range_succ, mesh_rpow_add hT γ n (k + 1)]
        ring


lemma geometric_tail_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    (∑ l ∈ Finset.range k, r ^ (l + 1)) ≤ r / (1 - r) := by
  have hs : (∑ l ∈ Finset.range k, r ^ l) ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr hr1]
    exact (summable_geometric_of_lt_one hr hr1).sum_le_tsum _ (fun _ _ => pow_nonneg hr _)
  calc
    (∑ l ∈ Finset.range k, r ^ (l + 1)) = r * ∑ l ∈ Finset.range k, r ^ l := by
      simp only [pow_succ', Finset.mul_sum]
    _ ≤ r * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hs hr
    _ = _ := (div_eq_mul_inv _ _).symm

lemma domain_subset {T : ℝ} (hT : 0 ≤ T) : domain T ⊆ Icc 0 T := by
  rintro x ⟨n, j, hj, rfl⟩
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hT hp.le)
  · calc
      (j : ℝ) * mesh T n ≤ (2 : ℝ) ^ n * mesh T n := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hT hp.le)
        exact_mod_cast hj
      _ = T := by dsimp [mesh]; field_simp

lemma refine_grid (T : ℝ) (n k j : ℕ) :
    ((j * 2 ^ k : ℕ) : ℝ) * mesh T (n + k) = (j : ℝ) * mesh T n := by
  rw [mesh_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

lemma domain_at_level {T : ℝ} {x : ℝ} (hx : x ∈ domain T) :
    ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∃ j : ℕ, j ≤ 2 ^ N ∧ x = (j : ℝ) * mesh T N := by
  obtain ⟨n, j, hj, rfl⟩ := hx
  refine ⟨n, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨j * 2 ^ k, ?_, (refine_grid T n k j).symm⟩
  rw [pow_add]
  exact Nat.mul_le_mul_right _ hj

/-- Bound for an ambient function, using only its values on the grids. -/
lemma ambient_chaining {S : Type*} [MetricSpace S] {T γ A : ℝ}
    (hT : 0 < T) (hγ : 0 < γ) (hA : 0 ≤ A) (g : ℝ → S)
    (hadj : ∀ (n j : ℕ), j < 2 ^ n →
      dist (g ((j : ℝ) * mesh T n)) (g ((j + 1 : ℕ) * mesh T n)) ≤ A * mesh T n ^ γ)
    {x y : ℝ} (hx : x ∈ domain T) (hy : y ∈ domain T) :
    dist (g x) (g y) ≤
      ((2 : ℝ) ^ γ * A * (1 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)))) *
        dist x y ^ γ := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-γ) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hB : 0 ≤ 1 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) := by positivity
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this hy hx (le_of_not_ge hxy)
  by_cases he : x = y
  · subst y
    simp [Real.zero_rpow hγ.ne']
  have hδ : 0 < y - x := sub_pos.mpr (lt_of_le_of_ne hxy he)
  have hδT : y - x ≤ T := by
    have hxI := domain_subset hT.le hx
    have hyI := domain_subset hT.le hy
    linarith [hxI.1, hyI.2]
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hδ hT) ((div_le_one hT).mpr hδT)
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hscale (m : ℕ) : (1 / 2 : ℝ) ^ m * T = mesh T m := by
    simp [mesh, div_eq_mul_inv, mul_comm]
  have hlo : mesh T (n + 1) < y - x := by
    simpa only [hscale] using (lt_div_iff₀ hT).mp hnlo
  have hhi : y - x ≤ mesh T n := by
    simpa only [hscale] using (div_le_iff₀ hT).mp hnhi
  have hmesh : mesh T n ≤ 2 * (y - x) := by
    rw [mesh_succ] at hlo
    linarith
  obtain ⟨nx, hnx⟩ := domain_at_level hx
  obtain ⟨ny, hny⟩ := domain_at_level hy
  obtain ⟨i, hi, hxi⟩ := hnx (n + (nx + ny)) (by omega)
  obtain ⟨j, hj, hyj⟩ := hny (n + (nx + ny)) (by omega)
  have hm := mesh_pos hT (n + (nx + ny))
  have hij : i ≤ j := by
    have he : (i : ℝ) ≤ (j : ℝ) := (mul_le_mul_iff_left₀ hm).mp (by
      simpa only [← hxi, ← hyj] using hxy)
    exact_mod_cast he
  have hclose : j ≤ i + 2 ^ (nx + ny) := by
    have hmul : (2 : ℝ) ^ (nx + ny) * mesh T (n + (nx + ny)) = mesh T n := by
      rw [mesh_add]; field_simp
    have hb : (j : ℝ) ≤ (i : ℝ) + (2 : ℝ) ^ (nx + ny) := by
      apply (mul_le_mul_iff_left₀ hm).mp
      rw [add_mul, hmul]
      linarith [hhi]
    exact_mod_cast hb
  have hc := finite_chaining hT hA (fun m a => g ((a : ℝ) * mesh T m))
    (fun m a _ => by
      congr 1
      rw [mesh_succ, Nat.cast_mul, Nat.cast_ofNat]
      ring)
    hadj n (nx + ny) i j hi hj hij hclose
  rw [← hxi, ← hyj] at hc
  have hsum := geometric_tail_bound hr0 hr1 (nx + ny)
  have hc' : dist (g x) (g y) ≤ A * mesh T n ^ γ *
      (1 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) := by
    apply hc.trans
    have hn : 0 ≤ A * mesh T n ^ γ :=
      mul_nonneg hA (Real.rpow_nonneg (mesh_pos hT n).le γ)
    apply mul_le_mul_of_nonneg_left _ hn
    simpa only [mul_div_assoc] using
      add_le_add_right (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)) 1
  have hp : mesh T n ^ γ ≤ (2 : ℝ) ^ γ * (y - x) ^ γ := by
    rw [← Real.mul_rpow (by norm_num) hδ.le]
    exact Real.rpow_le_rpow (mesh_pos hT n).le hmesh hγ.le
  calc
    dist (g x) (g y) ≤ A * mesh T n ^ γ *
        (1 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) := hc'
    _ ≤ A * ((2 : ℝ) ^ γ * (y - x) ^ γ) *
        (1 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ))) := by gcongr
    _ = _ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : x - y ≤ 0)]
      simp only [neg_sub]
      ring


/-- The finite real constant in the source's chaining calculation. -/
noncomputable def chainingConstant (γ A : ℝ) : ℝ :=
  (2 : ℝ) ^ γ * A * (1 + 2 * (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)))

lemma chainingConstant_nonneg {γ A : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A) :
    0 ≤ chainingConstant γ A := by
  have : (2 : ℝ) ^ (-γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold chainingConstant
  positivity

/-- Chaining on the actual subtype of dyadic times. -/
theorem dyadic_bound {S : Type*} [MetricSpace S] (T : ℝ) (hT : 0 < T)
    (γ A : ℝ) (hγ : 0 < γ) (hA : 0 ≤ A) (f : domain T → S)
    (hf : AdjacentBound T γ A f) : Bound γ (chainingConstant γ A) f := by
  classical
  let z : domain T := point T 0 0 (by norm_num)
  let g : ℝ → S := fun x => if hx : x ∈ domain T then f ⟨x, hx⟩ else f z
  have hg (x : domain T) : g x = f x := by simp [g, x.property]
  have hadj (n j : ℕ) (hj : j < 2 ^ n) :
      dist (g ((j : ℝ) * mesh T n)) (g ((j + 1 : ℕ) * mesh T n)) ≤ A * mesh T n ^ γ := by
    have hb := hf n j hj
    rw [← hg (point T n j hj.le), ← hg (point T n (j + 1) hj)] at hb
    exact hb
  intro x y
  have hh := ambient_chaining hT hγ hA g hadj x.property y.property
  simpa only [hg, chainingConstant, Subtype.dist_eq] using hh

/-- The canonical inclusion into the compact time interval. -/
def inclusion {T : ℝ} (hT : 0 < T) : domain T → Icc (0 : ℝ) T :=
  fun x => ⟨x, domain_subset hT.le x.property⟩

lemma inclusion_isometry {T : ℝ} (hT : 0 < T) : Isometry (inclusion hT) :=
  fun _ _ => rfl

lemma inclusion_dense {T : ℝ} (hT : 0 < T) : DenseRange (inclusion hT) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hT)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hsmall : mesh T n < ε := by
    have hs : (1 / 2 : ℝ) ^ n * T = mesh T n := by
      simp [mesh, div_eq_mul_inv, mul_comm]
    simpa only [hs] using (lt_div_iff₀ hT).mp hn
  have hm := mesh_pos hT n
  let j := ⌊(x : ℝ) / mesh T n⌋₊
  have hx0 : 0 ≤ (x : ℝ) / mesh T n := div_nonneg x.property.1 hm.le
  have hj : j ≤ 2 ^ n := by
    apply Nat.floor_le_of_le
    apply (div_le_iff₀ hm).mpr
    have he : (2 : ℝ) ^ n * mesh T n = T := by dsimp [mesh]; field_simp
    simpa only [Nat.cast_pow, Nat.cast_ofNat, he] using x.property.2
  refine ⟨point T n j hj, ?_⟩
  have hlow : (j : ℝ) * mesh T n ≤ x :=
    (le_div_iff₀ hm).mp (Nat.floor_le hx0)
  have hupp : (x : ℝ) < ((j : ℝ) + 1) * mesh T n :=
    (div_lt_iff₀ hm).mp (Nat.lt_floor_add_one ((x : ℝ) / mesh T n))
  change dist (x : ℝ) ((j : ℝ) * mesh T n) < ε
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

lemma bound_holder {X S : Type*} [MetricSpace X] [MetricSpace S]
    {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K) {f : X → S} (hf : Bound γ K f) :
    HolderWith (NNReal.mk K hK) (NNReal.mk γ hγ) f := by
  intro x y
  change edist (f x) (f y) ≤ ((NNReal.mk K hK : ℝ≥0) : ℝ≥0∞) * edist x y ^ γ
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ hγ, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
  exact_mod_cast hf x y

/-- Extension of a bound already established on the dyadics; the constant is unchanged. -/
theorem extension_of_bound {S : Type*} [MetricSpace S] [CompleteSpace S]
    {T γ K : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hK : 0 ≤ K)
    (f : domain T → S) (hf : Bound γ K f) :
    ∃ F : Icc (0 : ℝ) T → S, Continuous F ∧
      (∀ x, F (inclusion hT x) = f x) ∧ Bound γ K F ∧
      ∀ G : Icc (0 : ℝ) T → S, Continuous G →
        (∀ x, G (inclusion hT x) = f x) → G = F := by
  let hi := (inclusion_isometry hT).isUniformInducing
  let hd := inclusion_dense hT
  let he := hi.isDenseInducing hd
  have hu : UniformContinuous f := (bound_holder hγ.le hK hf).uniformContinuous hγ
  let F := he.extend f
  have hF : UniformContinuous F := uniformContinuous_uniformly_extend hi hd hu
  have hEq : ∀ x, F (inclusion hT x) = f x := uniformly_extend_of_ind hi hd hu
  refine ⟨F, hF.continuous, hEq, ?_, ?_⟩
  · intro x y
    refine hd.induction_on₂
      (p := fun a b => dist (F a) (F b) ≤ K * dist a b ^ γ) ?_ ?_ x y
    · exact isClosed_le
        ((hF.continuous.comp continuous_fst).dist (hF.continuous.comp continuous_snd))
        (continuous_const.mul ((continuous_fst.dist continuous_snd).rpow_const
          (fun _ => Or.inr hγ.le)))
    · intro a b
      simpa only [hEq, (inclusion_isometry hT).dist_eq a b] using hf a b
  · intro G hG hGeq
    exact (uniformly_extend_unique hi hd hGeq hG).symm

/-- The assigned finite-bound conclusion. -/
theorem chaining : Specs.ProbabilityFoundations.Ch05.DyadicHolderExtension.chaining.{u} := by
  intro S _ T hT γ A hγ hA f hf
  exact ⟨chainingConstant γ A, chainingConstant_nonneg hγ hA,
    dyadic_bound T hT γ A hγ hA f hf⟩

/-- The assigned unique-extension conclusion. -/
theorem extension : Specs.ProbabilityFoundations.Ch05.DyadicHolderExtension.extension.{u} := by
  intro S _ _ T hT γ A hγ hA f hf
  have hK := chainingConstant_nonneg hγ hA
  have hb := dyadic_bound T hT γ A hγ hA f hf
  obtain ⟨F, hF, hEq, hbound, huniq⟩ := extension_of_bound hT hγ hK f hb
  refine ⟨chainingConstant γ A, F, hK, hb, hF, ?_, hbound, ?_⟩
  · intro x hx
    exact hEq x
  · intro G hG hGeq
    exact huniq G hG (fun x => hGeq x (domain_subset hT.le x.property))

end ProbabilityFoundations.Ch05.Dyadic
