import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleTriangulation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleModel
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Intervals

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix
namespace P202.ShuffleTriangulation
open P202Specs.ShuffleModel P202Specs.ShuffleTriangulation

lemma tail_single {n : ℕ} (a : Fin (n+1)) (i : ℕ) :
    (∑ j : Fin (n+1) with i < j.val,
      weights (Convexity.StdSimplex.single a) j) = if i < a.val then 1 else 0 := by
  simp [weights, Convexity.StdSimplex.weights_single, Finsupp.single_apply,
    Finset.mem_filter]

lemma vertex_coordinates {p q : ℕ} (s : LatticePath p q)
    (k : Fin (p+q+1)) (i : Fin (p+q)) :
    productCoordinates p q (vertex s k) i =
      if i.val < p then (if i.val < (s.horizontal k).val then 1 else 0)
      else (if i.val-p < (s.vertical k).val then 1 else 0) := by
  simp only [productCoordinates, vertex]
  split <;> apply tail_single

lemma step_coordinate {p q : ℕ} (s : LatticePath p q)
    (l : Fin (p+q)) (k : Fin (p+q+1)) :
    productCoordinates p q (vertex s k) (s.stepLabel l) =
      if l.val < k.val then 1 else 0 := by
  rw [vertex_coordinates]
  rcases s.step l with h | h
  · have hb : (s.horizontal l.castSucc).val < p := by
      have := (s.horizontal l.succ).isLt
      omega
    simp only [LatticePath.stepLabel, h.1, ↓reduceDIte, Fin.val_mk, hb, ↓reduceIte]
    by_cases hl : l.val < k.val
    · have he : l.succ ≤ k := by change l.val+1 ≤ k.val; omega
      have hm := s.horizontal.monotone he
      simp only [Fin.le_def] at hm
      simp [hl, show (s.horizontal l.castSucc).val < (s.horizontal k).val by omega]
    · have he : k ≤ l.castSucc := by change k.val ≤ l.val; omega
      have hm := s.horizontal.monotone he
      simp only [Fin.le_def] at hm
      simp [hl, show ¬ (s.horizontal l.castSucc).val < (s.horizontal k).val by omega]
  · have hn : ¬ (s.horizontal l.succ).val = (s.horizontal l.castSucc).val+1 := by
      rw [h.1]
      omega
    have hb : ¬ p + (s.vertical l.castSucc).val < p := by omega
    simp only [LatticePath.stepLabel, hn, ↓reduceDIte, Fin.val_mk, hb, ↓reduceIte,
      Nat.add_sub_cancel_left]
    by_cases hl : l.val < k.val
    · have he : l.succ ≤ k := by change l.val+1 ≤ k.val; omega
      have hm := s.vertical.monotone he
      simp only [Fin.le_def] at hm
      simp [hl, show (s.vertical l.castSucc).val < (s.vertical k).val by omega]
    · have he : k ≤ l.castSucc := by change k.val ≤ l.val; omega
      have hm := s.vertical.monotone he
      simp only [Fin.le_def] at hm
      simp [hl, show ¬ (s.vertical l.castSucc).val < (s.vertical k).val by omega]

lemma orientationMatrix_permute {p q : ℕ} (s : LatticePath p q) :
    (orientationMatrix s).submatrix s.permutation id =
      fun i j : Fin (p+q) => if i ≤ j then 1 else 0 := by
  ext i j
  change productCoordinates p q (vertex s j.succ) (s.stepLabel i) -
    productCoordinates p q (vertex s 0) (s.stepLabel i) = _
  rw [step_coordinate, step_coordinate]
  simp only [Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, sub_zero, Fin.val_succ]
  congr 1
  change (i.val < j.val+1) = (i.val ≤ j.val)
  exact propext (by omega)

lemma orientation {p q : ℕ} (s : LatticePath p q) :
    Matrix.det (orientationMatrix s) = (s.sign : ℝ) := by
  have hd : Matrix.det ((orientationMatrix s).submatrix s.permutation id) = 1 := by
    rw [orientationMatrix_permute]
    rw [Matrix.det_of_isUpperTriangular]
    · simp
    · intro i j h
      change j < i at h
      exact ite_eq_right (not_le.mpr h)
  rw [Matrix.det_permute] at hd
  have hs : ((Equiv.Perm.sign s.permutation : ℤˣ) : ℝ) *
      ((Equiv.Perm.sign s.permutation : ℤˣ) : ℝ) = 1 := by
    exact_mod_cast (Int.isUnit_mul_self (Equiv.Perm.sign s.permutation).isUnit)
  change Matrix.det (orientationMatrix s) = ((Equiv.Perm.sign s.permutation : ℤˣ) : ℝ)
  calc
    Matrix.det (orientationMatrix s) = 1 * Matrix.det (orientationMatrix s) := by ring
    _ = (((Equiv.Perm.sign s.permutation : ℤˣ) : ℝ) *
        ((Equiv.Perm.sign s.permutation : ℤˣ) : ℝ)) * Matrix.det (orientationMatrix s) := by rw [hs]
    _ = ((Equiv.Perm.sign s.permutation : ℤˣ) : ℝ) *
        (((Equiv.Perm.sign s.permutation : ℤˣ) : ℝ) * Matrix.det (orientationMatrix s)) := by ring
    _ = ((Equiv.Perm.sign s.permutation : ℤˣ) : ℝ) := by rw [hd, mul_one]

lemma tail_edge {n : ℕ} (a : Fin (n+1)) (i : ℕ) :
    (∑ k : Fin (n+1) with i < k.val,
      ((if k.val = a.val then (1 : ℝ) else 0) - (if k.val = 0 then 1 else 0))) =
      if i < a.val then 1 else 0 := by
  have he (k : Fin (n+1)) :
      ((if k.val = a.val then (1 : ℝ) else 0) - (if k.val = 0 then 1 else 0)) =
      weights (Convexity.StdSimplex.single a) k -
        weights (Convexity.StdSimplex.single (0 : Fin (n+1))) k := by
    simp only [weights, Convexity.StdSimplex.weights_single, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero]
    simp only [eq_comm]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, tail_single, tail_single]
  simp

lemma standard_basis_coordinates (p q : ℕ) (i j : Fin (p+q)) :
    productCoordinates p q (standardProductVector p q j) i =
      if j.val < p then
        (if i.val < p then (if i ≤ j then 1 else 0) else 0)
      else (if i.val < p then 0 else (if i ≤ j then 1 else 0)) := by
  unfold standardProductVector productCoordinates
  by_cases hj : j.val < p
  · simp only [hj, ↓reduceIte]
    by_cases hi : i.val < p
    · simp only [hi, ↓reduceIte]
      rw [tail_edge (⟨j.val+1, by omega⟩ : Fin (p+1))]
      have he : i.val < j.val+1 ↔ i ≤ j := by
        change i.val < j.val+1 ↔ i.val ≤ j.val
        omega
      simp only [he]
    · simp [hi]
  · simp only [hj, ↓reduceIte]
    by_cases hi : i.val < p
    · simp [hi]
    · simp only [hi, ↓reduceIte]
      rw [tail_edge (⟨j.val-p+1, by have := j.isLt; omega⟩ : Fin (q+1))]
      have he : i.val-p < j.val-p+1 ↔ i ≤ j := by
        change i.val-p < j.val-p+1 ↔ i.val ≤ j.val
        omega
      simp only [he]

lemma standard_basis_orientation (p q : ℕ) :
    Matrix.det (fun i j : Fin (p+q) =>
      productCoordinates p q (standardProductVector p q j) i) = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    rw [standard_basis_coordinates]
    split <;> simp_all
  · intro i j hij
    change productCoordinates p q (standardProductVector p q j) i = 0
    rw [standard_basis_coordinates]
    change j < i at hij
    have h : ¬ i ≤ j := not_le.mpr hij
    simp [h]

/-- Barycentric pushforward carries a tail to the corresponding fiber tail. -/
lemma tail_map {m n : ℕ} (f : Fin (m+1) → Fin (n+1))
    (z : StdSimplex m) (i : ℕ) :
    (∑ j : Fin (n+1) with i < j.val, weights (z.map f) j) =
      ∑ k : Fin (m+1), if i < (f k).val then weights z k else 0 := by
  rw [← P202.ShuffleModel.ambientMap_weights f z]
  simp only [ambientMap, Finset.sum_filter]
  have distrib (j : Fin (n+1)) :
      (if i < j.val then ∑ k : Fin (m+1), if f k = j then weights z k else 0 else 0) =
      ∑ k : Fin (m+1), if i < j.val then (if f k = j then weights z k else 0) else 0 := by
    split <;> simp_all
  simp_rw [distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (f k)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

lemma coordinates_barycentric {p q : ℕ} (s : LatticePath p q)
    (z : StdSimplex (p+q)) (i : Fin (p+q)) :
    productCoordinates p q
      (weights (parametrization s z).1, weights (parametrization s z).2) i =
      ∑ k : Fin (p+q+1), weights z k * productCoordinates p q (vertex s k) i := by
  simp only [productCoordinates, parametrization, ContinuousMap.coe_mk]
  split <;> rw [tail_map] <;> apply Finset.sum_congr rfl <;> intro k _
  all_goals simp only [vertex, tail_single]; split <;> simp

lemma coordinates_tail {p q : ℕ} (s : LatticePath p q)
    (z : StdSimplex (p+q)) (i : Fin (p+q)) :
    productCoordinates p q
      (weights (parametrization s z).1, weights (parametrization s z).2)
      (s.stepLabel i) = ∑ k : Fin (p+q+1) with i.val < k.val, weights z k := by
  rw [coordinates_barycentric]
  simp_rw [step_coordinate]
  simp [Finset.sum_filter, mul_ite]

lemma weights_eq_of_tails_eq {n : ℕ} (x y : StdSimplex n)
    (h : ∀ i : Fin n,
      (∑ k : Fin (n+1) with i.val < k.val, weights x k) =
      ∑ k : Fin (n+1) with i.val < k.val, weights y k) : x = y := by
  have tail_eq (i : ℕ) :
      (∑ k : Fin (n+1) with i < k.val, weights x k) =
      ∑ k : Fin (n+1) with i < k.val, weights y k := by
    by_cases hi : i < n
    · exact h ⟨i, hi⟩
    · have he : (Finset.univ.filter (fun k : Fin (n+1) => i < k.val)) = ∅ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        have := k.isLt
        omega
      simp only [he, Finset.sum_empty]
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro k
  by_cases hk : k.val = 0
  · have hx := x.total_of_fintype
    have hy := y.total_of_fintype
    have split_sum (z : StdSimplex n) :
        (∑ j : Fin (n+1), z.weights j) = z.weights k +
          ∑ j : Fin (n+1) with 0 < j.val, z.weights j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      have he : Finset.univ.erase k =
          Finset.univ.filter (fun j : Fin (n+1) => 0 < j.val) := by
        ext j
        simp only [Finset.mem_erase, Finset.mem_univ, and_true,
          Finset.mem_filter, true_and]
        omega
      rw [he, add_comm]
    rw [split_sum x] at hx
    rw [split_sum y] at hy
    have ht := tail_eq 0
    change weights x k = weights y k
    change x.weights k + _ = 1 at hx
    change y.weights k + _ = 1 at hy
    dsimp [weights] at ht
    dsimp [weights]
    linarith
  · have split_tail (z : StdSimplex n) :
        (∑ j : Fin (n+1) with k.val-1 < j.val, weights z j) =
          weights z k + ∑ j : Fin (n+1) with k.val < j.val, weights z j := by
      have he : Finset.univ.filter (fun j : Fin (n+1) => k.val-1 < j.val) =
          insert k (Finset.univ.filter (fun j : Fin (n+1) => k.val < j.val)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]
        omega
      rw [he, Finset.sum_insert (by simp)]
    have ht := tail_eq (k.val-1)
    rw [split_tail x, split_tail y, tail_eq k.val] at ht
    exact add_right_cancel ht

lemma injectivity {p q : ℕ} (s : LatticePath p q) :
    Function.Injective (parametrization s) := by
  intro x y h
  apply weights_eq_of_tails_eq
  intro i
  rw [← coordinates_tail s x i, ← coordinates_tail s y i, h]

def simplexTail {n : ℕ} (z : StdSimplex n) (i : Fin n) : ℝ :=
  ∑ k : Fin (n+1) with i.val < k.val, weights z k

lemma simplexTail_antitone {n : ℕ} (z : StdSimplex n) : Antitone (simplexTail z) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_of_le_of_lt hij hk
  · intro k _ _
    exact z.weights_nonneg k

/-- Even for two different paths, a point has the same ordered barycentric
weights. This is uniqueness of the sorted list of its product tail coordinates. -/
lemma same_barycentric_coordinates {p q : ℕ} (s t : LatticePath p q)
    (x y : StdSimplex (p+q)) (h : parametrization s x = parametrization t y) : x = y := by
  let c := productCoordinates p q
    (weights (parametrization s x).1, weights (parametrization s x).2)
  have hs : c ∘ s.permutation = simplexTail x := by
    funext i
    exact coordinates_tail s x i
  have ht : c ∘ t.permutation = simplexTail y := by
    funext i
    dsimp [c, Function.comp_def]
    rw [h]
    exact coordinates_tail t y i
  have he := Tuple.unique_antitone (hs.symm ▸ simplexTail_antitone x)
    (ht.symm ▸ simplexTail_antitone y)
  rw [hs, ht] at he
  exact weights_eq_of_tails_eq x y (congrFun he)

lemma simplexTail_strict {n : ℕ} (z : StdSimplex n) (k : Fin (n+1))
    (hk : 0 < weights z k) (i j : Fin n) (hi : i.val < k.val) (hj : k.val ≤ j.val) :
    simplexTail z j < simplexTail z i := by
  let a := Finset.univ.filter (fun l : Fin (n+1) => i.val < l.val)
  let b := Finset.univ.filter (fun l : Fin (n+1) => j.val < l.val)
  have hab : b ⊆ a := by
    intro l hl
    simp only [b, a, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    omega
  have hkm : k ∈ a \ b := by
    simp [a, b, hi, not_lt.mpr hj]
  have hbound := Finset.single_le_sum (s := a \ b) (f := weights z)
    (fun l _ => z.weights_nonneg l) hkm
  have he := Finset.sum_sdiff (f := weights z) hab
  change (∑ l ∈ b, weights z l) < ∑ l ∈ a, weights z l
  linarith

lemma productCoordinates_injective {p q : ℕ}
    (x y : StdSimplex p × StdSimplex q)
    (h : productCoordinates p q (weights x.1, weights x.2) =
      productCoordinates p q (weights y.1, weights y.2)) : x = y := by
  apply Prod.ext
  · apply weights_eq_of_tails_eq
    intro i
    have he := congrFun h (i.castAdd q)
    simpa [productCoordinates, i.isLt] using he
  · apply weights_eq_of_tails_eq
    intro i
    have he := congrFun h (i.natAdd p)
    simpa [productCoordinates, Nat.not_lt.mpr (Nat.le_add_right p i.val)] using he

lemma positive_weight_vertex_eq {p q : ℕ} (s t : LatticePath p q)
    (x : StdSimplex (p+q)) (h : parametrization s x = parametrization t x)
    (k : Fin (p+q+1)) (hk : 0 < weights x k) : vertex s k = vertex t k := by
  have htail (l : Fin (p+q)) :
      simplexTail x (s.permutation.symm l) = simplexTail x (t.permutation.symm l) := by
    rw [simplexTail, simplexTail, ← coordinates_tail s x _, ← coordinates_tail t x _, h]
    change productCoordinates p q
      (weights (parametrization t x).1, weights (parametrization t x).2)
      (s.permutation (s.permutation.symm l)) =
      productCoordinates p q
      (weights (parametrization t x).1, weights (parametrization t x).2)
      (t.permutation (t.permutation.symm l))
    simp only [Equiv.apply_symm_apply]
  have hprefix (l : Fin (p+q)) :
      (s.permutation.symm l).val < k.val ↔ (t.permutation.symm l).val < k.val := by
    constructor
    · intro hs
      by_contra ht
      have hlt := simplexTail_strict x k hk (s.permutation.symm l)
        (t.permutation.symm l) hs (by omega)
      rw [htail l] at hlt
      exact lt_irrefl _ hlt
    · intro ht
      by_contra hs
      have hlt := simplexTail_strict x k hk (t.permutation.symm l)
        (s.permutation.symm l) ht (by omega)
      rw [htail l] at hlt
      exact lt_irrefl _ hlt
  have hv : (Convexity.StdSimplex.single (R := ℝ) (s.horizontal k),
      Convexity.StdSimplex.single (R := ℝ) (s.vertical k)) =
      (Convexity.StdSimplex.single (R := ℝ) (t.horizontal k),
        Convexity.StdSimplex.single (R := ℝ) (t.vertical k)) := by
    apply productCoordinates_injective
    funext l
    change productCoordinates p q (vertex s k) l = productCoordinates p q (vertex t k) l
    conv_lhs => rw [← s.permutation.apply_symm_apply l]
    conv_rhs => rw [← t.permutation.apply_symm_apply l]
    rw [show s.permutation = s.stepLabel from rfl,
      show t.permutation = t.stepLabel from rfl, step_coordinate, step_coordinate]
    simp only [hprefix]
  exact congrArg (fun z : StdSimplex p × StdSimplex q => (weights z.1, weights z.2)) hv

lemma ambient_barycentric {p q : ℕ} (s : LatticePath p q) (z : StdSimplex (p+q)) :
    (weights (parametrization s z).1, weights (parametrization s z).2) =
      ∑ k : Fin (p+q+1), weights z k • vertex s k := by
  ext j <;> simp [weights, parametrization, vertex, Finsupp.mapDomain_fintype,
    Finsupp.single_apply, Finset.sum_apply, mul_ite, Prod.fst_sum, Prod.snd_sum]

lemma cell_convex {p q : ℕ} (s : LatticePath p q) : Convex ℝ (cell s) := by
  have he : (fun z : StdSimplex (p+q) =>
      (weights (parametrization s z).1, weights (parametrization s z).2)) =
      Convexity.StdSimplex.affineMapMk (vertex s) := by
    funext z
    rw [Convexity.StdSimplex.affineMapMk_apply, Convexity.iConvexComb_eq_sum,
      Finsupp.sum_fintype _ _ (by simp)]
    exact ambient_barycentric s z
  unfold cell
  rw [he]
  exact Convexity.ConvexSpace.AffineMap.convex_range _

lemma vertex_mem_cell {p q : ℕ} (s : LatticePath p q) (k : Fin (p+q+1)) :
    vertex s k ∈ cell s := by
  refine ⟨Convexity.StdSimplex.single k, ?_⟩
  change (weights (parametrization s (Convexity.StdSimplex.single k)).1,
    weights (parametrization s (Convexity.StdSimplex.single k)).2) = vertex s k
  rw [P202.ShuffleModel.parametrization_vertex]
  rfl

lemma common_face {p q : ℕ} (s t : LatticePath p q) :
    cell s ∩ cell t = convexHull ℝ (commonVertices s t) := by
  apply Set.Subset.antisymm
  · rintro a ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy : parametrization s x = parametrization t y := by
      apply Prod.ext <;> apply Convexity.StdSimplex.ext
      · exact Finsupp.ext (congrFun (congrArg Prod.fst (hx.trans hy.symm)))
      · exact Finsupp.ext (congrFun (congrArg Prod.snd (hx.trans hy.symm)))
    have he := same_barycentric_coordinates s t x y hxy
    subst y
    rw [← hx]
    change (weights (parametrization s x).1, weights (parametrization s x).2) ∈ _
    rw [ambient_barycentric]
    have hsum : (∑ k ∈ x.weights.support, weights x k) = 1 := x.total
    have hs : (∑ k ∈ x.weights.support, weights x k • vertex s k) =
        ∑ k : Fin (p+q+1), weights x k • vertex s k := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp only [Finsupp.mem_support_iff, not_not] at hk
      simp [weights, hk]
    rw [← hs]
    apply (convex_convexHull ℝ (commonVertices s t)).sum_mem
      (fun k _ => x.weights_nonneg k) hsum
    intro k hk
    apply subset_convexHull
    refine ⟨⟨k, rfl⟩, ⟨k, ?_⟩⟩
    have hpos : 0 < weights x k := lt_of_le_of_ne (x.weights_nonneg k)
      (Ne.symm (Finsupp.mem_support_iff.mp hk))
    exact (positive_weight_vertex_eq s t x hxy k hpos).symm
  · apply convexHull_min
    · rintro a ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
      exact ⟨vertex_mem_cell s i, hj ▸ vertex_mem_cell t j⟩
    · exact (cell_convex s).inter (cell_convex t)

/-- Counting already traversed labels turns any ordering of the reference
steps into the underlying monotone lattice path. -/
def pathOfPermutation {p q : ℕ} (e : Equiv.Perm (Fin (p+q))) : LatticePath p q :=
  ⟨(⟨fun k => ⟨(Finset.univ.filter (fun h : Fin p =>
        (e.symm (h.castAdd q)).val < k.val)).card,
        by have := Finset.card_filter_le Finset.univ (fun h : Fin p =>
            (e.symm (h.castAdd q)).val < k.val)
           simp only [Finset.card_fin] at this
           omega⟩,
      by
        intro k l hkl
        change (Finset.univ.filter (fun h : Fin p =>
          (e.symm (h.castAdd q)).val < k.val)).card ≤
          (Finset.univ.filter (fun h : Fin p => (e.symm (h.castAdd q)).val < l.val)).card
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact lt_of_lt_of_le ha hkl⟩,
    ⟨fun k => ⟨(Finset.univ.filter (fun v : Fin q =>
        (e.symm (v.natAdd p)).val < k.val)).card,
        by have := Finset.card_filter_le Finset.univ (fun v : Fin q =>
            (e.symm (v.natAdd p)).val < k.val)
           simp only [Finset.card_fin] at this
           omega⟩,
      by
        intro k l hkl
        change (Finset.univ.filter (fun v : Fin q =>
          (e.symm (v.natAdd p)).val < k.val)).card ≤
          (Finset.univ.filter (fun v : Fin q => (e.symm (v.natAdd p)).val < l.val)).card
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact lt_of_lt_of_le ha hkl⟩), by
    intro k
    change (Finset.univ.filter (fun h : Fin p =>
      (e.symm (h.castAdd q)).val < k.val)).card +
      (Finset.univ.filter (fun v : Fin q =>
      (e.symm (v.natAdd p)).val < k.val)).card = k.val
    rw [Finset.card_filter, Finset.card_filter]
    rw [← Fin.sum_univ_add (fun l => if (e.symm l).val < k.val then (1 : ℕ) else 0)]
    rw [e.symm.sum_comp (fun l => if l.val < k.val then (1 : ℕ) else 0)]
    rw [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right (by have := k.isLt; omega)]
    simp⟩

lemma pathOfPermutation_coordinates {p q : ℕ} (e : Equiv.Perm (Fin (p+q)))
    (hh : Monotone (fun h : Fin p => e.symm (h.castAdd q)))
    (hv : Monotone (fun v : Fin q => e.symm (v.natAdd p)))
    (k : Fin (p+q+1)) (i : Fin (p+q)) :
    productCoordinates p q (vertex (pathOfPermutation e) k) i =
      if (e.symm i).val < k.val then 1 else 0 := by
  rw [vertex_coordinates]
  by_cases hi : i.val < p
  · let a : Fin p := ⟨i.val, hi⟩
    have hea : a.castAdd q = i := Fin.ext rfl
    have he := Fin.lt_card_filter_univ_iff_apply_of_imp
      (j := a) (fun h : Fin p => (e.symm (h.castAdd q)).val < k.val)
      (fun h h' hle hlt => lt_of_le_of_lt (hh hle) hlt)
    simp only [hi, ↓reduceIte]
    change (if a.val < _ then (1 : ℝ) else 0) = _
    change (if a.val < (Finset.univ.filter (fun h : Fin p =>
      (e.symm (h.castAdd q)).val < k.val)).card then (1 : ℝ) else 0) = _
    simp only [he, hea]
  · let a : Fin q := ⟨i.val-p, by have := i.isLt; omega⟩
    have hea : a.natAdd p = i := Fin.ext (by simp [a]; omega)
    have he := Fin.lt_card_filter_univ_iff_apply_of_imp
      (j := a) (fun v : Fin q => (e.symm (v.natAdd p)).val < k.val)
      (fun v v' hle hlt => lt_of_le_of_lt (hv hle) hlt)
    simp only [hi, ↓reduceIte]
    change (if a.val < _ then (1 : ℝ) else 0) = _
    change (if a.val < (Finset.univ.filter (fun v : Fin q =>
      (e.symm (v.natAdd p)).val < k.val)).card then (1 : ℝ) else 0) = _
    simp only [he, hea]

lemma stableSort_inverse_mono {n : ℕ} (c : Fin n → ℝ) {a b : Fin n}
    (hab : a ≤ b) (hc : c b ≤ c a) :
    (Tuple.sort (fun i => OrderDual.toDual (c i))).symm a ≤
      (Tuple.sort (fun i => OrderDual.toDual (c i))).symm b := by
  let f := fun i => OrderDual.toDual (c i)
  let e := Tuple.sort f
  change e.symm a ≤ e.symm b
  by_contra h
  have hlt : e.symm b < e.symm a := lt_of_not_ge h
  have hm := Tuple.monotone_sort f hlt.le
  have hm' : c a ≤ c b := by simpa [e, f, Function.comp_def] using hm
  have hstable := (Tuple.eq_sort_iff.mp (show e = Tuple.sort f from rfl)).2
    (e.symm b) (e.symm a) hlt
  have heq : f (e (e.symm b)) = f (e (e.symm a)) := by
    simp only [Equiv.apply_symm_apply]
    change c b = c a
    exact le_antisymm hc hm'
  have hba : b < a := by simpa only [Equiv.apply_symm_apply] using hstable heq
  exact (not_lt_of_ge hab) hba

/-- Gaps in any decreasing list in the unit interval are simplex weights. -/
lemma exists_simplex_of_antitone {n : ℕ} (r : Fin n → ℝ) (hr : Antitone r)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) :
    ∃ z : StdSimplex n, simplexTail z = r := by
  let f : ℕ → ℝ := fun k => match k with
    | 0 => 1
    | j+1 => if hj : j < n then r ⟨j, hj⟩ else 0
  have hf0 : f 0 = 1 := rfl
  have hfn : f (n+1) = 0 := by simp [f]
  have hfr (i : Fin n) : f (i.val+1) = r i := by simp [f, i.isLt]
  have hm (k : ℕ) : f (k+1) ≤ f k := by
    cases k with
    | zero =>
      by_cases hn : 0 < n
      · simpa [f, hn] using hr1 ⟨0, hn⟩
      · simp [f, hn]
    | succ k =>
      by_cases hk : k+1 < n
      · have hk' : k < n := by omega
        simpa [f, hk, hk'] using hr (show (⟨k, hk'⟩ : Fin n) ≤ ⟨k+1, hk⟩ by change k ≤ k+1; omega)
      · by_cases hk' : k < n
        · simpa [f, hk, hk'] using hr0 ⟨k, hk'⟩
        · simp [f, hk, hk']
  let z : StdSimplex n := {
    weights := Finsupp.onFinset Finset.univ (fun k : Fin (n+1) => f k.val - f (k.val+1)) (by simp)
    nonneg := fun k => sub_nonneg.mpr (hm k.val)
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change (∑ k : Fin (n+1), (f k.val - f (k.val+1))) = 1
      rw [Fin.sum_univ_eq_sum_range (fun k => f k-f (k+1)),
        Finset.sum_range_sub', hf0, hfn]
      norm_num }
  refine ⟨z, ?_⟩
  funext i
  change (∑ k : Fin (n+1) with i.val < k.val, (f k.val-f (k.val+1))) = r i
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range
    (fun k => if i.val < k then f k-f (k+1) else 0), ← Finset.sum_filter]
  have he : (Finset.range (n+1)).filter (fun k => i.val < k) =
      Finset.Ico (i.val+1) (n+1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sub _ (by have := i.isLt; omega),
    Finset.sum_range_sub', Finset.sum_range_sub', hfn, hfr]
  ring

lemma simplexTail_nonneg {n : ℕ} (z : StdSimplex n) (i : Fin n) :
    0 ≤ simplexTail z i := Finset.sum_nonneg (fun k _ => z.weights_nonneg k)

lemma simplexTail_le_one {n : ℕ} (z : StdSimplex n) (i : Fin n) :
    simplexTail z i ≤ 1 := by
  rw [← z.total_of_fintype]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => z.weights_nonneg k)

/-- Stable merging of the two factor tails constructs a path even when some
coordinates agree or a factor has dimension zero. -/
lemma coverage (p q : ℕ) (z : StdSimplex p × StdSimplex q) :
    ∃ (s : LatticePath p q) (x : StdSimplex (p+q)), parametrization s x = z := by
  let c := productCoordinates p q (weights z.1, weights z.2)
  have ch (a : Fin p) : c (a.castAdd q) = simplexTail z.1 a := by
    simp [c, productCoordinates]
    rfl
  have cv (a : Fin q) : c (a.natAdd p) = simplexTail z.2 a := by
    simp [c, productCoordinates, Nat.not_lt.mpr (Nat.le_add_right p a.val)]
    rfl
  have hc (i : Fin (p+q)) : 0 ≤ c i ∧ c i ≤ 1 := by
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [ch]
      exact ⟨simplexTail_nonneg z.1 a, simplexTail_le_one z.1 a⟩
    · rw [cv]
      exact ⟨simplexTail_nonneg z.2 a, simplexTail_le_one z.2 a⟩
  let e := Tuple.sort (fun i => OrderDual.toDual (c i))
  have hh : Monotone (fun a : Fin p => e.symm (a.castAdd q)) := by
    intro a b hab
    apply stableSort_inverse_mono c
    · exact hab
    · rw [ch, ch]
      exact simplexTail_antitone z.1 hab
  have hv : Monotone (fun a : Fin q => e.symm (a.natAdd p)) := by
    intro a b hab
    apply stableSort_inverse_mono c
    · change p+a.val ≤ p+b.val
      exact Nat.add_le_add_left hab p
    · rw [cv, cv]
      exact simplexTail_antitone z.2 hab
  let r := c ∘ e
  have hr : Antitone r := Tuple.monotone_sort (fun i => OrderDual.toDual (c i))
  obtain ⟨x, hx⟩ := exists_simplex_of_antitone r hr
    (fun i => (hc (e i)).1) (fun i => (hc (e i)).2)
  refine ⟨pathOfPermutation e, x, ?_⟩
  apply productCoordinates_injective
  funext i
  rw [coordinates_barycentric]
  simp_rw [pathOfPermutation_coordinates e hh hv]
  have he : (∑ k : Fin (p+q+1), weights x k *
      (if (e.symm i).val < k.val then (1 : ℝ) else 0)) = simplexTail x (e.symm i) := by
    simp [simplexTail, Finset.sum_filter, mul_ite]
  rw [he, congrFun hx]
  simp only [r, Function.comp_apply, Equiv.apply_symm_apply]
  rfl

/-- The full geometric triangulation, with exact common faces. -/
lemma triangulation (p q : ℕ) :
    (∀ s : LatticePath p q, Function.Injective (parametrization s)) ∧
    (∀ z : StdSimplex p × StdSimplex q,
      ∃ (s : LatticePath p q) (x : StdSimplex (p+q)), parametrization s x = z) ∧
    (∀ s t : LatticePath p q,
      cell s ∩ cell t = convexHull ℝ (commonVertices s t)) :=
  ⟨injectivity, coverage p q, common_face⟩

/-- The tail coordinate map is the determinant-one change from the standard
ordered product edge coordinates, on the entire ambient vector space. -/
lemma productCoordinates_change (p q : ℕ) (a : Ambient p × Ambient q) :
    productCoordinates p q a =
      (Matrix.of fun i j : Fin (p+q) => productCoordinates p q (standardProductVector p q j) i) *ᵥ
        standardProductCoordinates p q a := by
  funext i
  change productCoordinates p q a i = ∑ j : Fin (p+q),
    productCoordinates p q (standardProductVector p q j) i *
      standardProductCoordinates p q a j
  rw [Fin.sum_univ_add]
  simp_rw [standard_basis_coordinates]
  by_cases hi : i.val < p
  · simp [hi, standardProductCoordinates,
      Nat.not_lt.mpr (Nat.le_add_right p _), Fin.le_def, ite_mul]
    simp only [productCoordinates, hi, ↓reduceIte, Finset.sum_filter, Fin.sum_univ_succ,
      Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, zero_add, Fin.val_succ]
    apply Finset.sum_congr rfl
    intro j _
    have hiff : i.val < j.val+1 ↔ i.val ≤ j.val := by omega
    simp only [hiff]
    rfl
  · simp [hi, standardProductCoordinates,
      Nat.not_lt.mpr (Nat.le_add_right p _), Fin.le_def, ite_mul]
    simp only [productCoordinates, hi, ↓reduceIte, Finset.sum_filter, Fin.sum_univ_succ,
      Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, zero_add, Fin.val_succ]
    apply Finset.sum_congr rfl
    intro j _
    have hiff : i.val-p < j.val+1 ↔ i.val ≤ p+j.val := by omega
    simp only [hiff]
    rfl

lemma orientationMatrix_change_of_coordinates {p q : ℕ} (s : LatticePath p q) :
    orientationMatrix s =
      (Matrix.of fun i j : Fin (p+q) => productCoordinates p q (standardProductVector p q j) i) *
        standardOrientationMatrix s := by
  ext i j
  change productCoordinates p q (vertex s j.succ) i -
    productCoordinates p q (vertex s 0) i = _
  rw [productCoordinates_change p q (vertex s j.succ),
    productCoordinates_change p q (vertex s 0)]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, standardOrientationMatrix]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Determinant with columns measured in the standard product orientation. -/
lemma standard_orientation {p q : ℕ} (s : LatticePath p q) :
    Matrix.det (standardOrientationMatrix s) = (s.sign : ℝ) := by
  have h := orientation s
  rw [orientationMatrix_change_of_coordinates, Matrix.det_mul] at h
  change Matrix.det (fun i j : Fin (p+q) =>
    productCoordinates p q (standardProductVector p q j) i) *
      Matrix.det (standardOrientationMatrix s) = (s.sign : ℝ) at h
  rw [standard_basis_orientation, one_mul] at h
  exact h

end P202.ShuffleTriangulation
