import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalCoordinateRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Mathlib.Data.Finset.Prod
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module

noncomputable section
namespace LieAlgebrasAndRepresentations.ClassicalCoordinates
open Set Module
open scoped Classical

@[simp] lemma epsilon_apply {n : ℕ} (i j : Fin n) :
    epsilon i j = if i = j then 1 else 0 := by
  simp [epsilon, PiLp.single_apply, eq_comm]

@[simp] lemma sum_epsilon {n : ℕ} (i : Fin n) : ∑ j, epsilon i j = 1 := by
  simp [epsilon_apply]

lemma epsilon_injective (n : ℕ) : Function.Injective (@epsilon n) := by
  intro i j h
  by_contra hij
  have := congrArg (fun x : Space n => x i) h
  simp [epsilon_apply, Ne.symm hij] at this

/-- Coordinate differences as actual vectors of the sum-zero hyperplane. -/
def difference (n : ℕ) (p : Fin (n + 1) × Fin (n + 1)) : zeroSum n :=
  ⟨epsilon p.1 - epsilon p.2, by
    change ∑ j, (epsilon p.1 - epsilon p.2) j = 0
    simp [PiLp.sub_apply, Finset.sum_sub_distrib]⟩

lemma difference_injOn (n : ℕ) :
    Set.InjOn (difference n) {p | p.1 ≠ p.2} := by
  rintro ⟨i, j⟩ hij ⟨k, l⟩ hkl h
  change i ≠ j at hij
  have hval : epsilon i - epsilon j = epsilon k - epsilon l :=
    congrArg Subtype.val h
  have hi := congrArg (fun x : Space (n + 1) => x i) hval
  have hki : k = i := by
    by_contra hki
    by_cases hli : l = i <;>
      norm_num [PiLp.sub_apply, epsilon_apply, Ne.symm hij, hki, hli] at hi
  subst k
  have hjl : j = l := epsilon_injective _ (sub_right_injective hval)
  subst l
  rfl

lemma rootsA_image (n : ℕ) :
    rootsA n = difference n '' {p | p.1 ≠ p.2} := by
  ext x
  constructor
  · rintro ⟨i, j, hij, hx⟩
    exact ⟨(i,j), hij, Subtype.ext hx.symm⟩
  · rintro ⟨⟨i,j⟩, hij, rfl⟩
    exact ⟨i,j,hij,rfl⟩

lemma rootsA_finite (n : ℕ) : (rootsA n).Finite := by
  rw [rootsA_image]
  exact (Set.toFinite _).image _

lemma pairRoots_finite (n : ℕ) : (pairRoots n).Finite := by
  let f : (Fin n × Fin n) × (Bool × Bool) → Space n := fun p =>
    sign p.2.1 • epsilon p.1.1 + sign p.2.2 • epsilon p.1.2
  apply (Set.finite_range f).subset
  rintro x ⟨i, j, _, s, t, rfl⟩
  exact ⟨((i,j),(s,t)), rfl⟩

lemma axisRoots_finite (n : ℕ) (c : ℝ) : (axisRoots n c).Finite := by
  let f : Fin n × Bool → Space n := fun p => (c * sign p.2) • epsilon p.1
  apply (Set.finite_range f).subset
  rintro x ⟨i, s, rfl⟩
  exact ⟨(i,s), rfl⟩

lemma rootsB_finite (n : ℕ) : (rootsB n).Finite :=
  (axisRoots_finite n 1).union (pairRoots_finite n)

lemma rootsC_finite (n : ℕ) : (rootsC n).Finite :=
  (axisRoots_finite n 2).union (pairRoots_finite n)

lemma rootsD_finite (n : ℕ) : (rootsD n).Finite := pairRoots_finite n

/-- The counting parametrization is injective precisely away from the diagonal. -/
lemma rootsA_ncard (n : ℕ) : (rootsA n).ncard = n * (n + 1) := by
  rw [rootsA_image, (difference_injOn n).ncard_image]
  have hset : {p : Fin (n + 1) × Fin (n + 1) | p.1 ≠ p.2} =
      ((Finset.univ : Finset (Fin (n + 1))).offDiag : Set _) := by
    ext p
    simp
  rw [hset, Set.ncard_coe_finset, Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem countA : Specs.countAType := by
  intro n _
  exact rootsA_ncard n

@[simp] lemma inner_epsilon_left {n : ℕ} (i : Fin n) (x : Space n) :
    inner ℝ (epsilon i) x = x i := by
  simp [epsilon, EuclideanSpace.inner_single_left]

@[simp] lemma inner_epsilon_right {n : ℕ} (i : Fin n) (x : Space n) :
    inner ℝ x (epsilon i) = x i := by
  simp [epsilon, EuclideanSpace.inner_single_right]

lemma inner_difference_right {n : ℕ} (x : Space n) (i j : Fin n) :
    inner ℝ x (epsilon i - epsilon j) = x i - x j := by
  simp [inner_sub_right]

lemma difference_norm {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    inner ℝ (epsilon i - epsilon j) (epsilon i - epsilon j) = 2 := by
  rw [inner_difference_right]
  norm_num [PiLp.sub_apply, epsilon_apply, hij, Ne.symm hij]

lemma reflection_coordinate {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    rootReflection (epsilon i - epsilon j) (epsilon k) =
      epsilon (Equiv.swap i j k) := by
  rw [rootReflection, inner_difference_right, difference_norm hij]
  by_cases hki : k = i
  · subst k
    simp [epsilon_apply, hij]
  · by_cases hkj : k = j
    · subst k
      simp [epsilon_apply, Ne.symm hij]
    · simp [epsilon_apply, hki, hkj, Equiv.swap_apply_def]

lemma reflection_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : rootReflection a (b - c) = rootReflection a b - rootReflection a c := by
  simp only [rootReflection, inner_sub_left, mul_sub, sub_div, sub_smul]
  module

lemma reflection_difference {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j)
    (k l : Fin (n + 1)) :
    rootReflection (difference n (i,j)) (difference n (k,l)) =
      difference n (Equiv.swap i j k, Equiv.swap i j l) := by
  apply Subtype.ext
  change rootReflection (epsilon i - epsilon j) (epsilon k - epsilon l) = _
  rw [reflection_sub, reflection_coordinate hij k, reflection_coordinate hij l]
  rfl

lemma rootsA_inner_self {n : ℕ} {a : zeroSum n} (ha : a ∈ rootsA n) :
    inner ℝ a a = 2 := by
  rcases ha with ⟨i,j,hij,hval⟩
  rw [Submodule.coe_inner, hval]
  exact difference_norm hij

lemma rootsA_nonzero {n : ℕ} {a : zeroSum n} (ha : a ∈ rootsA n) : a ≠ 0 := by
  intro h
  have := rootsA_inner_self ha
  norm_num [h] at this

lemma rootsA_reflection_mem {n : ℕ} {a b : zeroSum n}
    (ha : a ∈ rootsA n) (hb : b ∈ rootsA n) : rootReflection a b ∈ rootsA n := by
  rcases ha with ⟨i,j,hij,hval⟩
  rcases hb with ⟨k,l,hkl,hval'⟩
  have ha : a = difference n (i,j) := Subtype.ext hval
  have hb : b = difference n (k,l) := Subtype.ext hval'
  rw [ha, hb, reflection_difference hij]
  exact ⟨_, _, (Equiv.swap i j).injective.ne hkl, rfl⟩

lemma rootsA_integral {n : ℕ} {a b : zeroSum n}
    (ha : a ∈ rootsA n) (hb : b ∈ rootsA n) :
    ∃ z : ℤ, 2 * inner ℝ b a / inner ℝ a a = (z : ℝ) := by
  rw [rootsA_inner_self ha]
  rcases ha with ⟨i,j,_,hval⟩
  rcases hb with ⟨k,l,_,hval'⟩
  rw [Submodule.coe_inner, hval, hval', inner_difference_right]
  simp only [PiLp.sub_apply, epsilon_apply]
  refine ⟨(if k = i then 1 else 0) - (if l = i then 1 else 0) -
    ((if k = j then 1 else 0) - (if l = j then 1 else 0)), ?_⟩
  push_cast
  split_ifs <;> norm_num

lemma rootsA_reduced {n : ℕ} {a b : zeroSum n}
    (ha : a ∈ rootsA n) (hb : b ∈ rootsA n)
    (hba : b ∈ Submodule.span ℝ ({a} : Set (zeroSum n))) : b = a ∨ b = -a := by
  rcases Submodule.mem_span_singleton.mp hba with ⟨t, rfl⟩
  have ht := rootsA_inner_self hb
  rw [real_inner_smul_left, real_inner_smul_right, rootsA_inner_self ha] at ht
  have ht' : t ^ 2 = 1 := by nlinarith
  rcases sq_eq_one_iff.mp ht' with rfl | rfl <;> simp

lemma rootsA_span (n : ℕ) : Submodule.span ℝ (rootsA n) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hmem : ∀ i : Fin (n + 1), difference n (i, 0) ∈ Submodule.span ℝ (rootsA n) := by
    intro i
    by_cases hi : i = 0
    · subst i
      have hz : difference n (0,0) = 0 := by apply Subtype.ext; simp [difference]
      rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨i,0,hi,rfl⟩
  have hsum : ∑ i : Fin (n + 1), (x : Space (n + 1)) i • difference n (i,0) = x := by
    apply Subtype.ext
    apply PiLp.ext
    intro k
    simp only [Submodule.coe_sum, Submodule.coe_smul, difference]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, epsilon_apply]
    simp [show ∑ i, (x : Space (n + 1)) i = 0 from x.property]
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)

theorem rootSystemA : Specs.rootSystemAType := by
  intro n _
  exact {
    finite := rootsA_finite n
    nonzero := fun _ ha => rootsA_nonzero ha
    reflection_mem := fun _ ha _ hb => rootsA_reflection_mem ha hb
    integral := fun _ ha _ hb => rootsA_integral ha hb
    reduced := fun _ ha _ hb hba => rootsA_reduced ha hb hba
    span_eq_top := rootsA_span n }

/-- A decreasing coordinate vector, centered to lie in the A hyperplane. -/
def regularA (n : ℕ) : zeroSum n :=
  ⟨WithLp.toLp 2 (fun i : Fin (n + 1) =>
    (∑ j : Fin (n + 1), (j.val : ℝ)) - (n + 1 : ℝ) * i.val), by
    change ∑ i : Fin (n + 1),
      ((∑ j : Fin (n + 1), (j.val : ℝ)) - (n + 1 : ℝ) * i.val) = 0
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp⟩

lemma regularA_inner_difference (n : ℕ) (i j : Fin (n + 1)) :
    inner ℝ (regularA n) (difference n (i,j)) =
      (n + 1 : ℝ) * ((j.val : ℝ) - i.val) := by
  rw [Submodule.coe_inner]
  change inner ℝ (regularA n).val (epsilon i - epsilon j) = _
  rw [inner_difference_right]
  dsimp [regularA]
  ring

lemma regularA_positive_iff (n : ℕ) (i j : Fin (n + 1)) :
    0 < inner ℝ (regularA n) (difference n (i,j)) ↔ i < j := by
  rw [regularA_inner_difference, mul_pos_iff_of_pos_left (by positivity : 0 < (n + 1 : ℝ)),
    sub_pos]
  exact_mod_cast Iff.rfl

lemma regularA_regular (n : ℕ) : RootRegular (rootsA n) (regularA n) := by
  rintro a ⟨i,j,hij,ha⟩
  have ha : a = difference n (i,j) := Subtype.ext ha
  rw [ha, regularA_inner_difference]
  apply mul_ne_zero (by positivity)
  exact sub_ne_zero.mpr (by exact_mod_cast (Fin.val_ne_of_ne (Ne.symm hij)))

lemma positiveRootsA_iff {n : ℕ} (a : zeroSum n) :
    a ∈ positiveRoots (rootsA n) (regularA n) ↔
      ∃ i j : Fin (n + 1), i < j ∧ a = difference n (i,j) := by
  constructor
  · rintro ⟨⟨i,j,hij,ha⟩,hpos⟩
    have ha : a = difference n (i,j) := Subtype.ext ha
    exact ⟨i,j, (regularA_positive_iff n i j).mp (ha ▸ hpos), ha⟩
  · rintro ⟨i,j,hij,rfl⟩
    exact ⟨⟨i,j,ne_of_lt hij,rfl⟩,(regularA_positive_iff n i j).mpr hij⟩

lemma simpleA_inner (n : ℕ) (i : Fin n) :
    inner ℝ (regularA n) (simpleA n i) = n + 1 := by
  change inner ℝ (regularA n) (difference n (i.castSucc,i.succ)) = _
  rw [regularA_inner_difference]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

lemma positiveRootsA_height {n : ℕ} {a : zeroSum n}
    (ha : a ∈ positiveRoots (rootsA n) (regularA n)) :
    (n + 1 : ℝ) ≤ inner ℝ (regularA n) a := by
  rcases (positiveRootsA_iff a).mp ha with ⟨i,j,hij,rfl⟩
  rw [regularA_inner_difference]
  have h : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show i.val + 1 ≤ j.val by omega)
  nlinarith [show (0 : ℝ) ≤ n by positivity]

lemma simpleA_mem_simpleRoots (n : ℕ) (i : Fin n) :
    simpleA n i ∈ simpleRoots (rootsA n) (regularA n) := by
  refine ⟨(positiveRootsA_iff _).mpr ⟨i.castSucc,i.succ,by simp,rfl⟩, ?_⟩
  intro b hb c hc heq
  have hb := positiveRootsA_height hb
  have hc := positiveRootsA_height hc
  have hi := simpleA_inner n i
  rw [heq, inner_add_right] at hi
  linarith [show (0 : ℝ) ≤ n by positivity]

lemma simpleRootsA_eq_range (n : ℕ) :
    simpleRoots (rootsA n) (regularA n) = Set.range (simpleA n) := by
  ext a
  constructor
  · intro ha
    rcases (positiveRootsA_iff a).mp ha.1 with ⟨i,j,hij,hval⟩
    have hin : i.val < n := by have := j.isLt; omega
    let k : Fin n := ⟨i.val, hin⟩
    by_cases hadj : j.val = i.val + 1
    · refine ⟨k, ?_⟩
      rw [hval]
      have hi : k.castSucc = i := Fin.ext rfl
      have hj : k.succ = j := Fin.ext hadj.symm
      change difference n (k.castSucc,k.succ) = difference n (i,j)
      rw [hi,hj]
    · let m : Fin (n + 1) := ⟨i.val + 1, by omega⟩
      have him : i < m := by change i.val < i.val + 1; omega
      have hmj : m < j := by change i.val + 1 < j.val; omega
      have hpos₁ := (positiveRootsA_iff _).mpr ⟨i,m,him,rfl⟩
      have hpos₂ := (positiveRootsA_iff _).mpr ⟨m,j,hmj,rfl⟩
      exfalso
      apply ha.2 _ hpos₁ _ hpos₂
      rw [hval]
      apply Subtype.ext
      change epsilon i - epsilon j = (epsilon i - epsilon m) + (epsilon m - epsilon j)
      module
  · rintro ⟨i,rfl⟩
    exact simpleA_mem_simpleRoots n i

lemma simpleA_injective (n : ℕ) : Function.Injective (simpleA n) := by
  intro i j h
  have hi : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
  have hj : j.castSucc ≠ j.succ := by simp [Fin.ext_iff]
  have hp : (i.castSucc,i.succ) = (j.castSucc,j.succ) :=
    difference_injOn n hi hj (show difference n (i.castSucc,i.succ) =
      difference n (j.castSucc,j.succ) from h)
  exact Fin.ext (congrArg (fun p : Fin (n+1) × Fin (n+1) => p.1.val) hp)

lemma simpleA_basis (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : Basis (Fin n) ℝ (zeroSum n),
      (∀ i, b i = simpleA n i) ∧ IsSimpleBasis (rootsA n) (regularA n) b := by
  obtain ⟨c,hc⟩ := simpleRoots_basis (rootsA n) (rootSystemA n hn) (regularA n) (regularA_regular n)
  let f : Fin n → simpleRoots (rootsA n) (regularA n) :=
    fun i => ⟨simpleA n i, simpleA_mem_simpleRoots n i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact simpleA_injective n (congrArg Subtype.val h)
    · intro a
      have hma : a.val ∈ Set.range (simpleA n) := by
        rw [← simpleRootsA_eq_range]
        exact a.property
      obtain ⟨i,hi⟩ := hma
      exact ⟨i,Subtype.ext hi⟩
  let e := Equiv.ofBijective f hf
  refine ⟨c.reindex e.symm, ?_, ?_⟩
  · intro i
    simpa only [Basis.reindex_apply, Equiv.symm_symm, e, Equiv.ofBijective_apply, f] using hc (e i)
  · change Set.range (c.reindex e.symm) = _
    have hfun : (fun i => (c.reindex e.symm) i) = simpleA n := by
      funext i
      simpa only [Basis.reindex_apply, Equiv.symm_symm, e, Equiv.ofBijective_apply, f] using hc (e i)
    exact (congrArg Set.range hfun).trans (simpleRootsA_eq_range n).symm

lemma simpleA_gram {n : ℕ} (i j : Fin n) :
    inner ℝ (simpleA n i) (simpleA n j) =
      if i = j then 2 else if adjacent i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact rootsA_inner_self (simpleA_mem_simpleRoots n i).1.1
  · have hv : i.val ≠ j.val := Fin.val_ne_of_ne hij
    have hv' : i.val + 1 ≠ j.val + 1 := by omega
    rw [ite_eq_right hij]
    rw [Submodule.coe_inner]
    change inner ℝ (epsilon i.castSucc - epsilon i.succ)
      (epsilon j.castSucc - epsilon j.succ) = _
    rw [inner_sub_left, inner_difference_right, inner_difference_right]
    simp only [epsilon_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    unfold adjacent
    split_ifs <;> norm_num <;> omega

lemma simpleA_cartan {n : ℕ} (i j : Fin n) :
    cartanMatrix (simpleA n) i j =
      if i = j then 2 else if adjacent i j then -1 else 0 := by
  unfold cartanMatrix rootCartan
  rw [real_inner_comm, simpleA_gram]
  rw [rootsA_inner_self (simpleA_mem_simpleRoots n i).1.1]
  ring_nf

lemma simpleA_diagram_edges {n : ℕ} (i j : Fin n) :
    (dynkinDiagram (simpleA n)).edges i j = if adjacent i j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [dynkinDiagram, adjacent]
  · have hji : j ≠ i := Ne.symm hij
    have hadj : adjacent j i ↔ adjacent i j := by unfold adjacent; omega
    simp only [dynkinDiagram, ite_eq_right hij, simpleA_cartan, ite_eq_right hji]
    by_cases ha : adjacent i j
    · rw [ite_eq_left ha, ite_eq_left (hadj.mpr ha), ite_eq_left ha]
      norm_num
    · rw [ite_eq_right ha, ite_eq_right (not_congr hadj |>.mpr ha), ite_eq_right ha]
      norm_num

lemma simpleA_diagram_no_arrows {n : ℕ} (i j : Fin n) :
    ¬ (dynkinDiagram (simpleA n)).arrow i j := by
  change ¬ (i ≠ j ∧ inner ℝ (simpleA n i) (simpleA n j) ≠ 0 ∧
    inner ℝ (simpleA n j) (simpleA n j) < inner ℝ (simpleA n i) (simpleA n i))
  rw [rootsA_inner_self (simpleA_mem_simpleRoots n i).1.1,
    rootsA_inner_self (simpleA_mem_simpleRoots n j).1.1]
  simp

theorem simpleDiagramA : Specs.simpleDiagramAType := by
  intro n hn
  obtain ⟨b,hb,hsimple⟩ := simpleA_basis n hn
  have hbfun : (b : Fin n → zeroSum n) = simpleA n := funext hb
  refine ⟨regularA n,b,hb,regularA_regular n,hsimple,?_,?_⟩
  · rw [hbfun]
    exact simpleA_diagram_edges
  · rw [hbfun]
    exact simpleA_diagram_no_arrows

/-! Shared signed-coordinate calculations for B, C and D. -/

@[simp] lemma sign_ne_zero (s : Bool) : sign s ≠ 0 := by cases s <;> norm_num [sign]
@[simp] lemma sign_sq (s : Bool) : sign s * sign s = 1 := by cases s <;> norm_num [sign]

lemma sign_injective : Function.Injective sign := by
  intro s t h
  cases s <;> cases t <;> norm_num [sign] at *

lemma sign_mul (s t : Bool) : sign s * sign t = sign (s.xor t) := by
  cases s <;> cases t <;> norm_num [sign]

lemma sign_neg (s : Bool) : -sign s = sign (!s) := by
  cases s <;> norm_num [sign]

lemma pair_inner_self {n : ℕ} {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    inner ℝ (sign s • epsilon i + sign t • epsilon j)
      (sign s • epsilon i + sign t • epsilon j) = 2 := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_epsilon_left, epsilon_apply, ite_eq_left rfl, ite_eq_right hij, ite_eq_right (Ne.symm hij)]
  cases s <;> cases t <;> norm_num [sign]

lemma pairRoots_inner_self {n : ℕ} {a : Space n} (ha : a ∈ pairRoots n) :
    inner ℝ a a = 2 := by
  rcases ha with ⟨i,j,hij,s,t,rfl⟩
  exact pair_inner_self hij s t

lemma axis_inner_self {n : ℕ} (i : Fin n) (s : Bool) (c : ℝ) :
    inner ℝ ((c * sign s) • epsilon i) ((c * sign s) • epsilon i) = c ^ 2 := by
  simp only [real_inner_smul_left, real_inner_smul_right, inner_epsilon_left,
    epsilon_apply, ite_eq_left rfl]
  cases s <;> norm_num [sign] <;> ring

lemma axisRoots_inner_self {n : ℕ} {c : ℝ} {a : Space n} (ha : a ∈ axisRoots n c) :
    inner ℝ a a = c ^ 2 := by
  rcases ha with ⟨i,s,rfl⟩
  exact axis_inner_self i s c

lemma pairRoots_nonzero {n : ℕ} {a : Space n} (ha : a ∈ pairRoots n) : a ≠ 0 := by
  intro h
  have := pairRoots_inner_self ha
  norm_num [h] at this

lemma axisRoots_nonzero {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    {a : Space n} (ha : a ∈ axisRoots n c) : a ≠ 0 := by
  intro h
  have := axisRoots_inner_self ha
  simpa [h, sq_eq_zero_iff, hc] using this.symm

lemma reflection_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : rootReflection a (b + c) = rootReflection a b + rootReflection a c := by
  simp only [rootReflection, inner_add_left, mul_add, add_div, add_smul]
  module

lemma reflection_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (c : ℝ) : rootReflection a (c • b) = c • rootReflection a b := by
  simp only [rootReflection, real_inner_smul_left, smul_sub, smul_smul]
  congr 1
  congr 1
  ring

/-- A two-coordinate reflection is a signed transposition. -/
lemma reflection_pair_epsilon {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (k : Fin n) :
    ∃ u : Bool, rootReflection (sign s • epsilon i + sign t • epsilon j) (epsilon k) =
      sign u • epsilon (Equiv.swap i j k) := by
  by_cases hki : k = i
  · subst k
    refine ⟨!(s.xor t), ?_⟩
    rw [rootReflection, pair_inner_self hij]
    simp only [inner_add_right, real_inner_smul_right, inner_epsilon_left, epsilon_apply,
      ite_eq_left rfl, ite_eq_right (Ne.symm hij), Equiv.swap_apply_left]
    cases s <;> cases t <;> norm_num [sign] <;> module
  · by_cases hkj : k = j
    · subst k
      refine ⟨!(s.xor t), ?_⟩
      rw [rootReflection, pair_inner_self hij]
      simp only [inner_add_right, real_inner_smul_right, inner_epsilon_left, epsilon_apply,
        ite_eq_left rfl, ite_eq_right hij, Equiv.swap_apply_right]
      cases s <;> cases t <;> norm_num [sign] <;> module
    · refine ⟨false, ?_⟩
      rw [rootReflection, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        inner_epsilon_left, inner_epsilon_left]
      simp [epsilon_apply, Ne.symm hki, Ne.symm hkj,
        Equiv.swap_apply_of_ne_of_ne hki hkj, sign]

lemma pair_reflection_pair {n : ℕ} {a b : Space n}
    (ha : a ∈ pairRoots n) (hb : b ∈ pairRoots n) : rootReflection a b ∈ pairRoots n := by
  rcases ha with ⟨i,j,hij,s,t,rfl⟩
  rcases hb with ⟨k,l,hkl,u,v,rfl⟩
  obtain ⟨u',hu⟩ := reflection_pair_epsilon hij s t k
  obtain ⟨v',hv⟩ := reflection_pair_epsilon hij s t l
  refine ⟨_,_,(Equiv.swap i j).injective.ne hkl,u.xor u',v.xor v',?_⟩
  rw [reflection_add, reflection_smul, reflection_smul, hu, hv,
    smul_smul, smul_smul, sign_mul, sign_mul]

lemma pair_reflection_axis {n : ℕ} {c : ℝ} {a b : Space n}
    (ha : a ∈ pairRoots n) (hb : b ∈ axisRoots n c) : rootReflection a b ∈ axisRoots n c := by
  rcases ha with ⟨i,j,hij,s,t,rfl⟩
  rcases hb with ⟨k,u,rfl⟩
  obtain ⟨v,hv⟩ := reflection_pair_epsilon hij s t k
  refine ⟨Equiv.swap i j k,u.xor v,?_⟩
  rw [reflection_smul, hv, smul_smul, mul_assoc, sign_mul]

/-- A coordinate reflection changes exactly one sign. -/
lemma reflection_axis_epsilon {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    (i : Fin n) (s : Bool) (k : Fin n) :
    ∃ u : Bool, rootReflection ((c * sign s) • epsilon i) (epsilon k) = sign u • epsilon k := by
  by_cases hki : k = i
  · subst k
    refine ⟨true, ?_⟩
    rw [rootReflection, axis_inner_self]
    simp only [real_inner_smul_right, inner_epsilon_left, epsilon_apply, ite_true, mul_one,
      smul_smul]
    have heq : (2 * (c * sign s) / c ^ 2) * (c * sign s) = 2 := by
      cases s <;> dsimp [sign] <;> field_simp [hc] <;> ring
    rw [heq]
    norm_num [sign]
    module
  · refine ⟨false, ?_⟩
    rw [rootReflection, real_inner_smul_right, inner_epsilon_left]
    simp [epsilon_apply, Ne.symm hki, sign]

lemma axis_reflection_pair {n : ℕ} {c : ℝ} (hc : c ≠ 0) {a b : Space n}
    (ha : a ∈ axisRoots n c) (hb : b ∈ pairRoots n) : rootReflection a b ∈ pairRoots n := by
  rcases ha with ⟨i,s,rfl⟩
  rcases hb with ⟨k,l,hkl,u,v,rfl⟩
  obtain ⟨u',hu⟩ := reflection_axis_epsilon hc i s k
  obtain ⟨v',hv⟩ := reflection_axis_epsilon hc i s l
  refine ⟨k,l,hkl,u.xor u',v.xor v',?_⟩
  rw [reflection_add, reflection_smul, reflection_smul, hu, hv,
    smul_smul, smul_smul, sign_mul, sign_mul]

lemma axis_reflection_axis {n : ℕ} {c : ℝ} (hc : c ≠ 0) {a b : Space n}
    (ha : a ∈ axisRoots n c) (hb : b ∈ axisRoots n c) : rootReflection a b ∈ axisRoots n c := by
  rcases ha with ⟨i,s,rfl⟩
  rcases hb with ⟨k,u,rfl⟩
  obtain ⟨v,hv⟩ := reflection_axis_epsilon hc i s k
  refine ⟨k,u.xor v,?_⟩
  rw [reflection_smul, hv, smul_smul, mul_assoc, sign_mul]

lemma equal_norm_reduced {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b : E} {N : ℝ} (hN : N ≠ 0) (ha : inner ℝ a a = N) (hb : inner ℝ b b = N)
    (hba : b ∈ Submodule.span ℝ ({a} : Set E)) : b = a ∨ b = -a := by
  rcases Submodule.mem_span_singleton.mp hba with ⟨t, rfl⟩
  rw [real_inner_smul_left, real_inner_smul_right, ha] at hb
  have ht : t ^ 2 = 1 := by
    have : (t ^ 2 - 1) * N = 0 := by nlinarith [hb]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hN)
  rcases sq_eq_one_iff.mp ht with rfl | rfl <;> simp

/-- A vector supported on two distinct coordinates cannot be a multiple
of a vector supported on one coordinate. -/
lemma pair_not_axis_smul {n : ℕ} {c : ℝ} {a b : Space n}
    (ha : a ∈ axisRoots n c) (hb : b ∈ pairRoots n) (r : ℝ) : b ≠ r • a := by
  rcases ha with ⟨i,s,rfl⟩
  rcases hb with ⟨j,k,hjk,t,u,rfl⟩
  intro h
  by_cases hij : i = j
  · subst i
    have h := congrArg (fun x : Space n => x k) h
    simpa [PiLp.add_apply, PiLp.smul_apply, epsilon_apply, hjk, Ne.symm hjk] using h
  · have h := congrArg (fun x : Space n => x j) h
    simpa [PiLp.add_apply, PiLp.smul_apply, epsilon_apply, hij, Ne.symm hjk] using h

lemma pair_axis_disjoint (n : ℕ) (c : ℝ) : Disjoint (axisRoots n c) (pairRoots n) := by
  apply Set.disjoint_left.mpr
  intro a ha hb
  exact pair_not_axis_smul ha hb 1 (one_smul ℝ a).symm

lemma union_reduced {n : ℕ} {c : ℝ} (hc : c ≠ 0) {a b : Space n}
    (ha : a ∈ axisRoots n c ∪ pairRoots n) (hb : b ∈ axisRoots n c ∪ pairRoots n)
    (hba : b ∈ Submodule.span ℝ ({a} : Set (Space n))) : b = a ∨ b = -a := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact equal_norm_reduced (pow_ne_zero _ hc) (axisRoots_inner_self ha)
      (axisRoots_inner_self hb) hba
  · rcases Submodule.mem_span_singleton.mp hba with ⟨r,hr⟩
    exact False.elim (pair_not_axis_smul ha hb r hr.symm)
  · rcases Submodule.mem_span_singleton.mp hba with ⟨r,hr⟩
    have hr0 : r ≠ 0 := by
      intro h
      exact axisRoots_nonzero hc hb (by simpa [h] using hr.symm)
    apply False.elim
    apply pair_not_axis_smul hb ha r⁻¹
    rw [← hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  · exact equal_norm_reduced (by norm_num) (pairRoots_inner_self ha)
      (pairRoots_inner_self hb) hba

lemma pairRoots_integral_coordinates {n : ℕ} {a : Space n} (ha : a ∈ pairRoots n)
    (k : Fin n) : ∃ z : ℤ, a k = (z : ℝ) := by
  rcases ha with ⟨i,j,_,s,t,rfl⟩
  refine ⟨(if s then -1 else 1) * (if i = k then 1 else 0) +
    (if t then -1 else 1) * (if j = k then 1 else 0), ?_⟩
  change sign s * epsilon i k + sign t * epsilon j k = _
  simp only [epsilon_apply, sign]
  push_cast
  rfl

lemma axisRoots_integral_coordinates {n : ℕ} {c : ℝ} (hc : c = 1 ∨ c = 2)
    {a : Space n} (ha : a ∈ axisRoots n c) (k : Fin n) : ∃ z : ℤ, a k = (z : ℝ) := by
  rcases ha with ⟨i,s,rfl⟩
  rcases hc with rfl | rfl
  · refine ⟨(if s then -1 else 1) * (if i = k then 1 else 0), ?_⟩
    change (1 * sign s) * epsilon i k = _
    simp [epsilon_apply, sign]
  · refine ⟨2 * (if s then -1 else 1) * (if i = k then 1 else 0), ?_⟩
    change (2 * sign s) * epsilon i k = _
    simp [epsilon_apply, sign]

lemma pair_integral_of_coordinates {n : ℕ} {a b : Space n} (ha : a ∈ pairRoots n)
    (hb : ∀ k : Fin n, ∃ z : ℤ, b k = (z : ℝ)) :
    ∃ z : ℤ, 2 * inner ℝ b a / inner ℝ a a = (z : ℝ) := by
  rw [pairRoots_inner_self ha]
  rcases ha with ⟨i,j,hij,s,t,rfl⟩
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_epsilon_right, inner_epsilon_right]
  obtain ⟨zi,hi⟩ := hb i
  obtain ⟨zj,hj⟩ := hb j
  rw [hi,hj]
  refine ⟨(if s then -zi else zi) + (if t then -zj else zj), ?_⟩
  cases s <;> cases t <;> simp [sign] <;> ring

lemma axis_integral_of_coordinates {n : ℕ} {c : ℝ} (hc : c = 1 ∨ c = 2)
    {a b : Space n} (ha : a ∈ axisRoots n c)
    (hb : ∀ k : Fin n, ∃ z : ℤ, b k = (z : ℝ)) :
    ∃ z : ℤ, 2 * inner ℝ b a / inner ℝ a a = (z : ℝ) := by
  rw [axisRoots_inner_self ha]
  rcases ha with ⟨i,s,rfl⟩
  rw [real_inner_smul_right, inner_epsilon_right]
  obtain ⟨z,hz⟩ := hb i
  rw [hz]
  rcases hc with rfl | rfl
  · refine ⟨2 * (if s then -z else z), ?_⟩
    cases s <;> simp [sign] <;> ring
  · refine ⟨if s then -z else z, ?_⟩
    cases s <;> simp [sign] <;> ring

lemma pairRoots_axioms (n : ℕ) : RootAxioms (pairRoots n) where
  finite := pairRoots_finite n
  nonzero := fun _ ha => pairRoots_nonzero ha
  reflection_mem := fun _ ha _ hb => pair_reflection_pair ha hb
  integral := fun _ ha _ hb => pair_integral_of_coordinates ha (pairRoots_integral_coordinates hb)
  reduced := fun _ ha _ hb hba => equal_norm_reduced (by norm_num)
    (pairRoots_inner_self ha) (pairRoots_inner_self hb) hba

lemma union_axis_pair_axioms (n : ℕ) {c : ℝ} (hc : c = 1 ∨ c = 2) :
    RootAxioms (axisRoots n c ∪ pairRoots n) := by
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  refine ⟨(axisRoots_finite n c).union (pairRoots_finite n), ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact ha.elim (axisRoots_nonzero hc0) pairRoots_nonzero
  · intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (axis_reflection_axis hc0 ha hb)
    · exact Or.inr (axis_reflection_pair hc0 ha hb)
    · exact Or.inl (pair_reflection_axis ha hb)
    · exact Or.inr (pair_reflection_pair ha hb)
  · intro a ha b hb
    have hcoords : ∀ k : Fin n, ∃ z : ℤ, b k = (z : ℝ) := by
      exact hb.elim (axisRoots_integral_coordinates hc) pairRoots_integral_coordinates
    exact ha.elim (fun h => axis_integral_of_coordinates hc h hcoords)
      (fun h => pair_integral_of_coordinates h hcoords)
  · exact fun _ ha _ hb hba => union_reduced hc0 ha hb hba

lemma span_epsilon (n : ℕ) : Submodule.span ℝ (Set.range (@epsilon n)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hsum : ∑ i : Fin n, x i • epsilon i = x := by
    apply PiLp.ext
    intro k
    simp [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, epsilon_apply]
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))

lemma union_axis_pair_span (n : ℕ) {c : ℝ} (hc : c ≠ 0) :
    Submodule.span ℝ (axisRoots n c ∪ pairRoots n) = ⊤ := by
  apply top_unique
  rw [← span_epsilon n]
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have hm : c • epsilon i ∈ Submodule.span ℝ (axisRoots n c ∪ pairRoots n) :=
    Submodule.subset_span (Or.inl ⟨i,false,by simp [sign]⟩)
  simpa [smul_smul, hc] using Submodule.smul_mem _ c⁻¹ hm

lemma pairRoots_span (n : ℕ) (hn : 2 ≤ n) : Submodule.span ℝ (pairRoots n) = ⊤ := by
  apply top_unique
  rw [← span_epsilon n]
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  obtain ⟨j,hij⟩ : ∃ j : Fin n, i ≠ j := by
    by_cases hi : i.val = 0
    · exact ⟨⟨1,by omega⟩,by apply Fin.ne_of_val_ne; change i.val ≠ 1; omega⟩
    · exact ⟨⟨0,by omega⟩,by apply Fin.ne_of_val_ne; change i.val ≠ 0; omega⟩
  have hp : epsilon i + epsilon j ∈ Submodule.span ℝ (pairRoots n) :=
    Submodule.subset_span ⟨i,j,hij,false,false,by simp [sign]⟩
  have hm : epsilon i - epsilon j ∈ Submodule.span ℝ (pairRoots n) :=
    Submodule.subset_span ⟨i,j,hij,false,true,by simp [sign,sub_eq_add_neg]⟩
  have heq : (1/2 : ℝ) • ((epsilon i + epsilon j) + (epsilon i - epsilon j)) = epsilon i := by module
  rw [← heq]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hp hm)

theorem rootSystemB : Specs.rootSystemBType := by
  intro n _
  exact ⟨union_axis_pair_axioms n (Or.inl rfl), union_axis_pair_span n (by norm_num)⟩

theorem rootSystemC : Specs.rootSystemCType := by
  intro n _
  exact ⟨union_axis_pair_axioms n (Or.inr rfl), union_axis_pair_span n (by norm_num)⟩

theorem rootSystemD : Specs.rootSystemDType := by
  intro n hn
  exact ⟨pairRoots_axioms n, pairRoots_span n (by omega)⟩

/-- Unique counting parameters use the smaller support index first. -/
def pairParameter (n : ℕ) (p : (Fin n × Fin n) × (Bool × Bool)) : Space n :=
  sign p.2.1 • epsilon p.1.1 + sign p.2.2 • epsilon p.1.2

lemma pair_support {n : ℕ} {i j k l : Fin n} {s t u v : Bool} (hij : i ≠ j)
    (h : sign s • epsilon i + sign t • epsilon j = sign u • epsilon k + sign v • epsilon l) :
    (i = k ∨ i = l) ∧ (j = k ∨ j = l) := by
  constructor
  · by_contra hn
    push_neg at hn
    have he := congrArg (fun x : Space n => x i) h
    simp [PiLp.add_apply, PiLp.smul_apply, epsilon_apply, Ne.symm hij,
      Ne.symm hn.1, Ne.symm hn.2] at he
  · by_contra hn
    push_neg at hn
    have he := congrArg (fun x : Space n => x j) h
    simp [PiLp.add_apply, PiLp.smul_apply, epsilon_apply, hij,
      Ne.symm hn.1, Ne.symm hn.2] at he

lemma pairParameter_injOn (n : ℕ) :
    Set.InjOn (pairParameter n) {p | p.1.1 < p.1.2} := by
  rintro ⟨⟨i,j⟩,⟨s,t⟩⟩ hij ⟨⟨k,l⟩,⟨u,v⟩⟩ hkl h
  change i < j at hij
  change k < l at hkl
  change sign s • epsilon i + sign t • epsilon j = sign u • epsilon k + sign v • epsilon l at h
  have hsupp := pair_support (ne_of_lt hij) h
  have hi : i = k := by
    rcases hsupp.1 with hi | hi
    · exact hi
    · rcases hsupp.2 with hj | hj
      · subst l; subst k; exact False.elim (lt_asymm hij hkl)
      · exact False.elim ((ne_of_lt hij) (hi.trans hj.symm))
  subst k
  have hj : j = l := hsupp.2.resolve_left (ne_of_gt hij)
  subst l
  have hs : s = u := by
    apply sign_injective
    have he := congrArg (fun x : Space n => x i) h
    simpa [PiLp.add_apply, PiLp.smul_apply, epsilon_apply, ne_of_gt hij] using he
  have ht : t = v := by
    apply sign_injective
    have he := congrArg (fun x : Space n => x j) h
    simpa [PiLp.add_apply, PiLp.smul_apply, epsilon_apply, ne_of_lt hij] using he
  subst u; subst v
  rfl

lemma pairRoots_image (n : ℕ) :
    pairRoots n = pairParameter n '' {p | p.1.1 < p.1.2} := by
  ext a
  constructor
  · rintro ⟨i,j,hij,s,t,rfl⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨((i,j),(s,t)),h,rfl⟩
    · exact ⟨((j,i),(t,s)),h,add_comm _ _⟩
  · rintro ⟨⟨⟨i,j⟩,⟨s,t⟩⟩,h,rfl⟩
    exact ⟨i,j,ne_of_lt h,s,t,rfl⟩

lemma orderedPairs_ncard (n : ℕ) :
    {p : Fin n × Fin n | p.1 < p.2}.ncard = n.choose 2 := by
  have hset : {p : Fin n × Fin n | p.1 < p.2} =
      (↑((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 < p.2)) : Set _) := by
    ext p
    simp
  rw [hset, Set.ncard_coe_finset, Finset.card_product_filter_lt]
  simp

lemma pairRoots_ncard (n : ℕ) : (pairRoots n).ncard = 2 * n * (n - 1) := by
  rw [pairRoots_image, (pairParameter_injOn n).ncard_image]
  have hset : {p : (Fin n × Fin n) × (Bool × Bool) | p.1.1 < p.1.2} =
      {p : Fin n × Fin n | p.1 < p.2} ×ˢ (Set.univ : Set (Bool × Bool)) := by
    ext p
    simp
  rw [hset, Set.ncard_prod, orderedPairs_ncard]
  simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool]
  have heq : n.choose 2 * 2 = n * (n - 1) := by
    cases n with
    | zero => simp
    | succ m =>
      have h := Nat.add_one_mul_choose_eq m 1
      simpa using h.symm
  nlinarith

def axisParameter (n : ℕ) (c : ℝ) (p : Fin n × Bool) : Space n :=
  (c * sign p.2) • epsilon p.1

lemma axisParameter_injective (n : ℕ) {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (axisParameter n c) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  have hij : i = j := by
    by_contra hij
    have he := congrArg (fun x : Space n => x i) h
    have hn : c * sign s ≠ 0 := mul_ne_zero hc (sign_ne_zero s)
    simp [axisParameter, PiLp.smul_apply, epsilon_apply, Ne.symm hij] at he
    exact hc he
  subst j
  have he := congrArg (fun x : Space n => x i) h
  have hs : s = t := by
    apply sign_injective
    apply mul_left_cancel₀ hc
    simpa [axisParameter, PiLp.smul_apply, epsilon_apply] using he
  subst t
  rfl

lemma axisRoots_ncard (n : ℕ) {c : ℝ} (hc : c ≠ 0) :
    (axisRoots n c).ncard = 2 * n := by
  have heq : axisRoots n c = Set.range (axisParameter n c) := by
    ext a
    constructor
    · rintro ⟨i,s,rfl⟩; exact ⟨(i,s),rfl⟩
    · rintro ⟨⟨i,s⟩,rfl⟩; exact ⟨i,s,rfl⟩
  rw [heq, ← Set.image_univ, (axisParameter_injective n hc).injOn.ncard_image]
  simp [Nat.mul_comm]

lemma union_axis_pair_ncard (n : ℕ) {c : ℝ} (hc : c ≠ 0) :
    (axisRoots n c ∪ pairRoots n).ncard = 2 * n ^ 2 := by
  rw [Set.ncard_union_eq (pair_axis_disjoint n c) (axisRoots_finite n c) (pairRoots_finite n),
    axisRoots_ncard n hc, pairRoots_ncard]
  cases n with
  | zero => simp
  | succ m => simp only [Nat.add_sub_cancel]; ring

theorem countB : Specs.countBType := by
  intro n _
  exact union_axis_pair_ncard n (by norm_num)

theorem countC : Specs.countCType := by
  intro n _
  exact union_axis_pair_ncard n (by norm_num)

theorem countD : Specs.countDType := by
  intro n _
  exact pairRoots_ncard n

/-- Decreasing coordinates whose simple-root heights will all be one. -/
def regularBCD (n : ℕ) (offset : ℝ) : Space n :=
  WithLp.toLp 2 (fun i : Fin n => (n : ℝ) - i.val - offset)

lemma inner_regular_pair {n : ℕ} (c : ℝ) (i j : Fin n) (s t : Bool) :
    inner ℝ (regularBCD n c) (sign s • epsilon i + sign t • epsilon j) =
      sign s * ((n : ℝ) - i.val - c) + sign t * ((n : ℝ) - j.val - c) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_epsilon_right, inner_epsilon_right]
  rfl

lemma pair_height_separated {n : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {a : Space n} (ha : a ∈ pairRoots n) :
    inner ℝ (regularBCD n c) a ≤ -1 ∨ 1 ≤ inner ℝ (regularBCD n c) a := by
  rcases ha with ⟨i,j,hij,s,t,rfl⟩
  rw [inner_regular_pair]
  have hsum : (i.val : ℝ) + j.val + 3 ≤ (n : ℝ) + n := by
    exact_mod_cast (show i.val + j.val + 3 ≤ n + n by
      have := i.isLt; have := j.isLt; have := Fin.val_ne_of_ne hij; omega)
  have hgap : (i.val : ℝ) + 1 ≤ j.val ∨ (j.val : ℝ) + 1 ≤ i.val := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (by exact_mod_cast (show i.val + 1 ≤ j.val from h))
    · exact Or.inr (by exact_mod_cast (show j.val + 1 ≤ i.val from h))
  cases s <;> cases t <;> norm_num [sign] <;>
    rcases hgap with hgap | hgap <;> (first | left; linarith | right; linarith)

lemma union_height_separated {n : ℕ} {c offset : ℝ}
    (h : (c = 1 ∧ offset = 0) ∨ (c = 2 ∧ offset = 1/2))
    {a : Space n} (ha : a ∈ axisRoots n c ∪ pairRoots n) :
    inner ℝ (regularBCD n offset) a ≤ -1 ∨ 1 ≤ inner ℝ (regularBCD n offset) a := by
  rcases ha with ha | ha
  · rcases ha with ⟨i,s,rfl⟩
    rw [real_inner_smul_right, inner_epsilon_right]
    change (c * sign s) * ((n : ℝ) - i.val - offset) ≤ -1 ∨
      1 ≤ (c * sign s) * ((n : ℝ) - i.val - offset)
    have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases s <;> norm_num [sign] <;>
      (first | left; linarith | right; linarith)
  · apply pair_height_separated (ha := ha) <;> rcases h with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> norm_num

lemma regular_of_separated {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : Set E} {v : E} (h : ∀ a ∈ R, inner ℝ v a ≤ -1 ∨ 1 ≤ inner ℝ v a) :
    RootRegular R v := by
  intro a ha hz
  rcases h a ha with h | h <;> linarith

lemma simple_of_height_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : Set E} {v a : E} (h : ∀ b ∈ R, inner ℝ v b ≤ -1 ∨ 1 ≤ inner ℝ v b)
    (ha : a ∈ R) (hheight : inner ℝ v a = 1) : a ∈ simpleRoots R v := by
  refine ⟨⟨ha,by linarith⟩, ?_⟩
  rintro b ⟨hb,hbpos⟩ c ⟨hc,hcpos⟩ heq
  have hb1 : 1 ≤ inner ℝ v b := (h b hb).resolve_left (by linarith)
  have hc1 : 1 ≤ inner ℝ v c := (h c hc).resolve_left (by linarith)
  rw [heq, inner_add_right] at hheight
  linarith

lemma simpleB_mem (n : ℕ) (i : Fin n) : simpleB n i ∈ rootsB n := by
  unfold simpleB
  split_ifs with h
  · exact Or.inr ⟨i,⟨i.val+1,h⟩,by simp [Fin.ext_iff],false,true,by simp [sign,sub_eq_add_neg]⟩
  · exact Or.inl ⟨i,false,by simp [sign]⟩

lemma simpleC_mem (n : ℕ) (i : Fin n) : simpleC n i ∈ rootsC n := by
  unfold simpleC
  split_ifs with h
  · exact Or.inr ⟨i,⟨i.val+1,h⟩,by simp [Fin.ext_iff],false,true,by simp [sign,sub_eq_add_neg]⟩
  · exact Or.inl ⟨i,false,by simp [sign, two_smul]⟩

lemma simpleD_mem (n : ℕ) (hn : 4 ≤ n) (i : Fin n) : simpleD n i ∈ rootsD n := by
  unfold simpleD
  split_ifs with h
  · exact ⟨i,⟨i.val+1,h⟩,by simp [Fin.ext_iff],false,true,by simp [sign,sub_eq_add_neg]⟩
  · exact ⟨⟨n-2,by have := i.isLt; omega⟩,i,by
      apply Fin.ne_of_val_ne; change n-2 ≠ i.val; have := i.isLt; omega,
      false,false,by simp [sign]⟩

lemma simpleB_height (n : ℕ) (i : Fin n) : inner ℝ (regularBCD n 0) (simpleB n i) = 1 := by
  unfold simpleB
  split_ifs with h
  · rw [inner_difference_right]
    change ((n : ℝ) - i.val - 0) - ((n : ℝ) - (i.val + 1 : ℕ) - 0) = 1
    push_cast
    ring
  · rw [inner_epsilon_right]
    change (n : ℝ) - i.val - 0 = 1
    have hi : i.val + 1 = n := by have := i.isLt; omega
    exact_mod_cast (show (n : ℤ) - (i.val : ℤ) - 0 = 1 by omega)

lemma simpleC_height (n : ℕ) (i : Fin n) : inner ℝ (regularBCD n (1/2)) (simpleC n i) = 1 := by
  unfold simpleC
  split_ifs with h
  · rw [inner_difference_right]
    change ((n : ℝ) - i.val - 1/2) - ((n : ℝ) - (i.val + 1 : ℕ) - 1/2) = 1
    push_cast
    ring
  · rw [two_smul, inner_add_right, inner_epsilon_right]
    change ((n : ℝ) - i.val - 1/2) + ((n : ℝ) - i.val - 1/2) = 1
    have hi : (i.val : ℝ) + 1 = n := by exact_mod_cast (show i.val+1=n by have := i.isLt; omega)
    linarith

lemma simpleD_height (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    inner ℝ (regularBCD n 1) (simpleD n i) = 1 := by
  unfold simpleD
  split_ifs with h
  · rw [inner_difference_right]
    change ((n : ℝ) - i.val - 1) - ((n : ℝ) - (i.val + 1 : ℕ) - 1) = 1
    push_cast
    ring
  · rw [inner_add_right, inner_epsilon_right, inner_epsilon_right]
    change ((n : ℝ) - (n-2 : ℕ) - 1) + ((n : ℝ) - i.val - 1) = 1
    have hi : (i.val : ℝ) + 1 = n := by exact_mod_cast (show i.val+1=n by have := i.isLt; omega)
    have hn2 : ((n-2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hn2]
    linarith

lemma submodule_eq_top_of_adjacent (n : ℕ) (M : Submodule ℝ (Space n))
    (hlast : ∀ i : Fin n, ¬ i.val + 1 < n → epsilon i ∈ M)
    (hdiff : ∀ (i : Fin n) (h : i.val + 1 < n),
      epsilon i - epsilon ⟨i.val + 1, h⟩ ∈ M) : M = ⊤ := by
  apply top_unique
  rw [← span_epsilon n]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hall : ∀ k, ∀ i : Fin n, n - i.val = k → epsilon i ∈ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hki
      by_cases hi : i.val + 1 < n
      · have hj : epsilon ⟨i.val + 1, hi⟩ ∈ M :=
          ih (n - (i.val + 1)) (by omega) ⟨i.val + 1, hi⟩ rfl
        simpa only [sub_add_cancel] using M.add_mem (hdiff i hi) hj
      · exact hlast i hi
  exact hall (n - i.val) i rfl

lemma simpleB_span (n : ℕ) : Submodule.span ℝ (Set.range (simpleB n)) = ⊤ := by
  apply submodule_eq_top_of_adjacent
  · intro i hi
    have hm := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleB n) i)
    simpa [simpleB, hi] using hm
  · intro i hi
    have hm := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleB n) i)
    simpa [simpleB, hi] using hm

lemma simpleC_span (n : ℕ) : Submodule.span ℝ (Set.range (simpleC n)) = ⊤ := by
  apply submodule_eq_top_of_adjacent
  · intro i hi
    have hm := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleC n) i)
    have hm2 : (2 : ℕ) • epsilon i ∈ Submodule.span ℝ (Set.range (simpleC n)) := by
      simpa [simpleC, hi] using hm
    have hs := Submodule.smul_mem (Submodule.span ℝ (Set.range (simpleC n))) (1/2 : ℝ) hm2
    have heq : (1/2 : ℝ) • ((2 : ℕ) • epsilon i) = epsilon i := by module
    rwa [heq] at hs
  · intro i hi
    have hm := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleC n) i)
    simpa [simpleC, hi] using hm

lemma simpleD_span (n : ℕ) (hn : 4 ≤ n) :
    Submodule.span ℝ (Set.range (simpleD n)) = ⊤ := by
  let a : Fin n := ⟨n - 2, by omega⟩
  let b : Fin n := ⟨n - 1, by omega⟩
  have hab : a.val + 1 < n := by dsimp [a]; omega
  have hb : ¬ b.val + 1 < n := by dsimp [b]; omega
  have has : (⟨a.val + 1, hab⟩ : Fin n) = b := by apply Fin.ext; dsimp [a, b]; omega
  have hm : epsilon a - epsilon b ∈ Submodule.span ℝ (Set.range (simpleD n)) := by
    have h := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleD n) a)
    simpa [simpleD, hab, has] using h
  have hp : epsilon a + epsilon b ∈ Submodule.span ℝ (Set.range (simpleD n)) := by
    have h := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleD n) b)
    simpa [simpleD, hb, a] using h
  have heq : (1/2 : ℝ) • ((epsilon a + epsilon b) - (epsilon a - epsilon b)) = epsilon b := by module
  have he : epsilon b ∈ Submodule.span ℝ (Set.range (simpleD n)) := by
    rw [← heq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hp hm)
  apply submodule_eq_top_of_adjacent
  · intro i hi
    have hib : i = b := by apply Fin.ext; dsimp [b]; have := i.isLt; omega
    simpa [hib] using he
  · intro i hi
    have h := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := simpleD n) i)
    simpa [simpleD, hi] using h


lemma simple_basis_of_span {n : ℕ} (R : Set (Space n)) (hR : IsRootSystem R)
    (v : Space n) (hv : RootRegular R v) (s : Fin n → Space n)
    (hs : ∀ i, s i ∈ simpleRoots R v)
    (hspan : Submodule.span ℝ (Set.range s) = ⊤) :
    ∃ b : Basis (Fin n) ℝ (Space n),
      (∀ i, b i = s i) ∧ IsSimpleBasis R v b := by
  obtain ⟨c,hc⟩ := simpleRoots_basis R hR v hv
  have hcrange : Set.range c = simpleRoots R v := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      rw [hc a]
      exact a.property
    · intro hx
      exact ⟨⟨x,hx⟩, hc ⟨x,hx⟩⟩
  have hli : LinearIndepOn ℝ id (simpleRoots R v) := by
    rw [← hcrange]
    exact c.linearIndependent.linearIndepOn_id
  have hsub : Set.range s ⊆ simpleRoots R v := by
    rintro _ ⟨i,rfl⟩
    exact hs i
  have heq : Set.range s = simpleRoots R v := by
    apply Eq.symm
    apply eq_of_linearIndepOn_id_of_span_subtype hli hsub
    rw [hspan]
    exact Set.subset_univ _
  let b : Basis (Fin n) ℝ (Space n) :=
    basisOfTopLeSpanOfCardEqFinrank s hspan.ge (by simp [Space])
  have hb : (b : Fin n → Space n) = s := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  refine ⟨b, fun i => congrFun hb i, ?_⟩
  change Set.range b = simpleRoots R v
  rw [hb, heq]


lemma regularB_regular (n : ℕ) : RootRegular (rootsB n) (regularBCD n 0) :=
  regular_of_separated (fun _ ha => union_height_separated (Or.inl ⟨rfl, rfl⟩) ha)

lemma regularC_regular (n : ℕ) : RootRegular (rootsC n) (regularBCD n (1/2)) :=
  regular_of_separated (fun _ ha => union_height_separated (Or.inr ⟨rfl, rfl⟩) ha)

lemma regularD_regular (n : ℕ) : RootRegular (rootsD n) (regularBCD n 1) :=
  regular_of_separated (fun _ ha => pair_height_separated (by norm_num) (by norm_num) ha)

lemma simpleB_basis (n : ℕ) (hn : 2 ≤ n) :
    ∃ b : Basis (Fin n) ℝ (Space n),
      (∀ i, b i = simpleB n i) ∧ IsSimpleBasis (rootsB n) (regularBCD n 0) b := by
  apply simple_basis_of_span (rootsB n) (rootSystemB n hn) _ (regularB_regular n)
  · intro i
    exact simple_of_height_one
      (fun _ ha => union_height_separated (Or.inl ⟨rfl, rfl⟩) ha)
      (simpleB_mem n i) (simpleB_height n i)
  · exact simpleB_span n

lemma simpleC_basis (n : ℕ) (hn : 2 ≤ n) :
    ∃ b : Basis (Fin n) ℝ (Space n),
      (∀ i, b i = simpleC n i) ∧ IsSimpleBasis (rootsC n) (regularBCD n (1/2)) b := by
  apply simple_basis_of_span (rootsC n) (rootSystemC n hn) _ (regularC_regular n)
  · intro i
    exact simple_of_height_one
      (fun _ ha => union_height_separated (Or.inr ⟨rfl, rfl⟩) ha)
      (simpleC_mem n i) (simpleC_height n i)
  · exact simpleC_span n

lemma simpleD_basis (n : ℕ) (hn : 4 ≤ n) :
    ∃ b : Basis (Fin n) ℝ (Space n),
      (∀ i, b i = simpleD n i) ∧ IsSimpleBasis (rootsD n) (regularBCD n 1) b := by
  apply simple_basis_of_span (rootsD n) (rootSystemD n hn) _ (regularD_regular n)
  · intro i
    exact simple_of_height_one
      (fun _ ha => pair_height_separated (by norm_num) (by norm_num) ha)
      (simpleD_mem n hn i) (simpleD_height n hn i)
  · exact simpleD_span n hn

lemma simpleB_gram {n : ℕ} (i j : Fin n) :
    inner ℝ (simpleB n i) (simpleB n j) =
      if i = j then (if i.val+1<n then 2 else 1) else if adjacent i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    unfold simpleB
    split_ifs with hi
    · exact difference_norm (by simp [Fin.ext_iff])
    · simp only [inner_epsilon_left, epsilon_apply, ite_true]
  · rw [ite_eq_right hij]
    have hv := Fin.val_ne_of_ne hij
    unfold simpleB adjacent
    split_ifs <;>
      simp only [inner_sub_left, inner_sub_right, inner_epsilon_left, epsilon_apply, Fin.ext_iff] <;>
      split_ifs <;> norm_num <;> omega

lemma simpleC_gram {n : ℕ} (i j : Fin n) :
    inner ℝ (simpleC n i) (simpleC n j) =
      if i = j then (if i.val+1<n then 2 else 4) else
        if terminalEdge i j then -2 else if adjacent i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    unfold simpleC
    split_ifs with hi
    · exact difference_norm (by simp [Fin.ext_iff])
    · simp only [two_smul, inner_add_left, inner_add_right, inner_epsilon_left, epsilon_apply, ite_true]
      norm_num
  · rw [ite_eq_right hij]
    have hv := Fin.val_ne_of_ne hij
    have hi := i.isLt
    have hj := j.isLt
    unfold simpleC terminalEdge adjacent
    split_ifs <;>
      simp only [inner_sub_left, inner_sub_right, two_smul, inner_add_left, inner_add_right,
        inner_epsilon_left, epsilon_apply, Fin.ext_iff] <;>
      split_ifs <;> norm_num <;> omega

lemma simpleD_gram {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    inner ℝ (simpleD n i) (simpleD n j) =
      if i = j then 2 else if forkAdjacent i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact pairRoots_inner_self (simpleD_mem n hn i)
  · rw [ite_eq_right hij]
    have hv := Fin.val_ne_of_ne hij
    have hi := i.isLt
    have hj := j.isLt
    unfold simpleD forkAdjacent
    split_ifs <;>
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        inner_epsilon_left, epsilon_apply, Fin.ext_iff] <;>
      split_ifs <;> norm_num <;> omega


lemma simpleB_diagram_edges {n : ℕ} (i j : Fin n) :
    (dynkinDiagram (simpleB n)).edges i j =
      if terminalEdge i j then 2 else if adjacent i j then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [dynkinDiagram, cartanMatrix, rootCartan, simpleB_gram, ite_true]
  unfold terminalEdge adjacent
  split_ifs <;> norm_num <;> omega

lemma simpleB_diagram_arrows {n : ℕ} (i j : Fin n) :
    (dynkinDiagram (simpleB n)).arrow i j ↔ i.val + 2 = n ∧ j.val + 1 = n := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [dynkinDiagram, simpleB_gram, ite_true]
  unfold adjacent
  split_ifs <;> norm_num <;> omega

lemma simpleC_diagram_edges {n : ℕ} (i j : Fin n) :
    (dynkinDiagram (simpleC n)).edges i j =
      if terminalEdge i j then 2 else if adjacent i j then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [dynkinDiagram, cartanMatrix, rootCartan, simpleC_gram, ite_true]
  unfold terminalEdge adjacent
  split_ifs <;> norm_num <;> omega

lemma simpleC_diagram_arrows {n : ℕ} (i j : Fin n) :
    (dynkinDiagram (simpleC n)).arrow i j ↔ i.val + 1 = n ∧ j.val + 2 = n := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [dynkinDiagram, simpleC_gram, ite_true]
  unfold terminalEdge adjacent
  split_ifs <;> norm_num <;> omega

lemma simpleD_diagram_edges {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    (dynkinDiagram (simpleD n)).edges i j = if forkAdjacent i j then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [dynkinDiagram, cartanMatrix, rootCartan, simpleD_gram hn, ite_true]
  unfold forkAdjacent
  split_ifs <;> norm_num <;> omega

lemma simpleD_diagram_no_arrows {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    ¬ (dynkinDiagram (simpleD n)).arrow i j := by
  simp only [dynkinDiagram, simpleD_gram hn, ite_true]
  norm_num


theorem simpleDiagramB : Specs.simpleDiagramBType := by
  intro n hn
  obtain ⟨b, hb, hs⟩ := simpleB_basis n hn
  have hbfun : (b : Fin n → Space n) = simpleB n := funext hb
  refine ⟨regularBCD n 0, b, hb, regularB_regular n, hs, ?_, ?_⟩
  · intro i j
    simpa only [hbfun] using simpleB_diagram_edges i j
  · intro i j
    simpa only [hbfun] using simpleB_diagram_arrows i j

theorem simpleDiagramC : Specs.simpleDiagramCType := by
  intro n hn
  obtain ⟨b, hb, hs⟩ := simpleC_basis n hn
  have hbfun : (b : Fin n → Space n) = simpleC n := funext hb
  refine ⟨regularBCD n (1/2), b, hb, regularC_regular n, hs, ?_, ?_⟩
  · intro i j
    simpa only [hbfun] using simpleC_diagram_edges i j
  · intro i j
    simpa only [hbfun] using simpleC_diagram_arrows i j

theorem simpleDiagramD : Specs.simpleDiagramDType := by
  intro n hn
  obtain ⟨b, hb, hs⟩ := simpleD_basis n hn
  have hbfun : (b : Fin n → Space n) = simpleD n := funext hb
  refine ⟨regularBCD n 1, b, hb, regularD_regular n, hs, ?_, ?_⟩
  · intro i j
    simpa only [hbfun] using simpleD_diagram_edges hn i j
  · intro i j
    simpa only [hbfun] using simpleD_diagram_no_arrows hn i j

end LieAlgebrasAndRepresentations.ClassicalCoordinates
