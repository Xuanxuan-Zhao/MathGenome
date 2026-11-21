import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.NonseparatedCohomologyExample
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u
namespace AdvancedHomologicalAlgebra.NonseparatedExample
variable {k : Type u} [Field k]

@[simp] theorem coefficientSum_single (i : ℕ) (c : k) :
    coefficientSum k (Finsupp.single i c) = c := by
  simp [coefficientSum]

/-- Summation annihilates every differential. -/
theorem coefficientSum_comp_differential :
    coefficientSum k ∘ₗ differential k = 0 := by
  apply Finsupp.lhom_ext
  intro i c
  simp

/-- The prefix sum of the first `i` basis vectors. -/
def initialSegment (i : ℕ) : FiniteSequences k :=
  ∑ j ∈ Finset.range i, Finsupp.single j 1

/-- The finite telescoping identity, including the empty prefix. -/
theorem differential_initialSegment (i : ℕ) :
    differential k (initialSegment (k := k) i) =
      Finsupp.single 0 1 - Finsupp.single i 1 := by
  induction i with
  | zero => simp [initialSegment]
  | succ i ih =>
    rw [initialSegment, Finset.sum_range_succ, map_add]
    change differential k (initialSegment i) + _ = _
    rw [ih, differential_single]
    abel

/-- A finite primitive of the part with coefficient sum zero. -/
def finitePrimitive : FiniteSequences k →ₗ[k] FiniteSequences k :=
  -Finsupp.linearCombination k (initialSegment (k := k))

theorem differential_finitePrimitive :
    differential k ∘ₗ finitePrimitive (k := k) =
      LinearMap.id - (Finsupp.lsingle 0).comp (coefficientSum k) := by
  apply Finsupp.lhom_ext
  intro i c
  simp [finitePrimitive, differential_initialSegment, smul_sub]

/-- The direct sum differential has no kernel. -/
theorem differential_injective : Function.Injective (differential k) := by
  apply (injective_iff_map_eq_zero (differential k)).2
  intro a ha
  ext i
  induction i with
  | zero => simpa using congrArg (fun a : FiniteSequences k => a 0) ha
  | succ i ih =>
    have h := congrArg (fun a : FiniteSequences k => a (i+1)) ha
    simpa [ih] using h

theorem range_differential_eq_ker_sum :
    LinearMap.range (differential k) = LinearMap.ker (coefficientSum k) := by
  apply le_antisymm
  · rintro b ⟨a, rfl⟩
    change (coefficientSum k ∘ₗ differential k) a = 0
    rw [coefficientSum_comp_differential]
    rfl
  · intro b hb
    refine ⟨finitePrimitive b, ?_⟩
    have h := LinearMap.congr_fun (differential_finitePrimitive (k := k)) b
    simpa [LinearMap.mem_ker.mp hb] using h

theorem coefficientSum_surjective : Function.Surjective (coefficientSum k) := by
  intro c
  exact ⟨Finsupp.single 0 c, coefficientSum_single 0 c⟩

/-- The source's identification `H¹(K) ≃ k`, induced by coefficient sum. -/
def firstCohomologyEquiv : firstCohomology k ≃ₗ[k] k :=
  (Submodule.quotEquivOfEq _ _ range_differential_eq_ker_sum).trans
    ((coefficientSum k).quotKerEquivOfSurjective coefficientSum_surjective)

theorem tail_zero : tail k 0 = ⊤ := by
  ext a
  simp [mem_tail]

theorem tail_exhaustive : (⨆ p : ℤ, tail k p) = ⊤ := by
  apply top_unique
  rw [← tail_zero (k := k)]
  exact le_iSup (tail k) 0

theorem tail_separated : (⨅ p : ℤ, tail k p) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  ext i
  exact ((Submodule.mem_iInf _).mp ha (i+1)) i (by omega)

/-- Each tail still surjects onto the coefficient sum. -/
theorem coefficientSum_tail_surjective (p : ℤ) :
    Function.Surjective ((coefficientSum k).comp (tail k p).subtype) := by
  intro c
  refine ⟨⟨Finsupp.single p.toNat c, ?_⟩, coefficientSum_single p.toNat c⟩
  intro i hi
  apply Finsupp.single_eq_of_ne
  omega

theorem cohomologyTail_eq_top (p : ℤ) : cohomologyTail k p = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨b, rfl⟩ := (LinearMap.range (differential k)).mkQ_surjective x
  obtain ⟨a, ha⟩ := coefficientSum_tail_surjective (k := k) p (coefficientSum k b)
  refine Submodule.mem_map.mpr ⟨a.1, a.2, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  rw [range_differential_eq_ker_sum]
  change coefficientSum k (a.1 - b) = 0
  simpa only [map_sub, sub_eq_zero, LinearMap.comp_apply, Submodule.subtype_apply] using ha

theorem cohomology_not_separated : (⨅ p : ℤ, cohomologyTail k p) ≠ ⊥ := by
  simp only [cohomologyTail_eq_top, iInf_const]
  intro h
  have hz : (LinearMap.range (differential k)).mkQ (Finsupp.single 0 1) = 0 := by
    have : (LinearMap.range (differential k)).mkQ (Finsupp.single 0 1) ∈
        (⊥ : Submodule k (firstCohomology k)) := by rw [← h]; trivial
    exact this
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [range_differential_eq_ker_sum] at hm
  have : (1 : k) = 0 := by simpa only [LinearMap.mem_ker, coefficientSum_single] using hm
  exact one_ne_zero this

/-- The recurrence is a right inverse of the completed differential. -/
theorem completedDifferential_partialSums :
    completedDifferential k ∘ₗ partialSums k = LinearMap.id := by
  ext b n
  cases n with
  | zero => simp [completedDifferential, partialSums]
  | succ n =>
    simp [completedDifferential, partialSums, Finset.sum_range_succ]

/-- The recurrence is also a left inverse, so the completed complex is acyclic. -/
theorem partialSums_completedDifferential :
    partialSums k ∘ₗ completedDifferential k = LinearMap.id := by
  ext a n
  change (∑ j ∈ Finset.range (n+1), completedDifferential k a j) = a n
  induction n with
  | zero => simp [completedDifferential]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [completedDifferential]

/-- An explicit linear equivalence underlying the completed differential. -/
def completedDifferentialEquiv : Sequences k ≃ₗ[k] Sequences k :=
  LinearEquiv.ofLinearMap (completedDifferential k) (partialSums k)
    completedDifferential_partialSums partialSums_completedDifferential

theorem completedDifferential_extends :
    completedDifferential k ∘ₗ toProduct k = toProduct k ∘ₗ differential k := by
  apply LinearMap.ext
  intro a
  funext n
  change completedDifferential k (fun i => a i) n = differential k a n
  cases n <;> simp [completedDifferential]


/-- A product has a finite representative for each finite prefix. -/
def truncate (m : ℕ) (b : Sequences k) : FiniteSequences k :=
  ∑ i : Fin m, Finsupp.single i (b i)

theorem truncate_apply_lt (m : ℕ) (b : Sequences k) (i : ℕ) (hi : i < m) :
    truncate m b i = b i := by
  classical
  rw [truncate, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin m)]
  · simp
  · intro j _ hj
    apply Finsupp.single_eq_of_ne
    intro he
    exact hj (Fin.ext he.symm)
  · simp

@[simp] theorem quotientPrefix_mk (m : ℕ) (a : FiniteSequences k) :
    quotientPrefix k m ((tail k m).mkQ a) = finitePrefix k m a := rfl

theorem quotientPrefix_injective (m : ℕ) : Function.Injective (quotientPrefix k m) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (tail k m).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (tail k m).mkQ_surjective y
  apply (Submodule.Quotient.eq _).mpr
  intro i hi
  have he := congrFun h ⟨i, by exact_mod_cast hi⟩
  exact sub_eq_zero.mpr he

/-- Truncation is compatible with every quotient transition, not only adjacent ones. -/
theorem quotientPrefix_transition (m n : ℕ) (h : m ≤ n)
    (x : FiniteSequences k ⧸ tail k n) (i : Fin m) :
    quotientPrefix k m (quotientTransition k m n h x) i =
      quotientPrefix k n x ⟨i, lt_of_lt_of_le i.isLt h⟩ := by
  obtain ⟨a, rfl⟩ := (tail k n).mkQ_surjective x
  rfl

/-- The coefficient recovered from the inverse limit agrees with each prefix. -/
theorem completionToProduct_prefix (x : completion k) (m : ℕ) (i : Fin m) :
    completionToProduct k x i = quotientPrefix k m (x.1 m) i := by
  have h : i.val+1 ≤ m := i.isLt
  have hc := x.2 (i.val+1) m h
  have hh := quotientPrefix_transition (i.val+1) m h (x.1 m)
    (⟨i, Nat.lt_succ_self i⟩ : Fin (i.val+1))
  rw [hc] at hh
  exact hh

theorem completionToProduct_injective : Function.Injective (completionToProduct k) := by
  intro x y h
  apply Subtype.ext
  funext m
  apply quotientPrefix_injective
  funext i
  rw [← completionToProduct_prefix, ← completionToProduct_prefix]
  exact congrFun h i

theorem completionToProduct_surjective : Function.Surjective (completionToProduct k) := by
  intro b
  let x : completion k := ⟨fun m => (tail k m).mkQ (truncate m b), by
    intro m n h
    apply quotientPrefix_injective
    funext i
    rw [quotientPrefix_transition]
    change truncate n b i = truncate m b i
    rw [truncate_apply_lt n b i (lt_of_lt_of_le i.isLt h),
      truncate_apply_lt m b i i.isLt]⟩
  refine ⟨x, ?_⟩
  funext i
  exact truncate_apply_lt (i+1) b i (Nat.lt_succ_self i)

def completionEquivProduct : completion k ≃ₗ[k] Sequences k :=
  LinearEquiv.ofBijective (completionToProduct k)
    ⟨completionToProduct_injective, completionToProduct_surjective⟩

theorem completion_comparison :
    completionToProduct k ∘ₗ intoCompletion k = toProduct k := by
  apply LinearMap.ext
  intro a
  rfl


/-- The shifted part of the differential disappears in the next tail. -/
theorem differential_sub_mem_next (p : ℤ) (a : FiniteSequences k) (ha : a ∈ tail k p) :
    differential k a - a ∈ tail k (p+1) := by
  intro i hi
  cases i with
  | zero => simp
  | succ i => simp [ha i (by omega)]

theorem cohomologyCompletion_subsingleton : Subsingleton (cohomologyCompletion k) := by
  have (p : ℤ) : Subsingleton (firstCohomology k ⧸ cohomologyTail k p) :=
    Submodule.Quotient.subsingleton_iff.mpr (cohomologyTail_eq_top p)
  infer_instance

theorem cohomologyComparison_eq_zero : cohomologyComparison k = 0 := by
  have := cohomologyCompletion_subsingleton (k := k)
  exact Subsingleton.elim _ _

/-- The original associated graded differential really is the identity map. -/
theorem gradedDifferential_eq_id (p : ℤ) :
    gradedDifferential k p = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨a, ha, hx⟩ := x.2
  change quotientDifferential k p x.1 = x.1
  rw [← hx]
  exact (Submodule.Quotient.eq _).mpr (differential_sub_mem_next p a ha)

theorem productDifferential_sub_mem_next (p : ℤ) (a : Sequences k)
    (ha : a ∈ productTail k p) :
    completedDifferential k a - a ∈ productTail k (p+1) := by
  intro i hi
  cases i with
  | zero => simp [completedDifferential]
  | succ i => simp [completedDifferential, ha i (by omega)]

theorem productGradedDifferential_eq_id (p : ℤ) :
    productGradedDifferential k p = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨a, ha, hx⟩ := x.2
  change productQuotientDifferential k p x.1 = x.1
  rw [← hx]
  exact (Submodule.Quotient.eq _).mpr (productDifferential_sub_mem_next p a ha)

theorem quotientComparison_injective (p : ℤ) :
    Function.Injective (quotientComparison k p) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (tail k (p+1)).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (tail k (p+1)).mkQ_surjective y
  apply (Submodule.Quotient.eq _).mpr
  exact (Submodule.Quotient.eq (productTail k (p+1))).mp h

theorem gradedComparison_injective (p : ℤ) :
    Function.Injective (gradedComparison k p) := by
  intro x y h
  apply Subtype.ext
  exact quotientComparison_injective p (congrArg Subtype.val h)

/-- A single coefficient represents every class in a successive product-tail quotient. -/
theorem gradedComparison_surjective (p : ℤ) :
    Function.Surjective (gradedComparison k p) := by
  intro y
  obtain ⟨b, hb, hy⟩ := y.2
  let a : FiniteSequences k := Finsupp.single p.toNat (b p.toNat)
  have ha : a ∈ tail k p := by
    intro i hi
    apply Finsupp.single_eq_of_ne
    omega
  refine ⟨⟨(tail k (p+1)).mkQ a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change (productTail k (p+1)).mkQ (toProduct k a) = y.1
  rw [← hy]
  apply (Submodule.Quotient.eq _).mpr
  intro i hi
  change a i - b i = 0
  by_cases hip : (i : ℤ) < p
  · rw [ha i hip, hb i hip, sub_self]
  · have he : i = p.toNat := by omega
    subst i
    simp [a]

/-- The actual comparison on E₀ is a linear isomorphism commuting with d₀. -/
def gradedComparisonEquiv (p : ℤ) : gradedTerm k p ≃ₗ[k] productGradedTerm k p :=
  LinearEquiv.ofBijective (gradedComparison k p)
    ⟨gradedComparison_injective p, gradedComparison_surjective p⟩

theorem gradedComparison_commutes (p : ℤ) :
    productGradedDifferential k p ∘ₗ gradedComparison k p =
      gradedComparison k p ∘ₗ gradedDifferential k p := by
  rw [productGradedDifferential_eq_id, gradedDifferential_eq_id]
  simp

theorem cyclesZero_zero (p : ℤ) : cyclesZero k 0 p = gradedTerm k p := by
  unfold cyclesZero gradedTerm almostZero
  congr 1
  simp only [add_zero]
  apply le_antisymm inf_le_left
  intro a ha
  exact ⟨ha, differential_mem_tail p a ha⟩

theorem boundariesOne_zero (p : ℤ) : boundariesOne k 0 p = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨b, ⟨_, a, ha, rfl⟩, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (differential_mem_tail (p+1) a (by simpa using ha))

/-- In degree zero, an almost r-cycle for r≥1 already lies in the next tail. -/
theorem cyclesZero_eq_bot (r p : ℤ) (hr : 1 ≤ r) : cyclesZero k r p = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨a, ⟨ha, hd⟩, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hn : differential k a ∈ tail k (p+1) := by
    intro i hi
    exact hd i (by omega)
  simpa using (tail k (p+1)).sub_mem hn (differential_sub_mem_next p a ha)

/-- In degree one, every graded cycle is a boundary already on every r≥1 page. -/
theorem boundariesOne_eq_graded (r p : ℤ) (hr : 1 ≤ r) :
    boundariesOne k r p = gradedTerm k p := by
  apply le_antisymm
  · exact Submodule.map_mono inf_le_left
  · rintro x ⟨a, ha, rfl⟩
    refine Submodule.mem_map.mpr ⟨differential k a, ?_, ?_⟩
    · refine ⟨differential_mem_tail p a ha, Submodule.mem_map.mpr ⟨a, ?_, rfl⟩⟩
      intro i hi
      exact ha i (by omega)
    · exact (Submodule.Quotient.eq _).mpr (differential_sub_mem_next p a ha)

theorem pageZero_subsingleton (r p : ℤ) (hr : 1 ≤ r) :
    Subsingleton (pageZero k r p) := by
  have : Subsingleton (cyclesZero k r p) := by
    rw [cyclesZero_eq_bot r p hr]
    infer_instance
  unfold pageZero
  infer_instance

theorem pageOne_subsingleton (r p : ℤ) (hr : 1 ≤ r) :
    Subsingleton (pageOne k r p) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [boundariesOne_eq_graded r p hr]
  exact Submodule.comap_subtype_self (gradedTerm k p)

/-- Every bidegree of every page from E₁ onward vanishes. This uses the
source's exact Z/B formula, without any convergence assumption. -/
theorem page_subsingleton (r p q : ℤ) (hr : 1 ≤ r) : Subsingleton (page k r p q) := by
  unfold page
  split_ifs
  · exact pageZero_subsingleton r p hr
  · exact pageOne_subsingleton r p hr
  · infer_instance

/-- HA-S07's concrete two-term cohomology calculation. -/
theorem cohomology_calculation : Specs.Cohomology.{u} := by
  intro k _
  exact ⟨differential_injective, range_differential_eq_ker_sum,
    coefficientSum_surjective, ⟨firstCohomologyEquiv⟩⟩

/-- HA-S07's separation statements for the sum and its cohomology. -/
theorem filtration_calculation : Specs.Filtration.{u} := by
  intro k _
  exact ⟨tail_antitone, differential_mem_tail, tail_exhaustive, tail_separated,
    cohomologyTail_eq_top, cohomology_not_separated⟩

theorem completed_differential_calculation : Specs.CompletedDifferential.{u} := by
  intro k _
  exact ⟨completedDifferential_partialSums, partialSums_completedDifferential,
    completedDifferential_extends⟩
theorem completion_calculation : Specs.Completion.{u} := by
  intro k _
  exact ⟨⟨completionToProduct_injective, completionToProduct_surjective⟩,
    completion_comparison⟩

theorem graded_representative_calculation : Specs.GradedRepresentative.{u} := by
  intro k _ p a ha
  exact differential_sub_mem_next p a ha

theorem cohomology_completion_calculation : Specs.CohomologyCompletion.{u} := by
  intro k _
  exact ⟨cohomologyCompletion_subsingleton, cohomologyComparison_eq_zero⟩

theorem range_tailCohomologyInclusion (p : ℤ) :
    LinearMap.range (tailCohomologyInclusion k p) = cohomologyTail k p := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := (LinearMap.range (tailDifferential k p)).mkQ_surjective a
    exact Submodule.mem_map.mpr ⟨b.1, b.2, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨(LinearMap.range (tailDifferential k p)).mkQ ⟨b, hb⟩, rfl⟩
theorem zerothCohomology_subsingleton : Subsingleton (zerothCohomology k) := by
  have h : LinearMap.ker (differential k) = ⊥ :=
    LinearMap.ker_eq_bot.mpr differential_injective
  unfold zerothCohomology
  rw [h]
  infer_instance

theorem completed_zeroth_subsingleton : Subsingleton (completedZerothCohomology k) := by
  have h : LinearMap.ker (completedDifferential k) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (completedDifferentialEquiv (k := k)).injective
  unfold completedZerothCohomology
  rw [h]
  infer_instance

theorem completed_first_subsingleton : Subsingleton (completedFirstCohomology k) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact LinearMap.range_eq_top.mpr (completedDifferentialEquiv (k := k)).surjective

theorem cohomologyGradedTerm_subsingleton (p : ℤ) :
    Subsingleton (cohomologyGradedTerm k p) := by
  have : Subsingleton (firstCohomology k ⧸ cohomologyTail k (p+1)) :=
    Submodule.Quotient.subsingleton_iff.mpr (cohomologyTail_eq_top (p+1))
  infer_instance

theorem tail_eq_top_of_nonpos (p : ℤ) (hp : p ≤ 0) : tail k p = ⊤ := by
  ext a
  simp only [mem_tail, Submodule.mem_top, iff_true]
  intro i hi
  omega

theorem gradedTerm_subsingleton_of_neg (p : ℤ) (hp : p < 0) :
    Subsingleton (gradedTerm k p) := by
  have : tail k (p+1) = ⊤ := tail_eq_top_of_nonpos (p+1) (by omega)
  have : Subsingleton (FiniteSequences k ⧸ tail k (p+1)) :=
    Submodule.Quotient.subsingleton_iff.mpr this
  infer_instance

theorem gradedCoefficient_injective (p : ℤ) (hp : 0 ≤ p) :
    Function.Injective (gradedCoefficient (k := k) p hp) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply Subtype.ext
  obtain ⟨a, ha, he⟩ := x.2
  change x.1 = 0
  rw [← he]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  intro i hi
  by_cases hil : (i : ℤ) < p
  · exact ha i hil
  · have heq : i = p.toNat := by omega
    subst i
    change gradedCoefficient k p hp x = 0 at hx
    unfold gradedCoefficient at hx
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hx
    rw [← he] at hx
    exact hx

theorem gradedCoefficient_surjective (p : ℤ) (hp : 0 ≤ p) :
    Function.Surjective (gradedCoefficient (k := k) p hp) := by
  intro c
  refine ⟨⟨(tail k (p+1)).mkQ (Finsupp.single p.toNat c), ?_⟩, ?_⟩
  · refine Submodule.mem_map.mpr ⟨Finsupp.single p.toNat c, ?_, rfl⟩
    intro i hi
    apply Finsupp.single_eq_of_ne
    omega
  · change (Finsupp.single p.toNat c) p.toNat = c
    simp

def gradedCoefficientEquiv (p : ℤ) (hp : 0 ≤ p) : gradedTerm k p ≃ₗ[k] k :=
  LinearEquiv.ofBijective (gradedCoefficient k p hp)
    ⟨gradedCoefficient_injective p hp, gradedCoefficient_surjective p hp⟩
theorem acyclicity_calculation : Specs.Acyclicity.{u} := by
  intro k _
  exact ⟨zerothCohomology_subsingleton, completed_zeroth_subsingleton,
    completed_first_subsingleton⟩

theorem induced_filtration_calculation : Specs.InducedFiltration.{u} := by
  intro k _ p
  exact ⟨range_tailCohomologyInclusion (k := k) p, cohomologyGradedTerm_subsingleton p⟩

theorem associated_graded_calculation : Specs.AssociatedGraded.{u} := by
  intro k _
  exact ⟨gradedTerm_subsingleton_of_neg, fun p hp =>
    ⟨gradedCoefficient_injective p hp, gradedCoefficient_surjective p hp⟩,
    gradedDifferential_eq_id, productGradedDifferential_eq_id⟩

theorem same_zero_page_calculation : Specs.SameZeroPage.{u} := by
  intro k _ p
  exact ⟨⟨gradedComparison_injective p, gradedComparison_surjective p⟩,
    gradedComparison_commutes p⟩

theorem pages_calculation : Specs.Pages.{u} := by
  intro k _ r p q hr
  exact page_subsingleton r p q hr

section CompletionBridge
variable (k)

theorem inverseLimitDifferential_extends :
    inverseLimitDifferential k ∘ₗ intoCompletion k = intoCompletion k ∘ₗ differential k := by
  apply LinearMap.ext
  intro a
  rfl

theorem inverseLimitDifferential_intertwines :
    completionToProduct k ∘ₗ inverseLimitDifferential k =
      completedDifferential k ∘ₗ completionToProduct k := by
  apply LinearMap.ext
  intro x
  funext i
  cases i with
  | zero =>
      obtain ⟨a, ha⟩ := (tail k 1).mkQ_surjective (x.1 1)
      change quotientPrefix k 1 (tailQuotientDifferential k 1 (x.1 1)) ⟨0, by omega⟩ = _
      rw [← ha]
      change differential k a 0 = quotientPrefix k 1 (x.1 1) ⟨0, by omega⟩
      rw [← ha]
      exact differential_zero_apply a
  | succ i =>
      have h0 := completionToProduct_prefix x (i+2) (⟨i+1, by omega⟩ : Fin (i+2))
      have h1 := completionToProduct_prefix x (i+2) (⟨i, by omega⟩ : Fin (i+2))
      change quotientPrefix k (i+2) (tailQuotientDifferential k (i+2) (x.1 (i+2))) ⟨i+1, by omega⟩ =
        completionToProduct k x (i+1) - completionToProduct k x i
      rw [h0, h1]
      obtain ⟨a, ha⟩ := (tail k (i+2)).mkQ_surjective (x.1 (i+2))
      rw [← ha]
      exact differential_succ_apply a i

/-- Acyclicity of the two-term completed complex, on its actual inverse-limit terms. -/
theorem inverseLimitDifferential_bijective : Function.Bijective (inverseLimitDifferential k) := by
  constructor
  · intro x y h
    apply completionToProduct_injective
    apply completedDifferentialEquiv.injective
    change completedDifferential k (completionToProduct k x) =
      completedDifferential k (completionToProduct k y)
    calc
      _ = completionToProduct k (inverseLimitDifferential k x) :=
        (LinearMap.congr_fun (inverseLimitDifferential_intertwines k) x).symm
      _ = completionToProduct k (inverseLimitDifferential k y) := congrArg _ h
      _ = _ := LinearMap.congr_fun (inverseLimitDifferential_intertwines k) y
  · intro y
    obtain ⟨x, hx⟩ := completionToProduct_surjective
      (partialSums k (completionToProduct k y))
    refine ⟨x, completionToProduct_injective ?_⟩
    calc
      _ = completedDifferential k (completionToProduct k x) :=
        LinearMap.congr_fun (inverseLimitDifferential_intertwines k) x
      _ = completedDifferential k (partialSums k (completionToProduct k y)) := congrArg _ hx
      _ = _ := LinearMap.congr_fun (completedDifferential_partialSums (k := k)) _

theorem inverseLimitTail_iff (p : ℤ) (x : completion k) :
    x ∈ inverseLimitTail k p ↔ completionToProduct k x ∈ productTail k p := by
  change x.1 p.toNat = 0 ↔ ∀ i : ℕ, (i : ℤ) < p → completionToProduct k x i = 0
  constructor
  · intro hx i hi
    have hit : i < p.toNat := by omega
    rw [completionToProduct_prefix x p.toNat ⟨i, hit⟩, hx]
    rfl
  · intro hx
    apply quotientPrefix_injective
    funext i
    rw [← completionToProduct_prefix]
    exact hx i (by omega)

theorem inverseLimitTail_map (p : ℤ) :
    (inverseLimitTail k p).map (completionToProduct k) = productTail k p := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (inverseLimitTail_iff k p x).mp hx
  · intro b hb
    obtain ⟨x, rfl⟩ := completionToProduct_surjective b
    exact Submodule.mem_map.mpr ⟨x, (inverseLimitTail_iff k p x).mpr hb, rfl⟩

theorem integerCompletionRestriction_comparison :
    integerCompletionRestriction k ∘ₗ intoIntegerCompletion k = intoCompletion k := by
  rfl

theorem integerQuotientTransition_self (p : ℤ) (h : p ≤ p)
    (x : FiniteSequences k ⧸ tail k p) :
    integerQuotientTransition k p p h x = x := by
  obtain ⟨a, rfl⟩ := (tail k p).mkQ_surjective x
  rfl

theorem integerQuotientTransition_comp (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r)
    (x : FiniteSequences k ⧸ tail k r) :
    integerQuotientTransition k p q hpq (integerQuotientTransition k q r hqr x) =
      integerQuotientTransition k p r (le_trans hpq hqr) x := by
  obtain ⟨a, rfl⟩ := (tail k r).mkQ_surjective x
  rfl

theorem integerCompletionRestriction_extension (x : completion k) :
    integerCompletionRestriction k (integerCompletionExtension k x) = x := by
  apply Subtype.ext
  funext n
  change integerQuotientTransition k (n : ℤ) (n : ℤ).toNat _ (x.1 (n : ℤ).toNat) = x.1 n
  simp only [Int.toNat_natCast]
  exact integerQuotientTransition_self k n _ _

theorem integerCompletionExtension_restriction (x : integerCompletion k) :
    integerCompletionExtension k (integerCompletionRestriction k x) = x := by
  apply Subtype.ext
  funext p
  exact x.2 p p.toNat (by omega)

theorem integerCompletionRestriction_bijective :
    Function.Bijective (integerCompletionRestriction k) := by
  constructor
  · intro x y h
    have := congrArg (integerCompletionExtension k) h
    simpa only [integerCompletionExtension_restriction] using this
  · intro x
    exact ⟨integerCompletionExtension k x, integerCompletionRestriction_extension k x⟩

theorem completion_bridge_calculation : Specs.CompletionBridge.{u} := by
  intro k _
  exact ⟨integerCompletionRestriction_bijective k,
    integerCompletionRestriction_comparison k, inverseLimitDifferential_extends k,
    inverseLimitDifferential_intertwines k, inverseLimitDifferential_bijective k,
    inverseLimitTail_map k⟩
end CompletionBridge

section TwoTerm
variable {M N : ModuleCat.{u} k}

@[simp] theorem twoTerm_X0 (f : M ⟶ N) : (twoTerm f).X 0 = M := by simp [twoTerm, twoTermX]
@[simp] theorem twoTerm_X1 (f : M ⟶ N) : (twoTerm f).X 1 = N := by simp [twoTerm, twoTermX]
@[simp] theorem twoTerm_d01 (f : M ⟶ N) : (twoTerm f).d 0 1 = f := by
  change CochainComplex.of.d (twoTermX M N) (twoTermD f) 0 (0+1) = f
  rw [CochainComplex.of_d]
  rfl

@[simp] theorem twoTerm_d_succ_ne0 (f : M ⟶ N) (n : ℤ) (h : n ≠ 0) :
    (twoTerm f).d n (n+1) = 0 := by
  rw [show (twoTerm f).d n (n+1) = CochainComplex.of.d (twoTermX M N) (twoTermD f) n (n+1) from rfl,
    CochainComplex.of_d]
  simp [twoTermD, h]
  rfl

noncomputable def twoTerm_firstHomologyIso (f : M ⟶ N) :
    (twoTerm f).homology 1 ≅ ModuleCat.of k (N ⧸ LinearMap.range f.hom) := by
  let S := (twoTerm f).sc' 0 1 2
  have hg : S.g = 0 := twoTerm_d_succ_ne0 f 1 (by decide)
  have := S.isIso_homologyι hg
  refine (twoTerm f).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    asIso S.homologyι ≪≫ S.moduleCatOpcyclesIso ≪≫ ?_
  exact eqToIso (by change ModuleCat.of k (N ⧸ LinearMap.range ((twoTerm f).d 0 1).hom) = _; rw [twoTerm_d01]; rfl)

 theorem twoTerm_homology_zero (f : M ⟶ N) (hf : Function.Injective f) :
    IsZero ((twoTerm f).homology 0) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  rw [(twoTerm f).exactAt_iff' (-1) 0 1 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx0 : x = 0 := hf (hx.trans (f.hom.map_zero).symm)
  subst x
  exact ⟨0, map_zero _⟩

 theorem twoTerm_homology_other (f : M ⟶ N) (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    IsZero ((twoTerm f).homology n) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change IsZero (twoTermX M N n)
  simp only [twoTermX, ite_eq_right h0, ite_eq_right h1]
  exact ModuleCat.isZero_of_subsingleton _
theorem twoTerm_homology_one_zero (f : M ⟶ N) (hf : Function.Surjective f) :
    IsZero ((twoTerm f).homology 1) := by
  have h : IsZero (ModuleCat.of k (N ⧸ LinearMap.range f.hom)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (N ⧸ LinearMap.range f.hom)
    have hr : LinearMap.range f.hom = ⊤ := LinearMap.range_eq_top.mpr hf
    rw [hr]
    infer_instance
  exact h.of_iso (twoTerm_firstHomologyIso f)
end TwoTerm

section ComplexCohomology
variable (k)

/-- The concrete quotient is the categorical H¹ of the original complex. -/
def originalComplex_firstHomologyIso :
    (originalComplex k).homology 1 ≅ ModuleCat.of k (firstCohomology k) :=
  twoTerm_firstHomologyIso (ModuleCat.ofHom (differential k))

/-- The coefficient-sum identification of the categorical H¹. -/
def originalComplex_firstHomologyIsoField :
    (originalComplex k).homology 1 ≅ ModuleCat.of k k :=
  originalComplex_firstHomologyIso k ≪≫ (firstCohomologyEquiv (k := k)).toModuleIso

theorem originalComplex_homology_zero : IsZero ((originalComplex k).homology 0) :=
  twoTerm_homology_zero (ModuleCat.ofHom (differential k)) differential_injective

theorem originalComplex_homology_other (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    IsZero ((originalComplex k).homology n) :=
  twoTerm_homology_other _ n h0 h1

theorem completedComplex_acyclic (n : ℤ) : IsZero ((completedComplex k).homology n) := by
  by_cases h0 : n = 0
  · subst n
    exact twoTerm_homology_zero _ (completedDifferentialEquiv (k := k)).injective
  · by_cases h1 : n = 1
    · subst n
      exact twoTerm_homology_one_zero _ (completedDifferentialEquiv (k := k)).surjective
    · exact twoTerm_homology_other _ n h0 h1
theorem complex_cohomology_calculation : Specs.ComplexCohomology.{u} := by
  intro k _
  exact ⟨originalComplex_homology_zero k, ⟨originalComplex_firstHomologyIso k⟩,
    ⟨originalComplex_firstHomologyIsoField k⟩, originalComplex_homology_other k,
    completedComplex_acyclic k⟩

end ComplexCohomology

section IntegerCompletionFiltration
variable (k)

theorem tail_toNat_eq (p : ℤ) : tail k p = tail k (p.toNat : ℤ) := by
  ext a
  constructor <;> intro ha i hi <;> exact ha i (by omega)

theorem integerQuotientTransition_injective (p q : ℤ) (h : p ≤ q)
    (ht : tail k p = tail k q) :
    Function.Injective (integerQuotientTransition k p q h) := by
  intro x y hh
  obtain ⟨a, rfl⟩ := (tail k q).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (tail k q).mkQ_surjective y
  apply (Submodule.Quotient.eq _).mpr
  rw [← ht]
  exact (Submodule.Quotient.eq _).mp hh

theorem integerCompletionTail_restriction_iff (p : ℤ) (x : integerCompletion k) :
    x ∈ integerCompletionTail k p ↔
      integerCompletionRestriction k x ∈ inverseLimitTail k p := by
  change x.1 p = 0 ↔ x.1 p.toNat = 0
  have hc := x.2 p p.toNat (by omega)
  constructor
  · intro hp
    apply integerQuotientTransition_injective k p p.toNat (by omega) (tail_toNat_eq k p)
    rw [map_zero, hc, hp]
  · intro hn
    rw [← hc, hn, map_zero]

theorem integerCompletionTail_restriction (p : ℤ) :
    (integerCompletionTail k p).map (integerCompletionRestriction k) = inverseLimitTail k p := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (integerCompletionTail_restriction_iff k p x).mp hx
  · intro x hx
    obtain ⟨y, rfl⟩ := (integerCompletionRestriction_bijective k).surjective x
    exact Submodule.mem_map.mpr ⟨y, (integerCompletionTail_restriction_iff k p y).mpr hx, rfl⟩

theorem integerCompletionTail_map (p : ℤ) :
    (integerCompletionTail k p).map
      ((completionToProduct k).comp (integerCompletionRestriction k)) = productTail k p := by
  rw [Submodule.map_comp, integerCompletionTail_restriction, inverseLimitTail_map]

theorem integer_completion_filtration_calculation : Specs.IntegerCompletionFiltration.{u} := by
  intro k _ p
  exact integerCompletionTail_map k p
end IntegerCompletionFiltration

section TwoTermMaps
variable {M N M' N' : ModuleCat.{u} k}

def twoTermMapComponent (a : M ⟶ M') (b : N ⟶ N') (n : ℤ) :
    twoTermX M N n ⟶ twoTermX M' N' n := by
  by_cases h0 : n = 0
  · subst n; exact a
  · by_cases h1 : n = 1
    · subst n; exact b
    · exact 0

def twoTermMap (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : a ≫ g = f ≫ b) : twoTerm f ⟶ twoTerm g :=
  CochainComplex.ofHom (twoTermMapComponent a b) (by
    intro n
    by_cases h0 : n = 0
    · subst n
      change a ≫ (twoTerm g).d 0 1 = (twoTerm f).d 0 1 ≫ b
      rw [twoTerm_d01, twoTerm_d01]
      exact h
    · rw [twoTerm_d_succ_ne0 g n h0, twoTerm_d_succ_ne0 f n h0]
      exact (comp_zero).trans (zero_comp).symm)

@[simp] theorem twoTermMap_f0 (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : a ≫ g = f ≫ b) : (twoTermMap f g a b h).f 0 = a := rfl
@[simp] theorem twoTermMap_f1 (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : a ≫ g = f ≫ b) : (twoTermMap f g a b h).f 1 = b := rfl

def twoTermIso (f : M ⟶ N) (g : M' ⟶ N') (a : M ≅ M') (b : N ≅ N')
    (h : a.hom ≫ g = f ≫ b.hom) : twoTerm f ≅ twoTerm g where
  hom := twoTermMap f g a.hom b.hom h
  inv := twoTermMap g f a.inv b.inv (by
    apply (cancel_mono b.hom).mp
    simp only [Category.assoc, b.inv_hom_id, Category.comp_id]
    rw [← h, ← Category.assoc, a.inv_hom_id, Category.id_comp])
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    by_cases h0 : n = 0
    · subst n
      change a.hom ≫ a.inv = 𝟙 _
      exact a.hom_inv_id
    · by_cases h1 : n = 1
      · subst n
        change b.hom ≫ b.inv = 𝟙 _
        exact b.hom_inv_id
      · have : Subsingleton ((twoTerm f).X n) := by
          change Subsingleton (twoTermX M N n)
          simp only [twoTermX, ite_eq_right h0, ite_eq_right h1]
          infer_instance
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    by_cases h0 : n = 0
    · subst n
      change a.inv ≫ a.hom = 𝟙 _
      exact a.inv_hom_id
    · by_cases h1 : n = 1
      · subst n
        change b.inv ≫ b.hom = 𝟙 _
        exact b.inv_hom_id
      · have : Subsingleton ((twoTerm g).X n) := by
          change Subsingleton (twoTermX M' N' n)
          simp only [twoTermX, ite_eq_right h0, ite_eq_right h1]
          infer_instance
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _

end TwoTermMaps

section GradedComplexes
variable (k)

theorem originalGradedComplex_acyclic (p n : ℤ) :
    IsZero ((originalGradedComplex k p).homology n) := by
  have hd : Function.Bijective (gradedDifferential k p) := by
    rw [gradedDifferential_eq_id]
    exact Function.bijective_id
  by_cases h0 : n = 0
  · subst n
    exact twoTerm_homology_zero _ hd.1
  · by_cases h1 : n = 1
    · subst n
      exact twoTerm_homology_one_zero _ hd.2
    · exact twoTerm_homology_other _ n h0 h1

theorem completedGradedComplex_acyclic (p n : ℤ) :
    IsZero ((completedGradedComplex k p).homology n) := by
  have hd : Function.Bijective (productGradedDifferential k p) := by
    rw [productGradedDifferential_eq_id]
    exact Function.bijective_id
  by_cases h0 : n = 0
  · subst n
    exact twoTerm_homology_zero _ hd.1
  · by_cases h1 : n = 1
    · subst n
      exact twoTerm_homology_one_zero _ hd.2
    · exact twoTerm_homology_other _ n h0 h1

/-- The associated graded comparison is an isomorphism of E₀ complexes,
using the actual quotient map induced by the sum-to-product embedding. -/
def gradedComplexIso (p : ℤ) : originalGradedComplex k p ≅ completedGradedComplex k p :=
  twoTermIso (ModuleCat.ofHom (gradedDifferential k p))
    (ModuleCat.ofHom (productGradedDifferential k p))
    (gradedComparisonEquiv (k := k) p).toModuleIso
    (gradedComparisonEquiv (k := k) p).toModuleIso (by
      apply ModuleCat.hom_ext
      exact gradedComparison_commutes p)

@[simp] theorem gradedComplexIso_hom_f0 (p : ℤ) :
    (gradedComplexIso k p).hom.f 0 = ModuleCat.ofHom (gradedComparison k p) := rfl
@[simp] theorem gradedComplexIso_hom_f1 (p : ℤ) :
    (gradedComplexIso k p).hom.f 1 = ModuleCat.ofHom (gradedComparison k p) := rfl
theorem graded_complexes_calculation : Specs.GradedComplexes.{u} := by
  intro k _
  exact ⟨originalGradedComplex_acyclic k, completedGradedComplex_acyclic k,
    fun p => ⟨gradedComplexIso k p, gradedComplexIso_hom_f0 k p, gradedComplexIso_hom_f1 k p⟩⟩

end GradedComplexes

section LimitComplex
variable (k)

/-- The inverse limit of the tail-quotient complex is identified with
the explicit product complex through its canonical coefficient map. -/
def inverseLimitComplexIso : inverseLimitComplex k ≅ completedComplex k :=
  twoTermIso (ModuleCat.ofHom (inverseLimitDifferential k))
    (ModuleCat.ofHom (completedDifferential k))
    (completionEquivProduct (k := k)).toModuleIso
    (completionEquivProduct (k := k)).toModuleIso (by
      apply ModuleCat.hom_ext
      exact (inverseLimitDifferential_intertwines k).symm)

theorem inverseLimitComplex_acyclic (n : ℤ) :
    IsZero ((inverseLimitComplex k).homology n) := by
  have hd := inverseLimitDifferential_bijective k
  by_cases h0 : n = 0
  · subst n
    exact twoTerm_homology_zero _ hd.1
  · by_cases h1 : n = 1
    · subst n
      exact twoTerm_homology_one_zero _ hd.2
    · exact twoTerm_homology_other _ n h0 h1

@[simp] theorem inverseLimitComplexIso_hom_f0 :
    (inverseLimitComplexIso k).hom.f 0 = ModuleCat.ofHom (completionToProduct k) := rfl
@[simp] theorem inverseLimitComplexIso_hom_f1 :
    (inverseLimitComplexIso k).hom.f 1 = ModuleCat.ofHom (completionToProduct k) := rfl

/-- The actual completeness comparison, as a map of complexes. -/
def intoCompletionComplexMap : originalComplex k ⟶ inverseLimitComplex k :=
  twoTermMap (ModuleCat.ofHom (differential k))
    (ModuleCat.ofHom (inverseLimitDifferential k))
    (ModuleCat.ofHom (intoCompletion k))
    (ModuleCat.ofHom (intoCompletion k)) (by
      apply ModuleCat.hom_ext
      exact inverseLimitDifferential_extends k)

def sumToProductComplexMap : originalComplex k ⟶ completedComplex k :=
  twoTermMap (ModuleCat.ofHom (differential k))
    (ModuleCat.ofHom (completedDifferential k))
    (ModuleCat.ofHom (toProduct k))
    (ModuleCat.ofHom (toProduct k)) (by
      apply ModuleCat.hom_ext
      exact completedDifferential_extends)
theorem limit_complex_calculation : Specs.LimitComplex.{u} := by
  intro k _
  exact ⟨inverseLimitComplex_acyclic k, ⟨inverseLimitComplexIso k,
    inverseLimitComplexIso_hom_f0 k, inverseLimitComplexIso_hom_f1 k⟩⟩

end LimitComplex

section PageBridge

variable {k : Type u} [Field k]
/-- The all-degree F03 pages vanish from page one onward. -/
theorem ambientPage_subsingleton (r p n : ℤ) (hr : 1 ≤ r) :
    Subsingleton (ambientPage k r p n) := by
  have e := ambientPageEquiv (k := k) r p (n-p)
  have := page_subsingleton (k := k) r p (n-p) hr
  have : Subsingleton (ambientPage k r p (p+(n-p))) := e.injective.subsingleton
  simpa using (inferInstance : Subsingleton (ambientPage k r p (p+(n-p))))

theorem ambientPageDifferential_representative (r p n : ℤ) (hr : 1 ≤ r) :
    ambientPageDifferential k r p n ∘ₗ ambientToPage k r p n =
      ambientToPage k r (p+r) (n+1) ∘ₗ ambientAlmostDifferential k r p n := by
  have := ambientPage_subsingleton (k := k) r (p+r) (n+1) hr
  exact Subsingleton.elim _ _


theorem page_bridge_calculation : Specs.PageBridge.{u} := by
  intro k _
  exact ⟨ambientTail_le_term, ambientRestrictedDifferential_square_zero,
    ambientRestrictedTail_map, ambientRestrictedDifferential_mem,
    ambientBoundaries_le_cycles, (fun r p q => ⟨ambientPageEquiv r p q⟩),
    (fun p n => ⟨ambientZeroPageEquiv p n⟩), ambientZeroPageEquiv_representative,
    ambientZeroPageDifferential_representative, ambientPageDifferential_representative,
    ambientPage_subsingleton, ambientGradedDifferential_zero,
    ambientGradedDifferential_other⟩

end PageBridge

section PageBridgeTerms

variable {k : Type u} [Field k]
theorem originalTermEquiv_differential (n : ℤ) :
    (originalTermEquiv k (n+1)).toLinearMap ∘ₗ ((originalComplex k).d n (n+1)).hom =
      ambientRestrictedDifferential k n ∘ₗ (originalTermEquiv k n).toLinearMap := by
  by_cases h : n = 0
  · subst n
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change differential k a = differential k a
    rfl
  · rw [show (originalComplex k).d n (n+1) = 0 from
      twoTerm_d_succ_ne0 (ModuleCat.ofHom (differential k)) n h]
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    simp only [LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
    change 0 = ambientDifferential k n _
    simp [ambientDifferential_other n h]

theorem ambientRestrictedTail_exhaustive (n : ℤ) :
    (⨆ p : ℤ, ambientRestrictedTail k p n) = ⊤ := by
  apply top_unique
  have hz : ambientRestrictedTail k 0 n = ⊤ := by
    unfold ambientRestrictedTail
    rw [tail_zero, Submodule.comap_top]
  rw [← hz]
  exact le_iSup (ambientRestrictedTail k · n) 0

theorem ambientRestrictedTail_separated (n : ℤ) :
    (⨅ p : ℤ, ambientRestrictedTail k p n) = ⊥ := by
  unfold ambientRestrictedTail
  rw [← Submodule.comap_iInf, tail_separated, Submodule.comap_bot, Submodule.ker_subtype]

theorem page_bridge_terms_calculation : Specs.PageBridgeTerms.{u} := by
  intro k _
  exact ⟨originalTermEquiv_differential, ambientRestrictedTail_exhaustive,
    ambientRestrictedTail_separated⟩

end PageBridgeTerms

theorem ambientGradedDifferential_square_zero (p n : ℤ) :
    ambientGradedDifferential k p (n+1) ∘ₗ ambientGradedDifferential k p n = 0 := by
  by_cases hn : n = 0
  · subst n
    rw [ambientGradedDifferential_other (k := k) p (0+1) (by omega)]
    simp
  · rw [ambientGradedDifferential_other p n hn]
    simp

theorem ambientZeroPageDifferential_square_zero (p n : ℤ) :
    ambientZeroPageDifferential k p (n+1) ∘ₗ ambientZeroPageDifferential k p n = 0 := by
  apply LinearMap.ext
  intro a
  apply (ambientZeroPageEquiv (k := k) p ((n+1)+1)).injective
  simp only [ambientZeroPageDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero]
  exact LinearMap.congr_fun (ambientGradedDifferential_square_zero p n)
    ((ambientZeroPageEquiv p n) a)

theorem ambientPageDifferential_square_zero (r p n : ℤ) (hr : 1 ≤ r) :
    ambientPageDifferential k r (p+r) (n+1) ∘ₗ ambientPageDifferential k r p n = 0 := by
  have := ambientPage_subsingleton (k := k) r ((p+r)+r) ((n+1)+1) hr
  exact Subsingleton.elim _ _

theorem page_differentials_calculation : Specs.PageDifferentials.{u} := by
  intro k _
  exact ⟨ambientGradedDifferential_square_zero, ambientZeroPageDifferential_square_zero,
    ambientPageDifferential_square_zero⟩

/-- The unchanged full example: zero stable pages, nonseparated H¹, and an
acyclic tail completion with the same E₀ complex. -/
theorem nonseparated_cohomology_example : Specs.CompleteExample.{u} := by
  exact ⟨cohomology_calculation,
    filtration_calculation,
    completed_differential_calculation,
    completion_calculation,
    graded_representative_calculation,
    cohomology_completion_calculation,
    acyclicity_calculation,
    induced_filtration_calculation,
    associated_graded_calculation,
    same_zero_page_calculation,
    pages_calculation,
    completion_bridge_calculation,
    complex_cohomology_calculation,
    integer_completion_filtration_calculation,
    graded_complexes_calculation,
    limit_complex_calculation,
    page_bridge_calculation,
    page_bridge_terms_calculation,
    page_differentials_calculation⟩

end AdvancedHomologicalAlgebra.NonseparatedExample
