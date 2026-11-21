import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Concrete sequence model for HA-S07 (source lines 667–701).
`ℕ →₀ k` is the direct sum with its given bases. Integer tails are defined
by vanishing at indices below `p`, equivalently support in `i ≥ max(p,0)`.
These independent definitions do not assume any of the example's conclusions.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u
namespace AdvancedHomologicalAlgebra.NonseparatedExample
abbrev FiniteSequences (k : Type u) [Zero k] := ℕ →₀ k
abbrev Sequences (k : Type u) := ℕ → k

variable (k : Type u) [Field k]

/-- The basis map `eᵢ ↦ fᵢ - fᵢ₊₁`. -/
def differential : FiniteSequences k →ₗ[k] FiniteSequences k :=
  LinearMap.id - Finsupp.lmapDomain k k Nat.succ

section
variable {k}
@[simp] theorem differential_single (i : ℕ) (c : k) :
    differential k (Finsupp.single i c) =
      Finsupp.single i c - Finsupp.single (i+1) c := by
  simp [differential]

@[simp] theorem differential_zero_apply (a : FiniteSequences k) :
    differential k a 0 = a 0 := by
  simp only [differential, LinearMap.sub_apply, LinearMap.id_apply,
    Finsupp.lmapDomain_apply, Finsupp.sub_apply]
  rw [Finsupp.mapDomain_of_notMem_range a 0 (by simp)]
  simp

@[simp] theorem differential_succ_apply (a : FiniteSequences k) (i : ℕ) :
    differential k a (i+1) = a (i+1) - a i := by
  simp [differential, Finsupp.mapDomain_apply_of_injective Nat.succ_injective]

end
/-- Sum of all coefficients of a finite sequence. -/
def coefficientSum : FiniteSequences k →ₗ[k] k :=
  Finsupp.linearCombination k (fun _ : ℕ => (1 : k))

/-- The original decreasing, integer-indexed tail filtration. -/
def tail (p : ℤ) : Submodule k (FiniteSequences k) where
  carrier := {a | ∀ i : ℕ, (i : ℤ) < p → a i = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  smul_mem' := by intro c a ha i hi; simp [ha i hi]

section
variable {k}
@[simp] theorem mem_tail (p : ℤ) (a : FiniteSequences k) :
    a ∈ tail k p ↔ ∀ i : ℕ, (i : ℤ) < p → a i = 0 := Iff.rfl

theorem tail_antitone (p : ℤ) : tail k (p+1) ≤ tail k p := by
  intro a ha i hi
  exact ha i (by omega)

theorem differential_mem_tail (p : ℤ) (a : FiniteSequences k) (ha : a ∈ tail k p) :
    differential k a ∈ tail k p := by
  intro i hi
  cases i with
  | zero => simp [ha 0 hi]
  | succ i => simp [ha (i+1) hi, ha i (by omega)]

end
/-- The differential on the product, with the same matrix as on the sum. -/
def completedDifferential : Sequences k →ₗ[k] Sequences k where
  toFun a n := match n with
    | 0 => a 0
    | i+1 => a (i+1) - a i
  map_add' a b := by ext n; cases n <;> simp; abel
  map_smul' c a := by ext n; cases n <;> simp [mul_sub]

/-- The recurrence solving the completed differential. -/
def partialSums : Sequences k →ₗ[k] Sequences k where
  toFun b i := ∑ j ∈ Finset.range (i+1), b j
  map_add' a b := by ext i; simp [Finset.sum_add_distrib]
  map_smul' c a := by ext i; simp [Finset.mul_sum]

/-- The direct sum embeds in the product by taking coefficients. -/
def toProduct : FiniteSequences k →ₗ[k] Sequences k where
  toFun a := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two-term complex's degree-one cohomology in its concrete quotient model. -/
abbrev firstCohomology := FiniteSequences k ⧸ LinearMap.range (differential k)

/-- Image filtration on degree-one cohomology. -/
def cohomologyTail (p : ℤ) : Submodule k (firstCohomology k) :=
  (tail k p).map (LinearMap.range (differential k)).mkQ

/-- Truncation to the first `m` coefficients. -/
def finitePrefix (m : ℕ) : FiniteSequences k →ₗ[k] (Fin m → k) where
  toFun a i := a i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The quotient by a tail has a canonical finite-prefix map. -/
def quotientPrefix (m : ℕ) : (FiniteSequences k ⧸ tail k m) →ₗ[k] (Fin m → k) :=
  (tail k m).liftQ (finitePrefix k m) (by
    intro a ha
    change finitePrefix k m a = 0
    funext i
    exact ha i (by exact_mod_cast i.isLt))

/-- Transition in the tower of actual quotients by tails. -/
def quotientTransition (m n : ℕ) (h : m ≤ n) :
    (FiniteSequences k ⧸ tail k n) →ₗ[k] (FiniteSequences k ⧸ tail k m) :=
  (tail k n).liftQ (tail k m).mkQ (by
    intro a ha
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    intro i hi
    exact ha i (lt_of_lt_of_le hi (by exact_mod_cast h)))

/-- The tail completion, explicitly the inverse limit of the quotient tower. -/
def completion : Submodule k (∀ m : ℕ, FiniteSequences k ⧸ tail k m) where
  carrier := {x | ∀ m n (h : m ≤ n), quotientTransition k m n h (x n) = x m}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb m n h; simp [ha m n h, hb m n h]
  smul_mem' := by intro c a ha m n h; simp [ha m n h]

/-- Recover the `i`th coefficient from any sufficiently long prefix. -/
def completionToProduct : completion k →ₗ[k] Sequences k where
  toFun x i := quotientPrefix k (i+1) (x.1 (i+1)) ⟨i, Nat.lt_succ_self i⟩
  map_add' a b := by ext i; simp
  map_smul' c a := by ext i; simp

/-- The canonical comparison from the sum to its tail completion. -/
def intoCompletion : FiniteSequences k →ₗ[k] completion k where
  toFun a := ⟨fun m => (tail k m).mkQ a, by
    intro m n h
    rfl⟩
  map_add' a b := by apply Subtype.ext; funext m; exact map_add _ a b
  map_smul' c a := by apply Subtype.ext; funext m; exact map_smul _ c a

/-- Quotient transition for the image filtration on cohomology. -/
def cohomologyTransition (p q : ℤ) (h : p ≤ q) :
    (firstCohomology k ⧸ cohomologyTail k q) →ₗ[k]
      (firstCohomology k ⧸ cohomologyTail k p) :=
  (cohomologyTail k q).liftQ (cohomologyTail k p).mkQ (by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨a, (fun i hi => ha i (lt_of_lt_of_le hi h)), rfl⟩)

instance cohomologyQuotientGroups : ∀ p : ℤ,
    AddCommGroup (firstCohomology k ⧸ cohomologyTail k p) :=
  fun p => Submodule.Quotient.addCommGroup (cohomologyTail k p)

instance cohomologyQuotientModules : ∀ p : ℤ,
    Module k (firstCohomology k ⧸ cohomologyTail k p) :=
  fun p => Submodule.Quotient.module (cohomologyTail k p)

/-- The inverse limit occurring as the codomain of the completeness comparison.
Here all integer indices are retained. -/
def cohomologyCompletion : Submodule k
    (∀ p : ℤ, firstCohomology k ⧸ cohomologyTail k p) where
  carrier := {x | ∀ p q (h : p ≤ q), cohomologyTransition k p q h (x q) = x p}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb p q h; simp [ha p q h, hb p q h]
  smul_mem' := by intro c a ha p q h; simp [ha p q h]

/-- The actual canonical completeness comparison on degree-one cohomology. -/
def cohomologyComparison : firstCohomology k →ₗ[k] cohomologyCompletion k where
  toFun a := ⟨fun p => (cohomologyTail k p).mkQ a, by intro p q h; rfl⟩
  map_add' a b := by apply Subtype.ext; funext p; exact map_add _ a b
  map_smul' c a := by apply Subtype.ext; funext p; exact map_smul _ c a


/-- The completion has the product tail filtration, with all integer indices. -/
def productTail (p : ℤ) : Submodule k (Sequences k) where
  carrier := {a | ∀ i : ℕ, (i : ℤ) < p → a i = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  smul_mem' := by intro c a ha i hi; simp [ha i hi]

theorem completedDifferential_mem_productTail (p : ℤ) (a : Sequences k)
    (ha : a ∈ productTail k p) : completedDifferential k a ∈ productTail k p := by
  intro i hi
  cases i with
  | zero => exact ha 0 hi
  | succ i => simp [completedDifferential, ha (i+1) hi, ha i (by omega)]

/-- The actual successive-tail quotient, realized as the image of the tail in
its ambient quotient. This is canonically `F^p/F^(p+1)`. -/
def gradedTerm (p : ℤ) : Submodule k (FiniteSequences k ⧸ tail k (p+1)) :=
  (tail k p).map (tail k (p+1)).mkQ

def productGradedTerm (p : ℤ) : Submodule k (Sequences k ⧸ productTail k (p+1)) :=
  (productTail k p).map (productTail k (p+1)).mkQ

/-- Ambient quotient map induced by the original differential. -/
def quotientDifferential (p : ℤ) :
    (FiniteSequences k ⧸ tail k (p+1)) →ₗ[k] (FiniteSequences k ⧸ tail k (p+1)) :=
  (tail k (p+1)).mapQ (tail k (p+1)) (differential k)
    (differential_mem_tail (p+1))

/-- The differential on each nonzero pair of terms of `gr^p K`. -/
def gradedDifferential (p : ℤ) : gradedTerm k p →ₗ[k] gradedTerm k p :=
  (quotientDifferential k p).restrict (by
    rintro x ⟨a, ha, rfl⟩
    exact Submodule.mem_map.mpr ⟨differential k a, differential_mem_tail p a ha, rfl⟩)

def productQuotientDifferential (p : ℤ) :
    (Sequences k ⧸ productTail k (p+1)) →ₗ[k] (Sequences k ⧸ productTail k (p+1)) :=
  (productTail k (p+1)).mapQ (productTail k (p+1)) (completedDifferential k)
    (completedDifferential_mem_productTail k (p+1))

def productGradedDifferential (p : ℤ) :
    productGradedTerm k p →ₗ[k] productGradedTerm k p :=
  (productQuotientDifferential k p).restrict (by
    rintro x ⟨a, ha, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨completedDifferential k a, completedDifferential_mem_productTail k p a ha, rfl⟩)

/-- The associated graded comparison induced by the canonical sum-to-product map. -/
def quotientComparison (p : ℤ) :
    (FiniteSequences k ⧸ tail k (p+1)) →ₗ[k] (Sequences k ⧸ productTail k (p+1)) :=
  (tail k (p+1)).mapQ (productTail k (p+1)) (toProduct k) (by
    intro a ha; exact ha)

def gradedComparison (p : ℤ) : gradedTerm k p →ₗ[k] productGradedTerm k p :=
  (quotientComparison k p).restrict (by
    rintro x ⟨a, ha, rfl⟩
    exact Submodule.mem_map.mpr ⟨toProduct k a, ha, rfl⟩)

/-- `A_r^{p,0}` from HA-F03, specialized to the actual differential. -/
def almostZero (r p : ℤ) : Submodule k (FiniteSequences k) :=
  tail k p ⊓ (tail k (p+r)).comap (differential k)

/-- `Z_r^{p,-p}` in degree zero. There are no incoming boundaries in this degree. -/
def cyclesZero (r p : ℤ) : Submodule k (FiniteSequences k ⧸ tail k (p+1)) :=
  (almostZero k r p).map (tail k (p+1)).mkQ

/-- `B_r^{p,1-p}` in degree one. The cycles in degree one are the whole graded term. -/
def boundariesOne (r p : ℤ) : Submodule k (FiniteSequences k ⧸ tail k (p+1)) :=
  (tail k p ⊓ (tail k (p-r+1)).map (differential k)).map (tail k (p+1)).mkQ

/-- The page in degree zero is literally `Z_r/0`. -/
def pageZero (r p : ℤ) := cyclesZero k r p ⧸ (⊥ : Submodule k (cyclesZero k r p))

/-- The page in degree one is literally `Z_r/B_r`, with the boundary submodule
pulled back to the cycle module. These are the full formulas in HA-F03. -/
def pageOne (r p : ℤ) :=
  gradedTerm k p ⧸ (boundariesOne k r p).comap (gradedTerm k p).subtype

/-- All bidegrees of the actual two-term spectral-sequence page. Outside total
degrees zero and one the original complex, and hence every page, is zero. -/
def page (r p q : ℤ) : Type u :=
  if p+q = 0 then pageZero k r p else
  if p+q = 1 then pageOne k r p else (Fin 0 → k)

/-- The differential on the filtration subcomplex in its two nonzero degrees. -/
def tailDifferential (p : ℤ) : tail k p →ₗ[k] tail k p :=
  (differential k).restrict (differential_mem_tail p)

instance tailGroups (p : ℤ) : AddCommGroup (tail k p) := (tail k p).addCommGroup
instance tailModules (p : ℤ) : Module k (tail k p) := (tail k p).module

abbrev tailFirstCohomology (p : ℤ) := (tail k p : Type u) ⧸ LinearMap.range (tailDifferential k p)

/-- Map on degree-one cohomology induced by the subcomplex inclusion. -/
def tailCohomologyInclusion (p : ℤ) : tailFirstCohomology k p →ₗ[k] firstCohomology k :=
  (LinearMap.range (tailDifferential k p)).liftQ
    ((LinearMap.range (differential k)).mkQ.comp (tail k p).subtype) (by
      rintro x ⟨a, rfl⟩
      change (LinearMap.range (differential k)).mkQ (differential k a.1) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a.1, rfl⟩)

abbrev zerothCohomology (k : Type u) [Field k] := LinearMap.ker (differential k)
abbrev completedZerothCohomology (k : Type u) [Field k] :=
  LinearMap.ker (completedDifferential k)
abbrev completedFirstCohomology (k : Type u) [Field k] :=
  Sequences k ⧸ LinearMap.range (completedDifferential k)

/-- The successive quotient of the induced filtration, as its image in the ambient quotient. -/
def cohomologyGradedTerm (k : Type u) [Field k] (p : ℤ) :
    Submodule k (firstCohomology k ⧸ cohomologyTail k (p+1)) :=
  (cohomologyTail k p).map (cohomologyTail k (p+1)).mkQ

def gradedCoefficient (p : ℤ) (hp : 0 ≤ p) : gradedTerm k p →ₗ[k] k :=
  ((tail k (p+1)).liftQ (Finsupp.lapply p.toNat)
    (by
      intro a ha
      exact ha p.toNat (by omega))).comp (gradedTerm k p).subtype

/-- The differential induced on an actual quotient by a tail. -/
def tailQuotientDifferential (m : ℕ) :
    (FiniteSequences k ⧸ tail k m) →ₗ[k] (FiniteSequences k ⧸ tail k m) :=
  (tail k m).mapQ (tail k m) (differential k) (differential_mem_tail m)

theorem tailQuotientDifferential_transition (m n : ℕ) (h : m ≤ n)
    (x : FiniteSequences k ⧸ tail k n) :
    quotientTransition k m n h (tailQuotientDifferential k n x) =
      tailQuotientDifferential k m (quotientTransition k m n h x) := by
  obtain ⟨a, rfl⟩ := (tail k n).mkQ_surjective x
  rfl

/-- The differential on the inverse limit, obtained from the quotient differentials. -/
def inverseLimitDifferential : completion k →ₗ[k] completion k where
  toFun x := ⟨fun m => tailQuotientDifferential k m (x.1 m), by
    intro m n h
    rw [tailQuotientDifferential_transition, x.2 m n h]⟩
  map_add' a b := by apply Subtype.ext; funext m; exact map_add _ _ _
  map_smul' c a := by apply Subtype.ext; funext m; exact map_smul (tailQuotientDifferential k m) c (a.1 m)

/-- Projection to an actual quotient in the inverse system. -/
def inverseLimitProjection (m : ℕ) : completion k →ₗ[k] (FiniteSequences k ⧸ tail k m) where
  toFun x := x.1 m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Filtration induced on the inverse limit by the kernels of the quotient projections. -/
def inverseLimitTail (p : ℤ) : Submodule k (completion k) :=
  LinearMap.ker (inverseLimitProjection k p.toNat)

/-- The inverse-system map with every original integer filtration index retained. -/
def integerQuotientTransition (p q : ℤ) (h : p ≤ q) :
    (FiniteSequences k ⧸ tail k q) →ₗ[k] (FiniteSequences k ⧸ tail k p) :=
  (tail k q).liftQ (tail k p).mkQ (by
    intro a ha
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    intro i hi
    exact ha i (lt_of_lt_of_le hi h))

/-- The completion as an inverse limit over all integers. -/
def integerCompletion : Submodule k (∀ p : ℤ, FiniteSequences k ⧸ tail k p) where
  carrier := {x | ∀ p q (h : p ≤ q), integerQuotientTransition k p q h (x q) = x p}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb p q h; simp [ha p q h, hb p q h]
  smul_mem' := by intro c a ha p q h; simp [ha p q h]

/-- Restriction to the cofinal natural-index tower. -/
def integerCompletionRestriction : integerCompletion k →ₗ[k] completion k where
  toFun x := ⟨fun m => x.1 m, by
    intro m n h
    exact x.2 m n (by exact_mod_cast h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical sum-to-completion comparison with every integer index retained. -/
def intoIntegerCompletion : FiniteSequences k →ₗ[k] integerCompletion k where
  toFun a := ⟨fun p => (tail k p).mkQ a, by intro p q h; rfl⟩
  map_add' a b := by apply Subtype.ext; funext p; exact map_add _ _ _
  map_smul' c a := by apply Subtype.ext; funext p; exact map_smul (tail k p).mkQ c a

/-- Extension to all integer indices; nonpositive indices contribute zero quotients. -/
def integerCompletionExtension : completion k →ₗ[k] integerCompletion k where
  toFun x := ⟨fun p => integerQuotientTransition k p p.toNat (by omega) (x.1 p.toNat), by
    intro p q h
    have hn : p.toNat ≤ q.toNat := by omega
    change integerQuotientTransition k p q h
        (integerQuotientTransition k q q.toNat _ (x.1 q.toNat)) =
      integerQuotientTransition k p p.toNat _ (x.1 p.toNat)
    rw [← x.2 p.toNat q.toNat hn]
    obtain ⟨a, ha⟩ := (tail k q.toNat).mkQ_surjective (x.1 q.toNat)
    rw [← ha]
    rfl⟩
  map_add' a b := by apply Subtype.ext; funext p; exact map_add _ _ _
  map_smul' c a := by
    apply Subtype.ext
    funext p
    exact map_smul (integerQuotientTransition k p p.toNat (by omega)) c (a.1 p.toNat)
section TwoTerm
variable {k}
variable {M N : ModuleCat.{u} k}

def twoTermX (M N : ModuleCat.{u} k) (n : ℤ) : ModuleCat.{u} k :=
  if n = 0 then M else if n = 1 then N else ModuleCat.of k (Fin 0 → k)

def twoTermD (f : M ⟶ N) (n : ℤ) : twoTermX M N n ⟶ twoTermX M N (n+1) := by
  by_cases h : n = 0
  · subst n
    exact f
  · exact 0

def twoTerm (f : M ⟶ N) : CochainComplex (ModuleCat.{u} k) ℤ :=
  CochainComplex.of (twoTermX M N) (twoTermD f) (by
    intro n
    by_cases h : n = 0
    · subst n
      simp [twoTermD]
      exact comp_zero
    · simp [twoTermD, h])

end TwoTerm

def originalComplex : CochainComplex (ModuleCat.{u} k) ℤ :=
  twoTerm (ModuleCat.ofHom (differential k))

def completedComplex : CochainComplex (ModuleCat.{u} k) ℤ :=
  twoTerm (ModuleCat.ofHom (completedDifferential k))

/-- The projection to an original integer-indexed quotient. -/
def integerCompletionProjection (p : ℤ) :
    integerCompletion k →ₗ[k] (FiniteSequences k ⧸ tail k p) where
  toFun x := x.1 p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The filtration induced by the original integer-indexed quotient projections. -/
def integerCompletionTail (p : ℤ) : Submodule k (integerCompletion k) :=
  LinearMap.ker (integerCompletionProjection k p)

def originalGradedComplex (p : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ :=
  twoTerm (ModuleCat.ofHom (gradedDifferential k p))

def completedGradedComplex (p : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ :=
  twoTerm (ModuleCat.ofHom (productGradedDifferential k p))

instance limitQuotientGroups : ∀ m : ℕ,
    AddCommGroup (FiniteSequences k ⧸ tail k m) :=
  fun m => Submodule.Quotient.addCommGroup (tail k m)

instance limitQuotientModules : ∀ m : ℕ,
    Module k (FiniteSequences k ⧸ tail k m) :=
  fun m => Submodule.Quotient.module (tail k m)

def inverseLimitComplex : CochainComplex (ModuleCat.{u} k) ℤ :=
  twoTerm (ModuleCat.ofHom (inverseLimitDifferential k))

section PagePresentation

variable (k : Type u) [Field k]

/-- A simultaneous presentation of every degree of the two-term complex inside
one ambient space. The actual degree term is `ambientTerm k n`. -/
def ambientTerm (n : ℤ) : Submodule k (FiniteSequences k) :=
  if n = 0 ∨ n = 1 then ⊤ else ⊥

def ambientDifferential (n : ℤ) : FiniteSequences k →ₗ[k] FiniteSequences k :=
  if n = 0 then differential k else 0

def ambientTail (p n : ℤ) : Submodule k (FiniteSequences k) :=
  if n = 0 ∨ n = 1 then tail k p else ⊥

variable {k}

@[simp] theorem ambientTail_zero (p : ℤ) : ambientTail k p 0 = tail k p := by
  simp [ambientTail]
@[simp] theorem ambientTail_one (p : ℤ) : ambientTail k p 1 = tail k p := by
  simp [ambientTail]
@[simp] theorem ambientTail_other (p n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    ambientTail k p n = ⊥ := by simp [ambientTail, h0, h1]

@[simp] theorem ambientDifferential_zero : ambientDifferential k 0 = differential k := by
  simp [ambientDifferential]
@[simp] theorem ambientDifferential_other (n : ℤ) (h : n ≠ 0) :
    ambientDifferential k n = 0 := by simp [ambientDifferential, h]

theorem ambientDifferential_square_zero (n : ℤ) :
    ambientDifferential k (n+1) ∘ₗ ambientDifferential k n = 0 := by
  by_cases h : n = 0
  · subst n; simp
  · simp [ambientDifferential_other n h]

theorem ambientTail_antitone (p n : ℤ) : ambientTail k (p+1) n ≤ ambientTail k p n :=
by
  by_cases h : n = 0 ∨ n = 1
  · simpa [ambientTail, h] using (tail_antitone (k := k) p)
  · simp [ambientTail, h]

theorem ambientDifferential_mem_tail (p n : ℤ) (a : FiniteSequences k)
    (ha : a ∈ ambientTail k p n) :
    ambientDifferential k n a ∈ ambientTail k p (n+1) := by
  by_cases h : n = 0
  · subst n; simpa using differential_mem_tail p a (by simpa using ha)
  · simp [ambientDifferential_other n h]

variable (k)

def ambientGraded (p n : ℤ) :
    Submodule k (FiniteSequences k ⧸ ambientTail k (p+1) n) :=
  (ambientTail k p n).map (ambientTail k (p+1) n).mkQ

def ambientAlmost (r p n : ℤ) : Submodule k (FiniteSequences k) :=
  ambientTail k p n ⊓ (ambientTail k (p+r) (n+1)).comap (ambientDifferential k n)

def ambientCycles (r p n : ℤ) :
    Submodule k (FiniteSequences k ⧸ ambientTail k (p+1) n) :=
  (ambientAlmost k r p n).map (ambientTail k (p+1) n).mkQ

def ambientBoundaries (r p n : ℤ) :
    Submodule k (FiniteSequences k ⧸ ambientTail k (p+1) n) :=
  (ambientTail k p n ⊓ (ambientTail k (p-r+1) (n-1)).map
    (ambientDifferential k (n-1))).map (ambientTail k (p+1) n).mkQ

def ambientPage (r p n : ℤ) :=
  ambientCycles k r p n ⧸ (ambientBoundaries k r p n).comap
    (ambientCycles k r p n).subtype

instance ambientPageAddCommGroup (r p n : ℤ) : AddCommGroup (ambientPage k r p n) := by
  unfold ambientPage
  infer_instance
instance ambientPageModule (r p n : ℤ) : Module k (ambientPage k r p n) := by
  unfold ambientPage
  infer_instance

variable {k}
@[simp] theorem ambientAlmost_zero (r p : ℤ) :
    ambientAlmost k r p 0 = almostZero k r p := by
  simp [ambientAlmost, almostZero]
@[simp] theorem ambientAlmost_one (r p : ℤ) :
    ambientAlmost k r p 1 = tail k p := by
  simp [ambientAlmost]
@[simp] theorem ambientAlmost_other (r p n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    ambientAlmost k r p n = ⊥ := by
  simp [ambientAlmost, ambientTail_other p n h0 h1]

@[simp] theorem ambientCycles_zero (r p : ℤ) :
    ambientCycles k r p 0 = cyclesZero k r p := by
  simp [ambientCycles, cyclesZero, ambientTail]
  rfl
@[simp] theorem ambientCycles_one (r p : ℤ) :
    ambientCycles k r p 1 = gradedTerm k p := by
  simp [ambientCycles, gradedTerm, ambientTail]
  rfl
@[simp] theorem ambientCycles_other (r p n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    ambientCycles k r p n = ⊥ := by
  simp [ambientCycles, ambientAlmost_other r p n h0 h1]

@[simp] theorem ambientBoundaries_zero (r p : ℤ) :
    ambientBoundaries k r p 0 = ⊥ := by
  simp [ambientBoundaries]
@[simp] theorem ambientBoundaries_one (r p : ℤ) :
    ambientBoundaries k r p 1 = boundariesOne k r p := by
  simp [ambientBoundaries, boundariesOne, ambientTail]
  rfl
@[simp] theorem ambientBoundaries_other (r p n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    ambientBoundaries k r p n = ⊥ := by
  simp [ambientBoundaries, ambientTail_other p n h0 h1]

theorem ambientBoundaries_le_cycles (r p n : ℤ) :
    ambientBoundaries k r p n ≤ ambientCycles k r p n := by
  by_cases h0 : n = 0
  · subst n; simp only [ambientBoundaries_zero]; exact bot_le
  by_cases h1 : n = 1
  · subst n
    simp only [ambientBoundaries_one, ambientCycles_one]
    exact Submodule.map_mono inf_le_left
  simp [ambientBoundaries_other r p n h0 h1]

@[simp] theorem ambientPage_zero (r p : ℤ) : ambientPage k r p 0 = pageZero k r p := by
  unfold ambientPage
  rw [ambientBoundaries_zero, ambientCycles_zero]
  unfold pageZero
  congr 1
  exact Submodule.ker_subtype _
@[simp] theorem ambientPage_one (r p : ℤ) : ambientPage k r p 1 = pageOne k r p := by
  unfold ambientPage
  rw [ambientBoundaries_one, ambientCycles_one]
  rfl

theorem ambientPage_other_subsingleton (r p n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    Subsingleton (ambientPage k r p n) := by
  have : Subsingleton (ambientCycles k r p n) := by
    rw [ambientCycles_other r p n h0 h1]; infer_instance
  unfold ambientPage
  infer_instance

/-- The source's quotient formula in every total degree is exactly the concrete
page already calculated, including the zero terms outside degrees 0 and 1. -/
def ambientPageEquiv (r p q : ℤ) : ambientPage k r p (p+q) ≃ page k r p q := by
  unfold page
  split_ifs with h0 h1
  · rw [h0, ambientPage_zero]
  · rw [h1, ambientPage_one]
  · have := ambientPage_other_subsingleton (k := k) r p (p+q) h0 h1
    exact Equiv.ofBijective (fun _ => (0 : Fin 0 → k))
      ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨(by unfold ambientPage; exact 0), Subsingleton.elim _ _⟩⟩


variable (k)

def ambientQuotientDifferential (p n : ℤ) :
    (FiniteSequences k ⧸ ambientTail k (p+1) n) →ₗ[k]
      (FiniteSequences k ⧸ ambientTail k (p+1) (n+1)) :=
  (ambientTail k (p+1) n).mapQ (ambientTail k (p+1) (n+1))
    (ambientDifferential k n) (ambientDifferential_mem_tail (p+1) n)

/-- The all-degree differential on the actual successive filtration quotients. -/
def ambientGradedDifferential (p n : ℤ) :
    ambientGraded k p n →ₗ[k] ambientGraded k p (n+1) :=
  (ambientQuotientDifferential k p n).restrict (by
    rintro x ⟨a, ha, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨ambientDifferential k n a, ambientDifferential_mem_tail (k := k) p n (a : FiniteSequences k) ha, rfl⟩)

variable {k}

@[simp] theorem ambientGraded_zero (p : ℤ) : ambientGraded k p 0 = gradedTerm k p := by
  simp [ambientGraded, gradedTerm, ambientTail]
  rfl
@[simp] theorem ambientGraded_one (p : ℤ) : ambientGraded k p 1 = gradedTerm k p := by
  simp [ambientGraded, gradedTerm, ambientTail]
  rfl
@[simp] theorem ambientGraded_other (p n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    ambientGraded k p n = ⊥ := by
  simp [ambientGraded, ambientTail_other p n h0 h1]

/-- In total degree zero the induced differential is the original computed map. -/
theorem ambientGradedDifferential_zero (p : ℤ) :
    HEq (ambientGradedDifferential k p 0) (gradedDifferential k p) := by
  unfold ambientGradedDifferential ambientQuotientDifferential ambientGraded
    ambientTail ambientDifferential gradedDifferential gradedTerm quotientDifferential
  rfl

theorem ambientGradedDifferential_other (p n : ℤ) (h : n ≠ 0) :
    ambientGradedDifferential k p n = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨a, ha, hx⟩ := x.2
  change ambientQuotientDifferential k p n x.1 = 0
  rw [← hx]
  change (ambientTail k (p+1) (n+1)).mkQ (ambientDifferential k n a) = 0
  simp [ambientDifferential_other n h]

/-- The E₀ cycles are the entire associated graded in every degree. -/
theorem ambientCycles_page_zero (p n : ℤ) :
    ambientCycles k 0 p n = ambientGraded k p n := by
  unfold ambientCycles ambientAlmost ambientGraded
  congr 1
  simp only [add_zero]
  apply le_antisymm inf_le_left
  intro a ha
  exact ⟨ha, ambientDifferential_mem_tail (k := k) p n (a : FiniteSequences k) ha⟩

/-- No boundaries are present on E₀ in any degree. -/
theorem ambientBoundaries_page_zero (p n : ℤ) :
    ambientBoundaries k 0 p n = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨b, ⟨_, a, ha, rfl⟩, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have h := ambientDifferential_mem_tail (k := k) (p+1) (n-1) a
    (by simpa using ha)
  simpa using h

/-- The canonical E₀ identification; the differential is transported from the
quotient differential, rather than assigning the zero map on every page. -/
def ambientZeroPageEquiv (p n : ℤ) :
    ambientPage k 0 p n ≃ₗ[k] ambientGraded k p n := by
  unfold ambientPage
  have hb : (ambientBoundaries k 0 p n).comap (ambientCycles k 0 p n).subtype = ⊥ := by
    rw [ambientBoundaries_page_zero]
    exact LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _)
  exact ((Submodule.quotEquivOfEqBot _ hb).trans
    (LinearEquiv.ofEq _ _ (ambientCycles_page_zero p n)))

variable (k)

/-- The actual all-degree linear maps on the term submodules. -/
def ambientRestrictedDifferential (n : ℤ) :
    ambientTerm k n →ₗ[k] ambientTerm k (n+1) :=
  (ambientDifferential k n).restrict (by
    intro a ha
    by_cases h : n = 0
    · subst n; simp [ambientTerm]
    · simp [ambientDifferential_other n h])

/-- The filtration on those actual term modules. -/
def ambientRestrictedTail (p n : ℤ) : Submodule k (ambientTerm k n) :=
  (tail k p).comap (ambientTerm k n).subtype

variable {k}

theorem ambientRestrictedDifferential_square_zero (n : ℤ) :
    ambientRestrictedDifferential k (n+1) ∘ₗ ambientRestrictedDifferential k n = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact LinearMap.congr_fun (ambientDifferential_square_zero (k := k) n) (a : FiniteSequences k)

theorem ambientRestrictedTail_map (p n : ℤ) :
    (ambientRestrictedTail k p n).map (ambientTerm k n).subtype = ambientTail k p n := by
  rw [ambientRestrictedTail, Submodule.map_comap_subtype]
  by_cases h : n = 0 ∨ n = 1 <;> simp [ambientTerm, ambientTail, h]

theorem ambientRestrictedDifferential_mem (p n : ℤ) (a : ambientTerm k n)
    (ha : a ∈ ambientRestrictedTail k p n) :
    ambientRestrictedDifferential k n a ∈ ambientRestrictedTail k p (n+1) := by
  have h : (a : FiniteSequences k) ∈ ambientTail k p n := by
    rw [← ambientRestrictedTail_map]
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩
  have hd := ambientDifferential_mem_tail (k := k) p n (a : FiniteSequences k) h
  change ambientDifferential k n a ∈ tail k p
  unfold ambientTail at hd
  split_ifs at hd
  · exact hd
  · rw [show ambientDifferential k n a = 0 from hd]
    exact zero_mem _

variable (k)

/-- The map from almost cycles to their image in the associated graded. -/
def ambientToCycles (r p n : ℤ) : ambientAlmost k r p n →ₗ[k] ambientCycles k r p n :=
  (((ambientTail k (p+1) n).mkQ).comp (ambientAlmost k r p n).subtype).codRestrict
    (ambientCycles k r p n) (fun a => Submodule.mem_map.mpr ⟨a, a.2, rfl⟩)

/-- The canonical representative map to the F03 quotient. -/
def ambientToPage (r p n : ℤ) : ambientAlmost k r p n →ₗ[k] ambientPage k r p n :=
  (((ambientBoundaries k r p n).comap (ambientCycles k r p n).subtype).mkQ).comp
    (ambientToCycles k r p n)

/-- Actual differential of representatives; it lands in the target almost cycles. -/
def ambientAlmostDifferential (r p n : ℤ) :
    ambientAlmost k r p n →ₗ[k] ambientAlmost k r (p+r) (n+1) :=
  ((ambientDifferential k n).comp (ambientAlmost k r p n).subtype).codRestrict
    (ambientAlmost k r (p+r) (n+1)) (by
      intro a
      refine ⟨a.2.2, ?_⟩
      change ambientDifferential k (n+1) (ambientDifferential k n a.1) ∈
        ambientTail k ((p+r)+r) ((n+1)+1)
      have hz := LinearMap.congr_fun (ambientDifferential_square_zero (k := k) n) a.1
      change ambientDifferential k (n+1) (ambientDifferential k n a.1) = 0 at hz
      rw [hz]
      exact zero_mem _)

/-- The E₀ differential, transported across the canonical quotient identification. -/
def ambientZeroPageDifferential (p n : ℤ) :
    ambientPage k 0 p n →ₗ[k] ambientPage k 0 p (n+1) :=
  (ambientZeroPageEquiv p (n+1)).symm.toLinearMap ∘ₗ ambientGradedDifferential k p n ∘ₗ
    (ambientZeroPageEquiv p n).toLinearMap

variable {k}

@[simp] theorem ambientZeroPageEquiv_representative (p n : ℤ)
    (a : ambientAlmost k 0 p n) :
    ((ambientZeroPageEquiv (k := k) p n) (ambientToPage k 0 p n a) :
      FiniteSequences k ⧸ ambientTail k (p+1) n) =
      (ambientTail k (p+1) n).mkQ a.1 := by
  change ((LinearEquiv.ofEq _ _ (ambientCycles_page_zero p n))
    (ambientToCycles k 0 p n a) : FiniteSequences k ⧸ ambientTail k (p+1) n) = _
  rw [LinearEquiv.coe_ofEq_apply]
  rfl

variable (k)

def ambientAlmostDifferentialZero (p n : ℤ) :
    ambientAlmost k 0 p n →ₗ[k] ambientAlmost k 0 p (n+1) :=
  ((ambientDifferential k n).comp (ambientAlmost k 0 p n).subtype).codRestrict
    (ambientAlmost k 0 p (n+1)) (by
      intro a
      refine ⟨?_, ?_⟩
      · change ambientDifferential k n a.1 ∈ ambientTail k p (n+1)
        have ha := a.2.2
        change ambientDifferential k n a.1 ∈ ambientTail k (p+0) (n+1) at ha
        simpa only [add_zero] using ha
      · change ambientDifferential k (n+1) (ambientDifferential k n a.1) ∈
          ambientTail k (p+0) ((n+1)+1)
        have hz := LinearMap.congr_fun (ambientDifferential_square_zero (k := k) n) a.1
        change ambientDifferential k (n+1) (ambientDifferential k n a.1) = 0 at hz
        rw [hz]
        exact zero_mem _)

variable {k}
/-- The nonzero page differential is induced by exactly the source differential. -/
theorem ambientZeroPageDifferential_representative (p n : ℤ)
    (a : ambientAlmost k 0 p n) :
    ambientZeroPageDifferential k p n (ambientToPage k 0 p n a) =
      ambientToPage k 0 p (n+1) (ambientAlmostDifferentialZero k p n a) := by
  apply (ambientZeroPageEquiv (k := k) p (n+1)).injective
  apply Subtype.ext
  simp only [ambientZeroPageDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [ambientZeroPageEquiv_representative]
  change ambientQuotientDifferential k p n
    ((ambientZeroPageEquiv p n) (ambientToPage k 0 p n a)).1 = _
  rw [ambientZeroPageEquiv_representative]
  rfl

variable (k)
/-- The page differential in all total degrees and for every page index.
For r≥1 its source and target have been proved zero; at r=0 this retains
the actual nonzero differential of the associated graded. -/
def ambientPageDifferential (r p n : ℤ) :
    ambientPage k r p n →ₗ[k] ambientPage k r (p+r) (n+1) := by
  by_cases hr : r = 0
  · subst r
    rw [add_zero]
    exact ambientZeroPageDifferential k p n
  · exact 0

variable {k}

theorem ambientTail_le_term (p n : ℤ) : ambientTail k p n ≤ ambientTerm k n := by
  unfold ambientTail ambientTerm
  split_ifs <;> simp

end PagePresentation

section PagePresentationTerms

variable (k : Type u) [Field k]
def originalTermEquiv (n : ℤ) : (originalComplex k).X n ≃ₗ[k] ambientTerm k n := by
  by_cases h0 : n = 0
  · subst n
    change FiniteSequences k ≃ₗ[k] (⊤ : Submodule k (FiniteSequences k))
    exact Submodule.topEquiv.symm
  by_cases h1 : n = 1
  · subst n
    change FiniteSequences k ≃ₗ[k] (⊤ : Submodule k (FiniteSequences k))
    exact Submodule.topEquiv.symm
  · have : Subsingleton ((originalComplex k).X n) := by
      change Subsingleton (twoTermX (ModuleCat.of k (FiniteSequences k))
        (ModuleCat.of k (FiniteSequences k)) n)
      simp only [twoTermX, ite_eq_right h0, ite_eq_right h1]
      infer_instance
    have : Subsingleton (ambientTerm k n) := by
      unfold ambientTerm
      rw [ite_eq_right (not_or_intro h0 h1)]
      infer_instance
    exact LinearEquiv.ofSubsingleton _ _

end PagePresentationTerms

namespace Specs
/-- Exact concrete calculation of both cohomology groups. -/
def Cohomology : Prop := ∀ (k : Type u) [Field k],
  Function.Injective (differential k) ∧
  LinearMap.range (differential k) = LinearMap.ker (coefficientSum k) ∧
  Function.Surjective (coefficientSum k) ∧
  Nonempty (firstCohomology k ≃ₗ[k] k)

/-- The original complex is exhaustive and separated; its image filtration
on its nonzero degree-one cohomology is constant. -/
def Filtration : Prop := ∀ (k : Type u) [Field k],
  (∀ p : ℤ, tail k (p+1) ≤ tail k p) ∧
  (∀ p : ℤ, ∀ a ∈ tail k p, differential k a ∈ tail k p) ∧
  (⨆ p : ℤ, tail k p) = ⊤ ∧
  (⨅ p : ℤ, tail k p) = ⊥ ∧
  (∀ p : ℤ, cohomologyTail k p = ⊤) ∧
  (⨅ p : ℤ, cohomologyTail k p) ≠ ⊥

/-- The product differential is invertible, with inverse given by the source's
recurrence, and extends the differential on the sum. -/
def CompletedDifferential : Prop := ∀ (k : Type u) [Field k],
  completedDifferential k ∘ₗ partialSums k = LinearMap.id ∧
  partialSums k ∘ₗ completedDifferential k = LinearMap.id ∧
  completedDifferential k ∘ₗ toProduct k = toProduct k ∘ₗ differential k
/-- The inverse limit of the actual tail quotients is the product, by its
canonical coefficient map, and the comparison is the usual inclusion. -/
def Completion : Prop := ∀ (k : Type u) [Field k],
  Function.Bijective (completionToProduct k) ∧
  completionToProduct k ∘ₗ intoCompletion k = toProduct k

/-- Representative identity inducing the identity on successive-tail quotients. -/
def GradedRepresentative : Prop := ∀ (k : Type u) [Field k] (p : ℤ)
  (a : FiniteSequences k), a ∈ tail k p → differential k a - a ∈ tail k (p+1)

/-- The codomain of the cohomology completeness comparison is zero. -/
def CohomologyCompletion : Prop := ∀ (k : Type u) [Field k],
  Subsingleton (cohomologyCompletion k) ∧ cohomologyComparison k = 0

/-- Both completed cohomology groups vanish, and the original H⁰ vanishes. -/
def Acyclicity : Prop := ∀ (k : Type u) [Field k],
  Subsingleton (zerothCohomology k) ∧
  Subsingleton (completedZerothCohomology k) ∧
  Subsingleton (completedFirstCohomology k)

/-- This is precisely the image filtration induced by inclusion of subcomplexes;
its associated graded is zero, despite the nonzero underlying H¹. -/
def InducedFiltration : Prop := ∀ (k : Type u) [Field k] (p : ℤ),
  LinearMap.range (tailCohomologyInclusion k p) = cohomologyTail k p ∧
  Subsingleton (cohomologyGradedTerm k p)

/-- The graded terms have their expected support and scalar dimension, and the
actual quotient differential on the two nonzero cochain terms is the identity. -/
def AssociatedGraded : Prop := ∀ (k : Type u) [Field k],
  (∀ p : ℤ, p < 0 → Subsingleton (gradedTerm k p)) ∧
  (∀ (p : ℤ) (hp : 0 ≤ p), Function.Bijective (gradedCoefficient (k := k) p hp)) ∧
  (∀ p : ℤ, gradedDifferential k p = LinearMap.id) ∧
  (∀ p : ℤ, productGradedDifferential k p = LinearMap.id)

/-- The canonical completion comparison induces the same E₀, including d₀. -/
def SameZeroPage : Prop := ∀ (k : Type u) [Field k] (p : ℤ),
  Function.Bijective (gradedComparison k p) ∧
  productGradedDifferential k p ∘ₗ gradedComparison k p =
    gradedComparison k p ∘ₗ gradedDifferential k p

/-- The exact Z/B page formulas vanish for every bidegree from E₁ onward. -/
def Pages : Prop := ∀ (k : Type u) [Field k] (r p q : ℤ),
  1 ≤ r → Subsingleton (page k r p q)

/-- The natural tower is the actual integer-tail completion, with its canonical
comparison, quotient-induced differential and induced tail filtration. -/
def CompletionBridge : Prop := ∀ (k : Type u) [Field k],
  Function.Bijective (integerCompletionRestriction k) ∧
  integerCompletionRestriction k ∘ₗ intoIntegerCompletion k = intoCompletion k ∧
  inverseLimitDifferential k ∘ₗ intoCompletion k = intoCompletion k ∘ₗ differential k ∧
  completionToProduct k ∘ₗ inverseLimitDifferential k =
    completedDifferential k ∘ₗ completionToProduct k ∧
  Function.Bijective (inverseLimitDifferential k) ∧
  (∀ p : ℤ, (inverseLimitTail k p).map (completionToProduct k) = productTail k p)

/-- Categorical cohomology of the actual complexes, with zero terms outside
cochain degrees zero and one. The H¹ quotient model has an explicit bridge. -/
def ComplexCohomology : Prop := ∀ (k : Type u) [Field k],
  IsZero ((originalComplex k).homology 0) ∧
  Nonempty ((originalComplex k).homology 1 ≅ ModuleCat.of k (firstCohomology k)) ∧
  Nonempty ((originalComplex k).homology 1 ≅ ModuleCat.of k k) ∧
  (∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero ((originalComplex k).homology n)) ∧
  (∀ n : ℤ, IsZero ((completedComplex k).homology n))

def IntegerCompletionFiltration : Prop := ∀ (k : Type u) [Field k] (p : ℤ),
  (integerCompletionTail k p).map
    ((completionToProduct k).comp (integerCompletionRestriction k)) = productTail k p

/-- The associated graded complexes are acyclic in all degrees, and the
canonical completion comparison is an isomorphism of the entire E₀ complex. -/
def GradedComplexes : Prop := ∀ (k : Type u) [Field k],
  (∀ p n : ℤ, IsZero ((originalGradedComplex k p).homology n)) ∧
  (∀ p n : ℤ, IsZero ((completedGradedComplex k p).homology n)) ∧
  (∀ p : ℤ, ∃ e : originalGradedComplex k p ≅ completedGradedComplex k p,
    e.hom.f 0 = ModuleCat.ofHom (gradedComparison k p) ∧
    e.hom.f 1 = ModuleCat.ofHom (gradedComparison k p))

/-- The completed quotient-system complex itself is acyclic and is identified
with the product complex by the canonical coefficient comparison in both degrees. -/
def LimitComplex : Prop := ∀ (k : Type u) [Field k],
  (∀ n : ℤ, IsZero ((inverseLimitComplex k).homology n)) ∧
  (∃ e : inverseLimitComplex k ≅ completedComplex k,
    e.hom.f 0 = ModuleCat.ofHom (completionToProduct k) ∧
    e.hom.f 1 = ModuleCat.ofHom (completionToProduct k))


/-- Full all-degree module presentation of the source F03 pages of the actual
term submodules, including d₀ and every positive-page differential. -/
def PageBridge : Prop := ∀ (k : Type u) [Field k],
  (∀ p n : ℤ, ambientTail k p n ≤ ambientTerm k n) ∧
  (∀ n : ℤ, ambientRestrictedDifferential k (n+1) ∘ₗ
    ambientRestrictedDifferential k n = 0) ∧
  (∀ p n : ℤ, (ambientRestrictedTail k p n).map (ambientTerm k n).subtype =
    ambientTail k p n) ∧
  (∀ p n : ℤ, ∀ a ∈ ambientRestrictedTail k p n,
    ambientRestrictedDifferential k n a ∈ ambientRestrictedTail k p (n+1)) ∧
  (∀ r p n : ℤ, ambientBoundaries k r p n ≤ ambientCycles k r p n) ∧
  (∀ r p q : ℤ, Nonempty (ambientPage k r p (p+q) ≃ page k r p q)) ∧
  (∀ p n : ℤ, Nonempty (ambientPage k 0 p n ≃ₗ[k] ambientGraded k p n)) ∧
  (∀ p n : ℤ, ∀ a : ambientAlmost k 0 p n,
    ((ambientZeroPageEquiv (k := k) p n) (ambientToPage k 0 p n a) :
      FiniteSequences k ⧸ ambientTail k (p+1) n) =
      (ambientTail k (p+1) n).mkQ a.1) ∧
  (∀ p n : ℤ, ∀ a : ambientAlmost k 0 p n,
    ambientZeroPageDifferential k p n (ambientToPage k 0 p n a) =
      ambientToPage k 0 p (n+1) (ambientAlmostDifferentialZero k p n a)) ∧
  (∀ r p n : ℤ, 1 ≤ r →
    ambientPageDifferential k r p n ∘ₗ ambientToPage k r p n =
      ambientToPage k r (p+r) (n+1) ∘ₗ ambientAlmostDifferential k r p n) ∧
  (∀ r p n : ℤ, 1 ≤ r → Subsingleton (ambientPage k r p n)) ∧
  (∀ p : ℤ, HEq (ambientGradedDifferential k p 0) (gradedDifferential k p)) ∧
  (∀ p n : ℤ, n ≠ 0 → ambientGradedDifferential k p n = 0)


def PageBridgeTerms : Prop := ∀ (k : Type u) [Field k],
  (∀ n : ℤ, (originalTermEquiv k (n+1)).toLinearMap ∘ₗ
    ((originalComplex k).d n (n+1)).hom =
      ambientRestrictedDifferential k n ∘ₗ (originalTermEquiv k n).toLinearMap) ∧
  (∀ n : ℤ, (⨆ p : ℤ, ambientRestrictedTail k p n) = ⊤) ∧
  (∀ n : ℤ, (⨅ p : ℤ, ambientRestrictedTail k p n) = ⊥)

/-- The page differentials square to zero, with the zeroth page treated via
its canonical associated graded identification. -/
def PageDifferentials : Prop := ∀ (k : Type u) [Field k],
  (∀ p n : ℤ, ambientGradedDifferential k p (n+1) ∘ₗ
    ambientGradedDifferential k p n = 0) ∧
  (∀ p n : ℤ, ambientZeroPageDifferential k p (n+1) ∘ₗ
    ambientZeroPageDifferential k p n = 0) ∧
  (∀ r p n : ℤ, 1 ≤ r → ambientPageDifferential k r (p+r) (n+1) ∘ₗ
    ambientPageDifferential k r p n = 0)

/-- The complete HA-S07 example and its following completion calculation,
with the original field, integer indices, and absence of finiteness hypotheses. -/
def CompleteExample : Prop :=
  Cohomology.{u} ∧
  Filtration.{u} ∧
  CompletedDifferential.{u} ∧
  Completion.{u} ∧
  GradedRepresentative.{u} ∧
  CohomologyCompletion.{u} ∧
  Acyclicity.{u} ∧
  InducedFiltration.{u} ∧
  AssociatedGraded.{u} ∧
  SameZeroPage.{u} ∧
  Pages.{u} ∧
  CompletionBridge.{u} ∧
  ComplexCohomology.{u} ∧
  IntegerCompletionFiltration.{u} ∧
  GradedComplexes.{u} ∧
  LimitComplex.{u} ∧
  PageBridge.{u} ∧
  PageBridgeTerms.{u} ∧
  PageDifferentials.{u}

end Specs
end AdvancedHomologicalAlgebra.NonseparatedExample
