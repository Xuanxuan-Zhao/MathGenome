import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperPbwBasis
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.SuperLie
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.SuperEnveloping
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered
import Mathlib.Data.List.Chain
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Module

namespace LieNotes.SuperRestricted.SuperPbwBasis

open SuperEnveloping.Construction
open Shared.Lie.PBW (WordModule WordBelow wordBelow_wellFounded swapped_word_below
  bracket_word_below context context_single context_context context_empty
  wordPair wordPair_single_left wordPair_single_right adjacent_occurrence_cases)
open Shared.Lie.PBW.LinearReduction (System)

noncomputable section

universe u v w

variable {k : Type u} {V : Type v} {I : Type w}
  [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)] [LinearOrder I]
  (L : LieSuperalgebra k V) (b : Module.Basis I k V) (degree : I → ZMod 2)

private theorem parity_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [NeZero (2 : k)] in
private theorem sign_symm (i j : ZMod 2) : paritySign k i j = paritySign k j i := by
  rw [paritySign, paritySign, Nat.mul_comm]

omit [NeZero (2 : k)] in
private theorem sign_sq (i j : ZMod 2) : paritySign k i j * paritySign k i j = 1 := by
  rcases parity_cases i with rfl | rfl <;> rcases parity_cases j with rfl | rfl <;> simp

omit [NeZero (2 : k)] in
private theorem sign_add (i j l : ZMod 2) :
    paritySign k i (j + l) = paritySign k i j * paritySign k i l := by
  rcases parity_cases i with rfl | rfl <;> rcases parity_cases j with rfl | rfl <;>
    rcases parity_cases l with rfl | rfl <;> simp [show (1 : ZMod 2) + 1 = 0 by decide]

omit [NeZero (2 : k)] in
private theorem sign_add_left (i j l : ZMod 2) :
    paritySign k (i + j) l = paritySign k i l * paritySign k j l := by
  rw [sign_symm, sign_add, sign_symm (i := l) (j := i), sign_symm (i := l) (j := j)]

private theorem half_two : (2 : k)⁻¹ * 2 = 1 :=
  inv_mul_cancel₀ (NeZero.ne (2 : k))

private abbrev crosses (i j : I) : k := paritySign k (degree i) (degree j)

private abbrev bracket (i j : I) : V := L.bracket (b i) (b j)

private abbrev delta (l : List I) : WordModule k I := Finsupp.single l 1

private def letter : V →ₗ[k] WordModule k I :=
  (Finsupp.linearCombination k fun i => delta [i]).comp b.repr.toLinearMap

omit [NeZero (2 : k)] [LinearOrder I] in
@[simp] private theorem letter_basis (i : I) : letter b (b i) = delta [i] := by
  simp [letter]

omit [NeZero (2 : k)] [LinearOrder I] in
private theorem map_mem_of_basis {N : Type*} [AddCommGroup N] [Module k N]
    (f : V →ₗ[k] N) (R : Submodule k N) (h : ∀ i, f (b i) ∈ R) (x : V) : f x ∈ R := by
  have hle : Submodule.span k (Set.range b) ≤ R.comap f :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  rw [b.span_eq] at hle
  exact hle Submodule.mem_top

private def reduciblePair (i j : I) : Prop := j < i ∨ (i = j ∧ degree i = 1)

private def replacement (i j : I) : WordModule k I :=
  if j < i then crosses (k := k) degree i j • delta [j, i] + letter b (bracket L b i j)
  else (2 : k)⁻¹ • letter b (bracket L b i j)

private def rhs (p s : List I) (i j : I) : WordModule k I :=
  context p s (replacement L b degree i j)

private theorem replacement_decreases (p s : List I) (i j : I) :
    ∀ t ∈ (rhs L b degree p s i j).support,
      WordBelow t (p ++ i :: j :: s) := by
  let R := Finsupp.supported k k {t | WordBelow t (p ++ i :: j :: s)}
  have hbr : context p s (letter b (bracket L b i j)) ∈ R := by
    apply map_mem_of_basis b ((context p s).comp (letter b)) R
    intro a
    simp only [LinearMap.comp_apply, letter_basis, context_single]
    apply Finsupp.single_mem_supported k 1
    simpa only [Set.mem_ofPred_eq, List.append_assoc, List.cons_append, List.nil_append] using
      bracket_word_below p s i j a
  apply (Finsupp.mem_supported k (rhs L b degree p s i j)).mp
  unfold rhs replacement
  split
  · rename_i h
    rw [map_add, map_smul, context_single]
    refine R.add_mem (R.smul_mem _ (Finsupp.single_mem_supported k 1 ?_)) hbr
    simpa only [Set.mem_ofPred_eq, List.append_assoc, List.cons_append, List.nil_append] using
      swapped_word_below p s i j h
  · rw [map_smul]
    exact R.smul_mem _ hbr

private def system : System k (List I) where
  below := WordBelow
  wellFounded := wordBelow_wellFounded
  rule w f := ∃ p s i j, reduciblePair degree i j ∧
    w = p ++ i :: j :: s ∧ f = rhs L b degree p s i j
  decreases := by
    rintro _ _ ⟨p, s, i, j, _, rfl, rfl⟩
    exact replacement_decreases L b degree p s i j

private theorem irreducible_iff (l : List I) :
    ¬ (system L b degree).Reducible l ↔
      l.Pairwise (fun i j => i ≤ j ∧ (i = j → degree i ≠ 1)) := by
  let good := fun i j => i ≤ j ∧ (i = j → degree i ≠ 1)
  let ht : Trans good good good := ⟨by
    intro x y z hxy hyz
    refine ⟨hxy.1.trans hyz.1, ?_⟩
    rintro rfl
    exact hxy.2 (le_antisymm hxy.1 hyz.1)⟩
  change _ ↔ l.Pairwise good
  rw [← List.isChain_iff_pairwise]
  have hg (i j : I) : good i j ↔ ¬ reduciblePair degree i j := by
    simp [good, reduciblePair, not_lt, not_and]
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  constructor
  · intro h i j p s he
    exact (hg i j).2 (fun hij => h ⟨_, p, s, i, j, hij, he, rfl⟩)
  · rintro h ⟨_, p, s, i, j, hij, he, _⟩
    exact (hg i j).1 (h he) hij

private theorem rule_mem (p s : List I) (i j : I) (h : reduciblePair degree i j) :
    delta (p ++ i :: j :: s) - rhs L b degree p s i j ∈ (system L b degree).relations :=
  Submodule.subset_span ⟨_, _, ⟨p, s, i, j, h, rfl, rfl⟩, rfl⟩

private theorem rule_mem_lower (z p s : List I) (i j : I)
    (h : reduciblePair degree i j) (hz : WordBelow (p ++ i :: j :: s) z) :
    delta (p ++ i :: j :: s) - rhs L b degree p s i j ∈ (system L b degree).lowerRelations z :=
  Submodule.subset_span ⟨_, _, hz, ⟨p, s, i, j, h, rfl, rfl⟩, rfl⟩

omit [NeZero (2 : k)] [LinearOrder I] in
private theorem as_sum_of_singles (f : WordModule k I) :
    f = ∑ l ∈ f.support, f l • delta l := by
  conv_lhs => rw [← Finsupp.sum_single f]
  simp [Finsupp.sum]

private theorem context_closed (p s : List I) (f : WordModule k I)
    (hf : f ∈ (system L b degree).relations) :
    context p s f ∈ (system L b degree).relations := by
  let R := (system L b degree).relations
  refine (show R ≤ R.comap (context p s) from Submodule.span_le.mpr ?_) hf
  rintro _ ⟨_, _, ⟨a, c, i, j, h, rfl, rfl⟩, rfl⟩
  change context p s (delta (a ++ i :: j :: c) - rhs L b degree a c i j) ∈ R
  simpa [rhs, List.append_assoc] using rule_mem L b degree (p ++ a) (c ++ s) i j h

omit [NeZero (2 : k)] in
private theorem context_apply_append (p s l : List I) (f : WordModule k I) :
    context p s f (p ++ l ++ s) = f l := by
  have he : context (k := k) p s = Finsupp.lmapDomain k k (fun t => p ++ t ++ s) := by
    apply Finsupp.lhom_ext
    intro t c
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact context_single (k := k) p s t c
  rw [he, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective (fun a c h =>
    by simpa [List.append_assoc] using h) f l

private theorem disjoint_diamond (p m s : List I)
    (i j a c : I) (hij : reduciblePair degree i j) (hac : reduciblePair degree a c) :
    rhs L b degree p (m ++ a :: c :: s) i j -
      rhs L b degree (p ++ i :: j :: m) s a c ∈
        (system L b degree).lowerRelations (p ++ i :: j :: (m ++ a :: c :: s)) := by
  let z := p ++ i :: j :: (m ++ a :: c :: s)
  let R := (system L b degree).lowerRelations z
  let F := wordPair (k := k) p m s
  let x := replacement L b degree i j
  let y := replacement L b degree a c
  have hl : F x (delta [a, c] - y) ∈ R := by
    let G := (LinearMap.applyₗ (R := k) (M₂ := WordModule k I) (delta [a, c] - y)).comp F
    change G x ∈ R
    rw [as_sum_of_singles x, map_sum]
    refine R.sum_mem (fun l hl => ?_)
    rw [map_smul]
    refine R.smul_mem _ ?_
    have hb : WordBelow (p ++ l ++ m ++ a :: c :: s) z := by
      apply replacement_decreases L b degree p (m ++ a :: c :: s) i j
      have hh := Finsupp.mem_support_iff.mp hl
      have hn : (p ++ l ++ (m ++ a :: c :: s)) ∈
          (rhs L b degree p (m ++ a :: c :: s) i j).support := by
        rw [Finsupp.mem_support_iff]
        change context p (m ++ a :: c :: s) x _ ≠ 0
        rwa [context_apply_append]
      simpa only [List.append_assoc] using hn
    simpa [G, F, y, rhs, List.append_assoc] using
      rule_mem_lower L b degree z (p ++ l ++ m) s a c hac hb
  have hr : F (delta [i, j] - x) y ∈ R := by
    rw [as_sum_of_singles y, map_sum]
    refine R.sum_mem (fun l hl => ?_)
    rw [map_smul]
    refine R.smul_mem _ ?_
    have hb : WordBelow (p ++ i :: j :: (m ++ l ++ s)) z := by
      have hn : ((p ++ i :: j :: m) ++ l ++ s) ∈
          (rhs L b degree (p ++ i :: j :: m) s a c).support := by
        rw [Finsupp.mem_support_iff]
        change context (k := k) (p ++ i :: j :: m) s y _ ≠ 0
        rw [context_apply_append]
        exact Finsupp.mem_support_iff.mp hl
      simpa [z, List.append_assoc] using
        replacement_decreases L b degree (p ++ i :: j :: m) s a c _ hn
    simpa [F, x, rhs, List.append_assoc] using
      rule_mem_lower L b degree z p (m ++ l ++ s) i j hij hb
  have h := R.sub_mem hl hr
  convert h using 1
  simp only [F, map_sub, LinearMap.sub_apply, wordPair_single_right, wordPair_single_left,
    one_smul, List.append_assoc, List.cons_append, List.nil_append, rhs, x, y]
  abel

/-- The full signed relation for two basis letters in a fixed context. -/
private def basisRelator (p s : List I) (i j : I) : WordModule k I :=
  delta (p ++ i :: j :: s) - crosses (k := k) degree i j • delta (p ++ j :: i :: s) -
    context p s (letter b (bracket L b i j))

private theorem basisRelator_desc (p s : List I) (i j : I) (h : j < i) :
    basisRelator L b degree p s i j = delta (p ++ i :: j :: s) - rhs L b degree p s i j := by
  simp [basisRelator, rhs, replacement, h, List.append_assoc, sub_add_eq_sub_sub]

private theorem basisRelator_odd (p s : List I) (i : I) (h : degree i = 1) :
    basisRelator L b degree p s i i = (2 : k) •
      (delta (p ++ i :: i :: s) - rhs L b degree p s i i) := by
  simp only [basisRelator, crosses, h, paritySign_one_one, neg_one_smul, rhs, replacement,
    lt_irrefl, ite_false, map_smul, smul_sub, smul_smul, mul_comm (2 : k), half_two, one_smul,
    sub_neg_eq_add, two_smul]

private theorem basisRelator_mem (hb : Homogeneous L b degree) (R : Submodule k (WordModule k I))
    (p s : List I)
    (hr : ∀ i j, reduciblePair degree i j →
      delta (p ++ i :: j :: s) - rhs L b degree p s i j ∈ R) (i j : I) :
    basisRelator L b degree p s i j ∈ R := by
  rcases lt_trichotomy j i with hij | rfl | hji
  · rw [basisRelator_desc L b degree p s i j hij]
    exact hr i j (Or.inl hij)
  · rcases parity_cases (degree j) with h | h
    · have hs := L.skew (hb j) (hb j)
      rw [h, paritySign_zero_left, neg_one_smul] at hs
      have hz : bracket L b j j = 0 := by
        apply (smul_eq_zero_iff_right (NeZero.ne (2 : k))).mp
        rw [two_smul, ← eq_neg_iff_add_eq_zero]
        exact hs
      simp [basisRelator, crosses, h, hz]
    · rw [basisRelator_odd L b degree p s j h]
      exact R.smul_mem _ (hr j j (Or.inr ⟨rfl, h⟩))
  · have he : basisRelator L b degree p s i j =
        (-crosses (k := k) degree i j) • basisRelator L b degree p s j i := by
      have hs := L.skew (hb i) (hb j)
      change bracket L b i j = _ at hs
      rw [basisRelator, basisRelator]
      unfold crosses
      rw [hs, map_smul, map_smul, smul_sub, smul_sub,
        smul_smul, sign_symm (i := degree j) (j := degree i), neg_mul, sign_sq, neg_one_smul]
      module
    rw [he, basisRelator_desc L b degree p s j i hji]
    exact R.smul_mem _ (hr j i (Or.inl hji))

/-- A homogeneous vector has basis coefficients only in its own degree. -/
private theorem support_degree (hb : Homogeneous L b degree) {x : V} {d : ZMod 2}
    (hx : x ∈ L.grading.piece d) {i : I} (hi : i ∈ (b.repr x).support) :
    degree i = d := by
  have hcoord : (b.coord i).comp (generatorParity L.grading) =
      parityScalar k (degree i) • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, generatorParity_apply _ (hb j), map_smul,
      LinearMap.smul_apply]
    by_cases h : i = j
    · subst j
      rfl
    · simp [Module.Basis.coord_apply, Ne.symm h]
  have hs := LinearMap.congr_fun hcoord x
  simp only [LinearMap.comp_apply, generatorParity_apply _ hx, map_smul, LinearMap.smul_apply,
    Module.Basis.coord_apply, smul_eq_mul] at hs
  have he := mul_right_cancel₀ (Finsupp.mem_support_iff.mp hi) hs
  have h01 : (1 : k) ≠ -1 := by
    intro h
    apply NeZero.ne (2 : k)
    rw [← one_add_one_eq_two, ← eq_neg_iff_add_eq_zero]
    exact h
  have h10 : (-1 : k) ≠ 1 := Ne.symm h01
  rcases parity_cases (degree i) with hd | hd <;> rcases parity_cases d with rfl | rfl <;>
    simp_all [parityScalar, show (1 : ZMod 2) ≠ 0 by decide]

private theorem map_mem_of_homogeneous_basis (hb : Homogeneous L b degree)
    {N : Type*} [AddCommGroup N] [Module k N] (f : V →ₗ[k] N) (R : Submodule k N)
    {d : ZMod 2} (h : ∀ i, degree i = d → f (b i) ∈ R) {x : V}
    (hx : x ∈ L.grading.piece d) : f x ∈ R := by
  have he := b.linearCombination_repr x
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at he
  rw [show f x = f (∑ i ∈ (b.repr x).support, (b.repr x) i • b i) from congrArg f he.symm]
  rw [map_sum]
  refine R.sum_mem (fun i hi => ?_)
  rw [map_smul]
  exact R.smul_mem _ (h i (support_degree L b degree hb hx hi))

/-- The full relator with the two degrees fixed, as a bilinear map on the space of letters. -/
private def wordRelator (p s : List I) (d e : ZMod 2) :
    V →ₗ[k] V →ₗ[k] WordModule k I :=
  LinearMap.mk₂ k (fun x y =>
    wordPair p [] s (letter b x) (letter b y) -
    paritySign k d e • wordPair p [] s (letter b y) (letter b x) -
    context p s (letter b (L.bracket x y)))
    (by intros; simp only [map_add, LinearMap.add_apply, smul_add]; abel)
    (by intros; simp only [map_smul, LinearMap.smul_apply]; module)
    (by intros; simp only [map_add, LinearMap.add_apply, smul_add]; abel)
    (by intros; simp only [map_smul, LinearMap.smul_apply]; module)

omit [LinearOrder I] in
private theorem wordRelator_apply (p s : List I) (d e : ZMod 2) (x y : V) :
    wordRelator L b p s d e x y =
      wordPair p [] s (letter b x) (letter b y) -
      paritySign k d e • wordPair p [] s (letter b y) (letter b x) -
      context p s (letter b (L.bracket x y)) := rfl

private theorem wordRelator_basis (p s : List I) (i j : I) :
    wordRelator L b p s (degree i) (degree j) (b i) (b j) =
      basisRelator L b degree p s i j := by
  simp [wordRelator_apply, basisRelator, List.append_assoc]

private theorem wordRelator_mem (hb : Homogeneous L b degree) (R : Submodule k (WordModule k I))
    (p s : List I) (hr : ∀ i j, basisRelator L b degree p s i j ∈ R)
    {d e : ZMod 2} {x y : V} (hx : x ∈ L.grading.piece d) (hy : y ∈ L.grading.piece e) :
    wordRelator L b p s d e x y ∈ R := by
  let F := wordRelator L b p s d e
  change F.flip y x ∈ R
  apply map_mem_of_homogeneous_basis L b degree hb (F.flip y) R _ hx
  intro i hi
  change F (b i) y ∈ R
  apply map_mem_of_homogeneous_basis L b degree hb (F (b i)) R _ hy
  intro j hj
  simpa only [F, ← hi, ← hj, wordRelator_basis] using hr i j

private theorem wordRelator_mem_lower (hb : Homogeneous L b degree) (p s z : List I)
    (hlen : p.length + 2 + s.length < z.length)
    {d e : ZMod 2} {x y : V} (hx : x ∈ L.grading.piece d) (hy : y ∈ L.grading.piece e) :
    wordRelator L b p s d e x y ∈ (system L b degree).lowerRelations z := by
  apply wordRelator_mem L b degree hb _ p s _ hx hy
  apply basisRelator_mem L b degree hb _ p s
  intro i j h
  apply rule_mem_lower L b degree z p s i j h
  apply Prod.Lex.left
  simp only [List.length_append, List.length_cons]
  omega

private theorem basisRelator_mem_lower (z p s : List I) (i j : I)
    (h : reduciblePair degree i j) (hz : WordBelow (p ++ i :: j :: s) z) :
    basisRelator L b degree p s i j ∈ (system L b degree).lowerRelations z := by
  rcases h with h | ⟨rfl, h⟩
  · rw [basisRelator_desc _ _ _ _ _ _ _ h]
    exact rule_mem_lower L b degree z p s i j (Or.inl h) hz
  · rw [basisRelator_odd _ _ _ _ _ _ h]
    exact Submodule.smul_mem _ _ (rule_mem_lower L b degree z p s i i (Or.inr ⟨rfl, h⟩) hz)

/-- The difference of the two signed three-crossing expansions is a sum of short relators. -/
private theorem braid_mem_lower (hb : Homogeneous L b degree) (p s : List I) (i j l : I) :
    let D := basisRelator L b degree
    let e := crosses (k := k) degree
    D p (l :: s) i j + e i j • D (p ++ [j]) s i l +
        (e i j * e i l) • D p (i :: s) j l -
      D (p ++ [i]) s j l - e j l • D p (j :: s) i l -
        (e j l * e i l) • D (p ++ [l]) s i j ∈
      (system L b degree).lowerRelations (p ++ i :: j :: l :: s) := by
  dsimp only
  let z := p ++ i :: j :: l :: s
  let R := (system L b degree).lowerRelations z
  let D := wordRelator L b p s
  let A := D (degree i + degree j) (degree l) (bracket L b i j) (b l)
  let B := D (degree j) (degree i + degree l) (b j) (bracket L b i l)
  let C := D (degree i) (degree j + degree l) (b i) (bracket L b j l)
  have hlen : p.length + 2 + s.length < z.length := by
    simp only [z, List.length_append, List.length_cons]
    omega
  have hA : A ∈ R := wordRelator_mem_lower L b degree hb p s z hlen
    (L.bracket_mem (hb i) (hb j)) (hb l)
  have hB : B ∈ R := wordRelator_mem_lower L b degree hb p s z hlen
    (hb j) (L.bracket_mem (hb i) (hb l))
  have hC : C ∈ R := wordRelator_mem_lower L b degree hb p s z hlen
    (hb i) (L.bracket_mem (hb j) (hb l))
  have h := R.add_mem (R.sub_mem (R.neg_mem hA)
    (R.smul_mem (crosses (k := k) degree i j) hB)) hC
  convert h using 1
  have hs : paritySign k (degree i) (degree j) * paritySign k (degree j) (degree i + degree l) =
      paritySign k (degree j) (degree l) := by
    rw [sign_add, sign_symm (i := degree j) (j := degree i), ← mul_assoc, sign_sq, one_mul]
  simp only [A, B, C, D, basisRelator, crosses, wordRelator_apply, letter_basis,
    wordPair_single_left, wordPair_single_right, one_smul, List.append_assoc, List.cons_append,
    List.nil_append, sign_add_left, L.jacobi (hb i) (hb j) (hb l), map_add, map_smul]
  -- The sign for the middle short relator includes its coefficient from the first crossing.
  simp only [smul_sub, smul_smul, hs]
  simp only [sign_add]
  module

private theorem odd_triple_diamond (hb : Homogeneous L b degree) (p s : List I) (i : I)
    (hi : degree i = 1) :
    rhs L b degree p (i :: s) i i - rhs L b degree (p ++ [i]) s i i ∈
      (system L b degree).lowerRelations (p ++ i :: i :: i :: s) := by
  have hodd : b i ∈ L.grading.piece 1 := hi ▸ hb i
  have heven : bracket L b i i ∈ L.grading.piece 0 := by
    simpa only [show (1 : ZMod 2) + 1 = 0 by decide] using L.bracket_mem hodd hodd
  have hz : L.bracket (bracket L b i i) (b i) = 0 := by
    rw [L.skew heven hodd, L.oddTriple hodd, smul_zero]
  let z := p ++ i :: i :: i :: s
  have hlen : p.length + 2 + s.length < z.length := by
    simp only [z, List.length_append, List.length_cons]
    omega
  have h := (system L b degree).lowerRelations z |>.smul_mem ((2 : k)⁻¹)
    (wordRelator_mem_lower L b degree hb p s z hlen heven hodd)
  simpa only [rhs, replacement, lt_irrefl, ite_false, map_smul, wordRelator_apply, hz,
    map_zero, sub_zero, paritySign_zero_left, one_smul, letter_basis, wordPair_single_left,
    wordPair_single_right, List.append_nil, List.nil_append, List.cons_append, smul_sub] using h

private theorem overlap_diamond (hb : Homogeneous L b degree) (p s : List I) (i j l : I)
    (hij : reduciblePair degree i j) (hjl : reduciblePair degree j l) :
    rhs L b degree p (l :: s) i j - rhs L b degree (p ++ [i]) s j l ∈
      (system L b degree).lowerRelations (p ++ i :: j :: l :: s) := by
  by_cases hil : l < i
  swap
  · have le₁ : j ≤ i := hij.elim le_of_lt (fun h => h.1.ge)
    have le₂ : l ≤ j := hjl.elim le_of_lt (fun h => h.1.ge)
    have hli : i = l := le_antisymm (le_of_not_gt hil) (le₂.trans le₁)
    subst l
    have hij' : j = i := le_antisymm le₁ le₂
    subst j
    exact odd_triple_diamond L b degree hb p s i
      (hij.elim (fun h => (lt_irrefl i h).elim) And.right)
  let z := p ++ i :: j :: l :: s
  let R := (system L b degree).lowerRelations z
  let Q := R.mkQ
  let D := basisRelator L b degree
  let r := rhs L b degree
  let e := crosses (k := k) degree
  have zero_of_lower (a c : List I) (x y : I) (hr : reduciblePair degree x y)
      (ht : WordBelow (a ++ x :: y :: c) z) : Q (D a c x y) = 0 :=
    (Submodule.Quotient.mk_eq_zero R).2 (basisRelator_mem_lower L b degree z a c x y hr ht)
  have hA (h : j < i) : WordBelow ((p ++ [j]) ++ i :: l :: s) z := by
    simpa only [z, List.append_assoc, List.cons_append, List.nil_append] using
      swapped_word_below p (l :: s) i j h
  have hB (h : l < j) : WordBelow (p ++ i :: l :: j :: s) z := by
    simpa only [z, List.append_assoc, List.cons_append, List.nil_append] using
      swapped_word_below (p ++ [i]) s j l h
  have hA' : WordBelow (p ++ j :: l :: i :: s) z := by
    have hs := swapped_word_below (p ++ [j]) s i l hil
    rcases hij with h | ⟨h, _⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        Shared.Lie.PBW.WordBelow.trans hs (hA h)
    · simpa only [h, z, List.append_assoc, List.cons_append, List.nil_append] using hs
  have hB' : WordBelow ((p ++ [l]) ++ i :: j :: s) z := by
    have hs := swapped_word_below p (j :: s) i l hil
    rcases hjl with h | ⟨h, _⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        Shared.Lie.PBW.WordBelow.trans hs (hB h)
    · simpa only [h, z, List.append_assoc, List.cons_append, List.nil_append] using hs
  have hbraid := (Submodule.Quotient.mk_eq_zero R).2 (braid_mem_lower L b degree hb p s i j l)
  change Q (D p (l :: s) i j + e i j • D (p ++ [j]) s i l +
      (e i j * e i l) • D p (i :: s) j l - D (p ++ [i]) s j l -
      e j l • D p (j :: s) i l - (e j l * e i l) • D (p ++ [l]) s i j) = 0 at hbraid
  simp only [map_add, map_sub, map_smul, zero_of_lower p (i :: s) j l hjl hA',
    zero_of_lower (p ++ [l]) s i j hij hB', smul_zero, add_zero, sub_zero] at hbraid
  apply (Submodule.Quotient.mk_eq_zero R).1
  change Q (r p (l :: s) i j - r (p ++ [i]) s j l) = 0
  rw [map_sub]
  have hdesc (a c : List I) (x y : I) (h : y < x) :
      D a c x y = delta (a ++ x :: y :: c) - r a c x y :=
    basisRelator_desc L b degree a c x y h
  have hodd (a c : List I) (x : I) (h : degree x = 1) :
      D a c x x = (2 : k) • (delta (a ++ x :: x :: c) - r a c x x) :=
    basisRelator_odd L b degree a c x h
  rcases hij with hij | ⟨hij, hi⟩ <;> rcases hjl with hjl | ⟨hjl, hj⟩
  · have ha := zero_of_lower (p ++ [j]) s i l (Or.inl hil) (hA hij)
    have hb := zero_of_lower p (j :: s) i l (Or.inl hil) (hB hjl)
    simp only [ha, hb, hdesc _ _ _ _ hij, hdesc _ _ _ _ hjl, map_sub, smul_zero,
      add_zero, sub_zero, List.append_assoc, List.cons_append, List.nil_append] at hbraid
    calc
      _ = -((Q (delta z) - Q (r p (l :: s) i j)) -
            (Q (delta z) - Q (r (p ++ [i]) s j l))) := by
          abel
      _ = 0 := by rw [hbraid, neg_zero]
  · subst l
    have ha := zero_of_lower (p ++ [j]) s i j (Or.inl hil) (hA hij)
    have hs : e j j = -1 := by simp [e, crosses, hj]
    rw [ha, smul_zero, add_zero] at hbraid
    simp only [hdesc _ _ _ _ hij, hodd _ _ _ hj, map_sub, map_smul, hs, neg_one_smul,
      List.append_assoc, List.cons_append, List.nil_append] at hbraid
    apply (smul_eq_zero_iff_right (NeZero.ne (2 : k))).mp
    calc
      _ = -((Q (delta z) - Q (r p (j :: s) i j)) -
            (2 : k) • (Q (delta z) - Q (r (p ++ [i]) s j j)) -
            -(Q (delta z) - Q (r p (j :: s) i j))) := by module
      _ = 0 := by rw [hbraid, neg_zero]
  · subst j
    have hb := zero_of_lower p (i :: s) i l (Or.inl hil) (hB hjl)
    have hs : e i i = -1 := by simp [e, crosses, hi]
    rw [hb, smul_zero, sub_zero] at hbraid
    simp only [hdesc _ _ _ _ hjl, hodd _ _ _ hi, map_sub, map_smul, hs, neg_one_smul,
      List.append_assoc, List.cons_append, List.nil_append] at hbraid
    apply (smul_eq_zero_iff_right (NeZero.ne (2 : k))).mp
    calc
      _ = -((2 : k) • (Q (delta z) - Q (r p (l :: s) i i)) +
            -(Q (delta z) - Q (r (p ++ [i]) s i l)) -
            (Q (delta z) - Q (r (p ++ [i]) s i l))) := by module
      _ = 0 := by rw [hbraid, neg_zero]
  · subst j
    subst l
    exact (lt_irrefl i hil).elim

private theorem diamond (hb : Homogeneous L b degree) : (system L b degree).Diamond := by
  intro w f₁ f₂ h₁ h₂
  rcases h₁ with ⟨p, s, i, j, hij, rfl, rfl⟩
  rcases h₂ with ⟨q, t, a, c, hac, he, rfl⟩
  rcases adjacent_occurrence_cases p s q t i j a c he with h | h | h | h | h
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    simp
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact overlap_diamond L b degree hb p t i a c hij hac
  · rcases h with ⟨rfl, rfl, rfl⟩
    have h := ((system L b degree).lowerRelations (q ++ a :: i :: j :: s)).neg_mem
      (overlap_diamond L b degree hb q s a i j hac hij)
    simpa [List.append_assoc] using h
  · rcases h with ⟨m, rfl, rfl⟩
    exact disjoint_diamond L b degree p m t i j a c hij hac
  · rcases h with ⟨m, rfl, rfl⟩
    have h := ((system L b degree).lowerRelations (q ++ a :: c :: (m ++ i :: j :: s))).neg_mem
      (disjoint_diamond L b degree q m s a c i j hac hij)
    simpa [List.append_assoc] using h

/-- The tensor algebra on a based module is the algebra of its basis words. -/
private def wordAlgebra : TensorAlgebra k V ≃ₐ[k] MonoidAlgebra k (FreeMonoid I) :=
  (TensorAlgebra.equivFreeAlgebra b).trans FreeAlgebra.equivMonoidAlgebraFreeMonoid

private def toTensor : WordModule k I ≃ₗ[k] TensorAlgebra k V :=
  (MonoidAlgebra.coeffLinearEquiv k).symm.trans (wordAlgebra b).symm.toLinearEquiv

private abbrev tensorWord (l : List I) : TensorAlgebra k V :=
  word (TensorAlgebra.ι k) (l.map b)

omit [NeZero (2 : k)] in
private theorem word_append {A : Type*} [Ring A] [Algebra k A] (f : V →ₗ[k] A)
    (p s : List V) : word f (p ++ s) = word f p * word f s := by
  simp [word, List.prod_append]

omit [NeZero (2 : k)] [LinearOrder I] in
private theorem tensorWord_append (p s : List I) :
    tensorWord b (p ++ s) = tensorWord b p * tensorWord b s := by
  rw [tensorWord, List.map_append, word_append]

omit [NeZero (2 : k)] [LinearOrder I] in
private theorem toTensor_delta (l : List I) : toTensor b (delta l) = tensorWord b l := by
  change (wordAlgebra b).symm (MonoidAlgebra.single (FreeMonoid.ofList l) 1) = _
  induction l with
  | nil =>
    change (wordAlgebra b).symm (MonoidAlgebra.single 1 1) = 1
    rw [← MonoidAlgebra.one_def, map_one]
  | cons i l ih =>
    have hι : wordAlgebra b (TensorAlgebra.ι k (b i)) =
        MonoidAlgebra.single (FreeMonoid.of i) 1 := by
      simp [wordAlgebra, FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of]
    have hm : MonoidAlgebra.single (FreeMonoid.ofList (i :: l)) (1 : k) =
        MonoidAlgebra.single (FreeMonoid.of i) 1 *
          MonoidAlgebra.single (FreeMonoid.ofList l) 1 := by
      rw [MonoidAlgebra.single_mul_single, one_mul]
      rfl
    rw [hm, map_mul, ← hι, AlgEquiv.symm_apply_apply, ih]
    rfl

omit [NeZero (2 : k)] [LinearOrder I] in
private theorem toTensor_letter (x : V) : toTensor b (letter b x) = TensorAlgebra.ι k x := by
  have h : (toTensor b).toLinearMap.comp (letter b) = TensorAlgebra.ι k := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, letter_basis, toTensor_delta]
    simp [tensorWord, word]
  exact LinearMap.congr_fun h x

omit [NeZero (2 : k)] in
private theorem toTensor_context (p s : List I) (f : WordModule k I) :
    toTensor b (context p s f) = tensorWord b p * toTensor b f * tensorWord b s := by
  let F := (toTensor b).toLinearMap.comp (context p s)
  let G := (LinearMap.mulRight k (tensorWord b s)).comp
    ((LinearMap.mulLeft k (tensorWord b p)).comp (toTensor b).toLinearMap)
  have h : F = G := by
    ext l
    simp [F, G, toTensor_delta, tensorWord_append, mul_assoc]
  exact LinearMap.congr_fun h f

omit [NeZero (2 : k)] in
private theorem toTensor_pair (f g : WordModule k I) :
    toTensor b (wordPair [] [] [] f g) = toTensor b f * toTensor b g := by
  let F := (toTensor b).toLinearMap.comp ((wordPair (k := k) [] [] []).flip g)
  let G := (LinearMap.mulRight k (toTensor b g)).comp (toTensor b).toLinearMap
  have h : F = G := by
    ext l
    simp [F, G, toTensor_context, toTensor_delta, tensorWord, word]
  exact LinearMap.congr_fun h f

private theorem toTensor_relator (d e : ZMod 2) (x y : V) :
    toTensor b (wordRelator L b [] [] d e x y) = relator L d e x y := by
  simp only [wordRelator_apply, map_sub, map_smul, toTensor_pair, toTensor_letter, context_empty,
    relator]

private theorem context_relator (p s : List I) (i j : I) :
    context p s (basisRelator L b degree [] [] i j) = basisRelator L b degree p s i j := by
  simp [basisRelator, List.append_assoc]

private theorem toTensor_basisRelator (p s : List I) (i j : I) :
    toTensor b (basisRelator L b degree p s i j) =
      tensorWord b p * relator L (degree i) (degree j) (b i) (b j) * tensorWord b s := by
  rw [← context_relator L b degree, toTensor_context, ← wordRelator_basis, toTensor_relator]

/-- Evaluation in the adopted enveloping quotient. -/
private def evaluate : WordModule k I →ₗ[k] Enveloping L :=
  (quotientMap L).toLinearMap.comp (toTensor b).toLinearMap

omit [LinearOrder I] in
private theorem evaluate_delta (l : List I) : evaluate L b (delta l) = monomial L b l := by
  change quotientMap L (toTensor b (delta l)) = _
  rw [toTensor_delta]
  simp only [monomial, word, map_list_prod, List.map_map]
  rfl

private theorem relations_le_ker_evaluate (hb : Homogeneous L b degree) :
    (system L b degree).relations ≤ LinearMap.ker (evaluate L b) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨_, _, ⟨p, s, i, j, h, rfl, rfl⟩, rfl⟩
  have hraw (x y : I) :
      basisRelator L b degree p s x y ∈ LinearMap.ker (evaluate L b) := by
    rw [LinearMap.mem_ker]
    change quotientMap L (toTensor b (basisRelator L b degree p s x y)) = 0
    rw [toTensor_basisRelator]
    apply (quotientMap_eq_zero_iff L _).2
    exact (relationIdeal L).mul_mem_right _ _ ((relationIdeal L).mul_mem_left _ _
      (TwoSidedIdeal.subset_span ⟨degree x, degree y, b x, b y, hb x, hb y, rfl⟩))
  change delta (p ++ i :: j :: s) - rhs L b degree p s i j ∈ LinearMap.ker (evaluate L b)
  rcases h with h | ⟨rfl, h⟩
  · rw [← basisRelator_desc L b degree p s i j h]
    exact hraw i j
  · have hm := (LinearMap.ker (evaluate L b)).smul_mem ((2 : k)⁻¹) (hraw i i)
    simpa only [basisRelator_odd L b degree p s i h, smul_smul, half_two, one_smul] using hm

private theorem relations_eq_ker_evaluate (hb : Homogeneous L b degree) :
    (system L b degree).relations = LinearMap.ker (evaluate L b) := by
  refine le_antisymm (relations_le_ker_evaluate L b degree hb) ?_
  let R := (system L b degree).relations
  let M := R.map (toTensor b).toLinearMap
  have mul_left {a x : TensorAlgebra k V} (hx : x ∈ M) : a * x ∈ M := by
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := (toTensor b).surjective a
    change toTensor b g * toTensor b f ∈ M
    rw [congrArg (toTensor b) (as_sum_of_singles g)]
    simp only [map_sum, Finset.sum_mul, map_smul, smul_mul_assoc, toTensor_delta]
    refine M.sum_mem (fun l _ => M.smul_mem _ ?_)
    refine ⟨context l [] f, context_closed L b degree l [] f hf, ?_⟩
    simp only [LinearEquiv.coe_coe, toTensor_context, show tensorWord b [] = 1 from rfl, mul_one]
  have mul_right {x a : TensorAlgebra k V} (hx : x ∈ M) : x * a ∈ M := by
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := (toTensor b).surjective a
    change toTensor b f * toTensor b g ∈ M
    rw [congrArg (toTensor b) (as_sum_of_singles g)]
    simp only [map_sum, Finset.mul_sum, map_smul, mul_smul_comm, toTensor_delta]
    refine M.sum_mem (fun l _ => M.smul_mem _ ?_)
    refine ⟨context [] l f, context_closed L b degree [] l f hf, ?_⟩
    simp only [LinearEquiv.coe_coe, toTensor_context, show tensorWord b [] = 1 from rfl, one_mul]
  let J := TwoSidedIdeal.mk' (M : Set (TensorAlgebra k V))
    M.zero_mem M.add_mem M.neg_mem mul_left mul_right
  have mem_J (x : TensorAlgebra k V) : x ∈ J ↔ x ∈ M := by
    simp only [J, TwoSidedIdeal.mem_mk', SetLike.mem_coe]
  have hJ : relationIdeal L ≤ J := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨d, e, x, y, hx, hy, rfl⟩
    refine (mem_J _).2 ⟨wordRelator L b [] [] d e x y, ?_, toTensor_relator L b d e x y⟩
    apply wordRelator_mem L b degree hb R [] [] _ hx hy
    exact basisRelator_mem L b degree hb R [] [] (rule_mem L b degree [] [])
  intro f hf
  have hf' : quotientMap L (toTensor b f) = 0 := hf
  have ht := (mem_J _).1 (hJ ((quotientMap_eq_zero_iff L _).1 hf'))
  obtain ⟨g, hg, he⟩ := ht
  have hgf : g = f := (toTensor b).injective he
  exact hgf ▸ hg

omit [LinearOrder I] in
private theorem evaluate_surjective : Function.Surjective (evaluate L b) :=
  (SuperEnveloping.quotientMap_surjective L).comp (toTensor b).surjective

private def quotientEquiv (hb : Homogeneous L b degree) :
    (WordModule k I ⧸ (system L b degree).relations) ≃ₗ[k] Enveloping L :=
  (Submodule.quotEquivOfEq _ _ (relations_eq_ker_evaluate L b degree hb)).trans
    ((evaluate L b).quotKerEquivOfSurjective (evaluate_surjective L b))

private theorem quotientEquiv_mk (hb : Homogeneous L b degree) (f : WordModule k I) :
    quotientEquiv L b degree hb ((system L b degree).relations.mkQ f) = evaluate L b f := by
  simp only [quotientEquiv, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Ordered words with no repeated odd letters are a basis of the enveloping quotient. -/
theorem orderedBasis_exists (hb : Homogeneous L b degree) :
    ∃ B : Module.Basis (OrderedWord degree) k (Enveloping L),
      ∀ l, B l = monomial L b l.val := by
  let S := system L b degree
  let reindex : {l // ¬ S.Reducible l} ≃ OrderedWord degree :=
    (Equiv.refl (List I)).subtypeEquiv (irreducible_iff L b degree)
  refine ⟨((S.irreducibleBasis (diamond L b degree hb)).reindex reindex).map
    (quotientEquiv L b degree hb), fun l => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.reindex_apply, System.irreducibleBasis_apply,
    quotientEquiv_mk, evaluate_delta]
  rfl

private theorem below_length {l w : List I} (h : WordBelow l w) : l.length ≤ w.length := by
  exact Prod.lex_def.mp h |>.elim Nat.le_of_lt (fun h => h.1.le)

private abbrev orderedSpan (n : ℤ) : Submodule k (Enveloping L) :=
  Submodule.span k (Set.range (fun l : {l : OrderedWord degree // (l.val.length : ℤ) ≤ n} =>
    monomial L b l.val.val))

private theorem monomial_mem_orderedSpan (hb : Homogeneous L b degree) (n : ℤ)
    (l : List I) (hlen : (l.length : ℤ) ≤ n) : monomial L b l ∈ orderedSpan L b degree n := by
  classical
  let S := system L b degree
  let R := orderedSpan L b degree n
  induction l using S.wellFounded.induction with
  | h l ih =>
    by_cases hl : S.Reducible l
    · let f := S.chosen l hl
      have hrel : delta l - f ∈ S.relations :=
        Submodule.subset_span ⟨l, f, S.chosen_rule l hl, rfl⟩
      have he : evaluate L b (delta l) = evaluate L b f := by
        apply sub_eq_zero.mp
        rw [← map_sub]
        exact relations_le_ker_evaluate L b degree hb hrel
      rw [← evaluate_delta, he, congrArg (evaluate L b) (as_sum_of_singles f), map_sum]
      refine R.sum_mem (fun t ht => ?_)
      rw [map_smul, evaluate_delta]
      have hlt := below_length (S.decreases l f (S.chosen_rule l hl) t ht)
      exact R.smul_mem _ (ih t (S.decreases l f (S.chosen_rule l hl) t ht)
        ((Int.ofNat_le.mpr hlt).trans hlen))
    · exact Submodule.subset_span ⟨⟨⟨l, (irreducible_iff L b degree l).mp hl⟩, hlen⟩, rfl⟩

private theorem word_mem_orderedSpan (hb : Homogeneous L b degree) (n : ℤ)
    (xs : List V) (hx : (xs.length : ℤ) ≤ n) : word (ι L) xs ∈ orderedSpan L b degree n := by
  have h (ys : List V) (p : List I) (hlen : (p.length : ℤ) + ys.length ≤ n) :
      word (ι L) (p.map b ++ ys) ∈ orderedSpan L b degree n := by
    induction ys generalizing p with
    | nil =>
      simpa only [List.append_nil, monomial] using
        monomial_mem_orderedSpan L b degree hb n p (by simpa using hlen)
    | cons x ys ih =>
      let F : V →ₗ[k] Enveloping L :=
        (LinearMap.mulRight k (word (ι L) ys)).comp
          ((LinearMap.mulLeft k (monomial L b p)).comp (ι L))
      have hF (y : V) : F y = word (ι L) (p.map b ++ y :: ys) := by
        simp [F, monomial, word, List.prod_append, mul_assoc]
      rw [← hF]
      apply map_mem_of_basis b F (orderedSpan L b degree n) _ x
      intro i
      rw [hF]
      have hlen' : ((p ++ [i]).length : ℤ) + ys.length ≤ n := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen
        omega
      simpa only [List.map_append, List.map_singleton, List.append_assoc, List.singleton_append]
        using ih (p ++ [i]) hlen'
  simpa using h xs [] (by simpa using hx)

/-- Each filtration step is spanned by precisely the indicated range of lengths. -/
theorem filtration_eq_span (hb : Homogeneous L b degree) (n : ℤ) :
    filtration L n = Submodule.span k
      (Set.range (fun l : {l : OrderedWord degree // (l.val.length : ℤ) ≤ n} =>
        monomial L b l.val.val)) := by
  change filtration L n = orderedSpan L b degree n
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨xs, hx, rfl⟩
    exact word_mem_orderedSpan L b degree hb n xs hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact word_mem (ι L) (by simpa using l.property)

end

end LieNotes.SuperRestricted.SuperPbwBasis
