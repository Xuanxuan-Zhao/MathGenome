import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWOrdered
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.UniversalEnveloping
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic


/-! A linear form of the Diamond Lemma. Rules already include their contexts;
no compatibility with arbitrary concatenation is hidden in the hypotheses.
The lower-relation condition is precisely the ambiguity check to be discharged
for the concrete Lie rules, not an assumption of PBW. -/
namespace Shared.Lie.PBW.LinearReduction
universe u v
variable {k : Type u} {W : Type v} [CommRing k]

structure System (k : Type u) (W : Type v) [CommRing k] where
  below : W → W → Prop
  wellFounded : WellFounded below
  rule : W → (W →₀ k) → Prop
  decreases : ∀ w f, rule w f → ∀ t ∈ f.support, below t w

namespace System
noncomputable section
variable (S : System k W)

def Reducible (w : W) : Prop := ∃ f, S.rule w f

def relations : Submodule k (W →₀ k) :=
  Submodule.span k {d | ∃ w f, S.rule w f ∧ d = Finsupp.single w 1 - f}

def lowerRelations (w : W) : Submodule k (W →₀ k) :=
  Submodule.span k {d | ∃ t f, S.below t w ∧ S.rule t f ∧ d = Finsupp.single t 1 - f}

/-- Two right-hand sides at the same head differ by lower-head relations. -/
def Diamond : Prop := ∀ w f₁ f₂, S.rule w f₁ → S.rule w f₂ →
  f₁ - f₂ ∈ S.lowerRelations w

noncomputable def chosen (w : W) (h : S.Reducible w) : W →₀ k := h.choose

theorem chosen_rule (w : W) (h : S.Reducible w) : S.rule w (S.chosen w h) :=
  h.choose_spec

noncomputable def normalWord : W → (W →₀ k) := by
  classical
  exact S.wellFounded.fix fun w rec =>
    if h : S.Reducible w then
      (S.chosen w h).sum fun t c => c • (if ht : S.below t w then rec t ht else 0)
    else Finsupp.single w 1

noncomputable def normal : (W →₀ k) →ₗ[k] (W →₀ k) :=
  Finsupp.linearCombination k S.normalWord

@[simp] theorem normal_single (w : W) (c : k) :
    S.normal (Finsupp.single w c) = c • S.normalWord w :=
  Finsupp.linearCombination_single _ _ _

theorem normalWord_irreducible (w : W) (h : ¬ S.Reducible w) :
    S.normalWord w = Finsupp.single w 1 := by
  classical
  rw [normalWord, WellFounded.fix_eq]
  simp only [h, dite_false]

theorem normalWord_chosen (w : W) (h : S.Reducible w) :
    S.normalWord w = S.normal (S.chosen w h) := by
  classical
  rw [normalWord, WellFounded.fix_eq]
  simp only [h, dite_true]
  change (S.chosen w h).sum _ = (S.chosen w h).sum _
  apply Finset.sum_congr rfl
  intro t ht
  simp only [S.decreases w _ (S.chosen_rule w h) t ht, dite_true]
  rfl

/-- Ambiguity resolution proves invariance under every rule, by induction on
its head. In particular, the chosen rule in `normalWord` is immaterial. -/
theorem normalWord_rule (hd : S.Diamond) (w : W) (f : W →₀ k)
    (hf : S.rule w f) : S.normalWord w = S.normal f := by
  classical
  induction w using S.wellFounded.induction generalizing f with
  | h w ih =>
    let hr : S.Reducible w := ⟨f, hf⟩
    have hz : S.lowerRelations w ≤ LinearMap.ker S.normal := by
      apply Submodule.span_le.mpr
      rintro d ⟨t, r, htw, htr, rfl⟩
      change S.normal (Finsupp.single t 1 - r) = 0
      simp only [map_sub, normal_single, one_smul, ih t htw r htr, sub_self]
    have he : S.normal f = S.normal (S.chosen w hr) := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact hz (hd w f (S.chosen w hr) hf (S.chosen_rule w hr))
    exact (S.normalWord_chosen w hr).trans he.symm

theorem relations_le_ker (hd : S.Diamond) : S.relations ≤ LinearMap.ker S.normal := by
  apply Submodule.span_le.mpr
  rintro d ⟨w, f, hf, rfl⟩
  change S.normal (Finsupp.single w 1 - f) = 0
  simp only [map_sub, normal_single, one_smul, S.normalWord_rule hd w f hf, sub_self]

/-- The discrepancy between an expression and its normal form is a sum of
its single-word discrepancies. This statement is support-sensitive. -/
theorem sub_normal_mem_of_support (f : W →₀ k) (R : Submodule k (W →₀ k))
    (h : ∀ w ∈ f.support, Finsupp.single w 1 - S.normalWord w ∈ R) :
    f - S.normal f ∈ R := by
  classical
  change ((LinearMap.id : (W →₀ k) →ₗ[k] (W →₀ k)) - S.normal) f ∈ R
  rw [← f.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro w hw
  have he : Finsupp.single w (f w) = f w • Finsupp.single w 1 := by simp
  rw [he, map_smul]
  apply R.smul_mem
  simpa using h w hw

theorem single_sub_normalWord_mem (w : W) :
    Finsupp.single w 1 - S.normalWord w ∈ S.relations := by
  classical
  induction w using S.wellFounded.induction with
  | h w ih =>
    by_cases hr : S.Reducible w
    · rw [S.normalWord_chosen w hr]
      have h₁ : Finsupp.single w 1 - S.chosen w hr ∈ S.relations :=
        Submodule.subset_span ⟨w, _, S.chosen_rule w hr, rfl⟩
      have h₂ : S.chosen w hr - S.normal (S.chosen w hr) ∈ S.relations :=
        S.sub_normal_mem_of_support _ _ (fun t ht =>
          ih t (S.decreases w _ (S.chosen_rule w hr) t ht))
      convert S.relations.add_mem h₁ h₂ using 1 <;> abel
    · rw [S.normalWord_irreducible w hr, sub_self]
      exact S.relations.zero_mem

theorem sub_normal_mem (f : W →₀ k) : f - S.normal f ∈ S.relations :=
  S.sub_normal_mem_of_support f S.relations (fun w _ => S.single_sub_normalWord_mem w)

/-- The ambiguity hypothesis gives the exact kernel, not merely one inclusion. -/
theorem ker_normal (hd : S.Diamond) : LinearMap.ker S.normal = S.relations := by
  apply le_antisymm _ (S.relations_le_ker hd)
  intro f hf
  have he : S.normal f = 0 := hf
  simpa only [he, sub_zero] using S.sub_normal_mem f

/-- Every output is supported on words to which no rule applies. -/
theorem normalWord_support (w : W) :
    ∀ t ∈ (S.normalWord w).support, ¬ S.Reducible t := by
  classical
  let R := Finsupp.supported k k {t | ¬ S.Reducible t}
  have hs : ∀ w, S.normalWord w ∈ R := by
    intro w
    induction w using S.wellFounded.induction with
    | h w ih =>
      by_cases hr : S.Reducible w
      · rw [S.normalWord_chosen w hr, normal, Finsupp.linearCombination_apply]
        exact Submodule.sum_mem _ (fun t ht => R.smul_mem _
          (ih t (S.decreases w _ (S.chosen_rule w hr) t ht)))
      · rw [S.normalWord_irreducible w hr]
        exact Finsupp.single_mem_supported _ _ hr
  exact (Finsupp.mem_supported _ _).mp (hs w)

/-- Normalization fixes the whole submodule of irreducible expressions. -/
theorem normal_eq_self (f : W →₀ k)
    (h : ∀ w ∈ f.support, ¬ S.Reducible w) : S.normal f = f := by
  classical
  rw [normal, Finsupp.linearCombination_apply]
  conv_rhs => rw [← f.sum_single]
  apply Finset.sum_congr rfl
  intro w hw
  dsimp only
  rw [S.normalWord_irreducible w (h w hw)]
  simp


/-- No linear combination of irreducible words is killed in the linear
quotient once the ambiguity check has been proved. -/
theorem irreducibles_independent (hd : S.Diamond) :
    LinearIndependent k (fun w : {w : W // ¬ S.Reducible w} =>
      S.relations.mkQ (Finsupp.single w.val 1)) := by
  let N := S.relations.liftQ S.normal (S.relations_le_ker hd)
  apply LinearIndependent.of_comp N
  have hi := (Finsupp.linearIndependent_single_one k W).comp
    (fun w : {w : W // ¬ S.Reducible w} => w.val) Subtype.val_injective
  change LinearIndependent k (fun w : {w : W // ¬ S.Reducible w} =>
    S.normal (Finsupp.single w.val 1))
  simp only [normal_single, one_smul]
  convert hi using 1
  funext w
  exact S.normalWord_irreducible w.val w.property

/-- Spanning of the linear quotient requires termination, but not confluence. -/
theorem irreducibles_span :
    Submodule.span k (Set.range (fun w : {w : W // ¬ S.Reducible w} =>
      S.relations.mkQ (Finsupp.single w.val 1))) = ⊤ := by
  classical
  let V := Submodule.span k (Set.range (fun w : {w : W // ¬ S.Reducible w} =>
      S.relations.mkQ (Finsupp.single w.val 1)))
  have hs : ∀ w, S.relations.mkQ (Finsupp.single w 1) ∈ V := by
    intro w
    induction w using S.wellFounded.induction with
    | h w ih =>
      by_cases hr : S.Reducible w
      · have he : S.relations.mkQ (Finsupp.single w 1) =
            S.relations.mkQ (S.chosen w hr) := by
          apply sub_eq_zero.mp
          rw [← map_sub]
          exact (Submodule.Quotient.mk_eq_zero _).mpr
            (Submodule.subset_span ⟨w, _, S.chosen_rule w hr, rfl⟩)
        rw [he, ← (S.chosen w hr).sum_single]
        simp only [Finsupp.sum, map_sum]
        apply V.sum_mem
        intro t ht
        have he : Finsupp.single t ((S.chosen w hr) t) =
            (S.chosen w hr) t • Finsupp.single t 1 := by simp
        rw [he, map_smul]
        exact V.smul_mem _ (ih t (S.decreases w _ (S.chosen_rule w hr) t ht))
      · exact Submodule.subset_span ⟨⟨w, hr⟩, rfl⟩
  apply top_unique
  intro q _
  obtain ⟨f, rfl⟩ := S.relations.mkQ_surjective q
  rw [← f.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply V.sum_mem
  intro w hw
  have he : Finsupp.single w (f w) = f w • Finsupp.single w 1 := by simp
  rw [he, map_smul]
  exact V.smul_mem _ (hs w)

/-- The full abstract linear Diamond Lemma, with all ambiguity hypotheses
visible. Its index includes every irreducible word, including units when
these are not heads of rules. -/
noncomputable def irreducibleBasis (hd : S.Diamond) :
    Module.Basis {w : W // ¬ S.Reducible w} k ((W →₀ k) ⧸ S.relations) :=
  Module.Basis.mk (S.irreducibles_independent hd) (by rw [S.irreducibles_span])

@[simp] theorem irreducibleBasis_apply (hd : S.Diamond)
    (w : {w : W // ¬ S.Reducible w}) :
    S.irreducibleBasis hd w = S.relations.mkQ (Finsupp.single w.val 1) :=
  Module.Basis.mk_apply _ _ _

end
end System
end Shared.Lie.PBW.LinearReduction

namespace Shared.Lie.PBW
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v w
variable {k : Type u} {g : Type v} {ι : Type w}
  [CommRing k] [LieRing g] [LieAlgebra k g] [LinearOrder ι]

@[simp] theorem monomial_nil (b : Module.Basis ι k g) : monomial b [] = 1 := by
  simp [monomial, word]

@[simp] theorem monomial_cons (b : Module.Basis ι k g) (i : ι) (l : List ι) :
    monomial b (i :: l) = inclusion k g (b i) * monomial b l := by
  simp [monomial, word]

theorem monomial_append (b : Module.Basis ι k g) (l r : List ι) :
    monomial b (l ++ r) = monomial b l * monomial b r := by
  simp [monomial, List.map_append, word_append]

@[simp] theorem orderedMonomial_empty (b : Module.Basis ι k g) :
    orderedMonomial b (emptyWord ι) = 1 := monomial_nil b

@[simp] theorem orderedMonomial_singleton (b : Module.Basis ι k g) (i : ι) :
    orderedMonomial b (singletonWord i) = inclusion k g (b i) := by
  simp [orderedMonomial, singletonWord]

/-- Number of strict inversions; finite even for an infinite index type. -/
def inversions : List ι → ℕ
  | [] => 0
  | a :: l => (l.filter (· < a)).length + inversions l

/-- Swapping an adjacent descent lowers the inversion count in every context. -/
theorem inversions_swap (p s : List ι) (a b : ι) (h : b < a) :
    inversions (p ++ a :: b :: s) = inversions (p ++ b :: a :: s) + 1 := by
  induction p with
  | nil => simp [inversions, h, not_lt_of_gt h]; omega
  | cons c p ih =>
    simp only [List.cons_append, inversions, List.filter_append, List.length_append,
      List.filter_cons]
    split <;> split <;> simp_all <;> omega

/-- Lexicographic length/inversion order; it does not order the basis itself. -/
def WordBelow (l r : List ι) : Prop :=
  Prod.Lex (· < ·) (· < ·) (l.length, inversions l) (r.length, inversions r)

theorem wordBelow_wellFounded : WellFounded (WordBelow (ι := ι)) :=
  InvImage.wf (fun l : List ι => (l.length, inversions l))
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

theorem swapped_word_below (p s : List ι) (i j : ι) (h : j < i) :
    WordBelow (p ++ j :: i :: s) (p ++ i :: j :: s) := by
  unfold WordBelow
  have hi := inversions_swap p s i j h
  have hl : (p ++ j :: i :: s).length = (p ++ i :: j :: s).length := by simp
  rw [hl]
  exact Prod.Lex.right _ (by omega)

theorem bracket_word_below (p s : List ι) (i j a : ι) :
    WordBelow (p ++ a :: s) (p ++ i :: j :: s) := by
  exact Prod.Lex.left _ _ (by simp)

/-- Every nonordered word has an adjacent descent. -/
theorem exists_descent (l : List ι) (h : ¬ l.Pairwise (· ≤ ·)) :
    ∃ p a b s, l = p ++ a :: b :: s ∧ b < a := by
  induction l with
  | nil => exact (h List.Pairwise.nil).elim
  | cons a l ih =>
    by_cases hl : l.Pairwise (· ≤ ·)
    · cases l with
      | nil => exact (h (by simp)).elim
      | cons b s =>
        refine ⟨[], a, b, s, rfl, ?_⟩
        by_contra hn
        have hab : a ≤ b := le_of_not_gt hn
        apply h
        exact List.pairwise_cons.mpr ⟨fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hab
          · exact hab.trans ((List.pairwise_cons.mp hl).1 x hx), hl⟩
    · obtain ⟨p, x, y, s, he, hxy⟩ := ih hl
      exact ⟨a :: p, x, y, s, by simp [he], hxy⟩

/-- An adjacent replacement in the actual quotient, including arbitrary context. -/
theorem monomial_swap (b : Module.Basis ι k g) (p s : List ι) (i j : ι) :
    monomial b (p ++ i :: j :: s) = monomial b (p ++ j :: i :: s) +
      monomial b p * inclusion k g ⁅b i, b j⁆ * monomial b s := by
  have h := (quotient k g).2 (b i) (b j)
  simp only [monomial_append, monomial_cons]
  rw [← h]
  noncomm_ring

/-- A linear map takes every vector into a submodule if it does so on a basis. -/
theorem map_mem_of_basis (b : Module.Basis ι k g) {N : Type*}
    [AddCommGroup N] [Module k N] (f : g →ₗ[k] N) (S : Submodule k N)
    (h : ∀ i, f (b i) ∈ S) (x : g) : f x ∈ S := by
  have hs : Submodule.span k (Set.range b) ≤ S.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [b.span_eq] at hs
  exact hs (Submodule.mem_top)

/-- Insert a basis-linear factor between two fixed words. -/
noncomputable def sandwich (b : Module.Basis ι k g) (p s : List ι) : g →ₗ[k] U k g :=
  (LinearMap.mulRight k (monomial b s)).comp
    ((LinearMap.mulLeft k (monomial b p)).comp (inclusion k g).toLinearMap)

@[simp] theorem sandwich_apply (b : Module.Basis ι k g) (p s : List ι) (x : g) :
    sandwich b p s x = monomial b p * inclusion k g x * monomial b s := rfl

/-- All basis words belong to the span of the nondecreasing words. -/
theorem monomial_mem_ordered_span (b : Module.Basis ι k g) (l : List ι) :
    monomial b l ∈ Submodule.span k (Set.range (orderedMonomial b)) := by
  classical
  let S := Submodule.span k (Set.range (orderedMonomial b))
  suffices ∀ n, ∀ l : List ι, l.length = n → monomial b l ∈ S by
    exact this l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    suffices ∀ m, ∀ l : List ι, l.length = n → inversions l = m → monomial b l ∈ S by
      intro l hl
      exact this (inversions l) l hl rfl
    intro m
    induction m using Nat.strong_induction_on with
    | h m ihm =>
      intro l hlen hinv
      by_cases hs : l.Pairwise (· ≤ ·)
      · exact Submodule.subset_span ⟨⟨l, hs⟩, rfl⟩
      obtain ⟨p, i, j, s, rfl, hji⟩ := exists_descent l hs
      rw [monomial_swap]
      apply S.add_mem
      · apply ihm (inversions (p ++ j :: i :: s))
        · have hi := inversions_swap p s i j hji
          omega
        · simpa only [List.length_append, List.length_cons] using hlen
        · rfl
      · apply map_mem_of_basis b (sandwich b p s) S _ ⁅b i, b j⁆
        intro a
        have ha := ihn (p.length + 1 + s.length) (by
          simp only [List.length_append, List.length_cons] at hlen
          omega) (p ++ a :: s) (by simp; omega)
        simpa only [monomial_append, monomial_cons, mul_assoc, sandwich_apply] using ha

/-- The spanning result also holds for words in arbitrary elements of g. -/
theorem word_mem_ordered_span (b : Module.Basis ι k g) (xs : List g) :
    word k g xs ∈ Submodule.span k (Set.range (orderedMonomial b)) := by
  classical
  let S := Submodule.span k (Set.range (orderedMonomial b))
  suffices ∀ xs : List g, ∀ p : List ι, monomial b p * word k g xs ∈ S by
    simpa using this xs []
  intro xs
  induction xs with
  | nil => intro p; simpa [word] using monomial_mem_ordered_span b p
  | cons x xs ih =>
    intro p
    let f : g →ₗ[k] U k g := (LinearMap.mulRight k (word k g xs)).comp
      ((LinearMap.mulLeft k (monomial b p)).comp (inclusion k g).toLinearMap)
    have hf : ∀ i, f (b i) ∈ S := by
      intro i
      have h := ih (p ++ [i])
      simpa [f, monomial_append, mul_assoc] using h
    have hx := map_mem_of_basis b f S hf x
    simpa [f, word, mul_assoc] using hx

theorem ordered_span (b : Module.Basis ι k g) :
    Submodule.span k (Set.range (orderedMonomial b)) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨m, hm⟩ := filtration_exhaustive k g a
  apply (Submodule.span_le.mpr ?_ : filtration k g m ≤ _) hm
  rintro _ ⟨xs, _, rfl⟩
  exact word_mem_ordered_span b xs

/-- The singleton words are distinct even when the coefficient ring is trivial. -/
theorem singletonWord_injective : Function.Injective (singletonWord (ι := ι)) := by
  intro i j h
  have he := congrArg Subtype.val h
  simpa [singletonWord] using he

/-- Once independence is established, the original Lie map is injective. -/
theorem inclusion_injective_of_independent (b : Module.Basis ι k g)
    (h : LinearIndependent k (orderedMonomial b)) : Function.Injective (inclusion k g) := by
  have hi : LinearIndependent k (fun i => inclusion k g (b i)) := by
    simpa [Function.comp_def] using h.comp singletonWord singletonWord_injective
  intro x y hxy
  apply b.repr.injective
  apply hi
  change Finsupp.linearCombination k ((inclusion k g).toLinearMap ∘ b) (b.repr x) =
    Finsupp.linearCombination k ((inclusion k g).toLinearMap ∘ b) (b.repr y)
  rw [Finsupp.linearCombination_linear_comp]
  change (inclusion k g).toLinearMap (Finsupp.linearCombination k b (b.repr x)) =
    (inclusion k g).toLinearMap (Finsupp.linearCombination k b (b.repr y))
  rw [b.linearCombination_repr, b.linearCombination_repr]
  exact hxy


/-! Concrete rules for the free module on basis words. The generic linear
Diamond Lemma above applies to this system once its ambiguities are checked. -/
abbrev WordModule (k : Type u) (ι : Type w) [CommRing k] := List ι →₀ k

/-- Prefix and suffix insertion on the free module of words. -/
noncomputable def context (p s : List ι) : WordModule k ι →ₗ[k] WordModule k ι :=
  Finsupp.linearCombination k (fun l => Finsupp.single (p ++ l ++ s) 1)

@[simp] theorem context_single (p s l : List ι) (c : k) :
    context p s (Finsupp.single l c) = Finsupp.single (p ++ l ++ s) c := by
  simp [context]

@[simp] theorem context_context (p s a c : List ι) (f : WordModule k ι) :
    context p s (context a c f) = context (p ++ a) (c ++ s) f := by
  have he : (context (k := k) p s).comp (context a c) = context (p ++ a) (c ++ s) := by
    ext l
    simp [List.append_assoc]
  exact LinearMap.congr_fun he f

@[simp] theorem context_empty (f : WordModule k ι) : context [] [] f = f := by
  have he : context (k := k) (ι := ι) [] [] = LinearMap.id := by
    ext l
    simp
  exact LinearMap.congr_fun he f

/-- A basis-linear letter, before passing to the enveloping quotient. -/
noncomputable def letter (b : Module.Basis ι k g) : g →ₗ[k] WordModule k ι :=
  (Finsupp.linearCombination k (fun i => Finsupp.single [i] 1)).comp b.repr.toLinearMap

@[simp] theorem letter_basis (b : Module.Basis ι k g) (i : ι) :
    letter b (b i) = Finsupp.single [i] 1 := by simp [letter]

noncomputable def ruleRhs (b : Module.Basis ι k g) (p s : List ι) (i j : ι) :
    WordModule k ι :=
  context p s (Finsupp.single [j, i] 1 + letter b ⁅b i, b j⁆)

theorem ruleRhs_decreases (b : Module.Basis ι k g) (p s : List ι) (i j : ι)
    (hji : j < i) : ∀ t ∈ (ruleRhs b p s i j).support,
      WordBelow t (p ++ i :: j :: s) := by
  let R := Finsupp.supported k k {t | WordBelow t (p ++ i :: j :: s)}
  have hr : ruleRhs b p s i j ∈ R := by
    unfold ruleRhs
    rw [map_add]
    apply R.add_mem
    · simp only [context_single]
      apply Finsupp.single_mem_supported k 1
      simpa only [Set.mem_setOf_eq, List.append_assoc, List.cons_append, List.nil_append] using
        swapped_word_below p s i j hji
    · apply map_mem_of_basis b ((context p s).comp (letter b)) R _ ⁅b i, b j⁆
      intro a
      simp only [LinearMap.comp_apply, letter_basis, context_single]
      apply Finsupp.single_mem_supported k 1
      simpa only [Set.mem_setOf_eq, List.append_assoc, List.cons_append, List.nil_append] using
        bracket_word_below p s i j a
  exact (Finsupp.mem_supported _ _).mp hr

/-- All contexts are part of the rule itself; length/inversion termination
therefore requires no semigroup-order hypothesis. -/
noncomputable def reductionSystem (b : Module.Basis ι k g) :
    LinearReduction.System k (List ι) where
  below := WordBelow
  wellFounded := wordBelow_wellFounded
  rule w f := ∃ p s i j, j < i ∧ w = p ++ i :: j :: s ∧ f = ruleRhs b p s i j
  decreases := by
    rintro w f ⟨p, s, i, j, hji, rfl, rfl⟩
    exact ruleRhs_decreases b p s i j hji

theorem irreducible_iff_ordered (b : Module.Basis ι k g) (l : List ι) :
    ¬ (reductionSystem b).Reducible l ↔ l.Pairwise (· ≤ ·) := by
  constructor
  · intro h
    by_contra hs
    obtain ⟨p, i, j, s, he, hji⟩ := exists_descent l hs
    exact h ⟨ruleRhs b p s i j, p, s, i, j, hji, he, rfl⟩
  · intro hs
    rintro ⟨f, p, s, i, j, hji, he, hf⟩
    rw [he] at hs
    have ht := (List.pairwise_append.mp hs).2.1
    have hij := (List.pairwise_cons.mp ht).1 j (by simp)
    exact (not_lt_of_ge hij) hji

/-- Stability of the relation span under every unused prefix and suffix. -/
theorem context_relations (b : Module.Basis ι k g) (p s : List ι)
    (f : WordModule k ι) (hf : f ∈ (reductionSystem b).relations) :
    context p s f ∈ (reductionSystem b).relations := by
  let R := (reductionSystem b).relations
  have he : R ≤ R.comap (context p s) := by
    apply Submodule.span_le.mpr
    rintro d ⟨w, r, ⟨a, c, i, j, hji, rfl, rfl⟩, rfl⟩
    change context p s (Finsupp.single (a ++ i :: j :: c) 1 - ruleRhs b a c i j) ∈ R
    have he : context p s (Finsupp.single (a ++ i :: j :: c) 1 - ruleRhs b a c i j) =
        Finsupp.single ((p ++ a) ++ i :: j :: (c ++ s)) 1 -
          ruleRhs b (p ++ a) (c ++ s) i j := by
      simp [ruleRhs, List.append_assoc]
    rw [he]
    exact Submodule.subset_span ⟨_, _, ⟨p ++ a, c ++ s, i, j, hji, rfl, rfl⟩, rfl⟩
  exact he hf

/-- Evaluation in the actual enveloping quotient. -/
noncomputable def evaluateWords (b : Module.Basis ι k g) : WordModule k ι →ₗ[k] U k g :=
  Finsupp.linearCombination k (monomial b)

@[simp] theorem evaluateWords_single (b : Module.Basis ι k g) (l : List ι) (c : k) :
    evaluateWords b (Finsupp.single l c) = c • monomial b l := by
  simp [evaluateWords]

@[simp] theorem evaluateWords_context (b : Module.Basis ι k g) (p s : List ι)
    (f : WordModule k ι) :
    evaluateWords b (context p s f) = monomial b p * evaluateWords b f * monomial b s := by
  have he : (evaluateWords b).comp (context p s) =
      (LinearMap.mulRight k (monomial b s)).comp
        ((LinearMap.mulLeft k (monomial b p)).comp (evaluateWords b)) := by
    ext l
    simp [monomial_append, mul_assoc]
  exact LinearMap.congr_fun he f

@[simp] theorem evaluateWords_letter (b : Module.Basis ι k g) (x : g) :
    evaluateWords b (letter b x) = inclusion k g x := by
  have he : (evaluateWords b).comp (letter b) = (inclusion k g).toLinearMap := by
    apply b.ext
    intro i
    simp [monomial_cons]
  exact LinearMap.congr_fun he x

/-- Every concrete reduction is sound in the specified U(g). -/
theorem relations_le_evaluateWords_ker (b : Module.Basis ι k g) :
    (reductionSystem b).relations ≤ LinearMap.ker (evaluateWords b) := by
  apply Submodule.span_le.mpr
  rintro d ⟨w, r, ⟨p, s, i, j, hji, rfl, rfl⟩, rfl⟩
  change evaluateWords b (Finsupp.single (p ++ i :: j :: s) 1 - ruleRhs b p s i j) = 0
  simp only [map_sub, evaluateWords_single, one_smul, ruleRhs,
    evaluateWords_context, map_add, evaluateWords_letter]
  rw [monomial_swap b p s i j]
  simp [monomial_append, monomial_cons, mul_add, add_mul, mul_assoc]


/-- The unoriented defining relation follows from the descending rules,
using alternation for equal indices and skew symmetry for the opposite order. -/
theorem commutator_mem_relations (b : Module.Basis ι k g) (i j : ι) (s : List ι) :
    Finsupp.single (i :: j :: s) 1 - Finsupp.single (j :: i :: s) 1 -
      context [] s (letter b ⁅b i, b j⁆) ∈ (reductionSystem b).relations := by
  have hdesc : ∀ a c : ι, c < a →
      Finsupp.single (a :: c :: s) 1 - Finsupp.single (c :: a :: s) 1 -
        context [] s (letter b ⁅b a, b c⁆) ∈ (reductionSystem b).relations := by
    intro a c hca
    have hr : Finsupp.single (a :: c :: s) 1 - ruleRhs b [] s a c ∈
        (reductionSystem b).relations :=
      Submodule.subset_span ⟨_, _, ⟨[], s, a, c, hca, rfl, rfl⟩, rfl⟩
    simpa [ruleRhs, sub_add_eq_sub_sub] using hr
  rcases lt_trichotomy j i with hji | he | hij
  · exact hdesc i j hji
  · subst j
    simp
  · have hn := (reductionSystem b).relations.neg_mem (hdesc j i hij)
    rw [← lie_skew (b j) (b i), map_neg, map_neg] at hn
    convert hn using 1 <;> abel

abbrev WordQuotient (b : Module.Basis ι k g) :=
  WordModule k ι ⧸ (reductionSystem b).relations

/-- Left multiplication by one generator acts on the linear quotient. -/
noncomputable def prependQuotient (b : Module.Basis ι k g) (i : ι) :
    Module.End k (WordQuotient b) :=
  (reductionSystem b).relations.mapQ (reductionSystem b).relations (context [i] [])
    (fun f hf => context_relations b [i] [] f hf)

@[simp] theorem prependQuotient_mk (b : Module.Basis ι k g) (i : ι) (f : WordModule k ι) :
    prependQuotient b i ((reductionSystem b).relations.mkQ f) =
      (reductionSystem b).relations.mkQ (context [i] [] f) := rfl

noncomputable def quotientAction (b : Module.Basis ι k g) :
    g →ₗ[k] Module.End k (WordQuotient b) := b.constr k (prependQuotient b)

@[simp] theorem quotientAction_basis (b : Module.Basis ι k g) (i : ι) :
    quotientAction b (b i) = prependQuotient b i := b.constr_basis k _ i

/-- The action of any element on a word is the expected linear prefix. -/
theorem quotientAction_single (b : Module.Basis ι k g) (x : g) (l : List ι) :
    quotientAction b x ((reductionSystem b).relations.mkQ (Finsupp.single l 1)) =
      (reductionSystem b).relations.mkQ (context [] l (letter b x)) := by
  have he : (LinearMap.applyₗ (R := k) (M₂ := WordQuotient b)
      ((reductionSystem b).relations.mkQ (Finsupp.single l 1))).comp (quotientAction b) =
      ((reductionSystem b).relations.mkQ.comp (context [] l)).comp (letter b) := by
    apply b.ext
    intro i
    simp [prependQuotient, List.append_assoc]
  exact LinearMap.congr_fun he x

theorem quotientAction_lie_basis (b : Module.Basis ι k g) (i j : ι) :
    quotientAction b ⁅b i, b j⁆ =
      ⁅quotientAction b (b i), quotientAction b (b j)⁆ := by
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := (reductionSystem b).relations.mkQ_surjective q
  have he : ∀ f : WordModule k ι,
      quotientAction b ⁅b i, b j⁆ ((reductionSystem b).relations.mkQ f) =
      ⁅quotientAction b (b i), quotientAction b (b j)⁆
        ((reductionSystem b).relations.mkQ f) := by
    suffices H : (quotientAction b ⁅b i, b j⁆).comp (reductionSystem b).relations.mkQ =
        (⁅quotientAction b (b i), quotientAction b (b j)⁆).comp
          (reductionSystem b).relations.mkQ from LinearMap.congr_fun H
    ext s
    simp only [Finsupp.lsingle_apply, LinearMap.comp_apply, quotientAction_single,
      LieRing.of_associative_ring_bracket, quotientAction_basis, LinearMap.sub_apply,
      Module.End.mul_apply, prependQuotient_mk, context_single]
    simp only [List.append_nil, List.nil_append, List.cons_append]
    have hz := (Submodule.Quotient.mk_eq_zero (reductionSystem b).relations).mpr
      (commutator_mem_relations b i j s)
    change (reductionSystem b).relations.mkQ _ = 0 at hz
    rw [map_sub, map_sub] at hz
    exact (sub_eq_zero.mp hz).symm
  exact he f


/-- The quotient action respects brackets on all elements, by bilinearity and
its checked values on pairs of basis vectors. No PBW hypothesis is used. -/
noncomputable def quotientLieAction (b : Module.Basis ι k g) :
    g →ₗ⁅k⁆ Module.End k (WordQuotient b) :=
  { quotientAction b with
    map_lie' := by
      intro x y
      let A := quotientAction b
      let E := Module.End k (WordQuotient b)
      have he : ((LieModule.toEnd k g g).toLinearMap).compr₂ₛₗ A =
          (((LieModule.toEnd k E E).toLinearMap).compl₂ A).comp A := by
        apply b.ext
        intro i
        apply b.ext
        intro j
        exact quotientAction_lie_basis b i j
      exact LinearMap.congr_fun (LinearMap.congr_fun he x) y }

/-- Recover a word's class by acting on the empty word. The universal property
is used here only to compare presentations, not to infer independence. -/
noncomputable def recoverWords (b : Module.Basis ι k g) :
    U k g →ₗ[k] WordQuotient b :=
  (LinearMap.applyₗ (R := k) (M₂ := WordQuotient b)
    ((reductionSystem b).relations.mkQ (Finsupp.single [] 1))).comp
      (UniversalEnvelopingAlgebra.lift k (quotientLieAction b)).toLinearMap

@[simp] theorem recoverWords_monomial (b : Module.Basis ι k g) (l : List ι) :
    recoverWords b (monomial b l) =
      (reductionSystem b).relations.mkQ (Finsupp.single l 1) := by
  change UniversalEnvelopingAlgebra.lift k (quotientLieAction b) (monomial b l)
      ((reductionSystem b).relations.mkQ (Finsupp.single [] 1)) = _
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [monomial_cons, map_mul, Module.End.mul_apply, ih]
    change UniversalEnvelopingAlgebra.lift k (quotientLieAction b)
      (UniversalEnvelopingAlgebra.ι k (b i)) _ = _
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    change quotientAction b (b i) ((reductionSystem b).relations.mkQ (Finsupp.single l 1)) = _
    rw [quotientAction_basis]
    simp [prependQuotient]

/-- Exact comparison with the original quotient: all relations, and only
those relations, are killed by evaluation in U(g). This is independent of
confluence and hence independent of the eventual PBW conclusion. -/
theorem evaluateWords_ker (b : Module.Basis ι k g) :
    LinearMap.ker (evaluateWords b) = (reductionSystem b).relations := by
  apply le_antisymm _ (relations_le_evaluateWords_ker b)
  have he : (recoverWords b).comp (evaluateWords b) = (reductionSystem b).relations.mkQ := by
    ext l
    simp
  intro f hf
  apply (Submodule.Quotient.mk_eq_zero (reductionSystem b).relations).mp
  change (reductionSystem b).relations.mkQ f = 0
  rw [← he, LinearMap.comp_apply, hf, map_zero]

/-- Once the concrete ambiguity check holds, the abstract Diamond Lemma and
the actual quotient comparison prove independence of the specified products. -/
theorem orderedMonomial_independent_of_diamond (b : Module.Basis ι k g)
    (hd : (reductionSystem b).Diamond) : LinearIndependent k (orderedMonomial b) := by
  let e : OrderedWord ι → {l : List ι // ¬ (reductionSystem b).Reducible l} :=
    fun l => ⟨l.val, (irreducible_iff_ordered b l.val).mpr l.property⟩
  have hi : Function.Injective e := by
    intro l r h
    apply Subtype.ext
    exact congrArg (fun z : {l : List ι // ¬ (reductionSystem b).Reducible l} => z.val) h
  have h := ((reductionSystem b).irreducibles_independent hd).comp e hi
  apply LinearIndependent.of_comp (recoverWords b)
  simpa only [Function.comp_def, orderedMonomial, recoverWords_monomial, e] using h



/-- Two adjacent occurrences in one word are equal, overlap in one letter,
or are disjoint, in either order. -/
theorem adjacent_occurrence_cases {α : Type*} (p s q t : List α) (i j a c : α)
    (h : p ++ i :: j :: s = q ++ a :: c :: t) :
    (p = q ∧ i = a ∧ j = c ∧ s = t) ∨
    (q = p ++ [i] ∧ a = j ∧ s = c :: t) ∨
    (p = q ++ [a] ∧ i = c ∧ t = j :: s) ∨
    (∃ m, q = p ++ i :: j :: m ∧ s = m ++ a :: c :: t) ∨
    (∃ m, p = q ++ a :: c :: m ∧ t = m ++ i :: j :: s) := by
  rcases List.append_eq_append_iff.mp h with ⟨r, hq, he⟩ | ⟨r, hp, he⟩
  · cases r with
    | nil =>
      simp only [List.append_nil] at hq
      simp only [List.nil_append, List.cons.injEq] at he
      exact Or.inl ⟨hq.symm, he.1, he.2.1, he.2.2⟩
    | cons x r =>
      cases r with
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact Or.inr (Or.inl ⟨hq, rfl, rfl⟩)
      | cons y m =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl, he⟩ := he
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hq, he⟩)))
  · cases r with
    | nil =>
      simp only [List.append_nil] at hp
      simp only [List.nil_append, List.cons.injEq] at he
      exact Or.inl ⟨hp, he.1.symm, he.2.1.symm, he.2.2.symm⟩
    | cons x r =>
      cases r with
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact Or.inr (Or.inr (Or.inl ⟨hp, rfl, rfl⟩))
      | cons y m =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl, he⟩ := he
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hp, he⟩)))


theorem WordBelow.trans {a b c : List ι} (hab : WordBelow a b) (hbc : WordBelow b c) :
    WordBelow a c := by
  exact Prod.Lex.trans hab hbc

theorem ruleDifference_lower (b : Module.Basis ι k g) (w p s : List ι) (i j : ι)
    (hji : j < i) (hlt : WordBelow (p ++ i :: j :: s) w) :
    Finsupp.single (p ++ i :: j :: s) 1 - ruleRhs b p s i j ∈
      (reductionSystem b).lowerRelations w :=
  Submodule.subset_span ⟨_, _, hlt, ⟨p, s, i, j, hji, rfl, rfl⟩, rfl⟩

theorem commutator_mem_lower (b : Module.Basis ι k g) (w p s : List ι) (i j : ι)
    (hlen : p.length + 2 + s.length < w.length) :
    Finsupp.single (p ++ i :: j :: s) 1 - Finsupp.single (p ++ j :: i :: s) 1 -
      context p s (letter b ⁅b i, b j⁆) ∈ (reductionSystem b).lowerRelations w := by
  have hdesc : ∀ a c : ι, c < a →
      Finsupp.single (p ++ a :: c :: s) 1 - Finsupp.single (p ++ c :: a :: s) 1 -
        context p s (letter b ⁅b a, b c⁆) ∈ (reductionSystem b).lowerRelations w := by
    intro a c hca
    have hr := ruleDifference_lower b w p s a c hca (Prod.Lex.left _ _ (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen))
    simpa [ruleRhs, sub_add_eq_sub_sub, List.append_assoc] using hr
  rcases lt_trichotomy j i with hji | he | hij
  · exact hdesc i j hji
  · subst j
    simp
  · have hn := (reductionSystem b).lowerRelations w |>.neg_mem (hdesc j i hij)
    rw [← lie_skew (b j) (b i), map_neg, map_neg] at hn
    convert hn using 1 <;> abel

theorem short_letter_commutator_lower (b : Module.Basis ι k g) (p s : List ι)
    (a : ι) (x : g) (w : List ι) (hlen : p.length + 2 + s.length < w.length) :
    context (p ++ [a]) s (letter b x) - context p (a :: s) (letter b x) -
      context p s (letter b ⁅b a, x⁆) ∈ (reductionSystem b).lowerRelations w := by
  let f : g →ₗ[k] WordModule k ι :=
    ((context (p ++ [a]) s).comp (letter b) - (context p (a :: s)).comp (letter b)) -
      (context p s).comp ((letter b).comp ((LieModule.toEnd k g g) (b a)))
  change f x ∈ _
  apply map_mem_of_basis b f ((reductionSystem b).lowerRelations w) _ x
  intro i
  simpa [f, List.append_assoc] using commutator_mem_lower b w p s a i hlen

/-- Concatenate two word expressions around three fixed contexts. -/
noncomputable def wordPair (p m s : List ι) :
    WordModule k ι →ₗ[k] (WordModule k ι →ₗ[k] WordModule k ι) :=
  Finsupp.linearCombination k (fun l => context (p ++ l ++ m) s)

@[simp] theorem wordPair_single_left (p m s l : List ι) (c : k)
    (f : WordModule k ι) :
    wordPair p m s (Finsupp.single l c) f = c • context (p ++ l ++ m) s f := by
  simp [wordPair]

@[simp] theorem wordPair_single_right (p m s l : List ι) (c : k)
    (f : WordModule k ι) :
    wordPair p m s f (Finsupp.single l c) = c • context p (m ++ l ++ s) f := by
  have he : (LinearMap.applyₗ (R := k) (M₂ := WordModule k ι)
      (Finsupp.single l c)).comp (wordPair p m s) =
      c • context p (m ++ l ++ s) := by
    ext a
    simp [List.append_assoc]
  exact LinearMap.congr_fun he f

/-- The two reductions on disjoint descents commute modulo lower relations. -/
theorem disjoint_diamond (b : Module.Basis ι k g) (p m s : List ι)
    (i j a c : ι) (hji : j < i) (hca : c < a) :
    ruleRhs b p (m ++ a :: c :: s) i j -
      ruleRhs b (p ++ i :: j :: m) s a c ∈
      (reductionSystem b).lowerRelations (p ++ i :: j :: (m ++ a :: c :: s)) := by
  classical
  let W := p ++ i :: j :: (m ++ a :: c :: s)
  let R := (reductionSystem b).lowerRelations W
  let F := wordPair (k := k) p m s
  let rij : WordModule k ι := Finsupp.single [j, i] 1 + letter b ⁅b i, b j⁆
  let rac : WordModule k ι := Finsupp.single [c, a] 1 + letter b ⁅b a, b c⁆
  have hleft : F rij (Finsupp.single [a, c] 1 - rac) ∈ R := by
    dsimp [rij]
    rw [map_add, LinearMap.add_apply]
    apply R.add_mem
    · simpa [F, rac, ruleRhs, List.append_assoc] using
        ruleDifference_lower b W (p ++ j :: i :: m) s a c hca
          (by simpa [W, List.append_assoc] using swapped_word_below p (m ++ a :: c :: s) i j hji)
    · let L : g →ₗ[k] WordModule k ι :=
        (LinearMap.applyₗ (R := k) (M₂ := WordModule k ι)
          (Finsupp.single [a, c] 1 - rac)).comp (F.comp (letter b))
      change L ⁅b i, b j⁆ ∈ R
      apply map_mem_of_basis b L R _ ⁅b i, b j⁆
      intro d
      simpa [L, F, rac, ruleRhs, List.append_assoc] using
        ruleDifference_lower b W (p ++ d :: m) s a c hca
          (by simpa [W, List.append_assoc] using bracket_word_below p (m ++ a :: c :: s) i j d)
  have hright : F (Finsupp.single [i, j] 1 - rij) rac ∈ R := by
    dsimp [rac]
    rw [map_add]
    apply R.add_mem
    · simpa [F, rij, ruleRhs, List.append_assoc] using
        ruleDifference_lower b W p (m ++ c :: a :: s) i j hji
          (by simpa [W, List.append_assoc] using swapped_word_below (p ++ i :: j :: m) s a c hca)
    · let L : g →ₗ[k] WordModule k ι := (F (Finsupp.single [i, j] 1 - rij)).comp (letter b)
      change L ⁅b a, b c⁆ ∈ R
      apply map_mem_of_basis b L R _ ⁅b a, b c⁆
      intro d
      simpa [L, F, rij, ruleRhs, List.append_assoc] using
        ruleDifference_lower b W p (m ++ d :: s) i j hji
          (by simpa [W, List.append_assoc] using bracket_word_below (p ++ i :: j :: m) s a c d)
  have h := R.sub_mem hleft hright
  convert h using 1 <;> simp [F, rij, rac, ruleRhs, map_sub, List.append_assoc]


private theorem wb_trans {a b c : List ι} (hab : WordBelow a b) (hbc : WordBelow b c) :
    WordBelow a c := Prod.Lex.trans hab hbc

private theorem rule_lower_overlap (b : Module.Basis ι k g) (p s : List ι) (i j : ι)
    (hji : j < i) (z : List ι) (hz : WordBelow (p ++ i :: j :: s) z) :
    Finsupp.single (p ++ i :: j :: s) 1 - ruleRhs b p s i j ∈
      (reductionSystem b).lowerRelations z :=
  Submodule.subset_span ⟨_, _, hz, ⟨p, s, i, j, hji, rfl, rfl⟩, rfl⟩

/-- The only overlapping ambiguity. The hypothesis is the short commutator
lemma, proved separately by expanding an arbitrary Lie vector in the basis. -/
theorem overlap_mem_lower_from_short (b : Module.Basis ι k g)
    (short : ∀ (p s : List ι) (a : ι) (x : g) (z : List ι),
      p.length + 2 + s.length < z.length →
      context (p ++ [a]) s (letter b x) - context p (a :: s) (letter b x) -
        context p s (letter b ⁅b a, x⁆) ∈ (reductionSystem b).lowerRelations z)
    (p s : List ι) (i j l : ι) (hji : j < i) (hlj : l < j) :
    ruleRhs b p (l :: s) i j - ruleRhs b (p ++ [i]) s j l ∈
      (reductionSystem b).lowerRelations (p ++ i :: j :: l :: s) := by
  let z := p ++ i :: j :: l :: s
  let R := (reductionSystem b).lowerRelations z
  have hli : l < i := hlj.trans hji
  have hA : WordBelow (p ++ j :: i :: l :: s) z := swapped_word_below p (l :: s) i j hji
  have hB : WordBelow (p ++ i :: l :: j :: s) z := by
    simpa [z, List.append_assoc] using swapped_word_below (p ++ [i]) s j l hlj
  have hA' : WordBelow (p ++ j :: l :: i :: s) z := by
    apply wb_trans _ hA
    simpa [List.append_assoc] using swapped_word_below (p ++ [j]) s i l hli
  have hB' : WordBelow (p ++ l :: i :: j :: s) z := by
    exact wb_trans (swapped_word_below p (j :: s) i l hli) hB
  have rA : Finsupp.single (p ++ j :: i :: l :: s) 1 -
      ruleRhs b (p ++ [j]) s i l ∈ R := by
    simpa [R, List.append_assoc] using rule_lower_overlap b (p ++ [j]) s i l hli z
      (by simpa [List.append_assoc] using hA)
  have rA' : Finsupp.single (p ++ j :: l :: i :: s) 1 -
      ruleRhs b p (i :: s) j l ∈ R :=
    rule_lower_overlap b p (i :: s) j l hlj z hA'
  have rB : Finsupp.single (p ++ i :: l :: j :: s) 1 -
      ruleRhs b p (j :: s) i l ∈ R :=
    rule_lower_overlap b p (j :: s) i l hli z hB
  have rB' : Finsupp.single (p ++ l :: i :: j :: s) 1 -
      ruleRhs b (p ++ [l]) s i j ∈ R := by
    simpa [R, List.append_assoc] using rule_lower_overlap b (p ++ [l]) s i j hji z
      (by simpa [List.append_assoc] using hB')
  have c₁ := short p s j ⁅b i, b l⁆ z (by simp only [z, List.length_append, List.length_cons]; omega)
  have c₂ := short p s l ⁅b i, b j⁆ z (by simp only [z, List.length_append, List.length_cons]; omega)
  have c₃ := short p s i ⁅b j, b l⁆ z (by simp only [z, List.length_append, List.length_cons]; omega)
  have hJacobi : ⁅b j, ⁅b i, b l⁆⁆ - ⁅b l, ⁅b i, b j⁆⁆ - ⁅b i, ⁅b j, b l⁆⁆ = 0 := by
    rw [leibniz_lie (b i) (b j) (b l), ← lie_skew (b l) ⁅b i, b j⁆]
    abel
  have hZero : context p s (letter b ⁅b j, ⁅b i, b l⁆⁆) -
      context p s (letter b ⁅b l, ⁅b i, b j⁆⁆) -
      context p s (letter b ⁅b i, ⁅b j, b l⁆⁆) = 0 := by
    rw [← map_sub, ← map_sub, ← map_sub, ← map_sub, hJacobi, map_zero, map_zero]
  have hsum := R.add_mem (R.sub_mem (R.add_mem rA rA') (R.add_mem rB rB'))
    (R.sub_mem (R.sub_mem c₁ c₂) c₃)
  change _ ∈ R
  convert hsum using 1
  simp only [ruleRhs, map_add, context_single] at *
  simp only [List.append_assoc, List.cons_append, List.nil_append] at *
  apply sub_eq_zero.mp
  calc
    _ = context p s (letter b ⁅b j, ⁅b i, b l⁆⁆) -
        context p s (letter b ⁅b l, ⁅b i, b j⁆⁆) -
        context p s (letter b ⁅b i, ⁅b j, b l⁆⁆) := by abel
    _ = 0 := hZero

theorem overlap_mem_lower (b : Module.Basis ι k g) (p s : List ι) (i j l : ι)
    (hji : j < i) (hlj : l < j) :
    ruleRhs b p (l :: s) i j - ruleRhs b (p ++ [i]) s j l ∈
      (reductionSystem b).lowerRelations (p ++ i :: j :: l :: s) :=
  overlap_mem_lower_from_short b (short_letter_commutator_lower b) p s i j l hji hlj


/-- All choices of a first reduction differ by lower-head relations. -/
theorem reductionSystem_diamond (b : Module.Basis ι k g) : (reductionSystem b).Diamond := by
  intro w f₁ f₂ h₁ h₂
  rcases h₁ with ⟨p, s, i, j, hji, rfl, rfl⟩
  rcases h₂ with ⟨q, t, a, c, hca, he, rfl⟩
  rcases adjacent_occurrence_cases p s q t i j a c he with
    h | h | h | h | h
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    simp
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact overlap_mem_lower b p t i a c hji hca
  · rcases h with ⟨rfl, rfl, rfl⟩
    have h := ((reductionSystem b).lowerRelations (q ++ a :: i :: j :: s)).neg_mem
      (overlap_mem_lower b q s a i j hca hji)
    simpa [List.append_assoc] using h
  · rcases h with ⟨m, rfl, rfl⟩
    exact disjoint_diamond b p m t i j a c hji hca
  · rcases h with ⟨m, rfl, rfl⟩
    have h := ((reductionSystem b).lowerRelations (q ++ a :: c :: (m ++ i :: j :: s))).neg_mem
      (disjoint_diamond b q m s a c i j hca hji)
    simpa [List.append_assoc] using h

/-- The terminating contextual reduction system is confluent, so the ordered
products are linearly independent in the actual enveloping quotient. -/
theorem orderedMonomial_independent (b : Module.Basis ι k g) :
    LinearIndependent k (orderedMonomial b) :=
  orderedMonomial_independent_of_diamond b (reductionSystem_diamond b)

/-- The ordered products are the values of a basis, including the empty word. -/
noncomputable def orderedBasis (b : Module.Basis ι k g) :
    Module.Basis (OrderedWord ι) k (U k g) :=
  Module.Basis.mk (orderedMonomial_independent b) (by rw [ordered_span b])

@[simp] theorem orderedBasis_apply (b : Module.Basis ι k g) (l : OrderedWord ι) :
    orderedBasis b l = orderedMonomial b l := Module.Basis.mk_apply _ _ _

end Shared.Lie.PBW

namespace Shared.Lie.PBW
universe u v w

theorem spanning_spec : Specs.Shared.Lie.PBW.spanningExpected.{u,v,w} :=
  fun _ _ _ _ _ _ _ b => ordered_span b

theorem orderedBasis_spec : Specs.Shared.Lie.PBW.orderedBasisExpected.{u,v,w} := by
  intro k g ι _ _ _ _ b
  exact ⟨orderedBasis b, orderedBasis_apply b⟩

theorem inclusionInjective_spec : Specs.Shared.Lie.PBW.injectiveExpected.{u,v,w} := by
  intro k g ι _ _ _ _ b
  exact inclusion_injective_of_independent b (orderedMonomial_independent b)
end Shared.Lie.PBW
