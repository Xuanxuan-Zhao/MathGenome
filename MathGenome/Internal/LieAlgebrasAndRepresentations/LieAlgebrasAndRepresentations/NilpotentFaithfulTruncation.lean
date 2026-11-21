import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DerivedLowerSeries
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered
import Mathlib.Tactic.Abel
import Mathlib.Data.Set.Finite.List
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! LA-I08: derivation-stable weighted PBW truncations over arbitrary fields.
The adapted lower-central basis, weighted multiplication and derivation
stability, finite quotient, induced actions, faithfulness, and exact nilpotence
bound are proved for the actual enveloping algebra, including the zero algebra.
-/
namespace LieAlgebrasAndRepresentations.NilpotentTruncation
open _root_.Shared.Lie _root_.Shared.Lie.PBW
universe u v
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]

/-- Every lower-central term is invariant under all Lie derivations. -/
theorem derivation_mem_lowerCentral (δ : LieDerivation k L L) (m : ℕ) (x : L)
    (hx : x ∈ LieModule.lowerCentralSeries k L L m) :
    δ x ∈ LieModule.lowerCentralSeries k L L m := by
  induction m generalizing x with
  | zero => trivial
  | succ m ih =>
    rw [LieModule.lowerCentralSeries_succ] at hx ⊢
    change x ∈ (⁅(⊤ : LieIdeal k L), LieModule.lowerCentralSeries k L L m⁆).toSubmodule at hx
    rw [bracket_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, _, b, hb, rfl⟩ := hx
      rw [δ.apply_lie_eq_add]
      exact add_mem (LieSubmodule.lie_mem_lie (by trivial) (ih b hb))
        (LieSubmodule.lie_mem_lie (by trivial) hb)
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
    | smul r x _ hx =>
      change δ (r • x) ∈ (⁅(⊤ : LieIdeal k L),
        LieModule.lowerCentralSeries k L L m⁆ : LieIdeal k L).toSubmodule
      rw [map_smul]
      exact (⁅(⊤ : LieIdeal k L), LieModule.lowerCentralSeries k L L m⁆ : LieIdeal k L).toSubmodule.smul_mem r hx

theorem lowerCentralStable_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.lowerCentralStableExpected.{u,v} := by
  intro k L _ _ _ δ j x hx
  exact derivation_mem_lowerCentral δ (j - 1) x hx

/-- The infinitesimal algebra map x ↦ (ι(x), ι(δx)). -/
def infinitesimalLieMap (δ : LieDerivation k L L) :
    L →ₗ⁅k⁆ TrivSqZeroExt (U k L) (U k L) where
  toLinearMap :=
    { toFun := fun x => (inclusion k L x, inclusion k L (δ x))
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext
        · change inclusion k L (x + y) = inclusion k L x + inclusion k L y
          simp only [map_add]
        · change inclusion k L (δ (x + y)) = inclusion k L (δ x) + inclusion k L (δ y)
          simp only [map_add]
      map_smul' := by
        intro r x
        apply TrivSqZeroExt.ext
        · change inclusion k L (r • x) = r • inclusion k L x
          simp only [map_smul]
        · change inclusion k L (δ (r • x)) = r • inclusion k L (δ x)
          simp only [map_smul] }
  map_lie' := by
    intro x y
    apply TrivSqZeroExt.ext
    · exact (inclusion k L).map_lie x y
    · change inclusion k L (δ ⁅x, y⁆) =
        (inclusion k L x * inclusion k L (δ y) +
          inclusion k L (δ x) * inclusion k L y) -
        (inclusion k L y * inclusion k L (δ x) +
          inclusion k L (δ y) * inclusion k L x)
      rw [δ.apply_lie_eq_add, map_add, (inclusion k L).map_lie,
        (inclusion k L).map_lie]
      change (_ * _ - _ * _) + (_ * _ - _ * _) = _
      abel

def infinitesimalLift (δ : LieDerivation k L L) :
    U k L →ₐ[k] TrivSqZeroExt (U k L) (U k L) :=
  UniversalEnvelopingAlgebra.lift k (infinitesimalLieMap δ)

@[simp] theorem infinitesimalLift_fst (δ : LieDerivation k L L) (a : U k L) :
    (infinitesimalLift δ a).fst = a := by
  have h : (TrivSqZeroExt.fstHom k (U k L) (U k L)).comp (infinitesimalLift δ) =
      AlgHom.id k (U k L) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    exact congrArg TrivSqZeroExt.fst
      (UniversalEnvelopingAlgebra.lift_ι_apply k (infinitesimalLieMap δ) x)
  exact DFunLike.congr_fun h a

/-- Extension to U as a noncommutative associative derivation. -/
def extendDerivation (δ : LieDerivation k L L) : Module.End k (U k L) :=
  ({ toFun := TrivSqZeroExt.snd
     map_add' := TrivSqZeroExt.snd_add
     map_smul' := TrivSqZeroExt.snd_smul } :
      TrivSqZeroExt (U k L) (U k L) →ₗ[k] U k L).comp (infinitesimalLift δ).toLinearMap

@[simp] theorem extendDerivation_one (δ : LieDerivation k L L) :
    extendDerivation δ 1 = 0 := by
  change (infinitesimalLift δ 1).snd = 0
  simp

@[simp] theorem extendDerivation_generator (δ : LieDerivation k L L) (x : L) :
    extendDerivation δ (inclusion k L x) = inclusion k L (δ x) :=
  congrArg TrivSqZeroExt.snd
    (UniversalEnvelopingAlgebra.lift_ι_apply k (infinitesimalLieMap δ) x)

theorem extendDerivation_mul (δ : LieDerivation k L L) (a b : U k L) :
    extendDerivation δ (a * b) = a * extendDerivation δ b + extendDerivation δ a * b := by
  change (infinitesimalLift δ (a * b)).snd = _
  rw [map_mul, TrivSqZeroExt.snd_mul, infinitesimalLift_fst, infinitesimalLift_fst]
  rfl

theorem extendDerivation_extends (δ : LieDerivation k L L) : Extends (extendDerivation δ) δ :=
  ⟨⟨extendDerivation_one δ, extendDerivation_mul δ⟩, extendDerivation_generator δ⟩

/-- Equality of associative derivations can be tested on the Lie generators. -/
theorem envelopingDerivation_ext {D E : Module.End k (U k L)}
    (hD : IsEnvelopingDerivation D) (hE : IsEnvelopingDerivation E)
    (h : ∀ x, D (inclusion k L x) = E (inclusion k L x)) : D = E := by
  ext a
  induction a using enveloping_induction k L with
  | scalar r => simp only [Algebra.algebraMap_eq_smul_one, map_smul, hD.1, hE.1]
  | generator x => exact h x
  | mul a b ha hb => rw [hD.2, hE.2, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The associative derivations form a Lie subalgebra of the endomorphisms.
This uses the actual noncommutative Leibniz rule, not the commutative-algebra
`Derivation` structure. -/
def envelopingDerivations : LieSubalgebra k (Module.End k (U k L)) where
  carrier := {D | IsEnvelopingDerivation D}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro D E hD hE
    constructor
    · simp [hD.1, hE.1]
    · intro a b
      change D (a * b) + E (a * b) = a * (D b + E b) + (D a + E a) * b
      rw [hD.2, hE.2, mul_add, add_mul]
      abel
  smul_mem' := by
    intro r D hD
    constructor
    · simp [hD.1]
    · intro a b
      change r • D (a * b) = a * (r • D b) + (r • D a) * b
      rw [hD.2, smul_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  lie_mem' := by
    intro D E hD hE
    constructor
    · change D (E 1) - E (D 1) = 0
      simp [hD.1, hE.1]
    · intro a b
      change D (E (a * b)) - E (D (a * b)) =
        a * (D (E b) - E (D b)) + (D (E a) - E (D a)) * b
      simp only [hD.2, hE.2, map_add, mul_sub, sub_mul]
      abel

/-- Extension of derivations is linear and preserves Lie brackets. -/
def extendDerivationLieHom : LieDerivation k L L →ₗ⁅k⁆ Module.End k (U k L) where
  toLinearMap :=
    { toFun := extendDerivation
      map_add' := by
        intro δ ε
        apply envelopingDerivation_ext (extendDerivation_extends (δ + ε)).1
          ((envelopingDerivations (k := k) (L := L)).add_mem
            (extendDerivation_extends δ).1 (extendDerivation_extends ε).1)
        intro x
        simp only [LinearMap.add_apply, extendDerivation_generator,
          LieDerivation.add_apply, map_add]
      map_smul' := by
        intro r δ
        apply envelopingDerivation_ext (extendDerivation_extends (r • δ)).1
          ((envelopingDerivations (k := k) (L := L)).smul_mem r
            (extendDerivation_extends δ).1)
        intro x
        simp only [LinearMap.smul_apply, extendDerivation_generator,
          LieDerivation.smul_apply, map_smul] }
  map_lie' := by
    intro δ ε
    apply envelopingDerivation_ext (extendDerivation_extends ⁅δ, ε⁆).1
      ((envelopingDerivations (k := k) (L := L)).lie_mem
        (extendDerivation_extends δ).1 (extendDerivation_extends ε).1)
    intro x
    change extendDerivation ⁅δ, ε⁆ (inclusion k L x) =
      extendDerivation δ (extendDerivation ε (inclusion k L x)) -
        extendDerivation ε (extendDerivation δ (inclusion k L x))
    simp only [extendDerivation_generator, LieDerivation.commutator_apply, map_sub]

theorem derivationExtension_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.derivationExtensionExpected.{u,v} := by
  intro k L _ _ _
  refine ⟨extendDerivationLieHom, fun δ => ⟨extendDerivation_extends δ, ?_⟩⟩
  intro D hD
  exact envelopingDerivation_ext hD.1 (extendDerivation_extends δ).1
    (fun x => (hD.2 x).trans (extendDerivation_generator δ x).symm)

section Descent
variable {G M : Type*} [LieRing G] [LieAlgebra k G] [AddCommGroup M] [Module k M]

/-- Descent of a representation through an invariant linear subspace. -/
def quotientRepresentation (S : Submodule k M) (ρ : G →ₗ⁅k⁆ Module.End k M)
    (hρ : ∀ x a, a ∈ S → ρ x a ∈ S) : G →ₗ⁅k⁆ Module.End k (M ⧸ S) where
  toLinearMap :=
    { toFun := fun x => S.mapQ S (ρ x) (fun a ha => hρ x a ha)
      map_add' := by
        intro x y
        ext a
        change S.mkQ (ρ (x + y) a) = S.mkQ (ρ x a) + S.mkQ (ρ y a)
        rw [map_add, LinearMap.add_apply, map_add]
      map_smul' := by
        intro r x
        ext a
        change S.mkQ (ρ (r • x) a) = r • S.mkQ (ρ x a)
        rw [map_smul, LinearMap.smul_apply, map_smul] }
  map_lie' := by
    intro x y
    ext a
    change S.mkQ (ρ ⁅x, y⁆ a) = S.mkQ (ρ x (ρ y a)) - S.mkQ (ρ y (ρ x a))
    rw [ρ.map_lie]
    change S.mkQ (ρ x (ρ y a) - ρ y (ρ x a)) = _
    exact map_sub S.mkQ _ _

@[simp] theorem quotientRepresentation_mkQ (S : Submodule k M)
    (ρ : G →ₗ⁅k⁆ Module.End k M) (hρ) (x : G) (a : M) :
    quotientRepresentation S ρ hρ x (S.mkQ a) = S.mkQ (ρ x a) := rfl
end Descent

/-- Left multiplication by the canonical Lie generators on U. -/
def leftRegularRepresentation : L →ₗ⁅k⁆ Module.End k (U k L) :=
  ((Algebra.lsmul k k (U k L) : U k L →ₐ[k] Module.End k (U k L)) :
    U k L →ₗ⁅k⁆ Module.End k (U k L)).comp (inclusion k L)

@[simp] theorem leftRegularRepresentation_apply (x : L) (a : U k L) :
    leftRegularRepresentation x a = inclusion k L x * a := rfl

/-- The commutator identity already holds before taking the quotient. -/
theorem extendDerivation_left_commutator (δ : LieDerivation k L L) (x : L) :
    ⁅extendDerivation δ, leftRegularRepresentation (k := k) x⁆ =
      leftRegularRepresentation (k := k) (δ x) := by
  ext a
  change extendDerivation δ (inclusion k L x * a) -
    inclusion k L x * extendDerivation δ a = inclusion k L (δ x) * a
  rw [extendDerivation_mul, extendDerivation_generator]
  abel

/-- Once the weighted invariance lemmas are supplied, both quotient actions
and their commutator formula follow without further PBW arguments. -/
theorem quotient_actions (S : Submodule k (U k L))
    (hleft : ∀ a z, z ∈ S → a * z ∈ S)
    (hstable : ∀ (δ : LieDerivation k L L) z, z ∈ S → extendDerivation δ z ∈ S) :
    ∃ (ρ : L →ₗ⁅k⁆ Module.End k (U k L ⧸ S))
      (D : LieDerivation k L L →ₗ⁅k⁆ Module.End k (U k L ⧸ S)),
      (∀ x a, ρ x (S.mkQ a) = S.mkQ (inclusion k L x * a)) ∧
      (∀ δ a, D δ (S.mkQ a) = S.mkQ (extendDerivation δ a)) ∧
      (∀ δ, D δ (S.mkQ 1) = 0) ∧
      (∀ δ x, ⁅D δ, ρ x⁆ = ρ (δ x)) := by
  let ρ := quotientRepresentation S (leftRegularRepresentation (k := k) (L := L))
    (fun x a ha => hleft (inclusion k L x) a ha)
  let D := quotientRepresentation S (extendDerivationLieHom (k := k) (L := L)) hstable
  refine ⟨ρ, D, (fun _ _ => rfl), (fun _ _ => rfl), ?_, ?_⟩
  · intro δ
    change S.mkQ (extendDerivation δ 1) = 0
    rw [extendDerivation_one, map_zero]
  · intro δ x
    ext a
    change S.mkQ (extendDerivation δ (inclusion k L x * a)) -
      S.mkQ (inclusion k L x * extendDerivation δ a) = S.mkQ (inclusion k L (δ x) * a)
    rw [← map_sub]
    apply congrArg S.mkQ
    rw [extendDerivation_mul, extendDerivation_generator]
    abel

/-- Faithfulness is detected by the class of 1. -/
theorem quotient_action_injective (S : Submodule k (U k L))
    (ρ : L →ₗ⁅k⁆ Module.End k (U k L ⧸ S))
    (hρ : ∀ x a, ρ x (S.mkQ a) = S.mkQ (inclusion k L x * a))
    (hinj : Function.Injective (S.mkQ.comp (inclusion k L).toLinearMap)) :
    Function.Injective ρ := by
  intro x y h
  apply hinj
  change S.mkQ (inclusion k L x) = S.mkQ (inclusion k L y)
  have hh := DFunLike.congr_fun h (S.mkQ 1)
  simpa only [hρ, mul_one] using hh

theorem quotient_action_pow (S : Submodule k (U k L))
    (ρ : L →ₗ⁅k⁆ Module.End k (U k L ⧸ S))
    (hρ : ∀ x a, ρ x (S.mkQ a) = S.mkQ (inclusion k L x * a))
    (x : L) (n : ℕ) (a : U k L) :
    ((ρ x) ^ n) (S.mkQ a) = S.mkQ ((inclusion k L x) ^ n * a) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, hρ, ih, pow_succ, mul_assoc]

section Weighted
variable {d : ℕ} (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ)

@[simp] theorem wordWeight_nil : wordWeight w [] = 0 := rfl
@[simp] theorem wordWeight_cons (i : Fin d) (l : List (Fin d)) :
    wordWeight w (i :: l) = w i + wordWeight w l := rfl

theorem wordWeight_append (l r : List (Fin d)) :
    wordWeight w (l ++ r) = wordWeight w l + wordWeight w r := by
  simp [wordWeight, List.map_append, List.sum_append]

/-- A linear map can be checked on the nonzero coordinates of one vector. -/
theorem map_mem_of_support {M : Type*} [AddCommGroup M] [Module k M]
    (f : L →ₗ[k] M) (S : Submodule k M) (x : L)
    (h : ∀ i, b.repr x i ≠ 0 → f (b i) ∈ S) : f x ∈ S := by
  classical
  rw [← b.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  by_cases hi : b.repr x i = 0
  · simp [hi]
  · exact S.smul_mem _ (h i hi)

theorem length_le_wordWeight (hw : ∀ i, 0 < w i) (l : List (Fin d)) :
    l.length ≤ wordWeight w l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_cons, wordWeight_cons]
    exact (Nat.succ_le_succ ih).trans (by
      simpa only [Nat.one_add] using Nat.add_le_add_right (hw i) (wordWeight w l))

theorem orderedMonomial_mem_weightedSpan (N : ℕ) (l : OrderedWord (Fin d))
    (hl : N ≤ wordWeight w l.val) : orderedMonomial b l ∈ weightedSpan b w N :=
  Submodule.subset_span ⟨l, hl, rfl⟩

/-- This is decreasing in the cutoff, including N = 0. -/
theorem weightedSpan_antitone : Antitone (weightedSpan b w) := by
  intro m n hmn
  apply Submodule.span_le.mpr
  rintro a ⟨l, hl, rfl⟩
  exact orderedMonomial_mem_weightedSpan b w m l (hmn.trans hl)

theorem weightedSpan_zero : weightedSpan b w 0 = ⊤ := by
  apply top_unique
  rw [← ordered_span b]
  apply Submodule.span_le.mpr
  rintro a ⟨l, rfl⟩
  exact orderedMonomial_mem_weightedSpan b w 0 l (Nat.zero_le _)

/-- Normal ordering never decreases weight when brackets satisfy the
lower-central coefficient estimate. -/
theorem monomial_mem_weightedSpan
    (hbr : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → w i + w j ≤ w a)
    (l : List (Fin d)) : monomial b l ∈ weightedSpan b w (wordWeight w l) := by
  classical
  induction l using (wordBelow_wellFounded (ι := Fin d)).induction with
  | h l ih =>
    by_cases hl : l.Pairwise (· ≤ ·)
    · exact orderedMonomial_mem_weightedSpan b w _ ⟨l, hl⟩ le_rfl
    · obtain ⟨p, i, j, s, rfl, hji⟩ := exists_descent l hl
      rw [monomial_swap]
      apply Submodule.add_mem
      · have hh := ih _ (swapped_word_below p s i j hji)
        have hw : wordWeight w (p ++ i :: j :: s) = wordWeight w (p ++ j :: i :: s) := by
          simp only [wordWeight_append, wordWeight_cons]
          omega
        rw [hw]
        exact hh
      · apply map_mem_of_support b (sandwich b p s) _ ⁅b i, b j⁆
        intro a ha
        have hh := ih _ (bracket_word_below p s i j a)
        have hw : wordWeight w (p ++ i :: j :: s) ≤ wordWeight w (p ++ a :: s) := by
          simp only [wordWeight_append, wordWeight_cons]
          have := hbr i j a ha
          omega
        have hh' := weightedSpan_antitone b w hw hh
        simpa only [monomial_append, monomial_cons, sandwich_apply, mul_assoc] using hh'

/-- Products of weighted spans have at least the sum of the weights. -/
theorem weightedSpan_mul
    (hbr : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → w i + w j ≤ w a)
    (i j : ℕ) (a z : U k L) (ha : a ∈ weightedSpan b w i)
    (hz : z ∈ weightedSpan b w j) : a * z ∈ weightedSpan b w (i + j) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨r, hr, rfl⟩ := hz
      have hh := monomial_mem_weightedSpan b w hbr (l.val ++ r.val)
      apply weightedSpan_antitone b w (Nat.add_le_add hl hr)
      simpa only [wordWeight_append, monomial_append, orderedMonomial] using hh
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add] using Submodule.add_mem _ hx hy
    | smul r x _ hx => simpa only [Algebra.mul_smul_comm] using Submodule.smul_mem _ r hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [add_mul] using Submodule.add_mem _ hx hy
  | smul r x _ hx => simpa only [Algebra.smul_mul_assoc] using Submodule.smul_mem _ r hx

/-- A generator with only sufficiently heavy coordinates has that weight. -/
theorem inclusion_mem_weightedSpan_of_support (x : L) (N : ℕ)
    (hx : ∀ a, b.repr x a ≠ 0 → N ≤ w a) : inclusion k L x ∈ weightedSpan b w N := by
  apply map_mem_of_support b (inclusion k L).toLinearMap _ x
  intro a ha
  change inclusion k L (b a) ∈ weightedSpan b w N
  rw [← orderedMonomial_singleton b a]
  apply orderedMonomial_mem_weightedSpan
  simpa [singletonWord, wordWeight] using hx a ha

/-- Leibniz expansion preserves the weight of every word. -/
theorem derivation_monomial_mem_weightedSpan
    (hbr : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → w i + w j ≤ w a)
    (D : Module.End k (U k L)) (hD : IsEnvelopingDerivation D)
    (hgen : ∀ i, D (inclusion k L (b i)) ∈ weightedSpan b w (w i))
    (l : List (Fin d)) : D (monomial b l) ∈ weightedSpan b w (wordWeight w l) := by
  induction l with
  | nil => simp only [monomial_nil, hD.1]; exact Submodule.zero_mem _
  | cons i l ih =>
    rw [monomial_cons, hD.2, wordWeight_cons]
    apply Submodule.add_mem
    · apply weightedSpan_mul b w hbr _ _ _ _ _ ih
      exact inclusion_mem_weightedSpan_of_support b w (b i) (w i) (by
        intro a ha
        have he : i = a := by
          by_contra he
          exact ha (by simp [he])
        subst a
        exact le_rfl)
    · exact weightedSpan_mul b w hbr _ _ _ _ (hgen i)
        (monomial_mem_weightedSpan b w hbr l)

/-- Only finitely many PBW indices have weight below a fixed cutoff. -/
theorem finite_lowWords (hw : ∀ i, 0 < w i) (N : ℕ) :
    {l : OrderedWord (Fin d) | wordWeight w l.val < N}.Finite := by
  apply Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  apply (List.finite_length_lt (Fin d) N).subset
  rintro l ⟨a, ha, rfl⟩
  exact (length_le_wordWeight w hw a.val).trans_lt ha

/-- Finite dimension needs only positivity and PBW, not nilpotence or
multiplicativity of the weighted subspace. -/
theorem quotient_finiteDimensional (hw : ∀ i, 0 < w i) (N : ℕ) :
    FiniteDimensional k (QuotientSpace b w N) := by
  let q := (weightedSpan b w N).mkQ
  let s : Set (QuotientSpace b w N) :=
    (fun l : OrderedWord (Fin d) => q (orderedMonomial b l)) ''
      {l | wordWeight w l.val < N}
  have hs : s.Finite := (finite_lowWords w hw N).image _
  have hspan : Submodule.span k s = ⊤ := by
    apply top_unique
    rw [← (weightedSpan b w N).range_mkQ, ← Submodule.map_top]
    apply (Submodule.map_le_iff_le_comap).mpr
    rw [← ordered_span b]
    apply Submodule.span_le.mpr
    rintro a ⟨l, rfl⟩
    change q (orderedMonomial b l) ∈ Submodule.span k s
    by_cases hl : N ≤ wordWeight w l.val
    · have hz : q (orderedMonomial b l) = 0 :=
        (Submodule.Quotient.mk_eq_zero (weightedSpan b w N)).mpr
          (orderedMonomial_mem_weightedSpan b w N l hl)
      rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨l, Nat.lt_of_not_ge hl, rfl⟩
  exact Module.Finite.of_fg_top (hspan ▸ Submodule.fg_span hs)

/-- Coordinates for the weighted span in the actual PBW basis. -/
theorem weightedSpan_eq_basis_span (N : ℕ) :
    weightedSpan b w N = Submodule.span k
      ((orderedBasis b) '' {l : OrderedWord (Fin d) | N ≤ wordWeight w l.val}) := by
  unfold weightedSpan
  congr 1
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, orderedBasis_apply b l⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, (orderedBasis_apply b l).symm⟩

theorem mem_weightedSpan_iff (N : ℕ) (a : U k L) :
    a ∈ weightedSpan b w N ↔ ∀ l : OrderedWord (Fin d),
      wordWeight w l.val < N → (orderedBasis b).repr a l = 0 := by
  rw [weightedSpan_eq_basis_span, (orderedBasis b).mem_span_image]
  constructor
  · intro h l hl
    by_contra hn
    exact (not_le_of_gt hl) (h (Finsupp.mem_support_iff.mpr hn))
  · intro h l hl
    exact Nat.le_of_not_gt (fun hlt => (Finsupp.mem_support_iff.mp hl) (h l hlt))

/-- A singleton PBW coordinate restricts to the original basis coordinate. -/
theorem singleton_coordinate (i : Fin d) (x : L) :
    (orderedBasis b).repr (inclusion k L x) (singletonWord i) = b.repr x i := by
  let f := ((orderedBasis b).coord (singletonWord i)).comp (inclusion k L).toLinearMap
  have hf : f = b.coord i := by
    apply b.ext
    intro j
    change (orderedBasis b).repr (inclusion k L (b j)) (singletonWord i) = b.repr (b j) i
    rw [← orderedMonomial_singleton b j, ← orderedBasis_apply b (singletonWord j)]
    simp only [Module.Basis.repr_self_apply, singletonWord_injective.eq_iff]
  exact DFunLike.congr_fun hf x

/-- The quotient retains every Lie generator once the cutoff exceeds all
basis weights. This includes the empty basis (the zero Lie algebra). -/
theorem inclusion_quotient_injective (N : ℕ) (hw : ∀ i, w i < N) :
    Function.Injective ((weightedSpan b w N).mkQ.comp (inclusion k L).toLinearMap) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  have hmem : inclusion k L x ∈ weightedSpan b w N :=
    (Submodule.Quotient.mk_eq_zero (weightedSpan b w N)).mp hx
  apply b.repr.injective
  ext i
  have hi := (mem_weightedSpan_iff b w N (inclusion k L x)).mp hmem (singletonWord i)
  rw [singleton_coordinate] at hi
  simpa only [map_zero, Finsupp.zero_apply] using hi (by simpa [singletonWord] using hw i)

/-- Adaptation gives the required cutoff bound directly from γ_(c+1) = 0. -/
theorem adapted_weight_lt {c N : ℕ} (hb : IsAdapted b w)
    (hc : lowerCentralSeries k L (c + 1) = ⊥) (hN : c < N) (i : Fin d) : w i < N := by
  by_contra hi
  have hci : c + 1 ≤ w i := (Nat.succ_le_of_lt hN).trans (Nat.le_of_not_gt hi)
  have hm : b i ∈ (lowerCentralSeries k L (c + 1)).toSubmodule := by
    rw [show (lowerCentralSeries k L (c + 1)).toSubmodule =
      Submodule.span k (b '' {i | c + 1 ≤ w i}) from hb.2 (c + 1) (Nat.succ_pos c)]
    exact Submodule.subset_span ⟨i, hci, rfl⟩
  rw [hc] at hm
  exact b.ne_zero i hm

theorem adapted_basis_mem (hb : IsAdapted b w) (i : Fin d) :
    b i ∈ lowerCentralSeries k L (w i) := by
  change b i ∈ (lowerCentralSeries k L (w i)).toSubmodule
  rw [show (lowerCentralSeries k L (w i)).toSubmodule =
    Submodule.span k (b '' {a | w i ≤ w a}) from hb.2 (w i) (hb.1 i)]
  exact Submodule.subset_span ⟨i, show w i ≤ w i from le_rfl, rfl⟩

theorem adapted_support_weight (hb : IsAdapted b w) {j : ℕ} (hj : 0 < j)
    (x : L) (hx : x ∈ lowerCentralSeries k L j) (i : Fin d)
    (hi : b.repr x i ≠ 0) : j ≤ w i := by
  have hx' : x ∈ Submodule.span k (b '' {a | j ≤ w a}) := by
    rw [← hb.2 j hj]
    exact hx
  exact (b.mem_span_image.mp hx') (Finsupp.mem_support_iff.mpr hi)

/-- This is the precise coefficient estimate needed in weighted PBW reduction. -/
theorem adapted_bracket_weight (hb : IsAdapted b w) (i j a : Fin d)
    (ha : b.repr ⁅b i, b j⁆ a ≠ 0) : w i + w j ≤ w a := by
  apply adapted_support_weight b w hb (Nat.add_pos_left (hb.1 i) _) _ ?_ a ha
  exact lowerCentralSeries_bracket (w i) (w j) (hb.1 i) (hb.1 j)
    (LieSubmodule.lie_mem_lie (adapted_basis_mem b w hb i) (adapted_basis_mem b w hb j))

/-- Derivations cannot lower the lower-central weight of a basis factor. -/
theorem adapted_derivation_weight (hb : IsAdapted b w) (δ : LieDerivation k L L)
    (i a : Fin d) (ha : b.repr (δ (b i)) a ≠ 0) : w i ≤ w a := by
  apply adapted_support_weight b w hb (hb.1 i) _ ?_ a ha
  exact derivation_mem_lowerCentral δ _ _ (adapted_basis_mem b w hb i)

/-- Stability of the exact weighted PBW span under every extended derivation. -/
theorem weightedSpan_derivation (hb : IsAdapted b w)
    (δ : LieDerivation k L L) (D : Module.End k (U k L)) (hD : Extends D δ)
    (N : ℕ) (z : U k L) (hz : z ∈ weightedSpan b w N) :
    D z ∈ weightedSpan b w N := by
  have hgen : ∀ i, D (inclusion k L (b i)) ∈ weightedSpan b w (w i) := by
    intro i
    rw [hD.2]
    exact inclusion_mem_weightedSpan_of_support b w _ _ (adapted_derivation_weight b w hb δ i)
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    exact weightedSpan_antitone b w hl
      (derivation_monomial_mem_weightedSpan b w (adapted_bracket_weight b w hb) D hD.1 hgen l.val)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

theorem inclusion_mem_weightedSpan_one (hw : ∀ i, 0 < w i) (x : L) :
    inclusion k L x ∈ weightedSpan b w 1 := by
  apply map_mem_of_basis b (inclusion k L).toLinearMap (weightedSpan b w 1) ?_ x
  intro i
  change inclusion k L (b i) ∈ weightedSpan b w 1
  rw [← orderedMonomial_singleton b i]
  apply orderedMonomial_mem_weightedSpan
  simpa only [wordWeight, singletonWord, List.map_singleton, List.sum_singleton] using (Nat.succ_le_of_lt (hw i))

/-- Multiplicativity of the decreasing filtration gives the exact exponent N. -/
theorem inclusion_pow_mem (hw : ∀ i, 0 < w i)
    (hmul : ∀ i j (a z : U k L), a ∈ weightedSpan b w i → z ∈ weightedSpan b w j →
      a * z ∈ weightedSpan b w (i + j)) (x : L) (n : ℕ) :
    inclusion k L x ^ n ∈ weightedSpan b w n := by
  induction n with
  | zero => rw [pow_zero, weightedSpan_zero]; trivial
  | succ n ih =>
    rw [pow_succ]
    exact hmul n 1 _ _ ih (inclusion_mem_weightedSpan_one b w hw x)

theorem quotient_action_nilpotent (hw : ∀ i, 0 < w i)
    (hmul : ∀ i j (a z : U k L), a ∈ weightedSpan b w i → z ∈ weightedSpan b w j →
      a * z ∈ weightedSpan b w (i + j)) (N : ℕ)
    (ρ : L →ₗ⁅k⁆ Module.End k (QuotientSpace b w N))
    (hρ : ∀ x a, ρ x ((weightedSpan b w N).mkQ a) =
      (weightedSpan b w N).mkQ (inclusion k L x * a)) (x : L) : (ρ x) ^ N = 0 := by
  ext a
  change ((ρ x) ^ N) ((weightedSpan b w N).mkQ a) = 0
  rw [quotient_action_pow _ ρ hρ]
  apply (Submodule.Quotient.mk_eq_zero (weightedSpan b w N)).mpr
  have ha : a ∈ weightedSpan b w 0 := by rw [weightedSpan_zero]; trivial
  simpa only [Nat.add_zero] using hmul N 0 _ _ (inclusion_pow_mem b w hw hmul x N) ha

end Weighted

theorem quotientFinite_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.quotientFiniteExpected.{u,v} := by
  intro k L _ _ _ d b w hw N
  exact quotient_finiteDimensional b w hw N

theorem pbwSeparation_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.pbwSeparationExpected.{u,v} := by
  intro k L _ _ _ d b w N hw
  exact inclusion_quotient_injective b w N hw

theorem weightedMultiplicative_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.weightedMultiplicativeExpected.{u,v} := by
  intro k L _ _ _ d b w hb
  exact weightedSpan_mul b w (adapted_bracket_weight b w hb)

theorem weightedStable_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.weightedStableExpected.{u,v} := by
  intro k L _ _ _ d b w hb
  exact weightedSpan_derivation b w hb

section AdaptedBasis

/-- A finite decreasing filtration admits a basis whose weights describe all
its steps. Weight zero corresponds to the first quotient. -/
theorem finite_filtration_basis (c : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (F : ℕ → Submodule k V), Antitone F → F 0 = ⊤ → F c = ⊥ →
      ∃ (d : ℕ) (b : Module.Basis (Fin d) k V) (w : Fin d → ℕ),
        ∀ j, F j = Submodule.span k (b '' {i | j ≤ w i}) := by
  classical
  induction c with
  | zero =>
    intro V _ _ _ F hF h0 hc
    have hz : ∀ x : V, x = 0 := by
      intro x
      have hx : x ∈ F 0 := h0 ▸ Submodule.mem_top
      simpa only [hc, Submodule.mem_bot] using hx
    let : Subsingleton V := ⟨fun x y => (hz x).trans (hz y).symm⟩
    refine ⟨0, Module.Basis.empty V, Fin.elim0, ?_⟩
    intro j
    have hj : F j = ⊥ := le_bot_iff.mp ((hF (Nat.zero_le j)).trans (hc ▸ le_rfl))
    rw [hj]
    have hempty : {i : Fin 0 | j ≤ Fin.elim0 i} = ∅ := by
      ext i
      exact Fin.elim0 i
    rw [hempty, Set.image_empty, Submodule.span_empty]
  | succ c ih =>
    intro V _ _ _ F hF h0 hc
    let S := F 1
    let G : ℕ → Submodule k S := fun j => (F (j + 1)).comap S.subtype
    have hG : Antitone G := fun i j hij => Submodule.comap_mono (hF (Nat.add_le_add_right hij 1))
    have hG0 : G 0 = ⊤ := by
      ext x
      simp [G, S]
    have hGc : G c = ⊥ := by
      simp only [G, hc, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr S.subtype_injective]
    obtain ⟨dS, bS, wS, hbS⟩ := ih S G hG hG0 hGc
    obtain ⟨T, hT⟩ := S.exists_isCompl
    let bT := Module.finBasis k T
    let e := S.prodEquivOfIsCompl T hT
    let b := (bS.prod bT).map e
    let w : Fin dS ⊕ Fin (Module.finrank k T) → ℕ := Sum.elim (fun i => wS i + 1) (fun _ => 0)
    have hb_left (i : Fin dS) : b (Sum.inl i) = (bS i : V) := by
      simp [b, e, Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    have hb_right (i : Fin (Module.finrank k T)) : b (Sum.inr i) = (bT i : V) := by
      simp [b, e, Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    have hb : ∀ j, F j = Submodule.span k (b '' {i | j ≤ w i}) := by
      intro j
      cases j with
      | zero => simpa only [Nat.zero_le, Set.ofPred_true, Set.image_univ, b.span_eq] using h0
      | succ j =>
        have hm : (G j).map S.subtype = F (j + 1) := by
          change ((F (j + 1)).comap S.subtype).map S.subtype = F (j + 1)
          rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hF (Nat.le_add_left 1 j))]
        rw [← hm, hbS j, Submodule.map_span]
        congr 1
        ext x
        constructor
        · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
          exact ⟨Sum.inl i, by simpa only [Set.mem_ofPred_eq, w, Sum.elim_inl, Nat.add_le_add_iff_right] using hi,
            hb_left i⟩
        · rintro ⟨i, hi, rfl⟩
          cases i with
          | inl i =>
            refine ⟨bS i, ⟨i, ?_, rfl⟩, (hb_left i).symm⟩
            simpa only [Set.mem_ofPred_eq, w, Sum.elim_inl, Nat.add_le_add_iff_right] using hi
          | inr i => simp [w] at hi
    let r : Fin dS ⊕ Fin (Module.finrank k T) ≃ Fin (dS + Module.finrank k T) := finSumFinEquiv
    refine ⟨dS + Module.finrank k T, b.reindex r, w ∘ r.symm, ?_⟩
    intro j
    rw [hb j]
    congr 1
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨r i, by simpa only [Set.mem_ofPred_eq, Function.comp_apply, r.symm_apply_apply] using hi,
        by simp only [Module.Basis.reindex_apply, r.symm_apply_apply]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨r.symm i, hi, (Module.Basis.reindex_apply b r i).symm⟩

/-- Apply the finite filtration construction to the actual lower central
series. The shift by one gives positive lower-central weights. -/
theorem adaptedBasis_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.adaptedBasisExpected.{u,v} := by
  intro k L _ _ _ _ _
  obtain ⟨n, _, hc⟩ := (nilpotent_iff (k := k) (L := L)).mp inferInstance
  let F : ℕ → Submodule k L := fun j => (LieModule.lowerCentralSeries k L L j).toSubmodule
  have hF : Antitone F := by
    intro i j hij
    exact LieModule.antitone_lowerCentralSeries k L L hij
  have h0 : F 0 = ⊤ := rfl
  have hbot : F (n - 1) = ⊥ := congrArg LieSubmodule.toSubmodule hc
  obtain ⟨d, b, w, hb⟩ := finite_filtration_basis (k := k) (n - 1) L F hF h0 hbot
  refine ⟨d, b, fun i => w i + 1, (fun i => Nat.succ_pos _), ?_⟩
  intro j hj
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  change F r = Submodule.span k (b '' {i | r + 1 ≤ w i + 1})
  simpa only [Nat.add_le_add_iff_right] using hb r

end AdaptedBasis

/-- Assemble the adapted basis and weighted estimates into the quotient
construction. `truncation_spec` supplies the three proved inputs below. -/
theorem assemble_truncation
    (hBasis : Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.adaptedBasisExpected.{u,v})
    (hMul : Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.weightedMultiplicativeExpected.{u,v})
    (hStable : Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.weightedStableExpected.{u,v}) :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.truncationExpected.{u,v} := by
  intro k L _ _ _ _ _
  obtain ⟨d, b, w, hb⟩ := hBasis k L
  refine ⟨d, b, w, hb, extendDerivationLieHom, extendDerivation_extends, ?_⟩
  intro N
  have hm := hMul k L d b w hb
  have hs : ∀ (δ : LieDerivation k L L) z, z ∈ weightedSpan b w N →
      extendDerivation δ z ∈ weightedSpan b w N := by
    intro δ z hz
    exact hStable k L d b w hb δ (extendDerivation δ) (extendDerivation_extends δ) N z hz
  have hi : ∀ (a z : U k L), z ∈ weightedSpan b w N →
      a * z ∈ weightedSpan b w N ∧ z * a ∈ weightedSpan b w N := by
    intro a z hz
    have ha : a ∈ weightedSpan b w 0 := by rw [weightedSpan_zero]; trivial
    exact ⟨by simpa only [Nat.zero_add] using hm 0 N a z ha hz,
      by simpa only [Nat.add_zero] using hm N 0 z a hz ha⟩
  refine ⟨hi, hs, quotient_finiteDimensional b w hb.1 N, ?_⟩
  obtain ⟨ρ, D, hρ, hD, h1, hcomm⟩ :=
    quotient_actions (weightedSpan b w N) (fun a z hz => (hi a z hz).1) hs
  refine ⟨ρ, D, hρ, hD, h1, hcomm, ?_⟩
  intro c hc hN
  refine ⟨quotient_action_injective _ ρ hρ
    (inclusion_quotient_injective b w N (adapted_weight_lt b w hb hc hN)), ?_⟩
  exact quotient_action_nilpotent b w hb.1 hm N ρ hρ

/-- The complete derivation-stable weighted PBW truncation over every field. -/
theorem truncation_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.truncationExpected.{u,v} :=
  assemble_truncation adaptedBasis_spec weightedMultiplicative_spec weightedStable_spec

/-- Choose a positive cutoff to obtain the source's faithful representation
by nilpotent operators, simultaneously compatible with every derivation. -/
theorem faithful_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation.faithfulExpected.{u,v} := by
  intro k L _ _ _ _ _
  obtain ⟨n, hn, hc⟩ := (nilpotent_iff (k := k) (L := L)).mp inferInstance
  obtain ⟨d, b, w, hb, E, hE, h⟩ := truncation_spec k L
  obtain ⟨_, _, hfin, ρ, D, hρ, _, h1, hcomm, hfaith⟩ := h n
  have hclass : Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries.lowerCentralSeries_value
      k L (n - 1 + 1) = ⊥ := by
    change lowerCentralSeries k L (n - 1 + 1) = ⊥
    rw [Nat.sub_add_cancel (Nat.one_le_of_lt hn)]
    exact hc
  obtain ⟨hinj, hnil⟩ := hfaith (n - 1) hclass (Nat.sub_lt hn Nat.zero_lt_one)
  exact ⟨d, b, w, n, hn, hb, hfin, ρ, D, hinj, hnil, hρ, h1, hcomm⟩

end LieAlgebrasAndRepresentations.NilpotentTruncation
