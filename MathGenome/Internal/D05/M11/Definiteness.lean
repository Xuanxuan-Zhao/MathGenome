import MathGenome.Internal.Specs.D05.M11.Definiteness
import MathGenome.Internal.D05.M11.Inertia
import MathGenome.Internal.D05.M11.HermitianInertia
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Linarith

noncomputable section
namespace D05.M11.Definiteness
open scoped BigOperators
open Specs.D05.M11.Inertia.MaximalPositive
open Specs.D05.M11.Definiteness
open private sum_norm_nonneg sum_norm_pos normalForm_neg from MathGenome.Internal.D05.M11.Inertia.MaximalPositive

abbrev positiveDefinite : signPredicate_type := positiveDefinite_value
abbrev positiveSemidefinite : signPredicate_type := positiveSemidefinite_value
abbrev negativeDefinite : signPredicate_type := negativeDefinite_value
abbrev negativeSemidefinite : signPredicate_type := negativeSemidefinite_value
abbrev indefinite : signPredicate_type := indefinite_value
abbrev isotropic : isotropic_type := isotropic_value

variable {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]

private theorem positive_test (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) (i : Fin p) :
    B (e.symm (Pi.single i 1, 0, 0)) (e.symm (Pi.single i 1, 0, 0)) = 1 := by
  classical
  rw [h]
  simp [Pi.single_apply, apply_ite]

private theorem negative_test (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) (i : Fin q) :
    B (e.symm (0, Pi.single i 1, 0)) (e.symm (0, Pi.single i 1, 0)) = -1 := by
  classical
  rw [h]
  simp [Pi.single_apply, apply_ite]

private theorem psd_iff (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) :
    positiveSemidefinite (fun x y => B x y) ↔ q = 0 := by
  constructor
  · intro hp
    by_contra hq
    have hq' : 0 < q := Nat.pos_of_ne_zero hq
    have hh := hp (e.symm (0, Pi.single (⟨0, hq'⟩ : Fin q) 1, 0))
    dsimp only at hh
    rw [negative_test B e h] at hh
    norm_num at hh
  · rintro rfl x
    change 0 ≤ RCLike.re (B x x)
    rw [h]
    simpa using sum_norm_nonneg (e x).1

private theorem pd_iff (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) :
    positiveDefinite (fun x y => B x y) ↔ q = 0 ∧ r = 0 := by
  constructor
  · intro hp
    have hps : positiveSemidefinite (fun x y => B x y) := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · exact le_of_lt (hp x hx)
    have hq := (psd_iff B e h).mp hps
    refine ⟨hq, ?_⟩
    by_contra hr
    let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    let x := e.symm (0, 0, Pi.single i 1)
    have hx : x ≠ 0 := by
      intro hx
      have hi := congrArg (fun x => (e x).2.2 i) hx
      simpa [x] using hi
    have hh := hp x hx
    dsimp only at hh
    rw [h] at hh
    simpa [x] using hh
  · rintro ⟨rfl, rfl⟩ x hx
    have ha : (e x).1 ≠ 0 := by
      intro ha
      apply hx
      apply e.injective
      simpa only [map_zero] using (Prod.ext ha (Subsingleton.elim (e x).2 0))
    change 0 < RCLike.re (B x x)
    rw [h]
    simpa using sum_norm_pos (e x).1 ha

private theorem exists_positive_iff (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) :
    (∃ x, 0 < RCLike.re (B x x)) ↔ 0 < p := by
  constructor
  · rintro ⟨x, hx⟩
    by_contra hp
    have hp' : p = 0 := by omega
    subst p
    rw [h] at hx
    have hn := sum_norm_nonneg (e x).2.1
    simpa using (not_lt_of_ge (show RCLike.re ((∑ i : Fin 0,
      (e x).1 i * star ((e x).1 i)) - ∑ j, (e x).2.1 j * star ((e x).2.1 j)) ≤ 0 by
        simpa using neg_nonpos.mpr hn)) hx
  · intro hp
    refine ⟨e.symm (Pi.single (⟨0, hp⟩ : Fin p) 1, 0, 0), ?_⟩
    rw [positive_test B e h]
    simp

private theorem exists_negative_iff (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) :
    (∃ x, RCLike.re (B x x) < 0) ↔ 0 < q := by
  simpa using (exists_positive_iff (-B) _ (normalForm_neg B e h))

theorem normal_form_criteria : Specs.D05.M11.Definiteness.normal_form_criteria := by
  intro K V _ _ _ B p q r e h
  refine ⟨pd_iff B e h, psd_iff B e h, ?_, ?_, ?_⟩
  · simpa [negativeDefinite_value, positiveDefinite, negativeDefinite, positiveDefinite_value, Pi.neg_apply] using
      pd_iff (-B) _ (normalForm_neg B e h)
  · simpa [negativeSemidefinite_value, positiveSemidefinite, negativeSemidefinite, positiveSemidefinite_value, Pi.neg_apply] using
      psd_iff (-B) _ (normalForm_neg B e h)
  · exact and_congr (exists_positive_iff B e h) (exists_negative_iff B e h)

theorem real_normal_form_criteria : Specs.D05.M11.Definiteness.real_normal_form_criteria := by
  intro V _ _ B p q r e h
  obtain ⟨S, hS, _, _⟩ := D05.M11.Inertia.MaximalPositive.real_bilinear_bridge B
  have hn : IsNormalForm S e := by
    intro x y
    simpa only [hS, star_trivial] using h x y
  simpa only [positiveDefinite_value, positiveSemidefinite_value, negativeDefinite_value,
    negativeSemidefinite_value, indefinite_value, Pi.neg_apply, hS] using
    normal_form_criteria S e hn

/-- With no negative block, a zero sum of norm squares kills every positive
coordinate. Pairing with an arbitrary vector then vanishes in both slots. -/
theorem semidefinite_zero_iff_radical (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e)
    (hp : positiveSemidefinite (fun x y => B x y)) (x : V) :
    B x x = 0 ↔ (∀ y, B x y = 0) ∧ (∀ y, B y x = 0) := by
  have hq := (psd_iff B e h).mp hp
  subst q
  constructor
  · intro hx
    have ha : (e x).1 = 0 := by
      by_contra ha
      have hh := sum_norm_pos (e x).1 ha
      have hz := congrArg RCLike.re hx
      rw [h] at hz
      have hz' : (∑ i, RCLike.re ((e x).1 i * star ((e x).1 i))) = 0 := by
        simpa using hz
      linarith
    constructor
    · intro y
      rw [h, ha]
      simp
    · intro y
      rw [h, ha]
      simp
  · rintro ⟨hx, _⟩
    exact hx x

theorem real_semidefinite_radical : Specs.D05.M11.Definiteness.real_semidefinite_radical := by
  intro V _ _ _ B hB hp x
  obtain ⟨p, q, r, e, he⟩ := D05.M11.Inertia.normal_form_exists B hB
  obtain ⟨S, hS, _, _⟩ := D05.M11.Inertia.MaximalPositive.real_bilinear_bridge B
  have hn : IsNormalForm S e := by
    intro x y
    simpa only [hS, star_trivial] using he x y
  have hpS : positiveSemidefinite (fun x y => S x y) := by
    simpa only [positiveSemidefinite, positiveSemidefinite_value, hS] using hp
  simpa only [hS, Specs.D05.M11.Radicals.leftRadical_value,
    Specs.D05.M11.Radicals.rightRadical_value, LinearMap.mem_ker, LinearMap.ext_iff,
    LinearMap.zero_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply] using
    semidefinite_zero_iff_radical S e hn hpS x

theorem complex_semidefinite_radical : Specs.D05.M11.Definiteness.complex_semidefinite_radical := by
  intro V _ _ _ B hB hp x
  obtain ⟨p, q, r, e, he⟩ := D05.M11.HermitianInertia.normal_form_exists B hB
  exact semidefinite_zero_iff_radical B e he hp x

theorem isotropy_counterexample : Specs.D05.M11.Definiteness.isotropy_counterexample := by
  let B : LinearMap.BilinForm ℝ (Fin 2 → ℝ) := (!![1, 0; 0, -1] : Matrix _ _ ℝ).toBilin'
  have hval (x y : Fin 2 → ℝ) : B x y = x 0 * y 0 - x 1 * y 1 := by
    simp [B, Matrix.toBilin'_apply, Fin.sum_univ_two]
    ring
  have hsym : B.IsSymm := ⟨by intro x y; simp only [hval]; ring⟩
  have hl : Specs.D05.M11.Radicals.leftRadical_value B = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hz : ∀ y, B x y = 0 := LinearMap.ext_iff.mp hx
    have h0 := hz ![1, 0]
    have h1 := hz ![0, 1]
    simp only [hval, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one, mul_zero, sub_zero, zero_sub, neg_eq_zero] at h0 h1
    ext i
    fin_cases i <;> assumption
  have hr : Specs.D05.M11.Radicals.rightRadical_value B = ⊥ := by
    rw [← D05.M11.Radicals.radicals_eq_of_symmetric B hsym, hl]
  have hv : (![1, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro hv
    have := congrFun hv 0
    norm_num at this
  refine ⟨B, ?_, hsym, (D05.M11.Nondegenerate.nondegenerate_iff_left B).mpr hl,
    hl, hr, ⟨hv, ?_⟩, ?_⟩
  · ext i j
    simp [B, LinearMap.toMatrix₂_apply, Pi.basisFun_apply]
  · norm_num [hval]
  · simpa [hl] using hv

theorem zero_dimensional_positive_definite :
    Specs.D05.M11.Definiteness.zero_dimensional_positive_definite := by
  intro K V _ _ _ _ B hd x hx
  have : Subsingleton V := Module.finrank_zero_iff.mp hd
  exact (hx (Subsingleton.elim _ _)).elim

end D05.M11.Definiteness
