import MathGenome.Internal.Specs.D05.M11.Inertia.MaximalPositive
import MathGenome.Internal.D05.M02.Grassmann
import MathGenome.Internal.D05.M11.Hermitian
import MathGenome.Internal.D05.M11.Radicals
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

noncomputable section
namespace D05.M11.Inertia.MaximalPositive
open Specs.D05.M11.Inertia.MaximalPositive
open scoped BigOperators
open Module

variable {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]

/-- A positive and a nonpositive subspace have zero intersection. Grassmann
and rank-nullity then bound the positive dimension by the projection's rank. -/
theorem dimension_bound_of_nonpositive_kernel [FiniteDimensional K V]
    {W : Type*} [AddCommGroup W] [Module K W]
    (B : Form K V) (f : V →ₗ[K] W)
    (hn : ∀ x ∈ LinearMap.ker f, RCLike.re (B x x) ≤ 0)
    (U : Submodule K V) (hU : PositiveOn B U) :
    finrank K U ≤ finrank K (LinearMap.range f) := by
  have hi : U ⊓ LinearMap.ker f = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    by_contra hx0
    exact (not_lt_of_ge (hn x hx.2)) (hU x hx.1 hx0)
  have hg := D05.M02.Grassmann.grassmann U (LinearMap.ker f)
  rw [hi, finrank_bot, add_zero] at hg
  have hs := Submodule.finrank_le (U ⊔ LinearMap.ker f)
  have hr := f.finrank_range_add_finrank_ker
  omega

private theorem sum_norm_nonneg {n : ℕ} (x : Fin n → K) :
    0 ≤ ∑ i, RCLike.re (x i * star (x i)) := by
  apply Finset.sum_nonneg
  intro i _
  rw [RCLike.star_def, RCLike.mul_conj]
  simp only [← RCLike.ofReal_pow, RCLike.ofReal_re]
  positivity

theorem positive_dimension_bound :
    Specs.D05.M11.Inertia.MaximalPositive.positive_dimension_bound := by
  intro K V _ _ _ _ B p q r e h U hU
  let f : V →ₗ[K] (Fin p → K) := (LinearMap.fst K _ _).comp e.toLinearMap
  have hn : ∀ x ∈ LinearMap.ker f, RCLike.re (B x x) ≤ 0 := by
    intro x hx
    have hz : (e x).1 = 0 := hx
    rw [h x x, hz]
    simpa using neg_nonpos.mpr (sum_norm_nonneg (e x).2.1)
  have hb := dimension_bound_of_nonpositive_kernel B f hn U hU
  have hd : finrank K (LinearMap.range f) ≤ p := by
    simpa using (Submodule.finrank_le (LinearMap.range f))
  exact hb.trans hd

private theorem sum_norm_pos {n : ℕ} (x : Fin n → K) (hx : x ≠ 0) :
    0 < ∑ i, RCLike.re (x i * star (x i)) := by
  have he : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := he
  have hn (j : Fin n) : 0 ≤ RCLike.re (x j * star (x j)) := by
    rw [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    exact sq_nonneg ‖x j‖
  have hp : 0 < RCLike.re (x i * star (x i)) := by
    rw [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hi)
  exact hp.trans_le (Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i))

/-- Inclusion of the positive coordinate block into the original space. -/
def positiveInclusion {p q r : ℕ} (e : V ≃ₗ[K] Coordinates K p q r) :
    (Fin p → K) →ₗ[K] V :=
  e.symm.toLinearMap.comp (LinearMap.inl K (Fin p → K) _)

private theorem positiveInclusion_injective {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) :
    Function.Injective (positiveInclusion e) := by
  intro x y h
  have := congrArg (fun v => (e v).1) h
  simpa [positiveInclusion] using this

/-- The first block attains the upper bound. -/
theorem positive_dimension_attained (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) :
    ∃ U : Submodule K V, PositiveOn B U ∧ finrank K U = p := by
  refine ⟨LinearMap.range (positiveInclusion e), ?_, ?_⟩
  · rintro x ⟨a, rfl⟩ hx
    have ha : a ≠ 0 := by
      intro ha
      exact hx (by simp [ha])
    rw [h]
    simpa [positiveInclusion] using sum_norm_pos a ha
  · rw [LinearMap.finrank_range_of_inj (positiveInclusion_injective e)]
    simp

/-- Exchanging the positive and negative blocks realizes the negative form. -/
def swapBlocks (p q r : ℕ) : Coordinates K p q r ≃ₗ[K] Coordinates K q p r where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun x := (x.2.1, x.1, x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem normalForm_neg (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) :
    IsNormalForm (-B) (e.trans (swapBlocks p q r)) := by
  intro x y
  change -(B x y) = _
  rw [h]
  exact neg_sub _ _

theorem maximal_dimensions : Specs.D05.M11.Inertia.MaximalPositive.maximal_dimensions := by
  intro K V _ _ _ _ B p q r e h
  have hn := normalForm_neg B e h
  constructor
  · refine ⟨positive_dimension_attained B e h, ?_⟩
    rintro d ⟨U, hU, rfl⟩
    exact positive_dimension_bound B e h U hU
  · refine ⟨positive_dimension_attained (-B) _ hn, ?_⟩
    rintro d ⟨U, hU, rfl⟩
    exact positive_dimension_bound (-B) _ hn U hU

/-- Inclusion of the zero coordinate block. -/
def zeroInclusion {p q r : ℕ} (e : V ≃ₗ[K] Coordinates K p q r) :
    (Fin r → K) →ₗ[K] V :=
  e.symm.toLinearMap.comp ((LinearMap.inr K (Fin p → K) _).comp
    (LinearMap.inr K (Fin q → K) (Fin r → K)))

private theorem zeroInclusion_injective {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) : Function.Injective (zeroInclusion e) := by
  intro x y h
  have := congrArg (fun v => (e v).2.2) h
  simpa [zeroInclusion] using this

/-- Pairing with each positive and negative coordinate vector detects every
nonzero coordinate outside the zero block. -/
theorem radical_eq_zero_block (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r) (h : IsNormalForm B e) :
    radical B = LinearMap.range (zeroInclusion e) := by
  classical
  ext x
  constructor
  · intro hx
    have hx' : ∀ y, B x y = 0 := LinearMap.ext_iff.mp hx
    have hp : (e x).1 = 0 := by
      funext i
      have hi := hx' (e.symm (Pi.single i 1, 0, 0))
      rw [h] at hi
      simpa [Pi.single_apply, apply_ite] using hi
    have hq : (e x).2.1 = 0 := by
      funext j
      have hj := hx' (e.symm (0, Pi.single j 1, 0))
      rw [h] at hj
      simpa [Pi.single_apply, apply_ite] using hj
    refine ⟨(e x).2.2, e.injective ?_⟩
    simpa [zeroInclusion] using
      (show ((0, 0, (e x).2.2) : Coordinates K p q r) = e x from
        Prod.ext hp.symm (Prod.ext hq.symm rfl))
  · rintro ⟨z, rfl⟩
    apply LinearMap.ext
    intro y
    rw [h]
    simp [zeroInclusion]

theorem radical_dimension : Specs.D05.M11.Inertia.MaximalPositive.radical_dimension := by
  intro K V _ _ _ _ B p q r e h
  rw [radical_eq_zero_block B e h,
    LinearMap.finrank_range_of_inj (zeroInclusion_injective e)]
  simp

theorem unique_triple : Specs.D05.M11.Inertia.MaximalPositive.unique_triple := by
  intro K V _ _ _ _ B p q r p' q' r' e f he hf
  obtain ⟨hp, hq⟩ := maximal_dimensions B e he
  obtain ⟨hp', hq'⟩ := maximal_dimensions B f hf
  exact ⟨hp.unique hp', hq.unique hq',
    (radical_dimension B e he).symm.trans (radical_dimension B f hf)⟩

theorem real_bilinear_bridge : Specs.D05.M11.Inertia.MaximalPositive.real_bilinear_bridge := by
  intro V _ _ B
  obtain ⟨S, hS⟩ := (D05.M11.Hermitian.sesquilinear_iff_axioms
    (fun x y => B x y)).mpr ⟨B.map_add₂, by
      intro a x y
      simp,
    by intro x y z; exact (B x).map_add y z,
    by intro a x y; simp⟩
  refine ⟨S, hS, ?_, ?_⟩
  · constructor
    · intro h
      constructor
      intro x y
      simpa only [hS, star_trivial] using (h x y).symm
    · intro h x y
      simpa only [hS, star_trivial] using h.eq y x
  · ext x
    change S x = 0 ↔ B x = 0
    simp only [LinearMap.ext_iff, LinearMap.zero_apply, hS]

theorem normal_form_hermitian :
    Specs.D05.M11.Inertia.MaximalPositive.normal_form_hermitian := by
  intro K V _ _ _ B p q r e h
  have hH : Specs.D05.M11.Hermitian.isHermitian_value B := by
    intro x y
    rw [h y x, h x y]
    simp only [star_sub, star_sum, star_mul, star_star]
  refine ⟨hH, ?_⟩
  intro x
  change B x = 0 ↔ ∀ y, B y x = 0
  rw [LinearMap.ext_iff]
  simp only [LinearMap.zero_apply, hH x, star_eq_zero]

theorem real_invariants : Specs.D05.M11.Inertia.MaximalPositive.real_invariants := by
  intro V _ _ _ B p q r e h
  obtain ⟨S, hS, _, hr⟩ := real_bilinear_bridge B
  have hn : IsNormalForm S e := by
    intro x y
    simpa only [hS, star_trivial] using h x y
  obtain ⟨hp, hq⟩ := maximal_dimensions S e hn
  have hrad := radical_dimension S e hn
  rw [hr] at hrad
  refine ⟨?_, ?_, hrad⟩
  · simpa only [PositiveOn, hS, RCLike.re_to_real] using hp
  · simpa only [PositiveOn, LinearMap.neg_apply, hS, RCLike.re_to_real,
      neg_pos] using hq

theorem normal_form_matrix : Specs.D05.M11.Inertia.MaximalPositive.normal_form_matrix := by
  intro K V _ _ _ B p q r e
  classical
  constructor
  · intro h
    ext i j
    rw [LinearMap.toMatrix₂_apply]
    rw [h]
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [normalBasis, blockBasis, normalMatrix, Matrix.diagonal, Pi.basisFun_apply,
        Pi.single_apply, apply_ite, eq_comm]
  · intro h x y
    rw [apply_eq_dotProduct_toMatrix₂_mulVec (normalBasis e) (normalBasis e) B x y, h]
    simp [normalMatrix, normalBasis, blockBasis, Matrix.mulVec_diagonal, dotProduct,
      Fintype.sum_sum_type, sub_eq_add_neg, mul_neg]

end D05.M11.Inertia.MaximalPositive
