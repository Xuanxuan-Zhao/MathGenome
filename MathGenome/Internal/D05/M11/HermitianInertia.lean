import MathGenome.Internal.Specs.D05.M11.HermitianInertia
import MathGenome.Internal.D05.M11.HermitianDiagonal
import MathGenome.Internal.D05.M11.Inertia.MaximalPositive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Hermitian inertia by normalization and induction on the complex dimension.
The only recursive subspace is the first-slot orthogonal complement of a
nonisotropic line. Uniqueness uses the upstream dimension argument. -/

noncomputable section
namespace D05.M11.HermitianInertia
open Module
open Specs.D05.M11.Inertia.MaximalPositive
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A nonzero Hermitian form has a vector of normalized diagonal value ±1. -/
theorem exists_unit_diagonal (B : Form ℂ V)
    (hB : Specs.D05.M11.Hermitian.isHermitian_value B) (h0 : B ≠ 0) :
    ∃ e : V, B e e = 1 ∨ B e e = -1 := by
  have hn : ∃ x, B x x ≠ 0 := by
    by_contra! h
    exact h0 ((D05.M11.HermitianDiagonal.eq_zero_iff_diagonal_zero B).mpr h)
  obtain ⟨x, hx⟩ := hn
  obtain ⟨d, hd⟩ := D05.M11.Hermitian.diagonal_real B hB x
  have hd0 : d ≠ 0 := by
    intro h
    apply hx
    simp [hd, h]
  let s := Real.sqrt |d|
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr hd0))
  have hs2 : s ^ 2 = |d| := Real.sq_sqrt (abs_nonneg d)
  have hval : B (((s⁻¹ : ℝ) : ℂ) • x) (((s⁻¹ : ℝ) : ℂ) • x) = ((s⁻¹ * s⁻¹ * d : ℝ) : ℂ) := by
    simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hd, mul_assoc]
  refine ⟨((s⁻¹ : ℝ) : ℂ) • x, ?_⟩
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · right
    have he : s⁻¹ * s⁻¹ * d = -1 := by
      rw [abs_of_neg hneg] at hs2
      field_simp
      nlinarith
    simpa only [he, Complex.ofReal_neg, Complex.ofReal_one] using hval
  · left
    have he : s⁻¹ * s⁻¹ * d = 1 := by
      rw [abs_of_pos hpos] at hs2
      field_simp
      nlinarith
    simpa only [he, Complex.ofReal_one] using hval

/-- The first-slot kernel against one fixed vector. -/
abbrev orthogonalComplement (B : Form ℂ V) (e : V) : Submodule ℂ V :=
  LinearMap.ker (B.flip e)

/-- Explicit algebraic splitting. No positivity or spectral statement enters. -/
def orthogonalSplit (B : Form ℂ V) (e : V) (hd : B e e ≠ 0) :
    (ℂ × orthogonalComplement B e) ≃ₗ[ℂ] V := by
  let f : (ℂ × orthogonalComplement B e) →ₗ[ℂ] V :=
    { toFun := fun z => z.1 • e + z.2
      map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add,
          Submodule.coe_add, add_smul]; abel
      map_smul' := by intro a x; simp [smul_add, smul_smul] }
  apply LinearEquiv.ofBijective f
  constructor
  · apply (injective_iff_map_eq_zero f).mpr
    rintro ⟨a, w⟩ hz
    have hw : B w e = 0 := w.property
    have ha : a = 0 := by
      have hh := congrArg (fun v => B v e) hz
      change B (a • e + (w : V)) e = B 0 e at hh
      simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, hw, add_zero,
        map_zero, LinearMap.zero_apply] at hh
      exact (mul_eq_zero.mp hh).resolve_right hd
    apply Prod.ext ha
    apply Subtype.ext
    simpa [f, ha] using hz
  · intro x
    let a := B x e / B e e
    have hw : x - a • e ∈ orthogonalComplement B e := by
      change B (x - a • e) e = 0
      simp [a, div_mul_cancel₀ _ hd]
    refine ⟨(a, ⟨x - a • e, hw⟩), ?_⟩
    change a • e + (x - a • e) = x
    abel

@[simp] theorem orthogonalSplit_apply (B : Form ℂ V) (e : V) (hd : B e e ≠ 0)
    (a : ℂ) (w : orthogonalComplement B e) :
    orthogonalSplit B e hd (a, w) = a • e + w := rfl

/-- The pairing splits, including vanishing of both cross terms. -/
theorem orthogonalSplit_pairing (B : Form ℂ V)
    (hB : Specs.D05.M11.Hermitian.isHermitian_value B) (e : V) (hd : B e e ≠ 0)
    (a b : ℂ) (w z : orthogonalComplement B e) :
    B (orthogonalSplit B e hd (a, w)) (orthogonalSplit B e hd (b, z)) =
      a * star b * B e e + B w z := by
  have hw : B w e = 0 := w.property
  have hz : B e z = 0 := by rw [hB z e, show B z e = 0 from z.property, star_zero]
  simp only [orthogonalSplit_apply, map_add, LinearMap.add_apply,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul,
    hw, hz, mul_zero, zero_add, add_zero]
  simp only [starRingEnd_apply]
  ring

/-- Adjoining one positive coordinate, in the ordered first block. -/
def prependPositive (p q r : ℕ) :
    (ℂ × Coordinates ℂ p q r) ≃ₗ[ℂ] Coordinates ℂ (p+1) q r where
  toFun x := (Fin.cons x.1 x.2.1, x.2.2)
  invFun y := (y.1 0, Fin.tail y.1, y.2)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by
    ext i <;> try rfl
    exact Fin.cases rfl (fun _ => rfl) i
  map_smul' a x := by
    ext i <;> try rfl
    exact Fin.cases rfl (fun _ => rfl) i

/-- Adjoining one negative coordinate, in the ordered second block. -/
def prependNegative (p q r : ℕ) :
    (ℂ × Coordinates ℂ p q r) ≃ₗ[ℂ] Coordinates ℂ p (q+1) r where
  toFun x := (x.2.1, Fin.cons x.1 x.2.2.1, x.2.2.2)
  invFun y := (y.2.1 0, y.1, Fin.tail y.2.1, y.2.2)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by
    ext i <;> try rfl
    exact Fin.cases rfl (fun _ => rfl) i
  map_smul' a x := by
    ext i <;> try rfl
    exact Fin.cases rfl (fun _ => rfl) i

/-- The zero form uses only the zero coordinate block, including n=0. -/
def zeroCoordinates {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) :
    V ≃ₗ[ℂ] Coordinates ℂ 0 0 n where
  toFun x := (0, 0, e x)
  invFun y := e.symm y.2.2
  left_inv x := e.symm_apply_apply x
  right_inv y := by ext i <;> simp <;> exact Fin.elim0 i
  map_add' x y := by simp
  map_smul' a x := by simp

private theorem normal_form_exists_of_finrank (n : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    finrank ℂ V = n → ∀ B : Form ℂ V,
    Specs.D05.M11.Hermitian.isHermitian_value B →
    ∃ (p q r : ℕ) (e : V ≃ₗ[ℂ] Coordinates ℂ p q r), IsNormalForm B e := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ hn B hB
    by_cases h0 : B = 0
    · refine ⟨0, 0, finrank ℂ V, zeroCoordinates (Module.finBasis ℂ V).equivFun, ?_⟩
      intro x y
      simp [h0]
    obtain ⟨v, hv⟩ := exists_unit_diagonal B hB h0
    have hd : B v v ≠ 0 := by rcases hv with hv | hv <;> simp [hv]
    let W := orthogonalComplement B v
    have hW : W ≠ ⊤ := by
      intro h
      have hh : v ∈ W := by rw [h]; trivial
      exact hd hh
    have hdim : finrank ℂ W < n := by rw [← hn]; exact Submodule.finrank_lt hW
    let C : Form ℂ W := B.domRestrict₁₂ W W
    have hC : Specs.D05.M11.Hermitian.isHermitian_value C := fun x y => hB x y
    obtain ⟨p, q, r, e, he⟩ := ih (finrank ℂ W) hdim rfl C hC
    let S := orthogonalSplit B v hd
    let F := S.symm.trans (LinearEquiv.prodCongr (LinearEquiv.refl ℂ ℂ) e)
    have hF (a : ℂ) (w : W) : F (S (a, w)) = (a, e w) := by
      simp only [F, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
    rcases hv with hp | hq
    · refine ⟨p+1, q, r, F.trans (prependPositive p q r), ?_⟩
      intro x y
      obtain ⟨⟨a, w⟩, rfl⟩ := S.surjective x
      obtain ⟨⟨b, z⟩, rfl⟩ := S.surjective y
      simp only [LinearEquiv.trans_apply]
      rw [hF a w, hF b z]
      rw [orthogonalSplit_pairing B hB v hd a b w z, hp]
      have hc : B w z = (∑ i, (e w).1 i * star ((e z).1 i)) -
        ∑ j, (e w).2.1 j * star ((e z).2.1 j) := he w z
      rw [hc]
      simp [prependPositive, Fin.sum_univ_succ]
      ring
    · refine ⟨p, q+1, r, F.trans (prependNegative p q r), ?_⟩
      intro x y
      obtain ⟨⟨a, w⟩, rfl⟩ := S.surjective x
      obtain ⟨⟨b, z⟩, rfl⟩ := S.surjective y
      simp only [LinearEquiv.trans_apply]
      rw [hF a w, hF b z]
      rw [orthogonalSplit_pairing B hB v hd a b w z, hq]
      have hc : B w z = (∑ i, (e w).1 i * star ((e z).1 i)) -
        ∑ j, (e w).2.1 j * star ((e z).2.1 j) := he w z
      rw [hc]
      simp [prependNegative, Fin.sum_univ_succ]
      ring

theorem normal_form_exists : Specs.D05.M11.HermitianInertia.normal_form_exists := by
  intro V _ _ _ B hB
  exact normal_form_exists_of_finrank (finrank ℂ V) rfl B hB

theorem matrix_normal_form_exists :
    Specs.D05.M11.HermitianInertia.matrix_normal_form_exists := by
  intro V _ _ _ B hB
  obtain ⟨p, q, r, e, he⟩ := normal_form_exists B hB
  exact ⟨p, q, r, e, (D05.M11.Inertia.MaximalPositive.normal_form_matrix B e).mp he⟩

theorem normal_form_unique : Specs.D05.M11.HermitianInertia.normal_form_unique := by
  intro V _ _ _ B p q r p' q' r' e f he hf
  exact D05.M11.Inertia.MaximalPositive.unique_triple B e f he hf

theorem intrinsic_dimensions : Specs.D05.M11.HermitianInertia.intrinsic_dimensions := by
  intro V _ _ _ B p q r e he
  obtain ⟨hp, hq⟩ := D05.M11.Inertia.MaximalPositive.maximal_dimensions B e he
  exact ⟨hp, hq, D05.M11.Inertia.MaximalPositive.radical_dimension B e he⟩

theorem inertia : Specs.D05.M11.HermitianInertia.inertia := by
  intro V _ _ _ B hB
  obtain ⟨p, q, r, e, he⟩ := normal_form_exists B hB
  refine ⟨(p, q, r), ⟨e, he⟩, ?_⟩
  rintro ⟨p', q', r'⟩ ⟨f, hf⟩
  obtain ⟨hp, hq, hr⟩ := normal_form_unique B f e hf he
  exact Prod.ext hp (Prod.ext hq hr)

end D05.M11.HermitianInertia
