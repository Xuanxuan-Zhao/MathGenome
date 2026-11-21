import MathGenome.Internal.Specs.D07.Ch20.Hilbert90Multiplicative
import MathGenome.Internal.D07.Ch14.IndependentEmbeddings
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Intervals

/-! Multiplicative Hilbert 90 and the rational-circle example, paper.tex:5990–6010.
The weighted sum uses Dedekind independence from the assigned upstream goal.
All field universes and characteristics are allowed. The circle parametrization
is also verified directly, with its exceptional point handled explicitly. -/

universe u v
namespace D07.Ch20.Hilbert90Multiplicative
noncomputable section
open scoped BigOperators

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Enumerate all automorphisms by the powers of the specified generator. -/
private def powersEquiv (σ : L ≃ₐ[K] L) (hg : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Fin (orderOf σ) ≃ (L ≃ₐ[K] L) :=
  (finEquivZPowers (isOfFinOrder_of_finite σ)).trans
    { toFun := Subtype.val
      invFun := fun τ => ⟨τ, hg τ⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem exists_quotient (σ : L ≃ₐ[K] L)
    (hg : ∀ τ, τ ∈ Subgroup.zpowers σ) (a : L) (hn : Algebra.norm K a = 1) :
    ∃ b : L, b ≠ 0 ∧ a = b / σ b := by
  classical
  let n := orderOf σ
  let c : ℕ → L := fun j => ∏ k ∈ Finset.range j, (σ ^ k) a
  have c0 : c 0 = 1 := by simp [c]
  have cs (j : ℕ) : c (j+1) = c j * (σ ^ j) a := by
    simp [c, Finset.prod_range_succ]
  have shift (j : ℕ) : a * σ (c j) = c (j+1) := by
    induction j with
    | zero => simp [c]
    | succ j ih =>
      calc
        a * σ (c (j+1)) = (a * σ (c j)) * σ ((σ ^ j) a) := by
          rw [cs j, map_mul, mul_assoc]
        _ = c (j+1) * (σ ^ (j+1)) a := by
          rw [ih, pow_succ', AlgEquiv.mul_apply]
        _ = c (j+1+1) := (cs (j+1)).symm
  have cn : c n = 1 := by
    calc
      c n = ∏ j : Fin n, (σ ^ (j : ℕ)) a := by
        exact (Fin.prod_univ_eq_prod_range (fun j => (σ ^ j) a) n).symm
      _ = ∏ τ : L ≃ₐ[K] L, τ a :=
        Fintype.prod_equiv (powersEquiv σ hg) _ _ (fun _ => rfl)
      _ = algebraMap K L (Algebra.norm K a) :=
        (Algebra.norm_eq_prod_automorphisms K a).symm
      _ = 1 := by rw [hn, map_one]
  let B : L → L := fun x => ∑ j ∈ Finset.range n, c j * (σ ^ j) x
  have hB : ∃ x, B x ≠ 0 := by
    by_contra h
    have hz : ∀ x, ∑ j : Fin n, c j * (σ ^ (j : ℕ)) x = 0 := by
      intro x
      rw [Fin.sum_univ_eq_sum_range (fun j => c j * (σ ^ j) x) n]
      exact not_exists_not.mp h x
    have hi : Function.Injective (fun j : Fin n => (σ ^ (j : ℕ)).toRingHom) := by
      intro i j hij
      apply (powersEquiv σ hg).injective
      exact AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hc := D07.Ch14.IndependentEmbeddings.finite_relation_trivial
      L L n (fun j => (σ ^ (j : ℕ)).toRingHom) hi (fun j => c j) hz
    have hp : 0 < n := (isOfFinOrder_of_finite σ).orderOf_pos
    have hh := hc ⟨0, hp⟩
    simp [c] at hh
  obtain ⟨x, hx⟩ := hB
  have hb : a * σ (B x) = B x := by
    simp only [B, map_sum, map_mul, Finset.mul_sum]
    simp_rw [← mul_assoc, shift]
    have he (j : ℕ) : σ ((σ ^ j) x) = (σ ^ (j+1)) x := by
      rw [pow_succ', AlgEquiv.mul_apply]
    simp_rw [he]
    have hs := Finset.sum_range_succ' (fun j => c j * (σ ^ j) x) n
    have ht := Finset.sum_range_succ (fun j => c j * (σ ^ j) x) n
    have hend : c n * (σ ^ n) x = c 0 * (σ ^ 0) x := by
      simp [cn, c0, n, pow_orderOf_eq_one]
    rw [hend] at ht
    exact add_right_cancel (hs.symm.trans ht)
  refine ⟨B x, hx, (eq_div_iff ?_).mpr hb⟩
  exact fun h => hx (σ.injective (by simpa using h))

theorem hilbert90 : Specs.D07.Ch20.Hilbert90Multiplicative.Hilbert90.{u,v} := by
  intro K L _ _ _ _ _ σ hg a _
  constructor
  · exact exists_quotient σ hg a
  · rintro ⟨b, hb, rfl⟩
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, Algebra.norm_eq_of_algEquiv σ]
    exact mul_inv_cancel₀ (Algebra.norm_ne_zero_iff.mpr hb)

open Specs.D07.Ch20.Hilbert90Multiplicative

theorem complex_realization : ComplexRealization := by
  let f : GaussianRational →ₐ[ℚ] ℂ := QuadraticAlgebra.lift
    ⟨Complex.I, by simp [Algebra.smul_def]⟩
  refine ⟨f, f.injective, ?_⟩
  constructor
  · intro s t
    simp [f, QuadraticAlgebra.lift, Algebra.smul_def]
  · intro z
    simp [f, QuadraticAlgebra.lift, Algebra.smul_def]

theorem rational_norm : RationalNorm := by
  intro a b
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap ℚ GaussianRational (⟨a,b⟩ : GaussianRational)).det = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm_def, sq]

theorem rational_norm_one : RationalNormOne := by
  intro a b
  rw [rational_norm]

theorem rational_denominator : RationalDenominator := by
  intro s t h hz
  have hs := sq_nonneg s
  have ht := sq_nonneg t
  have : s = 0 ∧ t = 0 := by constructor <;> nlinarith
  exact h (Prod.ext this.1 this.2)

theorem rational_quotient : RationalQuotient := by
  intro s t _
  ext <;> simp [div_eq_mul_inv, QuadraticAlgebra.inv_def, QuadraticAlgebra.norm_def]
    <;> ring

theorem rational_circle : RationalCircle := by
  intro a b
  constructor
  · intro h
    by_cases ha : a = -1
    · have hb : b = 0 := by rw [ha] at h; nlinarith
      exact ⟨0, 1, by norm_num, by norm_num [ha], by norm_num [hb]⟩
    · have hp : (a+1,b) ≠ (0,0) := by
        intro hh
        have := congrArg Prod.fst hh
        exact ha (by linarith)
      have hd := rational_denominator (a+1) b hp
      refine ⟨a+1, b, hp, ?_, ?_⟩
      · apply (eq_div_iff hd).mpr
        linear_combination (a+1) * h
      · apply (eq_div_iff hd).mpr
        linear_combination b * h
  · rintro ⟨s, t, hst, rfl, rfl⟩
    have hd := rational_denominator s t hst
    field_simp [hd]
    ring

theorem rational_hilbert90 : RationalHilbert90 := by
  intro a b
  rw [rational_norm_one]
  constructor
  · intro h
    obtain ⟨s, t, hst, ha, hb⟩ := (rational_circle a b).mp h
    refine ⟨s, t, hst, ?_⟩
    rw [rational_quotient s t hst]
    exact QuadraticAlgebra.ext ha hb
  · rintro ⟨s, t, hst, he⟩
    rw [rational_quotient s t hst] at he
    exact (rational_circle a b).mpr ⟨s, t, hst,
      congrArg QuadraticAlgebra.re he, congrArg QuadraticAlgebra.im he⟩

end
end D07.Ch20.Hilbert90Multiplicative
