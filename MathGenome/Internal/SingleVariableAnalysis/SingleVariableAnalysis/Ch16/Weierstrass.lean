import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.BernsteinConvergence
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Weierstrass

/-!
K03.16.weierstrass. Pull a continuous function back to [0,1], use the
upstream Bernstein convergence and polynomial representation, then compose
the polynomial with the inverse affine substitution. Both scalar cases use
their actual scalar polynomials. On a singleton the constant polynomial is
exact. The final bound is in the canonical supremum norm.
-/
noncomputable section
open scoped Topology unitInterval

namespace SingleVariableAnalysis

/-- The affine parameterization of a closed real interval by [0,1]. -/
def intervalAffineMap (a b : ℝ) (hab : a ≤ b) : C(I, Set.Icc a b) where
  toFun t := ⟨a + (b - a) * (t : ℝ), by
    have ht0 := t.property.1
    have ht1 := t.property.2
    constructor <;> nlinarith⟩
  continuous_toFun :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _

/-- The unit coordinate of a point in a nondegenerate closed interval. -/
def intervalUnitCoordinate {a b : ℝ} (hab : a < b) (x : Set.Icc a b) : I :=
  ⟨((x : ℝ) - a) / (b - a), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr x.property.1) (sub_pos.mpr hab).le
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [x.property.2])⟩

theorem intervalAffineMap_unitCoordinate {a b : ℝ} (hab : a < b)
    (x : Set.Icc a b) :
    intervalAffineMap a b hab.le (intervalUnitCoordinate hab x) = x := by
  apply Subtype.ext
  change a + (b - a) * (((x : ℝ) - a) / (b - a)) = (x : ℝ)
  field_simp
  ring

theorem real_weierstrass_approximation (a b : ℝ) (hab : a ≤ b)
    (f : C(Set.Icc a b, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ,
      ‖f - (⟨fun x => p.eval (x : ℝ),
        p.continuous.comp continuous_subtype_val⟩ : C(Set.Icc a b, ℝ))‖ < ε := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    refine ⟨Polynomial.C (f ⟨a, le_rfl, le_rfl⟩), ?_⟩
    apply (ContinuousMap.norm_lt_iff _ hε).mpr
    intro x
    have hx : x = (⟨a, le_rfl, le_rfl⟩ : Set.Icc a a) :=
      Subtype.ext (le_antisymm x.property.2 x.property.1)
    simp [hx, ContinuousMap.sub_apply, hε]
  · let φ := intervalAffineMap a b hlt.le
    let g : C(I, ℝ) := f.comp φ
    obtain ⟨N, hN⟩ := realBernsteinApproximation_uniform g ε hε
    let n := max N 1
    obtain ⟨p, hp⟩ := realBernsteinApproximation_polynomial n (le_max_right _ _) g
    let q := p.comp ((Polynomial.X - Polynomial.C a) * Polynomial.C (b - a)⁻¹)
    refine ⟨q, (ContinuousMap.norm_lt_iff _ hε).mpr ?_⟩
    intro x
    let t := intervalUnitCoordinate hlt x
    have hx : φ t = x := intervalAffineMap_unitCoordinate hlt x
    have hg : g t = f x := congrArg f hx
    have hq : q.eval (x : ℝ) = p.eval (t : ℝ) := by
      simp [q, t, intervalUnitCoordinate, div_eq_mul_inv]
    change ‖f x - q.eval (x : ℝ)‖ < ε
    rw [hq, ← hp t, ← hg, norm_sub_rev, Real.norm_eq_abs]
    exact hN n (le_max_left _ _) t

theorem complex_weierstrass_approximation (a b : ℝ) (hab : a ≤ b)
    (f : C(Set.Icc a b, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ,
      ‖f - (⟨fun x => p.eval ((x : ℝ) : ℂ),
        p.continuous.comp (Complex.continuous_ofReal.comp continuous_subtype_val)⟩ :
          C(Set.Icc a b, ℂ))‖ < ε := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    refine ⟨Polynomial.C (f ⟨a, le_rfl, le_rfl⟩), ?_⟩
    apply (ContinuousMap.norm_lt_iff _ hε).mpr
    intro x
    have hx : x = (⟨a, le_rfl, le_rfl⟩ : Set.Icc a a) :=
      Subtype.ext (le_antisymm x.property.2 x.property.1)
    simp [hx, ContinuousMap.sub_apply, hε]
  · let φ := intervalAffineMap a b hlt.le
    let g : C(I, ℂ) := f.comp φ
    obtain ⟨N, hN⟩ := complexBernsteinApproximation_uniform g ε hε
    let n := max N 1
    obtain ⟨p, hp⟩ := complexBernsteinApproximation_polynomial n (le_max_right _ _) g
    let q := p.comp ((Polynomial.X - Polynomial.C (a : ℂ)) *
      Polynomial.C ((b - a : ℝ) : ℂ)⁻¹)
    refine ⟨q, (ContinuousMap.norm_lt_iff _ hε).mpr ?_⟩
    intro x
    let t := intervalUnitCoordinate hlt x
    have hx : φ t = x := intervalAffineMap_unitCoordinate hlt x
    have hg : g t = f x := congrArg f hx
    have hq : q.eval ((x : ℝ) : ℂ) = p.eval ((t : ℝ) : ℂ) := by
      simp [q, t, intervalUnitCoordinate, div_eq_mul_inv]
    change ‖f x - q.eval ((x : ℝ) : ℂ)‖ < ε
    rw [hq, ← hp t, ← hg, norm_sub_rev]
    exact hN n (le_max_left _ _) t

end SingleVariableAnalysis
