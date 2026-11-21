import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SectionalRecovery
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace P202.Geometry.SectionalRecovery
open P202.SectionalData
universe u

section Algebra
variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Polarization and Bianchi, without any dimension assumption. -/
theorem zero_of_diagonal (f : V → V → V → V → ℝ)
    (add₁ : ∀ x t y z w, f (x + t) y z w = f x y z w + f t y z w)
    (add₂ : ∀ x y t z w, f x (y + t) z w = f x y z w + f x t z w)
    (hs : CurvatureSymmetries f) (hd : ∀ x y, f x y y x = 0) :
    ∀ x y z w, f x y z w = 0 := by
  obtain ⟨h₁, h₂, hp, hb⟩ := hs
  have hdiag (x y w : V) : f x y y w = 0 := by
    have e := hd (x + w) y
    -- Linearity in the fourth slot follows here from pair interchange.
    have hadd (a b c d e : V) : f a b c (d + e) = f a b c d + f a b c e := by
      rw [hp a b c (d + e), add₂, ← hp c d a b, ← hp c e a b]
    rw [add₁, hadd, hadd, hd, hd] at e
    have eq : f w y y x = f x y y w := by
      rw [hp w y y x, h₁ y x w y, h₂ x y w y]
      ring
    rw [eq] at e
    linarith
  have hmid (x y z w : V) : f x y z w = -f x z y w := by
    have e := hdiag x (y + z) w
    have hadd (a b c d e : V) : f a b (c + d) e = f a b c e + f a b d e := by
      rw [hp a b (c + d) e, add₁, ← hp c e a b, ← hp d e a b]
    rw [add₂, hadd, hadd, hdiag, hdiag] at e
    linarith
  intro x y z w
  have e := hb x y z w
  have e₁ := hmid y z x w
  have e₂ := h₁ y x z w
  have e₃ := hmid z x y w
  have e₄ := h₁ z y x w
  linarith

/-- Skewness makes the sectional numerator vanish on dependent pairs. -/
theorem diagonal_dependent (f : V → V → V → V → ℝ)
    (smul₁ : ∀ c x y z w, f (c • x) y z w = c * f x y z w)
    (smul₂ : ∀ c x y z w, f x (c • y) z w = c * f x y z w)
    (hs : ∀ x y z w, f x y z w = -f y x z w)
    (x y : V) (h : ¬LinearIndependent ℝ ![x, y]) : f x y y x = 0 := by
  have self (v z w : V) : f v v z w = 0 := by linarith only [hs v v z w]
  by_cases hy : y = 0
  · subst y
    have e := smul₂ 0 x (0 : V) (0 : V) x
    simpa using e
  · have hh : ∃ t : ℝ, t • y = x := by
      by_contra hn
      apply h
      apply (linearIndependent_fin2 (K := ℝ) (f := ![x, y])).mpr
      change y ≠ 0 ∧ (∀ t : ℝ, t • y ≠ x)
      exact ⟨hy, fun t ht => hn ⟨t, ht⟩⟩
    obtain ⟨t, ht⟩ := hh
    rw [← ht, smul₁, self, mul_zero]

/-- The independent-pair hypothesis suffices even when there are no planes. -/
theorem zero_of_independent_diagonal (f : V → V → V → V → ℝ)
    (add₁ : ∀ x t y z w, f (x + t) y z w = f x y z w + f t y z w)
    (add₂ : ∀ x y t z w, f x (y + t) z w = f x y z w + f x t z w)
    (smul₁ : ∀ c x y z w, f (c • x) y z w = c * f x y z w)
    (smul₂ : ∀ c x y z w, f x (c • y) z w = c * f x y z w)
    (hs : CurvatureSymmetries f)
    (hd : ∀ x y, LinearIndependent ℝ ![x, y] → f x y y x = 0) :
    ∀ x y z w, f x y z w = 0 := by
  apply zero_of_diagonal f add₁ add₂ hs
  intro x y
  by_cases h : LinearIndependent ℝ ![x, y]
  · exact hd x y h
  · exact diagonal_dependent f smul₁ smul₂ hs.1 x y h

/-- Strict positivity of the Gram determinant on independent pairs. -/
theorem gram_pos (B : LinearMap.BilinForm ℝ V)
    (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x)
    (x y : V) (h : LinearIndependent ℝ ![x, y]) :
    0 < B x x * B y y - B x y ^ 2 := by
  have hi := (linearIndependent_fin2 (K := ℝ) (f := ![x, y])).mp h
  change y ≠ 0 ∧ (∀ t : ℝ, t • y ≠ x) at hi
  have hy := hp y hi.1
  have hv : x - (B x y / B y y) • y ≠ 0 := by
    intro e
    exact hi.2 _ (sub_eq_zero.mp e).symm
  have hq := hp _ hv
  have he : B y y * B (x - (B x y / B y y) • y)
      (x - (B x y / B y y) • y) = B x x * B y y - B x y ^ 2 := by
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    rw [hs y x]
    field_simp
    <;> ring
  rw [← he]
  exact mul_pos hy hq

/-- The sphere-positive algebraic space-form expression. -/
def spaceForm (B : LinearMap.BilinForm ℝ V) (κ : ℝ) (x y z w : V) : ℝ :=
  κ * (B y z * B x w - B x z * B y w)

theorem spaceForm_symmetries (B : LinearMap.BilinForm ℝ V) (κ : ℝ)
    (hs : ∀ x y, B x y = B y x) : CurvatureSymmetries (spaceForm B κ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z w; dsimp [spaceForm]; ring
  · intro x y z w; dsimp [spaceForm]; ring
  · intro x y z w; dsimp [spaceForm]
    rw [hs w x, hs z y, hs z x, hs w y]
    ring
  · intro x y z w; dsimp [spaceForm]
    rw [hs z x, hs z y, hs y x]
    ring

/-- Subtracting algebraic curvature tensors preserves their identities. -/
theorem symmetries_sub (f g : V → V → V → V → ℝ)
    (hf : CurvatureSymmetries f) (hg : CurvatureSymmetries g) :
    CurvatureSymmetries (fun x y z w => f x y z w - g x y z w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z w; linarith only [hf.1 x y z w, hg.1 x y z w]
  · intro x y z w; linarith only [hf.2.1 x y z w, hg.2.1 x y z w]
  · intro x y z w; exact congrArg₂ (fun a b : ℝ => a - b)
      (hf.2.2.1 x y z w) (hg.2.2.1 x y z w)
  · intro x y z w; linarith only [hf.2.2.2 x y z w, hg.2.2.2 x y z w]

/-- Function-level version, also directly applicable to the upstream curvature form. -/
theorem constant_of_sectional (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hpos : ∀ x, x ≠ 0 → 0 < B x x)
    (f : V → V → V → V → ℝ) (κ : ℝ)
    (add₁ : ∀ x t y z w, f (x + t) y z w = f x y z w + f t y z w)
    (add₂ : ∀ x y t z w, f x (y + t) z w = f x y z w + f x t z w)
    (smul₁ : ∀ c x y z w, f (c • x) y z w = c * f x y z w)
    (smul₂ : ∀ c x y z w, f x (c • y) z w = c * f x y z w)
    (hf : CurvatureSymmetries f)
    (hsec : ∀ x y, LinearIndependent ℝ ![x, y] →
      f x y y x / (B x x * B y y - B x y ^ 2) = κ) :
    ∀ x y z w, f x y z w = spaceForm B κ x y z w := by
  have hz := zero_of_independent_diagonal
    (fun x y z w => f x y z w - spaceForm B κ x y z w)
    (by intros; rw [add₁]; simp only [spaceForm, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.add_right]; ring)
    (by intros; rw [add₂]; simp only [spaceForm, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.add_right]; ring)
    (by intros; rw [smul₁]; simp only [spaceForm, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right]; ring)
    (by intros; rw [smul₂]; simp only [spaceForm, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right]; ring)
    (symmetries_sub _ _ hf (spaceForm_symmetries B κ hB))
    (by
      intro x y hi
      have hd := ne_of_gt (gram_pos B hB hpos x y hi)
      have e := (div_eq_iff hd).mp (hsec x y hi)
      dsimp [spaceForm]
      rw [hB y x]
      nlinarith only [e])
  intro x y z w
  exact sub_eq_zero.mp (hz x y z w)
end Algebra

open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurvatureData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem recovery : P202Specs.Geometry.SectionalRecovery.recoveryType.{u} := by
  intro n a M _ S g p r s hr hs hsec
  have hz := zero_of_independent_diagonal
    (fun x y z w => r x y z w - s x y z w)
    (by intros; simp only [map_add, LinearMap.add_apply]; ring)
    (by intros; simp only [map_add, LinearMap.add_apply]; ring)
    (by intros; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (symmetries_sub _ _ hr hs)
    (by
      intro x y h
      have hd := ne_of_gt (gram_pos (pairing g p) (g.symmetric p) (g.positive p) x y h)
      exact sub_eq_zero.mpr ((div_left_inj' hd).mp (hsec x y h)))
  ext x y z w
  exact sub_eq_zero.mp (hz x y z w)

theorem no_planes : P202Specs.Geometry.SectionalRecovery.no_planesType.{u} := by
  intro n a M _ S p r hr hn
  have hz := zero_of_independent_diagonal
    (fun x y z w => r x y z w)
    (by intros; simp only [map_add, LinearMap.add_apply])
    (by intros; simp only [map_add, LinearMap.add_apply])
    (by intros; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
    (by intros; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
    hr (by intro x y h; exact (hn x y h).elim)
  ext x y z w
  exact hz x y z w

theorem constant_sectional : P202Specs.Geometry.SectionalRecovery.constant_sectionalType.{u} := by
  intro n a M _ S g p r κ hr hk
  exact constant_of_sectional (pairing g p) (g.symmetric p) (g.positive p)
    (fun x y z w => r x y z w) κ
    (by intros; simp only [map_add, LinearMap.add_apply])
    (by intros; simp only [map_add, LinearMap.add_apply])
    (by intros; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
    (by intros; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]) hr hk

theorem curvature_constant : P202Specs.Geometry.SectionalRecovery.curvature_constantType.{u} := by
  intro n a M _ S g C hc T hT p κ hk
  apply constant_of_sectional (pairing g p) (g.symmetric p) (g.positive p)
    (curvatureForm g T p) κ
  · exact CurvatureAlgebra.form_add_first g T p
  · exact CurvatureAlgebra.form_add_second g T p
  · exact CurvatureAlgebra.form_smul_first g T p
  · exact CurvatureAlgebra.form_smul_second g T p
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact CurvatureAlgebra.form_skew_first C g T hT p
    · exact CurvatureAlgebra.form_skew_last C g hc.2 T hT p
    · exact CurvatureAlgebra.form_pair_exchange C g hc T hT p
    · intro x y z w
      have e := congrArg (fun v => pairing g p v w)
        (CurvatureAlgebra.tensor_first_bianchi C hc.1 T hT p x y z)
      simpa only [curvatureForm, pairing, map_add, LinearMap.add_apply,
        map_zero, LinearMap.zero_apply] using e
  · exact hk
/-- The boundary cases use the dimension of the actual derivation tangent fiber. -/
theorem low_dimension : P202Specs.Geometry.SectionalRecovery.low_dimensionType.{u} := by
  intro n a M _ S p r hr hn
  apply no_planes p r hr
  intro x y hi
  letI := (SmoothManifolds.tangent_dimension S p).1
  have hh := hi.fintype_card_le_finrank
  rw [(SmoothManifolds.tangent_dimension S p).2] at hh
  have h2 : 2 ≤ n := by simpa using hh
  exact (by decide : ¬ (2 : ℕ) ≤ 1) (h2.trans hn)
end P202.Geometry.SectionalRecovery
