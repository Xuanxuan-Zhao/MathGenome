import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.HyperbolicSplitting
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.ExponentialCalculus
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.SplitIfs

noncomputable section
open scoped Matrix.Norms.Operator
namespace D13Unified.Ch20
open Specs.D13Unified.Ch20.HyperbolicSplitting
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- No complex eigenvalue lies on the imaginary axis. -/
def IsHyperbolic (A : Matrix n n ℝ) : Prop := hyperbolicValue A

def stableSpace (A : Matrix n n ℝ) := stableSpaceValue A
def unstableSpace (A : Matrix n n ℝ) := unstableSpaceValue A
def stableProjection (A : Matrix n n ℝ) := projectionValue A true
def unstableProjection (A : Matrix n n ℝ) := projectionValue A false

lemma conjugate_shift (A : Matrix n n ℝ) (μ : ℂ) (z : n → ℂ) :
    star ((complexification A - μ • 1) z) =
      (complexification A - (star μ) • 1) (star z) := by
  ext i
  simp [complexification, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec,
    dotProduct, star_sum, mul_comm]

lemma conjugate_shift_pow (A : Matrix n n ℝ) (μ : ℂ) (z : n → ℂ) (k : ℕ) :
    star (((complexification A - μ • 1) ^ k) z) =
      ((complexification A - (star μ) • 1) ^ k) (star z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, conjugate_shift, ih]

theorem conjugate_generalized_eigenspace : conjugateType (n := n) := by
  intro A μ z hz
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hz
  apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
  refine ⟨k, ?_⟩
  rw [← conjugate_shift_pow, hk, star_zero]

lemma spectral_conjugate (A : Matrix n n ℝ) (stable : Bool) {z : n → ℂ}
    (hz : z ∈ complexSpectralSpace A stable) :
    star z ∈ complexSpectralSpace A stable := by
  unfold complexSpectralSpace at hz
  refine Submodule.iSup_induction _ (motive := fun v => star v ∈ complexSpectralSpace A stable) hz ?_ ?_ ?_
  · intro μ z hz
    have hμ : (if stable then (star μ.val).re < 0 else 0 < (star μ.val).re) := by
      simpa using μ.property
    exact Submodule.mem_iSup_of_mem ⟨star μ.val, hμ⟩
      (conjugate_generalized_eigenspace A μ.val z hz)
  · simp
  · intro x y hx hy
    simpa only [star_add] using (complexSpectralSpace A stable).add_mem hx hy

lemma complex_spectral_isCompl (A : Matrix n n ℝ) (hA : IsHyperbolic A) :
    IsCompl (complexSpectralSpace A true) (complexSpectralSpace A false) := by
  have hd : Disjoint (complexSpectralSpace A true) (complexSpectralSpace A false) := by
    unfold complexSpectralSpace
    simp only [Bool.false_eq_true, ↓reduceIte, iSup_subtype]
    apply (complexification A).independent_maxGenEigenspace.disjoint_biSup_biSup
    exact Set.disjoint_left.mpr (by intro μ hs hu; change μ.re < 0 at hs; change 0 < μ.re at hu; linarith)
  refine ⟨hd, ?_⟩
  apply codisjoint_iff.mpr
  apply top_unique
  rw [← Module.End.iSup_maxGenEigenspace_eq_top (complexification A)]
  apply iSup_le
  intro μ
  by_cases hm : μ.re = 0
  · have he : ¬ (complexification A).HasEigenvalue μ := fun he => hA μ he hm
    have hb : (complexification A).maxGenEigenspace μ = ⊥ := by
      by_contra hb
      exact he ((show (complexification A).HasUnifEigenvalue μ ⊤ from hb).lt (by simp))
    rw [hb]; exact bot_le
  · rcases lt_or_gt_of_ne hm with hs | hu
    · apply le_sup_of_le_left
      exact le_iSup (fun ν : {ν : ℂ // ν.re < 0} => (complexification A).maxGenEigenspace ν.val) ⟨μ, hs⟩
    · apply le_sup_of_le_right
      exact le_iSup (fun ν : {ν : ℂ // 0 < ν.re} => (complexification A).maxGenEigenspace ν.val) ⟨μ, hu⟩

omit [Fintype n] [DecidableEq n] in
lemma embed_re (z : n → ℂ) :
    realEmbedding (fun i => (z i).re) = (1 / 2 : ℂ) • (z + star z) := by
  ext i
  apply Complex.ext <;> simp [realEmbedding, Complex.mul_re, Complex.mul_im] <;> ring

omit [Fintype n] [DecidableEq n] in
lemma embed_im (z : n → ℂ) :
    realEmbedding (fun i => (z i).im) = (-Complex.I / 2) • (z - star z) := by
  ext i
  apply Complex.ext <;> simp [realEmbedding, Complex.mul_re, Complex.mul_im] <;> ring

omit [Fintype n] [DecidableEq n] in
lemma re_im_decomposition (z : n → ℂ) :
    z = realEmbedding (fun i => (z i).re) +
      Complex.I • realEmbedding (fun i => (z i).im) := by
  ext i
  apply Complex.ext <;> simp [realEmbedding, Complex.mul_re, Complex.mul_im]

theorem spectral_real_form : realFormType (n := n) := by
  intro A stable z
  change z ∈ complexSpectralSpace A stable ↔
    realEmbedding (fun i => (z i).re) ∈ complexSpectralSpace A stable ∧
    realEmbedding (fun i => (z i).im) ∈ complexSpectralSpace A stable
  constructor
  · intro hz
    have hc := spectral_conjugate A stable hz
    constructor
    · rw [embed_re]; exact Submodule.smul_mem _ _ (Submodule.add_mem _ hz hc)
    · rw [embed_im]; exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hz hc)
  · rintro ⟨hr, hi⟩
    rw [re_im_decomposition z]
    exact Submodule.add_mem _ hr (Submodule.smul_mem _ _ hi)

omit [Fintype n] [DecidableEq n] in
lemma realEmbedding_injective : Function.Injective (realEmbedding (n := n)) := by
  intro x y h
  ext i
  exact Complex.ofReal_injective (congrFun h i)

theorem hyperbolic_splitting : splittingType (n := n) := by
  intro A hA
  have hc := complex_spectral_isCompl A hA
  refine ⟨?_, codisjoint_iff.mpr ?_⟩
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro x hx
    apply realEmbedding_injective
    have hz : realEmbedding x ∈ complexSpectralSpace A true ⊓ complexSpectralSpace A false :=
      ⟨hx.1, hx.2⟩
    have hz0 : realEmbedding x = 0 := by
      simpa only [hc.inf_eq_bot, Submodule.mem_bot] using hz
    simpa using hz0
  · apply top_unique
    intro x hx
    have hz : realEmbedding x ∈ complexSpectralSpace A true ⊔ complexSpectralSpace A false := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hz
    apply Submodule.mem_sup.mpr
    refine ⟨(fun i => (z i).re), (spectral_real_form A true z).mp hz |>.1,
      (fun i => (w i).re), (spectral_real_form A false w).mp hw |>.1, ?_⟩
    ext i
    exact congrArg Complex.re (congrFun hzw i)

lemma spectral_invariant_complex (A : Matrix n n ℝ) (stable : Bool) {z : n → ℂ}
    (hz : z ∈ complexSpectralSpace A stable) :
    complexification A z ∈ complexSpectralSpace A stable := by
  unfold complexSpectralSpace at hz
  refine Submodule.iSup_induction _ (motive := fun v => complexification A v ∈ complexSpectralSpace A stable) hz ?_ ?_ ?_
  · intro μ z hz
    apply Submodule.mem_iSup_of_mem μ
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ.val hz
  · simp
  · intro x y hx hy
    simpa only [map_add] using (complexSpectralSpace A stable).add_mem hx hy

lemma embed_mulVec (A : Matrix n n ℝ) (x : n → ℝ) :
    realEmbedding (A.mulVec x) = complexification A (realEmbedding x) := by
  ext i
  exact Complex.ofRealHom.map_mulVec A x i

theorem spectral_invariant : invariantType (n := n) := by
  intro A stable x hx
  change realEmbedding (A.mulVec x) ∈ complexSpectralSpace A stable
  rw [embed_mulVec]
  exact spectral_invariant_complex A stable hx

lemma projection_eq (A : Matrix n n ℝ) (hA : IsHyperbolic A) (stable : Bool) :
    projectionValue A stable = (realSpectralSpace A stable).projection
      (realSpectralSpace A (!stable)) (by
        cases stable
        · exact (hyperbolic_splitting A hA).symm
        · exact hyperbolic_splitting A hA) := by
  unfold projectionValue
  split_ifs with h
  · rfl
  · exfalso; apply h
    cases stable
    · exact (hyperbolic_splitting A hA).symm
    · exact hyperbolic_splitting A hA

theorem spectral_projection_laws : projectionLawsType (n := n) := by
  intro A hA
  have hc := hyperbolic_splitting A hA
  rw [projection_eq A hA true, projection_eq A hA false]
  change (stableSpaceValue A).projection (unstableSpaceValue A) hc +
    (unstableSpaceValue A).projection (stableSpaceValue A) hc.symm = 1 ∧ _
  refine ⟨Submodule.projection_add_projection_eq_id hc,
    Submodule.range_projection hc, Submodule.ker_projection hc,
    Submodule.range_projection hc.symm, Submodule.ker_projection hc.symm,
    Submodule.isIdempotentElem_projection hc,
    Submodule.isIdempotentElem_projection hc.symm, ?_, ?_⟩
  · apply LinearMap.ext; intro x
    exact Submodule.projection_apply_of_mem_right hc (Submodule.projection_apply_mem hc.symm x)
  · apply LinearMap.ext; intro x
    exact Submodule.projection_apply_of_mem_right hc.symm (Submodule.projection_apply_mem hc x)

lemma projection_commutes_of_invariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p q : Submodule ℝ V) (hc : IsCompl p q) (f : Module.End ℝ V)
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q) :
    Commute (p.projection q hc) f := by
  ext x
  change p.projection q hc (f x) = f (p.projection q hc x)
  nth_rw 1 [← Submodule.projection_add_projection_eq_self hc x]
  rw [map_add, map_add,
    Submodule.projection_apply_of_mem_left hc (hp _ (Submodule.projection_apply_mem hc x)),
    Submodule.projection_apply_of_mem_right hc (hq _ (Submodule.projection_apply_mem hc.symm x)),
    add_zero]

lemma projection_commutes_matrix (A : Matrix n n ℝ) (hA : IsHyperbolic A) (stable : Bool) :
    Commute (projectionValue A stable) (Matrix.toLinAlgEquiv' A) := by
  rw [projection_eq A hA stable]
  exact projection_commutes_of_invariant _ _ _ _
    (spectral_invariant A stable) (spectral_invariant A (!stable))

theorem spectral_projections_commute : commutationType (n := n) := by
  intro A hA stable
  have hc := projection_commutes_matrix A hA stable
  refine ⟨hc, fun t => ?_⟩
  let e := Matrix.toLinAlgEquiv' (R := ℝ) (n := n)
  have hm : Commute (e.symm (projectionValue A stable)) A := by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hc.eq
  have he := (hm.smul_right t).exp_right
  change projectionValue A stable * e (NormedSpace.exp (t • A)) =
    e (NormedSpace.exp (t • A)) * projectionValue A stable
  simpa only [map_mul, e.apply_symm_apply] using congrArg e he.eq

end D13Unified.Ch20
