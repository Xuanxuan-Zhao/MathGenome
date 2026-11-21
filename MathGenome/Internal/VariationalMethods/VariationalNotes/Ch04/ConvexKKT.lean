import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.ConvexKKT
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.RefinedSlater
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Subgradients
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap

noncomputable section
open Set Topology
open scoped BigOperators
universe u v w z
namespace VariationalNotes.Ch04

section Algebra
variable {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]

lemma lagrangian_eq_objective_of_complementarity (q : ConvexProgram X I A J)
    (m : Multipliers I A J) (x : X) (hx : x ∈ feasibleSet q)
    (hc : complementarity q m x) : lagrangianReal q m x = (q.f x).untopD 0 := by
  have he : (∑ j, m.nu j * (q.e j x - q.d j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hx.2.1.2 j, sub_self, mul_zero]
  simp only [ConvexProgramSpecs.lagrangianReal, Finset.sum_eq_zero (fun i _ => hc.1 i),
    Finset.sum_eq_zero (fun l _ => hc.2 l), he, add_zero]

theorem kkt_sufficient : KKTSpecs.kkt_sufficient_at (X := X) (I := I) (A := A) (J := J) := by
  intro q m x ⟨hx, hm, hmin, hc⟩
  refine ⟨hx, fun y hy => ?_⟩
  obtain ⟨hfx, _⟩ := commonDomain_finite q x hx.1
  obtain ⟨hfy, _⟩ := commonDomain_finite q y hy.1
  rw [hfx, hfy]
  apply WithTop.coe_le_coe.mpr
  rw [← lagrangian_eq_objective_of_complementarity q m x hx hc]
  exact (hmin.2 y hy.1).trans (lagrangian_le_objective q m y hm hy)

lemma primalValue_eq_of_minimizer (q : ConvexProgram X I A J) (x : X)
    (hx : IsPrimalMinimizer q x) :
    convexProgramPrimalValue q = (((q.f x).untopD 0 : ℝ) : EReal) := by
  have hf := (commonDomain_finite q x hx.1.1).1
  apply le_antisymm
  · have h := iInf_le (fun y : feasibleSet q => ConvexAnalysis.Specs.toEReal (q.f y)) ⟨x, hx.1⟩
    rw [hf] at h
    exact h
  · apply le_iInf
    intro y
    have hyf := (commonDomain_finite q y y.property.1).1
    have hh := hx.2 y y.property
    rw [hf, hyf] at hh
    rw [hyf]
    exact EReal.coe_le_coe (WithTop.coe_le_coe.mp hh)

/-- At a feasible point the gap is a sum of nonpositive inequality
products. Equality forces every product to vanish, including zero multipliers. -/
lemma complementarity_of_lagrangian_eq_objective (q : ConvexProgram X I A J)
    (m : Multipliers I A J) (x : X) (hm : admissible m) (hx : x ∈ feasibleSet q)
    (heq : lagrangianReal q m x = (q.f x).untopD 0) : complementarity q m x := by
  have hg (i : I) : m.lam i * (q.g i x).untopD 0 ≤ 0 := by
    have h := hx.2.2 i
    rw [(commonDomain_finite q x hx.1).2 i] at h
    exact mul_nonpos_of_nonneg_of_nonpos (hm.1 i) (WithTop.coe_le_coe.mp h)
  have ha (l : A) : m.mu l * (q.a l x - q.b l) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hm.2 l) (sub_nonpos.mpr (hx.2.1.1 l))
  have he : (∑ j, m.nu j * (q.e j x - q.d j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hx.2.1.2 j, sub_self, mul_zero]
  have hgs : (∑ i, m.lam i * (q.g i x).untopD 0) ≤ 0 := Finset.sum_nonpos (fun i _ => hg i)
  have has : (∑ l, m.mu l * (q.a l x - q.b l)) ≤ 0 := Finset.sum_nonpos (fun l _ => ha l)
  change (q.f x).untopD 0 + _ + _ + _ = (q.f x).untopD 0 at heq
  rw [he] at heq
  have hgz : (∑ i, m.lam i * (q.g i x).untopD 0) = 0 := by linarith
  have haz : (∑ l, m.mu l * (q.a l x - q.b l)) = 0 := by linarith
  constructor
  · intro i
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hg i)).mp hgz i (Finset.mem_univ i)
  · intro l
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun l _ => ha l)).mp haz l (Finset.mem_univ l)

variable [TopologicalSpace X]

theorem lagrangian_minimizer_iff_subgradient :
    KKTSpecs.lagrangian_minimizer_iff_subgradient_at (X := X) (I := I) (A := A) (J := J) := by
  intro q m x hx
  change IsLagrangianMinimizer q m x ↔
    (0 : X →L[ℝ] ℝ) ∈ ConvexAnalysis.subdifferential (lagrangian q m) x
  rw [ConvexAnalysis.mem_subdifferential_iff (lagrangian_on_domain q m x hx)]
  simp only [zero_apply, add_zero]
  constructor
  · intro h y
    by_cases hy : y ∈ commonDomain q
    · rw [lagrangian_on_domain q m y hy]
      exact WithTop.coe_le_coe.mpr (h.2 y hy)
    · rw [lagrangian_outside_domain q m y hy]
      exact le_top
  · intro h
    refine ⟨hx, fun y hy => ?_⟩
    have hh := h y
    rw [lagrangian_on_domain q m y hy] at hh
    exact WithTop.coe_le_coe.mp hh

theorem kkt_iff_subgradient :
    KKTSpecs.kkt_iff_subgradient_at (X := X) (I := I) (A := A) (J := J) := by
  intro q m x
  constructor
  · rintro ⟨hx, hm, hmin, hc⟩
    exact ⟨hx, hm, (lagrangian_minimizer_iff_subgradient q m x hx.1).mp hmin, hc⟩
  · rintro ⟨hx, hm, hs, hc⟩
    exact ⟨hx, hm, (lagrangian_minimizer_iff_subgradient q m x hx.1).mpr hs, hc⟩
end Algebra

theorem kkt_necessary : KKTSpecs.kkt_necessary.{u,v,w,z} := by
  intro X _ _ _ _ _ _ _ I A J _ _ _ q p x hp hw hx
  obtain ⟨m, hm, hdual, _⟩ := refined_slater q p hp hw
  have hpx : (q.f x).untopD 0 = p := by
    have hh := (primalValue_eq_of_minimizer q x hx).symm.trans hp
    exact EReal.coe_injective hh
  have hlower (y : X) (hy : y ∈ commonDomain q) : p ≤ lagrangianReal q m y := by
    have hh := iInf_le (fun z : commonDomain q => (lagrangianReal q m z : EReal)) ⟨y, hy⟩
    change ConvexProgramSpecs.dualFunction q m ≤ _ at hh
    rw [hdual] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have heq : lagrangianReal q m x = (q.f x).untopD 0 := by
    apply le_antisymm (lagrangian_le_objective q m x hm hx.1)
    rw [hpx]
    exact hlower x hx.1.1
  refine ⟨m, hx.1, hm, ⟨hx.1.1, fun y hy => ?_⟩,
    complementarity_of_lagrangian_eq_objective q m x hm hx.1 heq⟩
  exact (heq.trans hpx).le.trans (hlower y hy)

section ConvexDerivatives
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma convex_supporting_inequality {f : E → ℝ} {D : Set E}
    (hf : ConvexOn ℝ D f) {x : E} (hx : x ∈ D) {f' : E →L[ℝ] ℝ}
    (hd : HasFDerivAt f f' x) (y : E) (hy : y ∈ D) :
    f x + f' (y - x) ≤ f y := by
  let l : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hc : ConvexOn ℝ (l ⁻¹' D) (f ∘ l) := hf.comp_affineMap l
  have h0 : (0 : ℝ) ∈ l ⁻¹' D := by simpa [l] using hx
  have h1 : (1 : ℝ) ∈ l ⁻¹' D := by simpa [l] using hy
  have hder : HasDerivAt (f ∘ l) (f' (y - x)) 0 := by
    apply HasFDerivAt.comp_hasDerivAt
    · simpa [l] using hd
    · exact AffineMap.hasDerivAt_lineMap
  have hh := hc.le_slope_of_hasDerivAt h0 h1 (by norm_num : (0 : ℝ) < 1) hder
  simp only [slope_def_field, Function.comp_apply, l, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hh
  linarith

lemma convex_minimizes_iff_derivative_zero {f : E → ℝ} {D : Set E}
    (hf : ConvexOn ℝ D f) {x : E} (hx : x ∈ interior D) {f' : E →L[ℝ] ℝ}
    (hd : HasFDerivAt f f' x) : (∀ y ∈ D, f x ≤ f y) ↔ f' = 0 := by
  constructor
  · intro h
    have hl : IsLocalMin f x := (show IsMinOn f D x from h).isLocalMin (mem_interior_iff_mem_nhds.mp hx)
    exact hl.hasFDerivAt_eq_zero hd
  · intro h y hy
    have hh := convex_supporting_inequality hf (interior_subset hx) hd y hy
    simpa [h] using hh

end ConvexDerivatives

section Smooth
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]

/-- A nonnegative weighted convex part plus an unrestricted affine part
is convex on exactly the common domain. -/
lemma lagrangianReal_convexOn (q : ConvexProgram X I A J) (m : Multipliers I A J)
    (hm : admissible m) : ConvexOn ℝ (commonDomain q) (lagrangianReal q m) := by
  classical
  let r : X →ᵃ[ℝ] ℝ :=
    (∑ l, m.mu l • (q.a l - AffineMap.const ℝ X (q.b l))) +
    (∑ j, m.nu j • (q.e j - AffineMap.const ℝ X (q.d j)))
  have hr : ConvexOn ℝ (commonDomain q) r := by
    refine ⟨commonDomain_convex q, ?_⟩
    intro x hx y hy a b ha hb hab
    rw [← Convex.combo_affine_apply hab]
  have hbase : ConvexOn ℝ (commonDomain q)
      (fun x => (penalizedObjective q m.lam x).untopD 0) :=
    ConvexAnalysis.convexOn_untopD_comp (penalizedObjective_convex q m.lam hm.1)
      (AffineMap.id ℝ X) (commonDomain_convex q)
      (fun x hx => by
        change x ∈ ConvexAnalysis.effectiveDomain (penalizedObjective q m.lam)
        rw [penalizedObjective_domain]
        exact hx)
  apply (hbase.add hr).congr
  intro x hx
  have hval : (penalizedObjective q m.lam x).untopD 0 =
      (q.f x).untopD 0 + ∑ i, m.lam i * (q.g i x).untopD 0 := by
    rw [penalizedObjective, ite_eq_left hx, WithTop.untopD_coe]
  change (penalizedObjective q m.lam x).untopD 0 + r x = _
  let ev : (X →ᵃ[ℝ] ℝ) →+ ℝ :=
    { toFun := fun a => a x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hrval : r x = (∑ l, m.mu l * (q.a l x - q.b l)) +
      ∑ j, m.nu j * (q.e j x - q.d j) := by
    change ev (_ + _) = _
    rw [map_add, map_sum, map_sum]
    rfl
  rw [hval, hrval]
  change _ = (q.f x).untopD 0 + _ + _ + _
  ring

lemma hasFDerivAt_lagrangianReal (q : ConvexProgram X I A J) (m : Multipliers I A J)
    (x : X) (hf : DifferentiableAt ℝ (fun y => (q.f y).untopD 0) x)
    (hg : ∀ i, DifferentiableAt ℝ (fun y => (q.g i y).untopD 0) x)
    (ha : ∀ l, DifferentiableAt ℝ (q.a l) x)
    (he : ∀ j, DifferentiableAt ℝ (q.e j) x) :
    HasFDerivAt (lagrangianReal q m)
      (fderiv ℝ (fun y => (q.f y).untopD 0) x +
      ∑ i, m.lam i • fderiv ℝ (fun y => (q.g i y).untopD 0) x +
      ∑ l, m.mu l • fderiv ℝ (q.a l) x +
      ∑ j, m.nu j • fderiv ℝ (q.e j) x) x := by
  exact ((hf.hasFDerivAt.add
    (HasFDerivAt.fun_sum (fun i _ => (hg i).hasFDerivAt.const_mul (m.lam i)))).add
    (HasFDerivAt.fun_sum (fun l _ => ((ha l).hasFDerivAt.sub_const (q.b l)).const_mul (m.mu l)))).add
    (HasFDerivAt.fun_sum (fun j _ => ((he j).hasFDerivAt.sub_const (q.d j)).const_mul (m.nu j)))

theorem lagrangian_minimizer_iff_derivative :
    KKTSpecs.lagrangian_minimizer_iff_derivative_at (X := X) (I := I) (A := A) (J := J) := by
  intro q m x hm hx hf hg ha he
  have hh := convex_minimizes_iff_derivative_zero (lagrangianReal_convexOn q m hm)
    hx (hasFDerivAt_lagrangianReal q m x hf hg ha he)
  exact (and_iff_right (interior_subset hx)).trans hh
end Smooth

section Gradient
variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]

theorem lagrangian_minimizer_iff_gradient :
    KKTSpecs.lagrangian_minimizer_iff_gradient_at (X := X) (I := I) (A := A) (J := J) := by
  intro q m x hm hx hf hg ha he
  rw [lagrangian_minimizer_iff_derivative q m x hm hx hf hg ha he]
  have hh := (InnerProductSpace.toDual ℝ X).injective.eq_iff
    (a := gradient (fun y => (q.f y).untopD 0) x +
      ∑ i, m.lam i • gradient (fun y => (q.g i y).untopD 0) x +
      ∑ l, m.mu l • gradient (q.a l) x +
      ∑ j, m.nu j • gradient (q.e j) x) (b := 0)
  simpa only [map_add, map_sum, map_smul, map_zero, toDual_gradient] using hh

theorem kkt_iff_gradient :
    KKTSpecs.kkt_iff_gradient_at (X := X) (I := I) (A := A) (J := J) := by
  intro q m x hx hf hg ha he
  constructor
  · rintro ⟨hfeas, hm, hmin, hc⟩
    exact ⟨hfeas, hm,
      (lagrangian_minimizer_iff_gradient q m x hm hx hf hg ha he).mp hmin, hc⟩
  · rintro ⟨hfeas, hm, hgrad, hc⟩
    exact ⟨hfeas, hm,
      (lagrangian_minimizer_iff_gradient q m x hm hx hf hg ha he).mpr hgrad, hc⟩

end Gradient

end VariationalNotes.Ch04
