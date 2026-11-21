import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanConjugacy
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootStrings
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

universe u
namespace LieAlgebrasAndRepresentations.InvariantRestrictionInjection
open Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection

section Polynomial
variable {E F : Type u} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F]

@[simp] lemma eval_ι (l : Module.Dual ℂ E) (x : E) :
    eval (SymmetricAlgebra.ι ℂ (Module.Dual ℂ E) l) x = l x := by
  simp [eval, polynomialEvaluation]

@[simp] lemma eval_pullback (a : E →ₗ[ℂ] F) (p : PolynomialFunctions F) (x : E) :
    eval (polynomialPullback a p) x = eval p (a x) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap c => simp [eval, polynomialPullback]
  | ι l => simp [polynomialPullback, LinearMap.dualMap_apply]
  | mul p q hp hq => simpa only [map_mul, eval, Pi.mul_apply] using congrArg₂ (· * ·) hp hq
  | add p q hp hq => simpa only [map_add, eval, Pi.add_apply] using congrArg₂ (· + ·) hp hq

lemma evaluation_coordinates [FiniteDimensional ℂ E] (p : PolynomialFunctions E) (x : E) :
    MvPolynomial.eval ((Module.finBasis ℂ E).equivFun x)
      (SymmetricAlgebra.equivMvPolynomial (Module.finBasis ℂ E).dualBasis p) = eval p x := by
  let b := Module.finBasis ℂ E
  have he : (MvPolynomial.aeval (b.equivFun x)).comp
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toAlgHom =
      (Pi.evalAlgHom ℂ (fun _ : E => ℂ) x).comp (polynomialEvaluation E) := by
    apply SymmetricAlgebra.algHom_ext
    apply b.dualBasis.ext
    intro i
    change MvPolynomial.aeval (b.equivFun x)
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis
        (SymmetricAlgebra.ι ℂ (Module.Dual ℂ E) (b.dualBasis i))) =
      eval (SymmetricAlgebra.ι ℂ (Module.Dual ℂ E) (b.dualBasis i)) x
    rw [SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.aeval_X, eval_ι]
    simp only [Module.Basis.equivFun_apply, Module.Basis.dualBasis_apply]
  exact DFunLike.congr_fun he p

lemma evaluation_injective [FiniteDimensional ℂ E] :
    Function.Injective (polynomialEvaluation E) := by
  intro p q hpq
  apply (SymmetricAlgebra.equivMvPolynomial (Module.finBasis ℂ E).dualBasis).injective
  apply MvPolynomial.funext
  intro v
  obtain ⟨x, rfl⟩ := (Module.finBasis ℂ E).equivFun.surjective v
  rw [evaluation_coordinates, evaluation_coordinates]
  exact congrFun hpq x

end Polynomial

section NormedPolynomial
variable {E : Type u}

lemma eval_differentiable [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (p : PolynomialFunctions E) : Differentiable ℂ (eval p) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap c =>
    convert (differentiable_const (c := c) : Differentiable ℂ (fun _ : E => c)) using 1
    funext x
    simp [eval]
  | ι l =>
    convert (LinearMap.toContinuousLinearMap l).differentiable using 1
    funext x
    exact eval_ι l x
  | mul p q hp hq =>
    convert hp.mul hq using 1
    funext x
    simp [eval]
  | add p q hp hq =>
    convert hp.add hq using 1
    funext x
    simp [eval]

end NormedPolynomial

private theorem infinitesimal_iff_exponentials_proof : infinitesimal_iff_exponentials_type.{u} := by
  intro L _ _ _ p
  let _ : NormedAddCommGroup L := Specs.LieAlgebrasAndRepresentations.RegularSemisimple.algebraNorm
  let _ : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  let _ : Algebra ℚ (L →L[ℂ] L) := RestrictScalars.algebra ℚ ℂ _
  let _ : NormedAlgebra ℚ (L →L[ℂ] L) := NormedAlgebra.restrictScalars ℚ ℂ _
  -- An affine tangent line and the corresponding adjoint orbit have the same velocity.
  have dp (z : L) := (eval_differentiable p z).hasFDerivAt
  have path (x z : L) : HasDerivAt (fun s : ℂ => eval p (z + s • ⁅x, z⁆))
      (fderiv ℂ (eval p) z ⁅x, z⁆) 0 := by
    have hv : HasDerivAt (fun s : ℂ => z + s • ⁅x, z⁆) ⁅x, z⁆ 0 := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℂ)).smul_const ⁅x, z⁆).const_add z
    exact (dp z).comp_hasDerivAt_of_eq 0 hv (by simp)
  have flow (x y : L) :
      let v (t : ℂ) := Specs.LieAlgebrasAndRepresentations.CartanConjugacy.exponentialOperator (t • x) y
      v 0 = y ∧ ∀ t, HasDerivAt (fun s => eval p (v s))
        (fderiv ℂ (eval p) (v t) ⁅x, v t⁆) t := by
    let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L x)
    let E (t : ℂ) := NormedSpace.exp (t • D)
    have hE (t : ℂ) : HasDerivAt E (D * E t) t := hasDerivAt_exp_smul_const' D t
    have hv (t : ℂ) : HasDerivAt (fun s => E s y) ⁅x, E t y⁆ t := by
      change HasDerivAt (fun s => E s y) (D (E t y)) t
      simpa only [mul_apply_eq_comp, map_zero, add_zero] using
        (hE t).clm_apply (hasDerivAt_const t y)
    have hEq (t : ℂ) :
        Specs.LieAlgebrasAndRepresentations.CartanConjugacy.exponentialOperator (t • x) y =
          E t y := by
      change (NormedSpace.exp
        (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L (t • x)))) y = E t y
      rw [map_smul, map_smul]
    dsimp only
    simp only [hEq]
    refine ⟨?_, ?_⟩
    · simp [E]
    · intro t
      exact (dp (E t y)).comp_hasDerivAt t (hv t)
  constructor
  · intro hp x y
    obtain ⟨h0, hd⟩ := flow x y
    let v (t : ℂ) := Specs.LieAlgebrasAndRepresentations.CartanConjugacy.exponentialOperator (t • x) y
    have hz (t : ℂ) : HasDerivAt (fun s => eval p (v s)) 0 t := by
      have h := hd t
      change HasDerivAt (fun s => eval p (v s)) (fderiv ℂ (eval p) (v t) ⁅x, v t⁆) t at h
      rw [(path x (v t)).unique (hp x (v t))] at h
      exact h
    have he : eval p (v 1) = eval p (v 0) := is_const_of_deriv_eq_zero
      (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0
    change v 0 = y at h0
    rw [h0] at he
    simpa [v] using he
  · intro hp x y
    obtain ⟨h0, hd⟩ := flow x y
    have hh : (fun t : ℂ => eval p
        (Specs.LieAlgebrasAndRepresentations.CartanConjugacy.exponentialOperator (t • x) y)) =
        fun _ => eval p y := funext fun t => hp (t • x) y
    have h := hd 0
    rw [hh, h0] at h
    have hz := h.unique (hasDerivAt_const (0 : ℂ) (eval p y))
    simpa only [hz] using path x y

private lemma preserved_under_closure {E : Type u} [AddCommGroup E] [Module ℂ E]
    {f : E → ℂ} {S : Set (E ≃ₗ[ℂ] E)}
    (hS : ∀ e ∈ S, ∀ x, f (e x) = f x) :
    ∀ e ∈ Subgroup.closure S, ∀ x, f (e x) = f x := by
  intro e he
  induction he using Subgroup.closure_induction with
  | mem e he => exact hS e he
  | one => intro x; rfl
  | mul e d _ _ he hd =>
    intro x
    change f (e (d x)) = f x
    rw [he, hd]
  | inv e _ he =>
    intro x
    change f (e.symm x) = f x
    simpa only [LinearEquiv.apply_symm_apply] using (he (e.symm x)).symm

private theorem exponentials_iff_inner (L : Type u) [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (p : PolynomialFunctions L) :
    ExponentialInvariant L p ↔ InnerInvariant L p := by
  constructor
  · intro hp
    apply preserved_under_closure
    intro e he y
    obtain ⟨x, hx⟩ := he
    change eval p (e.toLinearMap y) = eval p y
    rw [hx]
    exact hp x y
  · intro hp x y
    exact hp (RegularSemisimple.expAdEquiv x).toLinearEquiv (CartanConjugacy.inner_exp x) y

section Reflection
open scoped Matrix.Norms.Operator

open Specs.LieAlgebrasAndRepresentations in
/-- Each root gives a Cartan reflection whose pullback on linear functionals is
the reflection on the dual root space. -/
theorem weyl_reflection {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L) (hH : MaximalTori.IsMaximalToral_value H)
    (α : Module.Dual ℂ H) (hα : α ∈ RootDecomposition.rootSet_value H) :
    ∃ s ∈ weylGroup L H,
      (∀ h : H, s h = h - α h • RootForm.coroot_value H α) ∧
      ∀ β : Module.Dual ℂ H, β.comp s.toLinearMap = RootStrings.reflection_value H α β := by
  let c := RootForm.coroot_value H α
  have hc : α c = 2 := by
    change α (killingCoroot H α) = 2
    rw [killingCoroot_pairing hss H hH]
    exact mul_div_cancel_right₀ 2 (rootForm_self_ne_zero hss H hH α hα)
  let S : H →ₗ[ℂ] H := LinearMap.id - α.smulRight c
  have hS : Function.Involutive S := by
    intro h
    change h - α h • c - α (h - α h • c) • c = h
    rw [map_sub, map_smul, hc]
    simp only [smul_eq_mul]
    module
  let s := LinearEquiv.ofInvolutive S hS
  have hs (h : H) : s h = h - α h • c := rfl
  refine ⟨s, Subgroup.subset_closure ⟨α, hα, hs⟩, hs, ?_⟩
  intro β
  ext h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hs, map_sub, map_smul,
    RootStrings.reflection_value, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [mul_comm (α h)]

private lemma matrix_exponentialOperator {L : Type u} [LieRing L]
    [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (d : ℕ) (b : Module.Basis (Fin d) ℂ L) (x : L) :
    LinearMap.toMatrixAlgEquiv b
      (Specs.LieAlgebrasAndRepresentations.CartanConjugacy.exponentialOperator x) =
      NormedSpace.exp (LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad ℂ L x)) := by
  let : NormedAddCommGroup L := Specs.LieAlgebrasAndRepresentations.RegularSemisimple.algebraNorm
  let : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  let : Algebra ℚ (L →L[ℂ] L) := RestrictScalars.algebra ℚ ℂ _
  let : NormedAlgebra ℚ (L →L[ℂ] L) := NormedAlgebra.restrictScalars ℚ ℂ _
  let a : (L →L[ℂ] L) ≃ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    (Module.End.toContinuousLinearMap L).symm.trans (LinearMap.toMatrixAlgEquiv b)
  have ha : Continuous a :=
    a.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact NormedSpace.map_exp a ha (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L x))

private lemma restriction_reflection_invariant {L : Type u} [LieRing L]
    [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (hss : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L)
    (hH : Specs.LieAlgebrasAndRepresentations.MaximalTori.IsMaximalToral_value H)
    (p : PolynomialFunctions L) (hp : ExponentialInvariant L p)
    (s : H ≃ₗ[ℂ] H)
    (hs : ∃ α ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value H,
      ∀ h : H, s h = h - α h • Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H α) :
    ∀ h : H, eval (restriction L H p) (s h) = eval (restriction L H p) h := by
  let expOp : L → Module.End ℂ L :=
    Specs.LieAlgebrasAndRepresentations.CartanConjugacy.exponentialOperator
  obtain ⟨α, hα, hs⟩ := hs
  obtain ⟨e, f, he, hf, _, _, hef, _, _⟩ := exists_root_triple hss H hH α hα
  obtain ⟨hne, hnf, n, hn, hnH, _⟩ := RootStrings.reflection_lift hss H hH α hα e f he hf hef
  -- Compare the convergent operator exponential and the root lift in one basis.
  have hcomp : n.toLinearMap = expOp e * expOp (-f) * expOp e := by
    rw [hn]
    let b := Module.finBasis ℂ L
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [RootStrings.reflection_lift_matrix_exponential _ b e f hne hnf, map_mul, map_mul]
    simp only [expOp, matrix_exponentialOperator, map_neg]
  intro h
  have hs' : ((s h : H) : L) = n (h : L) := by
    rw [hs, hnH]
    rfl
  simp only [restriction, eval_pullback]
  change eval p ((s h : H) : L) = eval p (h : L)
  rw [hs']
  change eval p (n.toLinearMap (h : L)) = eval p (h : L)
  rw [hcomp]
  change eval p (expOp e (expOp (-f) (expOp e (h : L)))) = eval p (h : L)
  rw [hp e, hp (-f), hp e]

end Reflection

private lemma restriction_eq_imp_eq {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L]
    (hss : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L)
    (hH : Specs.LieAlgebrasAndRepresentations.MaximalTori.IsMaximalToral_value H)
    {p q : PolynomialFunctions L} (hp : InnerInvariant L p) (hq : InnerInvariant L q)
    (hrestr : restriction L H p = restriction L H q) : p = q := by
  let : NormedAddCommGroup L :=
    Specs.LieAlgebrasAndRepresentations.RegularSemisimple.algebraNorm
  let : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  have hdense := (RegularSemisimple.density L).2.1
  apply evaluation_injective
  change eval p = eval q
  apply Continuous.ext_on hdense (eval_differentiable p).continuous
    (eval_differentiable q).continuous
  intro x hx
  -- Conjugate H onto the centralizer of x to obtain a preimage of x in H.
  let K := Specs.LieAlgebrasAndRepresentations.RegularSemisimple.elementCentralizer x
  have hK := RegularSemisimple.regular_centralizer L hss x hx
  obtain ⟨e, he, hmap⟩ := cartan_conjugacy L hss H K
    ((isCartan_iff_maximal_toral hss H).mpr hH)
    ((isCartan_iff_maximal_toral hss K).mpr hK.1)
  have hxm : x ∈ H.map e.toLieHom := hmap.symm ▸ hK.2.2.1
  simp only [LieSubalgebra.mem_map, LieEquiv.coe_toLieHom] at hxm
  obtain ⟨y, hy, rfl⟩ := hxm
  let h : H := ⟨y, hy⟩
  calc
    eval p (e y) = eval p y := hp e.toLinearEquiv he y
    _ = eval (restriction L H p) h := (eval_pullback H.toSubmodule.subtype p h).symm
    _ = eval (restriction L H q) h := by rw [hrestr]
    _ = eval q y := eval_pullback H.toSubmodule.subtype q h
    _ = eval q (e y) := (hq e.toLinearEquiv he y).symm

end LieAlgebrasAndRepresentations.InvariantRestrictionInjection

namespace LieAlgebrasAndRepresentations

open Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection
open InvariantRestrictionInjection

theorem infinitesimal_iff_exponentials : infinitesimal_iff_exponentials_type.{u} :=
  infinitesimal_iff_exponentials_proof

theorem infinitesimal_iff_inner : infinitesimal_iff_inner_type.{u} := by
  intro L _ _ _ p
  exact (infinitesimal_iff_exponentials L p).trans (exponentials_iff_inner L p)

theorem restriction_weyl_invariant : restriction_weyl_invariant_type.{u} := by
  intro L _ _ _ hss H hH p hp
  change ∀ s ∈ weylGroup L H, ∀ h, eval (restriction L H p) (s h) = eval (restriction L H p) h
  apply preserved_under_closure
  exact restriction_reflection_invariant hss H hH p
    ((infinitesimal_iff_exponentials L p).mp hp)

theorem invariant_restriction_injective : invariant_restriction_injective_type.{u} := by
  intro L _ _ _ hss H hH
  let f := (restriction L H).comp (infinitesimalInvariants L).val
  have hf (p : infinitesimalInvariants L) : f p ∈ weylInvariants L H :=
    restriction_weyl_invariant L hss H hH p.val p.property
  refine ⟨f.codRestrict (weylInvariants L H) hf, fun _ => rfl, ?_⟩
  apply (AlgHom.injective_codRestrict f (weylInvariants L H) hf).2
  intro p q hpq
  have inner (r : infinitesimalInvariants L) : InnerInvariant L r.val :=
    (infinitesimal_iff_inner L r.val).mp r.property
  exact Subtype.ext (restriction_eq_imp_eq hss H hH (inner p) (inner q) hpq)

end LieAlgebrasAndRepresentations
