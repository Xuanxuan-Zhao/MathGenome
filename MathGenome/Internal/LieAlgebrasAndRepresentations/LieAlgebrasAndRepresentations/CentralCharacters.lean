import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CentralCharacters
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HarishChandraIsomorphism
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Nullstellensatz
import Batteries.Tactic.OpenPrivate

noncomputable section

universe u v

namespace LieAlgebrasAndRepresentations.CentralCharacters

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.CentralCharacters
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
open Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.SolvableRadical
open scoped Pointwise
open LieAlgebrasAndRepresentations.HarishChandraIsomorphism
  (evaluation_generator evaluation_ext evaluation_translation harish_chandra_isomorphism
    highest_vector_scalar)
open private finite_weightWeylGroup from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ChevalleyRestriction

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L)

omit [FiniteDimensional ℂ L] in
private theorem evaluation_in_basis {ι : Type*} (b : Module.Basis ι ℂ H) (x : ι → ℂ) :
    evaluation H (b.constr ℂ x) =
      (MvPolynomial.aeval x).comp (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply b.ext
  intro i
  change evaluation H (b.constr ℂ x) (SymmetricAlgebra.ι ℂ H (b i)) =
    MvPolynomial.aeval x (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι ℂ H (b i)))
  rw [evaluation_generator, b.constr_basis, SymmetricAlgebra.equivMvPolynomial_ι_apply,
    MvPolynomial.aeval_X]

/-- Pull back polynomials along the inverse Weyl transformation of weights. -/
private def pullback (w : weightWeylGroup H) :
    SymmetricAlgebra ℂ H →ₐ[ℂ] SymmetricAlgebra ℂ H :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι ℂ H).comp ((Module.evalEquiv ℂ H).symm.toLinearMap.comp
      ((w.val⁻¹).toLinearMap.dualMap.comp (Module.Dual.eval ℂ H))))

private theorem evaluation_pullback (w : weightWeylGroup H) (x : Module.Dual ℂ H) :
    (evaluation H x).comp (pullback H w) = evaluation H (w.val⁻¹ x) := by
  apply SymmetricAlgebra.algHom_ext
  ext h
  change evaluation H x (pullback H w (SymmetricAlgebra.ι ℂ H h)) =
    evaluation H (w.val⁻¹ x) (SymmetricAlgebra.ι ℂ H h)
  simp only [pullback, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, evaluation_generator,
    LinearEquiv.coe_coe, Module.apply_evalEquiv_symm_apply,
    LinearMap.dualMap_apply, Module.Dual.eval_apply]

private theorem evaluation_pullback_apply (w : weightWeylGroup H) (x : Module.Dual ℂ H)
    (p : SymmetricAlgebra ℂ H) :
    evaluation H x (pullback H w p) = evaluation H (w.val⁻¹ x) p :=
  DFunLike.congr_fun (evaluation_pullback H w x) p

private local instance polynomialAction : MulSemiringAction (weightWeylGroup H) (SymmetricAlgebra ℂ H) where
  smul w p := pullback H w p
  one_smul p := evaluation_ext H fun x => by
    change evaluation H x (pullback H 1 p) = evaluation H x p
    rw [evaluation_pullback_apply]
    rfl
  mul_smul w v p := evaluation_ext H fun x => by
    change evaluation H x (pullback H (w * v) p) =
      evaluation H x (pullback H w (pullback H v p))
    simp only [evaluation_pullback_apply, Subgroup.coe_mul, mul_inv_rev, LinearEquiv.mul_apply]
  smul_zero w := map_zero (pullback H w)
  smul_add w := map_add (pullback H w)
  smul_one w := map_one (pullback H w)
  smul_mul w := map_mul (pullback H w)

private local instance polynomialActionInvariant :
    Algebra.IsInvariant (weylInvariants H) (SymmetricAlgebra ℂ H) (weightWeylGroup H) where
  isInvariant p hp := by
    refine ⟨⟨p, ?_⟩, rfl⟩
    intro w hw x
    have he := congrArg (evaluation H x) (hp (⟨w⁻¹, (weightWeylGroup H).inv_mem hw⟩))
    change evaluation H x (pullback H ⟨w⁻¹, (weightWeylGroup H).inv_mem hw⟩ p) = _ at he
    simpa only [evaluation_pullback_apply, inv_inv] using he

private local instance polynomialActionCommutes :
    SMulCommClass (weightWeylGroup H) (weylInvariants H) (SymmetricAlgebra ℂ H) where
  smul_comm w p q := by
    change pullback H w (p.val * q) = p.val * pullback H w q
    rw [map_mul]
    congr 1
    apply evaluation_ext H
    intro x
    rw [evaluation_pullback_apply]
    exact p.property w.val⁻¹ ((weightWeylGroup H).inv_mem w.property) x

private theorem characters_eq_of_ker_eq {A : Type*} [Ring A] [Algebra ℂ A]
    {c d : A →ₐ[ℂ] ℂ} (hker : RingHom.ker c.toRingHom = RingHom.ker d.toRingHom) :
    c = d := by
  ext a
  have h : a - algebraMap ℂ A (c a) ∈ RingHom.ker c.toRingHom := by simp
  rw [hker] at h
  simpa using (RingHom.sub_mem_ker_iff d.toRingHom).mp h |>.symm

private def restrictedEvaluation (x : Module.Dual ℂ H) : weylInvariants H →ₐ[ℂ] ℂ :=
  (evaluation H x).comp (weylInvariants H).val

private def pointIdeal (x : Module.Dual ℂ H) : Ideal (SymmetricAlgebra ℂ H) :=
  RingHom.ker (evaluation H x).toRingHom

private theorem pointIdeal_smul (w : weightWeylGroup H) (x : Module.Dual ℂ H) :
    w • pointIdeal H x = pointIdeal H (w.val x) := by
  ext p
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change evaluation H x (pullback H w⁻¹ p) = 0 ↔ evaluation H (w.val x) p = 0
  simp only [evaluation_pullback_apply, Subgroup.coe_inv, inv_inv]

private theorem invariant_evaluations_eq_iff [Finite (weightWeylGroup H)]
    (x y : Module.Dual ℂ H) :
    restrictedEvaluation H x = restrictedEvaluation H y ↔
      ∃ w : weightWeylGroup H, y = w.val x := by
  constructor
  · intro he
    let : (pointIdeal H x).IsPrime := RingHom.ker_isPrime (evaluation H x).toRingHom
    let : (pointIdeal H y).IsPrime := RingHom.ker_isPrime (evaluation H y).toRingHom
    have hu : (pointIdeal H x).under (weylInvariants H) =
        (pointIdeal H y).under (weylInvariants H) := by
      change RingHom.ker (restrictedEvaluation H x).toRingHom =
        RingHom.ker (restrictedEvaluation H y).toRingHom
      rw [he]
    -- Evaluation kernels over the same invariant ideal form a single Weyl orbit.
    obtain ⟨w, hw⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
      (weylInvariants H) (SymmetricAlgebra ℂ H) (weightWeylGroup H)
      (pointIdeal H x) (pointIdeal H y) hu
    rw [pointIdeal_smul] at hw
    refine ⟨w, LinearMap.ext fun h => ?_⟩
    simpa only [evaluation_generator] using
      DFunLike.congr_fun (characters_eq_of_ker_eq hw) (SymmetricAlgebra.ι ℂ H h)
  · rintro ⟨w, rfl⟩
    ext p
    exact (p.property w.val w.property x).symm

private theorem maximal_ideal_is_point (Q : Ideal (SymmetricAlgebra ℂ H)) [Q.IsMaximal] :
    ∃ x, Q = pointIdeal H x := by
  let b := Module.finBasis ℂ H
  let e := SymmetricAlgebra.equivMvPolynomial b
  let P := Q.comap e.symm.toRingHom
  have hP : P.IsMaximal := Ideal.comap_isMaximal_of_surjective e.symm.toRingHom e.symm.surjective
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hP
  refine ⟨b.constr ℂ x, ?_⟩
  ext p
  have hp : e p ∈ P ↔ p ∈ Q := by simp [P]
  rw [← hp, hx, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  change MvPolynomial.aeval x (e p) = 0 ↔ evaluation H (b.constr ℂ x) p = 0
  rw [evaluation_in_basis]
  rfl

private theorem every_invariant_character [Finite (weightWeylGroup H)]
    (c : weylInvariants H →ₐ[ℂ] ℂ) : ∃ x, restrictedEvaluation H x = c := by
  let : Algebra.IsIntegral (weylInvariants H) (SymmetricAlgebra ℂ H) :=
    Algebra.IsInvariant.isIntegral (weylInvariants H) (SymmetricAlgebra ℂ H) (weightWeylGroup H)
  let P := RingHom.ker c.toRingHom
  let : P.IsMaximal := RingHom.ker_isMaximal_of_surjective c.toRingHom fun a =>
    ⟨algebraMap ℂ _ a, by simp⟩
  have hker : RingHom.ker (algebraMap (weylInvariants H) (SymmetricAlgebra ℂ H)) ≤ P := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
    exact bot_le
  obtain ⟨Q, hQ, hover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hker
  let _ := hQ
  obtain ⟨x, rfl⟩ := maximal_ideal_is_point H Q
  exact ⟨x, characters_eq_of_ker_eq hover⟩

/-- Central characters of Verma modules and their quotients, classified by
shifted Weyl orbits. Every complex algebra character of the center occurs. -/
theorem central_characters : central_characters_type.{u,v} := by
  intro L _ _ _ hss H _ φ hφ
  let : Finite (weightWeylGroup H) := finite_weightWeylGroup H hss
  obtain ⟨habel, ht, γ, hγ⟩ := harish_chandra_isomorphism hss H φ hφ
  let ρ := rhoValue H φ
  let χ (lam : Module.Dual ℂ H) := (restrictedEvaluation H (lam + ρ)).comp γ.toAlgHom
  refine ⟨habel, ht, γ, χ, hγ, fun _ _ => rfl,
    VermaModules.character_existsUnique hss H φ hφ, ?_, ?_, ?_⟩
  · intro lam ξ hξ z
    have hχ : χ lam z = evaluation H lam (projectionValue H φ habel ht z.val) := by
      change evaluation H (lam + ρ) (γ z).val = _
      rw [hγ]
      change evaluation H (lam + ρ) (translation H ρ (projectionValue H φ habel ht z.val)) = _
      rw [evaluation_translation, add_sub_cancel_right]
    have scalar (v : induced_value H φ ξ) : z.val • v = χ lam z • v := by
      rw [hχ]
      exact highest_vector_scalar hss H φ hφ habel ht lam ξ hξ z v
    refine ⟨scalar, ?_⟩
    intro V _ _ _ _ _ q hq v
    obtain ⟨w, rfl⟩ := hq v
    calc
      z.val • q w = q (z.val • w) := (q.map_smul _ _).symm
      _ = q (χ lam z • w) := congrArg q (scalar w)
      _ = χ lam z • q w := q.map_smul_of_tower _ _
  · intro lam mu
    rw [← invariant_evaluations_eq_iff H (lam + ρ) (mu + ρ)]
    constructor
    · intro he
      apply AlgHom.ext
      intro p
      obtain ⟨z, rfl⟩ := γ.surjective p
      exact DFunLike.congr_fun he z
    · intro he
      change (restrictedEvaluation H (lam + ρ)).comp γ.toAlgHom =
        (restrictedEvaluation H (mu + ρ)).comp γ.toAlgHom
      rw [he]
  · intro c
    obtain ⟨x, hx⟩ := every_invariant_character H (c.comp γ.symm.toAlgHom)
    refine ⟨x - ρ, AlgHom.ext fun z => ?_⟩
    change restrictedEvaluation H (x - ρ + ρ) (γ z) = c z
    rw [sub_add_cancel, hx, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, γ.symm_apply_apply]

end LieAlgebrasAndRepresentations.CentralCharacters
