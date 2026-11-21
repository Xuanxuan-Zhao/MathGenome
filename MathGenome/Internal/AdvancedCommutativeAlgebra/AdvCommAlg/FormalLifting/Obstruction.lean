import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Obstruction
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.TorsorOfLifts
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Conormal
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.JacobianPresentation

namespace AdvCommAlg.FormalLifting.Obstruction

open Specs.AdvCommAlg.Differentials.SquareZero
open Specs.AdvCommAlg.FormalLifting.Obstruction
open TensorProduct
universe u v w z
noncomputable section

section General
variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

theorem presentation_lift : presentationLift := by
  intro A B C _ _ _ _ _ E hE N hN u
  obtain ⟨φ, hφ⟩ := smooth_reduction_surjective hE N hN (u.comp (presentationMap E))
  exact ⟨φ, hφ⟩

variable (E : Algebra.Extension.{z} A B) (N : Ideal C) (hN : N ^ 2 = ⊥)
  (u : B →ₐ[A] C ⧸ N)

lemma presenting_lift_mem (φ : Lifts N (u.comp (presentationMap E))) (f : E.ker) :
    φ.1 f.val ∈ N := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have H := congrArg (fun g : E.Ring →ₐ[A] C ⧸ N => g f.val) φ.2
  simpa [AlgHom.comp_apply, presentationMap,
    show algebraMap E.Ring B f.val = 0 from f.property] using H

/-- Restrict a presenting lift to its kernel, before quotienting by I². -/
def kernelEvaluation (φ : Lifts N (u.comp (presentationMap E))) : E.ker →ₗ[A] N where
  toFun f := ⟨φ.1 f.val, presenting_lift_mem E N u φ f⟩
  map_add' f g := Subtype.ext (map_add φ.1 f.val g.val)
  map_smul' a f := Subtype.ext (φ.1.toLinearMap.map_smul a f.val)

include hN in
lemma kernelEvaluation_product (φ : Lifts N (u.comp (presentationMap E)))
    (f g : E.ker) : kernelEvaluation E N u φ (f * g) = 0 := by
  apply Subtype.ext
  change φ.1 (f.val * g.val) = 0
  rw [map_mul]
  have H := Ideal.mul_mem_mul (presenting_lift_mem E N u φ f)
    (presenting_lift_mem E N u φ g)
  rw [← pow_two, hN] at H
  exact H

/-- The obstruction is defined on the actual conormal module. -/
def obstructionMap (φ : Lifts N (u.comp (presentationMap E))) :
    letI := idealModule N hN u
    E.Cotangent →ₗ[B] N := by
  letI := idealModule N hN u
  let q := Ideal.Cotangent.lift (kernelEvaluation E N u φ)
    (kernelEvaluation_product E N hN u φ)
  refine { toFun := fun x => q x.val
           map_add' := fun x y => q.map_add x.val y.val
           map_smul' := ?_ }
  intro b x
  obtain ⟨f, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  change q (E.σ b • Ideal.toCotangent E.ker f) = b • q (Ideal.toCotangent E.ker f)
  rw [← (Ideal.toCotangent E.ker).map_smul]
  apply Subtype.ext
  change φ.1 (E.σ b * f.val) = ((quotientAction N hN) (u b)
    (kernelEvaluation E N u φ f) : C)
  have H := congrArg (fun g : E.Ring →ₐ[A] C ⧸ N => g (E.σ b)) φ.2
  have H' : Ideal.Quotient.mk N (φ.1 (E.σ b)) = u b := by
    simpa [AlgHom.comp_apply, presentationMap] using H
  rw [← H', map_mul]
  rfl

@[simp] lemma obstructionMap_mk (φ : Lifts N (u.comp (presentationMap E))) (f : E.ker) :
    (obstructionMap E N hN u φ (Algebra.Extension.Cotangent.mk f) : C) = φ.1 f.val := rfl

/-- Extension of scalars converts the upstream differential coordinates on P
into B-linear coordinates on B ⊗[P] Ω[P/A]. -/
lemma presentation_coordinates (φ : Lifts N (u.comp (presentationMap E))) :
    letI := idealModule N hN u
    ∃ e : (E.CotangentSpace →ₗ[B] N) ≃ Lifts N (u.comp (presentationMap E)),
      ∀ h p, (e h).1 p = φ.1 p + (h (1 ⊗ₜ[E.Ring] KaehlerDifferential.D A E.Ring p) : C) := by
  letI := idealModule N hN u
  letI := idealModule N hN (u.comp (presentationMap E))
  letI := idealTower N hN (u.comp (presentationMap E))
  letI : IsScalarTower E.Ring B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e := (LinearMap.liftBaseChangeEquiv B).symm.toEquiv.trans
    (liftEquiv N hN (u.comp (presentationMap E)) φ)
  refine ⟨e, ?_⟩
  intro h p
  exact liftEquiv_apply N hN (u.comp (presentationMap E)) φ
    ((LinearMap.liftBaseChangeEquiv B).symm h) p

/-- Vanishing of the obstruction before taking a cokernel is exactly
factorization of this presenting lift through B. -/
lemma obstruction_zero_iff (φ : Lifts N (u.comp (presentationMap E))) :
    letI := idealModule N hN u
    obstructionMap E N hN u φ = 0 ↔
      ∃ g : Lifts N u, g.1.comp (presentationMap E) = φ.1 := by
  letI := idealModule N hN u
  constructor
  · intro hz
    have hk : E.ker ≤ RingHom.ker φ.1 := by
      intro f hf
      have H := congrArg (fun o => (o (Algebra.Extension.Cotangent.mk ⟨f, hf⟩) : C)) hz
      exact H
    let g := AlgHom.liftOfSurjective (presentationMap E) E.algebraMap_surjective φ.1 hk
    have hg : g.comp (presentationMap E) = φ.1 := AlgHom.liftOfSurjective_comp ..
    have hred : (Ideal.Quotient.mkₐ A N).comp g = u := by
      apply AlgHom.cancel_right (show Function.Surjective (presentationMap E) from E.algebraMap_surjective) |>.mp
      rw [AlgHom.comp_assoc, hg]
      exact φ.2
    exact ⟨⟨g, hred⟩, hg⟩
  · rintro ⟨g, hg⟩
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    apply Subtype.ext
    rw [obstructionMap_mk]
    have H := congrArg (fun k : E.Ring →ₐ[A] C => k f.val) hg
    simpa [AlgHom.comp_apply, presentationMap,
      show algebraMap E.Ring B f.val = 0 from f.property] using H.symm

/-- Changing the lift adds exactly a map that factors through δ. -/
lemma obstruction_change (φ : Lifts N (u.comp (presentationMap E)))
    (e : (letI := idealModule N hN u
      E.CotangentSpace →ₗ[B] N) ≃ Lifts N (u.comp (presentationMap E)))
    (he : ∀ h p, (e h).1 p = φ.1 p +
      (h (1 ⊗ₜ[E.Ring] KaehlerDifferential.D A E.Ring p) : C)) :
    letI := idealModule N hN u
    ∀ h, obstructionMap E N hN u (e h) = obstructionMap E N hN u φ + deltaStar E N hN u h := by
  letI := idealModule N hN u
  intro h
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  apply Subtype.ext
  change (obstructionMap E N hN u (e h) (Algebra.Extension.Cotangent.mk f) : C) =
    (obstructionMap E N hN u φ (Algebra.Extension.Cotangent.mk f) : C) +
      (h (E.cotangentComplex (Algebra.Extension.Cotangent.mk f)) : C)
  rw [obstructionMap_mk, obstructionMap_mk, Algebra.Extension.cotangentComplex_mk]
  exact he h f.val

theorem obstruction_theory : obstructionTheory := by
  intro A B C _ _ _ _ _ E N hN u
  letI := idealModule N hN u
  let S := LinearMap.range (deltaStar E N hN u)
  refine ⟨obstructionMap E N hN u, fun φ f => obstructionMap_mk E N hN u φ f, ?_, ?_⟩
  · intro φ ψ
    obtain ⟨e, he⟩ := presentation_coordinates E N hN u φ
    obtain ⟨h, rfl⟩ := e.surjective ψ
    rw [obstruction_change E N hN u φ e he h, map_add]
    have hz : S.mkQ (deltaStar E N hN u h) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨h, rfl⟩
    change S.mkQ _ = S.mkQ _ + S.mkQ _
    rw [hz, add_zero]
  · intro φ
    constructor
    · intro hz
      have ho : obstructionMap E N hN u φ ∈ S :=
        (Submodule.Quotient.mk_eq_zero _).mp hz
      obtain ⟨h, hh⟩ := ho
      obtain ⟨e, he⟩ := presentation_coordinates E N hN u φ
      have hzero : obstructionMap E N hN u (e (-h)) = 0 := by
        rw [obstruction_change E N hN u φ e he, map_neg, hh, add_neg_cancel]
      obtain ⟨g, _⟩ := (obstruction_zero_iff E N hN u (e (-h))).mp hzero
      exact ⟨g⟩
    · rintro ⟨g⟩
      let ψ : Lifts N (u.comp (presentationMap E)) :=
        ⟨g.1.comp (presentationMap E), by
          simpa only [AlgHom.comp_assoc] using
            congrArg (fun k => k.comp (presentationMap E)) g.2⟩
      have hψ : obstructionMap E N hN u ψ = 0 :=
        (obstruction_zero_iff E N hN u ψ).mpr ⟨g, rfl⟩
      obtain ⟨e, he⟩ := presentation_coordinates E N hN u ψ
      obtain ⟨h, hh⟩ := e.surjective φ
      rw [← hh, obstruction_change E N hN u ψ e he, hψ, zero_add]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨h, rfl⟩

/-- FL-06 for an arbitrary surjection of compatible A-algebras. -/
theorem surjective_presentation : surjectivePresentation := by
  intro A B C _ _ _ _ _ P _ _ _ _ h hP N hN u
  let E := Specs.AdvCommAlg.Differentials.conormalExtension A P B h
  exact ⟨presentation_lift E hP N hN u, obstruction_theory E N hN u⟩

end General
section Finite
variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

lemma derivation_expansion {σ M : Type*} [Fintype σ] [AddCommGroup M]
    [Module A M] [Module (MvPolynomial σ A) M]
    [IsScalarTower A (MvPolynomial σ A) M]
    (D : Derivation A (MvPolynomial σ A) M) (f : MvPolynomial σ A) :
    D f = ∑ i, MvPolynomial.pderiv i f • D (MvPolynomial.X i) := by
  classical
  let b := KaehlerDifferential.mvPolynomialBasis A σ
  calc
    D f = D.liftKaehlerDifferential (KaehlerDifferential.D A (MvPolynomial σ A) f) := by simp
    _ = ∑ i, MvPolynomial.pderiv i f • D (MvPolynomial.X i) := by
      conv_lhs => rw [← b.sum_repr (KaehlerDifferential.D A (MvPolynomial σ A) f)]
      simp [b]

theorem polynomial_correction : polynomialCorrection := by
  intro A B C _ _ _ _ _ n m P N hN u x hx
  letI := idealModule N hN u
  intro t f
  let q := u.comp (MvPolynomial.aeval P.val)
  let φ : MvPolynomial (Fin n) A →ₐ[A] C := MvPolynomial.aeval x
  have hφ : (Ideal.Quotient.mkₐ A N).comp φ = q := by
    ext i
    simpa only [φ, q, AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hx i
  let ψ : Lifts N q := ⟨MvPolynomial.aeval (fun i => x i + (t i : C)), by
    ext i
    simp only [q, AlgHom.comp_apply, MvPolynomial.aeval_X]
    change Ideal.Quotient.mk N (x i + (t i : C)) = u (P.val i)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (t i).property, add_zero, hx]⟩
  letI := idealModule N hN q
  letI := idealTower N hN q
  let D := AdvCommAlg.Differentials.differenceDerivation N hN q φ hφ ψ
  have hDX (i : Fin n) : D (MvPolynomial.X i) = t i := by
    apply Subtype.ext
    change MvPolynomial.aeval (fun i => x i + (t i : C)) (MvPolynomial.X i) -
      MvPolynomial.aeval x (MvPolynomial.X i) = (t i : C)
    simp
  have hD : D f = ∑ i : Fin n,
      MvPolynomial.aeval P.val (MvPolynomial.pderiv i f) • t i := by
    rw [derivation_expansion D f]
    apply Finset.sum_congr rfl
    intro i _
    rw [hDX]
    rfl
  have H : (D f : C) = MvPolynomial.aeval (fun i => x i + (t i : C)) f -
      MvPolynomial.aeval x f := rfl
  rw [hD] at H
  exact (sub_eq_iff_eq_add.mp H.symm).trans (add_comm _ _)

/-- Relations vanish exactly when the corrected evaluation factors through
this presentation; the factor automatically has the specified reduction. -/
lemma corrected_factorization (n m : ℕ)
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (N : Ideal C) (u : B →ₐ[A] C ⧸ N) (x : Fin n → C)
    (hx : ∀ i, Ideal.Quotient.mk N (x i) = u (P.val i)) (t : Fin n → N) :
    (∃ g : Lifts N u, ∀ i, g.1 (P.val i) = x i + (t i : C)) ↔
      ∀ j, MvPolynomial.aeval (fun i => x i + (t i : C)) (P.relation j) = 0 := by
  let ev := MvPolynomial.aeval (R := A) (fun i => x i + (t i : C))
  constructor
  · rintro ⟨g, hg⟩ j
    have H : g.1.comp (MvPolynomial.aeval P.val) = ev := by
      ext i
      simpa only [ev, AlgHom.comp_apply, MvPolynomial.aeval_X] using hg i
    change ev (P.relation j) = 0
    rw [← H, AlgHom.comp_apply, P.aeval_val_relation, map_zero]
  · intro hrel
    have hk : RingHom.ker (MvPolynomial.aeval P.val).toRingHom ≤ RingHom.ker ev.toRingHom := by
      have heq : RingHom.ker (MvPolynomial.aeval P.val).toRingHom = P.ker := by
        ext f
        simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
          (SetLike.ext_iff.mp P.ker_eq_ker_aeval_val f).symm
      rw [heq, ← P.span_range_relation_eq_ker]
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hrel j
    let g := AlgHom.liftOfSurjective (MvPolynomial.aeval P.val) P.aeval_val_surjective ev hk
    have hg : g.comp (MvPolynomial.aeval P.val) = ev := AlgHom.liftOfSurjective_comp ..
    have hred : (Ideal.Quotient.mkₐ A N).comp g = u := by
      apply (AlgHom.cancel_right P.aeval_val_surjective).mp
      rw [AlgHom.comp_assoc, hg]
      ext i
      simp only [ev, AlgHom.comp_apply, MvPolynomial.aeval_X]
      change Ideal.Quotient.mk N (x i + (t i : C)) = u (P.val i)
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (t i).property, add_zero, hx]
    refine ⟨⟨g, hred⟩, ?_⟩
    intro i
    have H := congrArg (fun k : MvPolynomial (Fin n) A →ₐ[A] C => k (MvPolynomial.X i)) hg
    simpa only [ev, AlgHom.comp_apply, MvPolynomial.aeval_X] using H

theorem finite_lifting_equation : finiteLiftingEquation := by
  intro A B C _ _ _ _ _ n m P N hN u x hx
  letI := idealModule N hN u
  intro t
  rw [corrected_factorization n m P N u x hx t]
  apply forall_congr'
  intro j
  rw [polynomial_correction n m P N hN u x hx t (P.relation j)]
  exact add_eq_zero_iff_eq_neg'

theorem finite_solvability : finiteSolvability := by
  intro A B C _ _ _ _ _ n m P N hN u x hx
  letI := idealModule N hN u
  have hred : (Ideal.Quotient.mkₐ A N).comp (MvPolynomial.aeval x) =
      u.comp (MvPolynomial.aeval P.val) := by
    ext i
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hx i
  constructor
  · intro j
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have H := congrArg (fun k : MvPolynomial (Fin n) A →ₐ[A] C ⧸ N => k (P.relation j)) hred
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, P.aeval_val_relation, map_zero] using H
  · constructor
    · rintro ⟨g⟩
      have hmem (i : Fin n) : g.1 (P.val i) - x i ∈ N := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have H := congrArg (fun k : B →ₐ[A] C ⧸ N => k (P.val i)) g.2
        have H' : Ideal.Quotient.mk N (g.1 (P.val i)) = u (P.val i) := H
        rw [map_sub, H', hx, sub_self]
      let t : Fin n → N := fun i => ⟨g.1 (P.val i) - x i, hmem i⟩
      refine ⟨t, (finite_lifting_equation n m P N hN u x hx t).mp ⟨g, ?_⟩⟩
      intro i
      change g.1 (P.val i) = x i + (g.1 (P.val i) - x i)
      abel
    · rintro ⟨t, ht⟩
      obtain ⟨g, _⟩ := (finite_lifting_equation n m P N hN u x hx t).mpr ht
      exact ⟨g⟩

end Finite

end
end AdvCommAlg.FormalLifting.Obstruction
