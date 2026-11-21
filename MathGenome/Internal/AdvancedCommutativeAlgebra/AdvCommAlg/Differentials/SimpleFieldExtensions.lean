import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Hypersurfaces
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.SimpleFieldExtensions

namespace AdvCommAlg.Differentials
universe u v
noncomputable section
open Specs.AdvCommAlg.Differentials
set_option backward.isDefEq.respectTransparency false

/-- Transport the single polynomial relation to any isomorphic algebra. -/
lemma presentation_of_adjoinRoot_equiv {K : Type u} {L : Type v}
    [CommRing K] [CommRing L] [Algebra K L] (f : Polynomial K)
    (e : AdjoinRoot f ≃ₐ[K] L) :
    ∃ q : (L ⧸ Ideal.span {e (AdjoinRoot.mk f f.derivative)}) ≃ₗ[L]
        KaehlerDifferential K L,
      ∀ b : L, q (Ideal.Quotient.mk _ b) =
        b • KaehlerDifferential.D K L (e (AdjoinRoot.root f)) := by
  let P := (univariatePresentation K f).ofAlgEquiv e
  have hv (i : Fin 1) : P.val i = e (AdjoinRoot.root f) := by
    simp [P, Algebra.Generators.ofAlgEquiv_val, univariatePresentation_val]
  have hm : presentationJacobian P =
      fun (_ : Fin 1) (_ : Fin 1) => e (AdjoinRoot.mk f f.derivative) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change MvPolynomial.aeval P.val
      (MvPolynomial.pderiv 0 ((MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm f)) = _
    rw [singleton_pderiv]
    have he : MvPolynomial.aeval P.val =
        e.toAlgHom.comp ((AdjoinRoot.mkₐ f).comp
          (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toAlgHom) := by
      ext i
      simp [hv, MvPolynomial.uniqueAlgEquiv, AdjoinRoot.mk_X]
    rw [he]
    change e (AdjoinRoot.mk f ((MvPolynomial.uniqueAlgEquiv K (Fin 1))
      ((MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm f.derivative))) = _
    rw [AlgEquiv.apply_symm_apply]
  let c : (Fin 1 → L) ≃ₗ[L] L := LinearEquiv.funUnique (Fin 1) L L
  let I : Submodule L L := Ideal.span {e (AdjoinRoot.mk f f.derivative)}
  have hr : (LinearMap.range (jacobianRelationMap P)).map c.toLinearMap = I := by
    rw [jacobianRelationMap, hm, range_one_column,
      Submodule.map_span, Set.image_singleton]
    exact Ideal.submodule_span_eq
  let ec := Submodule.Quotient.equiv _ I c hr
  obtain ⟨q, hq, _⟩ := jacobian_cokernel K L 1 1 P
  refine ⟨ec.symm.trans q, ?_⟩
  intro b
  change q ((LinearMap.range (jacobianRelationMap P)).mkQ (fun _ => b)) = _
  rw [hq]
  have hx : (fun _ : Fin 1 => b) = b • (Pi.single 0 1 : Fin 1 → L) := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [hx, map_smul, jacobian_variables, hv]

/-- The algebraic simple extension is the literal minimal-polynomial quotient. -/
def simpleFieldEquiv {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (α : L) (hint : IsIntegral K α) (hgen : Algebra.adjoin K {α} = ⊤) :
    AdjoinRoot (minpoly K α) ≃ₐ[K] L :=
  (minpoly.equivAdjoin hint).trans
    ((Subalgebra.equivOfEq _ _ hgen).trans Subalgebra.topEquiv)

lemma simpleFieldEquiv_root {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (α : L) (hint : IsIntegral K α)
    (hgen : Algebra.adjoin K {α} = ⊤) :
    simpleFieldEquiv α hint hgen (AdjoinRoot.root (minpoly K α)) = α := by
  simp [simpleFieldEquiv, minpoly.equivAdjoin, AdjoinRoot.Minpoly.toAdjoin,
    AdjoinRoot.liftAlgHom_root]

theorem simple_field_presentation : simpleFieldPresentation.{u,v} := by
  intro K L _ _ _ α hint hgen
  let e := simpleFieldEquiv α hint hgen
  have he : e (AdjoinRoot.root (minpoly K α)) = α :=
    simpleFieldEquiv_root α hint hgen
  have hd : e (AdjoinRoot.mk (minpoly K α) (minpoly K α).derivative) =
      Polynomial.aeval α (minpoly K α).derivative := by
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, he]
  have H := presentation_of_adjoinRoot_equiv (minpoly K α) e
  rw [hd, he] at H
  exact H


theorem simple_separable_vanishing : simpleSeparableVanishing.{u,v} := by
  intro K L _ _ _ α hint hgen hsep
  obtain ⟨q, _⟩ := simple_field_presentation K L α hint hgen
  have hd : Polynomial.aeval α (minpoly K α).derivative ≠ 0 :=
    hsep.aeval_derivative_ne_zero (minpoly.aeval K α)
  have hi : Ideal.span {Polynomial.aeval α (minpoly K α).derivative} = ⊤ :=
    Ideal.span_singleton_eq_top.mpr (isUnit_iff_ne_zero.mpr hd)
  haveI : Subsingleton (L ⧸ Ideal.span {Polynomial.aeval α (minpoly K α).derivative}) :=
    Submodule.Quotient.subsingleton_iff.mpr hi
  exact ⟨fun x y => q.symm.injective (Subsingleton.elim _ _)⟩

theorem purely_inseparable_basis : purelyInseparableBasis.{u,v} := by
  intro K L _ _ _ p _ _ a hirr α hroot hgen
  let f : Polynomial K := Polynomial.X ^ p - Polynomial.C a
  have hp : p.Prime := Fact.out
  have hm : f.Monic := Polynomial.monic_X_pow_sub_C a hp.ne_zero
  have hr : Polynomial.aeval α f = 0 := by
    simp [f, hroot]
  have hint : IsIntegral K α := ⟨f, hm, hr⟩
  have hf : f = minpoly K α := minpoly.eq_of_irreducible_of_monic hirr hr hm
  have hd : f.derivative = 0 := by
    simp [f, Polynomial.derivative_X_pow]
  have hi : (Ideal.span {Polynomial.aeval α (minpoly K α).derivative} : Ideal L) = ⊥ := by
    rw [← hf, hd, map_zero]
    simp
  obtain ⟨q, hq⟩ := simple_field_presentation K L α hint hgen
  let c : L ≃ₗ[L] KaehlerDifferential K L :=
    ((Ideal.span {Polynomial.aeval α (minpoly K α).derivative} : Ideal L).quotEquivOfEqBot hi).symm.trans q
  refine ⟨(Module.Basis.singleton Unit L).map c, ?_⟩
  change c ((Module.Basis.singleton Unit L) ()) = _
  rw [Module.Basis.singleton_apply]
  change q (Ideal.Quotient.mk _ 1) = _
  simpa using hq 1

theorem purely_inseparable_adjoin_root : purelyInseparableAdjoinRoot.{u} := by
  intro K _ p _ _ a _
  let f : Polynomial K := Polynomial.X ^ p - Polynomial.C a
  have hr : (AdjoinRoot.root f) ^ p = algebraMap K (AdjoinRoot f) a := by
    have h := AdjoinRoot.eval₂_root f
    simpa [f, sub_eq_zero] using h
  obtain ⟨b, hb⟩ := purely_inseparable_basis K (AdjoinRoot f) p a Fact.out
    (AdjoinRoot.root f) hr (AdjoinRoot.adjoinRoot_eq_top (f := f))
  exact ⟨⟨b, hb⟩, by simpa using Module.finrank_eq_card_basis b⟩

end
end AdvCommAlg.Differentials
