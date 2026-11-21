import MathGenome.Internal.Specs.D07.Ch16.FinitePresentationFiniteRelationsCounterexample
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The infinite-variable counterexample in paper.tex:3101–3122. -/

universe u

noncomputable section

namespace D07.Ch16.FinitePresentationFiniteRelationsCounterexample

open MvPolynomial
open Specs.D07.Ch16.FinitePresentationFiniteRelationsCounterexample

theorem finitePresentationCriterion : FinitePresentationCriterion.{u} := by
  intro R _ I
  constructor
  · intro h
    let := h
    obtain ⟨n, m, π, A, hπ, hA⟩ := Module.FinitePresentation.exists_fin' R (R ⧸ I)
    refine ⟨n, π, hπ, ?_⟩
    rw [LinearMap.exact_iff.mp hA]
    exact Submodule.fg_range A
  · rintro ⟨n, π, hπ, hker⟩
    exact Module.finitePresentation_of_free_of_surjective π hπ hker

/-- The kernel theorem applies to the natural quotient map R → R/I;
the source R is finite as a module over itself. It does not require a
Noetherian hypothesis, nor a specified choice of presentation of R/I. -/
theorem presentationIndependence : PresentationIndependence.{u} := by
  intro R _ I h
  let := h
  have hker := Module.FinitePresentation.fg_ker I.mkQ I.mkQ_surjective
  rwa [Submodule.ker_mkQ] at hker

theorem everyPresentation : EveryPresentation.{u} := by
  intro R _ I n π hπ hker
  exact presentationIndependence R I
    ((finitePresentationCriterion R I).mpr ⟨n, π, hπ, hker⟩)

/-- Subtracting the constant term leaves an element of the variables ideal. -/
theorem sub_constantCoeff_mem (k : Type u) [CommRing k] (p : PolynomialRing k) :
    p - C (constantCoeff p) ∈ variablesIdeal k := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simpa only [map_add, add_sub_add_comm] using (variablesIdeal k).add_mem hp hq
  | mul_X p i hp =>
      simp only [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
      exact (variablesIdeal k).mul_mem_left p (Ideal.subset_span ⟨i, rfl⟩)

theorem variablesIdeal_eq_ker (k : Type u) [CommRing k] :
    variablesIdeal k = RingHom.ker (constantCoeff : PolynomialRing k →+* k) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp
  · intro p hp
    have hp0 : constantCoeff p = 0 := hp
    simpa only [hp0, map_zero, sub_zero] using sub_constantCoeff_mem k p

theorem idealNotFinitelyGenerated : IdealNotFinitelyGenerated.{u} := by
  classical
  intro k _ hfg
  obtain ⟨s, hs⟩ := hfg
  let t : Finset ℕ := s.biUnion MvPolynomial.vars
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset t
  let f : PolynomialRing k →+* Polynomial k :=
    eval₂Hom Polynomial.C (fun i => if i = j then Polynomial.X else 0)
  have hzero : ∀ p ∈ s, f p = 0 := by
    intro p hp
    have hmem : p ∈ variablesIdeal k := hs ▸ Submodule.subset_span hp
    have hp0 : constantCoeff p = 0 := by
      rw [variablesIdeal_eq_ker] at hmem
      exact hmem
    change eval₂Hom Polynomial.C _ p = 0
    rw [eval₂Hom_eq_constantCoeff_of_vars Polynomial.C (fun i hi => ?_), hp0, map_zero]
    have hij : i ≠ j := by
      intro hij
      apply hj
      exact Finset.mem_biUnion.mpr ⟨p, hp, hij ▸ hi⟩
    simp [hij]
  have hle : variablesIdeal k ≤ RingHom.ker f := by
    rw [← hs]
    exact Submodule.span_le.mpr hzero
  have hx : X j ∈ variablesIdeal k := Ideal.subset_span ⟨j, rfl⟩
  have hfx : f (X j) = 0 := hle hx
  simp [f] at hfx

theorem residueCyclic : ResidueCyclic.{u} := by
  intro k _
  exact Ideal.Quotient.span_singleton_one (variablesIdeal k)

theorem residueAlgebra : ResidueAlgebra.{u} := by
  intro k _
  let f : PolynomialRing k →ₐ[k] k :=
    { (constantCoeff : PolynomialRing k →+* k) with
      commutes' := fun a => constantCoeff_C ℕ a }
  have hf : Function.Surjective f := fun a => ⟨C a, constantCoeff_C ℕ a⟩
  have hker : variablesIdeal k = RingHom.ker f := variablesIdeal_eq_ker k
  let e : (PolynomialRing k ⧸ variablesIdeal k) ≃ₐ[k] k :=
    (Ideal.quotientEquivAlgOfEq k hker).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  have he (p : PolynomialRing k) :
      e (Ideal.Quotient.mk (variablesIdeal k) p) = constantCoeff p := by
    change (Ideal.quotientKerAlgEquivOfSurjective hf)
      ((Ideal.quotientEquivAlgOfEq k hker)
        (Ideal.Quotient.mk (variablesIdeal k) p)) = _
    rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
    rfl
  refine ⟨e, he, ?_⟩
  intro a
  apply e.injective
  rw [e.apply_symm_apply, he, constantCoeff_C]

theorem residueNotFinitelyPresented : ResidueNotFinitelyPresented.{u} := by
  intro k _ h
  exact idealNotFinitelyGenerated k (presentationIndependence _ _ h)

end D07.Ch16.FinitePresentationFiniteRelationsCounterexample
