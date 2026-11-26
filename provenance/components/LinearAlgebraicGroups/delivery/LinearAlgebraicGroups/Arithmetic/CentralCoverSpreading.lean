import Specs.LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

open scoped TensorProduct
open Algebra.TensorProduct WithConv

universe u

namespace LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading

open Specs.CentralCoverSpreading

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section Denominators

variable {A E X : Type u} [CommRing A] [IsDomain A] [Field E] [Algebra A E]
  [IsFractionRing A E] [CommRing X] [Algebra A X] [Algebra E X] [IsScalarTower A E X]

/-- A finite collection of denominators can be inverted by inverting their product. -/
private theorem exists_common_multiple {J : Type*} [Finite J] (d : J → A)
    (hd : ∀ j, d j ≠ 0) :
    ∃ a : A, a ≠ 0 ∧ ∀ j, d j ∣ a := by
  classical
  letI := Fintype.ofFinite J
  exact ⟨∏ j, d j, Finset.prod_ne_zero_iff.mpr fun j _ => hd j,
    fun j => Finset.dvd_prod_of_mem d (Finset.mem_univ j)⟩

/-- If adjoining the same generators over the fraction field gives the whole
algebra, every element is an integral element of the smaller generated algebra
after multiplication by one nonzero scalar. -/
private theorem exists_smul_mem_adjoin (s : Set X) (hs : Algebra.adjoin E s = ⊤) (x : X) :
    ∃ a : A, a ≠ 0 ∧ a • x ∈ Algebra.adjoin A s := by
  obtain ⟨a, ha⟩ := multiple_mem_adjoin_of_mem_localization_adjoin
    (nonZeroDivisors A) E s x (by rw [hs]; trivial)
  exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp a.property, ha⟩

/-- A product denominator controls membership of a finite set in a generated
algebra over every intervening coefficient ring where it becomes a unit. -/
private theorem finite_mem_adjoin_after_localization (s : Set X) (hs : Algebra.adjoin E s = ⊤)
    {J : Type*} [Finite J] (x : J → X) :
    ∃ a : A, a ≠ 0 ∧ ∀ (R : Type u) [CommRing R]
      [Algebra A R] [Algebra R X] [IsScalarTower A R X],
      IsUnit (algebraMap A R a) → ∀ j, x j ∈ Algebra.adjoin R s := by
  classical
  choose d hd hdx using fun j => exists_smul_mem_adjoin (A := A) s hs (x j)
  obtain ⟨a, ha, hdiv⟩ := exists_common_multiple d hd
  refine ⟨a, ha, fun R _ _ _ _ hu j => ?_⟩
  let S := Algebra.adjoin R s
  have hds : d j • x j ∈ S :=
    (Algebra.adjoin_le (S := S.restrictScalars A) (Algebra.subset_adjoin (R := R))) (hdx j)
  have hunit : IsUnit (algebraMap A R (d j)) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A R) (hdiv j)) hu
  obtain ⟨v, hv⟩ := hunit
  have hx : (↑v⁻¹ : R) • (d j • x j) ∈ S := S.smul_mem hds _
  rwa [← algebraMap_smul R (d j) (x j), ← hv, smul_smul, Units.inv_mul, one_smul] at hx

/-- Extension from a generating set over the scalar subring to the fraction
field, including the injectivity needed to identify the actual model. -/
private theorem adjoin_isBaseChange (s : Set X) (hs : Algebra.adjoin E s = ⊤) :
    IsBaseChange E (Algebra.adjoin A s).val.toLinearMap := by
  let S := Algebra.adjoin A s
  have hloc : IsLocalizedModule (nonZeroDivisors A) S.val.toLinearMap := by
    constructor
    · intro a
      rw [Module.End.isUnit_iff]
      let e := Units.mk0 (algebraMap A E a) (by
        exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp a.property)
          ((IsFractionRing.injective A E) (h.trans (map_zero _).symm)))
      have he (x : X) : (algebraMap A (Module.End A X) a) x = (e : E) • x := by
        change (a : A) • x = algebraMap A E a • x
        exact (algebraMap_smul E (a : A) x).symm
      have hinv (x : X) : (↑e⁻¹ : E) • ((algebraMap A (Module.End A X) a) x) = x := by
        rw [he, smul_smul, Units.inv_mul, one_smul]
      exact ⟨Function.LeftInverse.injective hinv, fun x =>
        ⟨(↑e⁻¹ : E) • x, by rw [he, smul_smul, Units.mul_inv, one_smul]⟩⟩
    · intro x
      obtain ⟨a, ha, hx⟩ := exists_smul_mem_adjoin (A := A) s hs x
      exact ⟨(⟨a • x, hx⟩, ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩), rfl⟩
    · intro x y h
      exact ⟨1, by simpa using Subtype.val_injective h⟩
  exact IsLocalizedModule.isBaseChange (nonZeroDivisors A) E S.val.toLinearMap

end Denominators

section Tensor

variable {R E : Type u} [CommRing R] [IsDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]

variable {B B' C C' : Type u} [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
  [Algebra R B] [Algebra R C] [Algebra R B'] [Algebra R C'] [Algebra E B'] [Algebra E C']
  [IsScalarTower R E B'] [IsScalarTower R E C']

omit [IsDomain R] [IsFractionRing R E] in
@[simp] private theorem tensorComparison_tmul (b : B →ₐ[R] B') (c : C →ₐ[R] C')
    (x : B) (y : C) : tensorComparison R E b c (x ⊗ₜ[R] y) = b x ⊗ₜ[E] c y := by
  simp [tensorComparison, lift_tmul, tmul_mul_tmul]

/-- For two algebras over a localization, the tensor products over the
original base and over the localization are canonically isomorphic. -/
private theorem tensorComparison_id_injective :
    Function.Injective (tensorComparison R E (AlgHom.id R B') (AlgHom.id R C')) := by
  let left : B' →ₐ[E] B' ⊗[R] C' := includeLeft
  let right : C' →ₐ[E] B' ⊗[R] C' :=
    { (includeRight : C' →ₐ[R] B' ⊗[R] C').toRingHom with
      commutes' := fun x => by
        have h :
            (includeRight : C' →ₐ[R] B' ⊗[R] C').toRingHom.comp (algebraMap E C') =
              algebraMap E (B' ⊗[R] C') := by
          apply IsLocalization.ringHom_ext (nonZeroDivisors R)
          ext r
          change (includeRight : C' →ₐ[R] B' ⊗[R] C') (algebraMap E C' (algebraMap R E r)) =
            algebraMap E (B' ⊗[R] C') (algebraMap R E r)
          rw [← IsScalarTower.algebraMap_apply R E C',
            ← IsScalarTower.algebraMap_apply R E (B' ⊗[R] C'), AlgHom.commutes]
        exact DFunLike.congr_fun h x }
  let back : B' ⊗[E] C' →ₐ[E] B' ⊗[R] C' := lift left right fun _ _ => Commute.all _ _
  have h : (back.restrictScalars R).comp
      (tensorComparison R E (AlgHom.id R B') (AlgHom.id R C')) = AlgHom.id R _ := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, tensorComparison_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply]
    change (lift left right (fun _ _ => Commute.all _ _)) (x ⊗ₜ[E] y) = _
    rw [lift_tmul]
    change (x ⊗ₜ[R] (1 : C')) * ((1 : B') ⊗ₜ[R] y) = _
    rw [tmul_mul_tmul, mul_one, one_mul]
  exact Function.LeftInverse.injective (DFunLike.congr_fun h)

/-- Tensor products of flat embedded models embed in the corresponding
generic tensor products. -/
private theorem tensorComparison_injective [Module.Flat R C] [Module.Flat R B']
    (b : B →ₐ[R] B') (c : C →ₐ[R] C')
    (hb : Function.Injective b) (hc : Function.Injective c) :
    Function.Injective (tensorComparison R E b c) := by
  have he : tensorComparison R E b c =
      (tensorComparison R E (AlgHom.id R B') (AlgHom.id R C')).comp (map b c) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp
  rw [he]
  exact tensorComparison_id_injective.comp
    (TensorProduct.map_injective_of_flat_flat b.toLinearMap c.toLinearMap hb hc)


omit [IsDomain R] [IsFractionRing R E] in
private theorem tensorComparison_natural
    {D D' F F' : Type u} [CommRing D] [CommRing D'] [CommRing F] [CommRing F']
    [Algebra R D] [Algebra R D'] [Algebra R F] [Algebra R F'] [Algebra E D'] [Algebra E F']
    [IsScalarTower R E D'] [IsScalarTower R E F']
    {b : B →ₐ[R] B'} {c : C →ₐ[R] C'} {d : D →ₐ[R] D'} {f : F →ₐ[R] F'}
    {g : B →ₐ[R] D} {h : C →ₐ[R] F} {g' : B' →ₐ[E] D'} {h' : C' →ₐ[E] F'}
    (hg : ∀ x, d (g x) = g' (b x)) (hh : ∀ y, f (h y) = h' (c y)) (x : B ⊗[R] C) :
    tensorComparison R E d f (map g h x) = map g' h' (tensorComparison R E b c x) := by
  have eq : (tensorComparison R E d f).comp (map g h) =
      ((map g' h').restrictScalars R).comp (tensorComparison R E b c) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [hg, hh]
  exact DFunLike.congr_fun eq x


end Tensor


section HopfRestriction

variable {R E U X : Type u} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [hFrac : IsFractionRing R E] [CommRing U] [Algebra R U] [CommRing X] [HopfAlgebra E X]
  [Algebra R X] [hTow : IsScalarTower R E X]

private structure RestrictedOperations (i : U →ₐ[R] X) where
  comul : U →ₐ[R] U ⊗[R] U
  counit : U →ₐ[R] R
  antipode : U →ₐ[R] U
  comul_agrees : ∀ x, tensorComparison R E i i (comul x) = Bialgebra.comulAlgHom E X (i x)
  counit_agrees : ∀ x, algebraMap R E (counit x) = Bialgebra.counitAlgHom E X (i x)
  antipode_agrees : ∀ x, i (antipode x) = HopfAlgebra.antipodeAlgHom E X (i x)

include hFrac hTow in
private theorem flat_of_injective_into_field_module (i : U →ₐ[R] X) (hi : Function.Injective i) :
    Module.Flat R U := by
  have : Module.IsTorsionFree R U := .of_smul_eq_zero fun a x hx => by
    have he := congrArg i hx
    rw [map_zero, map_smul, ← algebraMap_smul E a] at he
    rcases smul_eq_zero.mp he with ha | hx
    · exact Or.inl ((IsFractionRing.injective R E) (ha.trans (map_zero _).symm))
    · exact Or.inr (hi (hx.trans (map_zero i).symm))
  infer_instance

private theorem RestrictedOperations.coassoc {i : U →ₐ[R] X} (a : RestrictedOperations (E := E) i)
    (hi : Function.Injective i) :
      (Algebra.TensorProduct.assoc R R R U U U).toAlgHom.comp
        ((map a.comul (.id R U)).comp a.comul) =
      (map (.id R U) a.comul).comp a.comul := by
  letI : Module.Flat R U := flat_of_injective_into_field_module (E := E) i hi
  letI : Module.Flat R E := IsLocalization.flat E (nonZeroDivisors R)
  letI : Module.Flat R X := Module.Flat.trans R E X
  letI : Module.Flat R (X ⊗[E] X) := Module.Flat.trans R E _
  let t := tensorComparison R E i i
  have ht : Function.Injective t := tensorComparison_injective (E := E) i i hi hi
  ext x
  apply tensorComparison_injective (E := E) i t hi ht
  have hassoc (z : (U ⊗[R] U) ⊗[R] U) :
      tensorComparison R E i t (Algebra.TensorProduct.assoc R R R U U U z) =
      Algebra.TensorProduct.assoc E E E X X X (tensorComparison R E t i z) := by
    have eq : (tensorComparison R E i t).comp (Algebra.TensorProduct.assoc R R R U U U).toAlgHom =
        ((Algebra.TensorProduct.assoc E E E X X X).toAlgHom.restrictScalars R).comp
          (tensorComparison R E t i) := by
      apply Algebra.TensorProduct.ext'
      intro y z
      induction y with
      | tmul w y => simp [t]
      | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
    exact DFunLike.congr_fun eq z
  change tensorComparison R E i t (Algebra.TensorProduct.assoc R R R U U U
    (map a.comul (.id R U) (a.comul x))) = tensorComparison R E i t
      (map (.id R U) a.comul (a.comul x))
  rw [hassoc, tensorComparison_natural (E := E) (b := i) (c := i) (d := t) (f := i)
      (h' := AlgHom.id E X) a.comul_agrees (fun _ => rfl),
    tensorComparison_natural (E := E) (b := i) (c := i) (d := i) (f := t)
      (g' := AlgHom.id E X) (fun _ => rfl) a.comul_agrees, a.comul_agrees]
  exact Coalgebra.coassoc_apply (R := E) (i x)

private theorem RestrictedOperations.counitLaws {i : U →ₐ[R] X} (a : RestrictedOperations (E := E) i)
    (hi : Function.Injective i) :
    ((map a.counit (.id R U)).comp a.comul = (Algebra.TensorProduct.lid R U).symm) ∧
    ((map (.id R U) a.counit).comp a.comul = (Algebra.TensorProduct.rid R R U).symm) := by
  letI : Module.Flat R U := flat_of_injective_into_field_module (E := E) i hi
  letI : Module.Flat R E := IsLocalization.flat E (nonZeroDivisors R)
  letI : Module.Flat R X := Module.Flat.trans R E X
  let f := Algebra.ofId R E
  have hf : Function.Injective f := IsFractionRing.injective R E
  constructor
  · ext x
    apply tensorComparison_injective (E := E) f i hf hi
    change tensorComparison R E f i (map a.counit (.id R U) (a.comul x)) =
      tensorComparison R E f i (1 ⊗ₜ[R] x)
    rw [tensorComparison_natural (E := E) (b := i) (c := i) (d := f) (f := i)
        (g' := Bialgebra.counitAlgHom E X) (h' := AlgHom.id E X) a.counit_agrees (fun _ => rfl), a.comul_agrees,
      tensorComparison_tmul, map_one]
    exact Coalgebra.rTensor_counit_comul (R := E) (i x)
  · ext x
    apply tensorComparison_injective (E := E) i f hi hf
    change tensorComparison R E i f (map (.id R U) a.counit (a.comul x)) =
      tensorComparison R E i f (x ⊗ₜ[R] 1)
    rw [tensorComparison_natural (E := E) (b := i) (c := i) (d := i) (f := f)
        (g' := AlgHom.id E X) (h' := Bialgebra.counitAlgHom E X) (fun _ => rfl) a.counit_agrees, a.comul_agrees,
      tensorComparison_tmul, map_one]
    exact Coalgebra.lTensor_counit_comul (R := E) (i x)

private abbrev RestrictedOperations.bialgebra {i : U →ₐ[R] X} (a : RestrictedOperations (E := E) i)
    (hi : Function.Injective i) : Bialgebra R U :=
  Bialgebra.ofAlgHom a.comul a.counit (a.coassoc hi) (a.counitLaws hi).1 (a.counitLaws hi).2

private abbrev RestrictedOperations.hopfAlgebra {i : U →ₐ[R] X} (a : RestrictedOperations (E := E) i)
    (hi : Function.Injective i) : HopfAlgebra R U := by
  letI := a.bialgebra hi
  have compare {f g : U →ₐ[R] U} {f' g' : X →ₐ[E] X}
      (hf : ∀ x, i (f x) = f' (i x)) (hg : ∀ x, i (g x) = g' (i x)) (z : U ⊗[R] U) :
      i (lift f g (fun _ _ => Commute.all _ _) z) =
        lift f' g' (fun _ _ => Commute.all _ _) (tensorComparison R E i i z) := by
    have eq : i.comp (lift f g (fun _ _ => Commute.all _ _)) =
        ((lift f' g' (fun _ _ => Commute.all _ _)).restrictScalars R).comp
          (tensorComparison R E i i) := by
      apply Algebra.TensorProduct.ext'
      intro x y
      simp [hf, hg, lift_tmul]
    exact DFunLike.congr_fun eq z
  refine HopfAlgebra.ofAlgHom a.antipode ?_ ?_
  · ext x
    apply hi
    change i (lift a.antipode (.id R U) (fun _ _ => Commute.all _ _) (a.comul x)) =
      i (algebraMap R U (a.counit x))
    rw [compare (g' := AlgHom.id E X) a.antipode_agrees (fun _ => rfl), a.comul_agrees, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R E X, a.counit_agrees, ← lmul'_comp_map]
    exact DFunLike.congr_fun (congrArg WithConv.ofConv
      (AlgHom.antipode_id_cancel (R := E) (A := X))) (i x)
  · ext x
    apply hi
    change i (lift (.id R U) a.antipode (fun _ _ => Commute.all _ _) (a.comul x)) =
      i (algebraMap R U (a.counit x))
    rw [compare (f' := AlgHom.id E X) (fun _ => rfl) a.antipode_agrees, a.comul_agrees, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R E X, a.counit_agrees, ← lmul'_comp_map]
    exact DFunLike.congr_fun (congrArg WithConv.ofConv
      (AlgHom.id_antipode_cancel (R := E) (A := X))) (i x)


/-- The three structure maps restrict as soon as they restrict on the chosen
algebra generators. -/
private def restrictOperations (s : Set X)
    (hcomul : ∀ x ∈ s, Bialgebra.comulAlgHom E X x ∈
      (tensorComparison R E (Algebra.adjoin R s).val (Algebra.adjoin R s).val).range)
    (hcounit : ∀ x ∈ s, Bialgebra.counitAlgHom E X x ∈ (Algebra.ofId R E).range)
    (hantipode : ∀ x ∈ s, HopfAlgebra.antipodeAlgHom E X x ∈ Algebra.adjoin R s) :
    RestrictedOperations (E := E) (Algebra.adjoin R s).val := by
  let U := Algebra.adjoin R s
  let i := U.val
  let f := tensorComparison R E i i
  let g := Algebra.ofId R E
  let Δ := (Bialgebra.comulAlgHom E X).restrictScalars R
  let ε := (Bialgebra.counitAlgHom E X).restrictScalars R
  let S := (HopfAlgebra.antipodeAlgHom E X).restrictScalars R
  letI : Module.Flat R U := flat_of_injective_into_field_module (E := E) i Subtype.val_injective
  letI : Module.Flat R E := IsLocalization.flat E (nonZeroDivisors R)
  letI : Module.Flat R X := Module.Flat.trans R E X
  let fIso := AlgEquiv.ofInjective f
    (tensorComparison_injective (E := E) i i Subtype.val_injective Subtype.val_injective)
  let gIso := AlgEquiv.ofInjective g (IsFractionRing.injective R E)
  have hΔ : U ≤ f.range.comap Δ := Algebra.adjoin_le hcomul
  have hε : U ≤ g.range.comap ε := Algebra.adjoin_le hcounit
  have hS : U ≤ U.comap S := Algebra.adjoin_le hantipode
  refine ⟨fIso.symm.toAlgHom.comp ((Δ.comp i).codRestrict f.range fun x => hΔ x.property),
    gIso.symm.toAlgHom.comp ((ε.comp i).codRestrict g.range fun x => hε x.property),
    (S.comp i).codRestrict U (fun x => hS x.property), ?_, ?_, ?_⟩
  · intro x
    change ((fIso (fIso.symm ⟨Δ (i x), _⟩)) : X ⊗[E] X) = Δ (i x)
    rw [AlgEquiv.apply_symm_apply]
  · intro x
    change ((gIso (gIso.symm ⟨ε (i x), _⟩)) : E) = ε (i x)
    rw [AlgEquiv.apply_symm_apply]
  · intro x
    rfl


end HopfRestriction



section TensorFactors

variable {E X Y : Type u} [Field E] [CommRing X] [CommRing Y] [Algebra E X] [Algebra E Y]

/-- Each element in a tensor product has finite support in the two algebras.
Every pair of subalgebras containing those elements carries an integral
preimage of the tensor. -/
private theorem exists_tensor_factors (z : X ⊗[E] Y) :
    ∃ (s : Finset X) (t : Finset Y), ∀ (R : Type u) [CommRing R] [Algebra R E]
      [Algebra R X] [Algebra R Y] [IsScalarTower R E X] [IsScalarTower R E Y]
      (U : Subalgebra R X) (V : Subalgebra R Y), (s : Set X) ⊆ U → (t : Set Y) ⊆ V →
        z ∈ (tensorComparison R E U.val V.val).range := by
  classical
  induction z with
  | tmul x y =>
    refine ⟨{x}, {y}, fun R _ _ _ _ _ _ U V hs ht => ?_⟩
    exact ⟨(⟨x, hs (by simp)⟩ : U) ⊗ₜ[R] (⟨y, ht (by simp)⟩ : V), by simp⟩
  | add x y hx hy =>
    obtain ⟨sx, tx, hx⟩ := hx
    obtain ⟨sy, ty, hy⟩ := hy
    refine ⟨sx ∪ sy, tx ∪ ty, fun R _ _ _ _ _ _ U V hs ht => ?_⟩
    exact (tensorComparison R E U.val V.val).range.add_mem
      (hx R U V (fun _ hx => hs (Finset.mem_union_left _ hx))
        (fun _ hx => ht (Finset.mem_union_left _ hx)))
      (hy R U V (fun _ hy => hs (Finset.mem_union_right _ hy))
        (fun _ hy => ht (Finset.mem_union_right _ hy)))

end TensorFactors



section HopfDenominators

variable {A E X : Type u} [CommRing A] [IsDedekindDomain A] [Field E] [Algebra A E]
  [IsFractionRing A E] [CommRing X] [HopfAlgebra E X] [Algebra A X] [IsScalarTower A E X]

/-- A fixed finite set of fraction-field generators defines an affine group
model after inverting one denominator. Its operations are the restrictions
of the original ones, so the construction also works after further localization. -/
private theorem exists_hopf_denominator (s : Finset X) (hs : Algebra.adjoin E (s : Set X) = ⊤) :
    ∃ a : A, a ≠ 0 ∧ ∀ (R : Type u) [CommRing R] [IsDedekindDomain R]
      [Algebra A R] [Algebra R E] [IsFractionRing R E] [IsScalarTower A R E]
      [Algebra R X] [IsScalarTower A R X] [IsScalarTower R E X],
      IsUnit (algebraMap A R a) →
      Nonempty (RestrictedOperations (E := E) (Algebra.adjoin R (s : Set X)).val) := by
  classical
  choose L P hLP using fun x : s => exists_tensor_factors (Bialgebra.comulAlgHom E X x)
  let t : Finset X := Finset.univ.biUnion (fun x : s =>
    L x ∪ P x ∪ {HopfAlgebra.antipodeAlgHom E X x})
  obtain ⟨a, ha, hA⟩ := finite_mem_adjoin_after_localization (A := A) (s : Set X) hs
    (fun x : t => (x : X))
  have hE : Algebra.adjoin E (∅ : Set E) = ⊤ := by
    apply top_unique
    intro x _
    exact (Algebra.adjoin E (∅ : Set E)).algebraMap_mem x
  obtain ⟨b, hb, hB⟩ := finite_mem_adjoin_after_localization (A := A) (∅ : Set E) hE
    (fun x : s => Bialgebra.counitAlgHom E X x)
  refine ⟨a * b, mul_ne_zero ha hb, fun R _ _ _ _ _ _ _ _ _ hu => ?_⟩
  have hau := isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_right a b)) hu
  have hbu := isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_left b a)) hu
  have hmem (x : s) {y : X} (hy : y ∈ L x ∪ P x ∪ {HopfAlgebra.antipodeAlgHom E X x}) :
      y ∈ Algebra.adjoin R (s : Set X) :=
    hA R hau ⟨y, Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hy⟩⟩
  refine ⟨restrictOperations (R := R) (s : Set X) ?_ ?_ ?_⟩
  · intro x hx
    let w : s := ⟨x, hx⟩
    exact hLP w R _ _ (fun _ hy => hmem w (Finset.mem_union_left _
      (Finset.mem_union_left _ hy))) (fun _ hy => hmem w (Finset.mem_union_left _
      (Finset.mem_union_right _ hy)))
  · intro x hx
    have H := hB R hbu ⟨x, hx⟩
    change Bialgebra.counitAlgHom E X x ∈ Algebra.adjoin R (∅ : Set E) at H
    rw [Algebra.adjoin_empty] at H
    exact Algebra.mem_bot.mp H
  · intro x hx
    exact hmem ⟨x, hx⟩ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

end HopfDenominators

section PrincipalLocalization

variable {A E : Type u} [CommRing A] [IsDedekindDomain A] [Field E] [Algebra A E]
  [IsFractionRing A E]

private theorem denominator_isUnit (d : A) (hd : d ≠ 0) :
    IsUnit (algebraMap A E d) :=
  IsUnit.mk0 _ <| fun hz => hd ((IsFractionRing.injective A E) (hz.trans (map_zero _).symm))

private def localizationMap (d : A) (hd : d ≠ 0) : Localization.Away d →+* E :=
  IsLocalization.Away.lift d (denominator_isUnit (E := E) d hd)

private theorem localization_tower (d : A) (hd : d ≠ 0) :
    letI := (localizationMap (E := E) d hd).toAlgebra
    IsScalarTower A (Localization.Away d) E := by
  letI := (localizationMap (E := E) d hd).toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    (IsLocalization.Away.lift_comp d (S := Localization.Away d)
      (denominator_isUnit (E := E) d hd)).symm

private theorem localization_fractionRing (d : A) (hd : d ≠ 0) :
    letI := (localizationMap (E := E) d hd).toAlgebra
    IsFractionRing (Localization.Away d) E := by
  let R := Localization.Away d
  letI : IsDomain R := Localization.Away.isDomain hd
  letI : Algebra R E := (localizationMap (E := E) d hd).toAlgebra
  letI : IsScalarTower A R E := localization_tower (E := E) d hd
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers d) R E

private theorem localization_dedekind (d : A) (hd : d ≠ 0) :
    IsDedekindDomain (Localization.Away d) := by
  letI : IsDomain (Localization.Away d) := Localization.Away.isDomain hd
  apply IsLocalization.isDedekindDomain A (M := Submonoid.powers d) _ (Localization.Away d)
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd)

end PrincipalLocalization



section Ambient

variable {A R D X : Type u} [CommRing A] [CommRing R] [CommRing D] [CommRing X]
  [Algebra A R] [Algebra A D] [Algebra A X] [Algebra R X] [IsScalarTower A R X]

private def extendAmbientMap (f : D →ₐ[A] X) : R ⊗[A] D →ₐ[R] X :=
  lift (Algebra.ofId R X) f fun _ _ => Commute.all _ _

@[simp] private theorem extendAmbientMap_tmul (f : D →ₐ[A] X) (r : R) (x : D) :
    extendAmbientMap f (r ⊗ₜ[A] x) = algebraMap R X r * f x := by
  rw [extendAmbientMap, lift_tmul]
  rfl

private theorem extendAmbientMap_range (f : D →ₐ[A] X) (s : Set D)
    (hs : Algebra.adjoin A s = ⊤) :
    (extendAmbientMap (R := R) f).range = Algebra.adjoin R (f '' s) := by
  let U := Algebra.adjoin R (f '' s)
  have hU : ∀ x : D, f x ∈ U := by
    have hle : Algebra.adjoin A s ≤ (U.restrictScalars A).comap f :=
      Algebra.adjoin_le fun x hx => Algebra.subset_adjoin ⟨x, hx, rfl⟩
    intro x
    apply hle
    rw [hs]
    trivial
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z with
    | tmul r x =>
      change extendAmbientMap f (r ⊗ₜ[A] x) ∈ U
      rw [extendAmbientMap_tmul]
      exact U.mul_mem (U.algebraMap_mem r) (hU x)
    | add x y hx hy =>
      rw [map_add]
      exact U.add_mem hx hy
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨1 ⊗ₜ[A] x, by simp⟩

/-- The closure in the specified ambient algebra is obtained by adjoining the
images of its given generators. Its coordinate map is surjective by construction. -/
private def ambientModelMap (f : D →ₐ[A] X) (s : Set D) (hs : Algebra.adjoin A s = ⊤) :
    R ⊗[A] D →ₐ[R] Algebra.adjoin R (f '' s) :=
  (extendAmbientMap f).codRestrict _ fun x => by
    rw [← extendAmbientMap_range f s hs]
    exact ⟨x, rfl⟩

private theorem ambientModelMap_surjective (f : D →ₐ[A] X) (s : Set D)
    (hs : Algebra.adjoin A s = ⊤) : Function.Surjective (ambientModelMap (R := R) f s hs) := by
  intro x
  have hx : (x : X) ∈ (extendAmbientMap (R := R) f).range :=
    (extendAmbientMap_range (R := R) f s hs).symm ▸ x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

end Ambient



section FaithfulFlatness

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

/-- A finite flat algebra over a Noetherian ring admits a finite dual family
for any spanning family. Faithfulness gives a linear functional taking one to one. -/
private theorem exists_dual_family_and_unit_section [IsNoetherianRing B]
    [Module.Finite B C] [Module.FaithfullyFlat B C]
    {J : Type*} [Fintype J] (x : J → C) (hx : Submodule.span B (Set.range x) = ⊤) :
    ∃ (f : J → C →ₗ[B] B) (p : C →ₗ[B] B),
      (∀ c, ∑ j, (f j c) • x j = c) ∧ p 1 = 1 := by
  classical
  letI : Module.FinitePresentation B C :=
    Module.finitePresentation_of_finite B C
  letI : Module.Projective B C := Module.Flat.projective_of_finitePresentation
  obtain ⟨k, hk⟩ := (Fintype.linearCombination B x).exists_rightInverse_of_surjective
    (by rw [Fintype.range_linearCombination, hx])
  let f (j : J) := (LinearMap.proj j).comp k
  have h (c : C) : ∑ j, (f j c) • x j = c := DFunLike.congr_fun hk c
  let I : Ideal B := Ideal.span (Set.range fun j => f j 1)
  have hI : I.map (algebraMap B C) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← h 1]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩))
  have hI' : I = ⊤ := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) I, hI, Ideal.comap_top]
  have hs : Submodule.span B (Set.range fun j => f j 1) = ⊤ := hI'
  obtain ⟨a, ha⟩ := ((span_range_eq_top_iff_surjective_fintypeLinearCombination B _).mp hs) (1 : B)
  refine ⟨f, ∑ j, a j • f j, h, ?_⟩
  simpa [Fintype.linearCombination, smul_eq_mul] using ha

/-- The dual family gives projectivity, and the unit section witnesses
faithful flatness since each test module injects into its base change. -/
private theorem faithfullyFlat_of_dual_family_and_unit_section
    {J : Type*} [Fintype J] (x : J → C) (f : J → C →ₗ[B] B)
    (h : ∀ c, ∑ j, (f j c) • x j = c) (p : C →ₗ[B] B) (hp : p 1 = 1) :
    Module.Finite B C ∧ Module.FaithfullyFlat B C := by
  let f' : C →ₗ[B] (J → B) := LinearMap.pi f
  let g := Fintype.linearCombination B x
  have hfg : g.comp f' = LinearMap.id := LinearMap.ext h
  have hg : Function.Surjective g := fun c => ⟨f' c, h c⟩
  refine ⟨Module.Finite.of_surjective g hg,
    (Module.FaithfullyFlat.iff_flat_and_lTensor_faithful B C).mpr
      ⟨Module.Flat.of_retract f' g hfg, ?_⟩⟩
  intro N _ _ hN
  have hp' : p.comp (Algebra.linearMap B C) = LinearMap.id := by
    apply LinearMap.ext
    intro b
    change p (algebraMap B C b) = b
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hp, smul_eq_mul, mul_one]
  have hi : Function.Injective ((Algebra.linearMap B C).rTensor N) := by
    apply Function.LeftInverse.injective (g := p.rTensor N)
    intro t
    rw [← LinearMap.rTensor_comp_apply, hp', LinearMap.rTensor_id]
    rfl
  exact (hi.comp (TensorProduct.lid B N).symm.injective).nontrivial

end FaithfulFlatness



section DiagramMaps

variable {R E U V X Y : Type u} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
  [CommRing U] [HopfAlgebra R U] [CommRing V] [HopfAlgebra R V]
  [CommRing X] [HopfAlgebra E X] [CommRing Y] [HopfAlgebra E Y]
  [Algebra R X] [IsScalarTower R E X] [Algebra R Y] [IsScalarTower R E Y]

/-- A restriction of a generic homomorphism preserves the coproduct and
counit if the restricted operations were obtained by scalar comparison. -/
private def restrictBialgebraHom (x : GenericFibre R E U X) (y : GenericFibre R E V Y)
    (hy : Function.Injective y.inclusion) (q : X →ₐc[E] Y)
    (q₀ : U →ₐ[R] V) (hq : ∀ a, y.inclusion (q₀ a) = q (x.inclusion a)) :
    U →ₐc[R] V := by
  letI : Module.Flat R V := flat_of_injective_into_field_module (E := E) y.inclusion hy
  letI : Module.Flat R E := IsLocalization.flat E (nonZeroDivisors R)
  letI : Module.Flat R Y := Module.Flat.trans R E Y
  refine BialgHom.ofAlgHom q₀ ?_ ?_
  · ext a
    apply IsFractionRing.injective R E
    change algebraMap R E (Bialgebra.counitAlgHom R V (q₀ a)) =
      algebraMap R E (Bialgebra.counitAlgHom R U a)
    rw [y.counit, x.counit, hq]
    exact DFunLike.congr_fun q.counitAlgHom_comp (x.inclusion a)
  · ext a
    apply tensorComparison_injective (E := E) y.inclusion y.inclusion hy hy
    change tensorComparison R E y.inclusion y.inclusion
        (map q₀ q₀ (Bialgebra.comulAlgHom R U a)) =
      tensorComparison R E y.inclusion y.inclusion (Bialgebra.comulAlgHom R V (q₀ a))
    rw [tensorComparison_natural (g' := q.toAlgHom) (h' := q.toAlgHom) hq hq,
      x.comul, y.comul, hq]
    exact DFunLike.congr_fun q.map_comp_comulAlgHom (x.inclusion a)

end DiagramMaps

section GroupAlgebras

variable {R E M : Type u} [CommRing R] [Field E] [Algebra R E] [CommGroup M]

private theorem groupAlgebraInclusion_eq_map :
    groupAlgebraInclusion R E M = MonoidAlgebra.mapAlgHom M (Algebra.ofId R E) := by
  apply MonoidAlgebra.algHom_ext
  · intro m
    simp [groupAlgebraInclusion, MonoidAlgebra.of]
  · ext

private theorem groupAlgebraInclusion_injective (h : Function.Injective (algebraMap R E)) :
    Function.Injective (groupAlgebraInclusion R E M) := by
  rw [groupAlgebraInclusion_eq_map]
  intro x y hxy
  apply MonoidAlgebra.coeff_injective
  ext m
  apply h
  simpa using congrArg (fun p : MonoidAlgebra E M => p.coeff m) hxy

/-- Extending the coefficients in the marked group algebras preserves every
basis exponent and induces the actual tensor-product identification. -/
private theorem groupAlgebraInclusion_baseChange :
    IsBaseChange E (groupAlgebraInclusion R E M).toLinearMap := by
  apply IsBaseChange.of_equiv (MonoidAlgebra.scalarTensorEquiv R E (M := M)).toLinearEquiv
  intro x
  rw [AlgEquiv.toLinearEquiv_apply, MonoidAlgebra.scalarTensorEquiv_tmul, one_smul]
  exact DFunLike.congr_fun groupAlgebraInclusion_eq_map.symm x

private theorem monoidAlgebraFinitePresentation [IsNoetherianRing R] [Monoid.FG M] :
    Algebra.FinitePresentation R (MonoidAlgebra R M) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance


private theorem monoidAlgebra_mem_range_of_coefficients (p : MonoidAlgebra E M)
    (h : ∀ m ∈ p.coeff.support, ∃ r : R, algebraMap R E r = p.coeff m) :
    p ∈ (groupAlgebraInclusion R E M).range := by
  classical
  have hc (m : M) : ∃ r : R, algebraMap R E r = p.coeff m := by
    by_cases hm : m ∈ p.coeff.support
    · exact h m hm
    · exact ⟨0, by simpa using (Finsupp.notMem_support_iff.mp hm).symm⟩
  choose b hb using hc
  let r := Finsupp.onFinset p.coeff.support (fun m => if m ∈ p.coeff.support then b m else 0)
    (fun m hm => by by_contra hn; exact hm (ite_eq_right hn))
  refine ⟨MonoidAlgebra.ofCoeff r, ?_⟩
  rw [groupAlgebraInclusion_eq_map]
  ext m
  change (MonoidAlgebra.mapRingHom M (algebraMap R E) (MonoidAlgebra.ofCoeff r)).coeff m = _
  rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_ofCoeff]
  simp only [r, Finsupp.onFinset_apply]
  split_ifs with hm
  · exact hb m
  · simpa using (Finsupp.notMem_support_iff.mp hm).symm

private theorem groupAlgebra_mem_range_after_localization
    {A : Type u} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    {J : Type*} [Finite J] (p : J → MonoidAlgebra E M) :
    ∃ d : A, d ≠ 0 ∧ ∀ (S : Type u) [CommRing S] [Algebra A S] [Algebra S E]
      [IsScalarTower A S E], IsUnit (algebraMap A S d) →
        ∀ j, p j ∈ (groupAlgebraInclusion S E M).range := by
  classical
  letI := Fintype.ofFinite J
  let ι := Σ j : J, (p j).coeff.support
  have hE : Algebra.adjoin E (∅ : Set E) = ⊤ := by
    apply top_unique
    intro x _
    exact (Algebra.adjoin E (∅ : Set E)).algebraMap_mem x
  obtain ⟨d, hd, h⟩ := finite_mem_adjoin_after_localization (A := A) (∅ : Set E) hE
    (fun j : ι => (p j.1).coeff j.2)
  refine ⟨d, hd, fun S _ _ _ _ hu j => monoidAlgebra_mem_range_of_coefficients (p j) ?_⟩
  intro m hm
  have he := h S hu (⟨j, ⟨m, hm⟩⟩ : ι)
  rw [Algebra.adjoin_empty] at he
  exact Algebra.mem_bot.mp he

private theorem monoidAlgebra_adjoin_monomials (s : Finset M)
    (hs : Submonoid.closure (s : Set M) = ⊤) :
    Algebra.adjoin R (MonoidAlgebra.of R M '' (s : Set M)) = ⊤ := by
  let U := Algebra.adjoin R (MonoidAlgebra.of R M '' (s : Set M))
  have hU : ∀ m : M, MonoidAlgebra.of R M m ∈ U := by
    intro m
    have hm : m ∈ Submonoid.closure (s : Set M) := hs.symm ▸ trivial
    exact Submonoid.closure_induction (fun a ha => Algebra.subset_adjoin ⟨a, ha, rfl⟩)
      (by
        change MonoidAlgebra.of R M 1 ∈ U
        rw [map_one]
        exact U.one_mem)
      (fun a b _ _ ha hb => by simpa only [map_mul] using U.mul_mem ha hb) hm
  apply top_unique
  intro x _
  change x ∈ U
  clear ‹x ∈ ⊤›
  induction x using MonoidAlgebra.induction_on with
  | of m => exact hU m
  | add a b ha hb => exact U.add_mem ha hb
  | smul r p hp => exact U.smul_mem hp r



/-- The canonical Hopf algebra of a character group extends by scalar extension. -/
def groupAlgebraGenericFibre :
    GenericFibre R E (MonoidAlgebra R M) (MonoidAlgebra E M) where
  inclusion := groupAlgebraInclusion R E M
  baseChange := groupAlgebraInclusion_baseChange
  comul := by
    have he : (tensorComparison R E (groupAlgebraInclusion R E M)
        (groupAlgebraInclusion R E M)).comp (Bialgebra.comulAlgHom R (MonoidAlgebra R M)) =
        ((Bialgebra.comulAlgHom E (MonoidAlgebra E M)).restrictScalars R).comp
          (groupAlgebraInclusion R E M) := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        simp [groupAlgebraInclusion_eq_map]
      · ext
    exact DFunLike.congr_fun he
  counit := by
    have h := MonoidAlgebra.counitAlgHom_comp_mapRingHom (M := M) (algebraMap R E)
    intro x
    rw [groupAlgebraInclusion_eq_map]
    exact (DFunLike.congr_fun h x).symm
  antipode := by
    have he : (groupAlgebraInclusion R E M).comp (HopfAlgebra.antipodeAlgHom R (MonoidAlgebra R M)) =
        ((HopfAlgebra.antipodeAlgHom E (MonoidAlgebra E M)).restrictScalars R).comp
          (groupAlgebraInclusion R E M) := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        simp [groupAlgebraInclusion_eq_map, MonoidAlgebra.antipode_single]
      · ext
    exact DFunLike.congr_fun he

private theorem groupAlgebraInclusion_commutes_with_character_map
    (f : M →* M) (x : MonoidAlgebra R M) :
    groupAlgebraInclusion R E M (MonoidAlgebra.mapDomainBialgHom R f x) =
      MonoidAlgebra.mapDomainBialgHom E f (groupAlgebraInclusion R E M x) := by
  have he : (groupAlgebraInclusion R E M).comp (MonoidAlgebra.mapDomainBialgHom R f).toAlgHom =
      ((MonoidAlgebra.mapDomainBialgHom E f).toAlgHom.restrictScalars R).comp
        (groupAlgebraInclusion R E M) := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      simp [groupAlgebraInclusion_eq_map]
    · ext
  exact DFunLike.congr_fun he x


end GroupAlgebras



section ClosedModel

variable {A E X D : Type u} [CommRing A] [IsDedekindDomain A] [Field E] [Algebra A E]
  [IsFractionRing A E] [CommRing X] [HopfAlgebra E X]
  [CommRing D] [Algebra A D] [Algebra.FinitePresentation A D]

/-- The flat closure in the chosen affine ambient scheme admits the original
group law after restricting to one principal open of the base. -/
theorem exists_closed_affine_group_model
    (m : E ⊗[A] D →ₐ[E] X) (hm : Function.Surjective m) :
    ∃ d : A, d ≠ 0 ∧
      ∃ rE : Algebra (Localization.Away d) E,
      letI := rE
      ∃ h : IsScalarTower A (Localization.Away d) E,
      letI := h
      let R := Localization.Away d
      letI : Algebra R X := ((algebraMap E X).comp (algebraMap R E)).toAlgebra
      letI : IsScalarTower R E X := IsScalarTower.of_algebraMap_eq' rfl
      ∃ (U : Type u) (_ : CommRing U) (_ : HopfAlgebra R U)
        (f : R ⊗[A] D →ₐ[R] U) (e : GenericFibre R E U X),
        Algebra.FinitePresentation R U ∧ Module.Flat R U ∧ Function.Surjective f ∧
          ∀ x : D, e.inclusion (f (1 ⊗ₜ[A] x)) = m (1 ⊗ₜ[A] x) := by
  classical
  letI : Algebra A X := ((algebraMap E X).comp (algebraMap A E)).toAlgebra
  letI : IsScalarTower A E X := IsScalarTower.of_algebraMap_eq' rfl
  let f : D →ₐ[A] X := (m.restrictScalars A).comp includeRight
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := D)
  let t := s.image f
  have ht : (t : Set X) = f '' (s : Set D) := Finset.coe_image
  have hm' : extendAmbientMap (R := E) f = m := by
    apply Algebra.TensorProduct.ext'
    intro a x
    rw [extendAmbientMap_tmul]
    have he : a ⊗ₜ[A] x = algebraMap E (E ⊗[A] D) a * (1 ⊗ₜ[A] x) := by
      change a ⊗ₜ[A] x = (a ⊗ₜ[A] (1 : D)) * ((1 : E) ⊗ₜ[A] x)
      rw [tmul_mul_tmul, mul_one, one_mul]
    rw [he, map_mul, AlgHom.commutes]
    rfl
  have htE : Algebra.adjoin E (t : Set X) = ⊤ := by
    rw [ht, ← extendAmbientMap_range (R := E) f _ hs, hm', AlgHom.range_eq_top]
    exact hm
  obtain ⟨d, hd, hO⟩ := exists_hopf_denominator (A := A) t htE
  let R := Localization.Away d
  let rE := (localizationMap (E := E) d hd).toAlgebra
  letI : Algebra R E := rE
  let hAE := localization_tower (E := E) d hd
  letI : IsScalarTower A R E := hAE
  refine ⟨d, hd, rE, hAE, ?_⟩
  letI : IsDedekindDomain R := localization_dedekind d hd
  letI : IsFractionRing R E := localization_fractionRing d hd
  letI : Algebra R X := ((algebraMap E X).comp (algebraMap R E)).toAlgebra
  letI : IsScalarTower R E X := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A R X := IsScalarTower.to₁₂₄ A R E X
  obtain ⟨O⟩ := hO R (IsLocalization.Away.algebraMap_isUnit (S := R) d)
  let U := Algebra.adjoin R (t : Set X)
  letI : HopfAlgebra R U := O.hopfAlgebra Subtype.val_injective
  have hU : U = Algebra.adjoin R (f '' (s : Set D)) := congrArg (Algebra.adjoin R) ht
  let m₀ : R ⊗[A] D →ₐ[R] U := (extendAmbientMap f).codRestrict U fun x =>
    (hU.trans (extendAmbientMap_range (R := R) f _ hs).symm).symm ▸
      (show extendAmbientMap (R := R) f x ∈ (extendAmbientMap (R := R) f).range from ⟨x, rfl⟩)
  let e : GenericFibre R E U X :=
    ⟨U.val, adjoin_isBaseChange (A := R) _ htE, O.comul_agrees, O.counit_agrees, O.antipode_agrees⟩
  have hfp : Algebra.FinitePresentation R U :=
    Algebra.FinitePresentation.of_finiteType.mp (.adjoin_of_finite t.finite_toSet)
  have hflat : Module.Flat R U :=
    flat_of_injective_into_field_module (E := E) U.val Subtype.val_injective
  refine ⟨U, inferInstance, inferInstance, m₀, e, hfp, hflat, ?_, ?_⟩
  · intro x
    have hx : (x : X) ∈ (extendAmbientMap (R := R) f).range :=
      (hU.trans (extendAmbientMap_range (R := R) f _ hs).symm) ▸ x.property
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  · intro x
    change extendAmbientMap f ((1 : R) ⊗ₜ[A] x) = _
    rw [extendAmbientMap_tmul, map_one, one_mul]
    rfl

end ClosedModel



section FiniteModel

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- The finite span of a family is an algebra once the products of the family
and the unit are in the span. This gives a finite-module presentation of the
integral source using finitely many multiplication coefficients. -/
private theorem span_range_eq_top_of_mul
    (U : Subalgebra R B) (q : B →ₐ[R] C) (s : Set C)
    (hq : ∀ b : U, q b ∈ Algebra.adjoin R s)
    {J : Type*} [Fintype J] (x : J → Algebra.adjoin R s) :
    let V := Algebra.adjoin R s
    let q₀ := (q.comp U.val).codRestrict V hq
    letI := q₀.toAlgebra
    let W := Submodule.span U (Set.range x)
    (1 : V) ∈ W →
    (∀ i j, x i * x j ∈ W) →
    (∀ c : V, (c : C) ∈ s → c ∈ W) →
    W = ⊤ := by
  classical
  dsimp only
  let V := Algebra.adjoin R s
  let q₀ := (q.comp U.val).codRestrict V hq
  letI : Algebra U V := q₀.toAlgebra
  let W := Submodule.span U (Set.range x)
  intro h₁ hm hs
  change (1 : V) ∈ W at h₁
  change ∀ i j, x i * x j ∈ W at hm
  change ∀ c : V, (c : C) ∈ s → c ∈ W at hs
  have hmul {a b : V} (ha : a ∈ W) (hb : b ∈ W) : a * b ∈ W := by
    induction ha, hb using Submodule.span_induction₂ with
    | mem_mem a b ha hb =>
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      exact hm i j
    | zero_left => simp
    | zero_right => simp
    | add_left a₁ a₂ b _ _ _ h₁ h₂ => simpa [add_mul] using W.add_mem h₁ h₂
    | add_right a b₁ b₂ _ _ _ h₁ h₂ => simpa [mul_add] using W.add_mem h₁ h₂
    | smul_left u a b _ _ h => simpa [smul_mul_assoc] using W.smul_mem u h
    | smul_right u a b _ _ h => simpa [mul_smul_comm] using W.smul_mem u h
  let W' : Subalgebra R C :=
    { carrier := V.val '' (W : Set V)
      zero_mem' := ⟨0, W.zero_mem, map_zero V.val⟩
      add_mem' := fun ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ⟨a + b, W.add_mem ha hb, by rw [map_add, ea, eb]⟩
      one_mem' := ⟨1, h₁, map_one V.val⟩
      mul_mem' := fun ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ⟨a * b, hmul ha hb, by rw [map_mul, ea, eb]⟩
      algebraMap_mem' := fun r =>
        ⟨q₀ (algebraMap R U r), by
          change algebraMap U V (algebraMap R U r) ∈ W
          rw [Algebra.algebraMap_eq_smul_one]
          exact W.smul_mem _ h₁,
        by rw [AlgHom.commutes, AlgHom.commutes]⟩ }
  have hle : V ≤ W' := Algebra.adjoin_le fun c hc =>
    ⟨⟨c, Algebra.subset_adjoin hc⟩, hs _ hc, rfl⟩
  apply top_unique
  intro z _
  obtain ⟨z', hz', hzz'⟩ := hle z.property
  exact Subtype.val_injective hzz' ▸ hz'


/-- The generic dual basis and the section of the unit restrict once their
values on the integral module generators belong to the target model. -/
private theorem finite_faithfullyFlat_of_restricted_dual_family
    (U : Subalgebra R B) (V : Subalgebra R C)
    (q : B →ₐ[R] C) (q₀ : U →ₐ[R] V)
    (hq : ∀ b : U, (q₀ b : C) = q b)
    {J : Type*} [Fintype J] (x : J → V) :
    letI := q.toAlgebra
    letI := q₀.toAlgebra
    ∀ (f : J → C →ₗ[B] B) (p : C →ₗ[B] B),
      (∀ c, ∑ j, f j c • (x j : C) = c) → p 1 = 1 →
      Submodule.span U (Set.range x) = ⊤ →
      (∀ j k, f j (x k) ∈ U) → (∀ k, p (x k) ∈ U) →
      Module.Finite U V ∧ Module.FaithfullyFlat U V := by
  letI : Algebra B C := q.toAlgebra
  letI : Algebra U V := q₀.toAlgebra
  intro f p hf hp hx hfmem hpmem
  change Submodule.span U (Set.range x) = ⊤ at hx
  have smul_compat (a : U) (v : V) : ((a • v : V) : C) = (a : B) • (v : C) := by
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact congrArg (fun c => c * (v : C)) (hq a)
  have maps_into_model (l : C →ₗ[B] B) (hl : ∀ j, l (x j) ∈ U) (v : V) :
      l v ∈ U := by
    have hv : v ∈ Submodule.span U (Set.range x) := hx.symm ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact hl j
    | zero => simp
    | add a b _ _ ha hb =>
      change l ((a : C) + (b : C)) ∈ U
      rw [map_add]
      exact U.add_mem ha hb
    | smul a v _ hv =>
      rw [smul_compat, map_smul, smul_eq_mul]
      exact U.mul_mem a.property hv
  let restrict (l : C →ₗ[B] B) (hl : ∀ j, l (x j) ∈ U) : V →ₗ[U] U :=
    { toFun := fun v => ⟨l v, maps_into_model l hl v⟩
      map_add' := fun a b => Subtype.ext (map_add l (a : C) (b : C))
      map_smul' := fun a v => Subtype.ext (by
        change l ((a • v : V) : C) = (a : B) * l (v : C)
        rw [smul_compat, map_smul, smul_eq_mul]) }
  refine faithfullyFlat_of_dual_family_and_unit_section x
    (fun j => restrict (f j) (hfmem j)) (fun v => ?_) (restrict p hpmem) (Subtype.ext hp)
  apply Subtype.val_injective (p := fun z : C => z ∈ V)
  change V.val (∑ j, restrict (f j) (hfmem j) v • x j) = V.val v
  rw [map_sum]
  simpa only [Subalgebra.val_apply, smul_compat, restrict, LinearMap.coe_mk, AddHom.coe_mk] using hf v


end FiniteModel



section Kernel

variable {R B C N : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing N]
  [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R N]
  {q : B →ₐc[R] C} {j : C →ₐc[R] N}

/-- At every coordinate in the target algebra the kernel map is the
augmentation of the target group. -/
private theorem comp_eq_counit_of_isFullKernel (h : IsFullKernel q j) (b : B) :
    j (q b) = algebraMap R N (Bialgebra.counitAlgHom R B b) := by
  let ε := Bialgebra.counitAlgHom R B
  let w := b - algebraMap R B (ε b)
  have hε : w ∈ RingHom.ker ε.toRingHom := by simp [w, AlgHom.commutes]
  have hw : q w ∈ RingHom.ker j.toAlgHom.toRingHom := by
    rw [h.2]
    exact Ideal.mem_map_of_mem q.toAlgHom.toRingHom hε
  change j (q w) = 0 at hw
  rw [show w = b - algebraMap R B (ε b) from rfl, map_sub, map_sub, sub_eq_zero] at hw
  rw [hw]
  change j.toAlgHom (q.toAlgHom (algebraMap R B (ε b))) = _
  rw [AlgHom.commutes, AlgHom.commutes]

/-- The augmentation ideal description is the functor-of-points universal
property of the full scheme kernel, together with its closed immersion. -/
theorem isFullKernel_iff_affine_points (q : B →ₐc[R] C) (j : C →ₐc[R] N) :
    IsFullKernel q j ↔
      Function.Surjective j ∧
      (∀ b, j (q b) = algebraMap R N (Bialgebra.counitAlgHom R B b)) ∧
      ∀ (T : Type u) [CommRing T] [Algebra R T] (f : C →ₐ[R] T),
        (∀ b, f (q b) = algebraMap R T (Bialgebra.counitAlgHom R B b)) →
        ∃! g : N →ₐ[R] T, g.comp j.toAlgHom = f := by
  let ε := Bialgebra.counitAlgHom R B
  let I := (RingHom.ker ε.toRingHom).map q.toAlgHom.toRingHom
  constructor
  · intro h
    refine ⟨h.1, comp_eq_counit_of_isFullKernel h, fun T _ _ f hf => ?_⟩
    have hI : I ≤ RingHom.ker f.toRingHom := by
      refine Ideal.map_le_iff_le_comap.mpr fun b hb => ?_
      change f (q b) = 0
      change ε b = 0 at hb
      rw [hf, hb, map_zero]
    have hker : RingHom.ker j.toAlgHom.toRingHom ≤ RingHom.ker f.toRingHom := h.2 ▸ hI
    let g := AlgHom.liftOfSurjective j.toAlgHom h.1 f hker
    refine ⟨g, AlgHom.liftOfSurjective_comp _ _ _ _, fun g' hg => ?_⟩
    apply AlgHom.ext
    intro n
    obtain ⟨c, rfl⟩ := h.1 n
    exact (DFunLike.congr_fun hg c).trans
      (AlgHom.liftOfSurjective_apply j.toAlgHom h.1 f hker c).symm
  · rintro ⟨hSurj, hj, h⟩
    refine ⟨hSurj, le_antisymm ?_ ?_⟩
    · let f := Ideal.Quotient.mkₐ R I
      have hf (b : B) : f (q b) = algebraMap R (C ⧸ I) (ε b) := by
        have hw : b - algebraMap R B (ε b) ∈ RingHom.ker ε.toRingHom := by simp [ε]
        have hz : q.toAlgHom (b - algebraMap R B (ε b)) ∈ I :=
          Ideal.mem_map_of_mem q.toAlgHom.toRingHom hw
        rw [map_sub, AlgHom.commutes] at hz
        have hz' : f (q b - algebraMap R C (ε b)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
        rw [map_sub, AlgHom.commutes, sub_eq_zero] at hz'
        exact hz'
      obtain ⟨g, hg, _⟩ := h (C ⧸ I) f hf
      intro c hc
      change j c = 0 at hc
      change c ∈ I
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change f c = 0
      rw [← DFunLike.congr_fun hg c]
      change g (j c) = 0
      rw [hc, map_zero]
    · refine Ideal.map_le_iff_le_comap.mpr fun b hb => ?_
      change j (q b) = 0
      change ε b = 0 at hb
      rw [hj, hb, map_zero]

/-- To check the full kernel, lift its coordinate algebra linearly over the
scalar ring and check the lift on a module generating family of the cover. -/
private theorem isFullKernel_of_module_generators {J : Type*}
    (x : J → C) (s : N →ₗ[R] C) (hs : ∀ n, j (s n) = n)
    (hcomm : ∀ b, j (q b) = algebraMap R N (Bialgebra.counitAlgHom R B b))
    (hx : letI := q.toAlgHom.toAlgebra; Submodule.span B (Set.range x) = ⊤)
    (hrel : ∀ k, x k - s (j (x k)) ∈
      (RingHom.ker (Bialgebra.counitAlgHom R B).toRingHom).map q.toAlgHom.toRingHom) :
    IsFullKernel q j := by
  letI := q.toAlgHom.toAlgebra
  let ε := Bialgebra.counitAlgHom R B
  let K := (RingHom.ker ε.toRingHom).map q.toAlgHom.toRingHom
  refine ⟨fun n => ⟨s n, hs n⟩, le_antisymm ?_ ?_⟩
  · have hdiff (c : C) : c - s (j c) ∈ K := by
      have hc : c ∈ Submodule.span B (Set.range x) := hx.symm ▸ Submodule.mem_top
      induction hc using Submodule.span_induction with
      | mem c hm =>
        obtain ⟨k, rfl⟩ := hm
        exact hrel k
      | zero => simp
      | add a b _ _ ha hb =>
        simp only [map_add, add_sub_add_comm]
        exact K.add_mem ha hb
      | smul b c _ hc =>
        have hd : q b - algebraMap R C (ε b) ∈ K := by
          have hb : b - algebraMap R B (ε b) ∈ RingHom.ker ε.toRingHom := by
            simp [ε]
          have hk := Ideal.mem_map_of_mem q.toAlgHom.toRingHom hb
          change q.toAlgHom (b - algebraMap R B (ε b)) ∈ K at hk
          rw [map_sub, AlgHom.commutes] at hk
          exact hk
        change q b * c - s (j (q b * c)) ∈ K
        rw [map_mul, hcomm, ← Algebra.smul_def, map_smul, Algebra.smul_def]
        have he : q b * c - algebraMap R C (ε b) * s (j c) =
            q b * (c - s (j c)) + (q b - algebraMap R C (ε b)) * s (j c) := by ring
        rw [he]
        exact K.add_mem (K.mul_mem_left _ hc) (K.mul_mem_right _ hd)
    intro c hc
    change j c = 0 at hc
    change c ∈ K
    simpa only [hc, map_zero, sub_zero] using hdiff c
  · apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change ε b = 0 at hb
    change j (q b) = 0
    rw [hcomm, hb, map_zero]

end Kernel



section Torsor

open scoped CategoryTheory.MonObj
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.IntegralCentralQuotient (OverBase HopfSpectrum spectrumOfAlgHom spectrumOfHopfHom
  rightCoaction IsRightTorsor)

variable {R B C N : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing N]
  [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R N]

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation-ideal description identifies the actual kernel pullback over the base. -/
theorem fullKernel_isPullback (q : B →ₐc[R] C) (j : C →ₐc[R] N)
    (h : IsFullKernel q j) :
    IsPullback (spectrumOfHopfHom j).hom.hom (toUnit (HopfSpectrum R N).X)
      (spectrumOfHopfHom q).hom.hom η[(HopfSpectrum R B).X] := by
  let F := Over.forget (Spec (CommRingCat.of R))
  apply IsPullback.of_map_of_faithful F
  let q' := CommRingCat.ofHom q.toAlgHom.toRingHom
  let j' := CommRingCat.ofHom j.toAlgHom.toRingHom
  let ε := Bialgebra.counitAlgHom R B
  let e' := CommRingCat.ofHom ε.toRingHom
  let unit := CommRingCat.ofHom (algebraMap R N)
  change IsPullback (Spec.map j') (Spec.map unit) (Spec.map q') (Spec.map e')
  apply isPullback_SpecMap_of_isPushout
  have hp := (isFullKernel_iff_affine_points q j).mp h
  refine IsPushout.mk' (CommRingCat.hom_ext (RingHom.ext hp.2.1)) ?_ ?_
  · intro T f g hfg _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hp.1 x
    exact ConcreteCategory.congr_hom hfg y
  · intro T f g hfg
    letI : Algebra R T := g.hom.toAlgebra
    let f₀ : C →ₐ[R] T :=
      { f.hom with
        commutes' := fun a => by
          have he := ConcreteCategory.congr_hom hfg (algebraMap R B a)
          change f.hom (q.toAlgHom (algebraMap R B a)) =
            g.hom (ε (algebraMap R B a)) at he
          rw [q.toAlgHom.commutes, ε.commutes, Algebra.algebraMap_self_apply] at he
          exact he }
    have hf (b : B) : f₀ (q b) = algebraMap R T (ε b) :=
      ConcreteCategory.congr_hom hfg b
    obtain ⟨l, hl, _⟩ := hp.2.2 T f₀ hf
    refine ⟨CommRingCat.ofHom l.toRingHom, ?_, ?_⟩
    · exact CommRingCat.hom_ext (RingHom.ext fun c => DFunLike.congr_fun hl c)
    · exact CommRingCat.hom_ext (RingHom.ext l.commutes)

private theorem rightTranslation_isPullback {H G K : Grp (OverBase R)}
    (q : H ⟶ G) (j : K ⟶ H)
    (h : IsPullback j.hom.hom (toUnit K.X) q.hom.hom η[G.X]) :
    IsPullback (fst H.X K.X) (fst H.X K.X * (snd H.X K.X ≫ j.hom.hom))
      q.hom.hom q.hom.hom := by
  let p := fst H.X K.X
  let s := snd H.X K.X
  let i := j.hom.hom
  have hi : i ≫ q.hom.hom = 1 := h.w
  have hw : p ≫ q.hom.hom = (p * (s ≫ i)) ≫ q.hom.hom := by
    rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, mul_one]
  refine IsPullback.mk' hw ?_ ?_
  · intro T a b h₁ h₂
    apply CartesianMonoidalCategory.hom_ext _ _ h₁
    apply h.hom_ext _ (toUnit_unique _ _)
    rw [MonObj.comp_mul, MonObj.comp_mul, h₁] at h₂
    exact mul_left_cancel (by simpa only [Category.assoc] using h₂)
  · intro T a b hab
    have hd : (a⁻¹ * b) ≫ q.hom.hom = toUnit T ≫ η[G.X] := by
      change (a⁻¹ * b) ≫ q.hom.hom = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp, hab, inv_mul_cancel]
    let d := h.lift (a⁻¹ * b) (toUnit T) hd
    refine ⟨lift a d, lift_fst _ _, ?_⟩
    rw [MonObj.comp_mul, lift_fst, ← Category.assoc, lift_snd,
      show d ≫ i = a⁻¹ * b from h.lift_fst _ _ _, mul_inv_cancel_left]

set_option backward.isDefEq.respectTransparency false in
private theorem affineRightTranslation_isPullback {M : Type u} [CommGroup M]
    (q : B →ₐc[R] C) (j : C →ₐc[R] MonoidAlgebra R M) (h : IsFullKernel q j) :
    IsPullback (spectrumOfAlgHom (R := R)
      (includeLeft : C →ₐ[R] C ⊗[R] MonoidAlgebra R M)).left
      (spectrumOfAlgHom (rightCoaction j)).left
      (spectrumOfHopfHom q).hom.hom.left (spectrumOfHopfHom q).hom.hom.left := by
  let K := MonoidAlgebra R M
  let H := HopfSpectrum R C
  let Z := HopfSpectrum R K
  let F := Over.forget (Spec (CommRingCat.of R))
  let e : H.X ⊗ Z.X ≅ (algSpec (CommRingCat.of R)).obj (Opposite.op (CommAlgCat.of R (C ⊗[R] K))) :=
    Over.isoMk (pullbackSpecIso R C K) (pullbackSpecIso_hom_base R C K)
  let l : C →ₐ[R] C ⊗[R] K := includeLeft
  let r : K →ₐ[R] C ⊗[R] K := includeRight
  have hl : e.hom ≫ spectrumOfAlgHom l = fst H.X Z.X :=
    Over.OverMorphism.ext (pullbackSpecIso_hom_fst R C K)
  have hr : e.hom ≫ spectrumOfAlgHom r = snd H.X Z.X :=
    Over.OverMorphism.ext (pullbackSpecIso_hom_snd R C K)
  have hmul : toConv (rightCoaction j) = toConv l * toConv (r.comp j.toAlgHom) := by
    apply WithConv.ofConv_injective
    simp only [AlgHom.convMul_def, ofConv_toConv, rightCoaction, ← AlgHom.comp_assoc]
    congr 1
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [map_tmul, AlgHom.id_apply]
    change a ⊗ₜ[R] j b = (a ⊗ₜ[R] (1 : K)) * ((1 : C) ⊗ₜ[R] j b)
    rw [tmul_mul_tmul, mul_one, one_mul]
  let point (f : C →ₐ[R] C ⊗[R] K) :
      (algSpec (CommRingCat.of R)).obj (Opposite.op (CommAlgCat.of R (C ⊗[R] K))) ⟶ H.X :=
    spectrumOfAlgHom f
  have hprod : point (rightCoaction j) =
      point l * (spectrumOfAlgHom r ≫ (spectrumOfHopfHom j).hom.hom) := by
    have hs := congrArg (Spec.mapMulEquiv (R := R) (S := C) (T := C ⊗[R] K)) hmul
    rw [map_mul] at hs
    have hcomp : point (r.comp j.toAlgHom) =
        spectrumOfAlgHom r ≫ (spectrumOfHopfHom j).hom.hom :=
      (algSpec (CommRingCat.of R)).map_comp (CommAlgCat.ofHom r).op (CommAlgCat.ofHom j.toAlgHom).op
    change point (rightCoaction j) = point l * point (r.comp j.toAlgHom) at hs
    exact hs.trans (congrArg (point l * ·) hcomp)
  have ha : e.hom ≫ point (rightCoaction j) =
      fst H.X Z.X * (snd H.X Z.X ≫ (spectrumOfHopfHom j).hom.hom) := by
    rw [hprod, MonObj.comp_mul, show point l = spectrumOfAlgHom l from rfl,
      hl, ← Category.assoc, hr]
  have hs := rightTranslation_isPullback (spectrumOfHopfHom q) (spectrumOfHopfHom j)
    (fullKernel_isPullback q j h)
  have hs' : IsPullback (point l) (point (rightCoaction j))
      (spectrumOfHopfHom q).hom.hom (spectrumOfHopfHom q).hom.hom :=
    hs.of_iso e (Iso.refl H.X) (Iso.refl H.X) (Iso.refl (HopfSpectrum R B).X)
      ((Category.comp_id (fst H.X Z.X)).trans hl.symm)
      ((Category.comp_id (fst H.X Z.X * (snd H.X Z.X ≫ (spectrumOfHopfHom j).hom.hom))).trans
        ha.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact F.map_isPullback hs'

/-- A finite faithfully flat finitely presented map is a right torsor under its full kernel. -/
theorem fullKernelRightTorsor {M : Type u} [CommGroup M]
    (q : B →ₐc[R] C) (j : C →ₐc[R] MonoidAlgebra R M) (h : IsFullKernel q j)
    (hfin : letI := q.toAlgHom.toAlgebra; Module.Finite B C)
    (hff : letI := q.toAlgHom.toAlgebra; Module.FaithfullyFlat B C)
    (hfp : letI := q.toAlgHom.toAlgebra; Algebra.FinitePresentation B C) :
    IsRightTorsor q j := by
  let := q.toAlgHom.toAlgebra
  let f := CommRingCat.ofHom q.toAlgHom.toRingHom
  have hgeom := (flat_and_surjective_SpecMap_iff f).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
  exact ⟨(IsFinite.SpecMap_iff f).mpr (RingHom.finite_algebraMap.mpr hfin), hgeom.1, hgeom.2,
    (LocallyOfFinitePresentation.SpecMap_iff f).mpr (RingHom.finitePresentation_algebraMap.mpr hfp),
    affineRightTranslation_isPullback q j h⟩

end Torsor


section MarkedMap

variable {A E X M : Type u} [CommRing A] [IsDomain A] [Field E] [Algebra A E]
  [IsFractionRing A E] [CommRing X] [Algebra A X] [Algebra E X] [IsScalarTower A E X]
  [CommGroup M] [Monoid.FG M]

/-- A surjection from the generic algebra to a marked group algebra remains
a surjection on the model after making the generator images and finitely
many monomial preimages integral. -/
private theorem exists_marked_map_denominator (s : Finset X) (hs : Algebra.adjoin E (s : Set X) = ⊤)
    (q : X →ₐ[E] MonoidAlgebra E M) (hq : Function.Surjective q) :
    ∃ d : A, d ≠ 0 ∧ ∀ (R : Type u) [CommRing R] [Algebra A R] [Algebra R E]
      [IsScalarTower A R E] [Algebra R X] [IsScalarTower A R X] [IsScalarTower R E X],
      IsUnit (algebraMap A R d) → Function.Injective (algebraMap R E) →
      ∃ q₀ : Algebra.adjoin R (s : Set X) →ₐ[R] MonoidAlgebra R M,
        Function.Surjective q₀ ∧ ∀ x, groupAlgebraInclusion R E M (q₀ x) = q (x : X) := by
  classical
  obtain ⟨T, hT, hTf⟩ := Monoid.fg_iff.mp (inferInstance : Monoid.FG M)
  let t := hTf.toFinset
  have ht : Submonoid.closure (t : Set M) = ⊤ := by simpa [t] using hT
  choose x hx using fun m : t => hq (MonoidAlgebra.of E M m)
  obtain ⟨a, ha, hA⟩ := groupAlgebra_mem_range_after_localization (A := A)
    (fun u : s => q u)
  obtain ⟨b, hb, hB⟩ := finite_mem_adjoin_after_localization (A := A) (s : Set X) hs x
  refine ⟨a * b, mul_ne_zero ha hb, fun R _ _ _ _ _ _ _ hu hi => ?_⟩
  have hau := isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_right a b)) hu
  have hbu := isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_left b a)) hu
  let U := Algebra.adjoin R (s : Set X)
  let ι := groupAlgebraInclusion R E M
  have hι : Function.Injective ι := groupAlgebraInclusion_injective hi
  let e := AlgEquiv.ofInjective ι hι
  let g := q.restrictScalars R
  have hg : U ≤ ι.range.comap g := Algebra.adjoin_le fun u hu => hA R hau ⟨u, hu⟩
  let q₀ := e.symm.toAlgHom.comp ((g.comp U.val).codRestrict ι.range fun u => hg u.property)
  have ha (u : U) : ι (q₀ u) = q (u : X) := by
    change ((e (e.symm ⟨q (u : X), _⟩)) : MonoidAlgebra E M) = q (u : X)
    rw [AlgEquiv.apply_symm_apply]
  have he : q₀.range = ⊤ := by
    apply le_antisymm le_top
    rw [← monoidAlgebra_adjoin_monomials (R := R) t ht]
    apply Algebra.adjoin_le
    rintro _ ⟨m, hm, rfl⟩
    let z : t := ⟨m, hm⟩
    refine ⟨⟨x z, hB R hbu z⟩, hι ?_⟩
    change ι (q₀ (⟨x z, hB R hbu z⟩ : U)) = ι (MonoidAlgebra.of R M m)
    rw [ha, hx]
    simp [ι, groupAlgebraInclusion]
    rfl
  exact ⟨q₀, (AlgHom.range_eq_top q₀).mp he, ha⟩

end MarkedMap



section CoverDenominator

variable {A E B C : Type u} [CommRing A] [IsDomain A] [Field E] [Algebra A E]
  [IsFractionRing A E] [CommRing B] [CommRing C] [Algebra E B] [Algebra E C]
  [Algebra A B] [Algebra A C] [IsScalarTower A E B] [IsScalarTower A E C]

private theorem exists_cover_denominator [Algebra.FiniteType E B]
    (sB : Finset B) (hB : Algebra.adjoin E (sB : Set B) = ⊤)
    (sC : Finset C) (hC : Algebra.adjoin E (sC : Set C) = ⊤)
    (q : B →ₐ[E] C) (hFin : letI := q.toAlgebra; Module.Finite B C)
    (hFF : letI := q.toAlgebra; Module.FaithfullyFlat B C)
    {J : Type*} [Fintype J] (x : J → C)
    (hx : letI := q.toAlgebra; Submodule.span B (Set.range x) = ⊤) :
    ∃ d : A, d ≠ 0 ∧ ∀ (R : Type u) [CommRing R] [Algebra A R] [Algebra R E]
      [IsScalarTower A R E] [Algebra R B] [Algebra R C]
      [IsScalarTower A R B] [IsScalarTower A R C] [IsScalarTower R E B] [IsScalarTower R E C],
      IsUnit (algebraMap A R d) →
      let U := Algebra.adjoin R (sB : Set B)
      let V := Algebra.adjoin R (sC : Set C)
      ∃ (q₀ : U →ₐ[R] V) (x₀ : J → V),
        (∀ b : U, (q₀ b : C) = q b) ∧ (∀ j, (x₀ j : C) = x j) ∧
        letI := q₀.toAlgebra
        Submodule.span U (Set.range x₀) = ⊤ ∧
          Module.Finite U V ∧ Module.FaithfullyFlat U V := by
  classical
  letI := q.toAlgebra
  letI : Module.Finite B C := hFin
  letI : Module.FaithfullyFlat B C := hFF
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing E B
  obtain ⟨f, p, hDual, hUnit⟩ := exists_dual_family_and_unit_section x hx
  let v : Unit ⊕ ((J × J) ⊕ sC) → C :=
    Sum.elim (fun _ => 1) (Sum.elim (fun i : J × J => x i.1 * x i.2) Subtype.val)
  have hv : Function.Surjective (Fintype.linearCombination B x) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination B x).mp hx
  choose c hc using fun j => hv (v j)
  let coeff : (((Unit ⊕ ((J × J) ⊕ sC)) × J) ⊕ ((J × J) ⊕ J)) → B :=
    Sum.elim (fun pair => c pair.1 pair.2)
      (Sum.elim (fun pair : J × J => f pair.1 (x pair.2)) (fun j => p (x j)))
  obtain ⟨a, ha, hA⟩ := finite_mem_adjoin_after_localization (A := A) (sB : Set B) hB coeff
  obtain ⟨b, hb, hB'⟩ := finite_mem_adjoin_after_localization (A := A) (sC : Set C) hC
    (Sum.elim (fun z : sB => q z) x)
  refine ⟨a * b, mul_ne_zero ha hb, fun R _ _ _ _ _ _ _ _ _ _ hR => ?_⟩
  have hau := isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_right a b)) hR
  have hbu := isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_left b a)) hR
  let U := Algebra.adjoin R (sB : Set B)
  let V := Algebra.adjoin R (sC : Set C)
  let g := q.restrictScalars R
  have hq : ∀ z : U, g z ∈ V := by
    have h : U ≤ V.comap g := Algebra.adjoin_le fun z hz => hB' R hbu (Sum.inl ⟨z, hz⟩)
    exact fun z => h z.property
  let q₀ := (g.comp U.val).codRestrict V hq
  letI : Algebra U V := q₀.toAlgebra
  let x₀ : J → V := fun j => ⟨x j, hB' R hbu (.inr j)⟩
  let W := Submodule.span U (Set.range x₀)
  have hcoeff (j : Unit ⊕ ((J × J) ⊕ sC)) (i : J) : c j i ∈ U :=
    hA R hau (.inl (j, i))
  have hgen (j : Unit ⊕ ((J × J) ⊕ sC)) (z : V) (hz : (z : C) = v j) : z ∈ W := by
    let a' (i : J) : U := ⟨c j i, hcoeff j i⟩
    have eq : (∑ i, a' i • x₀ i) = z := by
      apply Subtype.val_injective
      change V.val (∑ i, a' i • x₀ i) = (z : C)
      rw [map_sum, hz]
      exact hc j
    rw [← eq]
    exact Submodule.sum_mem W fun i _ => W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hw : W = ⊤ :=
    span_range_eq_top_of_mul U g (sC : Set C) hq x₀
      (hgen (.inl ()) 1 rfl)
      (fun i j => hgen (.inr (.inl (i, j))) (x₀ i * x₀ j) rfl)
      (fun z hz => hgen (.inr (.inr ⟨z, hz⟩)) z rfl)
  exact ⟨q₀, x₀, fun _ => rfl, fun _ => rfl, hw,
    finite_faithfullyFlat_of_restricted_dual_family U V g q₀ (fun _ => rfl)
      x₀ f p hDual hUnit hw (fun j k => hA R hau (.inr (.inl (j, k))))
      (fun j => hA R hau (.inr (.inr j)))⟩

end CoverDenominator



section KernelCertificate

variable {R E V C M : Type u} [CommRing R] [Field E] [Algebra R E]
  [CommRing V] [Algebra R V] [CommRing C] [Algebra R C] [Algebra E C] [IsScalarTower R E C]
  [CommGroup M]

private def liftMonomials {S W : Type u} [CommRing S] [AddCommGroup W] [Module S W]
    (x : M → W) : MonoidAlgebra S M →ₗ[S] W :=
  (Finsupp.linearCombination S x).comp (MonoidAlgebra.coeffLinearEquiv S).toLinearMap

@[simp] private theorem liftMonomials_single {S W : Type u} [CommRing S] [AddCommGroup W]
    [Module S W] (x : M → W) (m : M) (a : S) :
    liftMonomials x (MonoidAlgebra.single m a) = a • x m := by
  change Finsupp.linearCombination S x (Finsupp.single m a) = _
  exact Finsupp.linearCombination_single _ _ _

private theorem liftMonomials_is_section (q : V →ₐ[R] MonoidAlgebra R M) (x : M → V)
    (hx : ∀ m, q (x m) = MonoidAlgebra.of R M m) (z : MonoidAlgebra R M) :
    q (liftMonomials x z) = z := by
  have h : q.toLinearMap.comp (liftMonomials x) = LinearMap.id := by
    apply MonoidAlgebra.lhom_ext'
    intro m
    apply LinearMap.ext
    intro r
    simp [MonoidAlgebra.lsingle_apply, hx]
  exact DFunLike.congr_fun h z

private theorem liftMonomials_comp_inclusion (i : V →ₐ[R] C) (x : M → V) (y : M → C)
    (hxy : ∀ m, i (x m) = y m) (z : MonoidAlgebra R M) :
    i (liftMonomials x z) = liftMonomials y (groupAlgebraInclusion R E M z) := by
  have h : i.toLinearMap.comp (liftMonomials x) =
      ((liftMonomials (S := E) y).restrictScalars R).comp
        (groupAlgebraInclusion R E M).toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro m
    apply LinearMap.ext
    intro r
    have hr : groupAlgebraInclusion R E M (MonoidAlgebra.single m r) =
        MonoidAlgebra.single m (algebraMap R E r) := by
      rw [groupAlgebraInclusion_eq_map, MonoidAlgebra.mapAlgHom_single]
      rfl
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, liftMonomials_single,
      AlgHom.toLinearMap_apply, map_smul, hxy, LinearMap.restrictScalars_apply, hr]
    exact (algebraMap_smul E r (y m)).symm
  exact DFunLike.congr_fun h z

private theorem exists_finite_ideal_expression {B C : Type u} [CommRing B] [CommRing C]
    (q : B →+* C) (K : Ideal B) {z : C} (hz : z ∈ K.map q) :
    ∃ (s : Finset C) (a : s → B) (b : s → C),
      (∀ j, a j ∈ K) ∧ (∑ j, b j * q (a j)) = z := by
  classical
  change z ∈ Submodule.span C (q '' (K : Set B)) at hz
  obtain ⟨s, hs, hzs⟩ := Submodule.mem_span_finite_of_mem_span hz
  obtain ⟨b, hb⟩ := Submodule.mem_span_finset'.mp hzs
  choose a ha hqa using fun j : s => hs j.property
  refine ⟨s, a, b, ha, ?_⟩
  simpa only [hqa, smul_eq_mul] using hb

end KernelCertificate



section KernelDenominator

variable {A E B C M : Type u} [CommRing A] [IsDomain A] [Field E] [Algebra A E]
  [IsFractionRing A E] [CommRing B] [CommRing C] [HopfAlgebra E B] [HopfAlgebra E C]
  [Algebra A B] [Algebra A C] [IsScalarTower A E B] [IsScalarTower A E C] [CommGroup M] [Finite M]

private theorem exists_kernel_denominator
    (sB : Finset B) (hB : Algebra.adjoin E (sB : Set B) = ⊤)
    (sC : Finset C) (hC : Algebra.adjoin E (sC : Set C) = ⊤)
    (q : B →ₐc[E] C) (j : C →ₐc[E] MonoidAlgebra E M) (hk : IsFullKernel q j)
    {J : Type*} [Fintype J] (x : J → C) :
    ∃ d : A, d ≠ 0 ∧ ∀ (R : Type u) [CommRing R] [IsDedekindDomain R]
      [Algebra A R] [Algebra R E] [IsFractionRing R E] [IsScalarTower A R E]
      [Algebra R B] [Algebra R C] [IsScalarTower A R B] [IsScalarTower A R C]
      [IsScalarTower R E B] [IsScalarTower R E C],
      IsUnit (algebraMap A R d) →
      let U := Algebra.adjoin R (sB : Set B)
      let V := Algebra.adjoin R (sC : Set C)
      ∀ (oB : RestrictedOperations (E := E) U.val) (oC : RestrictedOperations (E := E) V.val),
        letI := oB.hopfAlgebra Subtype.val_injective
        letI := oC.hopfAlgebra Subtype.val_injective
        ∀ (q₀ : U →ₐc[R] V) (j₀ : V →ₐc[R] MonoidAlgebra R M) (x₀ : J → V),
          (∀ b : U, (q₀ b : C) = q b) →
          (∀ z : V, groupAlgebraInclusion R E M (j₀ z) = j z) →
          (∀ k, (x₀ k : C) = x k) →
          (letI := q₀.toAlgHom.toAlgebra; Submodule.span U (Set.range x₀) = ⊤) →
          IsFullKernel q₀ j₀ := by
  classical
  choose y hy using fun m : M => hk.1 (MonoidAlgebra.of E M m)
  let v := liftMonomials (S := E) y
  have hker (k : J) : x k - v (j (x k)) ∈ RingHom.ker j.toAlgHom.toRingHom := by
    change j (x k - v (j (x k))) = 0
    rw [map_sub, sub_eq_zero]
    exact (liftMonomials_is_section j.toAlgHom y hy (j (x k))).symm
  choose t a b ha hb using fun k =>
    exists_finite_ideal_expression q.toAlgHom.toRingHom
      (RingHom.ker (Bialgebra.counitAlgHom E B).toRingHom) (hk.2 ▸ hker k)
  let L := Σ k : J, t k
  obtain ⟨d, hd, hD⟩ := finite_mem_adjoin_after_localization (A := A) (sB : Set B) hB
    (fun l : L => a l.1 l.2)
  obtain ⟨e, he, hE⟩ := finite_mem_adjoin_after_localization (A := A) (sC : Set C) hC
    (Sum.elim (fun l : L => b l.1 l.2) y)
  refine ⟨d * e, mul_ne_zero hd he, fun R _ _ _ _ _ _ _ _ _ _ _ _ hu oB oC q₀ j₀ x₀ hq hj hx hsp => ?_⟩
  have hdu := isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_right d e)) hu
  have heu := isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_left e d)) hu
  let U := Algebra.adjoin R (sB : Set B)
  let V := Algebra.adjoin R (sC : Set C)
  letI := oB.hopfAlgebra Subtype.val_injective
  letI := oC.hopfAlgebra Subtype.val_injective
  let i := groupAlgebraInclusion R E M
  have hi : Function.Injective i := groupAlgebraInclusion_injective (IsFractionRing.injective R E)
  let y₀ (m : M) : V := ⟨y m, hE R heu (.inr m)⟩
  have hy₀ (m : M) : j₀ (y₀ m) = MonoidAlgebra.of R M m := by
    apply hi
    rw [hj, show (y₀ m : C) = y m from rfl, hy]
    simp [i, groupAlgebraInclusion]
  refine isFullKernel_of_module_generators x₀ (liftMonomials y₀)
    (liftMonomials_is_section j₀.toAlgHom y₀ hy₀) ?_ hsp ?_
  · intro z
    apply hi
    rw [hj, hq, comp_eq_counit_of_isFullKernel hk]
    change algebraMap E (MonoidAlgebra E M) (Bialgebra.counitAlgHom E B (z : B)) =
      i (algebraMap R (MonoidAlgebra R M) (oB.counit z))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R E (MonoidAlgebra E M), oB.counit_agrees]
    rfl
  · intro k
    let K := RingHom.ker (Bialgebra.counitAlgHom R U).toRingHom
    let a₀ (l : t k) : U := ⟨a k l, hD R hdu ⟨k, l⟩⟩
    let b₀ (l : t k) : V := ⟨b k l, hE R heu (.inl ⟨k, l⟩)⟩
    have haug (l : t k) : a₀ l ∈ K := by
      change oB.counit (a₀ l) = 0
      apply IsFractionRing.injective R E
      rw [oB.counit_agrees, map_zero]
      exact ha k l
    have eq : (∑ l : t k, b₀ l * q₀ (a₀ l)) = x₀ k - liftMonomials y₀ (j₀ (x₀ k)) := by
      apply Subtype.val_injective (p := fun z : C => z ∈ V)
      change V.val (∑ l : t k, b₀ l * q₀ (a₀ l)) =
        V.val (x₀ k - liftMonomials y₀ (j₀ (x₀ k)))
      rw [map_sum, map_sub, liftMonomials_comp_inclusion (E := E) V.val y₀ y (fun _ => rfl), hj]
      change _ = (x₀ k : C) - liftMonomials y (j (x₀ k : C))
      rw [hx]
      simp only [map_mul, Subalgebra.val_apply, hq, a₀, b₀]
      exact hb k
    rw [← eq]
    exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _
      (Ideal.mem_map_of_mem q₀.toAlgHom.toRingHom (haug l)))

end KernelDenominator



section Centrality

private theorem centrality_of_compatible_coproducts
    {R E U V X Y : Type u} [CommRing R] [IsDomain R] [Field E] [Algebra R E]
    [IsFractionRing R E] [CommRing U] [Algebra R U] [CommRing V] [Algebra R V]
    [CommRing X] [Algebra R X] [Algebra E X] [IsScalarTower R E X]
    [CommRing Y] [Algebra R Y] [Algebra E Y] [IsScalarTower R E Y]
    [Module.Flat R V] [Module.Flat R X]
    (i : U →ₐ[R] X) (z : V →ₐ[R] Y) (hi : Function.Injective i) (hz : Function.Injective z)
    (Δ₀ : U →ₐ[R] U ⊗[R] U) (Δ : X →ₐ[E] X ⊗[E] X)
    (j₀ : U →ₐ[R] V) (j : X →ₐ[E] Y)
    (hΔ : ∀ x, tensorComparison R E i i (Δ₀ x) = Δ (i x))
    (hj : ∀ x, z (j₀ x) = j (i x))
    (h : ((map (AlgHom.id E X) j).comp Δ) =
      (Algebra.TensorProduct.comm E Y X).toAlgHom.comp ((map j (AlgHom.id E X)).comp Δ)) :
    ((map (AlgHom.id R U) j₀).comp Δ₀) =
      (Algebra.TensorProduct.comm R V U).toAlgHom.comp ((map j₀ (AlgHom.id R U)).comp Δ₀) := by
  let flip₀ := Algebra.TensorProduct.comm R V U
  let flip := Algebra.TensorProduct.comm E Y X
  have compare : (tensorComparison R E i z).comp flip₀.toAlgHom =
      (flip.toAlgHom.restrictScalars R).comp (tensorComparison R E z i) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.restrictScalars_apply, flip₀, flip,
      Algebra.TensorProduct.comm_tmul, tensorComparison_tmul]
  have hid (x : U) : i ((AlgHom.id R U) x) = (AlgHom.id E X) (i x) := rfl
  apply AlgHom.ext
  intro x
  apply tensorComparison_injective (E := E) i z hi hz
  change tensorComparison R E i z (map (AlgHom.id R U) j₀ (Δ₀ x)) =
    tensorComparison R E i z (flip₀ (map j₀ (AlgHom.id R U) (Δ₀ x)))
  have hf : tensorComparison R E i z (flip₀ (map j₀ (AlgHom.id R U) (Δ₀ x))) =
      flip (tensorComparison R E z i (map j₀ (AlgHom.id R U) (Δ₀ x))) :=
    DFunLike.congr_fun compare (map j₀ (AlgHom.id R U) (Δ₀ x))
  rw [hf, tensorComparison_natural (E := E) (b := i) (c := i) (d := i) (f := z) hid hj,
    tensorComparison_natural (E := E) (b := i) (c := i) (d := z) (f := i) hj hid, hΔ]
  exact DFunLike.congr_fun h (i x)

variable {R E U X M : Type u} [CommRing R] [IsDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E] [CommRing U] [HopfAlgebra R U] [CommRing X] [HopfAlgebra E X]
  [Algebra R X] [IsScalarTower R E X] [CommGroup M]

private theorem central_of_generic_central
    (e : GenericFibre R E U X) (eInj : Function.Injective e.inclusion)
    (j : X →ₐc[E] MonoidAlgebra E M) (j₀ : U →ₐc[R] MonoidAlgebra R M)
    (hj : ∀ x, groupAlgebraInclusion R E M (j₀ x) = j (e.inclusion x))
    (h : Specs.IntegralCentralQuotient.IsCentral j) :
    Specs.IntegralCentralQuotient.IsCentral j₀ := by
  let z := groupAlgebraInclusion R E M
  have hz : Function.Injective z := groupAlgebraInclusion_injective (IsFractionRing.injective R E)
  letI : Module.Flat R (MonoidAlgebra R M) := Module.Flat.of_free
  letI : Module.Flat R E := IsLocalization.flat E (nonZeroDivisors R)
  letI : Module.Flat R X := Module.Flat.trans R E X
  exact centrality_of_compatible_coproducts e.inclusion z eInj hz
    (Bialgebra.comulAlgHom R U) (Bialgebra.comulAlgHom E X) j₀.toAlgHom j.toAlgHom e.comul hj h

end Centrality

private theorem torus_characters_finitely_generated (I : Type) [Fintype I] :
    Monoid.FG (ULift.{u} (Multiplicative (I → ℤ))) := by
  apply Group.fg_iff_monoid_fg.mp
  have h : AddGroup.FG (I → ℤ) := by
    apply AddGroup.fg_def.mpr
    have hpi := AddSubgroup.FG.pi (P := fun _ : I => (⊤ : AddSubgroup ℤ))
      (fun _ => AddGroup.fg_def.mp (inferInstance : AddGroup.FG ℤ))
    have he : AddSubgroup.pi Set.univ (fun _ : I => (⊤ : AddSubgroup ℤ)) = ⊤ := by
      ext x
      simp [AddSubgroup.mem_pi]
    rwa [← he]
  letI : Group.FG (Multiplicative (I → ℤ)) := AddGroup.fg_iff_mul_fg.mp h
  let e : Multiplicative (I → ℤ) ≃* ULift.{u} (Multiplicative (I → ℤ)) := MulEquiv.ulift.symm
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective



set_option maxHeartbeats 1200000 in
/-- Spread the finite faithfully flat central cover, its marked diagonalizable
subgroups, and the given ambient immersion over one principal localization. -/
theorem centralCoverSpreading : Statement.{u} := by
  classical
  intro A E _ _ _ _ _ B C D _ _ _ _ _ _ _ _ _ I _ n hn generic ambient hamb hfin hff
  letI : Algebra A B := ((algebraMap E B).comp (algebraMap A E)).toAlgebra
  letI : Algebra A C := ((algebraMap E C).comp (algebraMap A E)).toAlgebra
  letI : IsScalarTower A E B := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A E C := IsScalarTower.of_algebraMap_eq' rfl
  letI (i : I) : NeZero (n i) := ⟨Nat.ne_of_gt (hn i)⟩
  let M := ULift.{u} (∀ i, Multiplicative (ZMod (n i)))
  let P := ULift.{u} (Multiplicative (I → ℤ))
  letI : Finite M := inferInstanceAs (Finite (ULift (∀ i, Multiplicative (ZMod (n i)))))
  letI : Monoid.FG M := Monoid.fg_of_finite
  letI : Monoid.FG P := torus_characters_finitely_generated I
  letI : Algebra B C := generic.cover.toAlgHom.toAlgebra
  letI : Module.Finite B C := hfin
  obtain ⟨m, x, hx⟩ := Module.Finite.exists_fin (R := B) (M := C)
  let f : D →ₐ[A] B := (ambient.restrictScalars A).comp includeRight
  obtain ⟨sD, hsD⟩ := Algebra.FiniteType.out (R := A) (A := D)
  let sB := sD.image f
  obtain ⟨sC, hsC⟩ := Algebra.FiniteType.out (R := E) (A := C)
  have hsB_eq : (sB : Set B) = f '' (sD : Set D) := Finset.coe_image
  have he : extendAmbientMap (R := E) f = ambient := by
    apply Algebra.TensorProduct.ext'
    intro a z
    rw [extendAmbientMap_tmul]
    have hz : a ⊗ₜ[A] z = algebraMap E (E ⊗[A] D) a * (1 ⊗ₜ[A] z) := by
      change a ⊗ₜ[A] z = (a ⊗ₜ[A] (1 : D)) * ((1 : E) ⊗ₜ[A] z)
      rw [tmul_mul_tmul, mul_one, one_mul]
    rw [hz, map_mul, AlgHom.commutes]
    rfl
  have hsB : Algebra.adjoin E (sB : Set B) = ⊤ := by
    rw [hsB_eq, ← extendAmbientMap_range (R := E) f _ hsD, he, AlgHom.range_eq_top]
    exact hamb
  obtain ⟨aB, haB, hOB⟩ := exists_hopf_denominator (A := A) sB hsB
  obtain ⟨aC, haC, hOC⟩ := exists_hopf_denominator (A := A) sC hsC
  obtain ⟨aQ, haQ, hQ⟩ := exists_cover_denominator (A := A) sB hsB sC hsC
    generic.cover.toAlgHom hfin hff x hx
  obtain ⟨aT, haT, hT⟩ := exists_marked_map_denominator (A := A) (M := P) sC hsC
    generic.sourceTorus.toAlgHom generic.sourceTorusClosed
  obtain ⟨aS, haS, hS⟩ := exists_marked_map_denominator (A := A) (M := P) sB hsB
    generic.targetTorus.toAlgHom generic.targetTorusClosed
  obtain ⟨aN, haN, hN⟩ := exists_marked_map_denominator (A := A) (M := M) sC hsC
    generic.kernel.toAlgHom generic.kernelFull.1
  obtain ⟨aK, haK, hK⟩ := exists_kernel_denominator (A := A) (M := M) sB hsB sC hsC
    generic.cover generic.kernel generic.kernelFull x
  let a : Fin 7 → A := ![aB, aC, aQ, aT, aS, aN, aK]
  have ha (i : Fin 7) : a i ≠ 0 := by
    fin_cases i <;> simp [a, haB, haC, haQ, haT, haS, haN, haK]
  obtain ⟨d, hd, hdiv⟩ := exists_common_multiple a ha
  let R := Localization.Away d
  let rE := (localizationMap (E := E) d hd).toAlgebra
  letI : Algebra R E := rE
  let hAE := localization_tower (E := E) d hd
  letI : IsScalarTower A R E := hAE
  refine ⟨d, hd, rE, hAE, ?_⟩
  letI : IsDedekindDomain R := localization_dedekind d hd
  letI : IsFractionRing R E := localization_fractionRing d hd
  letI : Algebra R B := ((algebraMap E B).comp (algebraMap R E)).toAlgebra
  letI : Algebra R C := ((algebraMap E C).comp (algebraMap R E)).toAlgebra
  letI : IsScalarTower R E B := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R E C := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A R B := IsScalarTower.to₁₂₄ A R E B
  letI : IsScalarTower A R C := IsScalarTower.to₁₂₄ A R E C
  have hu (i : Fin 7) : IsUnit (algebraMap A R (a i)) :=
    IsLocalization.Away.isUnit_of_dvd (S := R) d (hdiv i)
  have hi := IsFractionRing.injective R E
  obtain ⟨oB⟩ := hOB R (hu 0)
  obtain ⟨oC⟩ := hOC R (hu 1)
  let U := Algebra.adjoin R (sB : Set B)
  let V := Algebra.adjoin R (sC : Set C)
  letI : HopfAlgebra R U := oB.hopfAlgebra Subtype.val_injective
  letI : HopfAlgebra R V := oC.hopfAlgebra Subtype.val_injective
  let eB : GenericFibre R E U B :=
    ⟨U.val, adjoin_isBaseChange (A := R) _ hsB, oB.comul_agrees, oB.counit_agrees, oB.antipode_agrees⟩
  let eC : GenericFibre R E V C :=
    ⟨V.val, adjoin_isBaseChange (A := R) _ hsC, oC.comul_agrees, oC.counit_agrees, oC.antipode_agrees⟩
  let eT : GenericFibre R E (TorusCoordinates R I) (TorusCoordinates E I) := groupAlgebraGenericFibre
  let eN : GenericFibre R E (KernelCoordinates R n) (KernelCoordinates E n) := groupAlgebraGenericFibre
  obtain ⟨q, x₀, hq, hx₀, hs₀, hfin₀, hff₀⟩ := hQ R (hu 2)
  obtain ⟨t, ht, ht₀⟩ := hT R (hu 3) hi
  obtain ⟨s, hs, hs₁⟩ := hS R (hu 4) hi
  obtain ⟨j, _, hj⟩ := hN R (hu 5) hi
  have hiT : Function.Injective eT.inclusion := groupAlgebraInclusion_injective hi
  have hiN : Function.Injective eN.inclusion := groupAlgebraInclusion_injective hi
  let cover := restrictBialgebraHom eB eC Subtype.val_injective generic.cover q hq
  let sourceTorus := restrictBialgebraHom eC eT hiT generic.sourceTorus t ht₀
  let targetTorus := restrictBialgebraHom eB eT hiT generic.targetTorus s hs₁
  let kernel := restrictBialgebraHom eC eN hiN generic.kernel j hj
  have hSquare : sourceTorus.comp cover = (powerPullback R n).comp targetTorus := by
    apply BialgHom.ext
    intro b
    apply hiT
    change groupAlgebraInclusion R E P (t (q b)) =
      groupAlgebraInclusion R E P (powerPullback R n (s b))
    rw [ht₀, hq, groupAlgebraInclusion_commutes_with_character_map, hs₁]
    exact DFunLike.congr_fun generic.torusSquare (b : B)
  let diag : Diagram R U V n :=
    ⟨cover, sourceTorus, targetTorus, kernel, ht, hs, hSquare,
      hK R (hu 6) oB oC cover kernel x₀ hq hj hx₀ hs₀,
      central_of_generic_central eC Subtype.val_injective generic.kernel kernel hj
        generic.kernelCentral⟩
  have hU : U = Algebra.adjoin R (f '' (sD : Set D)) := congrArg (Algebra.adjoin R) hsB_eq
  let ambient₀ : R ⊗[A] D →ₐ[R] U := (extendAmbientMap f).codRestrict U fun z =>
    (hU.trans (extendAmbientMap_range (R := R) f _ hsD).symm).symm ▸
      (show extendAmbientMap (R := R) f z ∈ (extendAmbientMap (R := R) f).range from ⟨z, rfl⟩)
  have hAmbient₀ : Function.Surjective ambient₀ := by
    intro z
    have hz : (z : B) ∈ (extendAmbientMap (R := R) f).range :=
      (hU.trans (extendAmbientMap_range (R := R) f _ hsD).symm) ▸ z.property
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, Subtype.ext hw⟩
  have hBU : Algebra.FiniteType R U := .adjoin_of_finite sB.finite_toSet
  have hCV : Algebra.FiniteType R V := .adjoin_of_finite sC.finite_toSet
  have hUFlat : Module.Flat R U :=
    flat_of_injective_into_field_module (E := E) U.val Subtype.val_injective
  have hCoverPresentation : letI := diag.cover.toAlgHom.toAlgebra; Algebra.FinitePresentation U V := by
    letI : Algebra U V := q.toAlgebra
    letI : Module.Finite U V := hfin₀
    letI : IsNoetherianRing U := Algebra.FiniteType.isNoetherianRing R U
    have hf : (algebraMap U V).Finite := RingHom.finite_algebraMap.mpr hfin₀
    exact Algebra.FinitePresentation.of_finiteType.mp
      (RingHom.finiteType_algebraMap.mp hf.finiteType)
  refine ⟨{ target := U
            source := V
            diagram := diag
            targetPresentation := Algebra.FinitePresentation.of_finiteType.mp hBU
            sourcePresentation := Algebra.FinitePresentation.of_finiteType.mp hCV
            torusPresentation := monoidAlgebraFinitePresentation (M := P)
            kernelPresentation := monoidAlgebraFinitePresentation (M := M)
            targetFlat := hUFlat
            coverFinite := hfin₀
            coverFaithfullyFlat := hff₀
            coverPresentation := hCoverPresentation
            coverTorsor := fullKernelRightTorsor diag.cover diag.kernel diag.kernelFull
              hfin₀ hff₀ hCoverPresentation
            ambientMap := ambient₀
            ambientClosed := hAmbient₀
            genericTarget := eB
            genericSource := eC
            coverAgrees := hq
            sourceTorusAgrees := ht₀
            targetTorusAgrees := hs₁
            kernelAgrees := hj
            ambientAgrees := ?_ }⟩
  intro z
  change extendAmbientMap f ((1 : R) ⊗ₜ[A] z) = _
  rw [extendAmbientMap_tmul, map_one, one_mul]
  rfl



section CoordinateBridges

variable {R E U X : Type u} [CommRing R] [CommRing E] [Algebra R E]
  [CommRing U] [HopfAlgebra R U] [CommRing X] [HopfAlgebra E X]
  [Algebra R X] [IsScalarTower R E X]

/-- The generic fibre comparison induces the algebra isomorphism of the
scalar extension, taking each integral function to its specified image. -/
noncomputable def genericFibreAlgEquiv (f : GenericFibre R E U X) : E ⊗[R] U ≃ₐ[E] X :=
  letI : Algebra U X := f.inclusion.toAlgebra
  letI : IsScalarTower R U X := IsScalarTower.of_algebraMap_eq' f.inclusion.comp_algebraMap.symm
  letI : Algebra.IsPushout R E U X := ⟨f.baseChange⟩
  Algebra.IsPushout.equiv R E U X

@[simp] theorem genericFibreAlgEquiv_one_tmul (f : GenericFibre R E U X) (x : U) :
    genericFibreAlgEquiv f (1 ⊗ₜ[R] x) = f.inclusion x := by
  change f.baseChange.equiv (1 ⊗ₜ[R] x) = f.inclusion x
  rw [IsBaseChange.equiv_tmul, one_smul]
  rfl

end CoordinateBridges


end

end LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading
