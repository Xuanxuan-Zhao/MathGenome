import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.BasicNormalForm
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.PresentationSymmetries
import Mathlib.LinearAlgebra.DirectSum.Finsupp

noncomputable section

open scoped TensorProduct

namespace LieNotes.Quantum.BasicNormalForm

open Presentation PresentationSymmetries
open Specs.LieNotes.Quantum.BasicNormalForm
open Specs.LieNotes.Quantum.PresentationSymmetries (InvertsCartan)

universe u v

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

section OrderedWords

private abbrev Word := List Root
private abbrev WordPair := Word × Word
private abbrev OrderedWords (T : Type v) [Zero T] := WordPair →₀ T

variable (C : Cartan A T)

private def shiftWord : Word → T ≃ₐ[A] T
  | [] => AlgEquiv.refl
  | j :: w => (C.tau j).symm.trans (shiftWord w)

@[simp] private theorem shiftWord_nil (x : T) :
    shiftWord C [] x = x := rfl

@[simp] private theorem shiftWord_cons (j : Root) (w : Word) (x : T) :
    shiftWord C (j :: w) x = shiftWord C w ((C.tau j).symm x) := rfl

private def negativeAction (j : Root) : Module.End A (OrderedWords T) :=
  Finsupp.lsum A fun p => Finsupp.lsingle (j :: p.1, p.2)

@[simp] private theorem negativeAction_single (j : Root) (w v : Word) (t : T) :
    negativeAction (A := A) j (Finsupp.single (w, v) t) =
      Finsupp.single (j :: w, v) t := by
  simp [negativeAction, Finsupp.lsum_single]

private def cartanActionLinear (x : T) : Module.End A (OrderedWords T) :=
  Finsupp.lsum A fun p =>
    (Finsupp.lsingle p).comp (LinearMap.mul A T (shiftWord C p.1 x))

@[simp] private theorem cartanActionLinear_single (x : T) (w v : Word) (t : T) :
    cartanActionLinear C x (Finsupp.single (w, v) t) =
      Finsupp.single (w, v) (shiftWord C w x * t) := by
  simp [cartanActionLinear, Finsupp.lsum_single]

private def cartanAction : T →ₐ[A] Module.End A (OrderedWords T) where
  toFun := cartanActionLinear C
  map_zero' := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    simp
  map_add' x y := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    simp [add_mul, Finsupp.single_add]
  map_one' := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    simp
  map_mul' x y := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    simp [Module.End.mul_apply, mul_assoc]
  commutes' a := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    simp [Module.algebraMap_end_apply, Finsupp.smul_single, Algebra.smul_def]

@[simp] private theorem cartanAction_single (x : T) (w v : Word) (t : T) :
    cartanAction C x (Finsupp.single (w, v) t) =
      Finsupp.single (w, v) (shiftWord C w x * t) :=
  cartanActionLinear_single C x w v t

/-- Recursively commute a positive generator past the negative word. -/
private def positiveOnWord (i : Root) (v : Word) : Word → T →ₗ[A] OrderedWords T
  | [] => (Finsupp.lsingle ([], i :: v)).comp (C.tau i).symm.toLinearMap
  | j :: w => (negativeAction j).comp (positiveOnWord i v w) +
      (Finsupp.lsingle (w, v)).comp (LinearMap.mul A T (shiftWord C w (mixed C i j)))

private def positiveAction (i : Root) : Module.End A (OrderedWords T) :=
  Finsupp.lsum A fun p => positiveOnWord C i p.2 p.1

@[simp] private theorem positiveAction_single_nil (i : Root) (v : Word) (t : T) :
    positiveAction C i (Finsupp.single ([], v) t) =
      Finsupp.single ([], i :: v) ((C.tau i).symm t) := by
  simp [positiveAction, Finsupp.lsum_single, positiveOnWord]

private theorem positiveAction_single_cons (i j : Root) (w v : Word) (t : T) :
    positiveAction C i (Finsupp.single (j :: w, v) t) =
      negativeAction (A := A) j (positiveAction C i (Finsupp.single (w, v) t)) +
        Finsupp.single (w, v) (shiftWord C w (mixed C i j) * t) := by
  simp [positiveAction, Finsupp.lsum_single, positiveOnWord]

private theorem cartanAction_negative (x : T) (j : Root) :
    cartanAction C x * negativeAction j =
      negativeAction j * cartanAction C ((C.tau j).symm x) := by
  apply Finsupp.lhom_ext
  rintro ⟨w, v⟩ t
  simp [Module.End.mul_apply]

private theorem inverse_commute
    (h : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j)) (i j : Root) (x : T) :
    (C.tau i).symm ((C.tau j).symm x) = (C.tau j).symm ((C.tau i).symm x) := by
  apply (C.tau i).injective
  apply (C.tau j).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [(h j i).eq, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

private theorem positiveAction_cartan
    (h : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j)) (i : Root) (x : T) :
    positiveAction C i * cartanAction C x =
      cartanAction C ((C.tau i).symm x) * positiveAction C i := by
  apply Finsupp.lhom_ext
  rintro ⟨w, v⟩ t
  simp only [Module.End.mul_apply]
  induction w generalizing x t with
  | nil => simp
  | cons j w ih =>
      rw [cartanAction_single, shiftWord_cons, positiveAction_single_cons,
        positiveAction_single_cons, map_add]
      have htail := ih ((C.tau j).symm x) t
      rw [cartanAction_single] at htail
      rw [htail]
      rw [show cartanAction C ((C.tau i).symm x)
            (negativeAction j (positiveAction C i (Finsupp.single (w, v) t))) =
          negativeAction j (cartanAction C ((C.tau j).symm ((C.tau i).symm x))
            (positiveAction C i (Finsupp.single (w, v) t))) from
        DFunLike.congr_fun (cartanAction_negative C ((C.tau i).symm x) j) _]
      rw [inverse_commute C h i j x, cartanAction_single]
      by_cases hij : i = j
      · subst j
        rw [mul_left_comm]
      · simp [Specs.LieNotes.Quantum.Presentation.mixed, hij]

private theorem actions_basic
    (h : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j)) :
    SatisfiesBasic C (cartanAction C) (positiveAction C) negativeAction where
  cartanF := cartanAction_negative C
  eCartan := positiveAction_cartan C h
  comm i j := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    simp [Module.End.mul_apply, positiveAction_single_cons]

private def wordRepresentation
    (h : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j)) :
    B₀ C →ₐ[A] Module.End A (OrderedWords T) :=
  liftBasic C (cartanAction C) (positiveAction C) negativeAction (actions_basic C h)

variable (h : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j))

@[simp] private theorem wordRepresentation_cartan (t : T) :
    wordRepresentation C h (cartan₀ C t) = cartanAction C t :=
  Specs.LieNotes.Quantum.Presentation.liftBasic_cartan C _ _ _ _ t

@[simp] private theorem wordRepresentation_E (i : Root) :
    wordRepresentation C h (E₀ C i) = positiveAction C i :=
  Specs.LieNotes.Quantum.Presentation.liftBasic_E C _ _ _ _ i

@[simp] private theorem wordRepresentation_F (j : Root) :
    wordRepresentation C h (F₀ C j) = negativeAction j :=
  Specs.LieNotes.Quantum.Presentation.liftBasic_F C _ _ _ _ j

private def writeWord : OrderedWords T →ₗ[A] B₀ C :=
  Finsupp.lsum A fun p =>
    ((LinearMap.mul A (B₀ C)).flip (p.2.map (E₀ C)).prod).comp
      ((LinearMap.mul A (B₀ C) (p.1.map (F₀ C)).prod).comp (cartan₀ C).toLinearMap)

@[simp] private theorem writeWord_single (w v : Word) (t : T) :
    writeWord C (Finsupp.single (w, v) t) =
      (w.map (F₀ C)).prod * cartan₀ C t * (v.map (E₀ C)).prod := by
  simp [writeWord, Finsupp.lsum_single]

/-- The normal coordinates of an element are obtained by acting on the empty word. -/
private def readWord : B₀ C →ₗ[A] OrderedWords T :=
  (LinearMap.applyₗ (R := A) (Finsupp.single ([], []) 1)).comp (wordRepresentation C h).toLinearMap

private theorem read_write : Function.LeftInverse (readWord C h) (writeWord C) := by
  have he (v : Word) :
      wordRepresentation C h (v.map (E₀ C)).prod (Finsupp.single ([], []) 1) =
        Finsupp.single ([], v) 1 := by
    induction v with
    | nil => simp
    | cons i v ih => simp [Module.End.mul_apply, ih]
  have hf (w v : Word) (t : T) :
      wordRepresentation C h (w.map (F₀ C)).prod (Finsupp.single ([], v) t) =
        Finsupp.single (w, v) t := by
    induction w with
    | nil => simp
    | cons j w ih => simp [Module.End.mul_apply, ih]
  have heq : (readWord C h).comp (writeWord C) = LinearMap.id := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    simp [readWord, Module.End.mul_apply, he, hf]
  exact DFunLike.congr_fun heq

private theorem write_action_of_single (f : Module.End A (OrderedWords T)) (b : B₀ C)
    (hf : ∀ (w v : Word) (t : T),
      writeWord C (f (Finsupp.single (w, v) t)) = b * writeWord C (Finsupp.single (w, v) t))
    (m : OrderedWords T) :
    writeWord C (f m) = b * writeWord C m := by
  have heq : (writeWord C).comp f = (LinearMap.mul A (B₀ C) b).comp (writeWord C) := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    exact hf w v t
  exact DFunLike.congr_fun heq m

private theorem write_negative (j : Root) (m : OrderedWords T) :
    writeWord C (negativeAction (A := A) j m) = F₀ C j * writeWord C m := by
  apply write_action_of_single
  intro w v t
  simp [mul_assoc]

private theorem write_cartan (x : T) (m : OrderedWords T) :
    writeWord C (cartanAction C x m) = cartan₀ C x * writeWord C m := by
  apply write_action_of_single
  intro w v t
  induction w generalizing x with
  | nil => simp [mul_assoc]
  | cons j w ih =>
      rw [show writeWord C (cartanAction C x (Finsupp.single (j :: w, v) t)) =
          writeWord C (cartanAction C x (negativeAction (A := A) j (Finsupp.single (w, v) t))) by
        rw [negativeAction_single]]
      rw [show cartanAction C x (negativeAction (A := A) j (Finsupp.single (w, v) t)) =
          negativeAction j (cartanAction C ((C.tau j).symm x) (Finsupp.single (w, v) t)) from
        DFunLike.congr_fun (cartanAction_negative C x j) _]
      rw [write_negative, ih, ← negativeAction_single (A := A) j w v t, write_negative]
      rw [← mul_assoc, ← mul_assoc, (basic_relations C).cartanF x j]

private theorem write_positive (i : Root) (m : OrderedWords T) :
    writeWord C (positiveAction C i m) = E₀ C i * writeWord C m := by
  apply write_action_of_single
  intro w v t
  induction w with
  | nil =>
      simp only [positiveAction_single_nil, writeWord_single, List.map_nil, List.prod_nil,
        one_mul, List.map_cons, List.prod_cons]
      rw [← mul_assoc, ← mul_assoc (E₀ C i), (basic_relations C).eCartan i t]
  | cons j w ih =>
      rw [positiveAction_single_cons, map_add, write_negative, ih,
        ← cartanAction_single C (mixed C i j) w v t, write_cartan,
        ← negativeAction_single (A := A) j w v t, write_negative]
      rw [← mul_assoc (F₀ C j), ← add_mul, ← mul_assoc (E₀ C i),
        sub_eq_iff_eq_add.mp ((basic_relations C).comm i j), add_comm (F₀ C j * E₀ C i)]

private theorem write_read : Function.RightInverse (readWord C h) (writeWord C) := by
  intro b
  let q := basicQuotient C
  have intertwines (r : Specs.LieNotes.Quantum.Presentation.Raw A T) :
      ∀ m, writeWord C (wordRepresentation C h (q r) m) = q r * writeWord C m := by
    induction r using FreeAlgebra.induction with
    | grade0 a =>
        intro m
        simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul, Algebra.smul_def]
    | grade1 x =>
        intro m
        rcases x with t | (i | j)
        · change writeWord C (wordRepresentation C h (cartan₀ C t) m) =
            cartan₀ C t * writeWord C m
          rw [wordRepresentation_cartan, write_cartan]
        · change writeWord C (wordRepresentation C h (E₀ C i) m) = E₀ C i * writeWord C m
          rw [wordRepresentation_E, write_positive]
        · change writeWord C (wordRepresentation C h (F₀ C j) m) = F₀ C j * writeWord C m
          rw [wordRepresentation_F, write_negative]
    | mul r s ihr ihs =>
        intro m
        simp only [map_mul, Module.End.mul_apply, ihr, ihs, mul_assoc]
    | add r s ihr ihs =>
        intro m
        simp only [map_add, LinearMap.add_apply, ihr, ihs, add_mul]
  have hq : Function.Surjective q :=
    Ideal.Quotient.mkₐ_surjective A (basicIdeal C).asIdeal
  obtain ⟨r, rfl⟩ := hq b
  simpa [readWord] using intertwines r (Finsupp.single ([], []) 1)

private def freeToWords (A : Type u) [CommRing A] : FreeAlgebra A Root ≃ₗ[A] (Word →₀ A) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv ≪≫ₗ
    MonoidAlgebra.coeffLinearEquiv A ≪≫ₗ Finsupp.domLCongr FreeMonoid.toList

private theorem lift_freeToWords_single {B : Type*} [Semiring B] [Algebra A B]
    (g : Root → B) (w : Word) :
    FreeAlgebra.lift A g ((freeToWords A).symm (Finsupp.single w 1)) = (w.map g).prod := by
  simp only [freeToWords, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Finsupp.domLCongr_symm, Finsupp.domLCongr_single, FreeMonoid.toList_symm]
  change FreeAlgebra.lift A g
    (MonoidAlgebra.lift A (FreeAlgebra A Root) (FreeMonoid Root)
      (FreeMonoid.lift (FreeAlgebra.ι A)) (MonoidAlgebra.single (FreeMonoid.ofList w) 1)) = _
  rw [MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_ofList, map_list_prod]
  simp [List.map_map, Function.comp_def]

private def tensorToWords (A : Type u) (T : Type v) [CommRing A] [CommRing T] [Algebra A T] :
    OrderedTensor A T ≃ₗ[A] OrderedWords T :=
  TensorProduct.congr
    (TensorProduct.congr (freeToWords A) (LinearEquiv.refl A T) ≪≫ₗ
      TensorProduct.finsuppScalarLeft A T Word)
    (freeToWords A) ≪≫ₗ
  finsuppTensorFinsuppRid A T Word Word

private theorem tensorToWords_symm_single (w v : Word) (t : T) :
    (tensorToWords A T).symm (Finsupp.single (w, v) t) =
      (((freeToWords A).symm (Finsupp.single w 1)) ⊗ₜ[A] t) ⊗ₜ[A]
        (freeToWords A).symm (Finsupp.single v 1) := by
  apply (tensorToWords A T).injective
  rw [LinearEquiv.apply_symm_apply]
  simp [tensorToWords, TensorProduct.finsuppScalarLeft_apply_tmul, Finsupp.sum_single_index]

include h in
/-- Ordered multiplication is bijective whenever the Cartan translations commute. -/
theorem hasNormalForm : HasNormalForm C := by
  have heq : (multiplication C).comp (tensorToWords A T).symm.toLinearMap = writeWord C := by
    apply Finsupp.lhom_ext
    rintro ⟨w, v⟩ t
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorToWords_symm_single,
      multiplication_tmul, writeWord_single, negative, positive, lift_freeToWords_single]
  have hmul : multiplication C = (writeWord C).comp (tensorToWords A T).toLinearMap := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      using DFunLike.congr_fun heq (tensorToWords A T x)
  rw [HasNormalForm, hmul]
  have hwrite : Function.Bijective (writeWord C) :=
    ⟨(read_write C h).injective, (write_read C h).surjective⟩
  exact hwrite.comp (tensorToWords A T).bijective

end OrderedWords

theorem generic_normalForm :
    Specs.LieNotes.Quantum.BasicNormalForm.GenericNormalForm.{u} := by
  intro k _ _ q hq
  exact hasNormalForm (generic q hq) (generic_commute q hq)

theorem indeterminate_normalForm :
    Specs.LieNotes.Quantum.BasicNormalForm.IndeterminateNormalForm.{u} := by
  intro k _ _
  exact generic_normalForm (rationalQ k)
    (Specs.LieNotes.Quantum.Presentation.rationalQ_sq_ne k)

theorem truncated_normalForm :
    Specs.LieNotes.Quantum.BasicNormalForm.TruncatedNormalForm.{u} := by
  intro k _ _ N _
  exact hasNormalForm (truncated k N) (truncated_commute N)

theorem hasBasicSymmetries {C : Cartan A T} (h : InvertsCartan C) :
    HasBasicSymmetries C :=
  ⟨omega₀ h, eta₀ C, ⟨omega₀_cartan h, omega₀_E h, omega₀_F h, omega₀_involutive h,
    eta₀_cartan, eta₀_E, eta₀_F, eta₀_involutive C⟩⟩

theorem generic_symmetries :
    Specs.LieNotes.Quantum.BasicNormalForm.GenericSymmetries.{u} := by
  intro k _ _ q hq
  exact ⟨hasBasicSymmetries (generic_invertsCartan q hq), generic_kappa_K q hq⟩

theorem indeterminate_symmetries :
    Specs.LieNotes.Quantum.BasicNormalForm.IndeterminateSymmetries.{u} := by
  intro k _ _
  exact generic_symmetries (rationalQ k)
    (Specs.LieNotes.Quantum.Presentation.rationalQ_sq_ne k)

theorem truncated_symmetries :
    Specs.LieNotes.Quantum.BasicNormalForm.TruncatedSymmetries.{u} := by
  intro k _ _ N _
  exact ⟨hasBasicSymmetries (truncated_invertsCartan k N), truncated_kappa_H N⟩

end LieNotes.Quantum.BasicNormalForm
