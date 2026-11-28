import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SerreIdeal
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.BasicNormalForm
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.SerreCrossCommutators
import Batteries.Tactic.OpenPrivate

noncomputable section

open scoped TensorProduct

namespace LieNotes.Quantum.SerreIdeal

open Specs.LieNotes.Quantum.BasicNormalForm
open Specs.LieNotes.Quantum.SerreIdeal
open Specs.LieNotes.Quantum.SerreCrossCommutators (CrossCommutators)
open Presentation
open Specs.LieNotes.Quantum.SerrePresentation (serrePolynomial relationXY relationYX)

universe u v

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
variable (C : Cartan A T)

private abbrev Free (A : Type u) [CommRing A] := FreeAlgebra A Root

private def positiveImage : Submodule A (B₀ C) := (positiveRange C).map (multiplication C)
private def negativeImage : Submodule A (B₀ C) := (negativeRange C).map (multiplication C)

private theorem tripleTensor_induction {X : Type*} {Y : Type*}
    [AddCommMonoid X] [Module A X] [AddCommMonoid Y] [Module A Y]
    {P : (X ⊗[A] T) ⊗[A] Y → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hpure : ∀ f t e, P ((f ⊗ₜ[A] t) ⊗ₜ[A] e))
    (x : (X ⊗[A] T) ⊗[A] Y) : P x := by
  refine TensorProduct.inductionOn x (fun z e => ?_) hadd
  refine TensorProduct.inductionOn (motive := fun z => P (z ⊗ₜ[A] e)) z
    (fun f t => hpure f t e) ?_
  intro x y hx hy
  rw [TensorProduct.add_tmul]
  exact hadd _ _ hx hy

private theorem ordered_induction (h : HasNormalForm C) {P : B₀ C → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hpure : ∀ f t e, P (negative C f * cartan₀ C t * positive C e))
    (x : B₀ C) : P x := by
  obtain ⟨z, rfl⟩ := h.surjective x
  refine tripleTensor_induction (P := fun z => P (multiplication C z)) ?_ ?_ z
  · simpa only [map_add] using fun z w => hadd (multiplication C z) (multiplication C w)
  · simpa only [multiplication_tmul] using hpure

private theorem positiveImage_induction {P : B₀ C → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hpure : ∀ f t (e : freeSerreSubmodule C.q),
      P (negative C f * cartan₀ C t * positive C e))
    {x : B₀ C} (hx : x ∈ positiveImage C) : P x := by
  rcases hx with ⟨_, ⟨z, rfl⟩, rfl⟩
  let m := (multiplication C).comp
    (TensorProduct.map (LinearMap.id (M := Free A ⊗[A] T))
      (freeSerreSubmodule C.q).subtype)
  change P (m z)
  refine tripleTensor_induction (P := fun z => P (m z)) ?_ ?_ z
  · simpa only [map_add] using fun z w => hadd (m z) (m w)
  · simpa only [m, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply, multiplication_tmul] using hpure

private theorem negativeImage_induction {P : B₀ C → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hpure : ∀ (f : freeSerreSubmodule C.q) t e,
      P (negative C f * cartan₀ C t * positive C e))
    {x : B₀ C} (hx : x ∈ negativeImage C) : P x := by
  rcases hx with ⟨_, ⟨z, rfl⟩, rfl⟩
  let m := (multiplication C).comp
    (TensorProduct.map
      (TensorProduct.map (freeSerreSubmodule C.q).subtype (LinearMap.id (M := T)))
      (LinearMap.id (M := Free A)))
  change P (m z)
  refine tripleTensor_induction (P := fun z => P (m z)) ?_ ?_ z
  · simpa only [map_add] using fun z w => hadd (m z) (m w)
  · simpa only [m, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply, multiplication_tmul] using hpure

private theorem positiveImage_monomial (f : Free A) (t : T) (e : freeSerreSubmodule C.q) :
    negative C f * cartan₀ C t * positive C e ∈ positiveImage C := by
  refine ⟨(f ⊗ₜ[A] t) ⊗ₜ[A] (e : Free A), ?_, multiplication_tmul C f t e⟩
  refine ⟨(f ⊗ₜ[A] t) ⊗ₜ[A] e, ?_⟩
  simp

private theorem negativeImage_monomial (f : freeSerreSubmodule C.q) (t : T) (e : Free A) :
    negative C f * cartan₀ C t * positive C e ∈ negativeImage C := by
  refine ⟨((f : Free A) ⊗ₜ[A] t) ⊗ₜ[A] e, ?_, multiplication_tmul C f t e⟩
  refine ⟨(f ⊗ₜ[A] t) ⊗ₜ[A] e, ?_⟩
  simp

private theorem positiveImage_mul_positive (h : HasNormalForm C)
    (b : B₀ C) (e : freeSerreSubmodule C.q) : b * positive C e ∈ positiveImage C := by
  refine ordered_induction C h (P := fun b => b * positive C e ∈ positiveImage C) ?_ ?_ b
  · intro x y hx hy
    rw [add_mul]
    exact (positiveImage C).add_mem hx hy
  · intro f t p
    rw [mul_assoc, ← map_mul]
    exact positiveImage_monomial C f t
      ⟨p * e, (Specs.LieNotes.Quantum.SerrePresentation.serreIdeal C.q).mul_mem_left p _ e.property⟩

private theorem positiveImage_left (h : HasNormalForm C) (b : B₀ C) {x : B₀ C}
    (hx : x ∈ positiveImage C) : b * x ∈ positiveImage C := by
  refine positiveImage_induction C (P := fun x => b * x ∈ positiveImage C) ?_ ?_ hx
  · intro x y hx hy
    rw [mul_add]
    exact (positiveImage C).add_mem hx hy
  · intro f t e
    rw [← mul_assoc]
    exact positiveImage_mul_positive C h (b * (negative C f * cartan₀ C t)) e

private theorem positiveImage_right_positive (p : Free A) {x : B₀ C}
    (hx : x ∈ positiveImage C) : x * positive C p ∈ positiveImage C := by
  refine positiveImage_induction C (P := fun x => x * positive C p ∈ positiveImage C)
    ?_ ?_ hx
  · intro x y hx hy
    rw [add_mul]
    exact (positiveImage C).add_mem hx hy
  · intro f t e
    rw [mul_assoc, ← map_mul]
    exact positiveImage_monomial C f t
      ⟨e * p, (Specs.LieNotes.Quantum.SerrePresentation.serreIdeal C.q).mul_mem_right _ p e.property⟩


@[simp] private theorem positive_ι (i : Root) :
    positive C (FreeAlgebra.ι A i) = E₀ C i := FreeAlgebra.lift_ι_apply _ _
@[simp] private theorem negative_ι (i : Root) :
    negative C (FreeAlgebra.ι A i) = F₀ C i := FreeAlgebra.lift_ι_apply _ _

private def freeSerre (q : Aˣ) (i j : Root) : Free A :=
  serrePolynomial q (FreeAlgebra.ι A i) (FreeAlgebra.ι A j)

private theorem freeSerre_mem (q : Aˣ) (i j : Root) (hij : i ≠ j) :
    freeSerre q i j ∈ freeSerreSubmodule q := by
  apply TwoSidedIdeal.subset_span
  change freeSerre q i j = relationXY q ∨ freeSerre q i j = relationYX q
  fin_cases i <;> fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | contradiction

@[simp] private theorem positive_freeSerre (i j : Root) :
    positive C (freeSerre C.q i j) = serrePolynomial C.q (E₀ C i) (E₀ C j) := by
  simp only [freeSerre, serrePolynomial, map_pow, map_mul, map_sub, map_add, map_smul, positive_ι]

@[simp] private theorem negative_freeSerre (i j : Root) :
    negative C (freeSerre C.q i j) = serrePolynomial C.q (F₀ C i) (F₀ C j) := by
  simp only [freeSerre, serrePolynomial, map_pow, map_mul, map_sub, map_add, map_smul, negative_ι]

private theorem positiveImage_serre (i j : Root) (hij : i ≠ j) :
    serrePolynomial C.q (E₀ C i) (E₀ C j) ∈ positiveImage C := by
  simpa only [map_one, one_mul, positive_freeSerre] using
    positiveImage_monomial C 1 1 ⟨freeSerre C.q i j, freeSerre_mem C.q i j hij⟩

private theorem free_induction_right {P : Free A → Prop} (hone : P 1)
    (hsmul : ∀ (a : A) p, P p → P (a • p)) (hadd : ∀ p r, P p → P r → P (p + r))
    (hgen : ∀ p i, P p → P (p * FreeAlgebra.ι A i)) (x : Free A) : P x := by
  suffices h : ∀ p, P p → P (p * x) by simpa only [one_mul] using h 1 hone
  induction x using FreeAlgebra.induction with
  | grade0 a =>
    intro p hp
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
    exact hsmul a p hp
  | grade1 i => exact fun p hp => hgen p i hp
  | mul x y hx hy =>
    intro p hp
    rw [← mul_assoc]
    exact hy _ (hx _ hp)
  | add x y hx hy =>
    intro p hp
    rw [mul_add]
    exact hadd _ _ (hx _ hp) (hy _ hp)

private theorem positiveImage_right_of_serre (h : HasNormalForm C) (b : B₀ C)
    (hgen : ∀ i j : Root, i ≠ j → ∀ p : Free A,
      serrePolynomial C.q (E₀ C i) (E₀ C j) * positive C p * b ∈ positiveImage C)
    {x : B₀ C} (hx : x ∈ positiveImage C) : x * b ∈ positiveImage C := by
  have hs (e : Free A) (he : e ∈ freeSerreSubmodule C.q) :
      ∀ p : Free A, positive C (e * p) * b ∈ positiveImage C := by
    change e ∈ TwoSidedIdeal.span {relationXY C.q, relationYX C.q} at he
    induction he using TwoSidedIdeal.span_induction with
    | mem r hr =>
      change r = relationXY C.q ∨ r = relationYX C.q at hr
      rcases hr with rfl | rfl
      · intro p
        simpa only [show relationXY C.q = freeSerre C.q 0 1 from rfl, map_mul,
          positive_freeSerre] using hgen 0 1 (by decide) p
      · intro p
        simpa only [show relationYX C.q = freeSerre C.q 1 0 from rfl, map_mul,
          positive_freeSerre] using hgen 1 0 (by decide) p
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ =>
      intro p
      rw [add_mul, map_add, add_mul]
      exact (positiveImage C).add_mem (h₁ p) (h₂ p)
    | neg x _ hx =>
      intro p
      rw [neg_mul, map_neg, neg_mul]
      exact (positiveImage C).neg_mem (hx p)
    | left_absorb a x _ hx =>
      intro p
      rw [mul_assoc, map_mul, mul_assoc]
      exact positiveImage_left C h _ (hx p)
    | right_absorb a x _ hx =>
      intro p
      rw [mul_assoc]
      exact hx (a * p)
  refine positiveImage_induction C (P := fun x => x * b ∈ positiveImage C) ?_ ?_ hx
  · intro x y hx hy
    rw [add_mul]
    exact (positiveImage C).add_mem hx hy
  · intro f t e
    rw [mul_assoc]
    exact positiveImage_left C h _ (by simpa only [mul_one] using hs e e.property 1)

open private inverse_commute from MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.BasicNormalForm

private theorem three_cartan (i j l : Root) (t : T) :
    (E₀ C i * E₀ C j * E₀ C l) * cartan₀ C t =
      cartan₀ C ((C.tau i).symm ((C.tau j).symm ((C.tau l).symm t))) *
        (E₀ C i * E₀ C j * E₀ C l) := by
  calc
    _ = E₀ C i * (E₀ C j * (E₀ C l * cartan₀ C t)) := by simp only [mul_assoc]
    _ = _ := by
      rw [(basic_relations C).eCartan l, ← mul_assoc (E₀ C j), (basic_relations C).eCartan j,
        mul_assoc, ← mul_assoc (E₀ C i), (basic_relations C).eCartan i]
      simp only [mul_assoc]

private theorem serre_cartan (hc : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j))
    (i j : Root) (t : T) :
    serrePolynomial C.q (E₀ C i) (E₀ C j) * cartan₀ C t =
      cartan₀ C ((C.tau i).symm ((C.tau i).symm ((C.tau j).symm t))) *
        serrePolynomial C.q (E₀ C i) (E₀ C j) := by
  have h₁ : (C.tau i).symm ((C.tau j).symm ((C.tau i).symm t)) =
      (C.tau i).symm ((C.tau i).symm ((C.tau j).symm t)) :=
    congrArg (C.tau i).symm (inverse_commute C hc j i t)
  have h₂ : (C.tau j).symm ((C.tau i).symm ((C.tau i).symm t)) =
      (C.tau i).symm ((C.tau i).symm ((C.tau j).symm t)) :=
    (inverse_commute C hc j i ((C.tau i).symm t)).trans h₁
  simp only [serrePolynomial, pow_two]
  rw [← mul_assoc (E₀ C j) (E₀ C i) (E₀ C i)]
  simp only [sub_mul, add_mul, smul_mul_assoc, three_cartan, h₁, h₂, mul_add, mul_sub, mul_smul_comm]

private theorem serre_word_right_cartan (h : HasNormalForm C)
    (hc : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j))
    (i j : Root) (hij : i ≠ j) (p : Free A) (t : T) :
    serrePolynomial C.q (E₀ C i) (E₀ C j) * positive C p * cartan₀ C t ∈ positiveImage C := by
  let S := serrePolynomial C.q (E₀ C i) (E₀ C j)
  change S * positive C p * cartan₀ C t ∈ positiveImage C
  refine free_induction_right (P := fun p => ∀ t, S * positive C p * cartan₀ C t ∈ positiveImage C)
    ?_ ?_ ?_ ?_ p t
  · intro t
    rw [map_one, mul_one, serre_cartan C hc]
    exact positiveImage_left C h _ (positiveImage_serre C i j hij)
  · intro a p hp t
    rw [map_smul, mul_smul_comm, smul_mul_assoc]
    exact (positiveImage C).smul_mem a (hp t)
  · intro p r hp hr t
    rw [map_add, mul_add, add_mul]
    exact (positiveImage C).add_mem (hp t) (hr t)
  · intro p l hp t
    rw [map_mul, positive_ι, ← mul_assoc S, mul_assoc (S * positive C p),
      (basic_relations C).eCartan, ← mul_assoc]
    simpa only [positive_ι] using
      positiveImage_right_positive C (FreeAlgebra.ι A l) (hp ((C.tau l).symm t))

private theorem serre_word_right_F (h : HasNormalForm C)
    (hc : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j)) (hx : CrossCommutators C)
    (i j : Root) (hij : i ≠ j) (p : Free A) (l : Root) :
    serrePolynomial C.q (E₀ C i) (E₀ C j) * positive C p * F₀ C l ∈ positiveImage C := by
  let S := serrePolynomial C.q (E₀ C i) (E₀ C j)
  change S * positive C p * F₀ C l ∈ positiveImage C
  refine free_induction_right (P := fun p => S * positive C p * F₀ C l ∈ positiveImage C)
    ?_ ?_ ?_ ?_ p
  · rw [map_one, mul_one, (hx i j hij l).1.eq]
    exact positiveImage_left C h _ (positiveImage_serre C i j hij)
  · intro a p hp
    rw [map_smul, mul_smul_comm, smul_mul_assoc]
    exact (positiveImage C).smul_mem a hp
  · intro p r hp hr
    rw [map_add, mul_add, add_mul]
    exact (positiveImage C).add_mem hp hr
  · intro p a hp
    have ha := sub_eq_iff_eq_add.mp ((basic_relations C).comm a l)
    rw [map_mul, positive_ι, ← mul_assoc S, mul_assoc (S * positive C p), ha, mul_add]
    refine (positiveImage C).add_mem (serre_word_right_cartan C h hc i j hij p _) ?_
    rw [← mul_assoc]
    simpa only [positive_ι] using positiveImage_right_positive C (FreeAlgebra.ι A a) hp

private theorem positiveImage_right (h : HasNormalForm C)
    (hc : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j)) (hx : CrossCommutators C)
    (b : B₀ C) {x : B₀ C} (hx' : x ∈ positiveImage C) : x * b ∈ positiveImage C := by
  have hf (f : Free A) : ∀ x ∈ positiveImage C, x * negative C f ∈ positiveImage C := by
    induction f using FreeAlgebra.induction with
    | grade0 a =>
      intro x hx
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      exact (positiveImage C).smul_mem a hx
    | grade1 i =>
      simp only [negative_ι]
      exact fun x hx' => positiveImage_right_of_serre C h _
        (fun i' j hij p => serre_word_right_F C h hc hx i' j hij p i) hx'
    | mul f g hf hg =>
      intro x hx
      rw [map_mul, ← mul_assoc]
      exact hg _ (hf _ hx)
    | add f g hf hg =>
      intro x hx
      rw [map_add, mul_add]
      exact (positiveImage C).add_mem (hf _ hx) (hg _ hx)
  refine ordered_induction C h (P := fun b => x * b ∈ positiveImage C) ?_ ?_ b
  · intro b d hb hd
    rw [mul_add]
    exact (positiveImage C).add_mem hb hd
  · intro f t e
    rw [← mul_assoc, ← mul_assoc]
    exact positiveImage_right_positive C e
      (positiveImage_right_of_serre C h _ (fun i j hij p => serre_word_right_cartan C h hc i j hij p t)
        (hf f x hx'))


section Reversal

open MulOpposite
open LieNotes.Quantum.PresentationSymmetries
open private unop_serre from MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.PresentationSymmetries

private def reverseFree (A : Type u) [CommRing A] : Free A →ₐ[A] (Free A)ᵐᵒᵖ :=
  FreeAlgebra.lift A (fun i => op (FreeAlgebra.ι A i))

@[simp] private theorem reverseFree_ι (i : Root) :
    reverseFree A (FreeAlgebra.ι A i) = op (FreeAlgebra.ι A i) :=
  FreeAlgebra.lift_ι_apply _ _

private theorem reverseFree_serre (q : Aˣ) (i j : Root) :
    unop (reverseFree A (freeSerre q i j)) = freeSerre q i j := by
  have hh :
      reverseFree A (freeSerre q i j) =
        serrePolynomial q (op (FreeAlgebra.ι A i)) (op (FreeAlgebra.ι A j)) := by
    simp only [freeSerre, serrePolynomial, map_pow, map_mul, map_sub, map_add, map_smul,
      reverseFree_ι]
  rw [hh, unop_serre]
  rfl

private theorem reverseFree_mem (q : Aˣ) (e : freeSerreSubmodule q) :
    unop (reverseFree A e) ∈ freeSerreSubmodule q := by
  obtain ⟨e, he⟩ := e
  change e ∈ TwoSidedIdeal.span {relationXY q, relationYX q} at he
  change unop (reverseFree A e) ∈ Specs.LieNotes.Quantum.SerrePresentation.serreIdeal q
  induction he using TwoSidedIdeal.span_induction with
  | mem x hx =>
    change x = relationXY q ∨ x = relationYX q at hx
    rcases hx with rfl | rfl
    · change unop (reverseFree A (freeSerre q 0 1)) ∈ _
      rw [reverseFree_serre]
      exact freeSerre_mem q 0 1 (by decide)
    · change unop (reverseFree A (freeSerre q 1 0)) ∈ _
      rw [reverseFree_serre]
      exact freeSerre_mem q 1 0 (by decide)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, unop_add]
    exact TwoSidedIdeal.add_mem _ hx hy
  | neg x _ hx =>
    rw [map_neg, unop_neg]
    exact TwoSidedIdeal.neg_mem _ hx
  | left_absorb a x _ hx =>
    rw [map_mul, unop_mul]
    exact TwoSidedIdeal.mul_mem_right _ _ _ hx
  | right_absorb a x _ hx =>
    rw [map_mul, unop_mul]
    exact TwoSidedIdeal.mul_mem_left _ _ _ hx

private def etaValue (b : B₀ C) : B₀ C := unop (eta₀ C b)

@[simp] private theorem etaValue_add (b d : B₀ C) :
    etaValue C (b + d) = etaValue C b + etaValue C d := by simp [etaValue]

@[simp] private theorem etaValue_mul (b d : B₀ C) :
    etaValue C (b * d) = etaValue C d * etaValue C b := by simp [etaValue]

@[simp] private theorem etaValue_cartan (t : T) :
    etaValue C (cartan₀ C t) = cartan₀ C t := by simp [etaValue]

private theorem etaValue_positive (e : Free A) :
    etaValue C (positive C e) = negative C (unop (reverseFree A e)) := by
  have hh : (eta₀ C).comp (positive C) = (AlgHom.op (negative C)).comp (reverseFree A) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp
  exact congrArg unop (DFunLike.congr_fun hh e)

private theorem etaValue_negative (f : Free A) :
    etaValue C (negative C f) = positive C (unop (reverseFree A f)) := by
  have hh : (eta₀ C).comp (negative C) = (AlgHom.op (positive C)).comp (reverseFree A) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp
  exact congrArg unop (DFunLike.congr_fun hh f)

private theorem etaValue_positiveImage {x : B₀ C} (hx : x ∈ positiveImage C) :
    etaValue C x ∈ negativeImage C := by
  refine positiveImage_induction C (P := fun x => etaValue C x ∈ negativeImage C) ?_ ?_ hx
  · intro x y hx hy
    rw [etaValue_add]
    exact (negativeImage C).add_mem hx hy
  · intro f t e
    rw [etaValue_mul, etaValue_mul, etaValue_negative, etaValue_positive, etaValue_cartan,
      ← mul_assoc]
    exact negativeImage_monomial C ⟨_, reverseFree_mem C.q e⟩ t _

private theorem etaValue_negativeImage {x : B₀ C} (hx : x ∈ negativeImage C) :
    etaValue C x ∈ positiveImage C := by
  refine negativeImage_induction C (P := fun x => etaValue C x ∈ positiveImage C) ?_ ?_ hx
  · intro x y hx hy
    rw [etaValue_add]
    exact (positiveImage C).add_mem hx hy
  · intro f t e
    rw [etaValue_mul, etaValue_mul, etaValue_negative, etaValue_positive, etaValue_cartan,
      ← mul_assoc]
    exact positiveImage_monomial C _ t ⟨_, reverseFree_mem C.q f⟩

private theorem etaValue_mem_negativeImage_iff (x : B₀ C) :
    etaValue C x ∈ negativeImage C ↔ x ∈ positiveImage C :=
  ⟨fun hx => (eta₀_involutive C x) ▸ etaValue_negativeImage C hx,
    etaValue_positiveImage C⟩

private theorem etaValue_mem_positiveImage_iff (x : B₀ C) :
    etaValue C x ∈ positiveImage C ↔ x ∈ negativeImage C := by
  simpa only [show etaValue C (etaValue C x) = x from eta₀_involutive C x] using
    (etaValue_mem_negativeImage_iff C (etaValue C x)).symm

end Reversal

private theorem eval_serre_mem (f : Free A →ₐ[A] B₀ C)
    (h : ∀ i j : Root, i ≠ j → f (freeSerre C.q i j) ∈ serreIdeal C)
    {e : Free A} (he : e ∈ freeSerreSubmodule C.q) : f e ∈ serreIdeal C := by
  apply (TwoSidedIdeal.mem_comap (f := f.toRingHom)).mp
  refine (TwoSidedIdeal.span_le.mpr ?_) he
  intro x hx
  change x = relationXY C.q ∨ x = relationYX C.q at hx
  apply (TwoSidedIdeal.mem_comap (f := f.toRingHom)).mpr
  rcases hx with rfl | rfl
  · exact h 0 1 (by decide)
  · exact h 1 0 (by decide)

private theorem image_sum_eq (h : HasNormalForm C)
    (hc : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j)) (hx : CrossCommutators C) :
    negativeImage C ⊔ positiveImage C = (serreIdeal C).asIdeal.restrictScalars A := by
  apply le_antisymm
  · apply sup_le
    · intro x hx'
      change x ∈ serreIdeal C
      refine negativeImage_induction C (P := fun x => x ∈ serreIdeal C)
        (fun _ _ => (serreIdeal C).add_mem) ?_ hx'
      intro f t e
      refine (serreIdeal C).mul_mem_right _ _ ((serreIdeal C).mul_mem_right _ _ ?_)
      refine eval_serre_mem C (negative C) (fun i j hij => ?_) f.property
      rw [negative_freeSerre]
      exact TwoSidedIdeal.subset_span ⟨i, j, hij, Or.inr rfl⟩
    · intro x hx'
      change x ∈ serreIdeal C
      refine positiveImage_induction C (P := fun x => x ∈ serreIdeal C)
        (fun _ _ => (serreIdeal C).add_mem) ?_ hx'
      intro f t e
      refine (serreIdeal C).mul_mem_left _ _ (eval_serre_mem C (positive C) (fun i j hij => ?_) e.property)
      rw [positive_freeSerre]
      exact TwoSidedIdeal.subset_span ⟨i, j, hij, Or.inl rfl⟩
  · let M := negativeImage C ⊔ positiveImage C
    have hleft {b x : B₀ C} (hx' : x ∈ M) : b * x ∈ M := by
      obtain ⟨n, hn, p, hp, rfl⟩ := Submodule.mem_sup.mp hx'
      rw [mul_add]
      refine Submodule.add_mem_sup ((etaValue_mem_positiveImage_iff C _).mp ?_)
        (positiveImage_left C h b hp)
      rw [etaValue_mul]
      exact positiveImage_right C h hc hx _ ((etaValue_mem_positiveImage_iff C _).mpr hn)
    have hright {b x : B₀ C} (hx' : x ∈ M) : x * b ∈ M := by
      obtain ⟨n, hn, p, hp, rfl⟩ := Submodule.mem_sup.mp hx'
      rw [add_mul]
      refine Submodule.add_mem_sup ((etaValue_mem_positiveImage_iff C _).mp ?_)
        (positiveImage_right C h hc hx b hp)
      rw [etaValue_mul]
      exact positiveImage_left C h _ ((etaValue_mem_positiveImage_iff C _).mpr hn)
    let I := TwoSidedIdeal.mk' (M : Set (B₀ C)) M.zero_mem (fun {_ _} => M.add_mem)
      (fun {_} => M.neg_mem) hleft hright
    have hI : serreIdeal C ≤ I := by
      apply TwoSidedIdeal.span_le.mpr
      intro r hr
      obtain ⟨i, j, hij, hpos | hneg⟩ := hr
      · subst r
        apply (TwoSidedIdeal.mem_mk' ..).mpr
        exact Submodule.mem_sup_right (positiveImage_serre C i j hij)
      · subst r
        apply (TwoSidedIdeal.mem_mk' ..).mpr
        apply Submodule.mem_sup_left
        simpa only [map_one, mul_one, negative_freeSerre] using
          negativeImage_monomial C ⟨freeSerre C.q i j, freeSerre_mem C.q i j hij⟩ 1 1
    intro x hx'
    exact (TwoSidedIdeal.mem_mk' ..).mp (hI (show x ∈ serreIdeal C from hx'))

/-- The mixed commutators and ordered ideal equality for commuting Cartan translations. -/
theorem crossingSerreIdeal_of_normalForm (h : HasNormalForm C)
    (hc : ∀ i j : Root, Function.Commute (C.tau i) (C.tau j)) (hx : CrossCommutators C) :
    CrossingSerreIdeal C := by
  refine ⟨hx, ?_⟩
  unfold IdealCorrespondence
  rw [← image_sum_eq C h hc hx, positiveImage, negativeImage, ← Submodule.map_sup,
    Submodule.comap_map_eq_of_injective h.injective]

theorem generic_crossingSerreIdeal : GenericProp.{u} := by
  intro k _ _ q hq
  exact crossingSerreIdeal_of_normalForm (generic q hq) (BasicNormalForm.generic_normalForm q hq)
    (generic_commute q hq) (SerreCrossCommutators.generic_crossCommutators q hq)

theorem indeterminate_crossingSerreIdeal : IndeterminateProp.{u} := by
  intro k _ _
  exact generic_crossingSerreIdeal (rationalQ k)
    (Specs.LieNotes.Quantum.Presentation.rationalQ_sq_ne k)

theorem truncated_crossingSerreIdeal : TruncatedProp.{u} := by
  intro k _ _ N hN
  exact crossingSerreIdeal_of_normalForm (truncated k N) (BasicNormalForm.truncated_normalForm k N hN)
    (truncated_commute N) (SerreCrossCommutators.truncated_crossCommutators k N hN)

end LieNotes.Quantum.SerreIdeal
