import Specs.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
import LinearAlgebraicGroups.Albert.SpinFunctor
import LinearAlgebraicGroups.Arithmetic.SpinOrthogonalWords
import LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalGeometry
import LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalRootDatum
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Affine.SchemeImageQuotient
import LinearAlgebraicGroups.Affine.SmoothnessCriteria
import LinearAlgebraicGroups.Affine.Components
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Reflection
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo

open Specs.Arithmetic.OddSpinAwayFromTwo
open Module

universe u v

theorem formCoordinates (n : ℕ) (R : Type u) [CommRing R] (x : Space n R) :
    form n R x = (∑ i : Fin n, x.1 (.inl i) * x.1 (.inr i)) + x.2 ^ 2 := by
  simp [form, QuadraticMap.prod_apply, QuadraticMap.sq, pow_two]

theorem polarCoordinates (n : ℕ) (R : Type u) [CommRing R] (x y : Space n R) :
    (form n R).polarBilin x y =
      (∑ i : Fin n, (x.1 (.inl i) * y.1 (.inr i) + x.1 (.inr i) * y.1 (.inl i))) +
        2 * x.2 * y.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, formCoordinates,
    Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  simp only [mul_comm (y.1 (.inl _)) (x.1 (.inr _))]
  ring

theorem perfectPolar : PerfectPolar.{u} := by
  intro n k _ h₂
  change Function.Bijective (form n k).polarBilin
  suffices h : Function.Injective (form n k).polarBilin from
    ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := k) (V := Space n k)).symm).mp h⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have he (i : Fin n) : x.1 (.inl i) = 0 := by
    have h := DFunLike.congr_fun hx (Pi.single (.inr i) 1, 0)
    change (form n k).polarBilin x _ = 0 at h
    rw [polarCoordinates n k] at h
    simpa [Pi.single_apply, mul_ite] using h
  have hf (i : Fin n) : x.1 (.inr i) = 0 := by
    have h := DFunLike.congr_fun hx (Pi.single (.inl i) 1, 0)
    change (form n k).polarBilin x _ = 0 at h
    rw [polarCoordinates n k] at h
    simpa [Pi.single_apply, mul_ite] using h
  have hr : x.2 = 0 := by
    have h := DFunLike.congr_fun hx (0, 1)
    change (form n k).polarBilin x _ = 0 at h
    rw [polarCoordinates n k] at h
    exact (mul_eq_zero.mp (by simpa using h)).resolve_left h₂
  exact Prod.ext (funext (Sum.rec he hf)) hr

private theorem corootSpan (n : ℕ) (hn : 0 < n) :
    Submodule.span ℤ (Prod.snd '' corootPairs n) = evenSum n := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨r, v⟩, hv, rfl⟩
    change v ∈ evenSum n
    simp [corootPairs] at hv
    rcases hv with (⟨i, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ | ⟨i, j, _, rfl, rfl | rfl | rfl⟩)
    all_goals
      change Even (∑ a, _)
      simp [coordinate, Pi.neg_apply, Pi.sub_apply, Pi.add_apply,
        Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  · intro v hv
    let i₀ : Fin n := ⟨0, hn⟩
    let L := Submodule.span ℤ (Prod.snd '' corootPairs n)
    have hd (i : Fin n) : coordinate n i - coordinate n i₀ ∈ L := by
      by_cases h : i = i₀
      · simp [h, L]
      · exact Submodule.subset_span
          ⟨(_, _), Or.inr ⟨i, i₀, h, rfl, Or.inl rfl⟩, rfl⟩
    have ht : (2 : ℤ) • coordinate n i₀ ∈ L :=
      Submodule.subset_span ⟨(_, _), Or.inl ⟨i₀, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩
    obtain ⟨m, hm⟩ : Even (∑ i, v i) := hv
    have hs : (∑ i, v i • coordinate n i) = v := by
      ext j
      simp [coordinate, Finset.sum_apply, Pi.single_apply, mul_ite]
    have hdecomp :
        (∑ i, v i • (coordinate n i - coordinate n i₀)) + m • ((2 : ℤ) • coordinate n i₀) = v := by
      have hm' : m • ((2 : ℤ) • coordinate n i₀) = (m + m) • coordinate n i₀ := by
        rw [two_smul, smul_add, add_smul]
      rw [Finset.sum_congr rfl (fun i _ => smul_sub (v i) (coordinate n i) (coordinate n i₀)),
        Finset.sum_sub_distrib, hs, ← Finset.sum_smul, hm, hm', sub_add_cancel]
    rw [← hdecomp]
    exact L.add_mem (L.sum_mem fun i _ => L.smul_mem _ (hd i)) (L.smul_mem _ ht)

theorem corootLattice : CorootLattice := by
  intro n hn
  refine ⟨corootSpan n hn, fun v => ?_⟩
  change (∃ a : ℤ, 2 * a + ∑ i, v i = 0) ↔ Even (∑ i, v i)
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨-a, by omega⟩
  · rintro ⟨a, ha⟩
    exact ⟨-a, by omega⟩


theorem scalarKernel : ScalarKernel.{u} := by
  intro k _ n h₂
  exact Albert.SpinFunctor.regularSchemeKernelSpecification (form n k) ((basis n k).reindex Equiv.ulift.symm)
    (Or.inl (LinearMap.ker_eq_bot.mpr (perfectPolar n k h₂).1))

section Reflections

open CliffordAlgebra

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (q : QuadraticForm F V)

private def reflectionFunctional (w : V) : Module.Dual F V := (q w)⁻¹ • q.polarBilin w

private theorem reflectionFunctional_apply (w x : V) :
    reflectionFunctional q w x = q.polarBilin w x / q w := by
  simp [reflectionFunctional, div_eq_mul_inv, mul_comm]

private theorem reflectionFunctional_self {w : V} (hw : q w ≠ 0) :
    reflectionFunctional q w w = 2 := by
  rw [reflectionFunctional_apply, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
    two_smul, ← two_mul, mul_div_cancel_right₀ _ hw]

private theorem det_preReflection [FiniteDimensional F V] (w : V) (f : Module.Dual F V) :
    LinearMap.det (Module.preReflection w f) = 1 - f w := by
  classical
  let b := Module.finBasis F V
  rw [← LinearMap.det_toMatrix b, Module.preReflection, map_sub, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit, Matrix.det_one_sub_mul_comm,
    Matrix.det_unique]
  change 1 - (Matrix.replicateRow Unit (f ∘ b) * Matrix.replicateCol Unit (b.repr w)) () () =
    1 - f w
  rw [Matrix.replicateRow_mul_replicateCol_apply]
  congr 1
  conv_rhs => rw [← b.sum_repr w, map_sum]
  simp [dotProduct, mul_comm]

private def reflectionWord (l : List V) : V →ₗ[F] V :=
  l.foldr (fun w g => (Module.preReflection w (reflectionFunctional q w)).comp g) LinearMap.id

private theorem reflectionWord_apply (l : List V) (x : V) :
    reflectionWord q l x =
      l.foldr (fun w z => z - (q.polarBilin w z / q w) • w) x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change Module.preReflection w (reflectionFunctional q w) (reflectionWord q l x) = _
    rw [Module.preReflection_apply, reflectionFunctional_apply, ih]
    rfl

private theorem reflectionWord_det [FiniteDimensional F V] (l : List V)
    (hl : ∀ w ∈ l, q w ≠ 0) :
    LinearMap.det (reflectionWord q l) = (-1 : F) ^ l.length := by
  induction l with
  | nil => simp [reflectionWord]
  | cons w l ih =>
    change LinearMap.det ((Module.preReflection w (reflectionFunctional q w)).comp
      (reflectionWord q l)) = _
    rw [LinearMap.det_comp, det_preReflection, reflectionFunctional_self q
      (hl w List.mem_cons_self), ih (fun v hv => hl v (List.mem_cons_of_mem w hv)),
      List.length_cons, pow_succ, mul_comm]
    norm_num

private noncomputable def vectorUnit (w : V) (hw : q w ≠ 0) : (CliffordAlgebra q)ˣ :=
  (isUnit_ι_of_isUnit q (isUnit_iff_ne_zero.mpr hw)).unit

private theorem vectorUnit_val (w : V) (hw : q w ≠ 0) :
    (vectorUnit q w hw).val = ι q w := IsUnit.unit_spec _

private theorem twisted_vectorUnit (w : V) (hw : q w ≠ 0) (x : V) :
    involute (vectorUnit q w hw).val * ι q x * (vectorUnit q w hw)⁻¹.val =
      ι q (Module.preReflection w (reflectionFunctional q w) x) := by
  let a := vectorUnit q w hw
  let : Invertible (q w) := invertibleOfNonzero hw
  let : Invertible (ι q w) := invertibleιOfInvertible q w
  have ha : a.val = ι q w := vectorUnit_val q w hw
  have hi : a⁻¹.val = ⅟(ι q w) := by
    rw [invOf_eq_right_inv (b := a⁻¹.val)]
    change ι q w * a⁻¹.val = 1
    rw [← ha]
    exact a.val_inv
  change involute a.val * ι q x * a⁻¹.val = _
  rw [ha, hi, involute_ι, neg_mul, neg_mul, ι_mul_ι_mul_invOf_ι]
  simp [Module.preReflection_apply, reflectionFunctional_apply,
    invOf_eq_inv, div_eq_mul_inv, mul_comm]

private noncomputable def cliffordWord (l : List V) (hl : ∀ w ∈ l, q w ≠ 0) :
    (CliffordAlgebra q)ˣ :=
  match l with
  | [] => 1
  | w :: l => vectorUnit q w (hl w List.mem_cons_self) *
      cliffordWord l (fun v hv => hl v (List.mem_cons_of_mem w hv))

private theorem cliffordWord_calculation (l : List V) (hl : ∀ w ∈ l, q w ≠ 0) :
    let a := cliffordWord q l hl
    a.val ∈ evenOdd q (l.length : ZMod 2) ∧
    reverse a.val * a.val = algebraMap F _ (l.map q).prod ∧
    ∀ x : V, involute a.val * ι q x * a⁻¹.val = ι q (reflectionWord q l x) := by
  induction l with
  | nil =>
    simp [cliffordWord, reflectionWord, SetLike.one_mem_graded]
  | cons w l ih =>
    let b := vectorUnit q w (hl w List.mem_cons_self)
    let c := cliffordWord q l (fun v hv => hl v (List.mem_cons_of_mem w hv))
    obtain ⟨hc, hn, h⟩ := ih (fun v hv => hl v (List.mem_cons_of_mem w hv))
    change (b * c).val ∈ evenOdd q (_ : ZMod 2) ∧
      reverse (b * c).val * (b * c).val = _ ∧ _
    have hb : b.val = ι q w := vectorUnit_val q w _
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul, hb, List.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one q w) hc
    · rw [Units.val_mul, reverse.map_mul, hb, reverse_ι]
      simp only [List.map_cons, List.prod_cons, map_mul]
      calc
        _ = reverse c.val * (ι q w * ι q w) * c.val := by noncomm_ring
        _ = algebraMap F _ (q w) * (reverse c.val * c.val) := by
          rw [ι_sq_scalar, ← Algebra.commutes (q w) (reverse c.val), mul_assoc]
        _ = _ := by rw [hn]
    · intro x
      change involute (b * c).val * ι q x * (b * c)⁻¹.val =
        ι q (Module.preReflection w (reflectionFunctional q w) (reflectionWord q l x))
      simp only [Units.val_mul, mul_inv_rev, map_mul]
      calc
        _ = involute b.val * (involute c.val * ι q x * c⁻¹.val) * b⁻¹.val := by
          noncomm_ring
        _ = _ := by rw [h]; exact twisted_vectorUnit q w _ _

theorem geometricLifting : GeometricLifting.{u} := by
  intro F V _ _ _ _ _ q h₂ hker g hg hd
  obtain ⟨l, hl, h⟩ :=
    SpinOrthogonalWords.orthogonalWords q (Or.inl hker) g hg
  have hg' : (g : V →ₗ[F] V) = reflectionWord q l := by
    ext x
    rw [reflectionWord_apply, ← h]
    rfl
  have hsign : (-1 : F) ^ l.length = 1 := by
    rw [← reflectionWord_det q l hl, ← hg', ← LinearEquiv.coe_det, hd, Units.val_one]
  have he : Even l.length := by
    by_contra hne
    have ho : Odd l.length := Nat.not_even_iff_odd.mp hne
    rw [ho.neg_pow, one_pow, neg_eq_iff_add_eq_zero, ← two_mul, mul_one] at hsign
    exact h₂ hsign
  obtain ⟨hm, hn, ha⟩ := cliffordWord_calculation q l hl
  let a := cliffordWord q l hl
  change a.val ∈ evenOdd q _ at hm
  have hm₀ : a.val ∈ evenOdd q 0 := by
    obtain ⟨m, hlen⟩ := he
    have hc : (l.length : ZMod 2) = 0 := by rw [hlen, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
    simpa only [hc] using hm
  let d := (l.map q).prod
  have hd₀ : d ≠ 0 := by
    apply List.prod_ne_zero
    intro hx
    obtain ⟨v, hv, hv₀⟩ := List.mem_map.mp hx
    exact hl v hv hv₀
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq d⁻¹ zero_lt_two
  have hs₀ : s ≠ 0 := by
    intro hz
    exact (inv_ne_zero hd₀) (by simpa [hz] using hs.symm)
  let z : (CliffordAlgebra q)ˣ := Units.map (algebraMap F (CliffordAlgebra q)).toMonoidHom
    (Units.mk0 s hs₀)
  have hz : z.val = algebraMap F _ s := rfl
  refine ⟨z * a, ?_, ?_, ?_⟩
  · rw [Units.val_mul, hz, ← Algebra.smul_def]
    exact (evenOdd q 0).smul_mem s hm₀
  · change reverse (z.val * a.val) * (z.val * a.val) = 1
    rw [reverse.map_mul, hz, reverse.commutes]
    calc
      _ = reverse a.val * ((algebraMap F _ s) ^ 2 * a.val) := by
        simp only [pow_two, mul_assoc]
      _ = (algebraMap F _ s) ^ 2 * (reverse a.val * a.val) := by
        rw [← mul_assoc, ← map_pow, ← Algebra.commutes (s ^ 2) (reverse a.val),
          mul_assoc, map_pow]
      _ = 1 := by
        change reverse a.val * a.val = algebraMap F _ d at hn
        rw [hn, ← map_pow, ← map_mul, hs, inv_mul_cancel₀ hd₀, map_one]
  · intro x
    have hx : ι q (g x) = a.val * ι q x * a⁻¹.val := by
      have hax := ha x
      change involute a.val * ι q x * a⁻¹.val = _ at hax
      rw [involute_eq_of_mem_even hm₀] at hax
      rw [← LinearEquiv.coe_coe, hg', ← hax]
    rw [hx]
    change _ = (z.val * a.val) * ι q x * (a⁻¹ * z⁻¹).val
    rw [Units.val_mul]
    calc
      _ = z.val * (a.val * ι q x * a⁻¹.val) * z⁻¹.val := by
        rw [hz, Algebra.commutes s (a.val * ι q x * a⁻¹.val), ← hz]
        simp [mul_assoc]
      _ = _ := by noncomm_ring


open private contract_coord contract_polar orderedBasis orderedBasis_empty
  from LinearAlgebraicGroups.Albert.SpinFunctor

private theorem twistedCentralizer_scalar {I : Type*} [LinearOrder I] [Fintype I]
    (b : Basis I F V) (hpolar : Function.Surjective q.polarBilin) {a : CliffordAlgebra q}
    (ha : ∀ x, involute a * ι q x = ι q x * a) : ∃ t : F, a = algebraMap F _ t := by
  classical
  let B := orderedBasis q b
  have hzero (s : Finset I) (hs : s ≠ ∅) : B.coord s a = 0 := by
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨v, hv⟩ := hpolar (b.coord i)
    apply contract_coord q b a i _ s hi
    rw [← hv, contract_polar, ha, sub_self]
  refine ⟨B.coord ∅ a, ?_⟩
  calc
    a = ∑ s, B.repr a s • B s := (B.sum_repr a).symm
    _ = B.coord ∅ a • B ∅ := by
      apply Finset.sum_eq_single ∅
      · intro s _ hs
        rw [← Basis.coord_apply, hzero s hs, zero_smul]
      · simp
    _ = algebraMap F _ (B.coord ∅ a) := by
      change (B.coord ∅ a) • orderedBasis q b ∅ = _
      rw [orderedBasis_empty, Algebra.smul_def, mul_one]

theorem det_of_even_implementer [Infinite F] [FiniteDimensional F V]
    (h₂ : (2 : F) ≠ 0) (hpolar : Function.Bijective q.polarBilin)
    (g : V ≃ₗ[F] V) (hg : ∀ x, q (g x) = q x)
    (a : (CliffordAlgebra q)ˣ) (ha : a.val ∈ evenOdd q 0)
    (h : ∀ x, ι q (g x) = a.val * ι q x * a⁻¹.val) :
    LinearEquiv.det g = 1 := by
  obtain ⟨l, hl, hword⟩ :=
    SpinOrthogonalWords.orthogonalWords q (Or.inl (LinearMap.ker_eq_bot.mpr hpolar.1)) g hg
  have hg' : (g : V →ₗ[F] V) = reflectionWord q l := by
    ext x
    rw [reflectionWord_apply, ← hword]
    rfl
  let b := cliffordWord q l hl
  obtain ⟨hb, -, htw⟩ := cliffordWord_calculation q l hl
  change b.val ∈ evenOdd q _ at hb
  have hinv : involute b⁻¹.val * involute b.val = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hComm (x : V) : involute (b⁻¹ * a).val * ι q x = ι q x * (b⁻¹ * a).val := by
    have hax : a.val * ι q x = ι q (g x) * a.val := by
      rw [h, mul_assoc, Units.inv_mul, mul_one]
    have hbx : involute b⁻¹.val * ι q (g x) = ι q x * b⁻¹.val := by
      rw [← LinearEquiv.coe_coe, hg', ← htw x, ← mul_assoc, ← mul_assoc, hinv, one_mul]
    rw [Units.val_mul, map_mul, involute_eq_of_mem_even ha, mul_assoc, hax, ← mul_assoc,
      hbx, mul_assoc]
  obtain ⟨t, ht⟩ := twistedCentralizer_scalar q (Module.finBasis F V) hpolar.2 hComm
  have hfix : involute (b⁻¹ * a).val = (b⁻¹ * a).val := by rw [ht, AlgHom.commutes]
  have hbe : involute b.val = b.val := by
    have hab : involute (b.val * (b⁻¹ * a).val) = b.val * (b⁻¹ * a).val := by
      simpa only [← Units.val_mul, mul_inv_cancel_left] using involute_eq_of_mem_even ha
    rw [map_mul, hfix] at hab
    exact Units.mul_left_inj (b⁻¹ * a) |>.mp hab
  have helen : Even l.length := by
    by_contra hne
    have ho : Odd l.length := Nat.not_even_iff_odd.mp hne
    obtain ⟨m, hlen⟩ := ho
    have hc : (l.length : ZMod 2) = 1 := by
      rw [hlen, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      change (2 : ZMod 2) * m + 1 = 1
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
    rw [hc] at hb
    have hz : b.val + b.val = 0 := neg_eq_iff_add_eq_zero.mp
      ((involute_eq_of_mem_odd hb).symm.trans hbe)
    have hsmul : (2 : F) • b.val = 0 := by rwa [two_smul]
    let : Invertible (2 : F) := invertibleOfNonzero h₂
    exact b.ne_zero ((smul_eq_zero.mp hsmul).resolve_left h₂)
  apply Units.ext
  rw [LinearEquiv.coe_det, hg', reflectionWord_det q l hl, helen.neg_pow, one_pow, Units.val_one]

end Reflections


section VectorAction

open AlgebraicGeometry CategoryTheory CliffordAlgebra
open scoped TensorProduct
open Albert.SpinSpecification (ExtendedForm)
open Albert.SpinFunctor (Spin vectorAction vectorAction_preserves)
open private polar_baseChange_tmul polarCoordinate_baseChange cliffordEquiv cliffordEquiv_vector
  cliffordEquiv_even changeModule
  from LinearAlgebraicGroups.Albert.SpinFunctor

variable {k : Type u} [Field k] (n : ℕ)
variable (S : Type u) [CommRing S] [Algebra k S]

theorem extendedPerfectPolar (h₂ : (2 : k) ≠ 0) :
    Function.Bijective (ExtendedForm (form n k) S (basis n k)).polarBilin := by
  let b := (basis n k).baseChange S
  let q := ExtendedForm (form n k) S (basis n k)
  have hc (i : OddIndices n) : ∃ v, q.polarBilin v = b.coord i := by
    obtain ⟨v, hv⟩ := (perfectPolar n k h₂).2 ((basis n k).coord i)
    exact ⟨1 ⊗ₜ[k] v, polarCoordinate_baseChange (form n k) S (basis n k) v i hv⟩
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply b.repr.injective
    ext i
    obtain ⟨v, hv⟩ := hc i
    have h := DFunLike.congr_fun hx v
    change q.polarBilin x v = 0 at h
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply, hv, Basis.coord_apply] at h
    simpa using h
  · intro f
    obtain ⟨g, hg⟩ := Classical.axiomOfChoice hc
    refine ⟨∑ i, f (b i) • g i, ?_⟩
    apply b.ext
    intro j
    change q.polarBilin (∑ i, f (b i) • g i) (b j) = f (b j)
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have he (i : OddIndices n) : q.polarBilin (g i) (b j) = b.repr (b j) i :=
      DFunLike.congr_fun (hg i) (b j)
    simp only [he, Basis.repr_self]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [Finsupp.single_eq_of_ne hij, mul_zero]
    · simp

private theorem det_sq_of_isometry (h₂ : (2 : k) ≠ 0)
    (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k))
    (hg : ∀ x, ExtendedForm (form n k) S (basis n k) (g x) =
      ExtendedForm (form n k) S (basis n k) x) :
    (LinearMap.det g.toLinearMap) ^ 2 = 1 := by
  let q := form n k
  let Q := ExtendedForm q S (basis n k)
  let b := (basis n k).baseChange S
  let M := LinearMap.BilinForm.toMatrix b Q.polarBilin
  let B := LinearMap.BilinForm.toMatrix (basis n k) q.polarBilin
  have hB : B.det ≠ 0 := by
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (basis n k)).mp
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply (perfectPolar n k h₂).1
    rw [map_zero]
    exact LinearMap.ext hx
  have hM : M = (algebraMap k S).mapMatrix B := by
    ext i j
    simp only [M, B, b, LinearMap.BilinForm.toMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Basis.baseChange_apply, Q]
    exact polar_baseChange_tmul q S (basis n k) _ _
  have hu : IsUnit M.det := by
    rw [hM, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hB).map (algebraMap k S)
  have hP : LinearMap.BilinForm.comp Q.polarBilin g.toLinearMap g.toLinearMap = Q.polarBilin := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.BilinForm.comp_apply, LinearEquiv.coe_coe,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add]
    change Q (g (x + y)) - Q (g x) - Q (g y) = Q (x + y) - Q x - Q y
    rw [hg, hg, hg]
  have hdet := congrArg (fun B' => (LinearMap.BilinForm.toMatrix b B').det) hP
  rw [LinearMap.BilinForm.toMatrix_comp b b, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix] at hdet
  change LinearMap.det g.toLinearMap * M.det * LinearMap.det g.toLinearMap = M.det at hdet
  apply hu.mul_left_cancel
  rw [pow_two, mul_one]
  linear_combination hdet

variable {S} {T : Type u} [CommRing T] [Algebra k T]

private theorem repr_changeModule (f : S →ₐ[k] T) (x : S ⊗[k] Space n k)
    (i : OddIndices n) :
    ((basis n k).baseChange T).repr (changeModule f x) i =
      f (((basis n k).baseChange S).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    change ((basis n k).baseChange T).repr (f s ⊗ₜ[k] x) i = _
    simp
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

theorem det_vectorAction_natural (f : S →ₐ[k] T) (a : Spin (form n k) S (basis n k)) :
    LinearMap.det (vectorAction (form n k) T (basis n k)
      (Albert.SpinFunctor.map (form n k) (basis n k) f a)).toLinearMap =
      f (LinearMap.det (vectorAction (form n k) S (basis n k) a).toLinearMap) := by
  let b := basis n k
  let g := vectorAction (form n k) S b a
  let h := vectorAction (form n k) T b (Albert.SpinFunctor.map (form n k) b f a)
  have hh : h.toLinearMap.toMatrix (b.baseChange T) (b.baseChange T) =
      f.toRingHom.mapMatrix (g.toLinearMap.toMatrix (b.baseChange S) (b.baseChange S)) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearEquiv.coe_coe, Basis.baseChange_apply]
    change (b.baseChange T).repr (h (1 ⊗ₜ[k] b j)) i =
      f ((b.baseChange S).repr (g (1 ⊗ₜ[k] b j)) i)
    rw [← repr_changeModule n f]
    have hn := Albert.SpinFunctor.vectorAction_naturality (form n k) b f a (1 ⊗ₜ[k] b j)
    have hm : changeModule f (1 ⊗ₜ[k] b j) = 1 ⊗ₜ[k] b j :=
      congrArg (· ⊗ₜ[k] b j) f.map_one
    rw [hm] at hn
    rw [hn]
  rw [← LinearMap.det_toMatrix (b.baseChange T), ← LinearMap.det_toMatrix (b.baseChange S),
    hh, ← RingHom.map_det]
  rfl

variable (S)

theorem det_vectorAction (h₂ : (2 : k) ≠ 0)
    (a : Spin (form n k) S (basis n k)) :
    LinearEquiv.det (vectorAction (form n k) S (basis n k) a) = 1 := by
  let q := form n k
  let b := basis n k
  let d := LinearMap.det (vectorAction q S b a).toLinearMap
  have hd : d ^ 2 = 1 := det_sq_of_isometry n S h₂ _ (vectorAction_preserves q S b a)
  have hu : IsUnit (d + 1) := by
    by_contra hn
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hn)
    let : m.IsMaximal := hm
    let : Field (S ⧸ m) := Ideal.Quotient.field m
    let K := AlgebraicClosure (S ⧸ m)
    let f : S →ₐ[k] K := IsScalarTower.toAlgHom k S K
    let a' := Albert.SpinFunctor.map q b f a
    let g := vectorAction q K b a'
    let e := cliffordEquiv q K b
    let A := Units.map e.toMonoidHom a'.val
    have ha : A.val ∈ evenOdd (ExtendedForm q K b) 0 :=
      (cliffordEquiv_even q K b _).mpr a'.property.1
    have hA (x : K ⊗[k] Space n k) : ι (ExtendedForm q K b) (g x) =
        A.val * ι (ExtendedForm q K b) x * A⁻¹.val := by
      have h := congrArg e (Albert.SpinFunctor.vectorAction_characterization q K b a' x)
      have hi : A⁻¹.val = e a'.val⁻¹.val := by
        change ((Units.map e.toMonoidHom a'.val)⁻¹).val = _
        rw [← map_inv]
        rfl
      rw [hi]
      change _ = e a'.val * ι (ExtendedForm q K b) x * e a'.val⁻¹.val
      simpa only [e, cliffordEquiv_vector, Albert.SpinSpecification.conjugate, map_mul] using h
    have h₂K : (2 : K) ≠ 0 := by
      rw [← map_ofNat (algebraMap k K) 2]
      simpa only [map_zero] using (algebraMap k K).injective.ne h₂
    have he := det_of_even_implementer (ExtendedForm q K b) h₂K
      (extendedPerfectPolar n K h₂) g (vectorAction_preserves q K b a') A ha hA
    have he' := congrArg Units.val he
    rw [LinearEquiv.coe_det, Units.val_one] at he'
    change LinearMap.det (vectorAction q K b (Albert.SpinFunctor.map q b f a)).toLinearMap = 1 at he'
    rw [det_vectorAction_natural n f] at he'
    change f d = 1 at he'
    have hdm : d + 1 ∈ m := hle (Ideal.subset_span (Set.mem_singleton _))
    have hzero : f (d + 1) = 0 := by
      change algebraMap (S ⧸ m) K (Ideal.Quotient.mk m (d + 1)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hdm, map_zero]
    exact h₂K (by simpa only [map_add, map_one, he', one_add_one_eq_two] using hzero)
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_one]
  change d = 1
  apply hu.mul_left_cancel
  rw [mul_one, add_mul, ← pow_two, hd, one_mul, add_comm]


open private vectors_injective conjugate_mul conjugate_one
  from LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel

theorem determinantOneAction : DeterminantOneAction.{u} := by
  intro k _ n h₂ S _ _ a ha g hg
  let A : Spin (form n k) S (basis n k) := ⟨a, ha⟩
  have he : g = vectorAction (form n k) S (basis n k) A := by
    ext x
    apply vectors_injective (form n k) S (basis n k)
    exact (hg x).trans (Albert.SpinFunctor.vectorAction_characterization (form n k) S (basis n k) A x).symm
  rw [he]
  exact det_vectorAction n S h₂ A

theorem geometricVectorLifting : GeometricVectorLifting.{u} := by
  intro k _ n h₂ K _ _ _ g
  let q := form n k
  let b := basis n k
  let Q := ExtendedForm q K b
  let e := cliffordEquiv q K b
  have hg : ∀ x, Q (g.val x) = Q x := g.property.1
  have hd : LinearEquiv.det g.val = 1 := g.property.2
  have h₂K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap k K) 2]
    simpa only [map_zero] using (algebraMap k K).injective.ne h₂
  obtain ⟨A, hA, hn, he⟩ := geometricLifting Q h₂K
    (LinearMap.ker_eq_bot.mpr (extendedPerfectPolar n K h₂).1) g.val hg hd
  let a := Units.map e.symm.toMonoidHom A
  have ha : e a.val = A.val := e.apply_symm_apply _
  have hai : e a⁻¹.val = A⁻¹.val := by
    change e ((Units.map e.symm.toMonoidHom A)⁻¹).val = _
    rw [← map_inv]
    exact e.apply_symm_apply _
  open Albert.SpinSpecification (vectors conjugate reversion IsVectorAction) in
  have hV : IsVectorAction q K a g.val := by
    intro x
    apply e.injective
    change e (vectors q K (g.val x)) = e (conjugate q K a (vectors q K x))
    rw [cliffordEquiv_vector, conjugate, map_mul, map_mul, cliffordEquiv_vector, ha, hai]
    exact he x
  refine ⟨a, ?_, hV⟩
  open Albert.SpinSpecification (vectors conjugate reversion evenPart spinUnits) in
  change a.val ∈ evenPart q K ∧ reversion q K a.val * a.val = 1 ∧ _ ∧ _
  refine ⟨(cliffordEquiv_even q K b _).mp (ha.symm ▸ hA), ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_one]
    change Albert.CliffordModel.baseChangeEquiv K q b (reversion q K a.val) * e a.val = 1
    rw [baseChangeEquiv_reverse]
    change reverse (e a.val) * e a.val = 1
    rwa [ha]
  · rintro y ⟨x, rfl⟩
    exact ⟨g.val x, hV x⟩
  · rintro y ⟨x, rfl⟩
    refine ⟨g.val.symm x, ?_⟩
    have hx := hV (g.val.symm x)
    rw [LinearEquiv.apply_symm_apply] at hx
    rw [hx, ← conjugate_mul, inv_mul_cancel, conjugate_one]

end VectorAction


section OrthogonalScheme

set_option synthInstance.maxHeartbeats 200000

open AlgebraicGeometry CategoryTheory Opposite Matrix
open scoped CategoryTheory.MonObj TensorProduct
open Specs.StandardGroups (SLCoordinates spectrum specialLinearPoints)
open private polar_baseChange_tmul changeModule from LinearAlgebraicGroups.Albert.SpinFunctor
open private Representation Representation.mk Representation.equiv Representation.naturality Representation.hopf
  Representation.convolutionIso spectrumPointsIso specialLinearRepresentation
  from LinearAlgebraicGroups.Affine.StandardGroups

noncomputable section

variable {k : Type u} [Field k] (n : ℕ)

private def matrixBasis : Basis (ULift.{u} (OddIndices n)) k (Space n k) :=
  (basis n k).reindex Equiv.ulift.symm

/-- The Gram matrix of the split odd polar form. -/
def gram : Matrix (ULift.{u} (OddIndices n)) (ULift.{u} (OddIndices n)) k :=
  LinearMap.BilinForm.toMatrix (matrixBasis n) (form n k).polarBilin

variable (S : Type u) [CommRing S] [Algebra k S]

private abbrev gramOver : Matrix (ULift.{u} (OddIndices n)) (ULift.{u} (OddIndices n)) S := (algebraMap k S).mapMatrix (gram (k := k) n)

/-- The determinant-one matrices preserving the split odd polar form. -/
def orthogonalMatrices : Subgroup (SpecialLinearGroup (ULift.{u} (OddIndices n)) S) where
  carrier := {g | (g.val)ᵀ * gramOver (k := k) n S * g.val = gramOver (k := k) n S}
  one_mem' := by simp [SpecialLinearGroup.coe_one]
  mul_mem' {a b} ha hb := by
    change a.valᵀ * _ * a.val = _ at ha
    change b.valᵀ * _ * b.val = _ at hb
    change ((a * b).val)ᵀ * _ * (a * b).val = _
    rw [SpecialLinearGroup.coe_mul, transpose_mul]
    calc
      _ = b.valᵀ * (a.valᵀ * gramOver (k := k) n S * a.val) * b.val := by
        simp only [mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' {a} ha := by
    change a.valᵀ * _ * a.val = _ at ha
    change (a⁻¹).valᵀ * _ * (a⁻¹).val = _
    have hl : a.val * (a⁻¹).val = 1 := by rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    calc
      _ = (a⁻¹).valᵀ * (a.valᵀ * gramOver (k := k) n S * a.val) * (a⁻¹).val := by
        rw [ha]
      _ = (a.val * (a⁻¹).val)ᵀ * gramOver (k := k) n S * (a.val * (a⁻¹).val) := by
        rw [transpose_mul]
        simp only [mul_assoc]
      _ = _ := by rw [hl, transpose_one, one_mul, mul_one]

private def mapOrthogonal {S T : CommAlgCat.{u} k} (f : S ⟶ T) :
    orthogonalMatrices (k := k) n S →* orthogonalMatrices (k := k) n T :=
  ((SpecialLinearGroup.map f.hom.toRingHom).comp (orthogonalMatrices (k := k) n S).subtype).codRestrict _ <| by
    intro a
    have h := congrArg f.hom.toRingHom.mapMatrix a.property
    have hgram : f.hom.toRingHom.mapMatrix (gramOver (k := k) n S) = gramOver (k := k) n T :=
      Matrix.ext fun i j => f.hom.commutes (gram (k := k) n i j)
    let A := a.val.val
    have ht : f.hom.toRingHom.mapMatrix Aᵀ = (f.hom.toRingHom.mapMatrix A)ᵀ := rfl
    change f.hom.toRingHom.mapMatrix (Aᵀ * gramOver (k := k) n S * A) = _ at h
    change (f.hom.toRingHom.mapMatrix A)ᵀ * gramOver (k := k) n T * f.hom.toRingHom.mapMatrix A = _
    simpa only [map_mul, ht, hgram] using h

private def orthogonalMatrixFunctor : CommAlgCat.{u} k ⥤ GrpCat.{u} where
  obj S := GrpCat.of (orthogonalMatrices (k := k) n S)
  map f := GrpCat.ofHom (mapOrthogonal n f)
  map_id _ := by apply GrpCat.ext; intro a; rfl
  map_comp _ _ := by apply GrpCat.ext; intro a; rfl

private abbrev slRep (n : ℕ) :
    Representation (SLCoordinates k (ULift.{u} (OddIndices n)))
      (specialLinearPoints k (ULift.{u} (OddIndices n))) :=
  specialLinearRepresentation

private def universalSpecialLinear : SpecialLinearGroup (ULift.{u} (OddIndices n)) (SLCoordinates k (ULift.{u} (OddIndices n))) :=
  Representation.equiv (slRep (k := k) (n := n)) (CommAlgCat.of k (SLCoordinates k (ULift.{u} (OddIndices n)))) (AlgHom.id k (SLCoordinates k (ULift.{u} (OddIndices n))))

private def orthogonalRelations : Matrix (ULift.{u} (OddIndices n)) (ULift.{u} (OddIndices n)) (SLCoordinates k (ULift.{u} (OddIndices n))) :=
  let X := (universalSpecialLinear (k := k) n).val
  Xᵀ * gramOver (k := k) n (SLCoordinates k (ULift.{u} (OddIndices n))) * X - gramOver (k := k) n (SLCoordinates k (ULift.{u} (OddIndices n)))

private def orthogonalIdeal : Ideal (SLCoordinates k (ULift.{u} (OddIndices n))) :=
  Ideal.span (Set.range fun ij : (ULift.{u} (OddIndices n)) × (ULift.{u} (OddIndices n)) => orthogonalRelations (k := k) n ij.1 ij.2)

/-- Coordinate ring of the determinant-one split odd orthogonal scheme. -/
abbrev OrthogonalCoordinates := (SLCoordinates k (ULift.{u} (OddIndices n))) ⧸ orthogonalIdeal (k := k) n

private abbrev quo : (SLCoordinates k (ULift.{u} (OddIndices n))) →ₐ[k] OrthogonalCoordinates (k := k) n :=
  Ideal.Quotient.mkₐ k (orthogonalIdeal n)

private theorem eval_orthogonalRelations {S : CommAlgCat.{u} k} (f : (SLCoordinates k (ULift.{u} (OddIndices n))) →ₐ[k] S) :
    f.toRingHom.mapMatrix (orthogonalRelations n) =
      let A := (Representation.equiv (slRep (k := k) (n := n)) S f).val
      Aᵀ * gramOver (k := k) n S * A - gramOver (k := k) n S := by
  have hA := Representation.naturality (slRep (k := k) (n := n))
    (CommAlgCat.ofHom f) (AlgHom.id k (SLCoordinates k (ULift.{u} (OddIndices n))))
  have hm : f.toRingHom.mapMatrix (universalSpecialLinear (k := k) n).val =
      (Representation.equiv (slRep (k := k) (n := n)) S f).val :=
    (congrArg Subtype.val hA).symm
  have hgram : f.toRingHom.mapMatrix (gramOver (k := k) n (SLCoordinates k (ULift.{u} (OddIndices n)))) = gramOver (k := k) n S :=
    Matrix.ext fun i j => f.commutes (gram (k := k) n i j)
  have ht : f.toRingHom.mapMatrix (universalSpecialLinear (k := k) n).valᵀ =
      ((Representation.equiv (slRep (k := k) (n := n)) S f).val)ᵀ :=
    congrArg Matrix.transpose hm
  simp only [orthogonalRelations, map_sub, map_mul, hgram, ht, hm]

private def orthogonalEvaluation (S : CommAlgCat.{u} k) :
    (OrthogonalCoordinates (k := k) n →ₐ[k] S) ≃ orthogonalMatrices (k := k) n S where
  toFun f :=
    ⟨Representation.equiv (slRep (k := k) (n := n)) S (f.comp (quo n)), by
      apply sub_eq_zero.mp
      rw [← eval_orthogonalRelations n (f.comp (quo n))]
      ext i j
      change f (quo n (orthogonalRelations n i j)) = 0
      rw [show quo n (orthogonalRelations n i j) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i,j), rfl⟩), map_zero]⟩
  invFun g :=
    let f := (Representation.equiv (slRep (k := k) (n := n)) S).symm g.val
    Ideal.Quotient.liftₐ (orthogonalIdeal n) f (by
      have h : orthogonalIdeal n ≤ RingHom.ker f.toRingHom := by
        apply Ideal.span_le.mpr
        rintro x ⟨⟨i, j⟩, rfl⟩
        change f (orthogonalRelations n i j) = 0
        have he := eval_orthogonalRelations n f
        have hg := g.property
        change g.val.valᵀ * _ * g.val.val = _ at hg
        rw [show Representation.equiv (slRep (k := k) (n := n)) S f = g.val from
          (Representation.equiv (slRep (k := k) (n := n)) S).apply_symm_apply _] at he
        change f.toRingHom.mapMatrix (orthogonalRelations (k := k) n) =
          g.val.valᵀ * gramOver (k := k) n S * g.val.val - gramOver (k := k) n S at he
        rw [hg, sub_self] at he
        exact congrFun (congrFun he i) j
      exact fun x hx => h hx)
  left_inv f := by
    apply Ideal.Quotient.algHom_ext k
    let e := Representation.equiv (slRep (k := k) (n := n)) S
    exact (Ideal.Quotient.liftₐ_comp (orthogonalIdeal n) _ _).trans (e.symm_apply_apply _)
  right_inv g := by
    apply Subtype.ext
    let e := Representation.equiv (slRep (k := k) (n := n)) S
    exact (congrArg e (Ideal.Quotient.liftₐ_comp (orthogonalIdeal n) _ _)).trans
      (e.apply_symm_apply _)

private def orthogonalRepresentation :
    Representation (OrthogonalCoordinates (k := k) n) (orthogonalMatrixFunctor (k := k) n) :=
  Representation.mk (orthogonalEvaluation n) (by
    intro S T f a
    apply Subtype.ext
    change Representation.equiv (slRep (k := k) (n := n)) _ ((f.hom.comp a).comp (quo n)) =
      (SpecialLinearGroup.map f.hom.toRingHom)
        (Representation.equiv (slRep (k := k) (n := n)) _ (a.comp (quo n)))
    exact Representation.naturality (slRep (k := k) (n := n)) f (a.comp (quo n)))

/-- The split odd special orthogonal scheme, presented by the Gram matrix equations. -/
def specialOrthogonalGroup : Specs.AffineAlgebraicGroup k :=
  letI := Representation.hopf (orthogonalRepresentation (k := k) n)
  spectrum k (OrthogonalCoordinates (k := k) n)

private def orthogonalMatrixPoints :
    (groupPointsFunctor k).obj (specialOrthogonalGroup (k := k) n).val ≅ orthogonalMatrixFunctor (k := k) n :=
  letI := Representation.hopf (orthogonalRepresentation (k := k) n)
  spectrumPointsIso (Representation.convolutionIso (orthogonalRepresentation (k := k) n))

open Albert.SpinSpecification (SchemePoints ExtendedForm)

private theorem gramOver_eq :
    gramOver (k := k) n S =
      LinearMap.BilinForm.toMatrix ((matrixBasis (k := k) n).baseChange S)
        (ExtendedForm (form n k) S (basis n k)).polarBilin := by
  ext i j
  simp only [gramOver, gram, RingHom.mapMatrix_apply, Matrix.map_apply,
    LinearMap.BilinForm.toMatrix_apply, Basis.baseChange_apply]
  exact (polar_baseChange_tmul (form n k) S (basis n k) _ _).symm

private theorem isometry_iff_matrix (h₂ : (2 : k) ≠ 0)
    (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) :
    let Q := ExtendedForm (form n k) S (basis n k)
    let b := (matrixBasis (k := k) n).baseChange S
    let M := g.toLinearMap.toMatrix b b
    (∀ x, Q (g x) = Q x) ↔
      Mᵀ * gramOver (k := k) n S * M = gramOver (k := k) n S := by
  dsimp only
  let Q := ExtendedForm (form n k) S (basis n k)
  let b := (matrixBasis (k := k) n).baseChange S
  rw [gramOver_eq, ← LinearMap.BilinForm.toMatrix_comp b b,
    (LinearMap.BilinForm.toMatrix b).injective.eq_iff]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.BilinForm.comp_apply, LinearEquiv.coe_coe,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add]
    change Q (g (x + y)) - Q (g x) - Q (g y) = Q (x + y) - Q x - Q y
    rw [h, h, h]
  · intro h x
    have he := DFunLike.congr_fun (DFunLike.congr_fun h x) x
    simp only [LinearMap.BilinForm.comp_apply, LinearEquiv.coe_coe,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul] at he
    have hu : IsUnit (2 : S) := by
      rw [← map_ofNat (algebraMap k S) 2]
      exact (isUnit_iff_ne_zero.mpr h₂).map (algebraMap k S)
    exact hu.mul_left_cancel (by simpa only [two_mul] using he)

private def isometryMatrix (h₂ : (2 : k) ≠ 0) (S : CommAlgCat.{u} k) :
    specialOrthogonal (k := k) n S →* orthogonalMatrices (k := k) n S := by
  let b := (matrixBasis (k := k) n).baseChange S
  refine { toFun := fun a => ⟨⟨a.val.toLinearMap.toMatrix b b, ?_⟩, ?_⟩
           map_one' := ?_
           map_mul' := ?_ }
  · rw [LinearMap.det_toMatrix, ← LinearEquiv.coe_det]
    exact congrArg Units.val a.property.2
  · exact (isometry_iff_matrix n S h₂ a.val).mp a.property.1
  · apply Subtype.ext
    apply Subtype.ext
    exact LinearMap.toMatrix_id b
  · intro f g
    apply Subtype.ext
    apply Subtype.ext
    exact LinearMap.toMatrix_comp b b b f.val.toLinearMap g.val.toLinearMap

private theorem isometryMatrix_bijective (h₂ : (2 : k) ≠ 0) (S : CommAlgCat.{u} k) :
    Function.Bijective (isometryMatrix n h₂ S) := by
  let b := (matrixBasis (k := k) n).baseChange S
  constructor
  · intro a c h
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply (LinearMap.toMatrix b b).injective
    exact congrArg (fun z : orthogonalMatrices (k := k) n S => z.val.val) h
  · intro A
    let M := Matrix.toLin b b A.val.val
    let N := Matrix.toLin b b (A.val⁻¹).val
    have hleft : A.val.val * (A.val⁻¹).val = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    have hright : (A.val⁻¹).val * A.val.val = 1 := by
      rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
    let g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k) := LinearEquiv.ofLinearMap M N
      (by rw [← Matrix.toLin_mul b b b, hleft, Matrix.toLin_one])
      (by rw [← Matrix.toLin_mul b b b, hright, Matrix.toLin_one])
    have hg : g.toLinearMap.toMatrix b b = A.val.val := LinearMap.toMatrix_toLin b b _
    have hs : g ∈ specialOrthogonal (k := k) n S := by
      refine ⟨(isometry_iff_matrix n S h₂ g).mpr ?_, ?_⟩
      · change (g.toLinearMap.toMatrix b b)ᵀ * _ * _ = _
        rw [hg]
        exact A.property
      · change LinearEquiv.det g = 1
        apply Units.ext
        rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b, hg]
        exact A.val.prop
    refine ⟨⟨g, hs⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hg

private def orthogonalPoints (h₂ : (2 : k) ≠ 0) (S : CommAlgCat.{u} k) :
    SchemePoints (specialOrthogonalGroup (k := k) n).val S ≃* specialOrthogonal (k := k) n S :=
  ((orthogonalMatrixPoints (k := k) n).app S).groupIsoToMulEquiv.trans
    (MulEquiv.ofBijective _ (isometryMatrix_bijective n h₂ S)).symm

private theorem repr_matrixBasis_changeModule {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (x : S ⊗[k] Space n k) (i : (ULift.{u} (OddIndices n))) :
    ((matrixBasis (k := k) n).baseChange T).repr (changeModule f.hom x) i =
      f.hom (((matrixBasis (k := k) n).baseChange S).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    change ((matrixBasis (k := k) n).baseChange T).repr (f.hom s ⊗ₜ[k] x) i = _
    simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem orthogonalPoints_natural (h₂ : (2 : k) ≠ 0) :
    RepresentsSpecialOrthogonal (specialOrthogonalGroup (k := k) n).val (orthogonalPoints n h₂) := by
  intro S T f p x
  let a := orthogonalPoints n h₂ S p
  let c := orthogonalPoints n h₂ T ((algSpec (CommRingCat.of k)).map f.op ≫ p)
  let bS := (matrixBasis (k := k) n).baseChange S
  let bT := (matrixBasis (k := k) n).baseChange T
  have h (R : CommAlgCat.{u} k) (s : SchemePoints (specialOrthogonalGroup (k := k) n).val R) :
      isometryMatrix n h₂ R (orthogonalPoints n h₂ R s) =
        (orthogonalMatrixPoints (k := k) n).hom.app R s :=
    (MulEquiv.ofBijective _ (isometryMatrix_bijective n h₂ R)).apply_symm_apply _
  have hn := ConcreteCategory.congr_hom ((orthogonalMatrixPoints (k := k) n).hom.naturality f) p
  change (orthogonalMatrixPoints (k := k) n).hom.app T ((algSpec (CommRingCat.of k)).map f.op ≫ p) =
    mapOrthogonal n f ((orthogonalMatrixPoints (k := k) n).hom.app S p) at hn
  rw [← h, ← h] at hn
  have hM : c.val.toLinearMap.toMatrix bT bT = f.hom.toRingHom.mapMatrix
      (a.val.toLinearMap.toMatrix bS bS) :=
    congrArg (fun z : orthogonalMatrices (k := k) n T => z.val.val) hn
  change changeModule f.hom (a.val x) = c.val (changeModule f.hom x)
  apply bT.repr.injective
  ext i
  rw [repr_matrixBasis_changeModule n f]
  have hS := LinearMap.toMatrix_mulVec_repr bS bS a.val.toLinearMap x
  have hT := LinearMap.toMatrix_mulVec_repr bT bT c.val.toLinearMap (changeModule f.hom x)
  change f.hom (bS.repr (a.val.toLinearMap x) i) =
    bT.repr (c.val.toLinearMap (changeModule f.hom x)) i
  rw [← congrFun hS i, ← congrFun hT i, hM]
  simp only [mulVec, dotProduct, map_sum, map_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
  congr 1
  ext j
  rw [repr_matrixBasis_changeModule n f]
  rfl

theorem specialOrthogonalRepresentation : SpecialOrthogonalRepresentation.{u} := by
  intro k _ n h₂
  exact ⟨specialOrthogonalGroup n, orthogonalPoints n h₂, orthogonalPoints_natural n h₂⟩


private theorem matrixQuotient_mul_eq_zero {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (I : Ideal R) (hI : I ^ 2 = ⊥) {A B : Matrix J J R}
    (hA : (Ideal.Quotient.mk I).mapMatrix A = 0)
    (hB : (Ideal.Quotient.mk I).mapMatrix B = 0) : A * B = 0 := by
  have hentry {M : Matrix J J R} (hM : (Ideal.Quotient.mk I).mapMatrix M = 0) (i j : J) :
      M i j ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (congrFun hM i) j)
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro l _
  have h := Ideal.mul_mem_mul (hentry hA i l) (hentry hB l j)
  rw [← pow_two, hI] at h
  exact (Ideal.mem_bot.mp h)

private theorem gramLiftsSquareZero {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (B : Matrix J J R) (hB : Bᵀ = B) (hdet : IsUnit B.det) (a : R) (ha : 2 * a = 1)
    (I : Ideal R) (hI : I ^ 2 = ⊥) (g : Matrix J J (R ⧸ I))
    (hg : gᵀ * (Ideal.Quotient.mk I).mapMatrix B * g = (Ideal.Quotient.mk I).mapMatrix B)
    (hgdet : g.det = 1) :
    ∃ G : Matrix J J R, (Ideal.Quotient.mk I).mapMatrix G = g ∧ Gᵀ * B * G = B ∧ G.det = 1 := by
  let f := Ideal.Quotient.mk I
  choose m hm using fun i j => Ideal.Quotient.mk_surjective (I := I) (g i j)
  let M : Matrix J J R := m
  have hmapM : f.mapMatrix M = g := Matrix.ext hm
  let C := Mᵀ * B * M - B
  have hC : Cᵀ = C := by
    simp only [C, transpose_sub, transpose_mul, transpose_transpose, hB, mul_assoc]
  have hmapC : f.mapMatrix C = 0 := by
    simp only [C, map_sub, map_mul, show f.mapMatrix Mᵀ = (f.mapMatrix M)ᵀ from rfl,
      hmapM]
    exact sub_eq_zero.mpr hg
  let E := a • C
  have hE : Eᵀ = E := by rw [show (a • C)ᵀ = a • Cᵀ from rfl, hC]
  have hmapE : f.mapMatrix E = 0 := by
    have h : f.mapMatrix (a • C) = f a • f.mapMatrix C :=
      Matrix.ext fun i j => f.map_mul a (C i j)
    rw [show E = a • C from rfl, h, hmapC, smul_zero]
  let D := B⁻¹ * E
  have hmapD : f.mapMatrix D = 0 := by simp only [D, map_mul, hmapE, mul_zero]
  have hmapDt : f.mapMatrix Dᵀ = 0 := by
    change (f.mapMatrix D)ᵀ = 0
    rw [hmapD, transpose_zero]
  have hBD : B * D = E := B.mul_nonsing_inv_cancel_left E hdet
  have hDtB : Dᵀ * B = E := by
    have h := congrArg Matrix.transpose hBD
    rwa [transpose_mul, hB, hE] at h
  have hCD : C * D = 0 := matrixQuotient_mul_eq_zero I hI hmapC hmapD
  have hDtC : Dᵀ * C = 0 := matrixQuotient_mul_eq_zero I hI hmapDt hmapC
  have hDtE : Dᵀ * E = 0 := matrixQuotient_mul_eq_zero I hI hmapDt hmapE
  have hsum : E + E = C := by
    rw [show E = a • C from rfl, ← add_smul]
    rw [show a + a = 1 by linear_combination ha, one_smul]
  let G := M * (1 - D)
  have hmapG : f.mapMatrix G = g := by
    simp only [G, map_mul, map_sub, map_one, hmapD, sub_zero, mul_one, hmapM]
  have hG : Gᵀ * B * G = B := calc
    _ = (1 - Dᵀ) * (B + C) * (1 - D) := by
      have h : B + C = Mᵀ * B * M := by simp [C, add_sub_cancel]
      change (M * (1 - D))ᵀ * B * (M * (1 - D)) = _
      rw [transpose_mul, transpose_sub, transpose_one, h]
      simp only [mul_assoc]
    _ = (1 - Dᵀ) * (B + C - E) := by
      rw [mul_assoc, mul_sub, mul_one, add_mul, hBD, hCD, add_zero]
    _ = B := by
      rw [sub_mul, one_mul, mul_sub, mul_add, hDtB, hDtC, hDtE, add_zero, sub_zero,
        sub_sub, hsum, add_sub_cancel_right]
  have hGs : G.det ^ 2 = 1 := by
    have h := congrArg Matrix.det hG
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
    apply hdet.mul_left_cancel
    linear_combination h
  have hfd : f G.det = 1 := by rw [RingHom.map_det, hmapG, hgdet]
  have hu : IsUnit (G.det + 1) := (IsNilpotent.isUnit_quotient_mk_iff ⟨2, hI⟩).mp <| by
    change IsUnit (f (G.det + 1))
    rw [map_add, hfd, map_one, one_add_one_eq_two, ← map_ofNat f 2]
    exact (show IsUnit (2 : R) from isUnit_iff_exists_inv.mpr ⟨a, ha⟩).map f
  refine ⟨G, hmapG, hG, ?_⟩
  exact sub_eq_zero.mp (hu.mul_right_cancel (show (G.det - 1) * (G.det + 1) =
    0 * (G.det + 1) by linear_combination hGs))

private theorem gram_symmetric : (gram (k := k) n)ᵀ = gram n := by
  ext i j
  exact QuadraticMap.polar_comm _ _ _

private theorem gram_det_ne_zero (h₂ : (2 : k) ≠ 0) : (gram (k := k) n).det ≠ 0 := by
  let Q : LinearMap.BilinForm k (Space n k) := (form n k).polarBilin
  have hQ : Q.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply (perfectPolar n k h₂).1
    rw [map_zero]
    exact LinearMap.ext hx
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (matrixBasis (k := k) n)).mp hQ

private theorem orthogonalCoordinates_formallySmooth (h₂ : (2 : k) ≠ 0) :
    Algebra.FormallySmooth k (OrthogonalCoordinates (k := k) n) := by
  apply Algebra.FormallySmooth.iff_comp_surjective.mpr
  intro R _ _ I hI f
  let A := CommAlgCat.of k R
  let B := CommAlgCat.of k (R ⧸ I)
  let q : A ⟶ B := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  let g := orthogonalEvaluation n B f
  let J := gramOver (k := k) n R
  have hJ : Jᵀ = J := by
    change (algebraMap k R).mapMatrix (gram (k := k) n)ᵀ = J
    rw [gram_symmetric (k := k) n]
  have hJdet : IsUnit J.det := by
    rw [show J = (algebraMap k R).mapMatrix (gram (k := k) n) from rfl, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr (gram_det_ne_zero n h₂)).map (algebraMap k R)
  have hhalf : (2 : R) * algebraMap k R (2 : k)⁻¹ = 1 := by
    rw [← map_ofNat (algebraMap k R) 2, ← map_mul, mul_inv_cancel₀ h₂, map_one]
  have hmap : (Ideal.Quotient.mk I).mapMatrix J = gramOver (k := k) n (R ⧸ I) :=
    Matrix.ext fun i j => q.hom.commutes (gram (k := k) n i j)
  have hg : g.val.valᵀ * (Ideal.Quotient.mk I).mapMatrix J * g.val.val =
      (Ideal.Quotient.mk I).mapMatrix J := by
    rw [hmap]
    exact g.property
  obtain ⟨G, hmapG, hG, hdet⟩ := gramLiftsSquareZero J hJ hJdet _ hhalf I hI g.val.val hg
    g.val.property
  let lift : orthogonalMatrices (k := k) n R := ⟨⟨G, hdet⟩, hG⟩
  let F := (orthogonalEvaluation n A).symm lift
  refine ⟨F, (orthogonalEvaluation n B).injective ?_⟩
  have hn := Representation.naturality (orthogonalRepresentation (k := k) n) q F
  change orthogonalEvaluation n B (q.hom.comp F) =
    mapOrthogonal n q (orthogonalEvaluation n A F) at hn
  change orthogonalEvaluation n B (q.hom.comp F) = g
  rw [hn, (orthogonalEvaluation n A).apply_symm_apply]
  exact Subtype.ext (Subtype.ext hmapG)

theorem specialOrthogonal_smooth (h₂ : (2 : k) ≠ 0) :
    Smooth (specialOrthogonalGroup (k := k) n).val.X.hom := by
  have hs := orthogonalCoordinates_formallySmooth n h₂
  have hp : Algebra.FinitePresentation k (OrthogonalCoordinates (k := k) n) :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := OrthogonalCoordinates (k := k) n)).mp
      inferInstance
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (OrthogonalCoordinates (k := k) n))))
  apply HasRingHomProperty.Spec_iff (P := @Smooth).mpr
  change (algebraMap k (OrthogonalCoordinates (k := k) n)).Smooth
  exact RingHom.smooth_algebraMap.mpr ⟨hs, hp⟩

end

end OrthogonalScheme


section VectorMorphism

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct
open Albert.SpinFunctor (Spin spinScheme spinScheme_affine spinScheme_affineMorphism
  spinScheme_locallyOfFinitePresentation schemePoints vectorAction vectorAction_preserves
  vectorAction_characterization vectorAction_naturality schemePoints_naturality)
open Albert.SpinSpecification (SchemePoints IsVectorAction)
open private spinUnitPoints spinUnitPoints_represents changeModule vectors_injective
  from LinearAlgebraicGroups.Albert.SpinFunctor

noncomputable section

variable {k : Type u} [Field k] (n : ℕ)

private def spinAlgebraicGroup : Specs.AffineAlgebraicGroup k := by
  let G := spinScheme (form n k) (matrixBasis n)
  have ha : IsAffineHom G.X.hom := spinScheme_affineMorphism _ _
  have hp : LocallyOfFinitePresentation G.X.hom := spinScheme_locallyOfFinitePresentation _ _
  exact ⟨G, spinScheme_affine _ _, inferInstance, inferInstance⟩

private def spinToOrthogonalPoints (h₂ : (2 : k) ≠ 0) (S : CommAlgCat.{u} k) :
    SchemePoints (spinAlgebraicGroup (k := k) n).val S →*
      SchemePoints (specialOrthogonalGroup (k := k) n).val S :=
  (orthogonalPoints n h₂ S).symm.toMonoidHom.comp <|
    ((vectorAction (form n k) S (matrixBasis n)).codRestrict (specialOrthogonal n S) (by
      intro a
      have hv := vectorAction_characterization (form n k) S (matrixBasis n) a
      have h : a.val ∈ Albert.SpinSpecification.spinUnits (form n k) S := a.property
      have h₂' := determinantOneAction k n h₂ S a.val h _ hv
      have hq := vectorAction_preserves (form n k) S (matrixBasis n) a
      refine ⟨?_, h₂'⟩
      have hf : Albert.SpinSpecification.ExtendedForm (form n k) S (matrixBasis n) =
          Albert.SpinSpecification.ExtendedForm (form n k) S (basis n k) := by
        apply (Albert.CliffordModel.coefficient_form_unique S (form n k) (basis n k) _).mpr
        intro x
        simpa only [one_mul] using
          Albert.CliffordModel.coefficientForm_tmul S (form n k) (matrixBasis n) 1 x
      change ∀ x, Albert.SpinSpecification.ExtendedForm (form n k) S (basis n k)
        (vectorAction (form n k) S (matrixBasis n) a x) =
          Albert.SpinSpecification.ExtendedForm (form n k) S (basis n k) x
      simpa only [hf] using hq)).comp
      (schemePoints (form n k) (matrixBasis n) S).toMonoidHom

private theorem spinToOrthogonalPoints_action (h₂ : (2 : k) ≠ 0) (S : CommAlgCat.{u} k)
    (p : SchemePoints (spinAlgebraicGroup (k := k) n).val S) :
    (orthogonalPoints n h₂ S (spinToOrthogonalPoints n h₂ S p)).val =
      vectorAction (form n k) S (matrixBasis n) (schemePoints (form n k) (matrixBasis n) S p) := by
  exact congrArg (fun a : specialOrthogonal (k := k) n S => a.val)
    ((orthogonalPoints n h₂ S).apply_symm_apply _)

private def spinToOrthogonalNatural (h₂ : (2 : k) ≠ 0) :
    (groupPointsFunctor k).obj (spinAlgebraicGroup (k := k) n).val ⟶
      (groupPointsFunctor k).obj (specialOrthogonalGroup (k := k) n).val where
  app S := GrpCat.ofHom (spinToOrthogonalPoints n h₂ S)
  naturality {S T} f := by
    apply GrpCat.ext
    intro p
    change SchemePoints (spinAlgebraicGroup (k := k) n).val S at p
    let F := algSpec (CommRingCat.of k)
    change spinToOrthogonalPoints n h₂ T (F.map f.op ≫ p) =
      F.map f.op ≫ spinToOrthogonalPoints n h₂ S p
    apply (orthogonalPoints n h₂ T).injective
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply ((matrixBasis (k := k) n).baseChange T).ext
    intro i
    rw [Basis.baseChange_apply]
    let x : S ⊗[k] Space n k := 1 ⊗ₜ[k] matrixBasis n i
    have hx : changeModule f.hom x = 1 ⊗ₜ[k] matrixBasis n i :=
      congrArg (· ⊗ₜ[k] matrixBasis n i) f.hom.map_one
    have ho := (orthogonalPoints_natural n h₂) f (spinToOrthogonalPoints n h₂ S p) x
    change changeModule f.hom ((orthogonalPoints n h₂ S (spinToOrthogonalPoints n h₂ S p)).val x) =
      (orthogonalPoints n h₂ T (F.map f.op ≫ spinToOrthogonalPoints n h₂ S p)).val
        (changeModule f.hom x) at ho
    rw [spinToOrthogonalPoints_action n h₂ S p, hx] at ho
    change (orthogonalPoints n h₂ T (spinToOrthogonalPoints n h₂ T (F.map f.op ≫ p))).val
        (1 ⊗ₜ[k] matrixBasis n i) =
      (orthogonalPoints n h₂ T (F.map f.op ≫ spinToOrthogonalPoints n h₂ S p)).val
        (1 ⊗ₜ[k] matrixBasis n i)
    rw [spinToOrthogonalPoints_action n h₂ T, ← ho, ← hx]
    have hf := schemePoints_naturality (form n k) (matrixBasis n) f p
    exact (congrArg (fun a => vectorAction (form n k) T (matrixBasis n) a (changeModule f.hom x))
      hf).trans (vectorAction_naturality (form n k) (matrixBasis n) f.hom _ x).symm

/-- The morphism whose point action is even Clifford conjugation. -/
def spinVectorMorphism (h₂ : (2 : k) ≠ 0) :
    (spinAlgebraicGroup (k := k) n).val ⟶ (specialOrthogonalGroup (k := k) n).val :=
  (AffineAlgebraicGroup.groupHomEquiv _ _).symm (spinToOrthogonalNatural n h₂)

private theorem spinVectorMorphism_points (h₂ : (2 : k) ≠ 0) (S : CommAlgCat.{u} k)
    (p : SchemePoints (spinAlgebraicGroup (k := k) n).val S) :
    p ≫ (spinVectorMorphism n h₂).hom.hom = spinToOrthogonalPoints n h₂ S p :=
  congrArg (fun α => α.app S p)
    ((AffineAlgebraicGroup.groupHomEquiv (spinAlgebraicGroup n) (specialOrthogonalGroup n)).apply_symm_apply
      (spinToOrthogonalNatural n h₂))

private theorem spinVectorMorphism_action (h₂ : (2 : k) ≠ 0)
    (S : CommAlgCat.{u} k) (g : SchemePoints (spinAlgebraicGroup (k := k) n).val S) :
    IsVectorAction (form n k) S (spinUnitPoints (form n k) (matrixBasis n) S g)
      (orthogonalPoints n h₂ S (g ≫ (spinVectorMorphism n h₂).hom.hom)).val := by
  rw [spinVectorMorphism_points, spinToOrthogonalPoints_action]
  exact vectorAction_characterization _ _ _ _

private theorem spinVectorMorphism_geometricSurjective (h₂ : (2 : k) ≠ 0)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K] :
    Function.Surjective (fun g : SchemePoints (spinAlgebraicGroup (k := k) n).val
      (CommAlgCat.of k K) => g ≫ (spinVectorMorphism n h₂).hom.hom) := by
  let b := matrixBasis (k := k) n
  let o := orthogonalPoints n h₂
  intro y
  let S := CommAlgCat.of k K
  obtain ⟨a, ha, hay⟩ := geometricVectorLifting k n h₂ K (o S y)
  obtain ⟨g, hg⟩ := (schemePoints (form n k) b S).surjective (⟨a, ha⟩ : Spin (form n k) S b)
  refine ⟨g, ?_⟩
  apply (o S).injective
  apply Subtype.ext
  ext x
  apply vectors_injective (form n k) S b
  have h := spinVectorMorphism_action n h₂ S g x
  change _ = Albert.SpinSpecification.conjugate (form n k) S
    (schemePoints (form n k) b S g).val (Albert.SpinSpecification.vectors (form n k) S x) at h
  rw [hg] at h
  exact h.trans (hay x).symm


/-- Every scheme point of the target is in the image of the spin vector morphism. -/
theorem spinVectorMorphism_surjective (h₂ : (2 : k) ≠ 0) :
    Surjective (spinVectorMorphism n h₂).hom.hom.left := by
  constructor
  intro x
  let A := OrthogonalCoordinates (k := k) n
  let : CommRing A := inferInstanceAs (CommRing (OrthogonalCoordinates (k := k) n))
  let : Algebra k A := inferInstanceAs (Algebra k (OrthogonalCoordinates (k := k) n))
  change PrimeSpectrum A at x
  let I : Ideal A := x.asIdeal
  let : I.IsPrime := x.isPrime
  let K := AlgebraicClosure I.ResidueField
  let f : A →ₐ[k] K := Algebra.ofId A K |>.restrictScalars k
  let y : SchemePoints (specialOrthogonalGroup (k := k) n).val (CommAlgCat.of k K) :=
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op
  obtain ⟨g, hg⟩ := spinVectorMorphism_geometricSurjective n h₂ K y
  let z : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨g.left z, ?_⟩
  have hy := congrArg (fun p : SchemePoints (specialOrthogonalGroup (k := k) n).val
    (CommAlgCat.of k K) => p.left z) hg
  change (spinVectorMorphism n h₂).hom.hom.left (g.left z) = _ at hy
  refine hy.trans ?_
  apply PrimeSpectrum.ext
  change RingHom.ker (algebraMap A K) = x.asIdeal
  rw [IsScalarTower.algebraMap_eq A I.ResidueField K,
    RingHom.ker_comp_of_injective _ (algebraMap I.ResidueField K).injective]
  exact Ideal.ker_algebraMap_residueField I

open CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open Albert.SpinFunctor (muTwoScheme muTwoSchemePoints scalarSchemeInclusion scalarSchemeInclusion_points
  scalarSchemeInclusion_isClosedImmersion scalarEmbedding scalarEmbedding_injective
  scalarEmbedding_trivial_action regularKernel regularKernel_val)

private def spinScalarSubgroup : Specs.ClosedSubgroup (spinAlgebraicGroup (k := k) n).val :=
  ⟨muTwoScheme k, scalarSchemeInclusion (form n k) (matrixBasis n),
    scalarSchemeInclusion_isClosedImmersion (form n k) (matrixBasis n)⟩

private theorem spinVectorMorphism_kernelPoints (h₂ : (2 : k) ≠ 0) (S : CommAlgCat.{u} k)
    (a : SchemePoints (spinAlgebraicGroup (k := k) n).val S) :
    a ≫ (spinVectorMorphism n h₂).hom.hom = 1 ↔
      ∃! t : SchemePoints (spinScalarSubgroup (k := k) n).group S,
        t ≫ (spinScalarSubgroup (k := k) n).inclusion.hom.hom = a := by
  let q := form n k
  let b := matrixBasis (k := k) n
  let i := scalarSchemeInclusion q b
  let v := schemePoints q b S
  let m := muTwoSchemePoints k S
  have haction :
      a ≫ (spinVectorMorphism n h₂).hom.hom = 1 ↔ vectorAction q S b (v a) = 1 := by
    rw [spinVectorMorphism_points, ← (orthogonalPoints n h₂ S).injective.eq_iff, map_one]
    have he := spinToOrthogonalPoints_action n h₂ S a
    constructor
    · intro hx
      exact he.symm.trans (congrArg Subtype.val hx)
    · intro hx
      apply Subtype.ext
      exact he.trans hx
  rw [haction]
  let e := regularKernel q S b (Or.inl (LinearMap.ker_eq_bot.mpr (perfectPolar n k h₂).1))
  constructor
  · intro ha
    let x : (vectorAction q S b).ker := ⟨v a, ha⟩
    let t := m.symm (e.symm x)
    have ht : t ≫ i.hom.hom = a := by
      apply v.injective
      change schemePoints q b S (t ≫ i.hom.hom) = x.val
      rw [scalarSchemeInclusion_points]
      obtain h := congrArg (fun x => x.val) (e.apply_symm_apply x)
      change (e (e.symm x)).val = x.val at h
      change scalarEmbedding q S b (m (m.symm (e.symm x))) = x.val
      rw [m.apply_symm_apply, ← h]
      apply Subtype.ext
      apply Units.ext
      exact (regularKernel_val _ _ _ _ _).symm
    refine ⟨t, ht, fun s hs => m.injective (scalarEmbedding_injective q S b ?_)⟩
    change SchemePoints (muTwoScheme k) S at s
    change s ≫ i.hom.hom = a at hs
    exact (scalarSchemeInclusion_points q b s).symm.trans <|
      (congrArg v (hs.trans ht.symm)).trans (scalarSchemeInclusion_points q b t)
  · rintro ⟨t, ht, _⟩
    change SchemePoints (muTwoScheme k) S at t
    change t ≫ i.hom.hom = a at ht
    rw [← ht]
    exact (congrArg (vectorAction q S b) (scalarSchemeInclusion_points q b t)).trans
      (scalarEmbedding_trivial_action q S b (m t))

private theorem spinVectorMorphism_kernel (h₂ : (2 : k) ≠ 0) :
    Specs.IsSchemeKernel (spinVectorMorphism n h₂) (spinScalarSubgroup n) := by
  let G := spinAlgebraicGroup (k := k) n
  let O := specialOrthogonalGroup (k := k) n
  let Z := spinScalarSubgroup (k := k) n
  let p := (spinVectorMorphism n h₂).hom.hom
  let i := Z.inclusion.hom.hom
  let : IsClosedImmersion i.left := Z.isClosedImmersion
  let : Mono i := Over.mono_of_mono_left i
  let e := η[O.val.X]
  have hc : i ≫ p = toUnit Z.group.X ≫ e := by
    let S := CommAlgCat.of k (Albert.SpinSpecification.muTwoCoordinateRing k)
    have h : (𝟙 Z.group.X) ≫ i = i := Category.id_comp _
    have H := (spinVectorMorphism_kernelPoints n h₂ S i).mpr
      ⟨𝟙 Z.group.X, h, by intro t ht; exact (cancel_mono i).mp (ht.trans h.symm)⟩
    exact H
  let P := pullback p e
  have hP : IsPullback (pullback.fst p e) (pullback.snd p e) p e := IsPullback.of_hasPullback p e
  let c := hP.lift i (toUnit Z.group.X) hc
  have hc₁ : c ≫ pullback.fst p e = i := hP.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd p e = toUnit Z.group.X := hP.lift_snd _ _ _
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine O.val.X.left := O.property.1
  let : IsAffine (𝟙_ (SchemeOver k)).left := by change IsAffine (Spec (CommRingCat.of k)); infer_instance
  have hPleft : IsPullback (pullback.fst p e).left (pullback.snd p e).left p.left e.left :=
    (Over.forget (Spec (CommRingCat.of k))).map_isPullback hP
  have hPa : IsAffine P.left := IsAffine.of_isPullback hPleft
  obtain ⟨S, ⟨a⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hPa
  let g := a.hom ≫ pullback.fst p e
  have hg : g ≫ p = 1 := by
    change (a.hom ≫ pullback.fst p e) ≫ p = toUnit _ ≫ e
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact isTerminalTensorUnit.hom_ext _ _
  obtain ⟨t, ht, _⟩ := (spinVectorMorphism_kernelPoints n h₂ S.unop g).mp hg
  let d := a.inv ≫ t
  have hd : d ≫ i = pullback.fst p e := by
    change (a.inv ≫ t) ≫ i = _
    rw [Category.assoc, ht, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hdc : d ≫ c = 𝟙 P := by
    apply hP.hom_ext
    · simp only [Category.assoc, hc₁, hd, Category.id_comp]
    · exact isTerminalTensorUnit.hom_ext _ _
  have hcd : c ≫ d = 𝟙 Z.group.X := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, hd, hc₁, Category.id_comp]
  exact IsPullback.of_iso_pullback ⟨hc⟩ ⟨c, d, hcd, hdc⟩ hc₁ hc₂

private theorem spinScalarSubgroup_point_scalar (S : CommAlgCat.{u} k)
    (z : SchemePoints (spinScalarSubgroup (k := k) n).group S) :
    ∃ ζ : rootsOfUnity 2 S,
      (spinUnitPoints (form n k) (matrixBasis n) S
        (z ≫ (spinScalarSubgroup (k := k) n).inclusion.hom.hom)).val =
          algebraMap S _ (ζ.val : S) :=
  ⟨muTwoSchemePoints k S z, congrArg (fun a : Spin (form n k) S (matrixBasis n) => a.val.val)
    (scalarSchemeInclusion_points (form n k) (matrixBasis n) z)⟩

theorem vectorMorphism : VectorMorphism.{u} := by
  intro k _ n h₂
  let G := spinAlgebraicGroup (k := k) n
  let O := specialOrthogonalGroup (k := k) n
  let b := matrixBasis (k := k) n
  let p := spinVectorMorphism n h₂
  let e := spinUnitPoints (form n k) b
  let o := orthogonalPoints n h₂
  exact ⟨G, O, p, e, o, spinUnitPoints_represents _ _, orthogonalPoints_natural n h₂,
    spinVectorMorphism_action n h₂, spinVectorMorphism_surjective n h₂,
    spinVectorMorphism_geometricSurjective n h₂, spinScalarSubgroup n,
    spinVectorMorphism_kernel n h₂, rfl, spinScalarSubgroup_point_scalar n⟩

end

end VectorMorphism

section VectorCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup IsSchemeKernel)
open Specs.SchemeDerivedGroup (RepresentsQuotient)
open Specs.CentralIsogenies (IsCentralIsogeny)
open Albert.SpinFunctor (Spin spinScheme schemePoints muTwoSchemePoints scalarSchemeInclusion_points)
open Albert.SpinSpecification (SchemePoints muTwoPolynomial muTwoCoordinateRing ScalarClifford)
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private quotientRepresentsImage from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private spinUnitPoints spinUnitPoints_represents from LinearAlgebraicGroups.Albert.SpinFunctor

noncomputable section

variable {k : Type u} [Field k]

private theorem muTwo_monic : (muTwoPolynomial k).Monic :=
  Polynomial.monic_X_pow_sub_one two_ne_zero

private theorem muTwo_etale (h₂ : (2 : k) ≠ 0) :
    Algebra.Etale k (muTwoCoordinateRing k) := by
  have hs : (muTwoPolynomial k).Separable := by
    simpa using Polynomial.separable_X_pow_sub_C (n := 2) (1 : k) h₂ one_ne_zero
  obtain ⟨a, b, hab⟩ := (Polynomial.separable_def _).mp hs
  let P : StandardEtalePair k := ⟨muTwoPolynomial k, muTwo_monic, 1,
    ⟨b, a, 0, by simpa only [pow_zero, add_comm, mul_comm] using hab⟩⟩
  let A := muTwoCoordinateRing k
  let M := Submonoid.powers (1 : A)
  have hu : M ≤ IsUnit.submonoid A := by
    intro x hx
    obtain ⟨r, rfl⟩ := hx
    simp
  let e : Localization.Away (1 : A) ≃ₐ[A] A :=
    (IsLocalization.atUnits A M hu (S := Localization.Away (1 : A))).symm
  have h : AdjoinRoot.mk P.f P.g = (1 : A) := (AdjoinRoot.mk P.f).map_one
  let iso : P.Ring ≃ₐ[k] A :=
    P.equivAwayAdjoinRoot.trans (h ▸ e.restrictScalars k)
  exact Algebra.Etale.of_equiv iso

private theorem muTwo_finite : Module.Finite k (muTwoCoordinateRing k) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis' (muTwo_monic (k := k))).basis

variable (n : ℕ)

open scoped Matrix

private theorem spinVectorMorphism_flat_and_presentation (h₂ : (2 : k) ≠ 0)
    (hs : Smooth (specialOrthogonalGroup (k := k) n).val.X.hom) :
    Flat (spinVectorMorphism n h₂).hom.hom.left ∧
      LocallyOfFinitePresentation (spinVectorMorphism n h₂).hom.hom.left := by
  let G := spinAlgebraicGroup (k := k) n
  let O := specialOrthogonalGroup (k := k) n
  let p := spinVectorMorphism n h₂
  have := hs
  have : IsReduced O.val.X.left := isReduced_of_smooth_over_field O.val.X.hom
  obtain ⟨L, a, b, h, _, _⟩ := schemeImageFactorization G O p
  have hb : a.hom.hom.left ≫ b.hom.hom.left = p.hom.hom.left :=
    congrArg (fun f : G.val ⟶ O.val => f.hom.hom.left) h.1
  have : Surjective b.hom.hom.left := ⟨by
    intro y
    obtain ⟨x, hx⟩ := (spinVectorMorphism_surjective n h₂).1 y
    exact ⟨a.hom.hom.left x, by simpa only [← Scheme.Hom.comp_apply, hb] using hx⟩⟩
  have := h.2.2.2.2.2
  have : IsIso b.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have := h.2.1
  have := h.2.2.2.1
  rw [← hb]
  exact ⟨inferInstance, inferInstance⟩

private theorem spinScalarSubgroup_central :
    Centralizes (𝟙 (spinAlgebraicGroup (k := k) n).val)
      (spinScalarSubgroup (k := k) n).inclusion.hom.hom := by
  let G := spinAlgebraicGroup (k := k) n
  let Z := spinScalarSubgroup (k := k) n
  let W := G.val.X ⊗ Z.group.X
  let q := form n k
  let b := matrixBasis (k := k) n
  have : IsAffine G.val.X.left := G.property.1
  have : IsAffine Z.group.X.left := by
    change IsAffine (Spec (CommRingCat.of (muTwoCoordinateRing k)))
    infer_instance
  have : IsAffine W.left := by
    change IsAffine (pullback G.val.X.hom Z.group.X.hom)
    exact IsAffine.of_isPullback (IsPullback.of_hasPullback G.val.X.hom Z.group.X.hom)
  obtain ⟨S, ⟨a⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr ‹IsAffine W.left›
  let x : SchemePoints G.val S.unop := a.hom ≫ fst G.val.X Z.group.X
  let z : SchemePoints Z.group S.unop := a.hom ≫ snd G.val.X Z.group.X
  let j := Z.inclusion.hom.hom
  change (snd G.val.X Z.group.X ≫ j) * fst G.val.X Z.group.X *
    (snd G.val.X Z.group.X ≫ j)⁻¹ = fst G.val.X Z.group.X
  apply (cancel_epi a.hom).mp
  simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  change (z ≫ j) * x * (z ≫ j)⁻¹ = x
  let v : SchemePoints G.val S.unop →* (ScalarClifford q S.unop)ˣ :=
    (Spin q S.unop b).subtype.comp (schemePoints q b S.unop).toMonoidHom
  have hv : Function.Injective v := Subtype.val_injective.comp (schemePoints q b S.unop).injective
  apply hv
  rw [map_mul, map_mul, map_inv]
  have hc : (v (z ≫ j)).val = algebraMap S.unop _ ((muTwoSchemePoints k S.unop z).val : S.unop) :=
    congrArg (fun y : Spin q S.unop b => y.val.val) (scalarSchemeInclusion_points q b z)
  have hcomm : Commute (v (z ≫ j)) (v x) := by
    apply Units.ext
    change (v (z ≫ j)).val * (v x).val = (v x).val * (v (z ≫ j)).val
    rw [hc]
    exact Algebra.commutes _ _
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

/-- Right multiplication identifies the self-pullback of a homomorphism with
the product of its source and its scheme kernel. -/
private theorem kernel_product_pullback {G O : GroupScheme k} {p : G ⟶ O} {Z : ClosedSubgroup G}
    (hZ : IsSchemeKernel p Z) :
    IsPullback
      (prod.fst : G.X ⨯ Z.group.X ⟶ G.X)
      (prod.fst * (prod.snd ≫ Z.inclusion.hom.hom))
      p.hom.hom p.hom.hom := by
  let j := Z.inclusion.hom.hom
  let f := p.hom.hom
  have hmono : IsClosedImmersion j.left := Z.isClosedImmersion
  let : Mono j := Over.mono_of_mono_left _
  have hj : j ≫ f = 1 := hZ.w
  have hcomm : (prod.fst : G.X ⨯ Z.group.X ⟶ G.X) ≫ f =
      (prod.fst * (prod.snd ≫ j)) ≫ f := by
    rw [MonObj.mul_comp, Category.assoc, hj, MonObj.comp_one, mul_one]
  let lift (s : PullbackCone f f) : s.pt ⟶ Z.group.X :=
    hZ.lift (s.fst⁻¹ * s.snd) (toUnit s.pt) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, inv_mul_cancel]
      rfl)
  have hlift (s : PullbackCone f f) : lift s ≫ j = s.fst⁻¹ * s.snd := hZ.lift_fst _ _ _
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm
    (fun s => prod.lift s.fst (lift s)) (fun s => prod.lift_fst _ _) (fun s => ?_)
    (fun s z hz₁ hz₂ => ?_))
  · rw [MonObj.comp_mul, prod.lift_fst, ← Category.assoc, prod.lift_snd, hlift,
      mul_inv_cancel_left]
  · apply prod.hom_ext
    · rw [hz₁, prod.lift_fst]
    · rw [prod.lift_snd, ← cancel_mono j, hlift]
      rw [MonObj.comp_mul, hz₁, ← Category.assoc] at hz₂
      rw [← hz₂, inv_mul_cancel_left]

private theorem spinScalarSubgroup_etale (h₂ : (2 : k) ≠ 0) :
    Etale (spinScalarSubgroup (k := k) n).group.X.hom := by
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap k (muTwoCoordinateRing k))))
  apply HasRingHomProperty.Spec_iff (P := @Etale).mpr
  change (algebraMap k (muTwoCoordinateRing k)).Etale
  exact RingHom.etale_algebraMap.mpr (muTwo_etale h₂)

theorem spinVectorMorphism_finiteEtale (h₂ : (2 : k) ≠ 0)
    (hs : Smooth (specialOrthogonalGroup (k := k) n).val.X.hom) :
    IsFinite (spinVectorMorphism n h₂).hom.hom.left ∧ Etale (spinVectorMorphism n h₂).hom.hom.left := by
  let G := spinAlgebraicGroup (k := k) n
  let O := specialOrthogonalGroup (k := k) n
  let Z := spinScalarSubgroup (k := k) n
  let p := spinVectorMorphism n h₂
  let q := p.hom.hom.left
  have : IsAffine G.val.X.left := G.property.1
  have : IsAffine O.val.X.left := O.property.1
  have hSurj : Surjective q := spinVectorMorphism_surjective n h₂
  have hFlat : Flat q := (spinVectorMorphism_flat_and_presentation n h₂ hs).1
  have : QuasiCompact q := inferInstance
  have hZE := spinScalarSubgroup_etale n h₂
  have hZF : IsFinite Z.group.X.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (muTwoCoordinateRing k))))
    apply (IsFinite.SpecMap_iff _).mpr
    change (algebraMap k (muTwoCoordinateRing k)).Finite
    exact RingHom.finite_algebraMap.mpr muTwo_finite
  let a : G.val.X ⨯ Z.group.X ⟶ G.val.X := prod.fst
  let m : G.val.X ⨯ Z.group.X ⟶ G.val.X :=
    prod.fst * (prod.snd ≫ Z.inclusion.hom.hom)
  have hPb : IsPullback a m p.hom.hom p.hom.hom :=
    kernel_product_pullback (spinVectorMorphism_kernel n h₂)
  have hp : IsPullback a.left m.left q q :=
    (Over.forget (Spec (CommRingCat.of k))).map_isPullback hPb
  have ha := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd G.val.X Z.group.X)).flip
  have hA : IsFinite a.left := MorphismProperty.of_isPullback ha hZF
  have hE : Etale a.left := MorphismProperty.of_isPullback ha hZE
  constructor
  · let C := CommRingCat.of (Albert.SpinFunctor.CoordinateRing (form n k) (matrixBasis n))
    let D := CommRingCat.of (OrthogonalCoordinates (k := k) n)
    let qSpec : Spec C ⟶ Spec D := q
    obtain ⟨φ, hφ⟩ := Spec.map_surjective qSpec
    have hq : Spec.map φ = q := hφ
    have hp' : IsPullback a.left m.left (Spec.map φ) (Spec.map φ) := hq.symm ▸ hp
    have hbase : IsFinite (pullback.fst (Spec.map φ) (Spec.map φ)) := by
      have := hA
      have hcomp : IsFinite (hp'.isoPullback.inv ≫ a.left) := inferInstance
      exact hp'.isoPullback_inv_fst ▸ hcomp
    change IsFinite q
    rw [← hq]
    have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
      MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f hf =>
        have : IsIso f := hf
        inferInstance)
    apply of_pullback_fst_Spec_of_codescendsAlong (P := @IsFinite)
      (Q' := RingHom.FaithfullyFlat) (Q := RingHom.Finite) (P' := @Surjective ⊓ @Flat)
      RingHom.Finite.codescendsAlong_faithfullyFlat _ _ _ hbase
    · intro R S f hf
      exact (flat_and_surjective_SpecMap_iff f).mp ⟨hf.2, hf.1⟩
    · exact fun {_ _ f} => IsFinite.SpecMap_iff f
    · rw [hq]
      exact ⟨hSurj, hFlat⟩
  · exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hE

theorem spinVectorMorphism_isCentralIsogeny (h₂ : (2 : k) ≠ 0)
    (hs : Smooth (specialOrthogonalGroup (k := k) n).val.X.hom) :
    IsCentralIsogeny (spinVectorMorphism n h₂) :=
  ⟨(spinVectorMorphism_finiteEtale n h₂ hs).1,
    (spinVectorMorphism_flat_and_presentation n h₂ hs).1,
    spinVectorMorphism_surjective n h₂, spinScalarSubgroup n,
    spinVectorMorphism_kernel n h₂, spinScalarSubgroup_central n⟩

theorem spinVectorMorphism_quotient (h₂ : (2 : k) ≠ 0)
    (hs : Smooth (specialOrthogonalGroup (k := k) n).val.X.hom) :
    RepresentsQuotient (spinScalarSubgroup n) (spinVectorMorphism n h₂) := by
  have := (spinAlgebraicGroup (k := k) n).property.1
  have := (specialOrthogonalGroup (k := k) n).property.1
  refine quotientRepresentsImage
    (i := 𝟙 (specialOrthogonalGroup (k := k) n).val)
    ⟨Category.comp_id _, (spinVectorMorphism_flat_and_presentation n h₂ hs).1,
      spinVectorMorphism_surjective n h₂,
      (spinVectorMorphism_flat_and_presentation n h₂ hs).2, inferInstance, ?_⟩
    (spinVectorMorphism_kernel n h₂)
  change IsClosedImmersion (𝟙 (specialOrthogonalGroup (k := k) n).val.X.left)
  infer_instance


theorem vectorCover : VectorCover.{u} := by
  intro k _ n h₂
  let G := spinAlgebraicGroup (k := k) n
  let O := specialOrthogonalGroup (k := k) n
  let p := spinVectorMorphism n h₂
  have hO := specialOrthogonal_smooth n h₂
  have he := (spinVectorMorphism_finiteEtale n h₂ hO).2
  have hG : Smooth G.val.X.hom := by
    have hh : Smooth (p.hom.hom.left ≫ O.val.X.hom) := inferInstance
    rwa [p.hom.hom.w] at hh
  exact ⟨G, O, p, spinUnitPoints (form n k) (matrixBasis n), orthogonalPoints n h₂,
    spinUnitPoints_represents _ _, orthogonalPoints_natural n h₂,
    spinVectorMorphism_action n h₂, hG, hO, spinVectorMorphism_isCentralIsogeny n h₂ hO, he,
    spinScalarSubgroup n, spinVectorMorphism_kernel n h₂, rfl, spinScalarSubgroup_etale n h₂,
    spinVectorMorphism_quotient n h₂ hO, spinScalarSubgroup_point_scalar n⟩

end

end VectorCover

section DiagonalSpin

open AlgebraicGeometry CategoryTheory CliffordAlgebra
open scoped TensorProduct
open Albert.SpinSpecification (ExtendedForm ScalarClifford vectors reversion evenPart conjugate
  spinUnits IsVectorAction)

noncomputable section

section CliffordPair

variable {A R : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {e f : A} (he : e * e = 0) (hf : f * f = 0) (hef : e * f + f * e = 1)

include he hf hef in
private theorem cliffordPair_idempotents :
    (e * f) * (e * f) = e * f ∧ (f * e) * (f * e) = f * e ∧
    (e * f) * (f * e) = 0 ∧ (f * e) * (e * f) = 0 := by
  have h₁ : (e * f + f * e) * (e * f) = e * f := by rw [hef, one_mul]
  have h₂ : (f * e) * (e * f + f * e) = f * e := by rw [hef, mul_one]
  have h₃ : e * f * (f * e) = 0 := by
    calc
      _ = e * (f * f) * e := by noncomm_ring
      _ = 0 := by rw [hf, mul_zero, zero_mul]
  have h₄ : f * e * (e * f) = 0 := by
    calc
      _ = f * (e * e) * f := by noncomm_ring
      _ = 0 := by rw [he, mul_zero, zero_mul]
  exact ⟨by simpa only [add_mul, h₄, add_zero] using h₁,
    by simpa only [mul_add, h₄, zero_add] using h₂, h₃, h₄⟩

include he hf hef in
private theorem cliffordPair_mul (s t : R) :
    (s • (e * f) + f * e) * (t • (e * f) + f * e) = (s * t) • (e * f) + f * e := by
  obtain ⟨hp, hq, hpq, hqp⟩ := cliffordPair_idempotents he hf hef
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hp, hq, hpq, hqp, smul_zero, add_zero, zero_add, smul_smul, mul_comm t s]

include he hf hef in
private def cliffordPairUnit (t : Rˣ) : Aˣ where
  val := (t : R) • (e * f) + f * e
  inv := (↑t⁻¹ : R) • (e * f) + f * e
  val_inv := by rw [cliffordPair_mul he hf hef, Units.mul_inv, one_smul, hef]
  inv_val := by rw [cliffordPair_mul he hf hef, Units.inv_mul, one_smul, hef]

private theorem cliffordPair_commute (a : A) (hez : e * a = -(a * e))
    (hfz : f * a = -(a * f)) (t : R) : Commute (t • (e * f) + f * e) a := by
  have hefa : Commute (e * f) a := by
    change e * f * a = a * (e * f)
    rw [mul_assoc, hfz, mul_neg, ← mul_assoc, hez, neg_mul, neg_neg, mul_assoc]
  have hfea : Commute (f * e) a := by
    change f * e * a = a * (f * e)
    rw [mul_assoc, hez, mul_neg, ← mul_assoc, hfz, neg_mul, neg_neg, mul_assoc]
  exact (hefa.smul_left t).add_left hfea

private theorem cliffordPair_mul_e (t : Rˣ) :
    (cliffordPairUnit he hf hef t).val * e =
      (t : R) • (e * (cliffordPairUnit he hf hef t).val) := by
  have h₁ : e * (e * f) = 0 := by rw [← mul_assoc, he, zero_mul]
  have h₂ : f * e * e = 0 := by rw [mul_assoc, he, mul_zero]
  have h₃ : e * f * e = e := by
    have h := congrArg (· * e) hef
    simpa only [add_mul, h₂, add_zero, one_mul] using h
  change ((t : R) • (e * f) + f * e) * e =
    (t : R) • (e * ((t : R) • (e * f) + f * e))
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h₁, h₂,
    smul_zero, add_zero, zero_add, ← mul_assoc e f e, h₃]

private theorem cliffordPair_mul_f (t : Rˣ) :
    (cliffordPairUnit he hf hef t).val * f =
      (↑t⁻¹ : R) • (f * (cliffordPairUnit he hf hef t).val) := by
  have h₁ : f * (f * e) = 0 := by rw [← mul_assoc, hf, zero_mul]
  have h₂ : e * f * f = 0 := by rw [mul_assoc, hf, mul_zero]
  have h₃ : f * e * f = f := by
    have h := congrArg (· * f) hef
    simpa only [add_mul, h₂, zero_add, one_mul] using h
  change ((t : R) • (e * f) + f * e) * f =
    (↑t⁻¹ : R) • (f * ((t : R) • (e * f) + f * e))
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h₁, h₂,
    smul_zero, add_zero, zero_add, ← mul_assoc f e f, h₃, smul_smul,
    Units.inv_mul, one_smul]

end CliffordPair


section DiagonalClifford

open Module
open Albert.SpinFunctor (regular_scalarCentralizer)
open private cliffordEquiv cliffordEquiv_vector cliffordEquiv_even reversion_one reversion_mul
  reversion_scalar even_one even_mul conjugate_mul conjugate_inverse conjugationLinear
  scalar_tensor_injective polar_baseChange_tmul conjugate_one from LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel

variable {k : Type u} [Field k] (n : ℕ)

private theorem oddBasis_hyperbolic (i : Indices n) :
    basis n k (Sum.inl i) = (Pi.single i 1, 0) := by
  simp [basis]

private theorem oddBasis_line :
    basis n k (Sum.inr ()) = (0, 1) := by
  simp [basis]

private theorem oddBasis_hyperbolic_norm (i : Indices n) : form n k (basis n k (.inl i)) = 0 := by
  cases i <;> simp [oddBasis_hyperbolic, formCoordinates, Pi.single_apply]

private theorem oddBasis_e_polar (i : Fin n) (j : OddIndices n) :
    (form n k).polarBilin (basis n k (.inl (.inl i))) (basis n k j) =
      if j = .inl (.inr i) then 1 else 0 := by
  rw [polarCoordinates]
  cases j with
  | inl j =>
    cases j <;> simp [oddBasis_hyperbolic, Pi.single_apply, mul_ite,
      eq_comm]
  | inr j =>
    cases j
    simp [oddBasis_hyperbolic, oddBasis_line]

private theorem oddBasis_f_polar (i : Fin n) (j : OddIndices n) :
    (form n k).polarBilin (basis n k (.inl (.inr i))) (basis n k j) =
      if j = .inl (.inl i) then 1 else 0 := by
  rw [polarCoordinates]
  cases j with
  | inl j =>
    cases j <;> simp [oddBasis_hyperbolic, Pi.single_apply, mul_ite,
      eq_comm]
  | inr j =>
    cases j
    simp [oddBasis_hyperbolic, oddBasis_line]

variable (S : CommAlgCat.{u} k)

private abbrev oddClifford := ScalarClifford (form n k) S

private def basisVector (j : OddIndices n) : S ⊗[k] Space n k := 1 ⊗ₜ[k] basis n k j

private def cliffordVector (j : OddIndices n) : oddClifford n S :=
  vectors (form n k) S (basisVector n S j)

private abbrev E (i : Fin n) := cliffordVector n S (.inl (.inl i))
private abbrev F (i : Fin n) := cliffordVector n S (.inl (.inr i))

private theorem cliffordVectors_square (i : Indices n) :
    cliffordVector n S (.inl i) * cliffordVector n S (.inl i) = 0 := by
  let e := cliffordEquiv (form n k) S (basis n k)
  apply e.injective
  change e (vectors (form n k) S (basisVector n S (.inl i)) *
    vectors (form n k) S (basisVector n S (.inl i))) = e 0
  rw [map_mul, cliffordEquiv_vector, ι_sq_scalar, map_zero]
  rw [basisVector, Albert.CliffordModel.coefficientForm_tmul, oddBasis_hyperbolic_norm,
    map_zero, mul_zero, map_zero]

private theorem cliffordVectors_polar (i j : OddIndices n) :
    cliffordVector n S i * cliffordVector n S j +
      cliffordVector n S j * cliffordVector n S i =
    algebraMap S _ (algebraMap k S ((form n k).polarBilin (basis n k i) (basis n k j))) := by
  let e := cliffordEquiv (form n k) S (basis n k)
  apply e.injective
  change e (vectors (form n k) S (basisVector n S i) * vectors (form n k) S (basisVector n S j) +
    vectors (form n k) S (basisVector n S j) * vectors (form n k) S (basisVector n S i)) = _
  rw [map_add, map_mul, map_mul, cliffordEquiv_vector, cliffordEquiv_vector, ι_mul_ι_add_swap,
    AlgEquiv.commutes]
  congr 1
  exact polar_baseChange_tmul (form n k) S (basis n k) _ _

private theorem cliffordVectors_reverse (i : OddIndices n) :
    reversion (form n k) S (cliffordVector n S i) = cliffordVector n S i := by
  let e := cliffordEquiv (form n k) S (basis n k)
  apply e.injective
  change e (reversion (form n k) S (vectors (form n k) S (basisVector n S i))) =
    e (vectors (form n k) S (basisVector n S i))
  rw [show e (reversion (form n k) S _) = reverse (e _) from
    baseChangeEquiv_reverse S (form n k) (basis n k) _, cliffordEquiv_vector, reverse_ι]

private theorem cliffordVectors_mul_even (i j : OddIndices n) :
    cliffordVector n S i * cliffordVector n S j ∈ evenPart (form n k) S := by
  apply (cliffordEquiv_even (form n k) S (basis n k) _).mp
  change (cliffordEquiv (form n k) S (basis n k))
    (vectors (form n k) S (basisVector n S i) * vectors (form n k) S (basisVector n S j)) ∈ _
  rw [map_mul, cliffordEquiv_vector, cliffordEquiv_vector]
  exact ι_mul_ι_mem_evenOdd_zero (Q := ExtendedForm (form n k) S (basis n k)) _ _

private theorem cliffordPair_sum (i : Fin n) :
    E n S i * F n S i + F n S i * E n S i = 1 := by
  rw [cliffordVectors_polar n S, oddBasis_e_polar, ite_eq_left rfl, map_one, map_one]

private def planeUnit (i : Fin n) (t : Sˣ) : (oddClifford n S)ˣ :=
  cliffordPairUnit (cliffordVectors_square n S (.inl i)) (cliffordVectors_square n S (.inr i))
    (cliffordPair_sum n S i) t

private theorem planeUnit_even (i : Fin n) (t : Sˣ) :
    (planeUnit n S i t).val ∈ evenPart (form n k) S :=
  (evenPart (form n k) S).add_mem ((evenPart (form n k) S).smul_mem _
    (cliffordVectors_mul_even n S _ _)) (cliffordVectors_mul_even n S _ _)

private theorem planeUnit_inv (i : Fin n) (t : Sˣ) :
    (planeUnit n S i t)⁻¹ = planeUnit n S i t⁻¹ := Units.ext rfl

private theorem planeUnit_norm (i : Fin n) (t : Sˣ) :
    reversion (form n k) S (planeUnit n S i t).val =
      algebraMap S _ (t : S) * ((planeUnit n S i t)⁻¹).val := by
  rw [planeUnit_inv]
  change reversion (form n k) S ((t : S) • (E n S i * F n S i) + F n S i * E n S i) =
    algebraMap S _ (t : S) * ((↑t⁻¹ : S) • (E n S i * F n S i) + F n S i * E n S i)
  simp only [map_add, map_smul, reversion_mul (form n k) S (basis n k), cliffordVectors_reverse,
    ← Algebra.smul_def, smul_add, smul_smul, Units.mul_inv, one_smul, add_comm]

private def planeScale (i : Fin n) (t : Sˣ) (j : OddIndices n) : Sˣ :=
  if j = .inl (.inl i) then t else if j = .inl (.inr i) then t⁻¹ else 1

private theorem planeUnit_mul_vector (i : Fin n) (t : Sˣ) (j : OddIndices n) :
    (planeUnit n S i t).val * cliffordVector n S j =
      (planeScale n S i t j : S) • (cliffordVector n S j * (planeUnit n S i t).val) := by
  by_cases he : j = .inl (.inl i)
  · subst j
    rw [planeScale, ite_eq_left rfl]
    exact cliffordPair_mul_e _ _ _ t
  by_cases hf : j = .inl (.inr i)
  · subst j
    rw [planeScale, ite_eq_right he, ite_eq_left rfl]
    exact cliffordPair_mul_f _ _ _ t
  · rw [planeScale, ite_eq_right he, ite_eq_right hf, Units.val_one, one_smul]
    have hpE : E n S i * cliffordVector n S j = -(cliffordVector n S j * E n S i) := by
      apply eq_neg_of_add_eq_zero_left
      rw [cliffordVectors_polar n S, oddBasis_e_polar, ite_eq_right hf, map_zero, map_zero]
    have hpF : F n S i * cliffordVector n S j = -(cliffordVector n S j * F n S i) := by
      apply eq_neg_of_add_eq_zero_left
      rw [cliffordVectors_polar n S, oddBasis_f_polar, ite_eq_right he, map_zero, map_zero]
    exact (cliffordPair_commute (cliffordVector n S j) hpE hpF (t : S)).eq


private def planeWord (t : Fin n → Sˣ) (l : List (Fin n)) : (oddClifford n S)ˣ :=
  (l.map (fun i => planeUnit n S i (t i))).prod

private theorem planeWord_even (t : Fin n → Sˣ) (l : List (Fin n)) :
    (planeWord n S t l).val ∈ evenPart (form n k) S := by
  induction l with
  | nil => exact even_one (form n k) S (basis n k)
  | cons i l ih =>
    exact even_mul (form n k) S (basis n k) (planeUnit_even n S i (t i)) ih

private theorem planeWord_inverse_even (t : Fin n → Sˣ) (l : List (Fin n)) :
    ((planeWord n S t l)⁻¹).val ∈ evenPart (form n k) S := by
  induction l with
  | nil => exact even_one (form n k) S (basis n k)
  | cons i l ih =>
    change (((planeUnit n S i (t i)) * planeWord n S t l)⁻¹).val ∈ _
    rw [mul_inv_rev, Units.val_mul, planeUnit_inv]
    exact even_mul (form n k) S (basis n k) ih (planeUnit_even n S i _)

private theorem planeWord_norm (t : Fin n → Sˣ) (l : List (Fin n)) :
    reversion (form n k) S (planeWord n S t l).val * (planeWord n S t l).val =
      algebraMap S _ ((l.map fun i => (t i : S)).prod) := by
  let q := form n k
  induction l with
  | nil =>
    change reversion q S 1 * 1 = algebraMap S _ 1
    rw [reversion_one q S (basis n k), mul_one, map_one]
  | cons i l ih =>
    let a := planeUnit n S i (t i)
    let d := planeWord n S t l
    change reversion q S (a.val * d.val) * (a.val * d.val) =
      algebraMap S _ ((t i : S) * (l.map fun i => (t i : S)).prod)
    rw [reversion_mul q S (basis n k), show reversion q S a.val =
      algebraMap S _ (t i : S) * (a⁻¹).val from planeUnit_norm n S i (t i)]
    rw [mul_assoc (reversion q S d.val), mul_assoc (algebraMap S _ (t i : S)),
      ← mul_assoc (a⁻¹).val a.val d.val, Units.inv_mul, one_mul, ← mul_assoc]
    rw [← Algebra.commutes (t i : S) (reversion q S d.val), mul_assoc, ih, map_mul]

private theorem planeWord_mul_vector (t : Fin n → Sˣ) (l : List (Fin n)) (j : OddIndices n) :
    (planeWord n S t l).val * cliffordVector n S j =
      ((l.map fun i => (planeScale n S i (t i) j : S)).prod) •
        (cliffordVector n S j * (planeWord n S t l).val) := by
  induction l with
  | nil => simp [planeWord]
  | cons i l ih =>
    let a := planeUnit n S i (t i)
    let d := planeWord n S t l
    let c : S := (l.map fun i => (planeScale n S i (t i) j : S)).prod
    let b : S := planeScale n S i (t i) j
    let v := cliffordVector n S j
    change (a.val * d.val) * v = (b * c) • (v * (a.val * d.val))
    have ha : a.val * v = b • (v * a.val) := planeUnit_mul_vector n S i (t i) j
    calc
      _ = a.val * (d.val * v) := mul_assoc _ _ _
      _ = c • ((a.val * v) * d.val) := by rw [ih, mul_smul_comm, mul_assoc]
      _ = (b * c) • (v * (a.val * d.val)) := by
        rw [ha, smul_mul_assoc, smul_smul, mul_comm c b, mul_assoc]

private def diagonalUnit (t : Fin n → Sˣ) : (oddClifford n S)ˣ :=
  planeWord n S t (List.finRange n)

private theorem diagonalUnit_val (t : Fin n → Sˣ) :
    (diagonalUnit n S t).val =
      (List.ofFn fun i : Fin n => (t i : S) • (E n S i * F n S i) + F n S i * E n S i).prod := by
  rw [List.ofFn_eq_map]
  change (Units.coeHom _) ((List.finRange n).map _).prod = _
  rw [map_list_prod, List.map_map]
  rfl

private theorem diagonalUnit_norm (t : Fin n → Sˣ) :
    reversion (form n k) S (diagonalUnit n S t).val * (diagonalUnit n S t).val =
      algebraMap S _ (∏ i, (t i : S)) := by
  exact (planeWord_norm n S t (List.finRange n)).trans (congrArg (algebraMap S _)
    (by rw [← List.ofFn_eq_map, List.prod_ofFn]))

private def diagonalScale (t : Fin n → Sˣ) (j : OddIndices n) : Sˣ :=
  match j with
  | .inl (.inl i) => t i
  | .inl (.inr i) => (t i)⁻¹
  | .inr () => 1

private theorem planeScale_prod (t : Fin n → Sˣ) (j : OddIndices n) :
    (∏ i, planeScale n S i (t i) j) = diagonalScale n S t j := by
  cases j with
  | inl j =>
    cases j with
    | inl j =>
      rw [Finset.prod_eq_single j]
      · simp [planeScale, diagonalScale]
      · intro i _ hi
        simp [planeScale, Ne.symm hi]
      · simp
    | inr j =>
      rw [Finset.prod_eq_single j]
      · simp [planeScale, diagonalScale]
      · intro i _ hi
        simp [planeScale, Ne.symm hi]
      · simp
  | inr j =>
    cases j
    simp [planeScale, diagonalScale]

private theorem diagonalUnit_mul_vector (t : Fin n → Sˣ) (j : OddIndices n) :
    (diagonalUnit n S t).val * cliffordVector n S j =
      (diagonalScale n S t j : S) • (cliffordVector n S j * (diagonalUnit n S t).val) := by
  rw [← planeScale_prod n S t j]
  simpa only [diagonalUnit, ← List.ofFn_eq_map, List.prod_ofFn, Units.coe_prod] using
    planeWord_mul_vector n S t (List.finRange n) j

private theorem diagonalUnit_action (t : Fin n → Sˣ)
    (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) (hg : IsDiagonalAction t g) :
    IsVectorAction (form n k) S (diagonalUnit n S t) g := by
  let q := form n k
  let d := diagonalUnit n S t
  let v := vectors q S
  have heq : v.comp g.toLinearMap = (conjugationLinear q S d).comp v := by
    apply ((basis n k).baseChange S).ext
    intro j
    rw [Basis.baseChange_apply]
    change v (g (basisVector n S j)) = conjugate q S d (v (basisVector n S j))
    have hscale : g (basisVector n S j) = (diagonalScale n S t j : S) • basisVector n S j := by
      rcases j with (j | j)
      · rcases j with (i | i)
        · exact hg.1 i
        · exact hg.2.1 i
      · cases j
        simpa only [diagonalScale, Units.val_one, one_smul, basisVector] using hg.2.2
    rw [hscale, map_smul]
    change (diagonalScale n S t j : S) • cliffordVector n S j =
      (d.val * cliffordVector n S j) * (d⁻¹).val
    rw [diagonalUnit_mul_vector n S t j, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  intro x
  exact DFunLike.congr_fun heq x

private theorem scalar_diagonalUnit_norm (t : Fin n → Sˣ) (c : S) :
    let D := (diagonalUnit n S t).val
    let a := algebraMap S (oddClifford n S) c * D
    reversion (form n k) S a * a = algebraMap S _ (c ^ 2 * ∏ i, (t i : S)) := by
  let q := form n k
  let D := (diagonalUnit n S t).val
  let c' := algebraMap S (oddClifford n S) c
  change reversion q S (c' * D) * (c' * D) = _
  rw [reversion_mul q S (basis n k), reversion_scalar q S (basis n k),
    ← Algebra.commutes c (reversion q S D)]
  calc
    _ = (c' * c') * (reversion q S D * D) := by
      have hc : Commute c' (reversion q S D) := Algebra.commutes c _
      change (c' * reversion q S D) * (c' * D) = _
      rw [mul_assoc, ← mul_assoc (reversion q S D) c' D, ← hc.eq]
      simp only [mul_assoc]
    _ = _ := by rw [diagonalUnit_norm n S t, map_mul, pow_two, map_mul]


private theorem liftTorus_norm {R : Type u} [CommRing R] {m : ℕ} (a : liftTorus (R := R) m) :
    a.val.2 ^ 2 * ∏ i, a.val.1 i = 1 := a.property

private def liftedDiagonalUnit (a : liftTorus (R := S) n) : (oddClifford n S)ˣ :=
  Units.map (algebraMap S (oddClifford n S)).toMonoidHom a.val.2 * diagonalUnit n S a.val.1

private theorem liftedDiagonalUnit_val (a : liftTorus (R := S) n) :
    (liftedDiagonalUnit n S a).val = diagonalImplementer (S := S) a := by
  change algebraMap S (oddClifford n S) (a.val.2 : S) * (diagonalUnit n S a.val.1).val = _
  rw [diagonalUnit_val]
  rfl

private theorem scalarConjugation (c : Sˣ) (x : oddClifford n S) :
    conjugate (form n k) S (Units.map (algebraMap S (oddClifford n S)).toMonoidHom c) x = x := by
  let A := oddClifford n S
  let u := Units.map (algebraMap S A).toMonoidHom c
  change u.val * x * (u⁻¹).val = x
  have hc : Commute u.val x := Algebra.commutes (c : S) x
  rw [hc.eq, mul_assoc, Units.mul_inv, mul_one]

private theorem vectorAction_inverse {g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)}
    {a : (oddClifford n S)ˣ} (ha : IsVectorAction (form n k) S a g) :
    IsVectorAction (form n k) S a⁻¹ g.symm := by
  intro x
  have h := ha (g.symm x)
  rw [g.apply_symm_apply] at h
  rw [h, ← conjugate_mul, inv_mul_cancel, conjugate_one]

private theorem liftedDiagonalUnit_action (a : liftTorus (R := S) n)
    (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) (hg : IsDiagonalAction a.val.1 g) :
    IsVectorAction (form n k) S (liftedDiagonalUnit n S a) g := by
  intro x
  rw [liftedDiagonalUnit, conjugate_mul, scalarConjugation]
  exact diagonalUnit_action n S a.val.1 g hg x

private theorem liftedDiagonalUnit_isSpin (a : liftTorus (R := S) n)
    (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) (hg : IsDiagonalAction a.val.1 g) :
    liftedDiagonalUnit n S a ∈ spinUnits (form n k) S := by
  let q := form n k
  let b := basis n k
  let u := liftedDiagonalUnit n S a
  have hv := liftedDiagonalUnit_action n S a g hg
  have hi := vectorAction_inverse n S hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · change algebraMap S (oddClifford n S) (a.val.2 : S) * (diagonalUnit n S a.val.1).val ∈ _
    apply even_mul q S b
    · rw [Algebra.algebraMap_eq_smul_one]
      exact (evenPart q S).smul_mem _ (even_one q S b)
    · exact planeWord_even n S a.val.1 (List.finRange n)
  · change reversion q S (algebraMap S (oddClifford n S) (a.val.2 : S) *
      (diagonalUnit n S a.val.1).val) * (algebraMap S (oddClifford n S) (a.val.2 : S) *
      (diagonalUnit n S a.val.1).val) = 1
    have h := congrArg (Units.val : Sˣ → S) (liftTorus_norm a)
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_one] at h
    rw [scalar_diagonalUnit_norm n S a.val.1 (a.val.2 : S), h, map_one]
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, hv x⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨g.symm x, hi x⟩

private theorem liftTorus_of_cliffordUnit (h₂ : (2 : k) ≠ 0) (t : Fin n → Sˣ)
    (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) (hg : IsDiagonalAction t g)
    (a : (oddClifford n S)ˣ) (ha : a ∈ spinUnits (form n k) S)
    (hv : IsVectorAction (form n k) S a g) :
    ∃! z : liftTorus (R := S) n, z.val.1 = t ∧ a.val = diagonalImplementer (S := S) z := by
  let q := form n k
  let b := basis n k
  let d := diagonalUnit n S t
  have hd := diagonalUnit_action n S t g hg
  have hdi : IsVectorAction q S d⁻¹ g.symm := vectorAction_inverse n S hd
  have hact (x : S ⊗[k] Space n k) :
      conjugate q S (a * d⁻¹) (vectors q S x) = vectors q S x := by
    rw [conjugate_mul, ← hdi, ← hv, g.apply_symm_apply]
  have hcent (x : S ⊗[k] Space n k) :
      Commute (a * d⁻¹).val (vectors q S x) := by
    have h := congrArg (· * (a * d⁻¹).val) (hact x)
    change (a * d⁻¹).val * vectors q S x = vectors q S x * (a * d⁻¹).val
    simpa only [conjugate, mul_assoc, Units.inv_mul, mul_one] using h
  have he : (a * d⁻¹).val ∈ evenPart q S := even_mul q S b ha.1
    (planeWord_inverse_even n S t (List.finRange n))
  have hp : LinearMap.ker q.polarBilin = ⊥ :=
    LinearMap.ker_eq_bot.mpr (perfectPolar n k h₂).1
  obtain ⟨c, hc⟩ := regular_scalarCentralizer q S b (Or.inl hp) he hcent
  have hcd : a.val = algebraMap S (oddClifford n S) c * d.val := by
    have h := congrArg (· * d.val) hc
    simpa only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one] using h
  have hn : c ^ 2 * ∏ i, (t i : S) = 1 := by
    apply scalar_tensor_injective q S b
    have h := ha.2.1
    change reversion q S a.val * a.val = 1 at h
    rw [hcd, scalar_diagonalUnit_norm n S t c] at h
    exact h.trans (map_one _).symm
  let cU : Sˣ := ⟨c, c * ∏ i, (t i : S),
    by rw [← mul_assoc, ← pow_two, hn], by rw [mul_comm, ← mul_assoc, ← pow_two, hn]⟩
  let z : liftTorus (R := S) n := ⟨(t, cU), by
    apply Units.ext
    change (cU ^ 2 * ∏ i, t i : Sˣ).val = _
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_one] using hn⟩
  have hz : a.val = diagonalImplementer (S := S) z := by
    rw [← liftedDiagonalUnit_val]
    exact hcd
  refine ⟨z, ⟨rfl, hz⟩, ?_⟩
  intro z' hz'
  apply Subtype.ext
  apply Prod.ext
  · exact hz'.1
  · apply Units.ext
    apply scalar_tensor_injective q S b
    have h : (liftedDiagonalUnit n S z').val = (liftedDiagonalUnit n S z).val :=
      (liftedDiagonalUnit_val n S z').trans (hz'.2.symm.trans (hz.trans (liftedDiagonalUnit_val n S z).symm))
    change algebraMap S (oddClifford n S) (z'.val.2 : S) * (diagonalUnit n S z'.val.1).val =
      algebraMap S (oddClifford n S) c * d.val at h
    rw [hz'.1] at h
    change algebraMap S (oddClifford n S) (z'.val.2 : S) * d.val =
      algebraMap S (oddClifford n S) c * d.val at h
    simpa only [mul_assoc, Units.mul_inv, mul_one] using congrArg (· * (d⁻¹).val) h

theorem diagonalSpinPoints_all (h₂ : (2 : k) ≠ 0) (t : Fin n → Sˣ)
    (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) (hg : IsDiagonalAction t g) :
    (∀ a : (oddClifford n S)ˣ,
      (a ∈ spinUnits (form n k) S ∧ IsVectorAction (form n k) S a g) ↔
      ∃! z : liftTorus (R := S) n, z.val.1 = t ∧ a.val = diagonalImplementer (S := S) z) ∧
    (∀ z : liftTorus (R := S) n, z.val.1 = t →
      ∃ a : (oddClifford n S)ˣ, a ∈ spinUnits (form n k) S ∧
        IsVectorAction (form n k) S a g ∧ a.val = diagonalImplementer (S := S) z) := by
  have hdiag (z : liftTorus (R := S) n) (hz : z.val.1 = t) : IsDiagonalAction z.val.1 g := hz ▸ hg
  constructor
  · intro a
    constructor
    · exact fun h => liftTorus_of_cliffordUnit n S h₂ t g hg a h.1 h.2
    · rintro ⟨z, ⟨hz, ha⟩, -⟩
      have he : a = liftedDiagonalUnit n S z :=
        Units.ext (ha.trans (liftedDiagonalUnit_val n S z).symm)
      rw [he]
      exact ⟨liftedDiagonalUnit_isSpin n S z g (hdiag z hz),
        liftedDiagonalUnit_action n S z g (hdiag z hz)⟩
  · intro z hz
    exact ⟨liftedDiagonalUnit n S z, liftedDiagonalUnit_isSpin n S z g (hdiag z hz),
      liftedDiagonalUnit_action n S z g (hdiag z hz), liftedDiagonalUnit_val n S z⟩


theorem diagonalSpinPoints : DiagonalSpinPoints.{u} := by
  intro k _ n h₂ S t g hg
  exact diagonalSpinPoints_all n S h₂ t g hg

end DiagonalClifford

/-- The norm equation eliminates the first hyperbolic scale using the scalar
and the remaining hyperbolic scales. -/
def liftedTorusCoordinates (R : Type u) [CommRing R] (n : ℕ) :
    liftTorus (R := R) (n + 1) ≃* (Fin (n + 1) → Rˣ) where
  toFun a := Fin.cons a.val.2 (a.val.1 ∘ Fin.succ)
  invFun t := ⟨(Fin.cons ((t 0) ^ 2 * ∏ i : Fin n, t i.succ)⁻¹ (t ∘ Fin.succ), t 0), by
    change (t 0) ^ 2 *
      (∏ i, Fin.cons ((t 0) ^ 2 * ∏ i : Fin n, t i.succ)⁻¹ (t ∘ Fin.succ) i) = 1
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    calc
      _ = ((t 0) ^ 2 * ∏ i : Fin n, t i.succ) * ((t 0) ^ 2 * ∏ i : Fin n, t i.succ)⁻¹ := by
        ac_rfl
      _ = 1 := mul_inv_cancel _⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
        have h := liftTorus_norm a
        rw [Fin.prod_univ_succ] at h
        apply inv_eq_of_mul_eq_one_left
        calc
          _ = a.val.2 ^ 2 * (a.val.1 0 * ∏ i : Fin n, a.val.1 i.succ) := by ac_rfl
          _ = 1 := h
      · rfl
    · rfl
  right_inv t := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  map_mul' a b := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i

theorem liftTorusCoordinates : LiftTorusCoordinates.{u} := by
  intro R _ n
  exact ⟨liftedTorusCoordinates R n, fun _ => rfl⟩

end

end DiagonalSpin

section CliffordEquivariance

open AlgebraicGeometry
open scoped TensorProduct
open CliffordAlgebra
open Albert.SpinSpecification (ScalarClifford ExtendedForm vectors reversion evenPart
  conjugate spinUnits IsVectorAction)
open private cliffordEquiv cliffordEquiv_vector cliffordEquiv_even
  from LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel

noncomputable section

variable {k : Type u} [Field k] (n : ℕ) (S : CommAlgCat.{u} k)

private theorem scalarClifford_hom_ext {A : Type u} [Semiring A] [Algebra S A]
    {f g : ScalarClifford (form n k) S →ₐ[S] A}
    (h : ∀ x, f (vectors (form n k) S x) = g (vectors (form n k) S x)) : f = g := by
  let e := cliffordEquiv (form n k) S (basis n k)
  have H : f.comp e.symm.toAlgHom = g.comp e.symm.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    ext x
    change f (e.symm (ι _ x)) = g (e.symm (ι _ x))
    have he : e.symm (ι _ x) = vectors (form n k) S x :=
      (e.symm_apply_eq).mpr (cliffordEquiv_vector _ _ _ x).symm
    rw [he]
    exact h x
  exact AlgHom.ext fun a => by simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] using DFunLike.congr_fun H (e a)

private def conjugateAlgebraHom (a : (ScalarClifford (form n k) S)ˣ) :
    ScalarClifford (form n k) S →ₐ[S] ScalarClifford (form n k) S where
  toFun := conjugate (form n k) S a
  map_one' := by simp [conjugate]
  map_zero' := by simp [conjugate]
  map_add' x y := by simp [conjugate, mul_add, add_mul]
  map_mul' x y := by simp [conjugate, mul_assoc, ← mul_assoc (a⁻¹).val a.val (y * (a⁻¹).val)]
  commutes' r := by
    change a.val * algebraMap S _ r * (a⁻¹).val = algebraMap S _ r
    rw [← Algebra.commutes r a.val, mul_assoc, Units.mul_inv, mul_one]

private theorem cliffordMap_reversion {V : Type u} [AddCommGroup V] [Module S V]
    {Q : QuadraticForm S V} (h : Q →qᵢ Q) (x : CliffordAlgebra Q) :
    reverse (CliffordAlgebra.map h x) = CliffordAlgebra.map h (reverse x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul x y hx hy => simp only [map_mul, reverse.map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem cliffordMap_even {V : Type u} [AddCommGroup V] [Module S V]
    {Q : QuadraticForm S V} (h : Q →qᵢ Q) (hs : Function.Surjective h)
    {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 0) :
    CliffordAlgebra.map h x ∈ evenOdd Q 0 := by
  have hr : h.range = ⊤ := LinearMap.range_eq_top.mpr hs
  have hi : (LinearMap.range (ι Q)).map (CliffordAlgebra.map h).toLinearMap =
      LinearMap.range (ι Q) := by rw [ι_range_map_map, hr, Submodule.map_top]
  have he : (evenOdd Q 0).map (CliffordAlgebra.map h).toLinearMap = evenOdd Q 0 := by
    simp only [evenOdd, Submodule.map_iSup, Submodule.map_pow, hi]
  rw [← he]
  exact ⟨x, hx, rfl⟩

theorem isometry_clifford_equivariance (h : specialOrthogonal n S) :
    ∃! φ : ScalarClifford (form n k) S ≃ₐ[S] ScalarClifford (form n k) S,
      (∀ x, φ (vectors (form n k) S x) = vectors (form n k) S (h.val x)) ∧
      (∀ a, a ∈ spinUnits (form n k) S → Units.map φ.toMonoidHom a ∈ spinUnits (form n k) S) ∧
      (∀ a, IsVectorAction (form n k) S a h.val → ∀ x,
        φ x = conjugate (form n k) S a x) := by
  let q := form n k
  let b := basis n k
  let e := cliffordEquiv q S b
  let Q := ExtendedForm q S b
  let g : Q →qᵢ Q := ⟨h.val.toLinearMap, h.property.1⟩
  let g' : Q →qᵢ Q := ⟨h.val.symm.toLinearMap, (h⁻¹).property.1⟩
  let f := CliffordAlgebra.map g
  let f' := CliffordAlgebra.map g'
  have h₁ : Function.LeftInverse f' f :=
    CliffordAlgebra.leftInverse_map_of_leftInverse g g'
      h.val.left_inv
  have h₂ : Function.LeftInverse f f' :=
    CliffordAlgebra.leftInverse_map_of_leftInverse g' g
      h.val.right_inv
  let u := AlgEquiv.ofAlgHom f f' (AlgHom.ext h₂) (AlgHom.ext h₁)
  let φ := (e.trans u).trans e.symm
  have hvec (x : S ⊗[k] Space n k) : φ (vectors q S x) = vectors q S (h.val x) := by
    change e.symm (f (e (vectors q S x))) = vectors q S (h.val x)
    rw [cliffordEquiv_vector, map_apply_ι]
    exact e.symm_apply_eq.mpr (cliffordEquiv_vector q S b (h.val x)).symm
  have hrev (x : ScalarClifford q S) : reversion q S (φ x) = φ (reversion q S x) := by
    apply e.injective
    rw [show e (reversion q S (φ x)) = reverse (e (φ x)) from baseChangeEquiv_reverse S q b _]
    change reverse (e (e.symm (f (e x)))) = e (e.symm (f (e (reversion q S x))))
    rw [e.apply_symm_apply, e.apply_symm_apply,
      show e (reversion q S x) = reverse (e x) from baseChangeEquiv_reverse S q b _]
    exact cliffordMap_reversion S g (e x)
  have heven (x : ScalarClifford q S) (hx : x ∈ evenPart q S) : φ x ∈ evenPart q S := by
    apply (cliffordEquiv_even q S b (φ x)).mp
    change e (e.symm (f (e x))) ∈ _
    rw [e.apply_symm_apply]
    exact cliffordMap_even S g h.val.surjective ((cliffordEquiv_even q S b x).mpr hx)
  have hpres (a : (ScalarClifford q S)ˣ)
      (ha : Set.MapsTo (conjugate q S a) (LinearMap.range (vectors q S))
        (LinearMap.range (vectors q S))) :
      Set.MapsTo (conjugate q S (Units.map φ.toMonoidHom a)) (LinearMap.range (vectors q S))
        (LinearMap.range (vectors q S)) := by
    rintro y ⟨x, rfl⟩
    obtain ⟨w, hw⟩ := ha (LinearMap.mem_range_self (vectors q S) (h.val.symm x))
    refine ⟨h.val w, ?_⟩
    rw [← hvec w, hw]
    have h' := hvec (h.val.symm x)
    rw [h.val.apply_symm_apply] at h'
    rw [← h']
    simp only [conjugate, map_mul, Units.coe_map, ← map_inv]
    rfl
  refine ⟨φ, ⟨hvec, ?_, ?_⟩, ?_⟩
  · intro a ha
    rcases ha with ⟨he, hn, hforwards, hbackwards⟩
    refine ⟨heven _ he, ?_, hpres a hforwards, ?_⟩
    · change reversion q S (φ a.val) * φ a.val = 1
      rw [hrev, ← map_mul, hn, map_one]
    · rw [← map_inv]
      exact hpres a⁻¹ hbackwards
  · intro a ha x
    have he : φ.toAlgHom = conjugateAlgebraHom n S a := by
      apply scalarClifford_hom_ext n S
      intro y
      exact (hvec y).trans (ha y)
    exact DFunLike.congr_fun he x
  · intro θ hθ
    have he : θ.toAlgHom = φ.toAlgHom := scalarClifford_hom_ext n S (fun x =>
      (hθ.1 x).trans (hvec x).symm)
    exact AlgEquiv.ext fun x => DFunLike.congr_fun he x


theorem cliffordEquivariance : CliffordEquivariance.{u} := by
  intro k _ n S h
  exact isometry_clifford_equivariance n S h

end

end CliffordEquivariance

section DiagonalScheme

open AlgebraicGeometry CategoryTheory Opposite Matrix Module
open scoped TensorProduct
open scoped CategoryTheory.MonObj
open Specs.StandardGroups (multiplicativePowerGroup LaurentPowerCoordinates multiplicativePowerPoints
  laurentVariable)
open Albert.SpinSpecification (SchemePoints)
open private Representation.equiv Representation.naturality Representation.hopf Representation.convolutionIso spectrumPointsIso laurentPowerIso
  laurentPowerMulEquiv_eval laurentPowerMulEquiv basis_expansion
  from LinearAlgebraicGroups.Affine.StandardGroups

noncomputable section

variable {k : Type u} [Field k] (n : ℕ) (S : CommAlgCat.{u} k)

private abbrev MatrixIndex := ULift.{u} (OddIndices n)

private theorem gram_entry (i j : MatrixIndex n) :
    gramOver (k := k) n S i j =
      algebraMap k S ((form n k).polarBilin (basis n k i.down) (basis n k j.down)) := by
  simp only [gram, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply,
    matrixBasis, Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply]

private theorem diagonalScale_preserves_gram (t : Fin n → Sˣ) (i j : MatrixIndex n) :
    (diagonalScale n S t i.down : S) * gramOver (k := k) n S i j *
      (diagonalScale n S t j.down : S) = gramOver (k := k) n S i j := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  simp only [gram_entry]
  rcases i with (i | i)
  · rcases i with (i | i)
    · rw [oddBasis_e_polar]
      by_cases h : j = .inl (.inr i)
      · subst j
        simp [diagonalScale, Units.mul_inv]
      · rw [ite_eq_right h, map_zero, mul_zero, zero_mul]
    · rw [oddBasis_f_polar]
      by_cases h : j = .inl (.inl i)
      · subst j
        simp [diagonalScale, Units.inv_mul]
      · rw [ite_eq_right h, map_zero, mul_zero, zero_mul]
  · cases i
    rcases j with (j | j)
    · have h := polarCoordinates n k (basis n k (.inr ())) (basis n k (.inl j))
      rw [oddBasis_line, oddBasis_hyperbolic] at h
      rw [oddBasis_line, oddBasis_hyperbolic]
      rw [show (form n k).polarBilin (0, 1) (Pi.single j 1, 0) = 0 by simpa using h]
      simp
    · cases j
      simp [diagonalScale]

private theorem diagonalScale_det (t : Fin n → Sˣ) :
    (∏ i : MatrixIndex n, (diagonalScale n S t i.down : S)) = 1 := by
  rw [Fintype.prod_equiv (Equiv.ulift : MatrixIndex n ≃ OddIndices n)
    (fun i => (diagonalScale n S t i.down : S)) (fun i => (diagonalScale n S t i : S)) (fun _ => rfl)]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [diagonalScale, Units.val_one, mul_one, ← Finset.prod_mul_distrib,
    Units.mul_inv, Finset.prod_const_one]

private def diagonalIsometryMatrix (t : Fin n → Sˣ) : orthogonalMatrices (k := k) n S :=
  let d : MatrixIndex n → S := fun i => diagonalScale n S t i.down
  ⟨⟨diagonal d, by rw [det_diagonal]; exact diagonalScale_det n S t⟩, by
    change (diagonal d)ᵀ * _ * diagonal d = _
    rw [diagonal_transpose]
    exact Matrix.ext fun i j => by
      rw [mul_diagonal, diagonal_mul]
      exact diagonalScale_preserves_gram n S t i j⟩

private def diagonalIsometryMatrixHom : (Fin n → Sˣ) →* orthogonalMatrices (k := k) n S where
  toFun := diagonalIsometryMatrix n S
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change diagonal (fun i : MatrixIndex n => (diagonalScale n S 1 i.down : S)) = 1
    rw [← diagonal_one]
    congr 1
    funext ⟨i⟩
    rcases i with (i | i)
    · cases i <;> simp [diagonalScale]
    · cases i
      rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change diagonal (fun i : MatrixIndex n => (diagonalScale n S (a * b) i.down : S)) =
      diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext ⟨i⟩
    rcases i with (i | i)
    · cases i <;> simp [diagonalScale, mul_comm]
    · cases i
      simp [diagonalScale]

private theorem diagonalIsometryMatrix_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (t : Fin n → Sˣ) :
    mapOrthogonal n f (diagonalIsometryMatrix n S t) =
      diagonalIsometryMatrix n T (fun i => Units.map f.hom.toMonoidHom (t i)) := by
  apply Subtype.ext
  apply Subtype.ext
  change f.hom.toRingHom.mapMatrix
    (diagonal (fun i : MatrixIndex n => (diagonalScale n S t i.down : S))) = diagonal _
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  by_cases h : i = j
  · subst j
    simp only [diagonal_apply_eq]
    rcases i with ⟨i⟩
    rcases i with (i | i)
    · cases i <;> rfl
    · cases i
      exact map_one f.hom
  · simp only [diagonal_apply_ne _ h, map_zero]

private abbrev orthogonalTorusModel := multiplicativePowerGroup k (ULift.{u} (Fin n))

private def orthogonalTorusFunIso :
    (groupPointsFunctor k).obj (orthogonalTorusModel (k := k) n).val ≅
      multiplicativePowerPoints k (ULift.{u} (Fin n)) :=
  spectrumPointsIso laurentPowerIso

private def finiteTorusUnits (n : ℕ) : CommAlgCat.{u} k ⥤ GrpCat.{u} where
  obj S := GrpCat.of (Fin n → Sˣ)
  map f := GrpCat.ofHom (MonoidHom.pi (fun i =>
    (Units.map f.hom.toMonoidHom).comp (Pi.evalMonoidHom _ i)))
  map_id _ := by apply GrpCat.ext; intro a; rfl
  map_comp _ _ := by apply GrpCat.ext; intro a; rfl

private def torusReindexIso (n : ℕ) :
    multiplicativePowerPoints k (ULift.{u} (Fin n)) ≅ finiteTorusUnits (k := k) n :=
  NatIso.ofComponents (fun _ =>
    (show (ULift.{u} (Fin n) → _) ≃* (Fin n → _) from
      { toFun := fun t i => t ⟨i⟩
        invFun := fun t i => t i.down
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }).toGrpIso) (by
    intro S T f
    apply GrpCat.ext
    intro t
    rfl)

private def orthogonalTorusUnitsIso :
    (groupPointsFunctor k).obj (orthogonalTorusModel (k := k) n).val ≅
      finiteTorusUnits (k := k) n :=
  orthogonalTorusFunIso n ≪≫ torusReindexIso n

private def torusPointsToUnits :
    SchemePoints (orthogonalTorusModel (k := k) n).val S ≃* (Fin n → Sˣ) :=
  ((orthogonalTorusUnitsIso n).app S).groupIsoToMulEquiv

set_option maxHeartbeats 700000 in
set_option maxHeartbeats 1000000 in
private theorem torusPointsToUnits_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (p : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    torusPointsToUnits n T (mapPoints f p) =
      fun i => Units.map f.hom.toMonoidHom (torusPointsToUnits n S p i) := by
  let v := orthogonalTorusUnitsIso (k := k) n
  have h := ConcreteCategory.congr_hom (v.hom.naturality f) p
  exact h

private def diagonalOrthogonalNatural :
    (groupPointsFunctor k).obj (orthogonalTorusModel (k := k) n).val ⟶
      (groupPointsFunctor k).obj (specialOrthogonalGroup (k := k) n).val where
  app S := GrpCat.ofHom <|
    (orthogonalMatrixPoints (k := k) n).inv.app S |>.hom.comp
      ((diagonalIsometryMatrixHom n S).comp (torusPointsToUnits n S).toMonoidHom)
  naturality {S T} f := by
    apply GrpCat.ext
    intro a
    change SchemePoints (orthogonalTorusModel (k := k) n).val S at a
    let o := orthogonalMatrixPoints (k := k) n
    change o.inv.app T (diagonalIsometryMatrix n T (torusPointsToUnits n T (mapPoints f a))) =
      mapPoints f (o.inv.app S (diagonalIsometryMatrix n S (torusPointsToUnits n S a)))
    rw [torusPointsToUnits_natural, ← diagonalIsometryMatrix_natural n f]
    exact ConcreteCategory.congr_hom (o.inv.naturality f) _

/-- The diagonal torus morphism, in the ordinary coordinates of the hyperbolic planes. -/
def orthogonalTorusInclusion :
    (orthogonalTorusModel (k := k) n).val ⟶ (specialOrthogonalGroup (k := k) n).val :=
  (AffineAlgebraicGroup.groupHomEquiv _ _).symm (diagonalOrthogonalNatural n)

private theorem orthogonalTorusInclusion_matrix (a : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    (orthogonalMatrixPoints n).hom.app S (a ≫ (orthogonalTorusInclusion n).hom.hom) =
      diagonalIsometryMatrix n S (torusPointsToUnits n S a) := by
  have h := congrArg (fun f => f.app S a)
    ((AffineAlgebraicGroup.groupHomEquiv (orthogonalTorusModel n) (specialOrthogonalGroup n)).apply_symm_apply
      (diagonalOrthogonalNatural (k := k) n))
  change a ≫ (orthogonalTorusInclusion n).hom.hom = (diagonalOrthogonalNatural n).app S a at h
  rw [h]
  exact ConcreteCategory.congr_hom ((orthogonalMatrixPoints (k := k) n).inv_hom_id_app S) _

private theorem orthogonalTorusInclusion_action (h₂ : (2 : k) ≠ 0)
    (a : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    IsDiagonalAction (torusPointsToUnits n S a)
      (orthogonalPoints n h₂ S (a ≫ (orthogonalTorusInclusion n).hom.hom)).val := by
  let p := a ≫ (orthogonalTorusInclusion n).hom.hom
  let g := (orthogonalPoints n h₂ S p).val
  let t := torusPointsToUnits n S a
  let b := (matrixBasis (k := k) n).baseChange S
  have hm : g.toLinearMap.toMatrix b b =
      diagonal (fun i : MatrixIndex n => (diagonalScale n S t i.down : S)) := by
    exact congrArg (fun x : orthogonalMatrices (k := k) n S => x.val.val)
      ((MulEquiv.ofBijective (isometryMatrix n h₂ S) (isometryMatrix_bijective n h₂ S)).apply_symm_apply
        ((orthogonalMatrixPoints n).hom.app S p)) |>.trans
      (congrArg (fun x : orthogonalMatrices (k := k) n S => x.val.val)
        (orthogonalTorusInclusion_matrix n S a))
  have hb (j : OddIndices n) : b ⟨j⟩ = basisVector n S j := by
    rw [Basis.baseChange_apply]
    simp [matrixBasis, basisVector]
  have hw (j : OddIndices n) : g (basisVector n S j) =
      (diagonalScale n S t j : S) • basisVector n S j := by
    rw [← hb]
    apply b.repr.injective
    ext i
    have h := congrFun (congrFun hm i) (ULift.up j)
    rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe] at h
    rw [h, map_smul, Finsupp.smul_apply, Basis.repr_self, diagonal_apply, Finsupp.single_apply]
    split_ifs with hi hj hj
    · cases hi
      simp
    · exact (hj hi.symm).elim
    · exact (hi hj.symm).elim
    · simp
  refine ⟨fun i => hw (.inl (.inl i)), fun i => hw (.inl (.inr i)), ?_⟩
  simpa [diagonalScale, basisVector] using hw (.inr ())


set_option maxHeartbeats 700000 in
private theorem orthogonalEvaluation_entry (f : OrthogonalCoordinates (k := k) n →ₐ[k] S)
    (i j : MatrixIndex n) :
    f (quo n ((universalSpecialLinear (k := k) n).val i j)) = (orthogonalEvaluation n S f).val.val i j := by
  let A := Specs.StandardGroups.SLCoordinates k (MatrixIndex n)
  let a : CommAlgCat.of k A ⟶ S := CommAlgCat.ofHom (f.comp (quo n))
  have h := Representation.naturality (slRep (k := k) (n := n)) a (AlgHom.id k A)
  rw [AlgHom.comp_id] at h
  exact (congrArg (fun M : Matrix.SpecialLinearGroup (MatrixIndex n) S => M.val i j) h).symm

private theorem spectrumPointsIso_apply {A : Type u} [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] {F : TestAlgebra k ⥤ GrpCat.{u}}
    (c : convolutionPoints (CommHopfAlgCat.of k A) ≅ F) (f : A →ₐ[k] S) :
    (spectrumPointsIso c).hom.app S ((testSpec k).map (CommAlgCat.ofHom f).op) =
      c.hom.app S (WithConv.toConv f) := by
  let e := hopfSpecPointIso (CommHopfAlgCat.of k A)
  have he : e.hom.app S (WithConv.toConv f) = (testSpec k).map (CommAlgCat.ofHom f).op := rfl
  have hi := ConcreteCategory.congr_hom (e.hom_inv_id_app S) (WithConv.toConv f)
  change e.inv.app S (e.hom.app S (WithConv.toConv f)) = _ at hi
  change c.hom.app S (e.inv.app S ((testSpec k).map (CommAlgCat.ofHom f).op)) = _
  exact (congrArg (fun p : Points ((hopfSpec (CommRingCat.of k)).obj (op (CommHopfAlgCat.of k A))).X S =>
    c.hom.app S (e.inv.app S p)) he.symm).trans
    (congrArg (fun x : (convolutionPoints (CommHopfAlgCat.of k A)).obj S => c.hom.app S x) hi)

private abbrev LaurentTorus := LaurentPowerCoordinates k (ULift.{u} (Fin n))

private def universalTorusUnits : Fin n → (LaurentTorus (k := k) n)ˣ :=
  torusPointsToUnits n (CommAlgCat.of k (LaurentTorus (k := k) n)) (𝟙 _)

set_option maxHeartbeats 1200000 in
private theorem universalTorusUnits_val (i : Fin n) :
    (universalTorusUnits (k := k) n i : LaurentTorus (k := k) n) =
      laurentVariable k (ULift.{u} (Fin n)) ⟨i⟩ := by
  let A := LaurentTorus (k := k) n
  let S := CommAlgCat.of k A
  let e := orthogonalTorusFunIso (k := k) n
  let f := AlgHom.id k A
  have hmap : (testSpec k).map (CommAlgCat.ofHom f).op = 𝟙 _ :=
    (testSpec k).map_id _
  change ((e.hom.app S (𝟙 _) : ULift.{u} (Fin n) → Aˣ) ⟨i⟩).val = _
  have h := spectrumPointsIso_apply S laurentPowerIso f
  have hp := congrArg (fun p : SchemePoints (orthogonalTorusModel (k := k) n).val S =>
    ((e.hom.app S p : ULift.{u} (Fin n) → Aˣ) ⟨i⟩).val) hmap.symm
  have he := congrArg (fun t : ULift.{u} (Fin n) → Aˣ => (t ⟨i⟩).val) h
  exact hp.trans (he.trans (laurentPowerMulEquiv_eval S f (ULift.up i)))

private theorem universalTorusUnits_inv_val (i : Fin n) :
    (↑(universalTorusUnits (k := k) n i)⁻¹ : LaurentTorus (k := k) n) =
      AddMonoidAlgebra.single (-(Pi.single (ULift.up i) (1 : ℤ))) 1 := by
  let t := universalTorusUnits (k := k) n i
  apply t.isUnit.mul_right_cancel
  rw [Units.inv_mul, universalTorusUnits_val, laurentVariable, AddMonoidAlgebra.single_mul_single,
    neg_add_cancel, mul_one]
  rfl

private def diagonalCoordinateMap : OrthogonalCoordinates (k := k) n →ₐ[k] LaurentTorus (k := k) n :=
  let S := CommAlgCat.of k (LaurentTorus (k := k) n)
  (orthogonalEvaluation n S).symm (diagonalIsometryMatrix n S (universalTorusUnits n))

set_option maxHeartbeats 1200000 in
private theorem diagonalCoordinateMap_entry (i j : MatrixIndex n) :
    diagonalCoordinateMap (k := k) n (quo n ((universalSpecialLinear (k := k) n).val i j)) =
      (diagonalIsometryMatrix n (CommAlgCat.of k (LaurentTorus (k := k) n))
        (universalTorusUnits n)).val.val i j := by
  let S := CommAlgCat.of k (LaurentTorus (k := k) n)
  rw [orthogonalEvaluation_entry n S, diagonalCoordinateMap, Equiv.apply_symm_apply]

private theorem diagonalCoordinateMap_surjective : Function.Surjective (diagonalCoordinateMap (k := k) n) := by
  let A := LaurentTorus (k := k) n
  let f := diagonalCoordinateMap (k := k) n
  let m := AddMonoidAlgebra.of k (ULift.{u} (Fin n) → ℤ)
  have hpos (i : ULift.{u} (Fin n)) : m (Multiplicative.ofAdd (Pi.single i 1)) ∈ f.range := by
    let j : MatrixIndex n := ⟨.inl (.inl i.down)⟩
    refine ⟨quo n ((universalSpecialLinear (k := k) n).val j j), ?_⟩
    change diagonalCoordinateMap (k := k) n (quo n ((universalSpecialLinear (k := k) n).val j j)) = _
    rw [diagonalCoordinateMap_entry n]
    change diagonal (fun r : MatrixIndex n => (diagonalScale n (CommAlgCat.of k A)
      (universalTorusUnits (k := k) n) r.down : A)) j j = _
    rw [diagonal_apply_eq]
    exact universalTorusUnits_val n i.down
  have hneg (i : ULift.{u} (Fin n)) : m (Multiplicative.ofAdd (Pi.single i 1))⁻¹ ∈ f.range := by
    let j : MatrixIndex n := ⟨.inl (.inr i.down)⟩
    refine ⟨quo n ((universalSpecialLinear (k := k) n).val j j), ?_⟩
    change diagonalCoordinateMap (k := k) n (quo n ((universalSpecialLinear (k := k) n).val j j)) = _
    rw [diagonalCoordinateMap_entry n]
    change diagonal (fun r : MatrixIndex n => (diagonalScale n (CommAlgCat.of k A)
      (universalTorusUnits (k := k) n) r.down : A)) j j = _
    rw [diagonal_apply_eq]
    exact universalTorusUnits_inv_val n i.down
  intro a
  change a ∈ f.range
  induction a using AddMonoidAlgebra.induction_on with
  | of e =>
    rw [← basis_expansion (Multiplicative.ofAdd e), map_prod]
    apply Subalgebra.prod_mem
    intro i _
    change m (Multiplicative.ofAdd (Pi.single i 1) ^ e i) ∈ f.range
    rcases Int.eq_nat_or_neg (e i) with ⟨r, hr | hr⟩
    · rw [hr, zpow_natCast, map_pow]
      exact f.range.pow_mem (hpos i) r
    · rw [hr, _root_.zpow_neg, zpow_natCast, ← inv_pow, map_pow]
      exact f.range.pow_mem (hneg i) r
  | add a b ha hb => exact f.range.add_mem ha hb
  | smul c a ha => exact f.range.smul_mem ha c

set_option maxHeartbeats 1200000 in
private theorem orthogonalTorusInclusion_closed :
    IsClosedImmersion (orthogonalTorusInclusion (k := k) n).hom.hom.left := by
  let A := LaurentTorus (k := k) n
  let φ := diagonalCoordinateMap (k := k) n
  let S := CommAlgCat.of k A
  let a : SchemePoints (orthogonalTorusModel (k := k) n).val S := 𝟙 _
  let j := (orthogonalTorusInclusion (k := k) n).hom.hom
  let p : SchemePoints (specialOrthogonalGroup (k := k) n).val S :=
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op
  have h : j = p := by
    change a ≫ j = p
    have ha : a ≫ j = j := Category.id_comp j
    apply (orthogonalMatrixPoints (k := k) n).app S |>.groupIsoToMulEquiv.injective
    change (orthogonalMatrixPoints n).hom.app S (a ≫ (orthogonalTorusInclusion n).hom.hom) =
      (orthogonalMatrixPoints n).hom.app S p
    rw [orthogonalTorusInclusion_matrix]
    let := Representation.hopf (orthogonalRepresentation (k := k) n)
    have h := spectrumPointsIso_apply S (Representation.convolutionIso (orthogonalRepresentation (k := k) n)) φ
    exact ((orthogonalEvaluation n S).apply_symm_apply _).symm.trans h.symm
  change IsClosedImmersion j.left
  rw [h]
  let B := OrthogonalCoordinates (k := k) n
  let f : CommRingCat.of B ⟶ CommRingCat.of A := CommRingCat.ofHom φ.toRingHom
  exact IsClosedImmersion.spec_of_surjective f (diagonalCoordinateMap_surjective (k := k) n)

/-- The split diagonal torus of the odd special orthogonal model. -/
def orthogonalTorus : Specs.ClosedSubgroup (specialOrthogonalGroup (k := k) n).val :=
  ⟨(orthogonalTorusModel n).val, orthogonalTorusInclusion n, orthogonalTorusInclusion_closed n⟩

theorem orthogonalTorus_split :
    Specs.GeometricRadicals.IsSplitTorus (orthogonalTorus (k := k) n).group :=
  ⟨n, ⟨Iso.refl _⟩⟩

theorem orthogonalTorus_points (h₂ : (2 : k) ≠ 0)
    (a : SchemePoints (orthogonalTorus (k := k) n).group S) :
    IsDiagonalAction (torusPointsToUnits n S a)
      (orthogonalPoints n h₂ S (a ≫ (orthogonalTorus n).inclusion.hom.hom)).val :=
  orthogonalTorusInclusion_action n S h₂ a


theorem splitOrthogonalTorus : SplitOrthogonalTorus.{u} := by
  intro k _ n h₂
  exact ⟨specialOrthogonalGroup n, orthogonalPoints n h₂, orthogonalTorus n, torusPointsToUnits n,
    orthogonalPoints_natural n h₂, orthogonalTorus_split n,
    fun S a => orthogonalTorus_points n S h₂ a⟩

end

end DiagonalScheme


section LiftedTorusAlgebra

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open Albert.SpinSpecification (ScalarClifford vectors spinUnits)
open Albert.SpinFunctor (Spin changeCoefficients)
open private changeCoefficients_vector changeModule from LinearAlgebraicGroups.Albert.SpinFunctor

noncomputable section

variable {k : Type u} [Field k] (n : ℕ) (S : CommAlgCat.{u} k)

private theorem planeUnit_one (i : Fin n) : planeUnit n S i 1 = 1 := by
  apply Units.ext
  change (1 : S) • (E n S i * F n S i) + F n S i * E n S i = 1
  rw [one_smul, cliffordPair_sum]

private theorem planeUnit_mul (i : Fin n) (t s : Sˣ) :
    planeUnit n S i (t * s) = planeUnit n S i t * planeUnit n S i s := by
  apply Units.ext
  change ((t : S) * (s : S)) • (E n S i * F n S i) + F n S i * E n S i =
    (((t : S) • (E n S i * F n S i) + F n S i * E n S i) *
      ((s : S) • (E n S i * F n S i) + F n S i * E n S i))
  exact (cliffordPair_mul (cliffordVectors_square n S (.inl i))
    (cliffordVectors_square n S (.inr i)) (cliffordPair_sum n S i) _ _).symm

private theorem planeUnits_commute (i j : Fin n) (t s : Sˣ) :
    Commute (planeUnit n S i t) (planeUnit n S j s) := by
  by_cases h : i = j
  · subst j
    change planeUnit n S i t * planeUnit n S i s = planeUnit n S i s * planeUnit n S i t
    rw [← planeUnit_mul, ← planeUnit_mul, mul_comm t s]
  · apply Units.ext
    have he : Commute (planeUnit n S i t).val (E n S j) := by
      change (planeUnit n S i t).val * _ = _
      have ht := planeUnit_mul_vector n S i t (.inl (.inl j))
      simpa [planeScale, Ne.symm h] using ht
    have hf : Commute (planeUnit n S i t).val (F n S j) := by
      change (planeUnit n S i t).val * _ = _
      have ht := planeUnit_mul_vector n S i t (.inl (.inr j))
      simpa [planeScale, Ne.symm h] using ht
    exact (((he.mul_right hf).smul_right (s : S)).add_right (hf.mul_right he)).eq

private theorem planeWord_one (l : List (Fin n)) :
    planeWord n S 1 l = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change planeUnit n S i 1 * planeWord n S 1 l = 1
    rw [planeUnit_one, ih, one_mul]

private theorem planeWord_mul (t s : Fin n → Sˣ) (l : List (Fin n)) :
    planeWord n S (t * s) l = planeWord n S t l * planeWord n S s l := by
  induction l with
  | nil => simp [planeWord]
  | cons i l ih =>
    change planeUnit n S i (t i * s i) * planeWord n S (t * s) l =
      (planeUnit n S i (t i) * planeWord n S t l) * (planeUnit n S i (s i) * planeWord n S s l)
    rw [planeUnit_mul, ih]
    have hc : Commute (planeUnit n S i (s i)) (planeWord n S t l) :=
      Commute.list_prod_right _ _ (by
        intro x hx
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
        exact planeUnits_commute n S i j (s i) (t j))
    simp only [mul_assoc]
    rw [← mul_assoc (planeUnit n S i (s i)), hc.eq, mul_assoc]

private def diagonalUnitHom : (Fin n → Sˣ) →* (oddClifford n S)ˣ where
  toFun := diagonalUnit n S
  map_one' := planeWord_one n S (List.finRange n)
  map_mul' t s := planeWord_mul n S t s (List.finRange n)

private def liftedDiagonalUnitHom : liftTorus (R := S) n →* (oddClifford n S)ˣ where
  toFun := liftedDiagonalUnit n S
  map_one' := by
    change Units.map (algebraMap S (oddClifford n S)).toMonoidHom 1 * diagonalUnitHom n S 1 = _
    rw [map_one, map_one, one_mul]
  map_mul' a b := by
    let u := Units.map (algebraMap S (oddClifford n S)).toMonoidHom
    change u (a.val.2 * b.val.2) * diagonalUnitHom n S (a.val.1 * b.val.1) =
      (u a.val.2 * diagonalUnitHom n S a.val.1) * (u b.val.2 * diagonalUnitHom n S b.val.1)
    have hc : Commute (u b.val.2) (diagonalUnitHom n S a.val.1) := by
      apply Units.ext
      exact Algebra.commutes (b.val.2 : S) (diagonalUnitHom n S a.val.1).val
    rw [map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (u b.val.2), hc.eq, mul_assoc]

private theorem changeCoefficients_scalar {S T : CommAlgCat.{u} k}
    (f : S ⟶ T) (a : S) :
    changeCoefficients (form n k) f.hom (algebraMap S (oddClifford n S) a) =
      algebraMap T _ (f.hom a) := by
  change changeCoefficients (form n k) f.hom (a ⊗ₜ[k] (1 : CliffordAlgebra (form n k))) = _
  rw [changeCoefficients, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

private theorem changeCoefficients_cliffordVector {S T : CommAlgCat.{u} k}
    (f : S ⟶ T) (j : OddIndices n) :
    changeCoefficients (form n k) f.hom (cliffordVector n S j) = cliffordVector n T j := by
  change changeCoefficients (form n k) f.hom (vectors (form n k) S (basisVector n S j)) = _
  rw [changeCoefficients_vector]
  change vectors (form n k) T (f.hom 1 ⊗ₜ[k] basis n k j) = _
  rw [map_one]
  rfl

private theorem planeUnit_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T) (i : Fin n) (a : Sˣ) :
    Units.map (changeCoefficients (form n k) f.hom).toMonoidHom (planeUnit n S i a) =
      planeUnit n T i (Units.map f.hom.toMonoidHom a) := by
  apply Units.ext
  change changeCoefficients (form n k) f.hom ((a : S) • (E n S i * F n S i) + F n S i * E n S i) =
    (f.hom (a : S)) • (E n T i * F n T i) + F n T i * E n T i
  simp only [Algebra.smul_def, map_add, map_mul, changeCoefficients_scalar n f,
    changeCoefficients_cliffordVector n f]

private theorem diagonalUnit_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T) (t : Fin n → Sˣ) :
    Units.map (changeCoefficients (form n k) f.hom).toMonoidHom (diagonalUnit n S t) =
      diagonalUnit n T (fun i => Units.map f.hom.toMonoidHom (t i)) := by
  simp only [diagonalUnit, planeWord, map_list_prod, List.map_map, Function.comp_def, planeUnit_natural]

private def mapLiftedTorus {S T : CommAlgCat.{u} k} (f : S ⟶ T) (a : liftTorus (R := S) n) :
    liftTorus (R := T) n :=
  ⟨(fun i => Units.map f.hom.toMonoidHom (a.val.1 i), Units.map f.hom.toMonoidHom a.val.2), by
    change (Units.map f.hom.toMonoidHom a.val.2) ^ 2 *
      (∏ i, Units.map f.hom.toMonoidHom (a.val.1 i)) = 1
    rw [← map_pow, ← map_prod, ← map_mul, liftTorus_norm, map_one]⟩

private theorem liftedDiagonalUnit_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (a : liftTorus (R := S) n) :
    Units.map (changeCoefficients (form n k) f.hom).toMonoidHom (liftedDiagonalUnit n S a) =
      liftedDiagonalUnit n T (mapLiftedTorus n f a) := by
  rw [liftedDiagonalUnit, map_mul, diagonalUnit_natural, liftedDiagonalUnit]
  congr 1

private theorem liftedTorusCoordinates_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (a : liftTorus (R := S) (n + 1)) :
    liftedTorusCoordinates T n (mapLiftedTorus (n + 1) f a) =
      fun i => Units.map f.hom.toMonoidHom (liftedTorusCoordinates S n a i) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end

end LiftedTorusAlgebra

section SpinTorus

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj TensorProduct

open Albert.SpinSpecification (SchemePoints spinUnits vectors IsVectorAction)
open Albert.SpinFunctor (Spin schemePoints schemePoints_naturality changeCoefficients)
open private spinUnitPoints spinUnitPoints_represents vectors_injective
  from LinearAlgebraicGroups.Albert.SpinFunctor
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

noncomputable section

variable {k : Type u} [Field k] (m : ℕ)

/-- The spin torus has the scalar and the remaining hyperbolic scales as coordinates. -/
private def spinTorusParameters (S : CommAlgCat.{u} k) :
    SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S ≃* liftTorus (R := S) (m + 1) :=
  (torusPointsToUnits (m + 1) S).trans (liftedTorusCoordinates S m).symm

private theorem spinTorusParameters_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
    spinTorusParameters m T (mapPoints f a) = mapLiftedTorus (m + 1) f (spinTorusParameters m S a) := by
  apply (liftedTorusCoordinates T m).injective
  rw [liftedTorusCoordinates_natural]
  have eq (S : CommAlgCat.{u} k) (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
      liftedTorusCoordinates S m (spinTorusParameters m S a) = torusPointsToUnits (m + 1) S a :=
    (liftedTorusCoordinates S m).apply_symm_apply _
  rw [eq, eq, torusPointsToUnits_natural]

private def spinTorusOrthogonalPoints (S : CommAlgCat.{u} k) :
    SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S →*
      SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S :=
  (torusPointsToUnits (m + 1) S).symm.toMonoidHom.comp <|
    (MonoidHom.fst (Fin (m + 1) → Sˣ) Sˣ).comp <|
      (liftTorus (R := S) (m + 1)).subtype.comp (spinTorusParameters m S).toMonoidHom

private theorem spinTorusOrthogonalPoints_eval (S : CommAlgCat.{u} k)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
    torusPointsToUnits (m + 1) S (spinTorusOrthogonalPoints m S a) =
      (spinTorusParameters m S a).val.1 :=
  (torusPointsToUnits (m + 1) S).apply_symm_apply _

private def spinTorusProjectionNatural :
    (groupPointsFunctor k).obj (orthogonalTorusModel (k := k) (m + 1)).val ⟶
      (groupPointsFunctor k).obj (orthogonalTorusModel (k := k) (m + 1)).val where
  app S := GrpCat.ofHom (spinTorusOrthogonalPoints m S)
  naturality {S T} f := by
    apply GrpCat.ext
    intro a
    change SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S at a
    change spinTorusOrthogonalPoints m T (mapPoints f a) = mapPoints f (spinTorusOrthogonalPoints m S a)
    apply (torusPointsToUnits (m + 1) T).injective
    rw [spinTorusOrthogonalPoints_eval, torusPointsToUnits_natural,
      spinTorusOrthogonalPoints_eval, spinTorusParameters_natural]
    rfl

/-- Projection of the norm-equation torus onto the hyperbolic scales. -/
def spinTorusProjection :
    (orthogonalTorusModel (k := k) (m + 1)).val ⟶ (orthogonalTorusModel (k := k) (m + 1)).val :=
  (AffineAlgebraicGroup.groupHomEquiv _ _).symm (spinTorusProjectionNatural m)

private theorem spinTorusProjection_points (S : CommAlgCat.{u} k)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
    a ≫ (spinTorusProjection m).hom.hom = spinTorusOrthogonalPoints m S a :=
  congrArg (fun α => α.app S a)
    ((AffineAlgebraicGroup.groupHomEquiv _ _).apply_symm_apply (spinTorusProjectionNatural (k := k) m))

variable (h₂ : (2 : k) ≠ 0)

private def spinTorusVector (S : CommAlgCat.{u} k)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
    (S ⊗[k] Space (m + 1) k) ≃ₗ[S] (S ⊗[k] Space (m + 1) k) :=
  (orthogonalPoints (m + 1) h₂ S
    ((spinTorusOrthogonalPoints m S a) ≫ (orthogonalTorusInclusion (m + 1)).hom.hom)).val

private theorem spinTorusVector_diagonal (S : CommAlgCat.{u} k)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
    IsDiagonalAction (spinTorusParameters m S a).val.1 (spinTorusVector m h₂ S a) := by
  have hd := orthogonalTorusInclusion_action (m + 1) S h₂ (spinTorusOrthogonalPoints m S a)
  rw [spinTorusOrthogonalPoints_eval] at hd
  exact hd

private def spinTorusToSpinPoints (S : CommAlgCat.{u} k) :
    SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S →*
      SchemePoints (spinAlgebraicGroup (k := k) (m + 1)).val S :=
  (schemePoints (form (m + 1) k) (matrixBasis (m + 1)) S).symm.toMonoidHom.comp <|
    ((liftedDiagonalUnitHom (m + 1) S).comp (spinTorusParameters m S).toMonoidHom).codRestrict
      (Spin (form (m + 1) k) S (matrixBasis (m + 1))) (fun a =>
        liftedDiagonalUnit_isSpin (m + 1) S (spinTorusParameters m S a)
          (spinTorusVector m h₂ S a) (spinTorusVector_diagonal m h₂ S a))

private theorem spinTorusToSpinPoints_unit (S : CommAlgCat.{u} k)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
    spinUnitPoints (form (m + 1) k) (matrixBasis (m + 1)) S
      (spinTorusToSpinPoints m h₂ S a) = liftedDiagonalUnit (m + 1) S (spinTorusParameters m S a) := by
  let e := schemePoints (form (m + 1) k) (matrixBasis (m + 1)) S
  exact congrArg (fun x : Spin (form (m + 1) k) S (matrixBasis (m + 1)) => x.val)
    (e.apply_symm_apply _)

private theorem spinUnitPoints_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (a : SchemePoints (spinAlgebraicGroup (k := k) (m + 1)).val S) :
    spinUnitPoints (form (m + 1) k) (matrixBasis (m + 1)) T (mapPoints f a) =
      Units.map (changeCoefficients (form (m + 1) k) f.hom).toMonoidHom
        (spinUnitPoints (form (m + 1) k) (matrixBasis (m + 1)) S a) :=
  congrArg (fun x : Spin (form (m + 1) k) T (matrixBasis (m + 1)) => x.val)
    (schemePoints_naturality (form (m + 1) k) (matrixBasis (m + 1)) f a)

private theorem spinUnitPoints_injective (S : CommAlgCat.{u} k) :
    Function.Injective (spinUnitPoints (form (m + 1) k) (matrixBasis (m + 1)) S) :=
  Subtype.val_injective.comp (schemePoints (form (m + 1) k) (matrixBasis (m + 1)) S).injective

private def spinTorusInclusionNatural :
    (groupPointsFunctor k).obj (orthogonalTorusModel (k := k) (m + 1)).val ⟶
      (groupPointsFunctor k).obj (spinAlgebraicGroup (k := k) (m + 1)).val where
  app S := GrpCat.ofHom (spinTorusToSpinPoints m h₂ S)
  naturality {S T} f := by
    apply GrpCat.ext
    intro a
    change SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S at a
    change spinTorusToSpinPoints m h₂ T (mapPoints f a) = mapPoints f (spinTorusToSpinPoints m h₂ S a)
    apply spinUnitPoints_injective m T
    rw [spinTorusToSpinPoints_unit, spinTorusParameters_natural]
    have h := spinUnitPoints_natural m f (spinTorusToSpinPoints m h₂ S a)
    rw [spinTorusToSpinPoints_unit, liftedDiagonalUnit_natural] at h
    exact h.symm

/-- The intrinsic Clifford implementers of the diagonal scales satisfying the scalar norm equation. -/
def spinTorusInclusion :
    (orthogonalTorusModel (k := k) (m + 1)).val ⟶ (spinAlgebraicGroup (k := k) (m + 1)).val :=
  (AffineAlgebraicGroup.groupHomEquiv _ _).symm (spinTorusInclusionNatural m h₂)

private theorem spinTorusInclusion_points (S : CommAlgCat.{u} k)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
    a ≫ (spinTorusInclusion m h₂).hom.hom = spinTorusToSpinPoints m h₂ S a :=
  congrArg (fun α => α.app S a)
    ((AffineAlgebraicGroup.groupHomEquiv _ _).apply_symm_apply
      (spinTorusInclusionNatural (k := k) m h₂))

private theorem spinTorusImage_eq (S : CommAlgCat.{u} k)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S) :
    (a ≫ (spinTorusInclusion m h₂).hom.hom) ≫ (spinVectorMorphism (m + 1) h₂).hom.hom =
      (a ≫ (spinTorusProjection m).hom.hom) ≫ (orthogonalTorusInclusion (m + 1)).hom.hom := by
  let n := m + 1
  let q := form n k
  let d := spinTorusParameters m S a
  let E := orthogonalPoints n h₂ S
  apply E.injective
  apply Subtype.ext
  ext x
  apply vectors_injective q S (matrixBasis n)
  have hv := spinVectorMorphism_action n h₂ S (a ≫ (spinTorusInclusion m h₂).hom.hom) x
  have hu : spinUnitPoints q (matrixBasis n) S (a ≫ (spinTorusInclusion m h₂).hom.hom) =
      liftedDiagonalUnit n S d :=
    (congrArg (spinUnitPoints q (matrixBasis n) S) (spinTorusInclusion_points m h₂ S a)).trans
      (spinTorusToSpinPoints_unit m h₂ S a)
  change _ = Albert.SpinSpecification.conjugate q S
    (spinUnitPoints q (matrixBasis n) S (a ≫ (spinTorusInclusion m h₂).hom.hom)) _ at hv
  rw [hu] at hv
  have hd := liftedDiagonalUnit_action n S d (spinTorusVector m h₂ S a)
    (spinTorusVector_diagonal m h₂ S a) x
  rw [spinTorusProjection_points]
  exact hv.trans hd.symm

private theorem spinTorus_pullbackPoints (S : CommAlgCat.{u} k)
    (a : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S)
    (b : SchemePoints (spinAlgebraicGroup (k := k) (m + 1)).val S)
    (h : a ≫ (orthogonalTorusInclusion (m + 1)).hom.hom =
      b ≫ (spinVectorMorphism (m + 1) h₂).hom.hom) :
    ∃! c : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S,
      c ≫ (spinTorusProjection m).hom.hom = a ∧ c ≫ (spinTorusInclusion m h₂).hom.hom = b := by
  let n := m + 1
  let E := orthogonalPoints n h₂ S
  let t := torusPointsToUnits n S a
  let g := (E (a ≫ (orthogonalTorusInclusion n).hom.hom)).val
  let e := spinUnitPoints (form n k) (matrixBasis n) S
  have hg : IsDiagonalAction t g := orthogonalTorusInclusion_action n S h₂ a
  have hv : IsVectorAction (form n k) S (e b) g := by
    change IsVectorAction (form n k) S (e b) (E (a ≫ (orthogonalTorusInclusion n).hom.hom)).val
    rw [h]
    exact spinVectorMorphism_action n h₂ S b
  have he : e b ∈ spinUnits (form n k) S :=
    (schemePoints (form n k) (matrixBasis n) S b).property
  obtain ⟨z, hz, hu⟩ := liftTorus_of_cliffordUnit n S h₂ t g hg (e b) he hv
  let c := (spinTorusParameters m S).symm z
  have hc : spinTorusParameters m S c = z := (spinTorusParameters m S).apply_symm_apply _
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · apply (torusPointsToUnits n S).injective
    rw [spinTorusProjection_points, spinTorusOrthogonalPoints_eval, hc]
    exact hz.1
  · apply spinUnitPoints_injective m S
    rw [spinTorusInclusion_points, spinTorusToSpinPoints_unit, hc]
    exact Units.ext ((liftedDiagonalUnit_val n S z).trans hz.2.symm)
  · rintro c' ⟨hc₁, hc₂⟩
    apply (spinTorusParameters m S).injective
    rw [hc]
    apply hu
    constructor
    · rw [spinTorusProjection_points] at hc₁
      exact (spinTorusOrthogonalPoints_eval m S c').symm.trans
        (congrArg (torusPointsToUnits n S) hc₁)
    · rw [spinTorusInclusion_points] at hc₂
      exact (congrArg (fun d => (e d).val) hc₂.symm).trans
        ((congrArg Units.val (spinTorusToSpinPoints_unit m h₂ S c')).trans
          (liftedDiagonalUnit_val n S _))

private theorem spinTorus_pullback :
    IsPullback (spinTorusProjection (k := k) m).hom.hom (spinTorusInclusion m h₂).hom.hom
      (orthogonalTorusInclusion (m + 1)).hom.hom (spinVectorMorphism (m + 1) h₂).hom.hom := by
  let D := orthogonalTorusModel (k := k) (m + 1)
  let G := spinAlgebraicGroup (k := k) (m + 1)
  let O := specialOrthogonalGroup (k := k) (m + 1)
  let f := (spinTorusProjection (k := k) m).hom.hom
  let j := (spinTorusInclusion m h₂).hom.hom
  let i := (orthogonalTorusInclusion (k := k) (m + 1)).hom.hom
  let p := (spinVectorMorphism (m + 1) h₂).hom.hom
  have hw : f ≫ i = j ≫ p := by
    apply hom_ext_of_points D.property.1
    intro S a
    simp only [← Category.assoc]
    exact (spinTorusImage_eq m h₂ S a).symm
  let P := pullback i p
  have hP : IsPullback (pullback.fst i p) (pullback.snd i p) i p := IsPullback.of_hasPullback i p
  let u := hP.lift f j hw
  have hu₁ : u ≫ pullback.fst i p = f := hP.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd i p = j := hP.lift_snd _ _ _
  have : IsAffine D.val.X.left := D.property.1
  have : IsAffine G.val.X.left := G.property.1
  have : IsAffine O.val.X.left := O.property.1
  have hp₀ : IsPullback (pullback.fst i p).left (pullback.snd i p).left i.left p.left :=
    (Over.forget (Spec (CommRingCat.of k))).map_isPullback hP
  have hp₁ : IsAffine P.left := IsAffine.of_isPullback hp₀
  obtain ⟨A, ⟨a⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hp₁
  obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := spinTorus_pullbackPoints m h₂ A.unop
    (a.hom ≫ pullback.fst i p) (a.hom ≫ pullback.snd i p)
    (by
      change (a.hom ≫ pullback.fst i p) ≫ i = (a.hom ≫ pullback.snd i p) ≫ p
      simpa only [Category.assoc] using congrArg (a.hom ≫ ·) hP.w)
  let v := a.inv ≫ c
  have hv₁ : v ≫ f = pullback.fst i p := by
    change (a.inv ≫ c) ≫ f = _
    rw [Category.assoc, hc₁, Iso.inv_hom_id_assoc]
  have hv₂ : v ≫ j = pullback.snd i p := by
    change (a.inv ≫ c) ≫ j = _
    rw [Category.assoc, hc₂, Iso.inv_hom_id_assoc]
  have huv : u ≫ v = 𝟙 D.val.X := by
    apply hom_ext_of_points D.property.1
    intro S x
    have hx := (spinTorusImage_eq m h₂ S x).symm
    let α := spinTorus_pullbackPoints m h₂ S (x ≫ f) (x ≫ j) hx
    obtain ⟨w, _, hw⟩ := α
    rw [Category.comp_id]
    refine (hw (x ≫ u ≫ v) ⟨?_, ?_⟩).trans (hw x ⟨rfl, rfl⟩).symm
    · change (x ≫ u ≫ v) ≫ f = x ≫ f
      simp only [Category.assoc]
      rw [hv₁, ← hu₁]
    · change (x ≫ u ≫ v) ≫ j = x ≫ j
      simp only [Category.assoc]
      rw [hv₂, ← hu₂]
  have hvu : v ≫ u = 𝟙 P := by
    apply hP.hom_ext
    · simp only [Category.assoc, hu₁, hv₁, Category.id_comp]
    · simp only [Category.assoc, hu₂, hv₂, Category.id_comp]
  exact IsPullback.of_iso_pullback ⟨hw⟩ ⟨u, v, huv, hvu⟩ hu₁ hu₂

set_option maxHeartbeats 700000 in
/-- The full inverse image of the marked diagonal torus inside the intrinsic spin scheme. -/
def spinTorus : Specs.ClosedSubgroup (spinAlgebraicGroup (k := k) (m + 1)).val :=
  ⟨(orthogonalTorusModel (m + 1)).val, spinTorusInclusion m h₂, by
    have h : IsPullback (spinTorusProjection (k := k) m).hom.hom.left
        (spinTorusInclusion m h₂).hom.hom.left (orthogonalTorusInclusion (m + 1)).hom.hom.left
        (spinVectorMorphism (m + 1) h₂).hom.hom.left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isPullback (spinTorus_pullback m h₂)
    exact MorphismProperty.of_isPullback h (orthogonalTorusInclusion_closed (m + 1))⟩

theorem spinTorus_split :
    Specs.GeometricRadicals.IsSplitTorus (spinTorus m h₂).group :=
  ⟨m + 1, ⟨Iso.refl _⟩⟩

private theorem spinTorus_restriction :
    Specs.CentralIsogenies.IsTorusRestriction (spinVectorMorphism (m + 1) h₂)
      (T := spinTorus m h₂) (S := orthogonalTorus (m + 1)) (spinTorusProjection m) := by
  let p := spinVectorMorphism (m + 1) h₂
  let t := spinTorusProjection (k := k) m
  let i := (orthogonalTorusInclusion (k := k) (m + 1)).hom.hom
  let j := (spinTorusInclusion m h₂).hom.hom
  have hp := spinTorus_pullback m h₂
  have hp' : IsPullback t.hom.hom.left j.left i.left p.hom.hom.left :=
    (Over.forget (Spec (CommRingCat.of k))).map_isPullback hp
  have hs := (spinVectorMorphism_flat_and_presentation (m + 1) h₂
    (specialOrthogonal_smooth (m + 1) h₂)).1
  exact ⟨Grp.hom_ext _ _ hp.w, MorphismProperty.of_isPullback hp'.flip hs,
    MorphismProperty.of_isPullback hp'.flip (spinVectorMorphism_surjective (m + 1) h₂)⟩


end

end SpinTorus

section TorusGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.MonoidalCategory

open Specs.StandardGroups (LaurentPowerCoordinates)

noncomputable section

variable {k : Type u} [Field k] (n : ℕ)

private theorem orthogonalTorusModel_geometricallyConnected :
    GeometricallyConnected (orthogonalTorusModel (k := k) n).val.X.hom := by
  let A := LaurentPowerCoordinates k (ULift.{u} (Fin n))
  change GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
  intro K _ _
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let e := pullbackSymmetry f g ≪≫ pullbackSpecIso k K A
  let E := AddMonoidAlgebra.scalarTensorEquiv k K (M := (ULift.{u} (Fin n) → ℤ))
  have : IsDomain (K ⊗[k] A) := E.toRingEquiv.toMulEquiv.isDomain _
  exact e.hom.homeomorph.connectedSpace_iff.mpr
    (inferInstanceAs (ConnectedSpace (PrimeSpectrum (K ⊗[k] A))))

end


open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient

noncomputable section

variable {k : Type u} [Field k] (m : ℕ) (h₂ : (2 : k) ≠ 0)

private theorem spinScalarSubgroup_factors_through_torus :
    ∃ e : (spinScalarSubgroup (k := k) (m + 1)).group ⟶ (spinTorus m h₂).group,
      e ≫ (spinTorus m h₂).inclusion = (spinScalarSubgroup (k := k) (m + 1)).inclusion := by
  let Z := spinScalarSubgroup (k := k) (m + 1)
  let U := spinTorus m h₂
  let T := orthogonalTorus (k := k) (m + 1)
  let p := spinVectorMorphism (m + 1) h₂
  let f := spinTorusProjection (k := k) m
  let j := Z.inclusion.hom.hom
  let a : Z.group.X ⟶ T.group.X := toUnit _ ≫ η[T.group.X]
  have h : IsPullback f.hom.hom U.inclusion.hom.hom T.inclusion.hom.hom p.hom.hom :=
    spinTorus_pullback m h₂
  have hZ := spinVectorMorphism_kernel (m + 1) h₂
  have hw : a ≫ T.inclusion.hom.hom = j ≫ p.hom.hom := by
    change (toUnit Z.group.X ≫ η[T.group.X]) ≫ T.inclusion.hom.hom = _
    rw [Category.assoc, IsMonHom.one_hom, hZ.w]
  let g : Z.group.X ⟶ U.group.X := h.lift a j hw
  have hg : g ≫ U.inclusion.hom.hom = Z.inclusion.hom.hom := h.lift_snd _ _ _
  let : IsClosedImmersion U.inclusion.hom.hom.left := U.isClosedImmersion
  let : IsMonHom g := isMonHom_of_comp_closed g Z.inclusion U.inclusion hg
  exact ⟨Grp.homMk g, Grp.hom_ext _ _ hg⟩

end

end TorusGeometry


section TorusLattices

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

open Specs.StandardGroups (multiplicativePoints)
open Specs.DiagonalizableGroups (diagonalGroup groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (powerMorphism pairing characterValue)
open Albert.SpinSpecification (SchemePoints)
open CocharacterDynamics (unitCoordinates unitPoint cocharacterPoint)
open private integerPointsIso pointsIso_spec pointsIso_precompose integerHomEquiv
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private splitGroupHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

private abbrev multiplicativeModel (k : Type u) [Field k] := diagonalGroup k IntegerCharacters.{u}

private def unitPointsIso :
    multiplicativePoints k ≅ (groupPointsFunctor k).obj (multiplicativeModel k).val :=
  (DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso).symm

private def unitEquiv (S : CommAlgCat.{u} k) : SchemePoints (multiplicativeModel k).val S ≃* Sˣ :=
  (unitPointsIso.symm.app S).groupIsoToMulEquiv

private theorem unitEquiv_unitPoint (S : CommAlgCat.{u} k) (z : Sˣ) :
    unitEquiv S (unitPoint S z) = z := by
  apply Units.ext
  have h := pointsIso_spec (k := k) IntegerCharacters S (unitCoordinates S z) integerGenerator
  change ((unitEquiv S (unitPoint S z)) : S) =
    (z : S)
  have hz : unitCoordinates S z (MonoidAlgebra.single integerGenerator 1) = (z : S) := by
    rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
    exact congrArg Units.val (zpow_one z)
  exact h.trans hz

private theorem powerMorphism_unit (a : ℤ) (S : CommAlgCat.{u} k) (z : Sˣ) :
    unitEquiv S (cocharacterPoint (powerMorphism a) S z) = z ^ a := by
  let f := (zpowersHom IntegerCharacters.{u} (integerGenerator ^ a)).comp MulEquiv.ulift.toMonoidHom
  have h := pointsIso_precompose (k := k) f S (unitPoint S z) integerGenerator
  let e := DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters
  let c : IntegerCharacters →* Sˣ := e.hom.app S (unitPoint S z)
  change unitEquiv S (cocharacterPoint (powerMorphism a) S z) = c (f integerGenerator) at h
  have hf : f integerGenerator = integerGenerator ^ a := zpow_one _
  rw [hf, map_zpow] at h
  change unitEquiv S (cocharacterPoint (powerMorphism a) S z) = (unitEquiv S (unitPoint S z)) ^ a at h
  simpa only [unitEquiv_unitPoint] using h

private theorem powerMorphism_bijective : Function.Bijective (powerMorphism (k := k)) := by
  let exp : ℤ ≃ IntegerCharacters.{u} := {
    toFun a := ⟨Multiplicative.ofAdd a⟩
    invFun m := m.down.toAdd
    left_inv _ := rfl
    right_inv _ := rfl }
  let e := exp.trans ((integerHomEquiv IntegerCharacters).toEquiv.trans
    (splitGroupHomEquiv (k := k) IntegerCharacters IntegerCharacters).toEquiv)
  have he (a : ℤ) : e a = powerMorphism (k := k) a := by
    have ha : exp a = integerGenerator ^ a := by
      apply exp.symm.injective
      change a = a • (1 : ℤ)
      simp
    change specGroupMap (groupAlgebraMap k ((zpowersHom IntegerCharacters (exp a)).comp
      MulEquiv.ulift.toMonoidHom)) = _
    rw [ha]
    rfl
  exact (funext he) ▸ e.bijective

variable (n : ℕ)

private def coordinateEvalNat (i : Fin n) : finiteTorusUnits (k := k) n ⟶ multiplicativePoints k where
  app _ := GrpCat.ofHom (Pi.evalMonoidHom _ i)
  naturality _ _ _ := by apply GrpCat.ext; intro p; rfl

private def coordinateCharacter (i : Fin n) : Character (orthogonalTorusModel (k := k) n).val :=
  (AffineAlgebraicGroup.groupHomEquiv (orthogonalTorusModel n) (multiplicativeModel k)).symm
    ((orthogonalTorusUnitsIso n).hom ≫ coordinateEvalNat n i ≫ unitPointsIso.hom)

private theorem coordinateCharacter_unit (i : Fin n) (S : CommAlgCat.{u} k)
    (p : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    unitEquiv S (p ≫ (coordinateCharacter n i).hom.hom) = torusPointsToUnits n S p i := by
  let α := (orthogonalTorusUnitsIso (k := k) n).hom ≫ coordinateEvalNat n i ≫ unitPointsIso.hom
  have h := congrArg (fun f => f.app S p)
    ((AffineAlgebraicGroup.groupHomEquiv (orthogonalTorusModel n) (multiplicativeModel k)).apply_symm_apply α)
  have h' : p ≫ (coordinateCharacter n i).hom.hom = (unitEquiv S).symm (torusPointsToUnits n S p i) := h
  exact (congrArg (unitEquiv S) h').trans ((unitEquiv S).apply_symm_apply _)

/-- The exponents of the coordinate characters on a cocharacter. -/
private def cocharacterExponents (c : Cocharacter (orthogonalTorusModel (k := k) n).val) :
    Fin n → ℤ :=
  fun i => pairing (orthogonalTorusModel (k := k) n).val (coordinateCharacter n i) c

private theorem cocharacterExponents_point
    (c : Cocharacter (orthogonalTorusModel (k := k) n).val)
    (S : CommAlgCat.{u} k) (z : Sˣ) (i : Fin n) :
    torusPointsToUnits n S (cocharacterPoint c S z) i = z ^ cocharacterExponents n c i := by
  let χ := coordinateCharacter (k := k) n i
  have hcomp : powerMorphism (cocharacterExponents n c i) = c ≫ χ :=
    Function.rightInverse_invFun powerMorphism_bijective.surjective (c ≫ χ)
  let p : SchemePoints (orthogonalTorusModel (k := k) n).val S := cocharacterPoint c S z
  refine (coordinateCharacter_unit n i S p).symm.trans ?_
  change unitEquiv S (cocharacterPoint (c ≫ χ) S z) = _
  rw [← hcomp, powerMorphism_unit]

private def cocharacterPowersNat (a : Fin n → ℤ) : multiplicativePoints k ⟶ finiteTorusUnits (k := k) n where
  app S := GrpCat.ofHom
    { toFun := fun z i => z ^ (a i)
      map_one' := funext fun i => one_zpow _
      map_mul' := fun z w => funext fun i => mul_zpow z w _ }
  naturality {S T} f := by
    apply GrpCat.ext
    intro z
    change Sˣ at z
    funext i
    change (Units.map f.hom.toMonoidHom z) ^ (a i) =
      Units.map f.hom.toMonoidHom (z ^ a i)
    exact (map_zpow _ _ _).symm

private def torusCocharacter (a : Fin n → ℤ) :
    Cocharacter (orthogonalTorusModel (k := k) n).val :=
  (AffineAlgebraicGroup.groupHomEquiv (multiplicativeModel k) (orthogonalTorusModel n)).symm
    (unitPointsIso.inv ≫ cocharacterPowersNat n a ≫ (orthogonalTorusUnitsIso n).inv)

private theorem torusCocharacter_point (a : Fin n → ℤ) (S : CommAlgCat.{u} k)
    (z : Sˣ) :
    torusPointsToUnits n S (cocharacterPoint (torusCocharacter n a) S z) = fun i => z ^ (a i) := by
  let α := unitPointsIso.inv ≫ cocharacterPowersNat (k := k) n a ≫ (orthogonalTorusUnitsIso n).inv
  have h := congrArg (fun f => f.app S (unitPoint S z))
    ((AffineAlgebraicGroup.groupHomEquiv (multiplicativeModel k) (orthogonalTorusModel n)).apply_symm_apply α)
  change cocharacterPoint (torusCocharacter n a) S z =
    (torusPointsToUnits n S).symm (fun i => (unitEquiv S (unitPoint S z)) ^ a i) at h
  rw [h, MulEquiv.apply_symm_apply, unitEquiv_unitPoint]

private theorem cocharacter_ext_of_units {G : Specs.AffineAlgebraicGroup k}
    {a b : Cocharacter G.val}
    (h : ∀ (S : CommAlgCat.{u} k) (z : Sˣ), cocharacterPoint a S z = cocharacterPoint b S z) :
    a = b := by
  apply Grp.hom_ext
  apply hom_ext_of_points (multiplicativeModel k).property.1
  intro S p
  obtain ⟨z, hz⟩ := (unitEquiv S).symm.surjective p
  change (unitEquiv S).symm z = p at hz
  have hz' : unitPoint S z = p := by
    apply (unitEquiv S).injective
    rw [unitEquiv_unitPoint, ← hz, MulEquiv.apply_symm_apply]
  exact hz' ▸ h S z

private theorem torusCocharacter_exponents (c : Cocharacter (orthogonalTorusModel (k := k) n).val) :
    torusCocharacter n (cocharacterExponents n c) = c := by
  apply cocharacter_ext_of_units
  intro S z
  apply (torusPointsToUnits n S).injective
  rw [torusCocharacter_point]
  funext i
  exact (cocharacterExponents_point n c S z i).symm

private theorem cocharacterExponents_torusCocharacter (a : Fin n → ℤ) :
    cocharacterExponents n (torusCocharacter (k := k) n a) = a := by
  funext i
  let T := (orthogonalTorusModel (k := k) n).val
  let y := torusCocharacter (k := k) n a
  let χ := coordinateCharacter (k := k) n i
  have hleft := Function.leftInverse_invFun (powerMorphism_bijective (k := k)).injective
  change Function.invFun (powerMorphism (k := k)) (y ≫ χ) = a i
  apply Eq.trans (b := Function.invFun (powerMorphism (k := k)) (powerMorphism (k := k) (a i)))
    _ (hleft (a i))
  congr 1
  apply cocharacter_ext_of_units (G := multiplicativeModel k)
  intro S z
  apply (unitEquiv S).injective
  change unitEquiv S (cocharacterPoint y S z ≫ χ.hom.hom) =
    unitEquiv S (cocharacterPoint (powerMorphism (a i)) S z)
  let p : SchemePoints (orthogonalTorusModel (k := k) n).val S := cocharacterPoint y S z
  exact (coordinateCharacter_unit n i S p).trans
    ((congrFun (torusCocharacter_point n a S z) i).trans (powerMorphism_unit (a i) S z).symm)



private instance orthogonalTorusModel_comm :
    IsCommMonObj (orthogonalTorusModel (k := k) n).val.X :=
  AlgebraicGeometry.isCommMonObj_spec_asOver_spec (R := CommRingCat.of k)
    (A := CommRingCat.of (Specs.StandardGroups.LaurentPowerCoordinates k (ULift.{u} (Fin n))))

private def cocharacterCoordinates :
    Additive (Cocharacter (orthogonalTorusModel (k := k) n).val) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (AddEquiv.toIntLinearEquiv ({
    toFun := fun a => Additive.ofMul (torusCocharacter n a)
    invFun := fun c => cocharacterExponents n c.toMul
    left_inv := cocharacterExponents_torusCocharacter n
    right_inv := fun c => congrArg Additive.ofMul (torusCocharacter_exponents n c.toMul)
    map_add' := fun a b => by
      apply congrArg Additive.ofMul
      apply cocharacter_ext_of_units
      intro S z
      apply (torusPointsToUnits n S).injective
      have h : cocharacterPoint (torusCocharacter n a * torusCocharacter n b) S z =
        cocharacterPoint (torusCocharacter n a) S z * cocharacterPoint (torusCocharacter n b) S z := by
        let f := (torusCocharacter (k := k) n a).hom.hom
        let g := (torusCocharacter (k := k) n b).hom.hom
        change (unitPoint S z) ≫ (f * g) =
          (unitPoint S z ≫ f) * (unitPoint S z ≫ g)
        exact MonObj.comp_mul (unitPoint S z) f g
      let T := (orthogonalTorusModel (k := k) n).val
      let e := torusPointsToUnits n S
      let l : SchemePoints T S := cocharacterPoint (torusCocharacter n (a + b)) S z
      let x : SchemePoints T S := cocharacterPoint (torusCocharacter n a) S z
      let y : SchemePoints T S := cocharacterPoint (torusCocharacter n b) S z
      let r : SchemePoints T S := cocharacterPoint (torusCocharacter n a * torusCocharacter n b) S z
      change e l = e r
      have hl : e l = fun i => z ^ ((a + b) i) := torusCocharacter_point n _ S z
      have hx : e x = fun i => z ^ a i := torusCocharacter_point n _ S z
      have hy : e y = fun i => z ^ b i := torusCocharacter_point n _ S z
      calc
        e l = (e x) * (e y) := by
          rw [hl, hx, hy]
          funext i
          exact zpow_add z (a i) (b i)
        _ = e (x * y) := (e.map_mul _ _).symm
        _ = e r := congrArg e h.symm

    } : (Fin n → ℤ) ≃+ Additive (Cocharacter (orthogonalTorusModel (k := k) n).val))).symm

section NormExponents

private def liftedExponents (m : ℕ) (a : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ :=
  Fin.cons (-(2 * a 0 + ∑ i : Fin m, a i.succ)) (a ∘ Fin.succ)

private theorem lift_exponents_image (m : ℕ) :
    Set.range (liftedExponents m) = evenSum (m + 1) := by
  ext v
  have hm := (corootLattice (m + 1) (Nat.succ_pos m)).2 v
  change v ∈ Set.range (liftedExponents m) ↔ v ∈ evenSum (m + 1)
  rw [← hm]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a 0, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [liftedExponents, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    omega
  · rintro ⟨c, hc⟩
    refine ⟨Fin.cons c (v ∘ Fin.succ), ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.sum_univ_succ] at hc
      simp only [liftedExponents, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
      omega
    · rfl

private theorem zpow_sum_exponents {U I : Type*} [CommGroup U] [Fintype I]
    (z : U) (a : I → ℤ) : z ^ (∑ i, a i) = ∏ i, z ^ a i :=
  congrArg Additive.toMul (map_sum (zmultiplesHom (Additive U) (Additive.ofMul z)) a Finset.univ)

private theorem liftedTorusCoordinates_exponents (m : ℕ) {S : Type u} [CommRing S]
    (z : Sˣ) (a : Fin (m + 1) → ℤ) :
    ((liftedTorusCoordinates S m).symm (fun i => z ^ a i)).val.1 =
      fun i => z ^ liftedExponents m a i := by
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  change (((z ^ (a 0)) ^ (2 : ℕ)) * ∏ i : Fin m, z ^ (a i.succ))⁻¹ =
    z ^ (-(2 * a 0 + ∑ i : Fin m, a i.succ))
  rw [← zpow_sum_exponents, zpow_neg, zpow_add]
  congr 2
  rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rfl

private theorem torusProjection_cocharacter (m : ℕ) (a : Fin (m + 1) → ℤ) :
    torusCocharacter (k := k) (m + 1) a ≫ spinTorusProjection m =
      torusCocharacter (m + 1) (liftedExponents m a) := by
  apply cocharacter_ext_of_units
  intro S z
  apply (torusPointsToUnits (m + 1) S).injective
  let p : SchemePoints (orthogonalTorusModel (k := k) (m + 1)).val S :=
    cocharacterPoint (torusCocharacter (m + 1) a) S z
  have hright := torusCocharacter_point (m + 1) (liftedExponents m a) S z
  have hleft : cocharacterPoint (torusCocharacter (k := k) (m + 1) a ≫ spinTorusProjection m) S z =
      p ≫ (spinTorusProjection m).hom.hom := by
    change unitPoint S z ≫ ((torusCocharacter (m + 1) a).hom.hom ≫
      (spinTorusProjection m).hom.hom) = _
    exact (Category.assoc ..).symm
  rw [hleft, hright]
  rw [spinTorusProjection_points, spinTorusOrthogonalPoints_eval]
  change ((liftedTorusCoordinates S m).symm (torusPointsToUnits (m + 1) S p)).val.1 = _
  rw [torusCocharacter_point]
  exact liftedTorusCoordinates_exponents m z a

private theorem spinProjection_exponents (m : ℕ) :
    Set.range (fun c : Cocharacter (orthogonalTorusModel (k := k) (m + 1)).val =>
      cocharacterExponents (m + 1) (c ≫ spinTorusProjection m)) = evenSum (m + 1) := by
  rw [← lift_exponents_image m]
  ext a
  constructor
  · rintro ⟨c, rfl⟩
    have hc := torusCocharacter_exponents (m + 1) c
    let w := cocharacterExponents (m + 1) c
    refine ⟨w, ?_⟩
    have h := congrArg (fun c => cocharacterExponents (m + 1) (c ≫ spinTorusProjection m)) hc
    change cocharacterExponents (m + 1) (torusCocharacter (m + 1) w ≫ spinTorusProjection m) =
      cocharacterExponents (m + 1) (c ≫ spinTorusProjection m) at h
    rwa [torusProjection_cocharacter, cocharacterExponents_torusCocharacter] at h
  · rintro ⟨b, rfl⟩
    exact ⟨torusCocharacter (m + 1) b,
      by
        change cocharacterExponents (m + 1) (torusCocharacter (m + 1) b ≫ spinTorusProjection m) =
          liftedExponents m b
        rw [torusProjection_cocharacter, cocharacterExponents_torusCocharacter]⟩

private theorem liftedExponents_injective (m : ℕ) : Function.Injective (liftedExponents m) := by
  intro a b hab
  have ht : ∀ i : Fin m, a i.succ = b i.succ := fun i => by
    simpa only [liftedExponents, Fin.cons_succ, Function.comp_apply] using congrFun hab i.succ
  have hs : ∑ i : Fin m, a i.succ = ∑ i : Fin m, b i.succ :=
    Finset.sum_congr rfl (fun i _ => ht i)
  have hh := congrFun hab 0
  simp only [liftedExponents, Fin.cons_zero] at hh
  rw [hs] at hh
  funext i
  refine Fin.cases ?_ ht i
  omega

private theorem spinProjection_cocharacter_injective (m : ℕ) :
    Function.Injective (fun c : Cocharacter (orthogonalTorusModel (k := k) (m + 1)).val =>
      c ≫ spinTorusProjection m) := by
  intro a b h
  have h' := congrArg (cocharacterExponents (m + 1)) h
  let x := cocharacterExponents (m + 1) a
  let y := cocharacterExponents (m + 1) b
  have hx : torusCocharacter (m + 1) x = a := torusCocharacter_exponents (m + 1) a
  have hy : torusCocharacter (m + 1) y = b := torusCocharacter_exponents (m + 1) b
  rw [← hx, ← hy] at h'
  change cocharacterExponents (m + 1) (torusCocharacter (m + 1) x ≫ spinTorusProjection m) =
    cocharacterExponents (m + 1) (torusCocharacter (m + 1) y ≫ spinTorusProjection m) at h'
  rw [torusProjection_cocharacter, torusProjection_cocharacter,
    cocharacterExponents_torusCocharacter, cocharacterExponents_torusCocharacter] at h'
  exact hx.symm.trans ((congrArg (torusCocharacter (m + 1)) (liftedExponents_injective m h')).trans hy)

end NormExponents

private def characterOnPoints (χ : Character (orthogonalTorusModel (k := k) n).val)
    (S : CommAlgCat.{u} k) : SchemePoints (orthogonalTorusModel (k := k) n).val S →* Sˣ where
  toFun t := unitEquiv S (t ≫ χ.hom.hom)
  map_one' := by simp only [MonObj.one_comp, map_one]
  map_mul' t w := by simp only [MonObj.mul_comp, map_mul]

private def pointOnCharacters (S : CommAlgCat.{u} k)
    (t : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    Character (orthogonalTorusModel (k := k) n).val →* Sˣ where
  toFun χ := characterOnPoints n χ S t
  map_one' := by change unitEquiv S (t ≫ 1) = 1; rw [MonObj.comp_one, map_one]
  map_mul' χ ψ := by
    change unitEquiv S (t ≫ (χ.hom.hom * ψ.hom.hom)) =
      unitEquiv S (t ≫ χ.hom.hom) * unitEquiv S (t ≫ ψ.hom.hom)
    rw [MonObj.comp_mul, map_mul]

private theorem characterOnPoints_val (χ : Character (orthogonalTorusModel (k := k) n).val)
    (S : CommAlgCat.{u} k) (t : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    (characterOnPoints n χ S t : S) = characterValue χ S t := by
  let A := Specs.DiagonalizableGroups.groupAlgebra k IntegerCharacters
  let x := t ≫ χ.hom.hom
  let φ := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x
  let f : MonoidAlgebra k IntegerCharacters →ₐ[k] S := φ.unop.hom
  have hφ : (hopfSpecPointIso A).hom.app S (WithConv.toConv f) = x :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage x
  change (unitEquiv S x : S) = f (MonoidAlgebra.single integerGenerator 1)
  rw [← hφ]
  exact pointsIso_spec (k := k) IntegerCharacters S f integerGenerator

private theorem pairCharacter_at_unit (χ : Character (orthogonalTorusModel (k := k) n).val)
    (c : Cocharacter (orthogonalTorusModel (k := k) n).val) (S : CommAlgCat.{u} k) (z : Sˣ) :
    characterOnPoints n χ S (cocharacterPoint c S z) =
      z ^ pairing (orthogonalTorusModel (k := k) n).val χ c := by
  let a := pairing (orthogonalTorusModel (k := k) n).val χ c
  let h : powerMorphism a = c ≫ χ :=
    Function.rightInverse_invFun powerMorphism_bijective.surjective (c ≫ χ)
  change unitEquiv S (cocharacterPoint (c ≫ χ) S z) = z ^ a
  rw [← h, powerMorphism_unit]

private theorem pairing_eq_of_unit (χ : Character (orthogonalTorusModel (k := k) n).val)
    (c : Cocharacter (orthogonalTorusModel (k := k) n).val) (a : ℤ)
    (h : ∀ (S : CommAlgCat.{u} k) (z : Sˣ), characterOnPoints n χ S (cocharacterPoint c S z) = z ^ a) :
    pairing (orthogonalTorusModel (k := k) n).val χ c = a := by
  have he : c ≫ χ = powerMorphism a := by
    apply cocharacter_ext_of_units (G := multiplicativeModel k)
    intro S z
    apply (unitEquiv S).injective
    exact (h S z).trans (powerMorphism_unit a S z).symm
  change Function.invFun (powerMorphism (k := k)) (c ≫ χ) = a
  rw [he]
  exact Function.leftInverse_invFun (powerMorphism_bijective (k := k)).injective a

private def characterExponents (χ : Character (orthogonalTorusModel (k := k) n).val) : Fin n → ℤ :=
  fun i => pairing (orthogonalTorusModel (k := k) n).val χ (torusCocharacter n (coordinate n i))

private theorem product_coordinateCocharacters (S : CommAlgCat.{u} k)
    (t : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    (List.ofFn (fun i : Fin n => cocharacterPoint (torusCocharacter n (coordinate n i)) S
      (torusPointsToUnits n S t i))).prod = t := by
  let e := torusPointsToUnits n S
  apply e.injective
  rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
  funext j
  change (∏ i, e (cocharacterPoint (torusCocharacter n (coordinate n i)) S (e t i))) j = e t j
  rw [Finset.prod_apply]
  simp_rw [show ∀ i : Fin n, e (cocharacterPoint (torusCocharacter n (coordinate n i)) S
    (e t i)) j = (e t i) ^ (coordinate n i j) from
    fun i => congrFun (torusCocharacter_point n (coordinate n i) S (e t i)) j]
  rw [Finset.prod_eq_single j]
  · simp [coordinate]
  · intro i _ hij
    simp [coordinate, Pi.single_eq_of_ne (Ne.symm hij)]
  · simp

private theorem characterOnPoints_exponents (χ : Character (orthogonalTorusModel (k := k) n).val)
    (S : CommAlgCat.{u} k) (t : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    characterOnPoints n χ S t = ∏ i, (torusPointsToUnits n S t i) ^ (characterExponents n χ i) := by
  conv_lhs => rw [← product_coordinateCocharacters n S t]
  rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  exact pairCharacter_at_unit n χ (torusCocharacter n (coordinate n i)) S (torusPointsToUnits n S t i)

private theorem character_ext_of_units {χ ψ : Character (orthogonalTorusModel (k := k) n).val}
    (h : ∀ S t, characterOnPoints n χ S t = characterOnPoints n ψ S t) : χ = ψ := by
  apply Grp.hom_ext
  apply hom_ext_of_points (orthogonalTorusModel (k := k) n).property.1
  intro S t
  exact (unitEquiv S).injective (h S t)

private def torusCharacter (a : Fin n → ℤ) : Character (orthogonalTorusModel (k := k) n).val :=
  ∏ i, coordinateCharacter n i ^ (a i)

private theorem torusCharacter_onPoints (a : Fin n → ℤ) (S : CommAlgCat.{u} k)
    (t : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    characterOnPoints n (torusCharacter n a) S t = ∏ i, (torusPointsToUnits n S t i) ^ (a i) := by
  change pointOnCharacters n S t (∏ i, coordinateCharacter n i ^ (a i)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_zpow]
  exact congrArg (fun x : Sˣ => x ^ a i) (coordinateCharacter_unit n i S t)

private theorem torusCharacter_characterExponents (χ : Character (orthogonalTorusModel (k := k) n).val) :
    torusCharacter n (characterExponents n χ) = χ := by
  apply character_ext_of_units
  intro S t
  rw [torusCharacter_onPoints, characterOnPoints_exponents]

private theorem characterExponents_torusCharacter (a : Fin n → ℤ) :
    characterExponents n (torusCharacter (k := k) n a) = a := by
  funext j
  change pairing (orthogonalTorusModel (k := k) n).val (torusCharacter n a)
    (torusCocharacter n (coordinate n j)) = a j
  apply pairing_eq_of_unit
  intro S z
  rw [torusCharacter_onPoints]
  simp_rw [torusCocharacter_point]
  rw [Finset.prod_eq_single j]
  · simp [coordinate]
  · intro i _ hij
    simp [coordinate, Pi.single_eq_of_ne hij]
  · simp

private def characterCoordinates :
    Additive (Character (orthogonalTorusModel (k := k) n).val) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (AddEquiv.toIntLinearEquiv ({
    toFun := fun a => Additive.ofMul (torusCharacter n a)
    invFun := fun χ => characterExponents n χ.toMul
    left_inv := characterExponents_torusCharacter n
    right_inv := fun χ => congrArg Additive.ofMul (torusCharacter_characterExponents n χ.toMul)
    map_add' := fun a b => by
      apply congrArg Additive.ofMul
      apply character_ext_of_units
      intro S t
      change (pointOnCharacters n S t) (torusCharacter n (a + b)) =
        (pointOnCharacters n S t) (torusCharacter n a * torusCharacter n b)
      rw [map_mul]
      change characterOnPoints n (torusCharacter n (a + b)) S t =
        characterOnPoints n (torusCharacter n a) S t * characterOnPoints n (torusCharacter n b) S t
      simp [torusCharacter_onPoints, zpow_add, Finset.prod_mul_distrib]
    } : (Fin n → ℤ) ≃+ Additive (Character (orthogonalTorusModel (k := k) n).val))).symm

private theorem characterCoordinates_evaluation (χ : Character (orthogonalTorusModel (k := k) n).val)
    (S : CommAlgCat.{u} k) (t : SchemePoints (orthogonalTorusModel (k := k) n).val S) :
    characterValue χ S t = ((∏ i, (torusPointsToUnits n S t i) ^
      (characterCoordinates n (Additive.ofMul χ) i) : Sˣ) : S) := by
  rw [← characterOnPoints_val]
  exact congrArg Units.val (characterOnPoints_exponents n χ S t)

private theorem pairing_coordinates (χ : Character (orthogonalTorusModel (k := k) n).val)
    (c : Cocharacter (orthogonalTorusModel (k := k) n).val) :
    pairing (orthogonalTorusModel (k := k) n).val χ c =
      ∑ i, characterCoordinates n (Additive.ofMul χ) i * cocharacterCoordinates n (Additive.ofMul c) i := by
  change pairing (orthogonalTorusModel (k := k) n).val χ c =
    ∑ i, characterExponents n χ i * cocharacterExponents n c i
  apply pairing_eq_of_unit
  intro S z
  rw [characterOnPoints_exponents]
  simp_rw [cocharacterExponents_point, ← zpow_mul, mul_comm (cocharacterExponents n c _)]
  exact (zpow_sum_exponents z _).symm

end

open private spinUnitPoints spinUnitPoints_represents from LinearAlgebraicGroups.Albert.SpinFunctor

theorem splitSpinTorus : SplitSpinTorus.{u} := by
  intro k _ n h₂ hn
  rcases n with _ | m
  · exact (Nat.not_lt_zero _ hn).elim
  let n := m + 1
  let G := spinAlgebraicGroup (k := k) n
  let O := specialOrthogonalGroup (k := k) n
  let T := orthogonalTorus (k := k) n
  let U := spinTorus m h₂
  let p := spinVectorMorphism n h₂
  let r := spinTorusProjection (k := k) m
  refine ⟨G, O, p, spinUnitPoints (form n k) (matrixBasis n), orthogonalPoints n h₂,
    spinUnitPoints_represents _ _, orthogonalPoints_natural n h₂,
    spinVectorMorphism_action n h₂, T, U, r, orthogonalTorus_split n, spinTorus_split m h₂,
    orthogonalTorusModel_geometricallyConnected n, orthogonalTorusModel_geometricallyConnected n,
    spinTorus_restriction m h₂, spinTorus_pullback m h₂,
    ⟨spinScalarSubgroup n, spinVectorMorphism_kernel n h₂, rfl,
      spinScalarSubgroup_factors_through_torus m h₂⟩, torusPointsToUnits n, spinTorusParameters m,
    (fun S a => orthogonalTorus_points n S h₂ a), ?_, ?_, ?_⟩
  · intro S a
    exact (congrArg (torusPointsToUnits n S) (spinTorusProjection_points m S a)).trans
      (spinTorusOrthogonalPoints_eval m S a)
  · intro S a
    have he := (congrArg (spinUnitPoints (form n k) (matrixBasis n) S)
      (spinTorusInclusion_points m h₂ S a)).trans (spinTorusToSpinPoints_unit m h₂ S a)
    exact (congrArg Units.val he).trans (liftedDiagonalUnit_val n S (spinTorusParameters m S a))
  · exact ⟨orthogonalTorusModel_comm n, characterCoordinates n, cocharacterCoordinates n,
      pairing_coordinates n, (fun S a χ => characterCoordinates_evaluation n χ S a),
      (fun S z c i => cocharacterExponents_point n c S z i),
      spinProjection_cocharacter_injective m, spinProjection_exponents m⟩

end TorusLattices

section OrthogonalConnectedness

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonObj
open Albert.SpinSpecification (ExtendedForm SchemePoints)

noncomputable section

section ConnectedFamilies

variable {k : Type u} [Field k] {G : Specs.GroupScheme k}

private structure ConnectingFamily {L : Type u} [Field L] [Algebra k L]
    (p : SchemePoints G (CommAlgCat.of k L)) where
  S : CommAlgCat.{u} k
  isDomain : IsDomain S
  constants : CommAlgCat.of k L ⟶ S
  first : S ⟶ CommAlgCat.of k L
  last : S ⟶ CommAlgCat.of k L
  first_constants : constants ≫ first = 𝟙 _
  last_constants : constants ≫ last = 𝟙 _
  point : SchemePoints G S
  first_point : (algSpec (CommRingCat.of k)).map first.op ≫ point = 1
  last_point : (algSpec (CommRingCat.of k)).map last.op ≫ point = p

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem geometricallyConnected_of_families
    (h : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra k L]
      (p : SchemePoints G (CommAlgCat.of k L)), Nonempty (ConnectingFamily p)) :
    GeometricallyConnected G.X.hom := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
  intro K _ _
  let f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback G.X.hom f
  let e : SchemePoints G (CommAlgCat.of k K) := 1
  let eY : Spec (CommRingCat.of K) ⟶ Y := pullback.lift e.left (𝟙 _) (by rw [Category.id_comp]; exact e.w)
  let zK : Spec (CommRingCat.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨eY zK, Set.eq_univ_of_forall ?_⟩
  intro y
  let L := AlgebraicClosure (Y.residueField y)
  let q : Spec (CommRingCat.of L) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) L)) ≫ Y.fromSpecResidueField y
  obtain ⟨r, hr⟩ := Spec.map_surjective (q ≫ pullback.snd G.X.hom f)
  let : Algebra K L := r.hom.toAlgebra
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let rA : CommAlgCat.of k K ⟶ CommAlgCat.of k L :=
    CommAlgCat.ofHom (IsScalarTower.toAlgHom k K L)
  change ((algSpec (CommRingCat.of k)).map rA.op).left = _ at hr
  have hqr : (q ≫ pullback.fst G.X.hom f) ≫ G.X.hom =
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k L))).hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr]
    exact ((algSpec (CommRingCat.of k)).map rA.op).w
  let p : SchemePoints G (CommAlgCat.of k L) := Over.homMk (q ≫ pullback.fst G.X.hom f) hqr
  obtain ⟨C⟩ := h L p
  let sp := algSpec (CommRingCat.of k)
  let cK := C.point
  let dK := (sp.map ((rA ≫ C.constants).op)).left
  let m : Spec (CommRingCat.of C.S) ⟶ Y :=
    pullback.lift cK.left dK (cK.w.trans (Over.w (sp.map ((rA ≫ C.constants).op))).symm)
  let e0 : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of C.S) := (sp.map C.first.op).left
  let e1 : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of C.S) := (sp.map C.last.op).left
  let rSpec : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) := (sp.map rA.op).left
  have h0 : e0 ≫ m = rSpec ≫ eY := by
    apply pullback.hom_ext
    · have he : (sp.map C.first.op) ≫ C.point = (sp.map rA.op) ≫ e := by
        rw [C.first_point]
        exact (MonObj.comp_one _).symm
      simp only [Category.assoc, m, eY, pullback.lift_fst]
      exact congrArg Over.Hom.left he
    · simp only [Category.assoc, m, eY, pullback.lift_snd, Category.comp_id]
      change ((sp.map C.first.op) ≫ sp.map (rA ≫ C.constants).op).left = _
      rw [← Functor.map_comp, ← op_comp, Category.assoc, C.first_constants, Category.comp_id]
  have h1 : e1 ≫ m = q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, m, pullback.lift_fst]
      exact congrArg Over.Hom.left C.last_point
    · simp only [Category.assoc, m, pullback.lift_snd]
      rw [← hr]
      change ((sp.map C.last.op) ≫ sp.map (rA ≫ C.constants).op).left = _
      rw [← Functor.map_comp, ← op_comp, Category.assoc, C.last_constants, Category.comp_id]
  let zL : Spec (CommRingCat.of L) := ⟨⊥, Ideal.isPrime_bot⟩
  have h0' : m (e0 zL) = eY zK := by
    have he := congrArg (fun v : Spec (CommRingCat.of L) ⟶ Y => v zL) h0
    refine he.trans ?_
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have h1' : m (e1 zL) = y := by
    have he := congrArg (fun v : Spec (CommRingCat.of L) ⟶ Y => v zL) h1
    refine he.trans ?_
    change Y.fromSpecResidueField y (Spec.map
      (CommRingCat.ofHom (algebraMap (Y.residueField y) L)) zL) = y
    exact Scheme.fromSpecResidueField_apply y _
  let : IsDomain C.S := C.isDomain
  have hp : _root_.IsPreconnected (Set.range m) := isPreconnected_range m.continuous
  exact hp.subset_connectedComponent ⟨_, h0'⟩ ⟨_, h1'⟩

end ConnectedFamilies
section ReflectionsOverAlgebras

variable {R V : Type u} [CommRing R] [AddCommGroup V] [Module R V]
variable (Q : QuadraticForm R V) (w : V) (a : Rˣ)

private def unitReflectionFunctional : Module.Dual R V := (↑a⁻¹ : R) • Q.polarBilin w

private theorem unitReflectionFunctional_self (ha : Q w = (a : R)) :
    unitReflectionFunctional Q w a w = 2 := by
  simp only [unitReflectionFunctional, LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_self, two_smul, smul_eq_mul, ha, ← two_mul]
  rw [mul_left_comm (↑a⁻¹ : R) 2 (a : R), Units.inv_mul, mul_one]

private def unitReflection (ha : Q w = (a : R)) : V ≃ₗ[R] V :=
  Module.reflection (unitReflectionFunctional_self Q w a ha)

private theorem unitReflection_apply (ha : Q w = (a : R)) (x : V) :
    unitReflection Q w a ha x = x - ((↑a⁻¹ : R) * Q.polarBilin w x) • w := by
  rw [unitReflection, Module.reflection_apply]
  rfl

private theorem unitReflection_preserves (ha : Q w = (a : R)) (x : V) :
    Q (unitReflection Q w a ha x) = Q x := by
  let p := Q.polarBilin w x
  let t : R := (↑a⁻¹ : R) * p
  have ht : t * (a : R) = p := by
    change (↑a⁻¹ : R) * p * ↑a = p
    rw [mul_comm (↑a⁻¹ : R) p, mul_assoc, Units.inv_mul, mul_one]
  rw [unitReflection_apply, sub_eq_add_neg, QuadraticMap.map_add Q, Q.map_neg, Q.map_smul]
  change Q x + (t * t) • Q w + QuadraticMap.polar Q x (-(t • w)) = Q x
  rw [← QuadraticMap.polarBilin_apply_apply, map_neg, map_smul,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
    ← QuadraticMap.polarBilin_apply_apply, smul_eq_mul, smul_eq_mul, ha, mul_assoc, ht]
  exact add_neg_cancel_right _ _

private theorem det_preReflection_basis {I : Type v} [Fintype I] (b : Basis I R V)
    (f : Module.Dual R V) : LinearMap.det (Module.preReflection w f) = 1 - f w := by
  classical
  rw [← LinearMap.det_toMatrix b, Module.preReflection, map_sub, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit, Matrix.det_one_sub_mul_comm,
    Matrix.det_unique]
  change 1 - (Matrix.replicateRow Unit (f ∘ b) * Matrix.replicateCol Unit (b.repr w)) () () =
    1 - f w
  rw [Matrix.replicateRow_mul_replicateCol_apply]
  congr 1
  conv_rhs => rw [← b.sum_repr w, map_sum]
  simp [dotProduct, mul_comm]

private theorem unitReflection_det {I : Type v} [Fintype I] (b : Basis I R V)
    (ha : Q w = (a : R)) :
    (LinearEquiv.det (unitReflection Q w a ha) : R) = -1 := by
  rw [LinearEquiv.coe_det]
  change LinearMap.det (Module.preReflection w (unitReflectionFunctional Q w a)) = -1
  rw [det_preReflection_basis w b, unitReflectionFunctional_self Q w a ha]
  ring

end ReflectionsOverAlgebras

section ReflectionWords

open Albert.SpinSpecification (ExtendedForm SchemePoints)
open private changeModule changeModule_smul polar_baseChange_tmul from
  LinearAlgebraicGroups.Albert.SpinFunctor

variable {k : Type u} [Field k] (n : ℕ)
variable {S T : CommAlgCat.{u} k}

private abbrev reflectionForm (S : CommAlgCat.{u} k) := ExtendedForm (form n k) S (basis n k)
private abbrev RefVector (S : CommAlgCat.{u} k) :=
  {x : S ⊗[k] Space n k // IsUnit (reflectionForm n S x)}

private theorem extendedPolar_changeModule (f : S ⟶ T) (x y : S ⊗[k] Space n k) :
    f.hom ((reflectionForm n S).polarBilin x y) =
      (reflectionForm n T).polarBilin (changeModule f.hom x) (changeModule f.hom y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t w =>
      have hs : s ⊗ₜ[k] v = s • ((1 : S) ⊗ₜ[k] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have ht : t ⊗ₜ[k] w = t • ((1 : S) ⊗ₜ[k] w) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, ht]
      simp only [changeModule_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
      have hp (x : Space n k) : changeModule f.hom (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x := by simp [changeModule]
      rw [hp, hp, polar_baseChange_tmul, polar_baseChange_tmul, f.hom.commutes]

private theorem extendedForm_changeModule (h₂ : (2 : k) ≠ 0)
    (f : S ⟶ T) (x : S ⊗[k] Space n k) :
    f.hom (reflectionForm n S x) = reflectionForm n T (changeModule f.hom x) := by
  have h := extendedPolar_changeModule n f x x
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul, map_add] at h
  have hu : IsUnit (2 : T) := by
    rw [← map_ofNat (algebraMap k T) 2]
    exact (isUnit_iff_ne_zero.mpr h₂).map (algebraMap k T)
  exact hu.mul_left_cancel (by simpa only [two_mul] using h)

private def refVectorMap (h₂ : (2 : k) ≠ 0) (f : S ⟶ T) (w : RefVector n S) :
    RefVector n T :=
  ⟨changeModule f.hom w.val,
    extendedForm_changeModule n h₂ f w.val ▸ w.property.map f.hom⟩

private def reflectVector (w : RefVector n S) :
    (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k) :=
  unitReflection (reflectionForm n S) w.val w.property.unit w.property.unit_spec.symm

private theorem reflectVector_natural (h₂ : (2 : k) ≠ 0) (f : S ⟶ T)
    (w : RefVector n S) (x : S ⊗[k] Space n k) :
    changeModule f.hom (reflectVector n w x) =
      reflectVector n (refVectorMap n h₂ f w) (changeModule f.hom x) := by
  unfold reflectVector
  rw [unitReflection_apply, unitReflection_apply]
  simp only [map_sub, changeModule_smul, map_mul, extendedPolar_changeModule]
  have he : Units.map f.hom.toMonoidHom w.property.unit = (refVectorMap n h₂ f w).property.unit := by
    apply Units.ext
    change f.hom (↑w.property.unit) = ↑(refVectorMap n h₂ f w).property.unit
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    exact extendedForm_changeModule n h₂ f w.val
  have hi : f.hom (↑w.property.unit⁻¹) = ↑(refVectorMap n h₂ f w).property.unit⁻¹ := by
    exact congrArg (fun a : Tˣ => ((a⁻¹ : Tˣ) : T)) he
  rw [hi]
  rfl

private def reflectProduct (l : List (RefVector n S)) :
    (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k) :=
  (l.map (reflectVector n)).prod

private theorem reflectProduct_preserves (l : List (RefVector n S)) (x : S ⊗[k] Space n k) :
    reflectionForm n S (reflectProduct n l x) = reflectionForm n S x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change reflectionForm n S (reflectVector n w (reflectProduct n l x)) = _
    exact (unitReflection_preserves _ _ _ _ _).trans ih

private theorem reflectProduct_det (l : List (RefVector n S)) :
    (LinearEquiv.det (reflectProduct n l) : S) = (-1 : S) ^ l.length := by
  induction l with
  | nil => simp [reflectProduct]
  | cons w l ih =>
    change (LinearEquiv.det (reflectVector n w * reflectProduct n l) : S) = _
    rw [map_mul, Units.val_mul, ih, List.length_cons, pow_succ, mul_comm]
    rw [reflectVector, unitReflection_det _ _ _ ((basis n k).baseChange S)]

private theorem reflectProduct_natural (h₂ : (2 : k) ≠ 0) (f : S ⟶ T)
    (l : List (RefVector n S)) (x : S ⊗[k] Space n k) :
    changeModule f.hom (reflectProduct n l x) =
      reflectProduct n (l.map (refVectorMap n h₂ f)) (changeModule f.hom x) := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change changeModule f.hom (reflectVector n w (reflectProduct n l x)) =
      reflectVector n (refVectorMap n h₂ f w)
        (reflectProduct n (l.map (refVectorMap n h₂ f)) (changeModule f.hom x))
    rw [reflectVector_natural, ih]

private def reflectionReference (S : CommAlgCat.{u} k) : RefVector n S := by
  let x : Space n k := (0, 1)
  have hx : form n k x = 1 := by simp [x, formCoordinates]
  refine ⟨1 ⊗ₜ[k] x, ?_⟩
  change IsUnit (ExtendedForm (form n k) S (basis n k) (1 ⊗ₜ[k] x))
  rw [ExtendedForm, Albert.CliffordModel.coefficientForm_tmul, hx]
  simp

private theorem reflectProduct_replicate (w : RefVector n S) (m : ℕ) (h : Even m) :
    reflectProduct n (List.replicate m w) = 1 := by
  rw [reflectProduct, List.map_replicate, List.prod_replicate]
  have hi : (reflectVector n w)⁻¹ = reflectVector n w :=
    Module.reflection_inv (unitReflectionFunctional_self _ _ _ w.property.unit_spec.symm)
  have hu : reflectVector n w * reflectVector n w = 1 :=
    (congrArg (reflectVector n w * ·) hi.symm).trans (mul_inv_cancel _)
  obtain ⟨a, ha⟩ := h
  rw [ha, ← two_mul, pow_mul, pow_two, hu, one_pow]

end ReflectionWords

section OrthogonalPaths

open Albert.SpinSpecification (ExtendedForm SchemePoints)
open private changeModule changeModule_basis changeModule_smul from
  LinearAlgebraicGroups.Albert.SpinFunctor

variable {k : Type u} [Field k] (n : ℕ) (h₂ : (2 : k) ≠ 0)
variable {S T W : CommAlgCat.{u} k}

private theorem changeModule_comp (a : S ⟶ T) (b : T ⟶ W) (x : S ⊗[k] Space n k) :
    changeModule b.hom (changeModule a.hom x) = changeModule (a ≫ b).hom x := by
  induction x using TensorProduct.inductionOn with
  | tmul s v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem changeModule_identity (x : S ⊗[k] Space n k) :
    changeModule (AlgHom.id k S) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private def interpolateVector (a : S ⟶ T) (s : T) (w : RefVector n S) : T ⊗[k] Space n k :=
  (1 - s) • (reflectionReference n T).val + s • changeModule a.hom w.val

private theorem interpolateVector_natural (a : S ⟶ T) (f : T ⟶ W) (s : T)
    (w : RefVector n S) :
    changeModule f.hom (interpolateVector n a s w) =
      interpolateVector n (a ≫ f) (f.hom s) w := by
  have hr : changeModule f.hom (reflectionReference n T).val = (reflectionReference n W).val := by
    change changeModule f.hom (1 ⊗ₜ[k] ((0, 1) : Space n k)) = 1 ⊗ₜ[k] ((0, 1) : Space n k)
    simp [changeModule]
  simp only [interpolateVector, map_add, changeModule_smul, map_sub, map_one, hr, changeModule_comp]

private theorem interpolateVector_zero (a : S ⟶ T) (w : RefVector n S) :
    interpolateVector n a 0 w = (reflectionReference n T).val := by
  simp [interpolateVector]

private theorem interpolateVector_one (w : RefVector n S) :
    interpolateVector n (𝟙 S) 1 w = w.val := by
  simp [interpolateVector, changeModule_identity]

private def pointOfEvenWord (S : CommAlgCat.{u} k) (l : List (RefVector n S)) (he : Even l.length) :
    SchemePoints (specialOrthogonalGroup (k := k) n).val S := by
  refine (orthogonalPoints n h₂ S).symm ⟨reflectProduct n l, reflectProduct_preserves n l, ?_⟩
  apply Units.ext
  change (LinearEquiv.det (reflectProduct n l) : S) = 1
  rw [reflectProduct_det, he.neg_pow, one_pow]

private theorem pointOfEvenWord_congr (S : CommAlgCat.{u} k) {l l' : List (RefVector n S)}
    (h : l = l') (he : Even l.length) (he' : Even l'.length) :
    pointOfEvenWord n h₂ S l he = pointOfEvenWord n h₂ S l' he' := by
  subst l'
  rfl

private theorem pointOfEvenWord_natural (f : S ⟶ T) (l : List (RefVector n S)) (he : Even l.length) :
    (algSpec (CommRingCat.of k)).map f.op ≫ pointOfEvenWord n h₂ S l he =
      pointOfEvenWord n h₂ T (l.map (refVectorMap n h₂ f)) (by simpa using he) := by
  let o := orthogonalPoints n h₂
  apply (o T).injective
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply ((matrixBasis (k := k) n).baseChange T).ext
  intro i
  let p := pointOfEvenWord n h₂ S l he
  have hp : (o S p).val = reflectProduct n l := by
    change Subtype.val ((o S) ((o S).symm _)) = _
    rw [MulEquiv.apply_symm_apply]
  have hn := orthogonalPoints_natural n h₂ f p ((matrixBasis (k := k) n).baseChange S i)
  change changeModule f.hom ((o S p).val _) =
    (o T ((algSpec (CommRingCat.of k)).map f.op ≫ p)).val (changeModule f.hom _) at hn
  rw [hp, reflectProduct_natural n h₂, changeModule_basis] at hn
  change (o T ((algSpec (CommRingCat.of k)).map f.op ≫ p)).val
    ((matrixBasis (k := k) n).baseChange T i) = _
  rw [← hn]
  change _ = (Subtype.val ((o T) ((o T).symm _))) _
  rw [MulEquiv.apply_symm_apply]

private theorem reflectProduct_apply_field (L : Type u) [Field L] [Algebra k L]
    (l : List (RefVector n (CommAlgCat.of k L))) (x : L ⊗[k] Space n k) :
    let Q := reflectionForm n (CommAlgCat.of k L)
    reflectProduct n l x =
      (l.map Subtype.val).foldr (fun w z => z - (Q.polarBilin w z / Q w) • w) x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change reflectVector n w (reflectProduct n l x) = _
    have hw : (↑w.property.unit⁻¹ : L) = (reflectionForm n (CommAlgCat.of k L) w.val)⁻¹ := by
      rw [Units.val_inv_eq_inv_val, IsUnit.unit_spec]
    rw [reflectVector, unitReflection_apply, hw]
    change _ = _ - (_ / _) • w.val
    rw [ih, div_eq_mul_inv, mul_comm ((reflectionForm n (CommAlgCat.of k L) w.val)⁻¹)]

set_option maxHeartbeats 1800000 in
private theorem orthogonal_evenWord (L : Type u) [Field L] [IsAlgClosed L] [Algebra k L]
    (p : SchemePoints (specialOrthogonalGroup (k := k) n).val (CommAlgCat.of k L)) :
    ∃ (l : List (RefVector n (CommAlgCat.of k L))) (he : Even l.length),
      pointOfEvenWord n h₂ (CommAlgCat.of k L) l he = p := by
  let R := CommAlgCat.of k L
  let Q := reflectionForm n R
  let g := orthogonalPoints n h₂ R p
  obtain ⟨l, hl, haction⟩ := SpinOrthogonalWords.orthogonalWords Q
    (Or.inl (LinearMap.ker_eq_bot.mpr (extendedPerfectPolar n L h₂).1)) g.val g.property.1
  have hu (w : L ⊗[k] Space n k) (hw : w ∈ l) : IsUnit (Q w : L) :=
    IsUnit.mk0 (Q w : L) (hl w hw)
  let l' : List (RefVector n R) := l.attachWith (fun w => IsUnit (Q w : L)) hu
  have hmap : l'.map Subtype.val = l := List.unattach_attachWith
  have hlin : reflectProduct n l' = g.val := by
    apply LinearEquiv.ext
    intro x
    change reflectProduct n l' x = g.val x
    rw [reflectProduct_apply_field, hmap]
    exact (haction x).symm
  have hsign : (-1 : L) ^ l'.length = 1 := by
    refine (reflectProduct_det (S := R) n l').symm.trans ?_
    have hg : LinearEquiv.det g.val = 1 := g.property.2
    rw [hlin, hg]
    rfl
  have he : Even l'.length := by
    have h₂L : (2 : L) ≠ 0 := by
      rw [← map_ofNat (algebraMap k L) 2]
      simpa only [map_zero] using (algebraMap k L).injective.ne h₂
    by_contra h
    have ho := Nat.not_even_iff_odd.mp h
    rw [ho.neg_pow, one_pow, neg_eq_iff_add_eq_zero, ← two_mul, mul_one] at hsign
    exact h₂L hsign
  refine ⟨l', he, ?_⟩
  apply (orthogonalPoints n h₂ R).injective
  apply Subtype.ext
  change Subtype.val ((orthogonalPoints n h₂ R) ((orthogonalPoints n h₂ R).symm _)) = g.val
  rw [MulEquiv.apply_symm_apply]
  exact hlin

private def localizedTestAlgebra (B : CommAlgCat.{u} k) (P : B) : CommAlgCat.{u} k :=
  CommAlgCat.of k (Localization.Away P)

private def localizeCoefficients (B : CommAlgCat.{u} k) (P : B) :
    B ⟶ localizedTestAlgebra B P :=
  CommAlgCat.ofHom {
    __ := algebraMap B (Localization.Away P)
    commutes' _ := rfl }

private def localizedEvaluation {B L : CommAlgCat.{u} k} (P : B) (e : B ⟶ L)
    (h : IsUnit (e.hom P)) : localizedTestAlgebra B P ⟶ L :=
  CommAlgCat.ofHom {
    __ := IsLocalization.Away.lift (S := Localization.Away P) P (g := e.hom.toRingHom) h
    commutes' x := by
      change IsLocalization.Away.lift (S := Localization.Away P) P (g := e.hom.toRingHom) h
        (algebraMap B (Localization.Away P) (algebraMap k B x)) = _
      rw [IsLocalization.Away.lift_eq]
      exact e.hom.commutes x }

private theorem localizeCoefficients_evaluation {B L : CommAlgCat.{u} k}
    (P : B) (e : B ⟶ L) (h : IsUnit (e.hom P)) :
    localizeCoefficients B P ≫ localizedEvaluation P e h = e := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact IsLocalization.Away.lift_eq (S := Localization.Away P) P (g := e.hom.toRingHom) h x

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
include h₂ in
private theorem orthogonal_connectingFamily (L : Type u) [Field L] [IsAlgClosed L] [Algebra k L]
    (p : SchemePoints (specialOrthogonalGroup (k := k) n).val (CommAlgCat.of k L)) :
    Nonempty (ConnectingFamily p) := by
  let R := CommAlgCat.of k L
  let B := CommAlgCat.of k (Polynomial L)
  let C : R ⟶ B := CommAlgCat.ofHom Polynomial.CAlgHom
  let X : B := Polynomial.X
  obtain ⟨l, he, hp⟩ := orthogonal_evenWord n h₂ L p
  let norm := fun w : RefVector n R => reflectionForm n B (interpolateVector n C X w)
  let P : B := (l.map norm).prod
  let eval : L → (B ⟶ R) := fun s => CommAlgCat.ofHom ((Polynomial.aeval s).restrictScalars k)
  have hEC (s : L) : C ≫ eval s = 𝟙 _ := by
    ext x
    change (Polynomial.aeval s) (Polynomial.C x) = x
    rw [Polynomial.aeval_C]
    rfl
  have hEX (s : L) : (eval s).hom X = s := Polynomial.aeval_X _
  have evNorm (s : L) (w : RefVector n R) :
      (eval s).hom (norm w) = reflectionForm n R (interpolateVector n (𝟙 R) s w) := by
    simp only [norm, extendedForm_changeModule n h₂, interpolateVector_natural, hEC, hEX]
  have P0 : (Polynomial.aeval (0 : L)) P = 1 := by
    change (eval 0).hom (l.map norm).prod = 1
    rw [map_list_prod, List.map_map]
    have hq : reflectionForm n R (reflectionReference n R).val = 1 := by
      change ExtendedForm (form n k) L (basis n k) (1 ⊗ₜ[k] (0, 1)) = 1
      rw [ExtendedForm, Albert.CliffordModel.coefficientForm_tmul, formCoordinates]
      simp
    have hc : ((eval 0).hom : B → R) ∘ norm = fun _ => 1 := by
      funext w
      rw [Function.comp_apply, evNorm, interpolateVector_zero, hq]
    rw [hc, List.map_const', List.prod_replicate, one_pow]
  have P1 : (Polynomial.aeval (1 : L)) P ≠ 0 := by
    change (eval 1).hom (l.map norm).prod ≠ 0
    rw [map_list_prod, List.map_map]
    apply List.prod_ne_zero
    intro h
    obtain ⟨w, _, hw⟩ := List.mem_map.mp h
    change (eval 1).hom (norm w) = 0 at hw
    rw [evNorm, interpolateVector_one] at hw
    exact w.property.ne_zero hw
  have P_ne_zero : P ≠ 0 := by
    intro h
    rw [h, map_zero] at P0
    exact zero_ne_one P0
  let A := localizedTestAlgebra B P
  let i : B ⟶ A := localizeCoefficients B P
  let e (s : L) (hs : (Polynomial.aeval s) P ≠ 0) : A ⟶ R :=
    localizedEvaluation P (eval s) (show IsUnit ((Polynomial.aeval s) P) from IsUnit.mk0 _ hs)
  have heval (s : L) (hs : (Polynomial.aeval s) P ≠ 0) : i ≫ e s hs = eval s :=
    localizeCoefficients_evaluation P (eval s) _
  have hP0 : (Polynomial.aeval (0 : L)) P ≠ 0 := P0.trans_ne one_ne_zero
  let ev0 := e 0 hP0
  let ev1 := e 1 P1
  have hnorm (w : RefVector n R) (hw : w ∈ l) :
      IsUnit (reflectionForm n A (changeModule i.hom (interpolateVector n C X w))) := by
    rw [← extendedForm_changeModule n h₂]
    change IsUnit (algebraMap B (Localization.Away P) (norm w))
    exact IsLocalization.Away.isUnit_of_dvd (S := Localization.Away P) P (List.dvd_prod (List.mem_map_of_mem hw))
  let pointVector (w : {w : RefVector n R // w ∈ l}) : RefVector n A :=
    ⟨changeModule i.hom (interpolateVector n C X w.val), hnorm w.val w.property⟩
  let lA : List (RefVector n A) := l.attach.map pointVector
  have lenA : lA.length = l.length := by simp [lA]
  have hi0 : i ≫ ev0 = eval 0 := heval 0 hP0
  have hi1 : i ≫ ev1 = eval 1 := heval 1 P1
  have h0 : lA.map (refVectorMap n h₂ ev0) = List.replicate l.length (reflectionReference n R) := by
    simp only [lA, List.map_map]
    have hmap : refVectorMap n h₂ ev0 ∘ pointVector = fun _ => reflectionReference n R := by
      funext w
      apply Subtype.ext
      change changeModule ev0.hom (changeModule i.hom (interpolateVector n C X w.val)) = _
      rw [changeModule_comp, hi0, interpolateVector_natural, hEC, hEX, interpolateVector_zero]
    rw [hmap, List.map_const']
    simp
  have h1 : lA.map (refVectorMap n h₂ ev1) = l := by
    simp only [lA, List.map_map]
    have hmap : refVectorMap n h₂ ev1 ∘ pointVector = Subtype.val := by
      funext w
      apply Subtype.ext
      change changeModule ev1.hom (changeModule i.hom (interpolateVector n C X w.val)) = _
      rw [changeModule_comp, hi1, interpolateVector_natural, hEC, hEX, interpolateVector_one]
    rw [hmap]
    exact List.unattach_attach
  have hlen (f : A ⟶ R) : Even (lA.map (refVectorMap n h₂ f)).length := by
    simpa only [List.length_map, lenA] using he
  refine ⟨⟨A, Localization.Away.isDomain P_ne_zero, C ≫ i, ev0, ev1,
    ?_, ?_, pointOfEvenWord n h₂ A lA (lenA.symm ▸ he), ?_, ?_⟩⟩
  · rw [Category.assoc, hi0, hEC]
  · rw [Category.assoc, hi1, hEC]
  · have hrep : Even (List.replicate l.length (reflectionReference n R)).length := by
      simpa only [List.length_replicate] using he
    rw [pointOfEvenWord_natural, pointOfEvenWord_congr n h₂ R h0 (hlen ev0) hrep]
    apply (orthogonalPoints n h₂ R).injective
    rw [map_one]
    apply Subtype.ext
    change Subtype.val ((orthogonalPoints n h₂ R) ((orthogonalPoints n h₂ R).symm _)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact reflectProduct_replicate n _ _ he
  · rw [pointOfEvenWord_natural, pointOfEvenWord_congr n h₂ R h1 (hlen ev1) he]
    exact hp

include h₂ in
/-- The determinant-one split odd orthogonal group is geometrically connected. -/
theorem specialOrthogonal_geometricallyConnected :
    GeometricallyConnected (specialOrthogonalGroup (k := k) n).val.X.hom :=
  geometricallyConnected_of_families (orthogonal_connectingFamily n h₂)

end OrthogonalPaths

end

end OrthogonalConnectedness

section SpinConnectedness

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme IsSchemeKernel ClosedSubgroup)
noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem geometricallyConnected_of_finiteEtaleCover {G O : AffineAlgebraicGroup k}
    (p : G.val ⟶ O.val) [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]
    (hO : GeometricallyConnected O.val.X.hom)
    (Z U : ClosedSubgroup G.val) (hZ : IsSchemeKernel p Z)
    (hU : GeometricallyConnected U.group.X.hom)
    (j : Z.group ⟶ U.group) (hj : j ≫ U.inclusion = Z.inclusion) :
    GeometricallyConnected G.val.X.hom := by
  obtain ⟨Q, H, q, i, hi, _⟩ := identityComponentAndQuotient k G
  let a := i.hom.hom
  let b := p.hom.hom
  let u := U.inclusion.hom.hom
  let z := Z.inclusion.hom.hom
  have : IsOpenImmersion a.left := hi.openImmersion
  have : IsClosedImmersion a.left := hi.closedImmersion
  have : ConnectedSpace O.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton O.val.X.hom
  have : ConnectedSpace U.group.X.left := GeometricallyConnected.connectedSpace_of_subsingleton U.group.X.hom
  let e := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
  have hp : η[G.val.X].left e ∈ Set.range u.left := by
    refine ⟨η[U.group.X].left e, ?_⟩
    have h := congrArg (fun f : (𝟙_ (SchemeOver k)) ⟶ G.val.X => f.left)
      (IsMonHom.one_hom u)
    exact congrArg (fun f : Spec (CommRingCat.of k) ⟶ G.val.X.left => f e) h
  have hn : (Set.range (a ≫ b).left).Nonempty :=
    ⟨_, ⟨η[H.X].left e, rfl⟩⟩
  have hsurj : Surjective (a ≫ b).left := by
    change Surjective (a.left ≫ b.left)
    have hC : IsClopen (Set.range (a.left ≫ b.left)) :=
      ⟨(a.left ≫ b.left).isClosedMap.isClosed_range, (a.left ≫ b.left).isOpenMap.isOpen_range⟩
    exact ⟨Set.range_eq_univ.mp (hC.eq_univ hn)⟩
  have hUrange : Set.range u.left ⊆ Set.range a.left := by
    change Set.range u.left ⊆ Set.range i.hom.hom.left
    rw [hi.identityComponent]
    exact (isPreconnected_range u.left.continuous).subset_connectedComponent hp
  have hZrange : Set.range z.left ⊆ Set.range a.left := by
    have hj' : j.hom.hom.left ≫ u.left = z.left :=
      congrArg (fun f : Z.group ⟶ G.val => f.hom.hom.left) hj
    rw [← hj']
    change Set.range (u.left ∘ j.hom.hom.left) ⊆ Set.range a.left
    exact (Set.range_comp_subset_range _ _).trans hUrange
  let zH₀ := IsOpenImmersion.lift a.left z.left hZrange
  have hzH₀ : zH₀ ≫ a.left = z.left := IsOpenImmersion.lift_fac a.left z.left hZrange
  let zH : Z.group.X ⟶ H.X :=
    Over.homMk zH₀ (by rw [← a.w, ← Category.assoc, hzH₀]; exact z.w)
  have hzH : zH ≫ a = z := Over.OverMorphism.ext hzH₀
  let P := pullback (a ≫ b) b
  let x : P ⟶ H.X := pullback.fst _ _
  let y : P ⟶ G.val.X := pullback.snd _ _
  have hxy : (x ≫ a) ≫ b = y ≫ b := by rw [Category.assoc]; exact pullback.condition
  have hpull : IsPullback x.left y.left (a ≫ b).left b.left :=
    (IsPullback.of_hasPullback (a ≫ b) b).map (Over.forget _)
  have hy : Surjective y.left :=
    MorphismProperty.of_isPullback hpull hsurj
  have hz : ((x ≫ a)⁻¹ * y) ≫ b = (toUnit P) ≫ η[O.val.X] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, inv_mul_cancel]
    rfl
  let t := hZ.lift ((x ≫ a)⁻¹ * y) (toUnit P) hz
  have ht : t ≫ z = (x ≫ a)⁻¹ * y := hZ.lift_fst _ _ _
  let m := x * (t ≫ zH)
  have hm : m ≫ a = y := by
    rw [MonObj.mul_comp, Category.assoc, hzH, ht, mul_inv_cancel_left]
  have ha : Surjective a.left := by
    refine ⟨?_⟩
    intro w
    obtain ⟨v, hv⟩ := hy.1 w
    refine ⟨m.left v, ?_⟩
    exact (congrArg (fun f : P ⟶ G.val.X => f.left v) hm).trans hv
  have haIso : IsIso a.left :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top a.left
      (TopologicalSpace.Opens.ext_iff.mpr (Set.range_eq_univ.mpr ha.1))
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected a.left G.val.X.hom).mp
    (by rw [a.w]; exact hi.geometricallyConnected)

variable (m : ℕ) (h₂ : (2 : k) ≠ 0)

include h₂ in
private theorem spin_geometricallyConnected_of_orthogonal
    (hO : GeometricallyConnected (specialOrthogonalGroup (k := k) (m + 1)).val.X.hom) :
    GeometricallyConnected (spinAlgebraicGroup (k := k) (m + 1)).val.X.hom := by
  obtain ⟨hf, he⟩ := spinVectorMorphism_finiteEtale (m + 1) h₂ (specialOrthogonal_smooth (m + 1) h₂)
  obtain ⟨j, hj⟩ := spinScalarSubgroup_factors_through_torus m h₂
  exact geometricallyConnected_of_finiteEtaleCover (spinVectorMorphism (m + 1) h₂) hO
    (spinScalarSubgroup (m + 1)) (spinTorus m h₂) (spinVectorMorphism_kernel (m + 1) h₂)
    (orthogonalTorusModel_geometricallyConnected (m + 1)) j hj

theorem spin_geometricallyConnected (n : ℕ) (h₂ : (2 : k) ≠ 0) (hn : 0 < n) :
    GeometricallyConnected (spinAlgebraicGroup (k := k) n).val.X.hom := by
  rcases n with _ | m
  · exact (Nat.not_lt_zero _ hn).elim
  · exact spin_geometricallyConnected_of_orthogonal m h₂
      (specialOrthogonal_geometricallyConnected (m + 1) h₂)

open private spinUnitPoints spinUnitPoints_represents from LinearAlgebraicGroups.Albert.SpinFunctor

theorem splitOddConnectedness : SplitOddConnectedness.{u} := by
  intro k _ n h₂ hn
  exact ⟨spinAlgebraicGroup n, specialOrthogonalGroup n, spinVectorMorphism n h₂,
    spinUnitPoints (form n k) (matrixBasis n), orthogonalPoints n h₂,
    spinUnitPoints_represents _ _, orthogonalPoints_natural n h₂, spinVectorMorphism_action n h₂,
    spin_geometricallyConnected n h₂ hn, specialOrthogonal_geometricallyConnected n h₂⟩

end

end SpinConnectedness

section SpinCentre

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (GroupScheme IsSchemeKernel ClosedSubgroup)
noncomputable section

variable {k : Type u} [Field k]

private theorem whiskerRight_projection_pullback {A B X : SchemeOver k} (f : A ⟶ B) :
    IsPullback (f ▷ X) (fst A X) (fst B X) f := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ (fun c => lift c.snd (c.fst ≫ snd B X)) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simp [c.condition]
    · simp
  · intro c
    simp
  · intro c h h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h₂
    · simpa using congrArg (fun t => t ≫ snd B X) h₁

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem centre_of_cover {G O : GroupScheme k} (p : G ⟶ O)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    {Z : ClosedSubgroup G} (hZ : IsSchemeKernel p Z) (hZcentral : Centralizes (𝟙 G) Z.inclusion.hom.hom)
    (hO : ∀ (S : SchemeOver k) (a : S ⟶ O.X), Centralizes (𝟙 O) a → a = 1) :
    RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 G) z) := by
  intro S g
  let a := p.hom.hom
  constructor
  · intro hc
    have hP : IsPullback (a ▷ S).left (fst G.X S).left (fst O.X S).left a.left :=
      (whiskerRight_projection_pullback (X := S) a).map (Over.forget _)
    have hf : Flat (a ▷ S).left := MorphismProperty.of_isPullback hP.flip
      (inferInstanceAs (Flat p.hom.hom.left))
    have hs : Surjective (a ▷ S).left := MorphismProperty.of_isPullback hP.flip
      (inferInstanceAs (Surjective p.hom.hom.left))
    have : Epi (a ▷ S).left := Flat.epi_of_flat_of_surjective _
    have : Epi (a ▷ S) := Over.epi_of_epi_left _
    have hcO : Centralizes (𝟙 O) (g ≫ a) := by
      apply (cancel_epi (a ▷ S)).mp
      have h := congrArg (· ≫ a) hc
      change ((snd G.X S ≫ g) * fst G.X S * (snd G.X S ≫ g)⁻¹) ≫ a =
        fst G.X S ≫ a at h
      change (a ▷ S) ≫ ((snd O.X S ≫ g ≫ a) * fst O.X S * (snd O.X S ≫ g ≫ a)⁻¹) =
        (a ▷ S) ≫ fst O.X S
      simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc] at h
      simpa only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, whiskerRight_snd_assoc,
        whiskerRight_fst] using h
    have h := hO S (g ≫ a) hcO
    exact ⟨hZ.lift g (toUnit S) h, hZ.lift_fst _ _ _⟩
  · rintro ⟨z, rfl⟩
    have h := congrArg ((𝟙 G.X ⊗ₘ z) ≫ ·) hZcentral
    change (𝟙 G.X ⊗ₘ z) ≫
      ((snd G.X Z.group.X ≫ Z.inclusion.hom.hom) * fst G.X Z.group.X *
        (snd G.X Z.group.X ≫ Z.inclusion.hom.hom)⁻¹) =
      (𝟙 G.X ⊗ₘ z) ≫ fst G.X Z.group.X at h
    change (snd G.X S ≫ z ≫ Z.inclusion.hom.hom) * fst G.X S *
      (snd G.X S ≫ z ≫ Z.inclusion.hom.hom)⁻¹ = fst G.X S
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, tensorHom_fst, tensorHom_snd_assoc,
      Category.comp_id, Category.assoc] using h

theorem spinScalarSubgroup_represents_centre (n : ℕ) (h₂ : (2 : k) ≠ 0)
    (hO : ∀ (S : SchemeOver k) (a : S ⟶ (specialOrthogonalGroup (k := k) n).val.X),
      Centralizes (𝟙 (specialOrthogonalGroup (k := k) n).val) a → a = 1) :
    RepresentsSubgroup (spinScalarSubgroup (k := k) n)
      (fun _ z => Centralizes (𝟙 (spinAlgebraicGroup (k := k) n).val) z) := by
  have := (spinVectorMorphism_flat_and_presentation n h₂ (specialOrthogonal_smooth n h₂)).1
  have := spinVectorMorphism_surjective n h₂
  exact centre_of_cover (spinVectorMorphism n h₂) (spinVectorMorphism_kernel n h₂)
    (spinScalarSubgroup_central n) hO

end

end SpinCentre

section OrthogonalComparison

open AlgebraicGeometry CategoryTheory Matrix
open scoped CategoryTheory.MonObj

open Specs.AbstractPairing (Datum Root)

noncomputable section

variable {k : Type u} [Field k] (n : ℕ)

local instance : IsCommMonObj (orthogonalTorus (k := k) n).group.X :=
  orthogonalTorusModel_comm n

private theorem gram_eq_geometry (S : CommAlgCat.{u} k) :
    gramOver (k := k) n S = Specs.OddSpinOrthogonalGeometry.gram n S := by
  ext ⟨i⟩ ⟨j⟩
  rw [gram_entry]
  rcases i with ((i | i) | ⟨⟩)
  · rw [oddBasis_e_polar]
    by_cases h : j = .inl (.inr i) <;>
      simp [Specs.OddSpinOrthogonalGeometry.gram, Specs.OddSpinOrthogonalGeometry.partner, Specs.OddSpinOrthogonalGeometry.f, Specs.OddSpinOrthogonalGeometry.r, h]
  · rw [oddBasis_f_polar]
    by_cases h : j = .inl (.inl i) <;>
      simp [Specs.OddSpinOrthogonalGeometry.gram, Specs.OddSpinOrthogonalGeometry.partner, Specs.OddSpinOrthogonalGeometry.e, Specs.OddSpinOrthogonalGeometry.r, h]
  · rename_i r
    cases r
    rcases j with (j | r)
    · rw [oddBasis_line, oddBasis_hyperbolic, polarCoordinates]
      simp [Specs.OddSpinOrthogonalGeometry.gram, Specs.OddSpinOrthogonalGeometry.partner, Specs.OddSpinOrthogonalGeometry.r]
    · cases r
      rw [oddBasis_line, polarCoordinates]
      simp [Specs.OddSpinOrthogonalGeometry.gram, Specs.OddSpinOrthogonalGeometry.partner, Specs.OddSpinOrthogonalGeometry.r, map_ofNat]

private theorem gram_eq_root_coordinates (S : CommAlgCat.{u} k) :
    Specs.OddSpinOrthogonalGeometry.gram n S = Specs.Arithmetic.OddSpinOrthogonalRootDatum.gram n S := by
  ext ⟨i⟩ ⟨j⟩
  rcases i with ((i | i) | ⟨⟩) <;>
    simp [Specs.OddSpinOrthogonalGeometry.gram, Specs.OddSpinOrthogonalGeometry.partner, Specs.OddSpinOrthogonalGeometry.e, Specs.OddSpinOrthogonalGeometry.f, Specs.OddSpinOrthogonalGeometry.r,
      Specs.Arithmetic.OddSpinOrthogonalRootDatum.gram, Specs.Arithmetic.OddSpinOrthogonalRootDatum.partner, Specs.Arithmetic.OddSpinOrthogonalRootDatum.gramCoefficient,
      eq_comm]

private theorem orthogonalMatrices_eq_geometry (S : CommAlgCat.{u} k) :
    orthogonalMatrices (k := k) n S = Specs.OddSpinOrthogonalGeometry.orthogonalMatrices n S := by
  ext a
  change (a.valᵀ * gramOver (k := k) n S * a.val = _) ↔ (a.valᵀ * Specs.OddSpinOrthogonalGeometry.gram n S * a.val = _)
  rw [gram_eq_geometry]

private def geometryMatrixFunctorIso :
    orthogonalMatrixFunctor (k := k) n ≅ Specs.OddSpinOrthogonalGeometry.orthogonalPoints k n :=
  NatIso.ofComponents (fun S => (MulEquiv.subgroupCongr (orthogonalMatrices_eq_geometry n S)).toGrpIso)
    (by
      intro S T f
      apply GrpCat.ext
      intro a
      apply Subtype.ext
      apply Subtype.ext
      rfl)

private def orthogonalGeometryModel :
    Specs.OddSpinOrthogonalGeometry.MarkedModel n (specialOrthogonalGroup (k := k) n) (orthogonalTorus n) where
  orthogonal := orthogonalMatrixPoints n ≪≫ geometryMatrixFunctorIso n
  torus := orthogonalTorusUnitsIso n
  inclusion_matrix S a := by
    change (((orthogonalMatrixPoints n).hom.app S
      (a ≫ (orthogonalTorusInclusion n).hom.hom)).val.val : Matrix _ _ S) =
      diagonal (Specs.OddSpinOrthogonalGeometry.diagonalEntry (torusPointsToUnits n S a))
    refine (congrArg (fun M : orthogonalMatrices (k := k) n S => M.val.val)
      (orthogonalTorusInclusion_matrix n S a)).trans ?_
    funext ⟨i⟩
    rcases i with ((_ | _) | _) <;> rfl

private theorem orthogonalMatrices_eq_root_coordinates (S : CommAlgCat.{u} k) :
    Specs.OddSpinOrthogonalGeometry.orthogonalMatrices n S = Specs.Arithmetic.OddSpinOrthogonalRootDatum.orthogonalMatrices n S := by
  ext a
  change (a.valᵀ * Specs.OddSpinOrthogonalGeometry.gram n S * a.val = _) ↔
    (a.valᵀ * Specs.Arithmetic.OddSpinOrthogonalRootDatum.gram n S * a.val = _)
  rw [gram_eq_root_coordinates]

private def orthogonalRootPointCoordinates :
    Specs.Arithmetic.OddSpinOrthogonalRootDatum.PointCoordinates (orthogonalTorus (k := k) n) n where
  orthogonal S := ((orthogonalGeometryModel n).orthogonal.app S).groupIsoToMulEquiv.trans
    (MulEquiv.subgroupCongr (orthogonalMatrices_eq_root_coordinates n S))
  torus := torusPointsToUnits n
  orthogonal_natural f a := by
    let e := (orthogonalGeometryModel (k := k) n).orthogonal
    exact congrArg (fun M : Specs.OddSpinOrthogonalGeometry.orthogonalMatrices n _ => M.val.val)
      (ConcreteCategory.congr_hom (e.hom.naturality f) a)
  torus_natural f a i := congrFun (torusPointsToUnits_natural n f a) i
  inclusion S a := by
    refine ((orthogonalGeometryModel n).inclusion_matrix S a).trans ?_
    congr 1
    funext ⟨i⟩
    rcases i with ((_ | _) | _) <;> rfl

private def orthogonalRootLatticeCoordinates :
    Specs.Arithmetic.OddSpinOrthogonalRootDatum.LatticeCoordinates (orthogonalRootPointCoordinates (k := k) n) where
  characters := characterCoordinates n
  cocharacters := cocharacterCoordinates n
  pairing_eq := pairing_coordinates n
  character_eval S a χ := characterCoordinates_evaluation n χ S a
  cocharacter_eval := fun S z c i => cocharacterExponents_point n c S z i

private theorem orthogonalTypeBDatum (h₂ : (2 : k) ≠ 0) (hn : 0 < n)
    (hO : Specs.GeometricRadicals.IsReductive (specialOrthogonalGroup (k := k) n))
    (hT : Specs.RankOneFlag.IsGeometricallyMaximal (orthogonalTorus (k := k) n)) :
    ∃ D : Datum (orthogonalTorus (k := k) n), IsTypeBDatum n (orthogonalTorus n) D
      (characterCoordinates n) (cocharacterCoordinates n) := by
  obtain ⟨hr, D, hc⟩ := OddSpinOrthogonalRootDatum.orthogonalRootDatum
    k n h₂ hn (specialOrthogonalGroup n) (orthogonalTorus n) hO
    (orthogonalTorus_split n) hT (orthogonalRootPointCoordinates n)
    (orthogonalRootLatticeCoordinates n)
  refine ⟨D, pairing_coordinates n, hr, ?_⟩
  have he (α : Root (orthogonalTorus (k := k) n)) :
      characterCoordinates n (D.rootDatum.root α) = characterCoordinates n (Additive.ofMul α.val) :=
    congrArg (characterCoordinates n) (D.root_eq α)
  rw [Set.image_univ]
  change (Set.range (fun r : Root (orthogonalTorus (k := k) n) =>
    (characterCoordinates n (D.rootDatum.root r), cocharacterCoordinates n (D.rootDatum.coroot r)))) =
      corootPairs n at hc
  have hpair :
      (fun r : Root (orthogonalTorus (k := k) n) =>
        (characterCoordinates n (D.rootDatum.root r), cocharacterCoordinates n (D.rootDatum.coroot r))) =
      (fun r : Root (orthogonalTorus (k := k) n) =>
        (characterCoordinates n (Additive.ofMul r.val), cocharacterCoordinates n (D.rootDatum.coroot r))) :=
    funext fun r => Prod.ext (he r) rfl
  exact (congrArg (fun f : Root (orthogonalTorus (k := k) n) →
    (Fin n → ℤ) × (Fin n → ℤ) => Set.range f) hpair).symm.trans hc

end

end OrthogonalComparison

section FiniteCoverGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj IsMulCommutative

open _root_.LinearAlgebraicGroups.Specs
  (AffineAlgebraicGroup ClosedSubgroup GroupScheme IsNormalSubgroup subgroupConjugation)
open Specs.GeometricRadicals
  (GeometricGroup IsSemisimple IsSplitTorus geometricSolvableRadical baseChangedSubgroup)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSolvable)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private baseChangeMapPullback tensorHom_property from LinearAlgebraicGroups.Affine.Components
open private rationalSections rationalMap solvable_iff_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private affine_tensor from LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private descendClosedFactor splitTorus_baseChange from LinearAlgebraicGroups.Classification.CentralIsogenies
open private affine_quotient_smooth_connected from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private exists_section_lift from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private finite_zero_isTrivial from LinearAlgebraicGroups.Classification.IntegralCentralQuotient
open private existsImageFactorization from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private centralizes_iff mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private maximal_of_self_centralizing from LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalGeometry

noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
private theorem normal_of_surjective_image {G H I : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    {N : ClosedSubgroup G.val} (hN : IsNormalSubgroup N.inclusion)
    (q : N.group ⟶ I.val) (i : I.val ⟶ H.val)
    (h : Specs.IsImageFactorization (N.inclusion ≫ f) q i) :
    IsNormalSubgroup i := by
  let a := f.hom.hom ⊗ₘ q.hom.hom
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine N.group.X.left := (closedSubgroupAlgebraicGroup N).property.1
  let : IsAffine H.val.X.left := H.property.1
  let : IsAffine I.val.X.left := I.property.1
  let : IsAffine (G.val.X ⊗ N.group.X).left := affine_tensor
  let : IsAffine (H.val.X ⊗ I.val.X).left := affine_tensor
  let : Flat a.left := tensorHom_property f.hom.hom q.hom.hom @Flat inferInstance h.2.1
  let : Surjective a.left := tensorHom_property f.hom.hom q.hom.hom @Surjective inferInstance h.2.2.1
  let : Mono i.hom.hom := mono_over _ h.2.2.2.2.2
  obtain ⟨c, hc⟩ := hN
  apply descendClosedFactor a i.hom.hom (subgroupConjugation i) (c ≫ q.hom.hom)
  have hi : q.hom.hom ≫ i.hom.hom = N.inclusion.hom.hom ≫ f.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map h.1
  rw [Category.assoc, hi, ← Category.assoc, hc]
  simp only [a, subgroupConjugation, MonObj.mul_comp, MonObj.comp_mul, GrpObj.inv_comp,
    GrpObj.comp_inv, Category.assoc, tensorHom_fst, tensorHom_snd_assoc, hi]

set_option backward.isDefEq.respectTransparency false in
private theorem semisimple_of_finite_cover {G H : AffineAlgebraicGroup k} (f : G.val ⟶ H.val)
    (hf : IsCentralIsogeny f) (hsG : Smooth G.val.X.hom) (hcG : GeometricallyConnected G.val.X.hom)
    (hH : IsSemisimple H) : IsSemisimple G := by
  refine ⟨hsG, hcG, ?_⟩
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let P := GeometricGroup G
  let Q := GeometricGroup H
  let fK : P.val ⟶ Q.val := F.map f
  have hbase := (baseChangeMapPullback (K := K) f.hom.hom).flip
  let : IsFinite fK.hom.hom.left := MorphismProperty.of_isPullback hbase hf.1
  let : Flat fK.hom.hom.left := MorphismProperty.of_isPullback hbase hf.2.1
  let : Surjective fK.hom.hom.left := MorphismProperty.of_isPullback hbase hf.2.2.1
  let N := geometricSolvableRadical G
  let A := closedSubgroupAlgebraicGroup N
  have hN := GeometricRadicals.geometricSolvableRadicalLargest G
  obtain ⟨I, q, i, hI⟩ := existsImageFactorization A Q (N.inclusion ≫ fK)
  obtain ⟨hsI, hcI⟩ := affine_quotient_smooth_connected q hI.2.1 hI.2.2.1 hN.1.1 hN.1.2.1
  have hsolv : IsSolvable I.val := by
    apply (solvable_iff_sections I hsI hcI).mpr
    let : Group.IsSolvable (rationalSections A.val) :=
      (solvable_iff_sections A hN.1.1 hN.1.2.1).mp hN.2.1
    apply Group.isSolvable_of_surjective (f := rationalMap q)
    let : LocallyOfFiniteType A.val.X.hom := A.property.2.1
    let : LocallyOfFiniteType I.val.X.hom := I.property.2.1
    intro x
    exact exists_section_lift q.hom.hom x (hI.2.2.1.1 _)
  let J : ClosedSubgroup Q.val := ⟨I.val, i, hI.2.2.2.2.2⟩
  have hnorm : IsNormalSubgroup J.inclusion := normal_of_surjective_image fK hN.1.2.2 q i hI
  obtain ⟨j, hj⟩ := (GeometricRadicals.geometricSolvableRadicalLargest H).2.2 J
    ⟨hsI, hcI, hnorm⟩ hsolv
  obtain ⟨e⟩ := hH.2.2
  have hj0 : j = 0 := ((Grp.isZero_trivial (SchemeOver K)).of_iso e).eq_zero_of_tgt j
  have hi₀ : i = 0 := by
    change j ≫ (geometricSolvableRadical H).inclusion = i at hj
    rw [← hj, hj0, zero_comp]
  have hf₀ : N.inclusion ≫ fK = 0 := by rw [← hI.1, hi₀, comp_zero]
  let := N.isClosedImmersion
  exact finite_zero_isTrivial (G := A) (Q := Q) (N.inclusion ≫ fK)
    (inferInstanceAs (IsFinite (N.inclusion.hom.hom.left ≫ fK.hom.hom.left)))
    hf₀ hN.1.1 hN.1.2.1

set_option backward.isDefEq.respectTransparency false in
private theorem centralizes_after_torus_projection {G H : GroupScheme k}
    {U : ClosedSubgroup G} {T : ClosedSubgroup H}
    (f : G ⟶ H) (q : U.group ⟶ T.group) (hq : IsTorusRestriction f q)
    {S : SchemeOver k} (g : S ⟶ G.X) (hg : Centralizes U.inclusion g) :
    Centralizes T.inclusion (g ≫ f.hom.hom) := by
  let a := q.hom.hom ▷ S
  have hP : IsPullback a.left (fst U.group.X S).left (fst T.group.X S).left q.hom.hom.left :=
    (whiskerRight_projection_pullback (X := S) q.hom.hom).map (Over.forget _)
  let : Flat a.left := MorphismProperty.of_isPullback hP.flip hq.2.1
  let : Surjective a.left := MorphismProperty.of_isPullback hP.flip hq.2.2
  let : Epi a.left := Flat.epi_of_flat_of_surjective _
  let : Epi a := Over.epi_of_epi_left _
  apply (cancel_epi a).mp
  have hp : U.inclusion.hom.hom ≫ f.hom.hom = q.hom.hom ≫ T.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hq.1.symm
  have hc := congrArg (· ≫ f.hom.hom) hg
  change ((snd U.group.X S ≫ g) * (fst U.group.X S ≫ U.inclusion.hom.hom) *
      (snd U.group.X S ≫ g)⁻¹) ≫ f.hom.hom = (fst U.group.X S ≫ U.inclusion.hom.hom) ≫
        f.hom.hom at hc
  change a ≫ ((snd T.group.X S ≫ g ≫ f.hom.hom) * (fst T.group.X S ≫ T.inclusion.hom.hom) *
    (snd T.group.X S ≫ g ≫ f.hom.hom)⁻¹) = a ≫ fst T.group.X S ≫ T.inclusion.hom.hom
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hp] at hc
  simpa only [a, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, whiskerRight_snd_assoc,
    whiskerRight_fst_assoc] using hc

set_option backward.isDefEq.respectTransparency false in
private theorem geometricallyMaximal_of_full_torus_preimage {G H : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {T : ClosedSubgroup H.val} (hU : IsSplitTorus U.group)
    (f : G.val ⟶ H.val) (q : U.group ⟶ T.group) (hq : IsTorusRestriction f q)
    (hP : IsPullback q.hom.hom U.inclusion.hom.hom T.inclusion.hom.hom f.hom.hom)
    (hT : ∃ h : IsClosedImmersion
      ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
      RepresentsSubgroup (baseChangedSubgroup (AlgebraicClosure k) T h)
        (fun _ g => Centralizes ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion) g)) :
    IsGeometricallyMaximal U := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  obtain ⟨hiT, hC⟩ := hT
  have hiU : IsClosedImmersion (F.map U.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) U.inclusion.hom.hom).flip
      U.isClosedImmersion
  let U' := baseChangedSubgroup K U hiU
  let T' := baseChangedSubgroup K T hiT
  let q' : U'.group ⟶ T'.group := F.map q
  let f' : (GeometricGroup G).val ⟶ (GeometricGroup H).val := F.map f
  have hP' : IsPullback q'.hom.hom U'.inclusion.hom.hom T'.inclusion.hom.hom f'.hom.hom :=
    hP.map (baseChange k K)
  have hq' : IsTorusRestriction f' q' := by
    have hbase := (baseChangeMapPullback (K := K) q.hom.hom).flip
    exact ⟨Grp.hom_ext _ _ hP'.w, MorphismProperty.of_isPullback hbase hq.2.1,
      MorphismProperty.of_isPullback hbase hq.2.2⟩
  have hsU' : IsSplitTorus U'.group := splitTorus_baseChange K hU
  refine ⟨hiU, ?_⟩
  change Specs.GeometricRadicals.IsMaximalTorus U'
  apply maximal_of_self_centralizing (G := GeometricGroup G) (T := U') hsU'
  intro S g
  constructor
  · intro hc
    have hc' := centralizes_after_torus_projection f' q' hq' g hc
    obtain ⟨b, hb⟩ := (hC S _).mp hc'
    exact ⟨hP'.lift b g hb, hP'.lift_snd _ _ _⟩
  · rintro ⟨a, rfl⟩
    have hcomm : IsCommMonObj U'.group.X :=
      torus_commutative (closedSubgroupAlgebraicGroup (G := GeometricGroup G) U')
      (isTorus_of_split hsU')
    apply (centralizes_iff _ _).mpr
    intro W s t
    let : IsMulCommutative (W ⟶ U'.group.X) :=
      (isCommMonObj_iff_isMulCommutative U'.group.X).mp hcomm W
    have h :=
      (show Commute (s ≫ a) t from mul_comm _ _).map (IsMonHom.monoidHom U'.inclusion.hom.hom W)
    change Commute ((s ≫ a) ≫ U'.inclusion.hom.hom) (t ≫ U'.inclusion.hom.hom) at h
    simpa only [Category.assoc] using h

end

end FiniteCoverGeometry

section SpinLattice

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.AbstractPairing (Datum Root)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CentralIsogenies (characterPullback IsCentralIsogeny IsTorusRestriction)
open Specs.SimplyConnectedLattice (corootLatticeOf)

open private pushCocharacters from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
private theorem map_corootLattice_of_isogeny {G O : AffineAlgebraicGroup k}
    (hG : IsReductive G) (hO : IsReductive O)
    {U : ClosedSubgroup G.val} {T : ClosedSubgroup O.val}
    [IsCommMonObj U.group.X] [IsCommMonObj T.group.X]
    (hUs : IsSplitTorus U.group) (hUm : IsGeometricallyMaximal U)
    (hTs : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (p : G.val ⟶ O.val) (hp : IsCentralIsogeny p)
    (q : U.group ⟶ T.group) (hq : IsTorusRestriction p q)
    (E : Datum U) (D : Datum T) :
    (corootLatticeOf E).map (pushCocharacters q) = corootLatticeOf D := by
  obtain ⟨_, _, hroots, hcoroots⟩ :=
    Classification.CentralIsogenies.centralIsogenyComparison G O hG hO U T
      hUs hUm hTs hTm p q hp hq.1 hq.2.2
  let liftRoot : Root T → Root U := fun β => ⟨characterPullback q β.val, hroots.mapsTo β.property⟩
  have hsurj : Function.Surjective liftRoot := by
    intro α
    obtain ⟨β, hβ, he⟩ := hroots.surjOn α.property
    exact ⟨⟨β, hβ⟩, Subtype.ext he⟩
  have hc (β : Root T) :
      pushCocharacters q (E.rootDatum.coroot (liftRoot β)) = D.rootDatum.coroot β := by
    change Additive.ofMul ((E.rootDatum.coroot (liftRoot β)).toMul ≫ q) =
      D.rootDatum.coroot β
    exact congrArg Additive.ofMul
      ((hcoroots β.val β.property (liftRoot β).property).2 _ _
        (E.attached (liftRoot β)) (D.attached β))
  simp only [corootLatticeOf, Submodule.map_span]
  congr 1
  rw [← Set.range_comp, ← hsurj.range_comp (pushCocharacters q ∘ E.rootDatum.coroot)]
  exact congrArg Set.range (funext hc)

private theorem marked_corootLattice_eq {n : ℕ} (hn : 0 < n) {O : AffineAlgebraicGroup k}
    {T : ClosedSubgroup O.val} [IsCommMonObj T.group.X] (D : Datum T)
    (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (hD : IsTypeBDatum n T D X Y) :
    (corootLatticeOf D).map Y.toLinearMap = evenSum n := by
  have hs : Y.toLinearMap '' Set.range D.rootDatum.coroot = Prod.snd '' corootPairs n := by
    rw [← hD.2.2, Set.image_image, Set.image_univ, ← Set.range_comp]
    rfl
  rw [corootLatticeOf, Submodule.map_span, hs, (corootLattice n hn).1]

end

end SpinLattice

section AdjointCliffordAction

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj

open Albert.SpinSpecification (vectors coefficientMap spinUnits IsVectorAction conjugate SchemePoints)
open Albert.SpinFunctor (changeCoefficients)
open private changeCoefficients_vector changeModule from LinearAlgebraicGroups.Albert.SpinFunctor

noncomputable section

variable {k : Type u} [Field k] (n : ℕ) (S : CommAlgCat.{u} k)

private theorem scalarClifford_algEquiv_ext
    {φ ψ : oddClifford n S ≃ₐ[S] oddClifford n S}
    (h : ∀ x, φ (vectors (form n k) S x) = ψ (vectors (form n k) S x)) : φ = ψ :=
  AlgEquiv.ext fun x => DFunLike.congr_fun
    (scalarClifford_hom_ext n S (f := φ.toAlgHom) (g := ψ.toAlgHom) h) x

private def cliffordIsometry (h : specialOrthogonal n S) :
    oddClifford n S ≃ₐ[S] oddClifford n S :=
  (isometry_clifford_equivariance n S h).exists.choose

private theorem cliffordIsometry_spec (h : specialOrthogonal n S) :
    (∀ x, cliffordIsometry n S h (vectors (form n k) S x) = vectors (form n k) S (h.val x)) ∧
    (∀ a, a ∈ spinUnits (form n k) S →
      Units.map (cliffordIsometry n S h).toMonoidHom a ∈ spinUnits (form n k) S) ∧
    (∀ a, IsVectorAction (form n k) S a h.val → ∀ x,
      cliffordIsometry n S h x = conjugate (form n k) S a x) :=
  (isometry_clifford_equivariance n S h).exists.choose_spec

private def cliffordIsometryHom :
    specialOrthogonal n S →* (oddClifford n S ≃ₐ[S] oddClifford n S) where
  toFun := cliffordIsometry n S
  map_one' := by
    apply scalarClifford_algEquiv_ext n S
    intro x
    exact (cliffordIsometry_spec n S 1).1 x
  map_mul' g h := by
    apply scalarClifford_algEquiv_ext n S
    intro x
    change cliffordIsometry n S (g * h) (vectors (form n k) S x) =
      cliffordIsometry n S g (cliffordIsometry n S h (vectors (form n k) S x))
    rw [(cliffordIsometry_spec n S (g * h)).1,
      (cliffordIsometry_spec n S h).1, (cliffordIsometry_spec n S g).1]
    rfl

private theorem cliffordIsometry_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (a : specialOrthogonal n S) (b : specialOrthogonal n T)
    (hn : ∀ x, changeModule f.hom (a.val x) = b.val (changeModule f.hom x)) :
    ∀ x : oddClifford n S,
      coefficientMap (form n k) S f.hom (cliffordIsometry n S a x) =
        cliffordIsometry n T b (coefficientMap (form n k) S f.hom x) := by
  let Q := form n k
  let c := changeCoefficients Q f.hom
  let φ := cliffordIsometry n S a
  let ψ := cliffordIsometry n T b
  have h : c.comp (φ.toAlgHom.restrictScalars k) = (ψ.toAlgHom.restrictScalars k).comp c := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro s
      change c (φ (s ⊗ₜ[k] (1 : CliffordAlgebra Q))) = ψ (c (s ⊗ₜ[k] (1 : CliffordAlgebra Q)))
      have hφ : φ (s ⊗ₜ[k] (1 : CliffordAlgebra Q)) = s ⊗ₜ[k] (1 : CliffordAlgebra Q) :=
        φ.commutes s
      have hc : c (s ⊗ₜ[k] (1 : CliffordAlgebra Q)) = f.hom s ⊗ₜ[k] (1 : CliffordAlgebra Q) := by
        simp [c, changeCoefficients]
      rw [hφ, hc]
      exact (ψ.commutes (f.hom s)).symm
    · apply CliffordAlgebra.hom_ext
      apply LinearMap.ext
      intro v
      change c (φ (vectors Q S (1 ⊗ₜ[k] v))) = ψ (c (vectors Q S (1 ⊗ₜ[k] v)))
      rw [show φ (vectors Q S (1 ⊗ₜ[k] v)) = _ from (cliffordIsometry_spec n S a).1 _,
        changeCoefficients_vector, changeCoefficients_vector,
        show ψ (vectors Q T (changeModule f.hom (1 ⊗ₜ[k] v))) = _ from
          (cliffordIsometry_spec n T b).1 _, hn]
  exact fun x => DFunLike.congr_fun h x

private theorem representsCliffordAction {O : Specs.GroupScheme k}
    (o : ∀ S : CommAlgCat.{u} k, SchemePoints O S ≃* specialOrthogonal n S)
    (ho : RepresentsSpecialOrthogonal O o) :
    RepresentsCliffordAction O o := by
  refine ⟨fun S => (cliffordIsometryHom n S).comp (o S).toMonoidHom, ?_, ?_⟩
  · intro S a
    exact cliffordIsometry_spec n S (o S a)
  · intro S T f a
    exact cliffordIsometry_natural n f (o S a) (o T (mapPoints f a)) (ho f a)

end

end AdjointCliffordAction

section SplitModel

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

open Albert.SpinSpecification (SchemePoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (corootLatticeOf)
open private spinUnitPoints spinUnitPoints_represents from LinearAlgebraicGroups.Albert.SpinFunctor
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private pushCocharacters from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
/-- In odd dimension and characteristic different from two, the intrinsic spin
scheme is the simply connected cover of the split adjoint special orthogonal scheme. -/
theorem splitOddSpin : SplitOddSpin.{u} := by
  intro k _ n h₂ hn
  rcases n with _ | m
  · exact (Nat.not_lt_zero _ hn).elim
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  let G := spinAlgebraicGroup (k := k) n
  let O := specialOrthogonalGroup (k := k) n
  let T : Specs.ClosedSubgroup O.val := orthogonalTorus n
  let U : Specs.ClosedSubgroup G.val := spinTorus m h₂
  let p : G.val ⟶ O.val := spinVectorMorphism n h₂
  let q : U.group ⟶ T.group := spinTorusProjection m
  let Z := spinScalarSubgroup (k := k) n
  have hOs := specialOrthogonal_smooth n h₂
  have hTs := orthogonalTorus_split (k := k) n
  obtain ⟨hO, _, hOcentre, _, hTC, hTm⟩ :=
    LinearAlgebraicGroups.OddSpinOrthogonalGeometry.geometry n hn h₂ O T hTs
      (orthogonalGeometryModel n) hOs (specialOrthogonal_geometricallyConnected n h₂)
  have hp := spinVectorMorphism_isCentralIsogeny n h₂ hOs
  have he := (spinVectorMorphism_finiteEtale n h₂ hOs).2
  have hGs : Smooth G.val.X.hom := by
    have hh : Smooth (p.hom.hom.left ≫ O.val.X.hom) := inferInstance
    rwa [p.hom.hom.w] at hh
  have hG : IsSemisimple G := semisimple_of_finite_cover p hp hGs
    (spin_geometricallyConnected n h₂ hn) hO
  have hGr := reductive_of_semisimple G hG
  have hOr := reductive_of_semisimple O hO
  have hUs := spinTorus_split m h₂
  have hq := spinTorus_restriction m h₂
  have hP := spinTorus_pullback m h₂
  have hUm : IsGeometricallyMaximal U :=
    geometricallyMaximal_of_full_torus_preimage (U := U) (T := T) hUs p q hq hP (hTC (AlgebraicClosure k))
  let cT : IsCommMonObj T.group.X := orthogonalTorusModel_comm n
  let X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ) := characterCoordinates n
  let Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ) := cocharacterCoordinates n
  obtain ⟨D, hD⟩ := orthogonalTypeBDatum n h₂ hn hOr hTm
  obtain ⟨cU, ⟨E⟩⟩ := RootData.AbstractPairing.abstractPairing G hGr U hUs hUm
  have hTargetLattice := marked_corootLattice_eq hn D X Y hD
  let push : Additive (Cocharacter U.group) →ₗ[ℤ] (Fin n → ℤ) :=
    Y.toLinearMap.comp (pushCocharacters q)
  have hinj := spinProjection_cocharacter_injective (k := k) m
  have hPushInj : Function.Injective push := by
    intro a b hab
    exact congrArg Additive.ofMul (hinj (congrArg Additive.toMul (Y.injective hab)))
  have hRange : Set.range (fun c : Cocharacter U.group => Y (Additive.ofMul (c ≫ q))) =
      evenSum n := spinProjection_exponents (k := k) m
  have hMap := map_corootLattice_of_isogeny hGr hOr hUs hUm hTs hTm p hp q hq E D
  have hCoroot : (corootLatticeOf E).map push = evenSum n :=
    (Submodule.map_comp (pushCocharacters q) Y.toLinearMap _).trans
      ((congrArg (Submodule.map Y.toLinearMap) hMap).trans hTargetLattice)
  have hPushRange : LinearMap.range push = evenSum n := SetLike.coe_injective hRange
  have hFull : corootLatticeOf E = ⊤ :=
    (Submodule.map_injective_of_injective hPushInj)
      (hCoroot.trans (hPushRange.symm.trans (Submodule.map_top push).symm))
  have hSC := (Classification.SimplyConnectedLattice.latticeCriterion G hG U hUs hUm E).mpr hFull
  refine ⟨G, O, p, spinUnitPoints (form n k) (matrixBasis n), orthogonalPoints n h₂,
    cliffordEquivariance, representsCliffordAction n (orthogonalPoints n h₂) (orthogonalPoints_natural n h₂),
    spinUnitPoints_represents _ _, orthogonalPoints_natural n h₂,
    spinVectorMorphism_action n h₂, hG, hSC, hO, hp, he, hOcentre,
    Z, spinVectorMorphism_kernel n h₂, rfl, spinScalarSubgroup_represents_centre n h₂ hOcentre,
    spinScalarSubgroup_point_scalar n, spinVectorMorphism_quotient n h₂ hOs,
    T, U, q, hTs, hTm, hUs, hUm, hq, hP, spinTorus_pullbackPoints m h₂,
    torusPointsToUnits n, spinTorusParameters m, fun S a => orthogonalTorus_points n S h₂ a,
    ?_, ?_, cT, D, X, Y, hD, hTargetLattice, (fun S a χ => characterCoordinates_evaluation n χ S a),
    (fun S z c i => cocharacterExponents_point n c S z i), hinj, hRange⟩
  · intro S a
    exact (congrArg (torusPointsToUnits n S) (spinTorusProjection_points m S a)).trans
      (spinTorusOrthogonalPoints_eval m S a)
  · intro S a
    have ha := (congrArg (spinUnitPoints (form n k) (matrixBasis n) S)
      (spinTorusInclusion_points m h₂ S a)).trans (spinTorusToSpinPoints_unit m h₂ S a)
    exact (congrArg Units.val ha).trans (liftedDiagonalUnit_val n S (spinTorusParameters m S a))

end SplitModel

end LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
