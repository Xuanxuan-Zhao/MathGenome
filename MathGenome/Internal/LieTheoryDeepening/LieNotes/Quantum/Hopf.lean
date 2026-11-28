import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Hopf
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.AntipodeMap
import Mathlib.Tactic.FinCases

import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Coproduct
noncomputable section

namespace LieNotes.Quantum.Hopf

open Specs.LieNotes.Quantum
open Specs.LieNotes.Quantum.Presentation
open Specs.LieNotes.Quantum.Hopf (ConvolutionIdentities antipodeLinear)
open Specs.LieNotes.Quantum.AntipodeMap (GeneratorFormulas)
open scoped TensorProduct

universe u v

section Convolution

variable {A : Type u} {B : Type v} [CommRing A] [Ring B] [Algebra A B]

private def leftProduct (s : B →ₗ[A] B) : B ⊗[A] B →ₗ[A] B :=
  LinearMap.mul' A B ∘ₗ s.rTensor B

private def rightProduct (s : B →ₗ[A] B) : B ⊗[A] B →ₗ[A] B :=
  LinearMap.mul' A B ∘ₗ s.lTensor B

@[simp] private theorem leftProduct_tmul (s : B →ₗ[A] B) (x y : B) :
    leftProduct s (x ⊗ₜ[A] y) = s x * y := by
  rw [leftProduct, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply]

@[simp] private theorem rightProduct_tmul (s : B →ₗ[A] B) (x y : B) :
    rightProduct s (x ⊗ₜ[A] y) = x * s y := by
  rw [rightProduct, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.mul'_apply]

variable {s : B →ₗ[A] B}

private theorem leftProduct_mul_tmul (hs : ∀ x y, s (x * y) = s y * s x)
    (t : B ⊗[A] B) (a b : B) :
    leftProduct s (t * (a ⊗ₜ[A] b)) = s a * leftProduct s t * b := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, hs, mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy, mul_add]

private theorem rightProduct_tmul_mul (hs : ∀ x y, s (x * y) = s y * s x)
    (a b : B) (t : B ⊗[A] B) :
    rightProduct s ((a ⊗ₜ[A] b) * t) = a * rightProduct s t * s b := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, hs, mul_assoc]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy, add_mul]

-- The inner two factors can be contracted first whenever their contraction is a scalar.
private theorem leftProduct_mul (hs : ∀ x y, s (x * y) = s y * s x)
    {t : B ⊗[A] B} {r : A} (ht : leftProduct s t = algebraMap A B r) (z : B ⊗[A] B) :
    leftProduct s (t * z) = algebraMap A B r * leftProduct s z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => rw [leftProduct_mul_tmul hs, ht, ← Algebra.commutes, mul_assoc, leftProduct_tmul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

private theorem rightProduct_mul (hs : ∀ x y, s (x * y) = s y * s x)
    {t : B ⊗[A] B} {r : A} (ht : rightProduct s t = algebraMap A B r) (z : B ⊗[A] B) :
    rightProduct s (z * t) = rightProduct s z * algebraMap A B r := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => rw [rightProduct_tmul_mul hs, ht, mul_assoc, Algebra.commutes, ← mul_assoc,
      rightProduct_tmul]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

/-- The elements where both antipode products agree with the counit form a subalgebra. -/
private def convolutionSubalgebra (Δ : B →ₐ[A] B ⊗[A] B) (ε : B →ₐ[A] A)
    (hs₁ : s 1 = 1) (hs : ∀ x y, s (x * y) = s y * s x) : Subalgebra A B where
  carrier := {x | leftProduct s (Δ x) = algebraMap A B (ε x) ∧
    rightProduct s (Δ x) = algebraMap A B (ε x)}
  add_mem' := by
    intro x y hx hy
    exact ⟨by simp only [map_add, hx.1, hy.1], by simp only [map_add, hx.2, hy.2]⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨by rw [map_mul, leftProduct_mul hs hx.1, hy.1, ← map_mul, ← map_mul],
      by rw [map_mul, rightProduct_mul hs hy.2, hx.2, ← map_mul, ← map_mul]⟩
  algebraMap_mem' := by
    intro r
    constructor <;>
      simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, hs₁]

end Convolution

section Presentation

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
variable {C : Cartan A T}
variable (d : Coproduct.Data C) (S : U C →ₐ[A] (U C)ᵐᵒᵖ)

@[simp] private theorem antipodeLinear_one : antipodeLinear S 1 = 1 := by
  change (S 1).unop = 1
  rw [map_one, MulOpposite.unop_one]

private theorem antipodeLinear_mul (x y : U C) :
    antipodeLinear S (x * y) = antipodeLinear S y * antipodeLinear S x := by
  change (S (x * y)).unop = (S y).unop * (S x).unop
  rw [map_mul, MulOpposite.unop_mul]

private abbrev convolutionOn (d : Coproduct.Data C) (S : U C →ₐ[A] (U C)ᵐᵒᵖ) :
    Subalgebra A (U C) :=
  convolutionSubalgebra d.comul d.counit (antipodeLinear_one S) (antipodeLinear_mul S)

private theorem mem_convolutionOn (x : U C) : x ∈ convolutionOn d S ↔
    leftProduct (antipodeLinear S) (d.comul x) = algebraMap A (U C) (d.counit x) ∧
    rightProduct (antipodeLinear S) (d.comul x) = algebraMap A (U C) (d.counit x) := Iff.rfl

private theorem convolutionOn_E (hS : GeneratorFormulas C S)
    (hK : ∀ i, antipodeLinear S (Coproduct.K C i : U C) = (↑((Coproduct.K C i)⁻¹) : U C))
    (i : Root) : E C i ∈ convolutionOn d S := by
  have he : antipodeLinear S (E C i) = -((↑((Coproduct.K C i)⁻¹) : U C) * E C i) :=
    hS.2.1 i
  rw [mem_convolutionOn, d.comul_E, d.counit_E]
  simp only [map_add, leftProduct_tmul, rightProduct_tmul, antipodeLinear_one,
    he, hK, mul_one, map_zero, neg_add_cancel, true_and]
  rw [mul_neg, ← mul_assoc, Units.mul_inv, one_mul, add_neg_cancel]

private theorem convolutionOn_F (hS : GeneratorFormulas C S)
    (hKinv : ∀ i, antipodeLinear S (↑((Coproduct.K C i)⁻¹) : U C) = (Coproduct.K C i : U C))
    (i : Root) : F C i ∈ convolutionOn d S := by
  have hf : antipodeLinear S (F C i) = -(F C i * (Coproduct.K C i : U C)) := hS.2.2 i
  rw [mem_convolutionOn, d.comul_F, d.counit_F]
  simp only [map_add, leftProduct_tmul, rightProduct_tmul, antipodeLinear_one,
    hf, hKinv, one_mul, map_zero, add_neg_cancel, and_true]
  rw [neg_mul, mul_assoc, Units.mul_inv, mul_one, neg_add_cancel]

private theorem antipodeLinear_K_inv (i : Root)
    (hK : antipodeLinear S (Coproduct.K C i : U C) = (↑((Coproduct.K C i)⁻¹) : U C)) :
    antipodeLinear S (↑((Coproduct.K C i)⁻¹) : U C) = (Coproduct.K C i : U C) := by
  let k := Coproduct.K C i
  change antipodeLinear S (↑k⁻¹ : U C) = (↑((k⁻¹)⁻¹) : U C)
  apply Units.eq_inv_of_mul_eq_one_right
  calc
    antipodeLinear S (↑k⁻¹ : U C) * (↑k⁻¹ : U C) = antipodeLinear S ((k : U C) * ↑k⁻¹) := by
      rw [antipodeLinear_mul, hK]
    _ = 1 := by rw [Units.mul_inv, antipodeLinear_one]

private theorem convolutionOn_groupLike (k : (U C)ˣ)
    (hΔ : d.comul (k : U C) = (k : U C) ⊗ₜ[A] (k : U C))
    (hε : d.counit (k : U C) = 1)
    (hS : antipodeLinear S (k : U C) = (↑k⁻¹ : U C)) : (k : U C) ∈ convolutionOn d S := by
  rw [mem_convolutionOn, hΔ, hε]
  simp only [leftProduct_tmul, rightProduct_tmul, hS, map_one, Units.inv_mul, Units.mul_inv,
    and_self]

private theorem comul_K_inv (i : Root) :
    d.comul (↑((Coproduct.K C i)⁻¹) : U C) =
      (↑((Coproduct.K C i)⁻¹) : U C) ⊗ₜ[A] (↑((Coproduct.K C i)⁻¹) : U C) := by
  let k := Coproduct.K C i
  apply (Units.mul_right_inj (Units.map d.comul.toMonoidHom k)).mp
  change d.comul (k : U C) * d.comul (↑k⁻¹ : U C) =
    d.comul (k : U C) * ((↑k⁻¹ : U C) ⊗ₜ[A] (↑k⁻¹ : U C))
  calc
    d.comul (k : U C) * d.comul (↑k⁻¹ : U C) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    _ = _ := by
      rw [show d.comul (k : U C) = _ from d.comul_K i, Algebra.TensorProduct.tmul_mul_tmul,
        Units.mul_inv, ← Algebra.TensorProduct.one_def]

private theorem counit_K_inv (i : Root) : d.counit (↑((Coproduct.K C i)⁻¹) : U C) = 1 := by
  let k := Coproduct.K C i
  calc
    d.counit (↑k⁻¹ : U C) = d.counit (k : U C) * d.counit (↑k⁻¹ : U C) := by rw [d.counit_K, one_mul]
    _ = 1 := by rw [← map_mul, Units.mul_inv, map_one]

-- The two quotients of the free algebra retain generation by Cartan and root letters.
private theorem presentation_mem (P : Subalgebra A (U C))
    (ht : ∀ t, cartan C t ∈ P) (he : ∀ i, E C i ∈ P) (hf : ∀ i, F C i ∈ P)
    (x : U C) : x ∈ P := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective A (serreIdeal C).asIdeal x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective A (basicIdeal C).asIdeal b
  change serreQuotient C (basicQuotient C a) ∈ P
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact P.algebraMap_mem r
  | grade1 x =>
    rcases x with t | (i | i)
    · exact ht t
    · exact he i
    · exact hf i
  | mul a b ha hb => simpa only [map_mul] using P.mul_mem ha hb
  | add a b ha hb => simpa only [map_add] using P.add_mem ha hb

private theorem convolutionIdentities (hS : GeneratorFormulas C S)
    (hK : ∀ i, antipodeLinear S (Coproduct.K C i : U C) = (↑((Coproduct.K C i)⁻¹) : U C))
    (ht : ∀ t, cartan C t ∈ convolutionOn d S) : ConvolutionIdentities d (antipodeLinear S) := by
  have h (x : U C) := (mem_convolutionOn d S x).mp
    (presentation_mem (convolutionOn d S) ht (convolutionOn_E d S hS hK)
      (convolutionOn_F d S hS (fun i => antipodeLinear_K_inv S i (hK i))) x)
  exact ⟨LinearMap.ext fun x => (h x).1, LinearMap.ext fun x => (h x).2⟩

private def hopfData (hS : GeneratorFormulas C S)
    (hK : ∀ i, antipodeLinear S (Coproduct.K C i : U C) = (↑((Coproduct.K C i)⁻¹) : U C))
    (hbij : Function.Bijective S) (ht : ∀ t, cartan C t ∈ convolutionOn d S) :
    Specs.LieNotes.Quantum.Hopf.Data C d where
  antipode := S
  generatorFormulas := hS
  antipode_K := hK
  bijective := MulOpposite.unop_bijective.comp hbij
  convolution := convolutionIdentities d S hS hK ht

end Presentation

section LaurentCartan

variable {A : Type u} {B : Type v} [CommRing A] [Ring B] [Algebra A B]

private theorem unit_zpow_mem (P : Subalgebra A B) (g : Bˣ) (hp : (g : B) ∈ P)
    (hn : (↑g⁻¹ : B) ∈ P) (n : ℤ) : (↑(g ^ n) : B) ∈ P := by
  cases n with
  | ofNat n =>
    change (↑(g ^ (n : ℤ)) : B) ∈ P
    simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using P.pow_mem hp n
  | negSucc n =>
    simpa only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val] using (P.pow_mem hn (n + 1))

private theorem laurent_mem (P : Subalgebra A B) (f : Laurent A →ₐ[A] B)
    (hp : ∀ i : Root, f (↑(laurentUnit (A := A) (coordinate i)) : Laurent A) ∈ P)
    (hn : ∀ i : Root, f (↑((laurentUnit (A := A) (coordinate i))⁻¹) : Laurent A) ∈ P)
    (t : Laurent A) : f t ∈ P := by
  let g := (f.toMonoidHom.comp (AddMonoidAlgebra.of A Lattice)).toHomUnits
  have hg (i : Root) : g (Multiplicative.ofAdd (coordinate i)) =
      Units.map f.toMonoidHom (laurentUnit (coordinate i)) := Units.ext rfl
  induction t using AddMonoidAlgebra.induction_on with
  | of m =>
    have hm : m = m 0 • coordinate 0 + m 1 • coordinate 1 := by
      funext i
      fin_cases i <;> simp [coordinate]
    have hm' : Multiplicative.ofAdd m =
        Multiplicative.ofAdd (coordinate 0) ^ m 0 * Multiplicative.ofAdd (coordinate 1) ^ m 1 :=
      congrArg Multiplicative.ofAdd hm
    change (↑(g (Multiplicative.ofAdd m)) : B) ∈ P
    rw [hm', map_mul, map_zpow, map_zpow, hg 0, hg 1, Units.val_mul]
    exact P.mul_mem (unit_zpow_mem P _ (hp 0) (hn 0) (m 0))
      (unit_zpow_mem P _ (hp 1) (hn 1) (m 1))
  | add x y hx hy => simpa only [map_add] using P.add_mem hx hy
  | smul r x hx => simpa only [map_smul] using P.smul_mem hx r

end LaurentCartan

section Concrete

variable {k : Type u} [Field k] [CharZero k]

private def genericData (q : kˣ) (hq : (q : k)^2 ≠ 1)
    (d : Coproduct.Data (generic q hq)) : Specs.LieNotes.Quantum.Hopf.Data (generic q hq) d := by
  let C := generic q hq
  let h := AntipodeMap.genericCartanLaws q hq
  let S := AntipodeMap.genericAntipode q hq
  have hK (i : Root) : antipodeLinear S (Coproduct.K C i : U C) =
      (↑((Coproduct.K C i)⁻¹) : U C) := AntipodeMap.antipode_K C h i
  refine hopfData d S (AntipodeMap.antipode_formulas C h) hK (AntipodeMap.antipode_bijective C h) ?_
  apply laurent_mem (convolutionOn d S) (cartan C)
  · intro i
    exact convolutionOn_groupLike d S (Coproduct.K C i) (d.comul_K i) (d.counit_K i) (hK i)
  · intro i
    exact convolutionOn_groupLike d S (Coproduct.K C i)⁻¹ (comul_K_inv d i) (counit_K_inv d i)
      (antipodeLinear_K_inv S i (hK i))

private def truncatedData (N : ℕ) (d : Coproduct.TruncatedData k N) :
    Specs.LieNotes.Quantum.Hopf.TruncatedData k N d := by
  let C := truncated k N
  let h := AntipodeMap.truncatedCartanLaws (k := k) N
  let S := AntipodeMap.truncatedAntipode k N
  have hK (i : Root) : antipodeLinear S (Coproduct.K C i : U C) =
      (↑((Coproduct.K C i)⁻¹) : U C) := AntipodeMap.antipode_K C h i
  have hH (i : Root) : antipodeLinear S (Coproduct.H k N i) = -Coproduct.H k N i :=
    AntipodeMap.truncatedAntipode_H N i
  refine ⟨hopfData d.toData S (AntipodeMap.antipode_formulas C h) hK
    (AntipodeMap.antipode_bijective C h) ?_, hH⟩
  let P := convolutionOn d.toData S
  have hgen (i : Root) : cartan C (MvPolynomial.X i) ∈ P := by
    change Coproduct.H k N i ∈ convolutionOn d.toData S
    rw [mem_convolutionOn, d.comul_H, d.counit_H]
    simp only [map_add, leftProduct_tmul, rightProduct_tmul, antipodeLinear_one,
      hH, one_mul, mul_one, map_zero, neg_add_cancel, add_neg_cancel, and_self]
  intro t
  change cartan C t ∈ P
  induction t using MvPolynomial.induction_on with
  | C a =>
    change cartan C (algebraMap _ _ a) ∈ P
    rw [AlgHom.commutes]
    exact P.algebraMap_mem a
  | add x y hx hy => simpa only [map_add] using P.add_mem hx hy
  | mul_X x i hx => simpa only [map_mul] using P.mul_mem hx (hgen i)

end Concrete

theorem generic_hopf_conditional
    (hGeneric : Coproduct.GenericProp.{u}) (_ : Coproduct.IndeterminateProp.{u})
    (_ : Coproduct.ReductionProp.{u}) (_ : Coproduct.TruncatedProp.{u}) :
    Specs.LieNotes.Quantum.Hopf.GenericProp.{u} := by
  intro k _ _ q hq
  obtain ⟨d⟩ := hGeneric q hq
  exact ⟨d, ⟨genericData q hq d⟩⟩

theorem indeterminate_hopf_conditional
    (_ : Coproduct.GenericProp.{u}) (hIndeterminate : Coproduct.IndeterminateProp.{u})
    (_ : Coproduct.ReductionProp.{u}) (_ : Coproduct.TruncatedProp.{u}) :
    Specs.LieNotes.Quantum.Hopf.IndeterminateProp.{u} := by
  intro k _ _
  obtain ⟨d⟩ := hIndeterminate k
  exact ⟨d, ⟨genericData (rationalQ k) (rationalQ_sq_ne k) d⟩⟩

theorem truncated_hopf_conditional
    (_ : Coproduct.GenericProp.{u}) (_ : Coproduct.IndeterminateProp.{u})
    (_ : Coproduct.ReductionProp.{u}) (hTruncated : Coproduct.TruncatedProp.{u}) :
    Specs.LieNotes.Quantum.Hopf.TruncatedProp.{u} := by
  intro k _ _ N hN
  obtain ⟨d⟩ := hTruncated k N hN
  exact ⟨d, ⟨truncatedData N d⟩⟩

theorem truncated_compatibility_conditional
    (_ : Coproduct.GenericProp.{u}) (_ : Coproduct.IndeterminateProp.{u})
    (hReduction : Coproduct.ReductionProp.{u}) (_ : Coproduct.TruncatedProp.{u}) :
    Specs.LieNotes.Quantum.Hopf.ReductionProp.{u} := by
  intro k _ _ M N hM e dN dM SN SM
  obtain ⟨hΔ, hε⟩ := hReduction hM e dN dM
  exact ⟨hΔ, hε,
    AntipodeMap.reduceAntipode_spec e SN.antipode SM.antipode SN.generatorFormulas SM.generatorFormulas⟩

end LieNotes.Quantum.Hopf

universe v8_closure_d3044858561c1568_u0
theorem _root_.«LieNotes».«Quantum».«Hopf».«generic_hopf» : _root_.«Specs».«LieNotes».«Quantum».«Hopf».«GenericProp».{v8_closure_d3044858561c1568_u0} :=
  @_root_.«LieNotes».«Quantum».«Hopf».«generic_hopf_conditional».{v8_closure_d3044858561c1568_u0} (@_root_.«LieNotes».«Quantum».«Coproduct».«generic_coproduct».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«indeterminate_coproduct».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«truncated_compatibility».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«truncated_coproduct».{v8_closure_d3044858561c1568_u0})
theorem _root_.«LieNotes».«Quantum».«Hopf».«indeterminate_hopf» : _root_.«Specs».«LieNotes».«Quantum».«Hopf».«IndeterminateProp».{v8_closure_d3044858561c1568_u0} :=
  @_root_.«LieNotes».«Quantum».«Hopf».«indeterminate_hopf_conditional».{v8_closure_d3044858561c1568_u0} (@_root_.«LieNotes».«Quantum».«Coproduct».«generic_coproduct».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«indeterminate_coproduct».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«truncated_compatibility».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«truncated_coproduct».{v8_closure_d3044858561c1568_u0})
theorem _root_.«LieNotes».«Quantum».«Hopf».«truncated_compatibility» : _root_.«Specs».«LieNotes».«Quantum».«Hopf».«ReductionProp».{v8_closure_d3044858561c1568_u0} :=
  @_root_.«LieNotes».«Quantum».«Hopf».«truncated_compatibility_conditional».{v8_closure_d3044858561c1568_u0} (@_root_.«LieNotes».«Quantum».«Coproduct».«generic_coproduct».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«indeterminate_coproduct».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«truncated_compatibility».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«truncated_coproduct».{v8_closure_d3044858561c1568_u0})
theorem _root_.«LieNotes».«Quantum».«Hopf».«truncated_hopf» : _root_.«Specs».«LieNotes».«Quantum».«Hopf».«TruncatedProp».{v8_closure_d3044858561c1568_u0} :=
  @_root_.«LieNotes».«Quantum».«Hopf».«truncated_hopf_conditional».{v8_closure_d3044858561c1568_u0} (@_root_.«LieNotes».«Quantum».«Coproduct».«generic_coproduct».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«indeterminate_coproduct».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«truncated_compatibility».{v8_closure_d3044858561c1568_u0}) (@_root_.«LieNotes».«Quantum».«Coproduct».«truncated_coproduct».{v8_closure_d3044858561c1568_u0})
