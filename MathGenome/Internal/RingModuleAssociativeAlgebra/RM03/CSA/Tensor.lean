import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Enveloping
import Mathlib.Algebra.Central.TensorProduct
import Mathlib.RingTheory.SimpleRing.Congr

/-! Simplicity, centers and scalar extension of tensor products of algebras. -/

namespace RM03.CSA

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

variable {k : Type u} [Field k]
  {A : Type v} [Ring A] [Algebra k A] {B : Type w} [Ring B] [Algebra k B]

/-- The tensor extension of an endomorphism of the first factor preserves every ideal. -/
private theorem rTensor_mem (hA : IsCentralSimple k A) (I : TwoSidedIdeal (A ⊗[k] B))
    (T : Module.End k A) {z : A ⊗[k] B} (hz : z ∈ I) : T.rTensor B z ∈ I := by
  obtain ⟨t, rfl⟩ := (mulLeftRight_bijective hA).2 T
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simpa using I.add_mem ht hs
  | tmul a b =>
    have hAction : (AlgHom.mulLeftRight k A (a ⊗ₜ[k] b)).rTensor B z =
        (a ⊗ₜ[k] (1 : B)) * z * (MulOpposite.unop b ⊗ₜ[k] (1 : B)) := by
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        simp [LinearMap.rTensor_tmul, AlgHom.mulLeftRight_apply, tmul_mul_tmul]
      | add x y hx hy => simp [map_add, hx, hy, mul_add, add_mul]
    rw [hAction]
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hz)

/-- A central simple first factor and a simple second factor give a simple tensor product. -/
theorem isSimpleRing_tensor (hA : IsCentralSimple k A) (hB : IsSimpleRing B) :
    IsSimpleRing (A ⊗[k] B) := by
  classical
  let : IsSimpleRing A := hA.1
  let : IsSimpleRing B := hB
  have hinj : Function.Injective (includeRight : B →ₐ[k] A ⊗[k] B) :=
    includeRight_injective (FaithfulSMul.algebraMap_injective k A)
  let : Nontrivial (A ⊗[k] B) := hinj.nontrivial
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I ↦ ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ z : A ⊗[k] B, z ∈ I ∧ z ≠ 0 := by
    by_contra! h
    exact hI (eq_bot_iff.mpr fun z hz ↦ by simpa only [TwoSidedIdeal.mem_bot] using h z hz)
  obtain ⟨z, hz, hzne⟩ := hex
  let basis := Module.Free.chooseBasis k A
  let coefficients := TensorProduct.equivFinsuppOfBasisLeft (N := B) basis
  have hc : ∃ i, coefficients z i ≠ 0 := by
    by_contra! h
    apply hzne
    apply coefficients.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hc
  let T : Module.End k A := (LinearMap.toSpanSingleton k A 1).comp (basis.coord i)
  have hExtract (x : A ⊗[k] B) :
      T.rTensor B x = (1 : A) ⊗ₜ[k] coefficients x i := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      simp [T, coefficients, LinearMap.rTensor_tmul, Module.Basis.coord_apply,
        TensorProduct.smul_tmul]
    | add a b ha hb => simp [map_add, Finsupp.add_apply, ha, hb, TensorProduct.tmul_add]
  let includeB : B →ₐ[k] A ⊗[k] B := includeRight
  have hm : coefficients z i ∈ I.comap includeB := by
    rw [TwoSidedIdeal.mem_comap]
    change (1 : A) ⊗ₜ[k] coefficients z i ∈ I
    rw [← hExtract]
    exact rTensor_mem hA I T hz
  rcases hB.simple.eq_bot_or_eq_top (I.comap includeB) with hj | hj
  · rw [hj, TwoSidedIdeal.mem_bot] at hm
    exact (hi hm).elim
  · apply (I.one_mem_iff).mp
    have htop : (1 : B) ∈ I.comap includeB := hj.symm ▸ TwoSidedIdeal.mem_top B
    simpa only [TwoSidedIdeal.mem_comap, map_one] using htop

/-- The center comes from the second factor, which may have arbitrary dimension and center. -/
theorem center_tensor (hA : IsCentralSimple k A) :
    Subalgebra.center k (A ⊗[k] B) =
      (Subalgebra.center k B).map (includeRight : B →ₐ[k] A ⊗[k] B) := by
  classical
  let : IsSimpleRing A := hA.1
  let : Algebra.IsCentral k A := hA.2.1
  let basis := Module.Free.chooseBasis k B
  let coefficients := TensorProduct.equivFinsuppOfBasisRight (M := A) basis
  refine le_antisymm ?_ (includeRight_map_center_le k A B)
  intro z hz
  have hz' := Subalgebra.mem_center_iff.mp hz
  have hleft (a : A) (x : A ⊗[k] B) (i : Module.Free.ChooseBasisIndex k B) :
      coefficients ((a ⊗ₜ[k] (1 : B)) * x) i = a * coefficients x i := by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      simp [coefficients, tmul_mul_tmul]
    | add x y hx hy => simp [mul_add, map_add, Finsupp.add_apply, hx, hy]
  have hright (a : A) (x : A ⊗[k] B) (i : Module.Free.ChooseBasisIndex k B) :
      coefficients (x * (a ⊗ₜ[k] (1 : B))) i = coefficients x i * a := by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      simp [coefficients, tmul_mul_tmul]
    | add x y hx hy => simp [add_mul, map_add, Finsupp.add_apply, hx, hy]
  have hc (i : Module.Free.ChooseBasisIndex k B) :
      ∃ r : k, algebraMap k A r = coefficients z i := by
    apply Algebra.mem_bot.mp
    apply Algebra.IsCentral.out
    refine Subalgebra.mem_center_iff.mpr fun a ↦ ?_
    rw [← hleft, ← hright, hz']
  choose r hr using hc
  let includeB : B →ₐ[k] A ⊗[k] B := includeRight
  let b := ∑ i ∈ (coefficients z).support, r i • basis i
  have hb : includeB b = z := by
    calc
      includeB b = (coefficients z).sum (fun i a ↦ a ⊗ₜ[k] basis i) := by
        simp [includeB, b, Finsupp.sum, TensorProduct.smul_tmul, ← hr, Algebra.algebraMap_eq_smul_one]
      _ = coefficients.symm (coefficients z) :=
        (TensorProduct.equivFinsuppOfBasisRight_symm_apply basis _).symm
      _ = z := coefficients.symm_apply_apply z
  refine Subalgebra.mem_map.mpr ⟨b, Subalgebra.mem_center_iff.mpr fun c ↦ ?_, hb⟩
  apply includeRight_injective (FaithfulSMul.algebraMap_injective k A)
  change includeB (c * b) = includeB (b * c)
  rw [map_mul, map_mul, hb, hz']

/-- Tensor products of central simple algebras are central simple over the common field. -/
theorem isCentralSimple_tensor (hA : IsCentralSimple k A) (hB : IsCentralSimple k B) :
    IsCentralSimple k (A ⊗[k] B) := by
  let : FiniteDimensional k A := hA.2.2
  let : FiniteDimensional k B := hB.2.2
  refine ⟨isSimpleRing_tensor hA hB.1, ⟨?_⟩, inferInstance⟩
  rw [center_tensor hA]
  exact (Subalgebra.map_mono hB.2.1.out).trans_eq (Algebra.map_bot _)

variable {L : Type w} [Field L] [Algebra k L]

/-- Scalar extension preserves central simplicity for any extension field. -/
theorem isCentralSimple_baseChange (hA : IsCentralSimple k A) :
    IsCentralSimple L (BaseChange k L A) := by
  let := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := L)
  let e := baseChangeEquivTensor k L A
  let : FiniteDimensional k A := hA.2.2
  refine ⟨IsSimpleRing.of_ringEquiv e.toRingEquiv.symm (isSimpleRing_tensor hA inferInstance),
    ⟨?_⟩, inferInstance⟩
  intro z hz
  have hz' : e z ∈ Subalgebra.center k (A ⊗[k] L) := by
    refine Subalgebra.mem_center_iff.mpr fun x ↦ ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.mp hz y]
  rw [center_tensor hA] at hz'
  obtain ⟨l, _, hl⟩ := Subalgebra.mem_map.mp hz'
  exact Algebra.mem_bot.mpr ⟨l, e.injective ((e.commutes l).trans hl)⟩

/-- The center after scalar extension is the image of the extension field. -/
theorem center_baseChange (hA : IsCentralSimple k A) :
    (Subalgebra.center L (BaseChange k L A) : Set (BaseChange k L A)) =
      Set.range (algebraMap L (BaseChange k L A)) :=
  ((isCentralSimple_iff L (BaseChange k L A)).mp (isCentralSimple_baseChange hA)).2.2.2

/-- Scalar extension leaves the dimension of a central simple algebra unchanged. -/
theorem finrank_baseChange (_hA : IsCentralSimple k A) :
    Module.finrank L (BaseChange k L A) = Module.finrank k A :=
  Module.finrank_baseChange

end RM03.CSA
