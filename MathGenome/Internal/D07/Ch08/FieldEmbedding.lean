import MathGenome.Internal.Specs.D07.Ch08.FieldEmbedding
import MathGenome.Internal.D07.Ch08.FieldIdeals
import MathGenome.Internal.D07.Ch08.InjectiveKernel

/-! Maps out of fields, including the nonunital and zero-ring cases. -/

universe u v

namespace D07.Ch08.FieldEmbedding

open Specs.D07.Ch08.FieldEmbedding

theorem nonunital_kernel : NonunitalKernel.{u, v} := by
  intro F R _ _ f hf
  have hproper : TwoSidedIdeal.ker f ≠ ⊤ := by
    intro htop
    apply hf
    ext a
    have ha : a ∈ TwoSidedIdeal.ker f := htop.symm ▸ TwoSidedIdeal.mem_top F
    exact (TwoSidedIdeal.mem_ker f).mp ha
  have htrivial :=
    (FieldIdeals.nonzeroUnitsIffTrivialIdeals F).mp
      (fun a ha => isUnit_iff_ne_zero.mpr ha) (TwoSidedIdeal.ker f)
  exact ⟨hproper, htrivial.resolve_right hproper⟩

theorem nonunital_injective : NonunitalInjective.{u, v} := by
  intro F R _ _ f hf
  exact (TwoSidedIdeal.ker_eq_bot f).mp (nonunital_kernel F R f hf).2

theorem unital_kernel : UnitalKernel.{u, v} := by
  intro F R _ _ _ f
  have hnonzero : f.toNonUnitalRingHom ≠ 0 := by
    intro h
    have h1 : f 1 = 0 := DFunLike.congr_fun h (1 : F)
    rw [map_one] at h1
    exact one_ne_zero h1
  have hbot := (nonunital_kernel F R f.toNonUnitalRingHom hnonzero).2
  refine ⟨inferInstance, RingHom.ker_ne_top f, ?_⟩
  apply Ideal.ext
  intro a
  rw [RingHom.mem_ker, Submodule.mem_bot]
  constructor
  · intro ha
    have hmem : a ∈ TwoSidedIdeal.ker f.toNonUnitalRingHom :=
      (TwoSidedIdeal.mem_ker f.toNonUnitalRingHom).mpr ha
    simpa only [hbot, TwoSidedIdeal.mem_bot] using hmem
  · rintro rfl
    exact map_zero f

theorem unital_injective : UnitalInjective.{u, v} := by
  intro F R _ _ _ f
  exact (InjectiveKernel.injective_iff_kernel_zero F R f).mpr
    (unital_kernel F R f).2.2

theorem zero_ring_counterexample : ZeroRingCounterexample.{u, v} := by
  intro F R _ _ _
  let f : F →+* R :=
    { toFun := fun _ => 0
      map_zero' := rfl
      map_one' := Subsingleton.elim _ _
      map_add' := fun _ _ => (add_zero 0).symm
      map_mul' := fun _ _ => (mul_zero 0).symm }
  refine ⟨f, fun _ => rfl, ?_⟩
  intro hinj
  exact zero_ne_one (hinj (show f 0 = f 1 from rfl))

end D07.Ch08.FieldEmbedding
