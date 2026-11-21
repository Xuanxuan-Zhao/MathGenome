import MathGenome.Internal.Specs.D05.M15.Symmetric.KernelQuotient
import MathGenome.Internal.D05.M15.SymmetricBasis
import MathGenome.Internal.D05.M06.Complement
import Mathlib.LinearAlgebra.Isomorphisms

/-! K05.15.symmetric: functoriality, image, kernel and quotient compatibility.

We prove quotient compatibility directly by the two universal properties. Its
inverse sends a quotient vector to the class of its degree-one generator. For
a general linear map, factor through `V / ker f`; the resulting linear map is
injective, and its symmetric algebra map is injective by a linear retraction.
This avoids choosing coordinates in the statement or using any averaging.
-/
noncomputable section
namespace D05.M15.Symmetric.KernelQuotient
open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis

abbrev map := @Specs.D05.M15.Symmetric.KernelQuotient.map
abbrev generatedIdeal := @Specs.D05.M15.Symmetric.KernelQuotient.generatedIdeal

theorem map_generator : Specs.D05.M15.Symmetric.KernelQuotient.map_generator := by
  intro K V W _ _ _ _ _ f v
  exact _root_.SymmetricAlgebra.lift_ι_apply _ v

theorem map_unique : Specs.D05.M15.Symmetric.KernelQuotient.map_unique := by
  intro K V W _ _ _ _ _ f F hF
  exact D05.M15.Symmetric.hom_ext F (map f) (fun v => (hF v).trans (map_generator f v).symm)

theorem map_id : Specs.D05.M15.Symmetric.KernelQuotient.map_id := by
  intro K V _ _ _
  apply D05.M15.Symmetric.hom_ext
  intro v
  exact map_generator LinearMap.id v

theorem map_comp : Specs.D05.M15.Symmetric.KernelQuotient.map_comp := by
  intro K V W X _ _ _ _ _ _ _ f g
  apply D05.M15.Symmetric.hom_ext
  intro v
  change map (g.comp f) (_root_.SymmetricAlgebra.ι K V v) =
    map g (map f (_root_.SymmetricAlgebra.ι K V v))
  rw [map_generator, map_generator, map_generator]
  rfl

theorem map_degree_zero : Specs.D05.M15.Symmetric.KernelQuotient.map_degree_zero := by
  intro K V W _ _ _ _ _ f c
  exact (map f).commutes c

theorem map_injective : Specs.D05.M15.Symmetric.KernelQuotient.map_injective := by
  intro K V W _ _ _ _ _ f hf
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have h : (map g).comp (map f) = AlgHom.id K (symmetricAlgebra K V) := by
    rw [← map_comp, hg, map_id]
  exact (show Function.LeftInverse (map g) (map f) from fun x => DFunLike.congr_fun h x).injective

theorem map_surjective : Specs.D05.M15.Symmetric.KernelQuotient.map_surjective := by
  intro K V W _ _ _ _ _ f hf a
  induction a using _root_.SymmetricAlgebra.induction with
  | algebraMap c => exact ⟨algebraMap K _ c, (map f).commutes c⟩
  | ι w =>
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨_root_.SymmetricAlgebra.ι K V v, map_generator f v⟩
  | mul a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a*b, map_mul _ _ _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a+b, map_add _ _ _⟩

section Degrees
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The map on the original adjacent-relation quotient, constructed by descent. -/
def powerMap (f : V →ₗ[K] W) (p : ℕ) :
    symmetricPower K V p →ₗ[K] symmetricPower K W p :=
  (adjacentRelations K V p).liftQ
    (PiTensorProduct.lift ((elementary K W p).compLinearMap (fun _ => f))) (by
      apply Submodule.span_le.mpr
      rintro t ⟨x, i, j, _, rfl⟩
      change PiTensorProduct.lift _ (_ - _) = 0
      rw [map_sub, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
      change elementary K W p (f ∘ x) -
        elementary K W p ((f ∘ x) ∘ Equiv.swap i j) = 0
      rw [D05.M15.Symmetric.elementary_symmetric, sub_self])

@[simp] theorem powerMap_elementary (f : V →ₗ[K] W) (p : ℕ) (x : Fin p → V) :
    powerMap f p (elementary K V p x) = elementary K W p (f ∘ x) := by
  change PiTensorProduct.lift ((elementary K W p).compLinearMap (fun _ => f))
    (PiTensorProduct.tprod K x) = _
  exact PiTensorProduct.lift.tprod x

/-- Equality out of a symmetric power can be tested on elementary classes. -/
theorem powerMap_ext {H : Type*} [AddCommGroup H] [Module K H] (p : ℕ)
    (F G : symmetricPower K V p →ₗ[K] H)
    (h : ∀ x, F (elementary K V p x) = G (elementary K V p x)) : F = G := by
  have ht : F.comp (adjacentRelations K V p).mkQ =
      G.comp (adjacentRelations K V p).mkQ := by
    apply PiTensorProduct.ext
    exact MultilinearMap.ext h
  apply LinearMap.ext
  intro q
  obtain ⟨t, rfl⟩ := (adjacentRelations K V p).mkQ_surjective q
  exact LinearMap.congr_fun ht t

theorem powerMap_inclusion (f : V →ₗ[K] W) (p : ℕ) :
    (powerInclusion (K := K) (V := W) p).comp (powerMap f p) =
      (map f).toLinearMap.comp (powerInclusion (K := K) (V := V) p) := by
  apply powerMap_ext
  intro x
  change powerInclusion (K := K) (V := W) p (powerMap f p (elementary K V p x)) =
    map f (powerInclusion (K := K) (V := V) p (elementary K V p x))
  rw [powerMap_elementary, D05.M15.SymmetricBasis.inclusion_elementary,
    D05.M15.SymmetricBasis.inclusion_elementary, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (map_generator f (x i)).symm

theorem powerMap_surjective (f : V →ₗ[K] W) (hf : Function.Surjective f) (p : ℕ) :
    Function.Surjective (powerMap f p) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_iff'.mpr
  intro q
  obtain ⟨t, rfl⟩ := (adjacentRelations K W p).mkQ_surjective q
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    obtain ⟨y, hy⟩ := (Function.Surjective.piMap (fun _ : Fin p => hf)) x
    refine ⟨c • elementary K V p y, ?_⟩
    change powerMap f p (c • elementary K V p y) =
      (adjacentRelations K W p).mkQ (c • PiTensorProduct.tprod K x)
    rw [map_smul, map_smul, powerMap_elementary]
    exact congrArg (c • ·) (congrArg (elementary K W p) hy)
  | add x y hx hy =>
    simpa only [map_add] using (powerMap f p).range.add_mem hx hy

/-- A surjective linear map maps every homogeneous component onto the target
component; nullary products are included. -/
theorem homogeneous_range (f : V →ₗ[K] W) (hf : Function.Surjective f) (p : ℕ) :
    Submodule.map (map f).toLinearMap
      (LinearMap.range (powerInclusion (K := K) (V := V) p)) =
      LinearMap.range (powerInclusion (K := K) (V := W) p) := by
  rw [← LinearMap.range_comp, ← powerMap_inclusion, LinearMap.range_comp]
  rw [LinearMap.range_eq_top.mpr (powerMap_surjective f hf p), Submodule.map_top]

end Degrees

theorem degree_map : Specs.D05.M15.Symmetric.KernelQuotient.degree_map := by
  intro K V W _ _ _ _ _ f p
  refine ⟨powerMap f p, ⟨powerMap_elementary f p, powerMap_inclusion f p⟩, ?_⟩
  intro L hL
  exact powerMap_ext p L (powerMap f p) (fun x => (hL.1 x).trans (powerMap_elementary f p x).symm)

section Quotients
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem generatedIdeal_le_ker (f : V →ₗ[K] W) (U : Submodule K V)
    (hU : U ≤ LinearMap.ker f) :
    generatedIdeal U ≤ RingHom.ker (map f).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  change map f (_root_.SymmetricAlgebra.ι K V v) = 0
  rw [map_generator, LinearMap.mem_ker.mp (hU hv), map_zero]

/-- Descent of Sym(q) to the quotient by the generated ideal. -/
def quotientForward (U : Submodule K V) :
    (symmetricAlgebra K V ⧸ generatedIdeal U) →ₐ[K] symmetricAlgebra K (V ⧸ U) :=
  Ideal.Quotient.liftₐ (generatedIdeal U) (map U.mkQ) (fun a ha =>
    generatedIdeal_le_ker U.mkQ U (by rw [Submodule.ker_mkQ]) ha)

@[simp] theorem quotientForward_mk (U : Submodule K V) (a : symmetricAlgebra K V) :
    quotientForward U (Ideal.Quotient.mk (generatedIdeal U) a) = map U.mkQ a := rfl

/-- A quotient vector is sent to the class of its degree-one generator.
Vanishing on U follows from ideal membership, rather than a chosen complement. -/
def quotientGenerator (U : Submodule K V) :
    (V ⧸ U) →ₗ[K] (symmetricAlgebra K V ⧸ generatedIdeal U) :=
  U.liftQ ((Ideal.Quotient.mkₐ K (generatedIdeal U)).toLinearMap.comp
    (_root_.SymmetricAlgebra.ι K V)) (by
      intro v hv
      change Ideal.Quotient.mk (generatedIdeal U) (_root_.SymmetricAlgebra.ι K V v) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨v, hv, rfl⟩))

def quotientBackward (U : Submodule K V) :
    symmetricAlgebra K (V ⧸ U) →ₐ[K] (symmetricAlgebra K V ⧸ generatedIdeal U) :=
  _root_.SymmetricAlgebra.lift (quotientGenerator U)

@[simp] theorem quotientBackward_generator (U : Submodule K V) (v : V) :
    quotientBackward U (_root_.SymmetricAlgebra.ι K (V ⧸ U) (U.mkQ v)) =
      Ideal.Quotient.mk (generatedIdeal U) (_root_.SymmetricAlgebra.ι K V v) :=
  _root_.SymmetricAlgebra.lift_ι_apply _ _

theorem quotientForward_backward (U : Submodule K V) :
    (quotientForward U).comp (quotientBackward U) =
      AlgHom.id K (symmetricAlgebra K (V ⧸ U)) := by
  apply D05.M15.Symmetric.hom_ext
  intro v
  obtain ⟨v, rfl⟩ := U.mkQ_surjective v
  change quotientForward U (quotientBackward U
    (_root_.SymmetricAlgebra.ι K (V ⧸ U) (U.mkQ v))) = _
  rw [quotientBackward_generator, quotientForward_mk, map_generator]
  rfl

theorem quotientBackward_forward (U : Submodule K V) :
    (quotientBackward U).comp (quotientForward U) =
      AlgHom.id K (symmetricAlgebra K V ⧸ generatedIdeal U) := by
  apply Ideal.Quotient.algHom_ext
  apply D05.M15.Symmetric.hom_ext
  intro v
  change quotientBackward U (quotientForward U
    (Ideal.Quotient.mk (generatedIdeal U) (_root_.SymmetricAlgebra.ι K V v))) = _
  rw [quotientForward_mk, map_generator, quotientBackward_generator]
  rfl

/-- The canonical quotient isomorphism, constructed without any basis choice. -/
def quotientEquiv (U : Submodule K V) :
    (symmetricAlgebra K V ⧸ generatedIdeal U) ≃ₐ[K] symmetricAlgebra K (V ⧸ U) :=
  AlgEquiv.ofAlgHom (quotientForward U) (quotientBackward U)
    (quotientForward_backward U) (quotientBackward_forward U)

@[simp] theorem quotientEquiv_mk (U : Submodule K V) (a : symmetricAlgebra K V) :
    quotientEquiv U (Ideal.Quotient.mk (generatedIdeal U) a) = map U.mkQ a := rfl

theorem quotient_kernel (U : Submodule K V) :
    RingHom.ker (map U.mkQ).toRingHom = generatedIdeal U := by
  apply le_antisymm
  · intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (quotientEquiv U).injective
    rw [quotientEquiv_mk, map_zero]
    exact ha
  · exact generatedIdeal_le_ker U.mkQ U (by rw [Submodule.ker_mkQ])

/-- Factorization through the vector-space quotient reduces the general
kernel calculation to the quotient case and an injective linear map. -/
theorem kernel_eq (f : V →ₗ[K] W) :
    RingHom.ker (map f).toRingHom = generatedIdeal (LinearMap.ker f) := by
  let i : (V ⧸ LinearMap.ker f) →ₗ[K] W :=
    (LinearMap.range f).subtype.comp f.quotKerEquivRange.toLinearMap
  have hi : Function.Injective i :=
    Subtype.val_injective.comp f.quotKerEquivRange.injective
  have hf : i.comp (LinearMap.ker f).mkQ = f := by
    apply LinearMap.ext
    intro v
    exact f.quotKerEquivRange_apply_mk v
  have hmap : map f = (map i).comp (map (LinearMap.ker f).mkQ) := by
    rw [← map_comp, hf]
  rw [← quotient_kernel (LinearMap.ker f)]
  ext a
  change map f a = 0 ↔ map (LinearMap.ker f).mkQ a = 0
  rw [hmap, AlgHom.comp_apply]
  exact map_eq_zero_iff (map i) (map_injective i hi)

end Quotients

theorem kernel_eq_generatedIdeal :
    Specs.D05.M15.Symmetric.KernelQuotient.kernel_eq_generatedIdeal := by
  intro K V W _ _ _ _ _ _ _ f
  exact kernel_eq f

section Images
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem range_eq_adjoin (f : V →ₗ[K] W) :
    (map f).range = Algebra.adjoin K
      ((_root_.SymmetricAlgebra.ι K W) '' (LinearMap.range f : Set W)) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change map f a ∈ Algebra.adjoin K
      ((_root_.SymmetricAlgebra.ι K W) '' (LinearMap.range f : Set W))
    induction a using _root_.SymmetricAlgebra.induction with
    | algebraMap c =>
      rw [(map f).commutes]
      exact Subalgebra.algebraMap_mem _ c
    | ι v =>
      rw [map_generator]
      exact Algebra.subset_adjoin ⟨f v, ⟨v, rfl⟩, rfl⟩
    | mul a b ha hb =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ ha hb
    | add a b ha hb =>
      rw [map_add]
      exact Subalgebra.add_mem _ ha hb
  · apply Algebra.adjoin_le
    rintro _ ⟨w, ⟨v, rfl⟩, rfl⟩
    exact ⟨_root_.SymmetricAlgebra.ι K V v, map_generator f v⟩

theorem range_eq_subspace (f : V →ₗ[K] W) :
    (map f).range = (map (LinearMap.range f).subtype).range := by
  have hf : (LinearMap.range f).subtype.comp f.rangeRestrict = f := rfl
  have hs : Function.Surjective (map f.rangeRestrict) :=
    map_surjective f.rangeRestrict (by rintro ⟨w, v, rfl⟩; exact ⟨v, rfl⟩)
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨map f.rangeRestrict b, ?_⟩
    exact (DFunLike.congr_fun (map_comp f.rangeRestrict (LinearMap.range f).subtype) b).symm
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := hs b
    refine ⟨c, ?_⟩
    exact DFunLike.congr_fun (map_comp f.rangeRestrict (LinearMap.range f).subtype) c

end Images

theorem image_eq_adjoin : Specs.D05.M15.Symmetric.KernelQuotient.image_eq_adjoin := by
  intro K V W _ _ _ _ _ _ _ f
  exact range_eq_adjoin f

theorem image_eq_subspace : Specs.D05.M15.Symmetric.KernelQuotient.image_eq_subspace := by
  intro K V W _ _ _ _ _ _ _ f
  exact ⟨map_injective (LinearMap.range f).subtype Subtype.val_injective, range_eq_subspace f⟩

theorem quotient_equiv : Specs.D05.M15.Symmetric.KernelQuotient.quotient_equiv := by
  intro K V _ _ _ _ U
  refine ⟨quotientEquiv U, ⟨quotientEquiv_mk U, ?_⟩, ?_⟩
  · intro p
    rw [← Submodule.map_comp]
    have h : (quotientEquiv U).toLinearMap.comp
        (Ideal.Quotient.mkₐ K (generatedIdeal U)).toLinearMap = (map U.mkQ).toLinearMap := by
      apply LinearMap.ext
      intro a
      exact quotientEquiv_mk U a
    rw [h]
    exact homogeneous_range U.mkQ U.mkQ_surjective p
  · intro E hE
    apply AlgEquiv.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact (hE.1 a).trans (quotientEquiv_mk U a).symm

end D05.M15.Symmetric.KernelQuotient
