import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalDepth
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FiberRegularLifting
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import Mathlib.RingTheory.Flat.Equalizer

/-! Depth in a flat local family (CM-10).

We use chapter 6 regular-sequence depth throughout. Its finite-value and
one-element reduction interfaces are obtained from maximal regular sequences.
At depth zero a residue-field injection tensors to an S-linear injection of
the closed fiber. Base regular elements stay regular by flatness of N;
fiber regular elements lift with flat cokernel, so they stay regular after
tensoring with any M. The two quotient-tensor equivalences preserve the
S-action. Induction on the two natural-valued depths proves the equality.
Finally, surjective scalar change identifies fiber depth over S with depth
over S/mS, and tensor commutation restores the source's order of factors.
-/
universe u
open scoped TensorProduct Pointwise
open RingTheory.Sequence TensorProduct
noncomputable section
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AdvCommAlg.CohenMacaulay
namespace FlatLocalDepth

open AdvCommAlg.Depth

lemma depth_eq_of_linearEquiv {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M U : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup U] [Module R U] [Module.Finite R M] [Module.Finite R U]
    (e : M ≃ₗ[R] U) : depth R M = depth R U := by
  rw [depth_eq_libraryDepth (ModuleCat.of R M), depth_eq_libraryDepth (ModuleCat.of R U)]
  exact IsLocalRing.depth_eq_of_linearEquiv e

lemma exists_depth_eq_nat (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] : ∃ n : ℕ, depth R M = n := by
  have hI : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  obtain ⟨xs, hx⟩ := exists_maximalRegular_extension (IsLocalRing.maximalIdeal R)
    M hI [] (IsRegular.nil R M) (by simp)
  exact ⟨xs.length, (maximalRegular_length_eq_grade _ M hI xs (by simpa using hx)).symm⟩

lemma depth_quotSMulTop_add_one (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    depth R (QuotSMulTop x M) + 1 = depth R M := by
  let I := IsLocalRing.maximalIdeal R
  have hI : I • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  letI := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  have hs : IsRegular M [x] := (isRegular_cons_iff M x []).mpr
    ⟨hreg, IsRegular.nil R _⟩
  obtain ⟨ys, hys⟩ := exists_maximalRegular_extension I M hI [x] hs (by change ∀ a ∈ [x], a ∈ IsLocalRing.maximalIdeal R; simpa only [List.mem_singleton, forall_eq] using hx)
  have hys' : MaximalRegular I M (x :: ys) := by simpa using hys
  have hqI := ideal_smul_quotSMulTop_ne_top I M x hx hI
  have hmax : MaximalRegular I (QuotSMulTop x M) ys := by
    refine ⟨((isRegular_cons_iff M x ys).mp hys'.1).2,
      fun a ha => hys'.2.1 a (by simp [ha]), ?_⟩
    intro a ha hbad
    exact hys'.2.2 a ha ((isRegular_cons_iff M x (ys ++ [a])).mpr ⟨hreg, hbad⟩)
  have hM := maximalRegular_length_eq_grade I M hI (x :: ys) hys'
  have hQ := maximalRegular_length_eq_grade I (QuotSMulTop x M) hqI ys hmax
  change grade I _ + 1 = grade I M
  rw [← hM, ← hQ]
  simp

/-- A nonzero socle element gives the residue-field injection used in CM-10. -/
lemma exists_residueField_injection (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : depth R M = 0) :
    ∃ f : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] M, Function.Injective f := by
  have hs := (depth_zero_iff_socle_ne_bot R M).mp hM
  obtain ⟨x, hx, hxn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  have hxkill : ∀ r ∈ IsLocalRing.maximalIdeal R, r • x = 0 := by
    intro r hr
    exact (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨r, hr⟩
  let f : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] M :=
    (IsLocalRing.maximalIdeal R).liftQ (LinearMap.toSpanSingleton R M x)
      (fun r hr => hxkill r hr)
  letI : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal R))
  refine ⟨f, LinearMap.injective_of_ne_zero ?_⟩
  intro hf
  have hh := LinearMap.congr_fun hf (1 : R ⧸ IsLocalRing.maximalIdeal R)
  change (1 : R) • x = 0 at hh
  exact hxn (by simpa using hh)

/-- A nonzero finite submodule of depth zero forces depth zero in the ambient module. -/
lemma depth_zero_of_injective {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {U V : Type u} [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] [Module.Finite R U] [Nontrivial U]
    [Module.Finite R V] [Nontrivial V] (f : U →ₗ[R] V)
    (hf : Function.Injective f) (hU : depth R U = 0) : depth R V = 0 := by
  have hI (X : Type u) [AddCommGroup X] [Module R X] [Module.Finite R X]
      [Nontrivial X] : IsLocalRing.maximalIdeal R • (⊤ : Submodule R X) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  apply (grade_zero_iff_no_regular _ V (hI V)).mpr
  intro a ha hreg
  exact (grade_zero_iff_no_regular _ U (hI U)).mp hU a ha (hreg.of_injective f hf)

lemma exists_regular_of_depth_ne_zero (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : depth R M ≠ 0) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular M x := by
  classical
  by_contra h
  apply hM
  apply (grade_zero_iff_no_regular _ M _).mpr
  · simpa only [not_exists, not_and] using h
  · exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm

/-- Depth is unchanged by a surjective local change of scalar ring. -/
lemma depth_of_surjective (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [IsLocalRing R] [IsLocalRing A]
    (hf : Function.Surjective (algebraMap R A))
    (U : Type u) [AddCommGroup U] [Module R U] [Module A U] [IsScalarTower R A U] :
    depth A U = depth R U := by
  unfold depth
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R A) hf]
  exact grade_map_of_surjective U hf _

section TensorQuotients
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (N M : Type u) [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] [AddCommGroup M] [Module R M]

/-- The quotient-tensor equivalence retains the action on the first factor. -/
def quotientTensorLeftEquiv (p : Submodule S N) :
    (N ⧸ p) ⊗[R] M ≃ₗ[S]
      (N ⊗[R] M) ⧸ LinearMap.range (AlgebraTensorModule.rTensor R M p.subtype) where
  __ := TensorProduct.quotientTensorEquiv M (p.restrictScalars R)
  map_smul' s z := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      RingHom.id_apply]
    induction z with
    | add z w hz hw => simp only [smul_add, map_add, hz, hw]
    | tmul n m =>
      obtain ⟨n, rfl⟩ := p.mkQ_surjective n
      rw [smul_tmul']
      rfl

lemma range_lsmul_eq (A : Type u) [CommRing A] (X : Type u)
    [AddCommGroup X] [Module A X] (a : A) :
    (LinearMap.lsmul A X a).range = a • (⊤ : Submodule A X) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

/-- Quotienting the finite base module commutes with the tensor, over S. -/
def base_tensor_quotSMulEquiv (x : R) :
    N ⊗[R] QuotSMulTop x M ≃ₗ[S] QuotSMulTop (algebraMap R S x) (N ⊗[R] M) := by
  refine AlgebraTensorModule.tensorQuotientEquiv S R N (x • (⊤ : Submodule R M)) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ ?_
  apply Submodule.restrictScalars_injective R
  change (LinearMap.lTensor N (x • (⊤ : Submodule R M)).subtype).range = _
  rw [← range_lsmul_eq R M x, ← LinearMap.lTensor_range]
  have he : (LinearMap.lsmul R M x).lTensor N =
      (LinearMap.lsmul S (N ⊗[R] M) (algebraMap R S x)).restrictScalars R := by
    ext n m
    simp
  rw [he, LinearMap.range_restrictScalars, range_lsmul_eq]

/-- Quotienting the S-module factor commutes with tensoring over R. -/
def fiber_tensor_quotSMulEquiv (y : S) :
    (QuotSMulTop y N) ⊗[R] M ≃ₗ[S] QuotSMulTop y (N ⊗[R] M) := by
  refine quotientTensorLeftEquiv N M (y • ⊤) ≪≫ₗ Submodule.quotEquivOfEq _ _ ?_
  apply Submodule.restrictScalars_injective R
  change ((y • (⊤ : Submodule S N)).subtype.restrictScalars R |>.rTensor M).range = _
  have hr : ((LinearMap.lsmul S N y).restrictScalars R).range =
      (y • (⊤ : Submodule S N)).restrictScalars R := by
    rw [LinearMap.range_restrictScalars, range_lsmul_eq]
  change (LinearMap.rTensor M ((y • (⊤ : Submodule S N)).restrictScalars R).subtype).range = _
  rw [← hr, ← LinearMap.rTensor_range]
  have he : ((LinearMap.lsmul S N y).restrictScalars R).rTensor M =
      (LinearMap.lsmul S (N ⊗[R] M) y).restrictScalars R := by
    ext n m
    rfl
  rw [he, LinearMap.range_restrictScalars, range_lsmul_eq]

/-- Tensoring with R/I gives the S-module quotient by the extended ideal. -/
def tensorIdealQuotEquiv (I : Ideal R) :
    N ⊗[R] (R ⧸ I) ≃ₗ[S]
      N ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S N)) := by
  let p : Submodule S N := I.map (algebraMap R S) • ⊤
  let e : N ⊗[R] (R ⧸ I) ≃ₗ[R] N ⧸ p :=
    TensorProduct.tensorQuotEquivQuotSMul N I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by
        rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv R p
  refine { __ := e.toAddEquiv, map_smul' := ?_ }
  intro s z
  change e (s • z) = s • e z
  induction z with
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]
  | tmul n k =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective k
    simp only [smul_tmul', e, LinearEquiv.trans_apply,
      TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
      Submodule.quotEquivOfEq_mk, Submodule.Quotient.restrictScalarsEquiv_mk]
    rw [smul_comm, Submodule.Quotient.mk_smul]

/-- A fiber regular element is regular on the tensor even if M is not flat. -/
lemma fiber_regular_tensor (y : S) (hy : IsSMulRegular N y)
    [Module.Flat R (QuotSMulTop y N)] : IsSMulRegular (N ⊗[R] M) y := by
  let f := (LinearMap.lsmul S N y).restrictScalars R
  let p := (y • (⊤ : Submodule S N)).mkQ.restrictScalars R
  have he : Function.Exact f p := by
    intro n
    change Submodule.Quotient.mk n = 0 ↔ ∃ b : N, y • b = n
    rw [Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat p
    (Submodule.mkQ_surjective _) f hy he M
  have hi := (f.lTensor_inj_iff_rTensor_inj M).mp hinj
  have heq : f.rTensor M = (LinearMap.lsmul S (N ⊗[R] M) y).restrictScalars R := by
    ext n m
    rfl
  rw [heq] at hi
  exact hi

end TensorQuotients

section LocalDepth
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]
variable (M N : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
  [Module.Flat R N]

/-- The simultaneous depth-zero case of the flat local depth formula. -/
lemma tensor_depth_zero
    (hM : Depth.depth R M = 0)
    (hF : Depth.depth S (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) = 0) :
    Depth.depth S (N ⊗[R] M) = 0 := by
  letI : Module.Finite S (N ⊗[R] M) := tensor_finite_left R S M N
  letI : Module.FaithfullyFlat R N := faithfullyFlat_of_flatLocal R S N
  letI : Nontrivial (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) :=
    closedFiber_nontrivial R S N
  obtain ⟨f, hf⟩ := exists_residueField_injection R M hM
  let e := tensorIdealQuotEquiv (S := S) N (IsLocalRing.maximalIdeal R)
  let g := (AlgebraTensorModule.lTensor S N f).comp e.symm.toLinearMap
  have hg : Function.Injective g :=
    (Module.Flat.lTensor_preserves_injective_linearMap (M := N) f hf).comp e.symm.injective
  exact depth_zero_of_injective g hg hF

/-- Induction on the two finite depths. Fiber steps use a flat cokernel,
while base steps use flatness of N itself. -/
lemma tensor_depth_eq_nat (a b : ℕ)
    (hM : Depth.depth R M = a)
    (hF : Depth.depth S (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) = b) :
    Depth.depth S (N ⊗[R] M) = (a + b : ℕ) := by
  induction a generalizing M N b with
  | zero =>
    induction b generalizing N with
    | zero =>
      simpa using tensor_depth_zero R S M N hM hF
    | succ b ih =>
      let F := _root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N
      letI : Nontrivial F := closedFiber_nontrivial R S N
      obtain ⟨y, hym, hy⟩ := exists_regular_of_depth_ne_zero S F
        (by rw [hF]; simp)
      obtain ⟨hyN, hflat, hnonzero⟩ := fiberRegularLifting R S N y hym hy
      letI := hflat
      letI := hnonzero
      have hqF : Depth.depth S
          (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S (QuotSMulTop y N)) = b := by
        have hh := depth_quotSMulTop_add_one S F y hym hy
        rw [← depth_eq_of_linearEquiv (fiber_quotSMulEquiv N y), hF] at hh
        apply ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
        simpa only [Nat.cast_add, Nat.cast_one] using hh
      have hind := ih (QuotSMulTop y N) hqF
      letI : Module.FaithfullyFlat R N := faithfullyFlat_of_flatLocal R S N
      letI : Module.Finite S (N ⊗[R] M) := tensor_finite_left R S M N
      letI : Module.Finite S ((QuotSMulTop y N) ⊗[R] M) :=
        tensor_finite_left R S M (QuotSMulTop y N)
      have hyT := fiber_regular_tensor (R := R) (S := S) N M y hyN
      have hh := depth_quotSMulTop_add_one S (N ⊗[R] M) y hym hyT
      rw [← depth_eq_of_linearEquiv (fiber_tensor_quotSMulEquiv N M y), hind] at hh
      simpa using hh.symm
  | succ a ih =>
    obtain ⟨x, hxm, hx⟩ := exists_regular_of_depth_ne_zero R M
      (by rw [hM]; simp)
    letI := nontrivial_quotSMulTop_of_mem_maximalIdeal M hxm
    have hqM : Depth.depth R (QuotSMulTop x M) = a := by
      have hh := depth_quotSMulTop_add_one R M x hxm hx
      rw [hM] at hh
      apply ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
      simpa only [Nat.cast_add, Nat.cast_one] using hh
    have hind := ih (QuotSMulTop x M) N b hqM hF
    letI : Module.FaithfullyFlat R N := faithfullyFlat_of_flatLocal R S N
    letI : Module.Finite S (N ⊗[R] M) := tensor_finite_left R S M N
    letI : Module.Finite S (N ⊗[R] QuotSMulTop x M) :=
      tensor_finite_left R S (QuotSMulTop x M) N
    have hxS : algebraMap R S x ∈ IsLocalRing.maximalIdeal S :=
      IsLocalRing.map_maximalIdeal_le (algebraMap R S) (Ideal.mem_map_of_mem _ hxm)
    have hxT : IsSMulRegular (N ⊗[R] M) (algebraMap R S x) := by
      have hr := hx.lTensor N
      simpa only [IsSMulRegular, algebraMap_smul] using hr
    have hh := depth_quotSMulTop_add_one S (N ⊗[R] M) (algebraMap R S x) hxS hxT
    rw [← depth_eq_of_linearEquiv (base_tensor_quotSMulEquiv N M x), hind] at hh
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hh.symm

/-- The formula first expressed with the closed fiber as an S-module. -/
lemma tensor_depth_eq_left :
    Depth.depth S (N ⊗[R] M) = Depth.depth R M +
      Depth.depth S (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) := by
  letI := closedFiber_nontrivial R S N
  obtain ⟨a, ha⟩ := exists_depth_eq_nat R M
  obtain ⟨b, hb⟩ := exists_depth_eq_nat S
    (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)
  rw [ha, hb]
  simpa only [Nat.cast_add] using tensor_depth_eq_nat R S M N a b ha hb

end LocalDepth
end FlatLocalDepth

open FlatLocalDepth in
/-- CM-10: depth of the source tensor equals base depth plus closed-fiber depth. -/
theorem flatLocal_tensor_depth : Specs.flatLocal_tensor_depthType.{u} := by
  intro R S _ _ _ _ _ _ _ _ M N _ _ _ _ _ _
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  intro _ _ _ _ _
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := Specs.closedFiberLocalRing R S
  let F := N ⧸ (J • (⊤ : Submodule S N))
  letI : Module.Finite S (N ⊗[R] M) := tensor_finite_left R S M N
  letI : Module.Finite S (M ⊗[R] N) := tensor_finite R S M N
  change Depth.depth S (M ⊗[R] N) = Depth.depth R M + Depth.depth (S ⧸ J) F
  calc
    Depth.depth S (M ⊗[R] N) = Depth.depth S (N ⊗[R] M) :=
      depth_eq_of_linearEquiv (RegularSequence.rightTensorComm (S := S) M N)
    _ = Depth.depth R M + Depth.depth S F := tensor_depth_eq_left R S M N
    _ = Depth.depth R M + Depth.depth (S ⧸ J) F := by
      rw [depth_of_surjective S (S ⧸ J) Ideal.Quotient.mk_surjective F]

end AdvCommAlg.CohenMacaulay
