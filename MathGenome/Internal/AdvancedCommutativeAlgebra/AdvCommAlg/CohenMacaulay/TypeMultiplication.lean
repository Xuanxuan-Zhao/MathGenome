import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalDepth
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Type
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.TypeMultiplication
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! Type in a flat local family (CM-18). -/
universe u
open scoped TensorProduct Pointwise
open TensorProduct RingTheory.Sequence
noncomputable section
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
namespace AdvCommAlg.CohenMacaulay
namespace TypeMultiplication
open AdvCommAlg.Depth

/-- A linear equivalence identifies maximal-ideal annihilators, with their
canonical residue-field actions. -/
def socleEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {U V : Type u} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] V) : Socle R U ≃ₗ[IsLocalRing.ResidueField R] Socle R V := by
  apply residueLinearEquiv R
  exact {
    toFun := fun x => ⟨e x, (Submodule.mem_torsionBySet_iff _ _).mpr (by
      intro a
      rw [← e.map_smul, (Submodule.mem_torsionBySet_iff _ _).mp x.property a, e.map_zero])⟩
    invFun := fun y => ⟨e.symm y, (Submodule.mem_torsionBySet_iff _ _).mpr (by
      intro a
      rw [← e.symm.map_smul, (Submodule.mem_torsionBySet_iff _ _).mp y.property a,
        e.symm.map_zero])⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
    right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val)
    map_add' := fun x y => Subtype.ext (e.map_add x.val y.val)
    map_smul' := fun r x => Subtype.ext (e.map_smul r x.val) }

/-- Type at depth zero is the dimension of the original socle. -/
lemma moduleType_eq_socle_of_depth_zero (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (U : Type u) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Nontrivial U] (hU : depth R U = 0) :
    moduleType R (ModuleCat.of R U) =
      Module.finrank (IsLocalRing.ResidueField R) (Socle R U) := by
  have hm : MaximalRegular (IsLocalRing.maximalIdeal R) U [] := by
    refine ⟨IsRegular.nil R U, by simp, ?_⟩
    intro a ha hreg
    have hn := (grade_zero_iff_no_regular _ U (maximalIdeal_smul_ne_top R
      (ModuleCat.of R U))).mp hU a ha
    exact hn ((isRegular_cons_iff U a []).mp hreg).1
  rw [moduleType_eq_socle R (ModuleCat.of R U) [] hm]
  exact (socleEquiv (FirstSurvivingExt.nilQuotientEquiv (ModuleCat.of R U))).finrank_eq

/-- Type is invariant under a linear equivalence over the same local ring. -/
lemma moduleType_eq_of_linearEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {U V : Type u} [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] [Module.Finite R U] [Module.Finite R V]
    [Nontrivial U] [Nontrivial V] (e : U ≃ₗ[R] V) :
    moduleType R (ModuleCat.of R U) = moduleType R (ModuleCat.of R V) := by
  obtain ⟨xs, hxs⟩ := exists_maximalRegular R (ModuleCat.of R U)
  have hys : MaximalRegular (IsLocalRing.maximalIdeal R) V xs :=
    ⟨(e.isRegular_congr xs).mp hxs.1, hxs.2.1,
      fun a ha hreg => hxs.2.2 a ha ((e.isRegular_congr _).mpr hreg)⟩
  rw [moduleType_eq_socle R (ModuleCat.of R U) xs hxs,
    moduleType_eq_socle R (ModuleCat.of R V) xs hys]
  let eq : FirstSurvivingExt.Quotient (ModuleCat.of R U) xs ≃ₗ[R]
      FirstSurvivingExt.Quotient (ModuleCat.of R V) xs :=
    Submodule.Quotient.equiv _ _ e (by
      rw [Submodule.map_smul'', Submodule.map_top, e.range])
  exact (socleEquiv eq).finrank_eq

/-- Removing a regular element in the maximal ideal preserves type. -/
lemma moduleType_quotSMulTop (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (U : Type u) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Nontrivial U] (a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular U a) :
    moduleType R (ModuleCat.of R (QuotSMulTop a U)) = moduleType R (ModuleCat.of R U) := by
  letI := nontrivial_quotSMulTop_of_mem_maximalIdeal U ha
  obtain ⟨xs, hxs⟩ := exists_maximalRegular R (ModuleCat.of R (QuotSMulTop a U))
  have hcons : MaximalRegular (IsLocalRing.maximalIdeal R) U (a :: xs) := by
    refine ⟨(isRegular_cons_iff U a xs).mpr ⟨hreg, hxs.1⟩, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hxs.2.1 b hb
    · intro b hb hh
      exact hxs.2.2 b hb ((isRegular_cons_iff U a (xs ++ [b])).mp hh).2
  rw [moduleType_eq_socle R (ModuleCat.of R (QuotSMulTop a U)) xs hxs,
    moduleType_eq_socle R (ModuleCat.of R U) (a :: xs) hcons]
  exact (socleEquiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner U a xs)).symm.finrank_eq

/-- An injective linear map whose image contains the socle identifies socles. -/
def socleEquivOfInjective {A : Type u} [CommRing A] [IsLocalRing A]
    {U V : Type u} [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    (f : U →ₗ[A] V) (hf : Function.Injective f)
    (hs : ∀ z : Socle A V, z.val ∈ f.range) :
    Socle A U ≃ₗ[IsLocalRing.ResidueField A] Socle A V := by
  let g : Socle A U →ₗ[A] Socle A V :=
    { toFun := fun x => ⟨f x, (Submodule.mem_torsionBySet_iff _ _).mpr (by
        intro a
        rw [← f.map_smul, (Submodule.mem_torsionBySet_iff _ _).mp x.property a,
          f.map_zero])⟩
      map_add' := fun x y => Subtype.ext (f.map_add _ _)
      map_smul' := fun a x => Subtype.ext (f.map_smul _ _) }
  apply residueLinearEquiv A
  apply LinearEquiv.ofBijective g
  constructor
  · intro x y h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  · intro z
    obtain ⟨x, hx⟩ := hs z
    have hxS : x ∈ Socle A U := (Submodule.mem_torsionBySet_iff _ _).mpr (by
      intro a
      apply hf
      rw [f.map_smul, hx, f.map_zero]
      exact (Submodule.mem_torsionBySet_iff _ _).mp z.property a)
    exact ⟨⟨x, hxS⟩, Subtype.ext hx⟩

/-- Flatness tensors the kernel of simultaneous multiplication by generators
of the maximal ideal. This is the kernel argument in paper.tex:3935–3943. -/
lemma mem_range_tensor_socle (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N] (z : N ⊗[R] M)
    (hz : ∀ a ∈ IsLocalRing.maximalIdeal R, a • z = 0) :
    z ∈ (AlgebraTensorModule.lTensor S N (Socle R M).subtype).range := by
  classical
  obtain ⟨n, as, has⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R))
  let f : M →ₗ[R] (Fin n → M) := LinearMap.pi (fun i => LinearMap.lsmul R M (as i))
  have hf : f.ker = Socle R M := by
    ext m
    simp only [LinearMap.mem_ker, f, LinearMap.pi_apply, LinearMap.lsmul_apply,
      funext_iff, Pi.zero_apply]
    constructor
    · intro hm
      apply (Submodule.mem_torsionBySet_iff _ _).mpr
      have hh : IsLocalRing.maximalIdeal R ≤ (LinearMap.toSpanSingleton R M m).ker := by
        rw [← has]
        apply Submodule.span_le.mpr
        rintro a ⟨i, rfl⟩
        exact hm i
      intro a
      exact hh a.property
    · intro hm i
      exact (Submodule.mem_torsionBySet_iff _ _).mp hm
        ⟨as i, has ▸ Submodule.subset_span ⟨i, rfl⟩⟩
  rw [← hf, ← Module.Flat.ker_lTensor_eq]
  apply (piRight R S N (fun _ : Fin n => M)).injective
  have hc : (piRight R S N (fun _ : Fin n => M)).toLinearMap.comp
      (AlgebraTensorModule.lTensor S N f) =
      LinearMap.pi (fun i => LinearMap.lsmul S (N ⊗[R] M) (algebraMap R S (as i))) := by
    ext n m i
    simp [f, tmul_smul]
  change (piRight R S N (fun _ : Fin n => M))
    (AlgebraTensorModule.lTensor S N f z) = _
  rw [map_zero]
  change ((piRight R S N (fun _ : Fin n => M)).toLinearMap.comp
    (AlgebraTensorModule.lTensor S N f)) z = 0
  rw [hc]
  ext i
  simpa only [LinearMap.pi_apply, LinearMap.lsmul_apply, algebraMap_smul, Pi.zero_apply] using
    hz (as i) (has ▸ Submodule.subset_span ⟨i, rfl⟩)

/-- Socles commute with finite products, by the coordinatewise action. -/
def soclePiEquiv (A : Type u) [CommRing A] [IsLocalRing A]
    (ι : Type) (U : Type u) [AddCommGroup U] [Module A U] :
    Socle A (ι → U) ≃ₗ[IsLocalRing.ResidueField A] (ι → Socle A U) := by
  apply residueLinearEquiv A
  refine {
    toFun := fun x i => ⟨x.val i, (Submodule.mem_torsionBySet_iff _ _).mpr (by
      intro a
      exact congrFun ((Submodule.mem_torsionBySet_iff _ _).mp x.property a) i)⟩
    invFun := fun x => ⟨fun i => (x i).val, (Submodule.mem_torsionBySet_iff _ _).mpr (by
      intro a
      funext i
      exact (Submodule.mem_torsionBySet_iff _ _).mp (x i).property a)⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl }

/-- A basis of the base socle gives a product of copies of the actual closed
fiber, without identifying the two rings' residue fields. -/
def tensorSocleEquiv (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] :
    N ⊗[R] Socle R M ≃ₗ[S]
      (Fin (Module.finrank (IsLocalRing.ResidueField R) (Socle R M)) →
        _root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) := by
  letI := socle_finite R M
  let e := (Module.finBasis (IsLocalRing.ResidueField R) (Socle R M)).equivFun
  exact AlgebraTensorModule.congr (LinearEquiv.refl S N) (e.restrictScalars R) ≪≫ₗ
    piRight R S N (fun _ => IsLocalRing.ResidueField R) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => FlatLocalDepth.tensorIdealQuotEquiv
      (S := S) N (IsLocalRing.maximalIdeal R))

/-- The socle dimension formula is valid even before imposing depth zero. -/
lemma socle_finrank_tensor (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N] :
    Module.finrank (IsLocalRing.ResidueField S) (Socle S (N ⊗[R] M)) =
      Module.finrank (IsLocalRing.ResidueField R) (Socle R M) *
      Module.finrank (IsLocalRing.ResidueField S)
        (Socle S (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)) := by
  let f := AlgebraTensorModule.lTensor S N (Socle R M).subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Socle R M).injective_subtype
  have hs (z : Socle S (N ⊗[R] M)) : z.val ∈ f.range := by
    apply mem_range_tensor_socle R S M N
    intro a ha
    rw [← algebraMap_smul S a]
    exact (Submodule.mem_torsionBySet_iff _ _).mp z.property
      ⟨algebraMap R S a, IsLocalRing.map_maximalIdeal_le (algebraMap R S)
        (Ideal.mem_map_of_mem _ ha)⟩
  let e := (socleEquivOfInjective f hf hs).symm ≪≫ₗ
    socleEquiv (tensorSocleEquiv R S M N) ≪≫ₗ
    soclePiEquiv S (Fin (Module.finrank (IsLocalRing.ResidueField R) (Socle R M)))
      (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)
  rw [e.finrank_eq]
  haveI := socle_finite S (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)
  simp [Module.finrank_pi_fintype]

/-- Surjective local scalar change identifies socle dimensions over the
canonically isomorphic residue fields. -/
lemma socle_finrank_of_surjective (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [IsLocalRing R] [IsLocalRing A]
    (hf : Function.Surjective (algebraMap R A))
    (U : Type u) [AddCommGroup U] [Module R U] [Module A U] [IsScalarTower R A U] :
    Module.finrank (IsLocalRing.ResidueField R) (Socle R U) =
      Module.finrank (IsLocalRing.ResidueField A) (Socle A U) := by
  letI := IsLocalHom.of_surjective (algebraMap R A) hf
  have hmem (x : U) : x ∈ Socle R U ↔ x ∈ Socle A U := by
    simp only [Submodule.mem_torsionBySet_iff]
    constructor
    · intro hx a
      have ha : a.val ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
        rw [IsLocalRing.map_maximalIdeal_of_surjective _ hf]
        exact a.property
      obtain ⟨r, hr, he⟩ := (Ideal.mem_map_iff_of_surjective _ hf).mp ha
      rw [← he, algebraMap_smul]
      exact hx ⟨r, hr⟩
    · intro hx r
      have ha := IsLocalRing.map_maximalIdeal_le (algebraMap R A)
        (Ideal.mem_map_of_mem _ r.property)
      simpa only [algebraMap_smul] using hx ⟨algebraMap R A r.val, ha⟩
  let e : Socle R U ≃+ Socle A U :=
    { toFun := fun x => ⟨x.val, (hmem x.val).mp x.property⟩
      invFun := fun x => ⟨x.val, (hmem x.val).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hb : Function.Bijective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)) := by
    refine ⟨RingHom.injective _, ?_⟩
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) z
    obtain ⟨r, rfl⟩ := hf a
    exact ⟨IsLocalRing.residue R r, rfl⟩
  have hd := rank_eq_of_equiv_equiv
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)) e hb (by
      intro a x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
      apply Subtype.ext
      change r • x.val = algebraMap R A r • x.val
      rw [algebraMap_smul])
  exact congrArg Cardinal.toNat hd

/-- Changing to a surjective local scalar ring preserves the shared type.
This uses maximal regular quotients and socles, not Ext base change. -/
lemma moduleType_of_surjective (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [IsNoetherianRing R] [IsNoetherianRing A]
    [IsLocalRing R] [IsLocalRing A]
    (hf : Function.Surjective (algebraMap R A))
    (U : Type u) [AddCommGroup U] [Module R U] [Module A U] [IsScalarTower R A U]
    [Module.Finite R U] [Module.Finite A U] [Nontrivial U] :
    moduleType A (ModuleCat.of A U) = moduleType R (ModuleCat.of R U) := by
  letI := IsLocalHom.of_surjective (algebraMap R A) hf
  obtain ⟨xs, hxs⟩ := exists_maximalRegular R (ModuleCat.of R U)
  have hys : MaximalRegular (IsLocalRing.maximalIdeal A) U
      (xs.map (algebraMap R A)) := by
    refine ⟨(regular_map_algebraMap_iff (S := A) U xs).mpr hxs.1, ?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact IsLocalRing.map_maximalIdeal_le (algebraMap R A)
        (Ideal.mem_map_of_mem _ (hxs.2.1 a ha))
    · intro b hb hbad
      have hb' : b ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
        rw [IsLocalRing.map_maximalIdeal_of_surjective _ hf]
        exact hb
      obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hf).mp hb'
      apply hxs.2.2 a ha
      apply (regular_map_algebraMap_iff (S := A) U (xs ++ [a])).mp
      simpa using hbad
  rw [moduleType_eq_socle A (ModuleCat.of A U) _ hys,
    moduleType_eq_socle R (ModuleCat.of R U) xs hxs]
  let p : Submodule A U := Ideal.ofList (xs.map (algebraMap R A)) • ⊤
  have hp : p.restrictScalars R = Ideal.ofList xs • (⊤ : Submodule R U) := by
    dsimp [p]
    rw [← Ideal.map_ofList, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  let eq : FirstSurvivingExt.Quotient (ModuleCat.of R U) xs ≃ₗ[R] (U ⧸ p) :=
    Submodule.quotEquivOfEq _ _ hp.symm ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R p
  exact (socle_finrank_of_surjective R A hf (U ⧸ p)).symm.trans
    (socleEquiv eq).symm.finrank_eq

section Local
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]
variable (M N : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
  [Module.Flat R N]

open FlatLocalDepth

/-- Successively remove base and fiber regular elements. Each removal
preserves all three types, while lowering one of the two finite depths. -/
lemma tensor_type_eq_nat (a b : ℕ)
    (hM : depth R M = a)
    (hF : depth S (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) = b) :
    moduleType S (ModuleCat.of S (N ⊗[R] M)) =
      moduleType R (ModuleCat.of R M) * moduleType S
        (ModuleCat.of S (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)) := by
  induction a generalizing M N b with
  | zero =>
    induction b generalizing N with
    | zero =>
      letI := closedFiber_nontrivial R S N
      letI : Module.FaithfullyFlat R N := faithfullyFlat_of_flatLocal R S N
      letI : Module.Finite S (N ⊗[R] M) := tensor_finite_left R S M N
      rw [moduleType_eq_socle_of_depth_zero S (N ⊗[R] M)
        (tensor_depth_zero R S M N hM hF),
        moduleType_eq_socle_of_depth_zero R M hM,
        moduleType_eq_socle_of_depth_zero S _ hF]
      exact socle_finrank_tensor R S M N
    | succ b ih =>
      let F := _root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N
      letI : Nontrivial F := closedFiber_nontrivial R S N
      obtain ⟨y, hym, hy⟩ := exists_regular_of_depth_ne_zero S F (by rw [hF]; simp)
      obtain ⟨hyN, hflat, hnonzero⟩ := fiberRegularLifting R S N y hym hy
      letI := hflat
      letI := hnonzero
      letI : Module.FaithfullyFlat R (QuotSMulTop y N) :=
        faithfullyFlat_of_flatLocal R S (QuotSMulTop y N)
      have hqF : depth S
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
      letI : Nontrivial (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S
        (QuotSMulTop y N)) := closedFiber_nontrivial R S (QuotSMulTop y N)
      letI := nontrivial_quotSMulTop_of_mem_maximalIdeal F hym
      have hyT := fiber_regular_tensor (R := R) (S := S) N M y hyN
      letI := nontrivial_quotSMulTop_of_mem_maximalIdeal (N ⊗[R] M) hym
      calc
        moduleType S (ModuleCat.of S (N ⊗[R] M)) =
            moduleType S (ModuleCat.of S (QuotSMulTop y (N ⊗[R] M))) :=
          (moduleType_quotSMulTop S _ y hym hyT).symm
        _ = moduleType S (ModuleCat.of S ((QuotSMulTop y N) ⊗[R] M)) :=
          moduleType_eq_of_linearEquiv (fiber_tensor_quotSMulEquiv N M y).symm
        _ = _ := hind
        _ = moduleType R (ModuleCat.of R M) * moduleType S (ModuleCat.of S F) := by
          rw [moduleType_eq_of_linearEquiv (fiber_quotSMulEquiv N y),
            moduleType_quotSMulTop S F y hym hy]
  | succ a ih =>
    obtain ⟨x, hxm, hx⟩ := exists_regular_of_depth_ne_zero R M (by rw [hM]; simp)
    letI := nontrivial_quotSMulTop_of_mem_maximalIdeal M hxm
    have hqM : depth R (QuotSMulTop x M) = a := by
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
    letI := nontrivial_quotSMulTop_of_mem_maximalIdeal (N ⊗[R] M) hxS
    calc
      moduleType S (ModuleCat.of S (N ⊗[R] M)) =
          moduleType S (ModuleCat.of S
            (QuotSMulTop (algebraMap R S x) (N ⊗[R] M))) :=
        (moduleType_quotSMulTop S _ (algebraMap R S x) hxS hxT).symm
      _ = moduleType S (ModuleCat.of S (N ⊗[R] QuotSMulTop x M)) :=
        moduleType_eq_of_linearEquiv (base_tensor_quotSMulEquiv N M x).symm
      _ = _ := hind
      _ = _ := by rw [moduleType_quotSMulTop R M x hxm hx]

/-- The type formula with the closed fiber regarded as an S-module. -/
lemma tensor_type_left :
    moduleType S (ModuleCat.of S (N ⊗[R] M)) =
      moduleType R (ModuleCat.of R M) * moduleType S
        (ModuleCat.of S (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)) := by
  letI := closedFiber_nontrivial R S N
  obtain ⟨a, ha⟩ := exists_depth_eq_nat R M
  obtain ⟨b, hb⟩ := exists_depth_eq_nat S
    (_root_.Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)
  exact tensor_type_eq_nat R S M N a b ha hb

end Local

end TypeMultiplication
/-- CM-18: type is multiplicative for a finite flat local family. -/
theorem flatLocal_tensor_type : Specs.flatLocal_tensor_typeType.{u} := by
  intro R S _ _ _ _ _ _ _ _ M N _ _ _ _ _ _
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  intro _ _ _ _ _
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := Specs.closedFiberLocalRing R S
  let F := N ⧸ (J • (⊤ : Submodule S N))
  letI : Module.Finite (S ⧸ J) F := Module.Finite.of_restrictScalars_finite S (S ⧸ J) F
  letI := closedFiber_nontrivial R S N
  letI := tensor_nontrivial_of_flatLocal R S N M
  letI : Nontrivial (N ⊗[R] M) := by
    letI : Module.FaithfullyFlat R N := faithfullyFlat_of_flatLocal R S N
    infer_instance
  letI : Module.Finite S (N ⊗[R] M) := tensor_finite_left R S M N
  letI : Module.Finite S (M ⊗[R] N) := tensor_finite R S M N
  change Depth.moduleType S (ModuleCat.of S (M ⊗[R] N)) =
    Depth.moduleType R (ModuleCat.of R M) * Depth.moduleType (S ⧸ J) (ModuleCat.of (S ⧸ J) F)
  rw [TypeMultiplication.moduleType_eq_of_linearEquiv
      (RegularSequence.rightTensorComm (S := S) M N),
    TypeMultiplication.tensor_type_left R S M N,
    TypeMultiplication.moduleType_of_surjective S (S ⧸ J) Ideal.Quotient.mk_surjective F]

end AdvCommAlg.CohenMacaulay
