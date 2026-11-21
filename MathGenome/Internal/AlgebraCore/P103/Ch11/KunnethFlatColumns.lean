import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethFlatColumns
import MathGenome.Internal.AlgebraCore.P103.Ch11.FlatResolutions
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorBalance

namespace P103.Ch11.KunnethFlatColumns
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.KunnethFlatColumns
open P103.Specs.Ch02.FlatnessTests
open P103.Ch11.FlatResolutions
noncomputable section
universe u v w
variable {R : Type u} [Ring R]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Flat tensoring preserves an injection, at arbitrary module sizes. -/
theorem rightFlat_tensor_injective (U : ModuleCat.{v} Rᵐᵒᵖ)
    (hU : RightFlat.{u,v,w} R U) {A B : Type w}
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Injective (tensorMap (LinearMap.id : U →ₗ[Rᵐᵒᵖ] U) f) := by
  have he : Function.Exact (0 : A →ₗ[R] A) f := by
    intro a
    change f a = 0 ↔ ∃ x : A, (0 : A) = a
    exact ⟨fun h => ⟨0, (hf (h.trans (map_zero f).symm)).symm⟩,
      by rintro ⟨x,h⟩; rw [← h, map_zero]⟩
  have ht := rightFlat_tensor_exact hU (0 : A →ₗ[R] A) f he
  have hz : tensorMap (LinearMap.id : U →ₗ[Rᵐᵒᵖ] U) (0 : A →ₗ[R] A) = 0 := by
    apply tensor_hom_ext
    intro a b
    change tmul R a 0 = 0
    simp [tmul]
  intro a b hab
  have hab' : tensorMap (LinearMap.id : U →ₗ[Rᵐᵒᵖ] U) f (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (ht (a-b)).mp hab'
  rw [hz] at hc
  exact sub_eq_zero.mp hc.symm

/-- Tensoring the inclusion of cycles, with its actual cycle codomain. -/
def tensorCycles (U : ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    Tensor R U (cycles D q) →ₗ[ℤ] cycles (leftOrdinaryTensorComplex U D) q :=
  (tensorMap (LinearMap.id : U →ₗ[Rᵐᵒᵖ] U) (cycles D q).subtype).codRestrict _ (by
    intro z
    change (tensorMap (LinearMap.id : U →ₗ[Rᵐᵒᵖ] U)
      (D.d q ((ComplexShape.down ℕ).next q)).hom)
        (tensorMap LinearMap.id (cycles D q).subtype z) = 0
    have hh : (tensorMap (LinearMap.id : U →ₗ[Rᵐᵒᵖ] U)
        (D.d q ((ComplexShape.down ℕ).next q)).hom).comp
        (tensorMap LinearMap.id (cycles D q).subtype) = 0 := by
      apply tensor_hom_ext
      intro a x
      change tmul R a ((D.d q ((ComplexShape.down ℕ).next q)).hom x.val) = 0
      rw [show (D.d q ((ComplexShape.down ℕ).next q)).hom x.val = 0 from x.property]
      simp [tmul]
    exact LinearMap.congr_fun hh z)

theorem tensorCycles_bijective (U : ModuleCat.{v} Rᵐᵒᵖ)
    (hU : RightFlat.{u,v,w} R U) (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    Function.Bijective (tensorCycles U D q) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    exact rightFlat_tensor_injective U hU (cycles D q).subtype Subtype.val_injective
      (congrArg Subtype.val h)
  · have he : Function.Exact (cycles D q).subtype
        (D.d q ((ComplexShape.down ℕ).next q)).hom := by
      intro a
      exact ⟨fun h => ⟨⟨a,h⟩,rfl⟩, by rintro ⟨x,rfl⟩; exact x.property⟩
    have ht := rightFlat_tensor_exact hU (cycles D q).subtype
      (D.d q ((ComplexShape.down ℕ).next q)).hom he
    intro z
    obtain ⟨a,ha⟩ := (ht z.val).mp z.property
    exact ⟨a, Subtype.ext ha⟩

/-- Incoming differential, as a map into the cycle submodule. -/
def incomingCycles {S : Type*} [Ring S]
    (D : ChainComplex (ModuleCat.{w} S) ℕ) (q : ℕ) :
    D.X (q+1) →ₗ[S] cycles D q :=
  (D.d (q+1) q).hom.codRestrict _ (by
    intro y
    apply boundaryInclusion D q
    change ∃ x, (D.d ((ComplexShape.down ℕ).prev q) q).hom x = _
    rw [ChainComplex.prev]
    exact ⟨y,rfl⟩)

theorem incomingCycles_exact {S : Type*} [Ring S]
    (D : ChainComplex (ModuleCat.{w} S) ℕ) (q : ℕ) :
    Function.Exact (incomingCycles D q) (homologyClass D q) := by
  intro z
  rw [P103.Ch10.HomologySequence.class_zero_iff]
  change (∃ y, (D.d ((ComplexShape.down ℕ).prev q) q).hom y = z.val) ↔ _
  rw [ChainComplex.prev]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y, Subtype.ext hy⟩
  · rintro ⟨y,rfl⟩
    exact ⟨y,rfl⟩

def tensorCycleClass (U : ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    Tensor R U (cycles D q) →ₗ[ℤ] Homology (leftOrdinaryTensorComplex U D) q :=
  (homologyClass _ q).comp (tensorCycles U D q)

abbrev tensorHomologyQuotient (U : ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :=
  tensorMap (LinearMap.id : U →ₗ[Rᵐᵒᵖ] U) (homologyClass D q)

theorem tensorHomologyQuotient_surjective (U : ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    Function.Surjective (tensorHomologyQuotient U D q) :=
  P103.HomTensorExactness.tensorSecond_surjective (homologyClass D q)
    (cycleBoundaries D q).mkQ_surjective
    (tensorHomologyQuotient U D q).toAddMonoidHom (by intros; rfl)

/-- The two class maps kill exactly the same tensor boundaries. -/
theorem tensorCycleClass_ker (U : ModuleCat.{v} Rᵐᵒᵖ)
    (hU : RightFlat.{u,v,w} R U) (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    LinearMap.ker (tensorCycleClass U D q) = LinearMap.ker (tensorHomologyQuotient U D q) := by
  have he := rightFlat_tensor_exact hU (incomingCycles D q) (homologyClass D q)
    (incomingCycles_exact D q)
  have hb : (tensorCycles U D q).comp
      (tensorMap (LinearMap.id : U →ₗ[Rᵐᵒᵖ] U) (incomingCycles D q)) =
      incomingCycles (leftOrdinaryTensorComplex U D) q := by
    apply tensor_hom_ext
    intro a x
    rfl
  ext z
  change tensorCycleClass U D q z = 0 ↔ tensorHomologyQuotient U D q z = 0
  rw [he z, tensorCycleClass, LinearMap.comp_apply,
    incomingCycles_exact (leftOrdinaryTensorComplex U D) q (tensorCycles U D q z)]
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨y, (tensorCycles_bijective U hU D q).1 ?_⟩
    rw [← LinearMap.comp_apply, hb]
    exact hy
  · rintro ⟨y,hy⟩
    refine ⟨y, ?_⟩
    exact (LinearMap.congr_fun hb y).symm.trans
      (congrArg (tensorCycles U D q) hy)

/-- The normalized flat-column isomorphism, obtained from two surjective
class maps with equal kernels. -/
def columnEquiv (U : ModuleCat.{v} Rᵐᵒᵖ)
    (hU : RightFlat.{u,v,w} R U) (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    Tensor R U (Homology D q) ≃ₗ[ℤ] Homology (leftOrdinaryTensorComplex U D) q :=
  (tensorHomologyQuotient U D q).quotKerEquivOfSurjective
      (tensorHomologyQuotient_surjective U D q) |>.symm.trans
    ((Submodule.quotEquivOfEq _ _ (tensorCycleClass_ker U hU D q).symm).trans
      ((tensorCycleClass U D q).quotKerEquivOfSurjective
        ((cycleBoundaries _ q).mkQ_surjective.comp (tensorCycles_bijective U hU D q).2)))

theorem columnEquiv_formula (U : ModuleCat.{v} Rᵐᵒᵖ)
    (hU : RightFlat.{u,v,w} R U) (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    ColumnFormula U D q (columnEquiv U hU D q) := by
  intro a x
  change columnEquiv U hU D q (tensorHomologyQuotient U D q (tmul R a x)) = _
  unfold columnEquiv
  simp only [LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk]
  rfl

theorem column_isomorphism : column_isomorphismType.{u,v,w} := by
  intro R _ U hU D q
  exact ⟨columnEquiv U hU D q, columnEquiv_formula U hU D q⟩

theorem column_natural : column_naturalType.{u,v,w} := by
  intro R _ U U' D D' f g q e e' he he'
  apply tensor_hom_ext
  intro a x
  obtain ⟨x,rfl⟩ := (cycleBoundaries D q).mkQ_surjective x
  change homologyMap _ q (e (tmul R a (homologyClass D q x))) =
    e' (tmul R (f.hom a) (homologyMap g q (homologyClass D q x)))
  rw [he]
  rw [P103.Ch10.Complexes.homologyMap_apply (f := g)]
  rw [he']
  rw [P103.Ch10.Complexes.homologyMap_apply]
  apply congrArg (homologyClass _ q)
  apply Subtype.ext
  rfl

/-- The argument uses units, so it also applies to torsion integer modules. -/
theorem sign_submodules : sign_submodulesType.{v} := by
  intro A B d p
  rcases Int.units_eq_one_or ((p : ℤ).negOnePow) with h | h <;>
    simp [h, Units.smul_def]


/-- Every ordinary diagonal is finite, without any rank bound on its modules. -/
instance diagonalFinite (n : ℕ) : Finite (Diagonal n) := by
  apply Finite.of_injective (fun i : Diagonal n => (⟨i.val.1, by omega⟩ : Fin (n+1)))
  intro i j hij
  have hij' : i.val.1 = j.val.1 := congrArg (fun t : Fin (n+1) => t.val) hij
  apply Subtype.ext
  apply Prod.ext
  · exact hij'
  · have h := hij'
    have hi := i.property
    have hj := j.property
    omega

noncomputable instance diagonalFintype (n : ℕ) : Fintype (Diagonal n) := Fintype.ofFinite _

/-- Reconstruction on the ordinary nonnegative diagonal. -/
theorem ordinary_reconstruction
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (z : (ordinaryTotal C D).X n) :
    ∑ i : Diagonal n, ordinaryInclusion C D i.val.1 i.val.2 n i.property
      (ordinaryProjection C D i.val.1 i.val.2 n i.property z) = z := by
  classical
  let F : (ordinaryTotal C D).X n →ₗ[ℤ] (ordinaryTotal C D).X n :=
    ∑ i : Diagonal n, (ordinaryInclusion C D i.val.1 i.val.2 n i.property).comp
      (ordinaryProjection C D i.val.1 i.val.2 n i.property)
  have hF : F = LinearMap.id := by
    suffices hh : ModuleCat.ofHom F =
        ModuleCat.ofHom (LinearMap.id : (ordinaryTotal C D).X n →ₗ[ℤ] (ordinaryTotal C D).X n)
        from congrArg ModuleCat.Hom.hom hh
    apply P103.Ch11.TorBalance.ordinaryTotal_hom_ext C D n
    intro p q hpq a b
    change F (ordinaryInclusion C D p q n hpq (tmul R a b)) = _
    dsimp only [F]
    rw [LinearMap.sum_apply]
    rw [Finset.sum_eq_single (⟨(p,q),hpq⟩ : Diagonal n)]
    · simp only [LinearMap.comp_apply, ordinaryProjection_inclusion]
      rfl
    · intro j _ hj
      have hne : p ≠ j.val.1 ∨ q ≠ j.val.2 := by
        by_contra! h
        apply hj
        exact Subtype.ext (Prod.ext h.1.symm h.2.symm)
      simp only [LinearMap.comp_apply, ordinaryProjection_inclusion_ne C D p q
        j.val.1 j.val.2 n hpq j.property hne, map_zero]
    · simp
  simpa only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun hF z

/-- Ordinary total coordinates determine every element. -/
theorem ordinary_ext
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (a b : (ordinaryTotal C D).X n)
    (h : ∀ p q (hpq : p+q=n), ordinaryProjection C D p q n hpq a =
      ordinaryProjection C D p q n hpq b) : a = b := by
  rw [← ordinary_reconstruction C D n a, ← ordinary_reconstruction C D n b]
  apply Finset.sum_congr rfl
  intro i _
  rw [h]

/-- A zero horizontal differential leaves precisely the signed vertical one. -/
theorem zero_horizontal_projection_d (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (z : (ordinaryTotal (zeroDifferentialComplex X) D).X (n+1)) :
    ordinaryProjection (zeroDifferentialComplex X) D p q n h
      (((ordinaryTotal (zeroDifferentialComplex X) D).d (n+1) n).hom z) =
    (p : ℤ).negOnePow • tensorMap (LinearMap.id : X p →ₗ[Rᵐᵒᵖ] X p)
      (D.d (q+1) q).hom
      (ordinaryProjection (zeroDifferentialComplex X) D p (q+1) (n+1) (by omega) z) := by
  have hz := LinearMap.congr_fun (ordinaryProjection_d (zeroDifferentialComplex X) D p q n h) z
  have hzero : tensorMap ((zeroDifferentialComplex X).d (p+1) p).hom
      (LinearMap.id : D.X q →ₗ[R] D.X q) = 0 := by
    apply tensor_hom_ext
    intro a b
    change tmul R 0 b = 0
    simp [tmul]
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    hzero, LinearMap.zero_apply, zero_add] using hz

/-- Projecting a total cycle to a column gives a column cycle; the fixed
Koszul sign cancels because it is a unit. -/
theorem projection_mem_cycles (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (z : cycles (ordinaryTotal (zeroDifferentialComplex X) D) n) :
    ordinaryProjection (zeroDifferentialComplex X) D p q n h z.val ∈
      cycles (leftOrdinaryTensorComplex (X p) D) q := by
  cases q with
  | zero =>
    change ((leftOrdinaryTensorComplex (X p) D).d 0
      ((ComplexShape.down ℕ).next 0)).hom _ = 0
    rw [ChainComplex.next_nat_zero,
      (leftOrdinaryTensorComplex (X p) D).shape 0 0 (by simp [ComplexShape.down])]
    rfl
  | succ q =>
    obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1,by omega⟩
    have hz : ((ordinaryTotal (zeroDifferentialComplex X) D).d (k+1) k).hom z.val = 0 := by
      have hz := z.property
      change ((ordinaryTotal (zeroDifferentialComplex X) D).d (k+1)
        ((ComplexShape.down ℕ).next (k+1))).hom z.val = 0 at hz
      rwa [ChainComplex.next_nat_succ] at hz
    have hd := zero_horizontal_projection_d X D p q k (by omega) z.val
    rw [hz, map_zero] at hd
    change ((leftOrdinaryTensorComplex (X p) D).d (q+1)
      ((ComplexShape.down ℕ).next (q+1))).hom _ = 0
    rw [ChainComplex.next_nat_succ]
    change tensorMap (LinearMap.id : X p →ₗ[Rᵐᵒᵖ] X p) (D.d (q+1) q).hom
      (ordinaryProjection (zeroDifferentialComplex X) D p (q+1) (k+1) h z.val) = 0
    rcases Int.units_eq_one_or ((p : ℤ).negOnePow) with hs | hs <;>
      simpa only [hs, Units.smul_def, Units.val_one, Units.val_neg, one_smul,
        neg_one_smul, neg_eq_zero] using hd.symm

/-- Including a column cycle gives a cycle of the actual upstream total. -/
theorem inclusion_mem_cycles (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (z : cycles (leftOrdinaryTensorComplex (X p) D) q) :
    ordinaryInclusion (zeroDifferentialComplex X) D p q n h z.val ∈
      cycles (ordinaryTotal (zeroDifferentialComplex X) D) n := by
  cases n with
  | zero =>
    change ((ordinaryTotal (zeroDifferentialComplex X) D).d 0
      ((ComplexShape.down ℕ).next 0)).hom _ = 0
    rw [ChainComplex.next_nat_zero,
      (ordinaryTotal (zeroDifferentialComplex X) D).shape 0 0 (by simp [ComplexShape.down])]
    rfl
  | succ n =>
    change ((ordinaryTotal (zeroDifferentialComplex X) D).d (n+1)
      ((ComplexShape.down ℕ).next (n+1))).hom _ = 0
    rw [ChainComplex.next_nat_succ]
    apply ordinary_ext (zeroDifferentialComplex X) D n
    intro k l hkl
    rw [zero_horizontal_projection_d, map_zero]
    by_cases hkp : k=p
    · subst k
      have hql : q=l+1 := by omega
      subst q
      rw [ordinaryProjection_inclusion]
      have hz : tensorMap (LinearMap.id : X p →ₗ[Rᵐᵒᵖ] X p) (D.d (l+1) l).hom z.val = 0 := by
        have hz := z.property
        change ((leftOrdinaryTensorComplex (X p) D).d (l+1)
          ((ComplexShape.down ℕ).next (l+1))).hom z.val = 0 at hz
        rw [ChainComplex.next_nat_succ] at hz
        exact hz
      rw [hz, smul_zero]
    · rw [ordinaryProjection_inclusion_ne _ _ p q k (l+1) (n+1) h (by omega)
        (Or.inl (Ne.symm hkp)), map_zero, smul_zero]

def columnCycleInclusion (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n) :
    cycles (leftOrdinaryTensorComplex (X p) D) q →ₗ[ℤ]
      cycles (ordinaryTotal (zeroDifferentialComplex X) D) n :=
  ({ toFun z := ⟨ordinaryInclusion (zeroDifferentialComplex X) D p q n h z.val,
      inclusion_mem_cycles X D p q n h z⟩
     map_zero' := Subtype.ext (map_zero _)
     map_add' a b := Subtype.ext ((ordinaryInclusion (zeroDifferentialComplex X) D p q n h).map_add a.val b.val) } :
    cycles (leftOrdinaryTensorComplex (X p) D) q →+
      cycles (ordinaryTotal (zeroDifferentialComplex X) D) n).toIntLinearMap

def columnCycleProjection (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n) :
    cycles (ordinaryTotal (zeroDifferentialComplex X) D) n →ₗ[ℤ]
      cycles (leftOrdinaryTensorComplex (X p) D) q :=
  ({ toFun z := ⟨ordinaryProjection (zeroDifferentialComplex X) D p q n h z.val,
      projection_mem_cycles X D p q n h z⟩
     map_zero' := Subtype.ext (map_zero _)
     map_add' a b := Subtype.ext ((ordinaryProjection (zeroDifferentialComplex X) D p q n h).map_add a.val b.val) } :
    cycles (ordinaryTotal (zeroDifferentialComplex X) D) n →+
      cycles (leftOrdinaryTensorComplex (X p) D) q).toIntLinearMap

/-- Including an incoming column differential introduces exactly the
vertical Koszul sign, and has no horizontal contribution. -/
theorem inclusion_incoming (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (y : Tensor R (X p) (D.X (q+1))) :
    ((ordinaryTotal (zeroDifferentialComplex X) D).d (n+1) n).hom
      (ordinaryInclusion (zeroDifferentialComplex X) D p (q+1) (n+1) (by omega) y) =
    (p : ℤ).negOnePow • ordinaryInclusion (zeroDifferentialComplex X) D p q n h
      (((leftOrdinaryTensorComplex (X p) D).d (q+1) q).hom y) := by
  apply ordinary_ext (zeroDifferentialComplex X) D n
  intro k l hkl
  rw [zero_horizontal_projection_d]
  by_cases hkp : k=p
  · subst k
    have hlq : l=q := by omega
    subst l
    rw [ordinaryProjection_inclusion]
    rw [LinearMap.map_smul_of_tower, ordinaryProjection_inclusion]
    rfl
  · rw [ordinaryProjection_inclusion_ne _ _ p (q+1) k (l+1) (n+1) (by omega) (by omega)
      (Or.inl (Ne.symm hkp)), map_zero, smul_zero]
    rw [LinearMap.map_smul_of_tower,
      ordinaryProjection_inclusion_ne _ _ p q k l n h hkl (Or.inl (Ne.symm hkp)), smul_zero]

/-- The column inclusion descends through the boundary quotient. -/
def columnHomologyInclusion (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n) :
    Homology (leftOrdinaryTensorComplex (X p) D) q →ₗ[ℤ]
      Homology (ordinaryTotal (zeroDifferentialComplex X) D) n :=
  (QuotientAddGroup.lift (cycleBoundaries (leftOrdinaryTensorComplex (X p) D) q).toAddSubgroup
    ((homologyClass (R := ℤ) (ordinaryTotal (zeroDifferentialComplex X) D) n).toAddMonoidHom.comp
      (columnCycleInclusion X D p q n h).toAddMonoidHom) (by
      intro z hz
      change homologyClass _ n (columnCycleInclusion X D p q n h z) = 0
      apply (P103.Ch10.HomologySequence.class_zero_iff _ _ _).mpr
      change ∃ y, ((leftOrdinaryTensorComplex (X p) D).d
        ((ComplexShape.down ℕ).prev q) q).hom y = z.val at hz
      rw [ChainComplex.prev] at hz
      obtain ⟨y,hy⟩ := hz
      change ∃ t, ((ordinaryTotal (zeroDifferentialComplex X) D).d
        ((ComplexShape.down ℕ).prev n) n).hom t = _
      rw [ChainComplex.prev]
      refine ⟨((p : ℤ).negOnePow)⁻¹ •
        ordinaryInclusion (zeroDifferentialComplex X) D p (q+1) (n+1) (by omega) y, ?_⟩
      rw [LinearMap.map_smul_of_tower, inclusion_incoming, inv_smul_smul, hy]
      rfl)).toIntLinearMap

/-- The column projection descends through the boundary quotient. -/
def columnHomologyProjection (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n) :
    Homology (ordinaryTotal (zeroDifferentialComplex X) D) n →ₗ[ℤ]
      Homology (leftOrdinaryTensorComplex (X p) D) q :=
  (QuotientAddGroup.lift (cycleBoundaries (R := ℤ) (ordinaryTotal (zeroDifferentialComplex X) D) n).toAddSubgroup
    ((homologyClass (leftOrdinaryTensorComplex (X p) D) q).toAddMonoidHom.comp
      (columnCycleProjection X D p q n h).toAddMonoidHom) (by
      intro z hz
      change homologyClass _ q (columnCycleProjection X D p q n h z) = 0
      apply (P103.Ch10.HomologySequence.class_zero_iff _ _ _).mpr
      change ∃ y, ((ordinaryTotal (zeroDifferentialComplex X) D).d
        ((ComplexShape.down ℕ).prev n) n).hom y = z.val at hz
      rw [ChainComplex.prev] at hz
      obtain ⟨y,hy⟩ := hz
      change ∃ t, ((leftOrdinaryTensorComplex (X p) D).d
        ((ComplexShape.down ℕ).prev q) q).hom t = _
      rw [ChainComplex.prev]
      refine ⟨(p : ℤ).negOnePow •
        ordinaryProjection (zeroDifferentialComplex X) D p (q+1) (n+1) (by omega) y, ?_⟩
      rw [LinearMap.map_smul_of_tower]
      exact (zero_horizontal_projection_d X D p q n h y).symm.trans
        (congrArg (ordinaryProjection (zeroDifferentialComplex X) D p q n h) hy))).toIntLinearMap

@[simp] theorem columnHomologyProjection_inclusion
    (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ) (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (p q n : ℕ) (h : p+q=n) (z : Homology (leftOrdinaryTensorComplex (X p) D) q) :
    columnHomologyProjection X D p q n h (columnHomologyInclusion X D p q n h z) = z := by
  obtain ⟨z,rfl⟩ := (cycleBoundaries _ q).mkQ_surjective z
  change homologyClass _ q (columnCycleProjection X D p q n h
    (columnCycleInclusion X D p q n h z)) = homologyClass _ q z
  apply congrArg (homologyClass _ q)
  apply Subtype.ext
  exact ordinaryProjection_inclusion (zeroDifferentialComplex X) D p q n h z.val

theorem columnHomologyProjection_inclusion_ne
    (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ) (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (p q p' q' n : ℕ) (h : p+q=n) (h' : p'+q'=n) (hne : p≠p' ∨ q≠q')
    (z : Homology (leftOrdinaryTensorComplex (X p) D) q) :
    columnHomologyProjection X D p' q' n h' (columnHomologyInclusion X D p q n h z) = 0 := by
  obtain ⟨z,rfl⟩ := (cycleBoundaries _ q).mkQ_surjective z
  change homologyClass _ q' (columnCycleProjection X D p' q' n h'
    (columnCycleInclusion X D p q n h z)) = 0
  have hz : columnCycleProjection X D p' q' n h'
      (columnCycleInclusion X D p q n h z) = 0 := by
    apply Subtype.ext
    exact ordinaryProjection_inclusion_ne (zeroDifferentialComplex X) D p q p' q' n h h' hne z.val
  rw [hz, map_zero]

abbrev DiagonalColumnHomology (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :=
  DirectSum (Diagonal n) (fun i => Homology (leftOrdinaryTensorComplex (X i.val.1) D) i.val.2)

def totalHomologySum (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    DiagonalColumnHomology X D n →ₗ[ℤ]
      Homology (ordinaryTotal (zeroDifferentialComplex X) D) n :=
  DirectSum.toModule ℤ _ _ (fun i => columnHomologyInclusion X D i.val.1 i.val.2 n i.property)

theorem totalHomologySum_projection (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (i : Diagonal n) :
    (columnHomologyProjection X D i.val.1 i.val.2 n i.property).comp (totalHomologySum X D n) =
      DirectSum.component ℤ _ _ i := by
  classical
  apply DirectSum.linearMap_ext
  intro j
  apply LinearMap.ext
  intro z
  change columnHomologyProjection X D i.val.1 i.val.2 n i.property
    (totalHomologySum X D n (DirectSum.lof ℤ _ _ j z)) = _
  rw [totalHomologySum, DirectSum.toModule_lof]
  by_cases hji : j=i
  · subst j
    simp only [columnHomologyProjection_inclusion, LinearMap.comp_apply, DirectSum.component.lof_self]
  · have hne : j.val.1 ≠ i.val.1 ∨ j.val.2 ≠ i.val.2 := by
      by_contra! h
      exact hji (Subtype.ext (Prod.ext h.1 h.2))
    rw [columnHomologyProjection_inclusion_ne X D _ _ _ _ n j.property i.property hne]
    symm
    simp only [LinearMap.comp_apply, DirectSum.component.of, dite_eq_right hji]

theorem totalHomologySum_bijective (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    Function.Bijective (totalHomologySum X D n) := by
  classical
  constructor
  · intro a b hab
    apply DirectSum.ext_component ℤ
    intro i
    have hi := congrArg (columnHomologyProjection X D i.val.1 i.val.2 n i.property) hab
    simpa only [← LinearMap.comp_apply, totalHomologySum_projection] using hi
  · intro z
    obtain ⟨z,rfl⟩ := Quotient.exists_rep z
    refine ⟨∑ i : Diagonal n, DirectSum.lof ℤ _ _ i
      (homologyClass _ i.val.2 (columnCycleProjection X D i.val.1 i.val.2 n i.property z)), ?_⟩
    rw [map_sum]
    simp only [totalHomologySum, DirectSum.toModule_lof]
    change ∑ i : Diagonal n, homologyClass _ n
      (columnCycleInclusion X D i.val.1 i.val.2 n i.property
        (columnCycleProjection X D i.val.1 i.val.2 n i.property z)) = homologyClass _ n z
    rw [← map_sum]
    apply congrArg (homologyClass _ n)
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    change (∑ i : Diagonal n, ordinaryInclusion (zeroDifferentialComplex X) D
      i.val.1 i.val.2 n i.property
      (ordinaryProjection (zeroDifferentialComplex X) D i.val.1 i.val.2 n i.property z.val)) = z.val
    exact ordinary_reconstruction (zeroDifferentialComplex X) D n z.val

/-- Decomposing the actual total homology into its signed columns requires
no flatness; the sign leaves cycles and boundaries unchanged. -/
def totalColumnEquiv (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    DiagonalColumnHomology X D n ≃ₗ[ℤ]
      Homology (ordinaryTotal (zeroDifferentialComplex X) D) n :=
  LinearEquiv.ofBijective (totalHomologySum X D n) (totalHomologySum_bijective X D n)

/-- Applying the flat-column isomorphism to every diagonal summand. -/
def diagonalEquiv (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (hX : ∀ p, RightFlat.{u,v,w} R (X p))
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    DiagonalTensor X D n ≃ₗ[ℤ] Homology (ordinaryTotal (zeroDifferentialComplex X) D) n :=
  (DirectSum.congrLinearEquiv (fun i : Diagonal n => columnEquiv (X i.val.1) (hX i.val.1) D i.val.2)).trans
    (totalColumnEquiv X D n)

theorem diagonalEquiv_formula (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (hX : ∀ p, RightFlat.{u,v,w} R (X p))
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    DiagonalFormula X D n (diagonalEquiv X hX D n) := by
  intro p q h a x
  refine ⟨columnCycleInclusion X D p q n h (columnCycle (X p) D q a x), rfl, ?_⟩
  change totalHomologySum X D n
    ((DirectSum.congrLinearEquiv (fun i : Diagonal n => columnEquiv (X i.val.1) (hX i.val.1) D i.val.2))
      (DirectSum.lof ℤ _ _ ⟨(p,q),h⟩ (tmul R a (homologyClass D q x)))) = _
  rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
    totalHomologySum, DirectSum.toModule_lof]
  change columnHomologyInclusion X D p q n h
    (columnEquiv (X p) (hX p) D q (tmul R a (homologyClass D q x))) = _
  rw [columnEquiv_formula (X p) (hX p) D q a x]
  rfl

theorem diagonal_isomorphism : diagonal_isomorphismType.{u,v,w} := by
  intro R _ X hX D n
  exact ⟨diagonalEquiv X hX D n, diagonalEquiv_formula X hX D n⟩

/-- The representative formulas force simultaneous naturality of the
complete diagonal isomorphism, without any extra flatness hypotheses. -/
theorem diagonal_natural : diagonal_naturalType.{u,v,w} := by
  classical
  intro R _ X X' D D' f g n e e' he he' t
  induction t using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | of i t =>
    change homologyMap (R := ℤ) (ordinaryTotalMap (familyMap f) g) n
      (e (DirectSum.lof ℤ _ _ i t)) = e' (diagonalMap f g n (DirectSum.lof ℤ _ _ i t))
    induction t using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ha a b ha hb => simp only [map_add, ha, hb]
    | ht a x =>
      obtain ⟨x,rfl⟩ := (cycleBoundaries D i.val.2).mkQ_surjective x
      obtain ⟨z,hz,hez⟩ := he i.val.1 i.val.2 i.property a x
      obtain ⟨z',hz',hez'⟩ := he' i.val.1 i.val.2 i.property
        ((f i.val.1).hom a) (cyclesMap g i.val.2 x)
      change homologyMap (R := ℤ) (ordinaryTotalMap (familyMap f) g) n
        (e (DirectSum.lof ℤ _ _ i (tmul R a (homologyClass D i.val.2 x)))) = _
      rw [hez, diagonalMap, DirectSum.toModule_lof]
      change homologyMap (R := ℤ) (ordinaryTotalMap (familyMap f) g) n (homologyClass _ n z) =
        e' (DirectSum.lof ℤ _ _ i (tmul R ((f i.val.1).hom a)
          (homologyMap g i.val.2 (homologyClass D i.val.2 x))))
      rw [P103.Ch10.Complexes.homologyMap_apply (f := g), hez']
      rw [P103.Ch10.Complexes.homologyMap_apply]
      apply congrArg (homologyClass _ n)
      apply Subtype.ext
      change ((ordinaryTotalMap (familyMap f) g).f n).hom z.val = z'.val
      rw [hz, hz']
      exact P103.Ch11.TorBalance.ordinaryTotalMap_inclusion (familyMap f) g
        i.val.1 i.val.2 n i.property a x.val

end
end P103.Ch11.KunnethFlatColumns
