import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FlatSquareZeroLifts
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SquareZeroLiftTorsor

noncomputable section

open scoped BigOperators TensorProduct
open TensorProduct
open RingTheory.Sequence

namespace CommutativeAlgebraNotes.CompleteIntersectionTangentSpace

open Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
open Algebra.Extension

private theorem ofList_ofFn {R : Type*} [CommRing R] {s : ℕ} (f : Fin s → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  unfold Ideal.ofList
  congr 1
  ext x
  simp

/-- A relation among a regular sequence has all coefficients in its ideal. -/
private theorem coeff_mem_span_of_sum_eq_zero {R : Type*} [CommRing R] :
    ∀ {s : ℕ} (f : Fin s → R), IsWeaklyRegular R (List.ofFn f) →
      ∀ a : Fin s → R, (∑ i, a i * f i) = 0 →
        ∀ i, a i ∈ Ideal.span (Set.range f) := by
  intro s
  induction s with
  | zero => exact fun _ _ _ _ i => i.elim0
  | succ s ih =>
    intro f h a ha
    classical
    let g : Fin s → R := f ∘ Fin.castSucc
    let I : Ideal R := Ideal.span (Set.range g)
    let r := f (Fin.last s)
    have hreg := h
    rw [List.ofFn_succ', List.concat_eq_append, isWeaklyRegular_append_iff,
      ofList_ofFn, isWeaklyRegular_singleton_iff] at hreg
    change _ ∧ IsSMulRegular (R ⧸ (I * ⊤)) r at hreg
    rw [Ideal.mul_top] at hreg
    have hs : ∑ i : Fin s, a i.castSucc * g i ∈ I := by
      exact I.sum_mem (fun i _ => I.mul_mem_left _ (Ideal.subset_span (Set.mem_range_self i)))
    rw [Fin.sum_univ_castSucc] at ha
    change (∑ i : Fin s, a i.castSucc * g i) + a (Fin.last s) * r = 0 at ha
    have hm : a (Fin.last s) * r ∈ I := by
      rw [eq_neg_of_add_eq_zero_right ha]
      exact I.neg_mem hs
    have hl : a (Fin.last s) ∈ I := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      apply hreg.2
      change Ideal.Quotient.mk I r * Ideal.Quotient.mk I (a (Fin.last s)) =
        Ideal.Quotient.mk I r * 0
      rw [← map_mul, mul_comm r, Ideal.Quotient.eq_zero_iff_mem.mpr hm, mul_zero]
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hl
    have hrel : ∑ i : Fin s, (a i.castSucc + b i * r) * g i = 0 := by
      simp only [add_mul, Finset.sum_add_distrib]
      convert ha using 2
      rw [← hb, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hg := ih g hreg.1 _ hrel
    have hle : I ≤ Ideal.span (Set.range f) :=
      Ideal.span_mono (fun _ ⟨i, hi⟩ => ⟨i.castSucc, hi⟩)
    intro i
    refine Fin.lastCases (hle hl) (fun j => ?_) i
    have hj := (Ideal.span (Set.range f)).sub_mem (hle (hg j))
      ((Ideal.span (Set.range f)).mul_mem_left (b j) (Ideal.subset_span ⟨Fin.last s, rfl⟩))
    simpa only [r, add_sub_cancel_right] using hj

private theorem coeff_mem_span_of_sum_mem_sq {R : Type*} [CommRing R] {s : ℕ}
    (f : Fin s → R) (h : IsWeaklyRegular R (List.ofFn f))
    (a : Fin s → R) (ha : ∑ i, a i * f i ∈ Ideal.span (Set.range f) ^ 2) :
    ∀ i, a i ∈ Ideal.span (Set.range f) := by
  classical
  let I : Ideal R := Ideal.span (Set.range f)
  let L : (Fin s → I) →ₗ[R] R :=
    { toFun := fun b => ∑ i, (b i : R) * f i
      map_add' := by intro b c; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c b; simp [mul_assoc, Finset.mul_sum] }
  have hsq : I ^ 2 ≤ L.range := by
    rw [pow_two, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
    refine ⟨fun i => ⟨x * b i, I.mul_mem_right _ hx⟩, ?_⟩
    change (∑ i, (x * b i) * f i) = x * y
    rw [← hb, Finset.mul_sum]
    simp only [mul_assoc]
  obtain ⟨b, hb⟩ := hsq ha
  change ∑ i, (b i : R) * f i = ∑ i, a i * f i at hb
  have hz : ∑ i, (a i - (b i : R)) * f i = 0 := by
    simp [sub_mul, Finset.sum_sub_distrib, hb]
  intro i
  simpa using I.add_mem (coeff_mem_span_of_sum_eq_zero f h _ hz i) (b i).property

section Polynomial

universe u

variable {k : Type u} [Field k] {n s : ℕ} (f : Fin s → P k n)

private abbrev polyExtension := (generators f).toExtension

private theorem algMap_poly (x : P k n) :
    algebraMap (polyExtension f).Ring (B f) x = q f x :=
  (generators f).algebraMap_apply x |>.trans
    (DFunLike.congr_fun (MvPolynomial.aeval_unique (q f)) x).symm

private def relation (i : Fin s) : (polyExtension f).ker :=
  ⟨f i, by
    change f i ∈ (generators f).ker
    rw [generators_ker]
    exact Ideal.subset_span (Set.mem_range_self i)⟩

private def scaledRelation (a : (polyExtension f).Ring) (i : Fin s) : (polyExtension f).ker :=
  a • relation f i

private theorem conormal_sum (a : Fin s → P k n) :
    ∑ i, q f (a i) • relationClass f i =
      Cotangent.mk (P := polyExtension f) (∑ i, scaledRelation f (a i) i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change q f (a i) • Cotangent.mk (relation f i) =
    Cotangent.mk ((show (polyExtension f).Ring from a i) • relation f i)
  rw [map_smul]
  calc
    _ = algebraMap (polyExtension f).Ring (B f) (a i) • Cotangent.mk (relation f i) :=
      congrArg (fun t : B f => t • Cotangent.mk (relation f i)) (algMap_poly f (a i)).symm
    _ = _ := algebraMap_smul (B f) _ _

theorem conormalBasis : ConormalBasis.{u} := by
  intro k _ n s f hf
  classical
  have hli : LinearIndependent (B f) (relationClass f) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    choose b hb using fun i => (Ideal.Quotient.mk_surjective (I := J f)) (a i)
    have hh : ∑ i, q f (b i) • relationClass f i = 0 := by
      simpa only [show ∀ i, q f (b i) = a i from hb] using ha
    rw [conormal_sum, Cotangent.mk_eq_zero_iff] at hh
    have hsq : ∑ i, b i * f i ∈ J f ^ 2 := by
      have he : ((∑ i, scaledRelation f (b i) i : (polyExtension f).ker) :
          (polyExtension f).Ring) = ∑ i, b i * f i := by
        rw [Submodule.coe_sum]
        rfl
      rw [he] at hh
      change (∑ i, b i * f i) ∈ (generators f).ker ^ 2 at hh
      rwa [generators_ker] at hh
    intro i
    rw [← hb i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (coeff_mem_span_of_sum_mem_sq f hf.toIsWeaklyRegular b hsq i)
  have hsp : ⊤ ≤ Submodule.span (B f) (Set.range (relationClass f)) := by
    intro x _
    obtain ⟨v, rfl⟩ := Cotangent.mk_surjective x
    have hv := v.property
    change v.val ∈ (generators f).ker at hv
    rw [generators_ker] at hv
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv
    have he : (∑ i, scaledRelation f (a i) i) = v := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact ha
    rw [← he]
    rw [← conormal_sum f a]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i))
  exact ⟨Module.Basis.mk hli hsp, Module.Basis.mk_apply hli hsp⟩

set_option maxHeartbeats 1000000 in
theorem jacobianIntertwines : JacobianIntertwines.{u} := by
  intro k _ n s f h i
  let G := generators f
  let x := G.toExtension.cotangentComplex (relationClass f i)
  change h x = _
  have hrepr (j : Fin n) :
      G.cotangentSpaceBasis.repr x j = q f (MvPolynomial.pderiv j (f i)) := by
    change G.cotangentSpaceBasis.repr (G.toExtension.cotangentComplex
      (Cotangent.mk (relation f i))) j = _
    rw [cotangentComplex_mk, G.cotangentSpaceBasis_repr_one_tmul]
    exact (DFunLike.congr_fun (MvPolynomial.aeval_unique (q f)) _).symm
  rw [← G.cotangentSpaceBasis.sum_repr x, map_sum]
  simp only [map_smul, hrepr, smul_eq_mul]
  rfl

end Polynomial

section Deformations

open SquareZeroLift FlatSquareZeroLifts

universe u z l m

variable {k : Type u} [Field k] {C : Type u} [CommRing C] [Algebra k C]

private theorem hasLift (D : MarkedDeformation.{u,u,u,z} (dual k) C) :
    ∃ (L : Lift.{u,u,u,u,max u z} (dualExtension k) (c C))
      (j : D ≃ₐ[dual k] L.Ring), ∀ d, L.map (j d) = reduction D d := by
  obtain ⟨L, j, hj, _⟩ := flatToSquareZero (dualResidue k) (dual k).residue_surjective
    (dualResidue_squareZero k) (reduction D) ⟨D.marking, fun _ => rfl⟩
  exact ⟨L, j, hj⟩

private theorem coefficient_ext {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]
    [Algebra A C] (e : BaseExtension R A) {F G : Coefficients e C →ₗ[C] Coefficients e C}
    (h : ∀ b i, F (coefficientTensor e b i) = G (coefficientTensor e b i)) : F = G :=
  AlgebraTensorModule.ext h

private theorem coefficientTensor_eq {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]
    [Algebra A C] (e : BaseExtension R A) (b : C) (i : e.I) :
    coefficientTensor e b i = b • coefficientMap (B := C) e i :=
  TensorProduct.tmul_eq_smul_one_tmul b i

private theorem marking_preserved
    (L : Lift.{u,u,u,u,l} (dualExtension k) (c C))
    (M : Lift.{u,u,u,u,m} (dualExtension k) (c C))
    (j : L.Ring ≃ₐ[dual k] M.Ring) (hj : ∀ x, M.map (j x) = L.map x)
    (x : L.ker) : M.marking (L.mapKer j hj x) = L.marking x := by
  let mapKer : L.ker →ₗ[C] M.ker := {
    toFun := L.mapKer j hj
    map_add' := fun a b => Subtype.ext (j.map_add a b)
    map_smul' := fun b a => by
      obtain ⟨y, rfl⟩ := L.surjective b
      simp only [RingHom.id_apply]
      rw [L.map_smul, ← hj y, M.map_smul]
      exact Subtype.ext (j.map_mul y a) }
  let F := M.marking.toLinearMap ∘ₗ mapKer ∘ₗ L.marking.symm.toLinearMap
  have hF : F = LinearMap.id := by
    apply coefficient_ext (dualExtension k)
    intro b i
    have ht := coefficientTensor_eq (dualExtension k) b i
    have hi : mapKer (coefficientInKernel (dualExtension k) L.map L.over i) =
        coefficientInKernel (dualExtension k) M.map M.over i :=
      Subtype.ext (j.commutes i)
    change F (coefficientTensor (dualExtension k) b i) = _
    rw [ht, F.map_smul, LinearMap.id_apply]
    congr 1
    change M.marking (mapKer (L.marking.symm (c C i))) = _
    have hL : L.marking.symm (c C i) = coefficientInKernel (dualExtension k) L.map L.over i :=
      L.marking.symm_apply_eq.mpr (L.induces i).symm
    rw [hL, hi]
    exact M.induces i
  have hx := DFunLike.congr_fun hF (L.marking x)
  simpa only [F, mapKer, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply] using hx

private theorem marking_eq_of_reduction
    {D E : MarkedDeformation.{u,u,u,z} (dual k) C}
    (j : D ≃ₐ[dual k] E) (hj : ∀ d, reduction E (j d) = reduction D d) :
    (MarkedDeformation.specialFibreCongr j).trans E.marking = D.marking := by
  apply AlgEquiv.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r d =>
    change E.marking (r ⊗ₜ[dual k] j d) = D.marking (r ⊗ₜ[dual k] d)
    have ht {X : Type (max u z)} [CommRing X] [Algebra (dual k) X] (x : X) :
        r ⊗ₜ[dual k] x = r • ((1 : k) ⊗ₜ[dual k] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht (j d), ht d, map_smul, map_smul]
    exact congrArg (fun x : C => r • x) (hj d)

private theorem reduction_eq_of_marking
    {D E : MarkedDeformation.{u,u,u,z} (dual k) C} (j : D.MarkedIso E) (d : D) :
    reduction E (j.val d) = reduction D d :=
  DFunLike.congr_fun j.property ((1 : k) ⊗ₜ[dual k] d)

private def chosenLift (D : MarkedDeformation.{u,u,u,z} (dual k) C) :=
  (hasLift D).choose

private theorem hasSmallLift {n s : ℕ} (f : Fin s → P k n)
    (D : MarkedDeformation.{u,u,u,z} (dual k) (B f)) :
    ∃ L : Lift.{u,u,u,u,u} (dualExtension k) (c (B f)), Corresponds D L := by
  obtain ⟨j, hj⟩ := (hasLift D).choose_spec
  let p := presentation f
  let e := p.representativeIso (chosenLift D)
  refine ⟨p.representative (chosenLift D), j.trans e.equiv.symm, fun d => ?_⟩
  exact (e.symm.over (j d)).trans (hj d)

private theorem lift_iso_iff {D E : MarkedDeformation.{u,u,u,z} (dual k) C}
    {L M : Lift.{u,u,u,u,u} (dualExtension k) (c C)}
    (hL : Corresponds D L) (hM : Corresponds E M) :
    Nonempty (L.Iso M) ↔ D.Isomorphic E := by
  obtain ⟨l, hl⟩ := hL
  obtain ⟨m, hm⟩ := hM
  constructor
  · rintro ⟨e⟩
    let a := (l.trans e.equiv).trans m.symm
    refine ⟨⟨a, marking_eq_of_reduction a fun d => ?_⟩⟩
    calc
      reduction E (a d) = M.map (m (m.symm (e.equiv (l d)))) := (hm _).symm
      _ = L.map (l d) := by rw [m.apply_symm_apply, e.over]
      _ = reduction D d := hl d
  · rintro ⟨j⟩
    let a := (l.symm.trans j.val).trans m
    have ha (x : L.Ring) : M.map (a x) = L.map x := by
      calc
        _ = reduction E (j.val (l.symm x)) := hm _
        _ = reduction D (l.symm x) := reduction_eq_of_marking j _
        _ = L.map x := by rw [← hl, l.apply_symm_apply]
    exact ⟨⟨a, ha, marking_preserved L M a ha⟩⟩

private theorem representedByDeformation
    (L : Lift.{u,u,u,u,u} (dualExtension k) (c C)) :
    ∃ D : MarkedDeformation.{u,u,u,z} (dual k) C, Corresponds D L := by
  obtain ⟨hflat, ⟨mark, hmark⟩⟩ :=
    squareZeroToFlat (dualResidue k) (dual k).residue_surjective (dualResidue_squareZero k) L
  let : Module.Flat (dual k) L.Ring := hflat
  let D : MarkedDeformation.{u,u,u,z} (dual k) C := {
    carrier := ULift.{z} L.Ring
    marking := (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) ULift.algEquiv).trans mark }
  exact ⟨D, ULift.algEquiv, fun d => (hmark d.down).symm⟩

open Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor (liftClass)

private theorem deformationClassEquiv {n s : ℕ} (f : Fin s → P k n) :
    ∃ F : MarkedDeformation.Classes.{u,u,u,z} (dual k) (B f) ≃ LiftClasses (k := k) (B f),
      ∀ D L, Corresponds D L → F (MarkedDeformation.classModel D) = liftClass L := by
  let l (D : MarkedDeformation.{u,u,u,z} (dual k) (B f)) := (hasSmallLift f D).choose
  have hl (D : MarkedDeformation.{u,u,u,z} (dual k) (B f)) :
      Corresponds D (l D) := (hasSmallLift f D).choose_spec
  let F : MarkedDeformation.Classes.{u,u,u,z} (dual k) (B f) → LiftClasses (k := k) (B f) :=
    Quotient.lift (fun D => liftClass (l D))
      (fun D E h => Quotient.sound ((lift_iso_iff (hl D) (hl E)).mpr h))
  have hF (D : MarkedDeformation.{u,u,u,z} (dual k) (B f)) (L)
      (h : Corresponds D L) : F (MarkedDeformation.classModel D) = liftClass L :=
    Quotient.sound ((lift_iso_iff (hl D) h).mpr ⟨⟨AlgEquiv.refl,
      marking_eq_of_reduction AlgEquiv.refl (fun _ => rfl)⟩⟩)
  refine ⟨Equiv.ofBijective F ⟨?_, ?_⟩, hF⟩
  · intro X Y h
    obtain ⟨D, rfl⟩ := Quotient.exists_rep X
    obtain ⟨E, rfl⟩ := Quotient.exists_rep Y
    exact Quotient.sound ((lift_iso_iff (hl D) (hl E)).mp (Quotient.exact h))
  · intro X
    obtain ⟨L, rfl⟩ := Quotient.exists_rep X
    obtain ⟨D, h⟩ := representedByDeformation L
    exact ⟨MarkedDeformation.classModel D, hF D L h⟩

end Deformations

section Cokernel

open SquareZeroLift TensorProduct

universe u

variable {k : Type u} [Field k] {n s : ℕ} (f : Fin s → P k n)

private def residueHom : (presentation f).barExtension.Hom (polyExtension f) :=
  ⟨(presentation f).barPolynomialEquiv.toRingHom,
    fun a => ((presentation f).barPolynomialEquiv.commutes a).trans
      (congrArg (algebraMap k (polyExtension f).Ring) (Algebra.algebraMap_self_apply a).symm),
    fun x => by
      rw [Algebra.algebraMap_self_apply]
      exact (algMap_poly f _).trans (barMap_eq f x).symm⟩

private def residueInv : (polyExtension f).Hom (presentation f).barExtension :=
  ⟨(presentation f).barPolynomialEquiv.symm.toRingHom,
    fun a => ((presentation f).barPolynomialEquiv.symm.commutes a).trans
      (congrArg (algebraMap k (presentation f).barExtension.Ring)
        (Algebra.algebraMap_self_apply a).symm),
    fun x => by
      rw [Algebra.algebraMap_self_apply]
      exact (barMap_eq f _).trans <|
        (congrArg (q f) ((presentation f).barPolynomialEquiv.apply_symm_apply x)).trans
          (algMap_poly f x).symm⟩

private theorem residueInv_comp : (residueInv f).comp (residueHom f) =
    Hom.id (presentation f).barExtension := by
  ext x
  exact (presentation f).barPolynomialEquiv.symm_apply_apply x

private theorem residueHom_comp : (residueHom f).comp (residueInv f) =
    Hom.id (polyExtension f) := by
  ext x
  exact (presentation f).barPolynomialEquiv.apply_symm_apply x

private def relationEquiv :
    (presentation f).BarConormal ≃ₗ[B f] (polyExtension f).Cotangent :=
  LinearEquiv.ofLinearMap (Cotangent.map (residueHom f)) (Cotangent.map (residueInv f))
    (by simpa only [LinearMap.restrictScalars_self, residueHom_comp, Cotangent.map_id] using
      (Cotangent.map_comp _ (residueInv f) (residueHom f)).symm)
    (by simpa only [LinearMap.restrictScalars_self, residueInv_comp, Cotangent.map_id] using
      (Cotangent.map_comp _ (residueHom f) (residueInv f)).symm)

private def differentialEquiv :
    (presentation f).barExtension.CotangentSpace ≃ₗ[B f] (polyExtension f).CotangentSpace :=
  LinearEquiv.ofLinearMap (CotangentSpace.map (residueHom f)) (CotangentSpace.map (residueInv f))
    (by simpa only [LinearMap.restrictScalars_self, residueHom_comp, CotangentSpace.map_id] using
      (CotangentSpace.map_comp (residueInv f) (residueHom f)).symm)
    (by simpa only [LinearMap.restrictScalars_self, residueInv_comp, CotangentSpace.map_id] using
      (CotangentSpace.map_comp (residueHom f) (residueInv f)).symm)

private theorem relationEquiv_apply (i : Fin s) :
    relationEquiv f (reducedRelation f i) = relationClass f i := by
  change Cotangent.map (residueHom f) (Cotangent.mk _) = Cotangent.mk (relation f i)
  rw [Cotangent.map_mk]
  congr 1
  exact Subtype.ext ((presentation f).barPolynomialEquiv.apply_symm_apply (f i))

private abbrev dualKernelModule (k : Type u) [Field k] :
    Module k (dualExtension k).I :=
  kernelModule (dualExtension k).hom (dualExtension k).surjective (dualExtension k).squareZero

attribute [local instance 2000] dualKernelModule

private def kernelEquiv (k : Type u) [Field k] : (dualExtension k).I ≃ₗ[k] k where
  toFun x := x.val.snd
  invFun a := ⟨TrivSqZeroExt.inr a, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · exact (RingHom.mem_ker.mp x.property).symm
    · rfl
  right_inv a := rfl
  map_add' x y := rfl
  map_smul' a x := by
    have ha : (dualExtension k).hom (algebraMap k (dual k) a) = a := AlgHom.commutes _ _
    have hs := congrArg (fun y : (dualExtension k).I => y.val.snd)
      ((dualExtension k).hom_smul (algebraMap k (dual k) a) x)
    rw [ha] at hs
    refine hs.trans ?_
    let y : TrivSqZeroExt k k := x.val
    change (TrivSqZeroExt.inl a * y).snd = a • y.snd
    exact congrArg TrivSqZeroExt.snd (TrivSqZeroExt.inl_mul_eq_smul a y)

private def coeffEquiv {k : Type u} [Field k] (C : Type u) [CommRing C] [Algebra k C] :
    Coeff (k := k) C ≃ₗ[C] C :=
  (AlgebraTensorModule.congr (LinearEquiv.refl C C) (kernelEquiv k)).trans
    (AlgebraTensorModule.rid k C C)

private theorem coeffEquiv_one (C : Type u) [CommRing C] [Algebra k C] :
    coeffEquiv (k := k) C (c (k := k) C (epsilon k)) = 1 := by
  rw [show c (k := k) C (epsilon k) = FlatSquareZeroLifts.coefficientTensor
    (dualExtension k) (1 : C) (epsilon k) from rfl]
  simp [coeffEquiv, show kernelEquiv k (epsilon k) = 1 from rfl]

set_option maxHeartbeats 1200000 in
theorem cokernelIdentification : CokernelIdentification.{u} := by
  intro k _ n s f hf
  obtain ⟨b, hb⟩ := conormalBasis f hf
  let E := coeffEquiv (k := k) (B f)
  let V := ((differentialEquiv f).arrowCongr E).trans
    (((generators f).cotangentSpaceBasis.constr (B f) (M' := B f)).symm)
  let W := ((relationEquiv f).arrowCongr E).trans ((b.constr (B f) (M' := B f)).symm)
  have hW (g : (presentation f).BarConormal →ₗ[B f] Coeff (k := k) (B f)) (i : Fin s) :
      W g i = E (g (reducedRelation f i)) := by
    simp [W, hb, ← relationEquiv_apply f i]
  have hcomm (g : (presentation f).barExtension.CotangentSpace →ₗ[B f] Coeff (k := k) (B f)) :
      W (restriction f g) = jacobian f (V g) := by
    let h := (differentialEquiv f).arrowCongr E g
    have hv (j : Fin n) : V g j = h ((generators f).cotangentSpaceBasis j) := by
      simp [V, h]
    ext i
    rw [hW]
    let x := (presentation f).barExtension.cotangentComplex (reducedRelation f i)
    let y := (polyExtension f).cotangentComplex (relationClass f i)
    have he : differentialEquiv f x = y := by
      calc
        _ = (polyExtension f).cotangentComplex (relationEquiv f (reducedRelation f i)) :=
          CotangentSpace.map_cotangentComplex (residueHom f) (reducedRelation f i)
        _ = _ := congrArg (polyExtension f).cotangentComplex (relationEquiv_apply f i)
    change E (g x) = _
    calc
      _ = h y := by
        change E (g x) = E (g ((differentialEquiv f).symm y))
        rw [← he, LinearEquiv.symm_apply_apply]
      _ = jacobian f (fun j => h ((generators f).cotangentSpaceBasis j)) i :=
        jacobianIntertwines f h i
      _ = _ := congrArg (fun v => jacobian f v i) (funext hv).symm
  have hrange : (restriction f).range.map W.toLinearMap = (jacobian f).range := by
    ext y
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨V g, (hcomm g).symm⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨g, rfl⟩ := V.surjective v
      exact ⟨_, ⟨g, rfl⟩, hcomm g⟩
  refine ⟨E, Submodule.Quotient.equiv _ _ W hrange, coeffEquiv_one (k := k) _, fun g => ?_⟩
  change (jacobian f).range.mkQ (W g) = _
  congr 1
  exact funext (hW g)

end Cokernel

open SquareZeroLift

universe u z

set_option maxHeartbeats 1500000 in
theorem tangentSpace : TangentSpace.{u,z} := by
  intro k _ n s f hf
  obtain ⟨F, hF⟩ := deformationClassEquiv f
  obtain ⟨U, E, hE⟩ := cokernelIdentification f hf
  let D₀ := Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.trivial.{u,z} k (B f)
  let X₀ := F (MarkedDeformation.classModel D₀)
  obtain ⟨L, _⟩ := hasSmallLift f D₀
  obtain ⟨a, ha⟩ := (presentation f).torsor (c (k := k) (B f)) ⟨L⟩
  let := a
  let G := F.trans ((Equiv.vaddConst X₀).symm.trans E.toEquiv)
  refine ⟨F, a, U, E, G, hF, ha, hE, fun X => rfl, ?_⟩
  let := G.addCommGroup
  let := G.addEquiv.module k
  refine ⟨G.addEquiv.linearEquiv k, rfl, ?_⟩
  change E (X₀ -ᵥ X₀) = 0
  rw [vsub_self, map_zero]

end CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
