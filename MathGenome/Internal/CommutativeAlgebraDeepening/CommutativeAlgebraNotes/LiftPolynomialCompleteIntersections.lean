import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LiftPolynomialCompleteIntersections
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.KoszulFlatDeformationModels
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
import Mathlib.RingTheory.Flat.Equalizer
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace CommutativeAlgebraNotes.LiftPolynomialCompleteIntersections

open scoped TensorProduct
open LocalArtinAlgebra MarkedDeformation
open KoszulFlatDeformationModelsSpec (Model)
open Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace (P B J q)
open Specs.CommutativeAlgebraNotes.LiftPolynomialCompleteIntersections

open private ker_mk_one span_eq_top_of_residue
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.KoszulFlatDeformationModels
open private ofList_ofFn from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace

universe u v z

private theorem residue_ker {k : Type u} [Field k] (A : LocalArtinAlgebra.{u,v} k)
    {M : Type*} [AddCommGroup M] [Module A M] :
    LinearMap.ker (TensorProduct.mk A k M 1) =
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := by
  rw [ker_mk_one A.residue_surjective]
  exact congrArg (fun I : Ideal A => I • (⊤ : Submodule A M)) A.ker_residue

/-- A flat marked deformation admits a polynomial presentation by equations
lifting the given equations of its closed fibre. -/
private theorem presentation {k : Type u} [Field k] {n s : ℕ} (f : Fin s → P k n)
    {A : LocalArtinAlgebra.{u,v} k} (D : MarkedDeformation.{u,v,u,z} A (B f)) :
    ∃ (g : Fin s → MvPolynomial (Fin n) A),
      (∀ i, MvPolynomial.map A.residue.toRingHom (g i) = f i) ∧
      Nonempty (Model (List.ofFn g) ≃ₐ[A] D) := by
  classical
  let PA := MvPolynomial (Fin n) A
  let red : PA →+* P k n := MvPolynomial.map A.residue.toRingHom
  let iD := TensorProduct.mk A k D 1
  have hiD : Function.Surjective iD :=
    TensorProduct.mk_surjective (R := ↑A) (S := k) (M := ↑D) A.residue_surjective
  choose x hx using fun j : Fin n => hiD (D.marking.symm (q f (MvPolynomial.X j)))
  let ev : PA →ₐ[A] D := MvPolynomial.aeval x
  let α : k ⊗[A] PA ≃ₐ[k] P k n := MvPolynomial.algebraTensorAlgEquiv A k
  let ev₀ : k ⊗[A] PA →ₐ[k] k ⊗[A] D :=
    Algebra.TensorProduct.map (AlgHom.id k k) ev
  have hred (p : PA) : α (1 ⊗ₜ[A] p) = red p := by
    exact (MvPolynomial.algebraTensorAlgEquiv_tmul A k 1 p).trans (one_smul _ _)
  have hcomm : D.marking.toAlgHom.comp ev₀ = (q f).comp α.toAlgHom := by
    apply AlgHom.ext
    intro t
    have heq : (D.marking.toAlgHom.comp ev₀).comp α.symm.toAlgHom = q f := by
      apply MvPolynomial.algHom_ext
      intro j
      change D.marking (ev₀ (α.symm (MvPolynomial.X j))) = _
      rw [show α.symm (MvPolynomial.X j) = 1 ⊗ₜ[A] MvPolynomial.X j from
        MvPolynomial.algebraTensorAlgEquiv_symm_X A k j]
      change D.marking (1 ⊗ₜ[A] ev (MvPolynomial.X j)) = _
      rw [show ev (MvPolynomial.X j) = x j from MvPolynomial.aeval_X _ _, ←
        show iD (x j) = 1 ⊗ₜ[A] x j from rfl, hx, AlgEquiv.apply_symm_apply]
    have ht := DFunLike.congr_fun heq (α t)
    change D.marking (ev₀ (α.symm (α t))) = q f (α t) at ht
    change D.marking (ev₀ t) = q f (α t)
    simpa only [AlgEquiv.symm_apply_apply] using ht
  have hcomm' (p : PA) : D.marking (iD (ev p)) = q f (red p) := by
    rw [← hred p]
    exact DFunLike.congr_fun hcomm (1 ⊗ₜ[A] p)
  have hsred : Function.Surjective red := MvPolynomial.map_surjective _ A.residue_surjective
  -- The lifted variables generate by nilpotence of the maximal ideal.
  have hev : Function.Surjective ev := by
    have hrs : ev.toLinearMap.range.map iD = ⊤ := by
      apply Submodule.eq_top_iff'.mpr
      intro d
      obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (D.marking d)
      obtain ⟨t, ht⟩ := hsred p
      exact ⟨ev t, ⟨t, rfl⟩, D.marking.injective ((hcomm' t).trans (by rw [ht]; exact hp))⟩
    exact LinearMap.range_eq_top.mp (span_eq_top_of_residue A iD (residue_ker A) _ hrs)
  let K := LinearMap.ker ev.toLinearMap
  let iK := TensorProduct.mk A k K 1
  let incl := K.subtype.lTensor k
  have hex : Function.Exact K.subtype ev.toLinearMap :=
    LinearMap.exact_subtype_ker_map ev.toLinearMap
  have htex : Function.Exact incl (ev.toLinearMap.lTensor k) :=
    lTensor_exact k hex hev
  -- Flatness of the quotient makes the reduced kernel embed in the reduced polynomial ring.
  have hincl : Function.Injective incl :=
    LinearMap.lTensor_injective_of_exact_of_flat _ hev _ K.injective_subtype hex k
  have hiK : Function.Surjective iK :=
    TensorProduct.mk_surjective (R := ↑A) (S := k) (M := K) A.residue_surjective
  let rK := (α.toLinearEquiv.toLinearMap.restrictScalars A).comp incl |>.comp iK
  have hrK (t : K) : rK t = red (t : PA) := hred _
  have hrKker : LinearMap.ker rK = IsLocalRing.maximalIdeal A • (⊤ : Submodule A K) := by
    rw [show rK = ((α.toLinearEquiv.toLinearMap.restrictScalars A).comp incl).comp iK from rfl,
      LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr (α.injective.comp hincl),
      Submodule.comap_bot, residue_ker A]
  have hpre (p : P k n) (hp : p ∈ J f) : ∃ t : K, rK t = p := by
    obtain ⟨w, hw⟩ := hsred p
    have hz : (ev.toLinearMap.lTensor k) (1 ⊗ₜ[A] w) = 0 := by
      apply D.marking.injective
      rw [map_zero]
      change D.marking (iD (ev w)) = 0
      rw [hcomm', hw]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
    obtain ⟨y, hy⟩ := (htex (1 ⊗ₜ[A] w)).mp hz
    obtain ⟨t, ht⟩ := hiK y
    exact ⟨t, show α (incl (iK t)) = p by rw [ht, hy, hred, hw]⟩
  choose g₀ hg₀ using fun i : Fin s => hpre (f i) (Ideal.subset_span (Set.mem_range_self i))
  let g : Fin s → PA := fun i => g₀ i
  have hg (i : Fin s) : red (g i) = f i := (hrK _).symm.trans (hg₀ i)
  let I := Ideal.ofList (List.ofFn g)
  have hIK : I ≤ RingHom.ker ev.toRingHom := by
    rw [show I = Ideal.span (Set.range g) from ofList_ofFn g, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (g₀ i).property
  -- The lifted equations generate the kernel after reduction and hence over A.
  let N : Submodule A K := (I.restrictScalars A).comap K.subtype
  have hN : N.map rK = LinearMap.range rK := by
    apply le_antisymm
    · rintro _ ⟨t, _, rfl⟩
      exact ⟨t, rfl⟩
    rintro _ ⟨t, rfl⟩
    have ht : rK t ∈ J f := by
      rw [hrK]
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q f (red (t : PA)) = 0
      rw [← hcomm', show ev (t : PA) = 0 from t.property, map_zero, map_zero]
    have him : I.map red = J f := by
      rw [show I = Ideal.span (Set.range g) from ofList_ofFn g, Ideal.map_span]
      congr 1
      rw [← Set.range_comp, show red ∘ g = f from funext hg]
    rw [← him, Ideal.mem_map_iff_of_surjective red hsred] at ht
    obtain ⟨w, hw, hwt⟩ := ht
    let wK : K := ⟨w, hIK hw⟩
    exact ⟨wK, hw, (hrK wK).trans hwt⟩
  have htop : N = ⊤ := by
    let r := rK.rangeRestrict
    have hr : LinearMap.ker r = LinearMap.ker rK := LinearMap.ker_rangeRestrict rK
    apply span_eq_top_of_residue A r (hr.trans hrKker)
    apply Submodule.eq_top_iff'.mpr
    intro d
    have hd : (d : P k n) ∈ N.map rK := hN.symm ▸ d.property
    obtain ⟨x, hx, he⟩ := hd
    exact ⟨x, hx, Subtype.ext he⟩
  have hI : I = RingHom.ker ev.toRingHom := by
    refine le_antisymm hIK fun t ht => ?_
    let tK : K := ⟨t, ht⟩
    have h : tK ∈ N := htop.symm ▸ Submodule.mem_top
    exact h
  exact ⟨g, hg, ⟨(Ideal.quotientEquivAlgOfEq A hI).trans
    (Ideal.quotientKerAlgEquivOfSurjective hev)⟩⟩

/-- Scalar extension of a polynomial quotient applies the coefficient map to its equations. -/
private def baseChangeModelEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} (g : List (MvPolynomial (Fin n) R)) :
    S ⊗[R] Model g ≃ₐ[S] Model (g.map (MvPolynomial.map (algebraMap R S))) := by
  let α : S ⊗[R] MvPolynomial (Fin n) R ≃ₐ[S] MvPolynomial (Fin n) S :=
    MvPolynomial.algebraTensorAlgEquiv R S
  let i : MvPolynomial (Fin n) R →ₐ[R] S ⊗[R] MvPolynomial (Fin n) R :=
    Algebra.TensorProduct.includeRight
  have he : ((Ideal.ofList g).map i.toRingHom).map α.toRingHom =
      Ideal.ofList (g.map (MvPolynomial.map (algebraMap R S))) := by
    rw [Ideal.map_map, Ideal.map_ofList]
    congr 1
    apply List.map_congr_left
    intro p _
    change α (1 ⊗ₜ[R] p) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  exact (Algebra.TensorProduct.tensorQuotientEquiv S (MvPolynomial (Fin n) R) S
    (Ideal.ofList g)).trans (Ideal.quotientEquivAlg _ _ α he.symm)

/-- Lift the equations to the larger Artin algebra and transport the original marking
through the canonical identification of special fibres. -/
theorem lifts : Lifting.{u,v,z} := by
  intro k _ n s f hf A' A π hπ D
  classical
  obtain ⟨g, hg, ⟨e⟩⟩ := presentation f D
  let : Algebra A' A := π.toAlgebra
  let : IsScalarTower A' A k := π.residueScalarTower
  choose g' hg' using fun i : Fin s =>
    MvPolynomial.map_surjective (algebraMap A' A) hπ (g i)
  have hlist : (List.ofFn g').map (MvPolynomial.map (algebraMap A' A)) = List.ofFn g := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext hg')
  have hres : (List.ofFn g').map (MvPolynomial.map A'.residue.toRingHom) = List.ofFn f := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rw [← hg i, ← hg' i, MvPolynomial.map_map]
    have heq : A'.residue.toRingHom = A.residue.toRingHom.comp (algebraMap A' A) :=
      RingHom.ext fun a => (π.residue_apply a).symm
    rw [heq]
    rfl
  let M := Model (List.ofFn g')
  let : Module.Flat A' M := KoszulFlatDeformationModels.flatModel A' _ _ hres hf
  let E := ULift.{z} M
  let e' : A ⊗[A'] E ≃ₐ[A] D :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A)
      (ULift.algEquiv : E ≃ₐ[A'] M)).trans
    ((baseChangeModelEquiv (List.ofFn g')).trans
      ((Ideal.quotientEquivAlgOfEq A (congrArg Ideal.ofList hlist)).trans e))
  let c : SpecialFibre A (A ⊗[A'] E) ≃ₐ[k] SpecialFibre A' E :=
    Algebra.TensorProduct.cancelBaseChange A' A k k E
  let D' : MarkedDeformation.{u,v,u,z} A' (B f) :=
    { carrier := E
      marking := c.symm.trans ((specialFibreCongr e').trans D.marking) }
  refine ⟨D', ⟨⟨e', ?_⟩⟩⟩
  apply AlgEquiv.ext
  intro t
  change D.marking (specialFibreCongr e' t) =
    D.marking (specialFibreCongr e' (c.symm (c t)))
  rw [AlgEquiv.symm_apply_apply]

/-- Unobstructedness and the Jacobian formula for first-order deformations. -/
theorem unobstructed : Unobstructed.{u,v,z} :=
  ⟨lifts, CompleteIntersectionTangentSpace.tangentSpace⟩

end CommutativeAlgebraNotes.LiftPolynomialCompleteIntersections
