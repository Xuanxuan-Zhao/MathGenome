import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.DimensionShifting
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtExactSequences
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorExactSequences

import MathGenome.Internal.AlgebraCore.P103.Ch11.VanishingAndFlatness
namespace P103.Ch11.DimensionShifting
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence P103.Specs.Ch10.Horseshoe
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.DimensionShifting
open P103.Specs.Ch11.VanishingAndFlatness
open P103.Ch10.HomologySequence
noncomputable section
set_option linter.unusedVariables false
universe u v w

/-- Exactness identifies an injective arrow with the actual kernel. -/
def kernelEquiv {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (d : X →ₗ[ℤ] Y) (f : Y →ₗ[ℤ] Z) (hd : Function.Injective d)
    (he : Function.Exact d f) : X ≃ₗ[ℤ] LinearMap.ker f :=
  LinearEquiv.ofBijective (d.codRestrict (LinearMap.ker f)
    (fun x => (he (d x)).mpr ⟨x, rfl⟩))
    ⟨fun _ _ h => hd (congrArg Subtype.val h), by
      intro y
      obtain ⟨x, hx⟩ := (he y.val).mp y.property
      exact ⟨x, Subtype.ext hx⟩⟩

/-- These are the only zero-term arguments needed in the proof. -/
theorem connecting_bijective {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    {U V W : HomologicalComplex (ModuleCat S) c} (i : U ⟶ V) (p : V ⟶ W)
    (n m : ι) (d : Homology W n →ₗ[S] Homology U m)
    (he : SequenceExact i p n m d) (hn : Subsingleton (Homology V n))
    (hm : Subsingleton (Homology V m)) : Function.Bijective d := by
  letI := hn
  letI := hm
  exact ⟨exact_injective_of_subsingleton _ _ he.2.1,
    exact_surjective_of_subsingleton _ _ he.2.2⟩

 theorem ext_first_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : ext_firstType.{u,v,w} := by
  intro R _ K M A i p hi he hp hM B L N hL hN
  obtain ⟨hH, hs⟩ := P103.Ch11.ExtExactSequences.first_sequence
    R K M A i p hi he hp B L N hL hN
  refine ⟨hH, fun H => ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hs H
  refine ⟨δ, fun n => (hδ n).1, ?_, ?_⟩
  · intro n
    have hn := hEP R M B hM H.middle H.projective n
    have hm := hEP R M B hM H.middle H.projective (n+1)
    exact ⟨(LinearEquiv.ofBijective (δ (n+1))
      (connecting_bijective _ _ _ _ _ (hδ (n+1)).2 hn hm)).symm, rfl⟩
  · letI := hEP R M B hM H.middle H.projective 0
    have hsδ : Function.Surjective (δ 0) :=
      exact_surjective_of_subsingleton _ _ (hδ 0).2.2.2
    have hsD : Function.Surjective ((δ 0).comp
        (P103.Specs.Ch11.ExtExactSequences.homClass L B)) :=
      hsδ.comp (P103.Ch11.ExtExactSequences.homClass_bijective L B).2
    exact ⟨(hb.2.2.linearEquivOfSurjective hsD).symm, fun _ => rfl⟩

 theorem ext_second_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : ext_secondType.{u,v,w} := by
  intro R _ A P hP B I L i p hi he hp hI
  obtain ⟨δ, hδ, hb⟩ := P103.Ch11.ExtExactSequences.second_sequence
    R A P hP B I L i p hi he hp
  refine ⟨δ, fun n => (hδ n).1, ?_, ?_⟩
  · intro n
    have hn := hEI R A I hI P hP n
    have hm := hEI R A I hI P hP (n+1)
    exact ⟨(LinearEquiv.ofBijective (δ (n+1))
      (connecting_bijective _ _ _ _ _ (hδ (n+1)).2 hn hm)).symm, rfl⟩
  · letI := hEI R A I hI P hP 0
    have hsδ : Function.Surjective (δ 0) :=
      exact_surjective_of_subsingleton _ _ (hδ 0).2.2.2
    have hsD : Function.Surjective ((δ 0).comp
        (P103.Specs.Ch11.ExtExactSequences.homClass P L)) :=
      hsδ.comp (P103.Ch11.ExtExactSequences.homClass_bijective P L).2
    exact ⟨(hb.2.2.linearEquivOfSurjective hsD).symm, fun _ => rfl⟩

 theorem tor_first_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : tor_firstType.{u,v,w} := by
  intro R _ K F A i p hi he hp hF B L N hL hN
  obtain ⟨hH, hs⟩ := P103.Ch11.TorExactSequences.first_sequence
    R K F A i.hom p.hom hi he hp L N hL hN B
  refine ⟨hH, fun H => ?_⟩
  obtain ⟨⟨δ, hδ⟩, _⟩ := hs H
  refine ⟨δ, fun n => (hδ n).1, ?_, ?_⟩
  · intro n
    have hn := hTR R F B hF H.middle H.projective (n+1)
    have hm := hTR R F B hF H.middle H.projective n
    exact ⟨LinearEquiv.ofBijective (δ (n+1))
      (connecting_bijective _ _ _ _ _ (hδ (n+1)).2 hn hm), rfl⟩
  · obtain ⟨z, hz⟩ := P103.Ch11.ExtTorDefinitions.tor_zero R K L B
    obtain ⟨zF, hzF⟩ := P103.Ch11.ExtTorDefinitions.tor_zero R F H.middle B
    have hc (x : TorWith L B 0) :
        tensorMap i.hom (LinearMap.id : B →ₗ[R] B) (z x) =
          zF (homologyMap (tensorFirstMap H.inclusion B) 0 x) := by
      have hh := P103.Ch11.ExtTorDefinitions.tor_zero_natural R K F L H.middle B B
        i.hom LinearMap.id H.inclusion H.augmentation_inclusion z zF hz hzF x
      simpa only [P103.Ch11.TorExactSequences.tensorSecondMap_id, Category.comp_id] using hh.symm
    have hx := P103.Ch11.TorExactSequences.exact_equiv_middle
      (δ 0).toAddMonoidHom
      (homologyMap (tensorFirstMap H.inclusion B) 0).toAddMonoidHom
      z zF (tensorMap i.hom (LinearMap.id : B →ₗ[R] B)).toAddMonoidHom
      (hδ 0).2.2.2 hc
    let d := z.toIntLinearEquiv.toLinearMap.comp (δ 0)
    have hd : Function.Injective d := by
      letI := hTR R F B hF H.middle H.projective 0
      exact z.injective.comp (exact_injective_of_subsingleton _ _ (hδ 0).2.2.1)
    exact ⟨z, kernelEquiv d _ hd hx, hz, fun _ => rfl⟩

 theorem tor_second_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : tor_secondType.{u,v,w} := by
  intro R _ A P hP K F B i p hi he hp hF
  obtain ⟨⟨δ, hδ⟩, _⟩ := P103.Ch11.TorExactSequences.second_sequence
    R A P hP K F B i.hom p.hom hi he hp
  refine ⟨δ, fun n => (hδ n).1, ?_, ?_⟩
  · intro n
    have hn := hTL R A F hF P hP (n+1)
    have hm := hTL R A F hF P hP n
    exact ⟨LinearEquiv.ofBijective (δ (n+1))
      (connecting_bijective _ _ _ _ _ (hδ (n+1)).2 hn hm), rfl⟩
  · obtain ⟨z, hz⟩ := P103.Ch11.ExtTorDefinitions.tor_zero R A P K
    obtain ⟨zF, hzF⟩ := P103.Ch11.ExtTorDefinitions.tor_zero R A P F
    have hc (x : TorWith P K 0) :
        tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i.hom (z x) =
          zF (homologyMap (tensorSecondMap P.complex i.hom) 0 x) := by
      have hh := P103.Ch11.ExtTorDefinitions.tor_zero_natural R A A P P K F
        LinearMap.id i.hom (𝟙 P.complex) (P103.Ch10.Comparison.chainLift_id P)
        z zF hz hzF x
      simpa only [P103.Ch11.TorExactSequences.tensorFirstMap_id, Category.id_comp] using hh.symm
    have hx := P103.Ch11.TorExactSequences.exact_equiv_middle
      (δ 0).toAddMonoidHom
      (homologyMap (tensorSecondMap P.complex i.hom) 0).toAddMonoidHom
      z zF (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i.hom).toAddMonoidHom
      (hδ 0).2.2.2 hc
    let d := z.toIntLinearEquiv.toLinearMap.comp (δ 0)
    have hd : Function.Injective d := by
      letI := hTL R A F hF P hP 0
      exact z.injective.comp (exact_injective_of_subsingleton _ _ (hδ 0).2.2.1)
    exact ⟨z, kernelEquiv d _ hd hx, hz, fun _ => rfl⟩

 theorem right_ext_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : right_extType.{u,v,w} := by
  intro R _
  exact ⟨ext_first_conditional hEI hEP hLF hREI hREP hRF hTL hTR Rᵐᵒᵖ,
    ext_second_conditional hEI hEP hLF hREI hREP hRF hTL hTR Rᵐᵒᵖ⟩

 theorem connector_naturality_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : connector_naturalityType.{u,v,w} :=
  ⟨P103.Ch11.ExtExactSequences.first_natural,
    P103.Ch11.ExtExactSequences.second_natural,
    P103.Ch11.TorExactSequences.first_naturality,
    P103.Ch11.TorExactSequences.second_naturality,
    P103.Ch11.ExtTorDefinitions.ext_zero_natural,
    P103.Ch11.ExtTorDefinitions.ext_zero_natural,
    P103.Ch11.ExtTorDefinitions.tor_zero_natural⟩

 theorem scalar_compatibility_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : scalar_compatibilityType.{u,v,w} :=
  ⟨P103.Ch11.ExtExactSequences.connectors_linear,
    P103.Ch11.ExtExactSequences.connectors_linear,
    P103.Ch11.TorExactSequences.connecting_linear.1,
    P103.Ch11.TorExactSequences.connecting_linear.2,
    P103.Ch11.ExtTorDefinitions.ext_zero_linear,
    P103.Ch11.ExtTorDefinitions.ext_zero_linear,
    P103.Ch11.ExtTorDefinitions.tor_zero_linear⟩

 theorem inverse_naturality_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : inverse_naturalityType.{u,v,w} := by
  intro X Y X' Y' _ _ _ _ e e' a b h
  ext y
  apply e'.injective
  have hh := LinearMap.congr_fun h (e.symm y)
  simpa using hh.symm

 theorem cokernel_naturality_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : cokernel_naturalityType.{u,v,w} := by
  intro X Y Z X' Y' Z' _ _ _ _ _ _ f f' a h d d' c e e' he he' hc q
  obtain ⟨y, rfl⟩ := (LinearMap.range f).mkQ_surjective q
  change e' (Submodule.Quotient.mk (a y)) = c (e (Submodule.Quotient.mk y))
  rw [he', he]
  exact (LinearMap.congr_fun hc y).symm

 theorem kernel_naturality_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : kernel_naturalityType.{u,v,w} := by
  intro X Y Z X' Y' Z' _ _ _ _ _ _ g g' d d' a b e e' he he' hc x
  rw [he', he]
  exact (LinearMap.congr_fun hc x).symm


/-- Inverting a commutative square of isomorphisms. All group universes are independent. -/
theorem inverse_square {X Y X' Y' : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    (e : X ≃ₗ[ℤ] Y) (e' : X' ≃ₗ[ℤ] Y')
    (a : X →ₗ[ℤ] X') (b : Y →ₗ[ℤ] Y')
    (h : b.comp e.toLinearMap = e'.toLinearMap.comp a) :
    a.comp e.symm.toLinearMap = e'.symm.toLinearMap.comp b := by
  ext y
  apply e'.injective
  have hh := LinearMap.congr_fun h (e.symm y)
  simpa using hh.symm

/-- The degree-zero Ext action on the actual augmentation classes. -/
theorem homClass_map {R : Type u} [Ring R] {A A' : ModuleCat.{v} R}
    (P : ProjectiveChoice R A) (Q : ProjectiveChoice R A')
    {B B' : ModuleCat.{w} R} (E : ExtMaps.{u,v,w} R 0)
    (f : A' ⟶ A) (g : B ⟶ B') (h : A →ₗ[R] B) :
    E.map P Q f g (P103.Specs.Ch11.ExtExactSequences.homClass P.val B h) =
      P103.Specs.Ch11.ExtExactSequences.homClass Q.val B' (g.hom.comp (h.comp f.hom)) := by
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists R A' A Q.val P.val Q.property f.hom
  rw [E.formula P Q f g l hl]
  exact P103.Ch11.ExtExactSequences.homClass_natural P.val Q.val f g l hl h

/-- The degree-zero Tor action under every prescribed augmentation identification. -/
theorem torZero_map {R : Type u} [Ring R] {A A' : ModuleCat.{v} Rᵐᵒᵖ}
    (P : ProjectiveChoice Rᵐᵒᵖ A) (Q : ProjectiveChoice Rᵐᵒᵖ A')
    {B B' : ModuleCat.{w} R} (T : TorMaps.{u,v,w} R 0)
    (f : A ⟶ A') (g : B ⟶ B')
    (z : TorWith P.val B 0 ≃+ P103.BalancedTensor.Tensor R A B)
    (z' : TorWith Q.val B' 0 ≃+ P103.BalancedTensor.Tensor R A' B')
    (hz : ∀ q, z (homologyClass _ 0 q) = tensorMap P.val.ε LinearMap.id q.val)
    (hz' : ∀ q, z' (homologyClass _ 0 q) = tensorMap Q.val.ε LinearMap.id q.val)
    (x : TorWith P.val B 0) :
    z' (T.map P Q f g x) = tensorMap f.hom g.hom (z x) := by
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists Rᵐᵒᵖ A A' P.val Q.val P.property f.hom
  rw [T.formula P Q f g l hl]
  exact P103.Ch11.ExtTorDefinitions.tor_zero_natural R A A' P.val Q.val B B'
    f.hom g.hom l hl z z' hz hz' x

theorem ext_first_shift_natural_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : ext_first_shift_naturalType.{u,v,w} := by
  intro R _ n E F A₁ A₂ A₃ A₁' A₂' A₃' i p i' p' a b c
    hi he hp hi' he' hp' hab hbc L N L' N' hL hN hL' hN' H H' B B' g e e' hδ hε
  have hn := P103.Ch11.ExtExactSequences.first_natural R n E F A₁ A₂ A₃ A₁' A₂' A₃' i p i' p' a b c
    hi he hp hi' he' hp' hab hbc L N L' N' hL hN hL' hN' H H' B B' g
    e.symm.toLinearMap e'.symm.toLinearMap hδ hε
  exact inverse_square e.symm e'.symm _ _ hn

theorem ext_first_edge_natural_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : ext_first_edge_naturalType.{u,v,w} := by
  intro R _ E F A₁ A₂ A₃ A₁' A₂' A₃' i p i' p' a b c
    hi he hp hi' he' hp' hab hbc L N L' N' hL hN hL' hN' H H' B B' g δ ε e e' hδ hε heq heq' h
  rw [heq, heq']
  have hn := LinearMap.congr_fun (P103.Ch11.ExtExactSequences.first_natural R 0 E F A₁ A₂ A₃ A₁' A₂' A₃' i p i' p' a b c
    hi he hp hi' he' hp' hab hbc L N L' N' hL hN hL' hN' H H' B B' g
    δ ε hδ hε) (P103.Specs.Ch11.ExtExactSequences.homClass L B h)
  have hz := homClass_map ⟨L, hL⟩ ⟨L', hL'⟩ E a g h
  simp only [LinearMap.comp_apply] at hn
  rw [hz] at hn
  exact hn

theorem ext_second_shift_natural_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : ext_second_shift_naturalType.{u,v,w} := by
  intro R _ n E F A A' P Q hP hQ f B₁ B₂ B₃ B₁' B₂' B₃'
    i p i' p' a b c hi he hp hi' he' hp' hab hbc e e' hδ hε
  have hn := P103.Ch11.ExtExactSequences.second_natural R n E F A A' P Q hP hQ f B₁ B₂ B₃ B₁' B₂' B₃'
    i p i' p' a b c hi he hp hi' he' hp' hab hbc
    e.symm.toLinearMap e'.symm.toLinearMap hδ hε
  exact inverse_square e.symm e'.symm _ _ hn

theorem ext_second_edge_natural_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : ext_second_edge_naturalType.{u,v,w} := by
  intro R _ E F A A' P Q hP hQ f B₁ B₂ B₃ B₁' B₂' B₃'
    i p i' p' a b c hi he hp hi' he' hp' hab hbc δ ε e e' hδ hε heq heq' h
  rw [heq, heq']
  have hn := LinearMap.congr_fun (P103.Ch11.ExtExactSequences.second_natural R 0 E F A A' P Q hP hQ f B₁ B₂ B₃ B₁' B₂' B₃'
    i p i' p' a b c hi he hp hi' he' hp' hab hbc
    δ ε hδ hε) (P103.Specs.Ch11.ExtExactSequences.homClass P B₃ h)
  have hz := homClass_map ⟨P, hP⟩ ⟨Q, hQ⟩ E f c h
  simp only [LinearMap.comp_apply] at hn
  rw [hz] at hn
  exact hn

theorem tor_first_edge_natural_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : tor_first_edge_naturalType.{u,v,w} := by
  intro R _ A M C A' M' C' i p i' p' a b c hi he hp hi' he' hp' hab hbc
    L N L' N' H H' B B' g T1 T0 δ ε z z' e e' hδ hε hz hz' heq heq' x
  rw [heq', heq]
  have hn := LinearMap.congr_fun (P103.Ch11.TorExactSequences.first_naturality
    R A M C A' M' C' i p i' p' a b c hi he hp hi' he' hp' hab hbc
    L N L' N' H H' B B' g 0 T1 T0 δ ε hδ hε) x
  change T0.map L L' a g (δ x) = ε (T1.map N N' c g x) at hn
  rw [← hn]
  exact torZero_map L L' T0 a g z z' hz hz' (δ x)

theorem tor_second_edge_natural_conditional
    (hEI : P103.Specs.Ch11.VanishingAndFlatness.ext_injectiveType.{u,v,w})
    (hEP : P103.Specs.Ch11.VanishingAndFlatness.ext_projectiveType.{u,v,w})
    (hLF : P103.Specs.Ch11.VanishingAndFlatness.left_flat_iff_tor_oneType.{u,v,w})
    (hREI : P103.Specs.Ch11.VanishingAndFlatness.right_ext_injectiveType.{u,v,w})
    (hREP : P103.Specs.Ch11.VanishingAndFlatness.right_ext_projectiveType.{u,v,w})
    (hRF : P103.Specs.Ch11.VanishingAndFlatness.right_flat_iff_tor_oneType.{u,v,w})
    (hTL : P103.Specs.Ch11.VanishingAndFlatness.tor_left_flatType.{u,v,w})
    (hTR : P103.Specs.Ch11.VanishingAndFlatness.tor_right_flatType.{u,v,w}) : tor_second_edge_naturalType.{u,v,w} := by
  intro R _ A A' P P' a B M C B' M' C' i p i' p' b m c
    hi he hp hi' he' hp' hab hbc T1 T0 δ ε z z' e e' hδ hε hz hz' heq heq' x
  rw [heq', heq]
  have hn := LinearMap.congr_fun (P103.Ch11.TorExactSequences.second_naturality
    R A A' P P' a B M C B' M' C' i p i' p' b m c
    hi he hp hi' he' hp' hab hbc 0 T1 T0 δ ε hδ hε) x
  change T0.map P P' a b (δ x) = ε (T1.map P P' a c x) at hn
  rw [← hn]
  exact torZero_map P P' T0 a b z z' hz hz' (δ x)


/-- The inverse of a scalar-compatible group equivalence is scalar-compatible. -/
theorem equiv_smul_of_symm {S X Y : Type*} [Ring S]
    [AddCommGroup X] [AddCommGroup Y] [Module S X] [Module S Y]
    (e : X ≃ₗ[ℤ] Y) (h : ∀ (r : S) y, e.symm (r • y) = r • e.symm y)
    (r : S) (x : X) : e (r • x) = r • e x := by
  apply e.symm.injective
  rw [e.symm_apply_apply, h, e.symm_apply_apply]

/-- Scalar compatibility upgrades the very same map to a linear equivalence. -/
def linearEquivOfCompatibleScalars {S X Y : Type*} [Ring S]
    [AddCommGroup X] [AddCommGroup Y] [Module S X] [Module S Y]
    (e : X ≃ₗ[ℤ] Y) (h : ∀ (r : S) x, e (r • x) = r • e x) : X ≃ₗ[S] Y :=
  LinearEquiv.ofBijective
    { toFun := e, map_add' := e.map_add, map_smul' := h } e.bijective

end
end P103.Ch11.DimensionShifting

universe v8_closure_2f7f1a5d42588b38_u0 v8_closure_2f7f1a5d42588b38_u1 v8_closure_2f7f1a5d42588b38_u2
theorem _root_.«P103».«Ch11».«DimensionShifting».«cokernel_naturality» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«cokernel_naturalityType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«cokernel_naturality_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«connector_naturality» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«connector_naturalityType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«connector_naturality_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«ext_first» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«ext_firstType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«ext_first_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«ext_first_edge_natural» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«ext_first_edge_naturalType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«ext_first_edge_natural_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«ext_first_shift_natural» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«ext_first_shift_naturalType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«ext_first_shift_natural_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«ext_second» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«ext_secondType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«ext_second_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«ext_second_edge_natural» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«ext_second_edge_naturalType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«ext_second_edge_natural_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«ext_second_shift_natural» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«ext_second_shift_naturalType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«ext_second_shift_natural_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«inverse_naturality» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«inverse_naturalityType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«inverse_naturality_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«kernel_naturality» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«kernel_naturalityType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«kernel_naturality_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«right_ext» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«right_extType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«right_ext_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«scalar_compatibility» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«scalar_compatibilityType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«scalar_compatibility_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«tor_first» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«tor_firstType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«tor_first_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«tor_first_edge_natural» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«tor_first_edge_naturalType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«tor_first_edge_natural_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«tor_second» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«tor_secondType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«tor_second_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
theorem _root_.«P103».«Ch11».«DimensionShifting».«tor_second_edge_natural» : _root_.«P103».«Specs».«Ch11».«DimensionShifting».«tor_second_edge_naturalType».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} :=
  @_root_.«P103».«Ch11».«DimensionShifting».«tor_second_edge_natural_conditional».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2} (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«left_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_injective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_ext_projective».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«right_flat_iff_tor_one».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_left_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2}) (@_root_.«P103».«Ch11».«VanishingAndFlatness».«tor_right_flat».{v8_closure_2f7f1a5d42588b38_u0, v8_closure_2f7f1a5d42588b38_u1, v8_closure_2f7f1a5d42588b38_u2})
