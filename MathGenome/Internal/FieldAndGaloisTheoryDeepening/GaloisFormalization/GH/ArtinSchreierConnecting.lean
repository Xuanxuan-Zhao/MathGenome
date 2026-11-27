import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierConnecting
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.ArtinSchreierCoefficients
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.CohomologyExactSequence
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.AdditiveGaloisCohomology

namespace GaloisFormalization.GH.ArtinSchreierConnecting

open Model (ShortExactCoefficients)
open KrullLayers (AbsoluteGaloisGroup)
open ArtinSchreierCoefficients (primeFieldAction primeFieldInclusion wp quotientMap)
open Specs.GaloisFormalization.GH.ArtinSchreierConnecting

universe u v

noncomputable section

attribute [local instance] ZMod.algebra

private theorem oneTuple {G : Type v} (x : Fin 1 → G) : ![x 0] = x :=
  funext fun i => by rw [Subsingleton.elim i 0]; rfl

section Characters

variable (p : ℕ) (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]

local instance : DistribMulAction G (ZMod p) := primeFieldAction G p
local instance : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
local instance : Module (ZMod p) (PrimeCohomology p G) := primeCohomologyModule p G
local instance : Module (ZMod p) (Characters p G) := charactersModule p G

private def cocycleCharacterEquiv : continuousCocycles G (ZMod p) 1 ≃+ Characters p G where
  toFun c :=
    { toAddMonoidHom := AddMonoidHom.mk' (fun g => c.val.val ![g.toMul]) fun g h =>
        (mem_continuousCocycles_one c.val).mp c.property g.toMul h.toMul
      continuous_toFun := c.val.property.comp (continuous_pi fun i => by
        rw [Subsingleton.elim i 0]
        exact continuous_toMul) }
  invFun χ :=
    ⟨cochainOne (fun g => χ (Additive.ofMul g)) ((map_continuous χ).comp continuous_ofMul),
      (mem_continuousCocycles_one _).mpr fun g h => map_add χ (Additive.ofMul g) (Additive.ofMul h)⟩
  left_inv c := Subtype.ext (Subtype.ext (funext fun x => congrArg c.val.val (oneTuple x)))
  right_inv χ := ContinuousAddMonoidHom.ext fun _ => rfl
  map_add' _ _ := ContinuousAddMonoidHom.ext fun _ => rfl

private def classEquiv : continuousCocycles G (ZMod p) 1 ≃+ PrimeCohomology p G :=
  AddEquiv.ofBijective (continuousClass G (ZMod p) 1).toAddMonoidHom
    ⟨fun c d h => by
      obtain ⟨t, ht⟩ := (continuousClass_succ_eq_iff c d).mp h
      have ht₀ : continuousDifferential G (ZMod p) 0 t = 0 := by
        apply Subtype.ext
        funext x
        rw [← oneTuple x, differential_zero]
        exact sub_self _
      exact Subtype.ext (sub_eq_zero.mp (ht.symm.trans ht₀)),
      continuousClass_surjective 1⟩

private def characterEquiv : PrimeCohomology p G ≃ₗ[ZMod p] Characters p G :=
  let e := (classEquiv p G).symm.trans (cocycleCharacterEquiv p G)
  e.toLinearEquiv (ZMod.map_smul e)

private theorem characterEquiv_class (c : continuousCocycles G (ZMod p) 1) (g : G) :
    (characterEquiv p G).toFun (continuousClass G (ZMod p) 1 c) (Additive.ofMul g) =
      c.val.val ![g] := by
  change cocycleCharacterEquiv p G ((classEquiv p G).symm ((classEquiv p G) c)) _ = _
  rw [AddEquiv.symm_apply_apply]
  rfl

end Characters

section BaseField

variable (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
  [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul (AbsoluteGaloisGroup k S) S]

local notation "Γ" => AbsoluteGaloisGroup k S

private def baseZeroCocycle (a : k) : continuousCocycles Γ S 0 :=
  ⟨cochainZero (algebraMap k S a), (mem_continuousCocycles_zero _).mpr fun g => g.commutes a⟩

private def baseFixed : k →ₗ[ℤ] Model.fixedCoefficients Γ S ⊤ :=
  ((algebraMap k S).toAddMonoidHom.toIntLinearMap).codRestrict _ fun a =>
    (Model.mem_fixedCoefficients Γ S ⊤ (algebraMap k S a)).mpr fun g _ => g.commutes a

private def baseZeroEquiv : k ≃ₗ[ℤ] ContinuousH Γ S 0 :=
  (LinearEquiv.ofBijective (baseFixed k S) ⟨fun a b hab =>
    (algebraMap k S).injective (congrArg Subtype.val hab), fun x => by
      have hfixed : ∀ g : Γ, g x.val = x.val := fun g =>
        (Model.mem_fixedCoefficients Γ S ⊤ x.val).mp x.property g (Subgroup.mem_top g)
      obtain ⟨a, ha⟩ := (KrullLayers.mem_range_algebraMap_iff_fixed x.val).mpr hfixed
      exact ⟨a, Subtype.ext ha⟩⟩).trans (continuousHZeroEquiv Γ S).symm

private theorem baseZeroEquiv_apply (a : k) :
    baseZeroEquiv k S a = continuousClass Γ S 0 (baseZeroCocycle k S a) := by
  apply (continuousHZeroEquiv Γ S).injective
  rw [baseZeroEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (continuousHZeroEquiv_class Γ S (baseZeroCocycle k S a)).symm

end BaseField

/-- The Artin–Schreier connecting isomorphism, with the character of each root. -/
theorem artinSchreierConnecting : ConnectingIsomorphism.{u,v} := by
  unfold ConnectingIsomorphism
  intro p k S _ _ _ _ _ _ _ _
  dsimp only
  let G := AbsoluteGaloisGroup k S
  let : CharP S p := charP_of_injective_algebraMap' k p
  let : TopologicalSpace S := ⊥
  let : DiscreteTopology S := ⟨rfl⟩
  let : ContinuousSMul G S := KrullLayers.continuous_fieldAction k S
  let : DistribMulAction G (ZMod p) := primeFieldAction G p
  let : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  let : Module (ZMod p) (PrimeCohomology p G) := primeCohomologyModule p G
  let : Module (ZMod p) (Characters p G) := charactersModule p G

  obtain ⟨hi, hexact, hp⟩ := ArtinSchreierCoefficients.shortExact p k S
  obtain ⟨hiEquiv, hpEquiv⟩ := ArtinSchreierCoefficients.equivariant p k S
  let seq : ShortExactCoefficients G (ZMod p) S S :=
    { i := (primeFieldInclusion p S).toAddMonoidHom
      p := (wp p S).toAddMonoidHom
      i_equivariant := hiEquiv
      p_equivariant := hpEquiv
      i_injective := hi
      exact := hexact
      p_surjective := hp }
  obtain ⟨δ, hδ⟩ := continuousCohomology_longExact seq
  let base := baseZeroEquiv k S
  have base_natural (a : k) : seq.cohomologyP 0 (base a) = base (wp p k a) := by
    change seq.cohomologyP 0 (baseZeroEquiv k S a) = baseZeroEquiv k S (wp p k a)
    rw [baseZeroEquiv_apply, baseZeroEquiv_apply]
    change continuousClass G S 0 (Model.continuousCocycleMap (MonoidHom.id G) continuous_id
      seq.p seq.p_equivariant 0 (baseZeroCocycle k S a)) =
      continuousClass G S 0 (baseZeroCocycle k S (wp p k a))
    apply congrArg (continuousClass G S 0)
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact (ArtinSchreierCoefficients.wp_natural p (algebraMap k S) a).symm

  let fromBase : k →ₗ[ZMod p] PrimeCohomology p G :=
    ((δ 0).comp base.toLinearMap).toAddMonoidHom.toZModLinearMap p
  have fromBase_exact : Function.Exact (wp p k) fromBase.toFun := by
    intro a
    change δ 0 (base a) = 0 ↔ ∃ b, wp p k b = a
    rw [hδ.exact_right 0 (base a)]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨b, rfl⟩ := base.surjective c
      exact ⟨b, base.injective ((base_natural b).symm.trans hc)⟩
    · rintro ⟨b, rfl⟩
      exact ⟨base b, base_natural b⟩
  have hzero : Subsingleton (ContinuousH G S 1) :=
    AdditiveGaloisCohomology.continuous_additive_vanishing k S 1 (by decide)
  have δ_surjective : Function.Surjective (δ 0) := fun z =>
    (hδ.exact_left 0 z).mp (hzero.elim _ _)
  have fromBase_surjective : Function.Surjective fromBase.toFun :=
    δ_surjective.comp base.surjective
  let connect := Function.Exact.linearEquivOfSurjective (f := wp p k) (g := fromBase)
    fromBase_exact fromBase_surjective

  refine ⟨connect, characterEquiv p G, characterEquiv_class p G, ?_⟩
  intro a α hα g
  have hlift : seq.cochainP 0 (cochainZero α) = (baseZeroCocycle k S a).val :=
    Subtype.ext (funext fun _ => hα)
  obtain ⟨c, hc, hclass, -⟩ := hδ.connecting_formula 0 (baseZeroCocycle k S a) (cochainZero α) hlift
  have hconnect : connect.toFun (quotientMap p k a) = continuousClass G (ZMod p) 1 c := by
    change δ 0 (baseZeroEquiv k S a) = continuousClass G (ZMod p) 1 c
    rw [baseZeroEquiv_apply]
    exact hclass
  change primeFieldInclusion p S
    ((characterEquiv p G).toFun (connect.toFun (quotientMap p k a)) (Additive.ofMul g)) = g • α - α
  rw [hconnect, characterEquiv_class]
  exact (congrArg (fun f : continuousCochains G S 1 => f.val ![g]) hc).trans
    (differential_cochainZero α g)

end

end GaloisFormalization.GH.ArtinSchreierConnecting
