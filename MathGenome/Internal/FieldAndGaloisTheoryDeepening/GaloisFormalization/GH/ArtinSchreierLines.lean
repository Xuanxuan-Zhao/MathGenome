import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierLines
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.ArtinSchreierConnecting
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace GaloisFormalization.GH.ArtinSchreierLines

open Specs.GaloisFormalization.GH.ArtinSchreierLines
open Specs.GaloisFormalization.GH.ArtinSchreierConnecting
  (Characters charactersModule primeCohomologyModule PrimeCohomology)
open Specs.GaloisFormalization.GH.ArtinSchreierCoefficients
  (Quotient primeFieldInclusion wp quotientMap primeFieldAction)
open KrullLayers (AbsoluteGaloisGroup LayerGroup)
open IntermediateField (fixedField adjoin)

universe u v

noncomputable section
attribute [local instance] ZMod.algebra

section Characters

variable {p : ℕ} [Fact p.Prime] {G : Type v} [Group G] [TopologicalSpace G]
  [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]

local instance : Module (ZMod p) (Characters p G) := charactersModule p G

omit [DiscreteTopology (ZMod p)] in
private theorem mem_characterKernel (χ : Characters p G) (g : G) :
    g ∈ characterKernel χ ↔ χ (Additive.ofMul g) = 0 :=
  Iff.rfl

private theorem character_smul_apply (c : ZMod p) (χ : Characters p G) (g : Additive G) :
    (c • χ) g = c * χ g := by
  let eval : Characters p G →+ ZMod p :=
    { toFun f := f g
      map_zero' := rfl
      map_add' _ _ := rfl }
  exact ZMod.map_smul eval c χ

omit [DiscreteTopology (ZMod p)] in
private theorem character_surjective {χ : Characters p G} (hχ : χ ≠ 0) :
    Function.Surjective χ := by
  have h : ∃ g, χ g ≠ 0 := by
    by_contra! hz
    exact hχ (ContinuousAddMonoidHom.ext hz)
  obtain ⟨g, hg⟩ := h
  intro y
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (y / χ g)
  refine ⟨n • g, ?_⟩
  rw [map_nsmul, nsmul_eq_mul, hn, div_mul_cancel₀ _ hg]

private theorem characterKernel_open (χ : Characters p G) :
    IsOpen (characterKernel χ : Set G) :=
  (isOpen_discrete ({0} : Set (ZMod p))).preimage
    ((map_continuous χ).comp continuous_ofMul)

private theorem characterKernel_eq_iff {χ ψ : Characters p G} (hχ : χ ≠ 0) (hψ : ψ ≠ 0) :
    characterKernel χ = characterKernel ψ ↔ ∃ c : ZMod p, c ≠ 0 ∧ ψ = c • χ := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := character_surjective hχ 1
    have hbψ : ψ b ≠ 0 := by
      intro hz
      have hm := (mem_characterKernel ψ b.toMul).mpr hz
      rw [← h] at hm
      exact one_ne_zero (hb.symm.trans ((mem_characterKernel χ b.toMul).mp hm))
    refine ⟨ψ b, hbψ, ContinuousAddMonoidHom.ext fun g => ?_⟩
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (χ g)
    have hng : χ (n • b) = χ g := by
      rw [map_nsmul, nsmul_eq_mul, hb, mul_one, hn]
    have hsub : χ (g - n • b) = 0 := by rw [map_sub, hng, sub_self]
    have hm : Additive.toMul (g - n • b) ∈ characterKernel χ :=
      (mem_characterKernel χ _).mpr hsub
    rw [h] at hm
    have hzero := (mem_characterKernel ψ _).mp hm
    change ψ (g - n • b) = 0 at hzero
    rw [map_sub, sub_eq_zero] at hzero
    rw [character_smul_apply, hzero, map_nsmul, nsmul_eq_mul, hn, mul_comm]
  · rintro ⟨c, hc, rfl⟩
    ext g
    simp only [mem_characterKernel, character_smul_apply, mul_eq_zero, hc, false_or]

end Characters

theorem characterKernels : CharacterKernels.{v} := by
  intro p G _ _ _ _ _
  exact ⟨fun χ hχ => ⟨character_surjective hχ, characterKernel_open χ, inferInstance⟩,
    fun _ _ => characterKernel_eq_iff⟩

section Lines

variable {p : ℕ} [Fact p.Prime]

private theorem exists_line_generator {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (D : Lines p V) : ∃ (x : V) (hx : x ≠ 0), D = lineOf x hx := by
  have hD := (Submodule.isAtom_iff_finrank_eq_one.mpr D.prop).ne_bot
  obtain ⟨x, hxD, hx⟩ := D.val.ne_bot_iff.mp hD
  exact ⟨x, hx, Subtype.ext (eq_span_singleton_of_mem_of_finrank_eq_one D.prop hxD hx)⟩

private theorem lineOf_eq_iff {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    lineOf (p := p) x hx = lineOf y hy ↔ ∃ c : ZMod p, c ≠ 0 ∧ y = c • x := by
  constructor
  · intro h
    have hmem : y ∈ Submodule.span (ZMod p) {x} := by
      change y ∈ (lineOf x hx).val
      rw [h]
      exact Submodule.mem_span_singleton_self y
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨c, ?_, hc.symm⟩
    rintro rfl
    exact hy (by simpa using hc.symm)
  · rintro ⟨c, _, rfl⟩
    apply Subtype.ext
    exact (eq_span_singleton_of_mem_of_finrank_eq_one (lineOf x hx).prop
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) hy)

private def lineMap {V W : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (f : V ≃ₗ[ZMod p] W) :
    Lines p V ≃ Lines p W where
  toFun D := ⟨D.val.map f.toLinearMap, (f.finrank_map_eq D.val).trans D.prop⟩
  invFun D := ⟨D.val.map f.symm.toLinearMap, (f.symm.finrank_map_eq D.val).trans D.prop⟩
  left_inv D := Subtype.ext (by simp [← Submodule.map_comp])
  right_inv D := Subtype.ext (by simp [← Submodule.map_comp])

private theorem lineMap_lineOf {V W : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (f : V ≃ₗ[ZMod p] W) (x : V)
    (hx : x ≠ 0) (hfx : f x ≠ 0) :
    lineMap f (lineOf x hx) = lineOf (f x) hfx := by
  apply Subtype.ext
  change (Submodule.span _ {x}).map f.toLinearMap = Submodule.span _ {f x}
  rw [Submodule.map_span, Set.image_singleton]
  rfl

end Lines

section Fields

variable {p : ℕ} [Fact p.Prime] {k : Type u} {S : Type v}
  [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
  [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]

local notation "Γ" => AbsoluteGaloisGroup k S

local instance : Module (ZMod p) (Characters p Γ) := charactersModule p Γ

omit [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)] in
private theorem card_primeField : Nat.card (Multiplicative (ZMod p)) = p := by
  change Nat.card (ZMod p) = p
  rw [Nat.card_eq_fintype_card, ZMod.card]

private theorem fixingSubgroup_fixedField_characterKernel (χ : Characters p Γ) :
    (fixedField (characterKernel χ)).fixingSubgroup = characterKernel χ :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨characterKernel χ, (characterKernel χ).isClosed_of_isOpen (characterKernel_open χ)⟩

private def fieldOfCharacter {χ : Characters p Γ} (hχ : χ ≠ 0) : CyclicLayers p k S := by
  let H : Subgroup Γ := characterKernel χ
  let F := fixedField H
  have hfix : F.fixingSubgroup = H := fixingSubgroup_fixedField_characterKernel χ
  have hprop : IsOpen (F.fixingSubgroup : Set Γ) ∧ F.fixingSubgroup.Normal := by
    rw [hfix]
    exact ⟨characterKernel_open χ, inferInstance⟩
  obtain ⟨hfinite, hgalois⟩ :=
    (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois F).mp hprop
  let E : FiniteGaloisIntermediateField k S :=
    { toIntermediateField := F
      finiteDimensional := hfinite
      isGalois := hgalois }
  have hk : (KrullLayers.restrict E).toMonoidHom.ker = H :=
    (KrullLayers.restrict_ker E).trans hfix
  let e₁ := QuotientGroup.liftEquiv H (KrullLayers.restrict_surjective E) hk.symm
  let e₂ := QuotientGroup.liftEquiv H (φ := χ.toAddMonoidHom.toMultiplicativeRight)
    (character_surjective hχ) rfl
  let e := e₁.symm.trans e₂
  have hcard : Nat.card (LayerGroup E) = p :=
    (Nat.card_congr e.toEquiv).trans (card_primeField (p := p))
  exact ⟨E, (IsGalois.card_aut_eq_finrank k E).symm.trans hcard, isCyclic_of_prime_card hcard⟩

private theorem fieldOfCharacter_eq_iff {χ ψ : Characters p Γ} (hχ : χ ≠ 0) (hψ : ψ ≠ 0) :
    fieldOfCharacter hχ = fieldOfCharacter hψ ↔ characterKernel χ = characterKernel ψ := by
  constructor
  · intro h
    have he := congrArg (fun E : CyclicLayers p k S => E.val.toIntermediateField) h
    change fixedField (characterKernel χ) = fixedField (characterKernel ψ) at he
    have hk := congrArg IntermediateField.fixingSubgroup he
    rw [fixingSubgroup_fixedField_characterKernel, fixingSubgroup_fixedField_characterKernel] at hk
    exact hk
  · intro h
    apply Subtype.ext
    apply FiniteGaloisIntermediateField.val_injective
    exact congrArg fixedField h

private def layerCharacter (E : FiniteGaloisIntermediateField k S)
    (e : LayerGroup E ≃* Multiplicative (ZMod p)) : Characters p Γ where
  toAddMonoidHom := (e.toMonoidHom.comp (KrullLayers.restrict E).toMonoidHom).toAdditiveLeft
  continuous_toFun := (continuous_of_discreteTopology (f := fun x : LayerGroup E =>
    (e x).toAdd)).comp ((map_continuous (KrullLayers.restrict E)).comp continuous_toMul)

omit [DiscreteTopology (ZMod p)] in
private theorem layerCharacter_ne_zero (E : FiniteGaloisIntermediateField k S)
    (e : LayerGroup E ≃* Multiplicative (ZMod p)) : layerCharacter E e ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := KrullLayers.restrict_surjective E (e.symm (Multiplicative.ofAdd 1))
  have hz := DFunLike.congr_fun h (Additive.ofMul g)
  change (e (KrullLayers.restrict E g)).toAdd = 0 at hz
  rw [hg, e.apply_symm_apply] at hz
  exact one_ne_zero hz

omit [DiscreteTopology (ZMod p)] in
private theorem layerCharacter_kernel (E : FiniteGaloisIntermediateField k S)
    (e : LayerGroup E ≃* Multiplicative (ZMod p)) :
    characterKernel (layerCharacter E e) = KrullLayers.layerKernel E := by
  rw [← KrullLayers.restrict_ker]
  ext g
  rw [mem_characterKernel, MonoidHom.mem_ker]
  change e (KrullLayers.restrict E g) = 1 ↔ KrullLayers.restrict E g = 1
  rw [← e.map_one, e.injective.eq_iff]

private theorem fieldOfLayerCharacter (E : CyclicLayers p k S)
    (e : LayerGroup E.val ≃* Multiplicative (ZMod p)) :
    fieldOfCharacter (layerCharacter_ne_zero E.val e) = E := by
  apply Subtype.ext
  apply FiniteGaloisIntermediateField.val_injective
  change fixedField (characterKernel (layerCharacter E.val e)) = E.val.toIntermediateField
  rw [layerCharacter_kernel, KrullLayers.fixedField_layerKernel]

private theorem exists_character_field (E : CyclicLayers p k S) :
    ∃ (χ : Characters p Γ) (hχ : χ ≠ 0), fieldOfCharacter hχ = E := by
  let e : LayerGroup E.val ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq ((IsGalois.card_aut_eq_finrank k E.val).trans E.prop.1)
      (card_primeField (p := p))
  exact ⟨layerCharacter E.val e, layerCharacter_ne_zero E.val e, fieldOfLayerCharacter E e⟩

private def characterLineField (D : Lines p (Characters p Γ)) : CyclicLayers p k S :=
  fieldOfCharacter (exists_line_generator D).choose_spec.choose

private theorem characterLineField_lineOf (χ : Characters p Γ) (hχ : χ ≠ 0) :
    characterLineField (lineOf χ hχ) = fieldOfCharacter hχ := by
  let h := exists_line_generator (lineOf (p := p) χ hχ)
  exact (fieldOfCharacter_eq_iff h.choose_spec.choose hχ).mpr
    ((characterKernel_eq_iff h.choose_spec.choose hχ).mpr
      ((lineOf_eq_iff h.choose_spec.choose hχ).mp h.choose_spec.choose_spec.symm))

private def characterLineEquiv : Lines p (Characters p Γ) ≃ CyclicLayers p k S :=
  Equiv.ofBijective characterLineField ⟨by
    intro D E h
    obtain ⟨χ, hχ, rfl⟩ := exists_line_generator D
    obtain ⟨ψ, hψ, rfl⟩ := exists_line_generator E
    rw [characterLineField_lineOf, characterLineField_lineOf] at h
    exact (lineOf_eq_iff hχ hψ).mpr ((characterKernel_eq_iff hχ hψ).mp
      ((fieldOfCharacter_eq_iff hχ hψ).mp h)), by
    intro E
    obtain ⟨χ, hχ, h⟩ := exists_character_field E
    exact ⟨lineOf χ hχ, (characterLineField_lineOf χ hχ).trans h⟩⟩

private theorem characterLineEquiv_lineOf (χ : Characters p Γ) (hχ : χ ≠ 0) :
    characterLineEquiv (lineOf χ hχ) = fieldOfCharacter hχ :=
  characterLineField_lineOf χ hχ

private theorem adjoin_fixingSubgroup_iff (α : S) (g : Γ) :
    g ∈ (adjoin k {α}).fixingSubgroup ↔ g α = α := by
  constructor
  · intro hg
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg α
      (IntermediateField.subset_adjoin k {α} rfl)
  · intro h
    let F := adjoin k {α}
    have heq : g.toAlgHom.comp F.val = F.val := by
      apply IntermediateField.adjoin_algHom_ext k
      intro x hx
      change g x = x
      have hx' : x = α := hx
      rw [hx']
      exact h
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      fun x hx => DFunLike.congr_fun heq ⟨x, hx⟩

omit [DiscreteTopology (ZMod p)] in
private theorem rootCharacter_kernel [CharP S p] (α : S) (χ : Characters p Γ)
    (hχ : ∀ g : Γ, primeFieldInclusion p S (χ (Additive.ofMul g)) = g • α - α) :
    characterKernel χ = (adjoin k {α}).fixingSubgroup := by
  have hinj : Function.Injective (primeFieldInclusion p S) :=
    ArtinSchreierCoefficients.primeFieldInclusion_injective p S
  ext g
  rw [mem_characterKernel, adjoin_fixingSubgroup_iff]
  rw [← hinj.eq_iff, hχ g, map_zero, sub_eq_zero]
  rfl

end Fields

/-- The lines of Artin–Schreier classes, or equivalently of their continuous
characters, classify the embedded cyclic degree-p extensions. -/
theorem artinSchreierLines : LineClassification.{u,v} := by
  unfold LineClassification
  intro p k S _ _ _ _ _ _ _ _
  dsimp only
  let G := AbsoluteGaloisGroup k S
  let : CharP S p := charP_of_injective_algebraMap' k p
  let : DistribMulAction G (ZMod p) := primeFieldAction G p
  let : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  let : Module (ZMod p) (PrimeCohomology p G) := primeCohomologyModule p G
  let : Module (ZMod p) (Characters p G) := charactersModule p G
  obtain ⟨connect, toCharacter, _, hroot⟩ :=
    ArtinSchreierConnecting.artinSchreierConnecting p k S
  let e := connect.trans toCharacter
  let el := lineMap e
  let ef : Lines p (Characters p G) ≃ CyclicLayers p k S := characterLineEquiv
  let ec := el.trans ef
  have hfields (a : k) (α : S) (hα : wp p S α = algebraMap k S a)
      (ha : quotientMap p k a ≠ 0) :
      characterKernel (e (quotientMap p k a)) = (adjoin k {α}).fixingSubgroup ∧
      (ec (lineOf (quotientMap p k a) ha)).val.toIntermediateField = adjoin k {α} := by
    have hk := rootCharacter_kernel α (e (quotientMap p k a)) (hroot a α hα)
    have hχ : e (quotientMap p k a) ≠ 0 := fun h => ha (e.injective (h.trans (e.map_zero).symm))
    refine ⟨hk, ?_⟩
    change (ef (lineMap e (lineOf (quotientMap p k a) ha))).val.toIntermediateField = _
    rw [lineMap_lineOf e _ ha hχ,
      show ef (lineOf (e (quotientMap p k a)) hχ) = fieldOfCharacter hχ from
        characterLineEquiv_lineOf _ _]
    change fixedField (characterKernel (e (quotientMap p k a))) = _
    rw [hk, InfiniteGalois.fixedField_fixingSubgroup]
  refine ⟨e, el, ef, ec, fun _ => rfl, fun _ => rfl, ?_, hroot, hfields, ?_, ?_⟩
  · intro χ hχ
    rw [show ef (lineOf χ hχ) = fieldOfCharacter hχ from characterLineEquiv_lineOf χ hχ]
    rfl
  · intro E f
    refine ⟨layerCharacter E.val f, layerCharacter_ne_zero E.val f, fun _ => rfl, ?_⟩
    apply ef.injective
    rw [Equiv.apply_symm_apply]
    exact ((characterLineEquiv_lineOf _ _).trans (fieldOfLayerCharacter E f)).symm

  · intro E
    obtain ⟨x, hx, hline⟩ := exists_line_generator (ec.symm E)
    have hq : Function.Surjective (quotientMap p k) :=
      (LinearMap.range (wp p k)).mkQ_surjective
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨α, hα⟩ := (ArtinSchreierCoefficients.shortExact p k S).2.2 (algebraMap k S a)
    have hE : E = ec (lineOf (quotientMap p k a) hx) := by
      rw [← hline, Equiv.apply_symm_apply]
    exact ⟨a, α, hx, hα, hline, hE ▸ (hfields a α hα hx).2⟩

end

end GaloisFormalization.GH.ArtinSchreierLines
