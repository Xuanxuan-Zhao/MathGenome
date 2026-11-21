import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.ContinuityTests

/-!
Homeomorphisms and embeddings with their source meanings verified before
using the library map predicates. The two-point data are aliases of the
canonical shared data in Specs; true represents 1 and false represents 0.
-/

open Set Topology
universe u v w

namespace D10Topology.Ch02
open D10Topology.Ch01

@[instance_reducible] def sierpinskiTopology : TopologicalSpace Bool :=
  CharacteristicMaps.topology

noncomputable def characteristic {X : Type u} (A : Set X) : X → Bool :=
  CharacteristicMaps.chi A

section Maps
variable {X : Type u} {Y : Type v} {Z : Type w}
  [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [TopologicalSpace Z]

theorem homeomorph_iff_continuous_inverse (f : X → Y) :
    IsHomeomorph f ↔ Continuous f ∧ ∃ g : Y → X,
      Function.LeftInverse g f ∧ Function.RightInverse g f ∧ Continuous g := by
  constructor
  · intro hf
    let h := hf.homeomorph f
    exact ⟨hf.continuous, h.symm, h.left_inv, h.right_inv, h.continuous_invFun⟩
  · rintro ⟨hf, g, hleft, hright, hg⟩
    exact (Homeomorph.mk ⟨f, g, hleft, hright⟩ hf hg).isHomeomorph

theorem equiv_homeomorph_iff (e : X ≃ Y) :
    IsHomeomorph e ↔ Continuous e ∧ Continuous e.symm := by
  constructor
  · intro he
    exact ⟨he.continuous, e.continuous_symm_iff.mpr he.isOpenMap⟩
  · rintro ⟨he, hinv⟩
    exact (Homeomorph.mk e he hinv).isHomeomorph

theorem continuous_bijection_homeomorph_iff_open (f : X → Y)
    (hf : Continuous f) (hb : Function.Bijective f) :
    IsHomeomorph f ↔ IsOpenMap f :=
  ⟨fun h => h.isOpenMap, fun ho => ⟨hf, ho, hb⟩⟩

theorem continuous_bijection_homeomorph_iff_closed (f : X → Y)
    (hf : Continuous f) (hb : Function.Bijective f) :
    IsHomeomorph f ↔ IsClosedMap f := by
  constructor
  · intro h
    exact (h.homeomorph f).isClosedMap
  · intro hc
    exact ((Equiv.ofBijective f hb).toHomeomorphOfContinuousClosed hf hc).isHomeomorph

theorem embedding_iff_homeomorph_range (e : X → Y) :
    IsEmbedding e ↔ ∃ h : X ≃ₜ range e, ∀ x, (h x : Y) = e x := by
  constructor
  · intro he
    let h : X ≃ₜ range e := (Equiv.ofInjective e he.injective).toHomeomorphOfIsInducing
      (IsInducing.subtypeVal.of_comp_iff.mp he.toIsInducing)
    exact ⟨h, fun _ => rfl⟩
  · rintro ⟨h, hh⟩
    have heq : e = Subtype.val ∘ h := funext fun x => (hh x).symm
    rw [heq]
    exact IsEmbedding.subtypeVal.comp h.isEmbedding

theorem embedding_iff_induced (e : X → Y) :
    IsEmbedding e ↔ Function.Injective e ∧ tX = tY.induced e := by
  exact ⟨fun h => ⟨h.injective, h.toIsInducing.eq_induced⟩,
    fun h => ⟨⟨h.2⟩, h.1⟩⟩

theorem embedding_iff_open_preimages (e : X → Y) :
    IsEmbedding e ↔ Function.Injective e ∧ Continuous e ∧
      ∀ U : Set X, IsOpen U → ∃ V : Set Y, IsOpen V ∧ U = e ⁻¹' V := by
  constructor
  · intro he
    refine ⟨he.injective, he.continuous, ?_⟩
    intro U hU
    obtain ⟨V, hV, heq⟩ := he.toIsInducing.isOpen_iff.mp hU
    exact ⟨V, hV, heq.symm⟩
  · rintro ⟨hi, hc, ho⟩
    apply (embedding_iff_induced e).mpr
    refine ⟨hi, TopologicalSpace.ext ?_⟩
    funext U
    apply propext
    change IsOpen U ↔ ∃ V : Set Y, IsOpen V ∧ e ⁻¹' V = U
    constructor
    · intro hU
      obtain ⟨V, hV, heq⟩ := ho U hU
      exact ⟨V, hV, heq.symm⟩
    · rintro ⟨V, hV, rfl⟩
      exact hV.preimage hc

theorem embedding_iff_open_family (e : X → Y) :
    IsEmbedding e ↔ Function.Injective e ∧
      openSets tX = (fun V : Set Y => e ⁻¹' V) '' openSets tY := by
  constructor
  · intro he
    exact ⟨he.injective, he.toIsInducing.setOfPred_isOpen⟩
  · rintro ⟨hi, heq⟩
    apply (embedding_iff_open_preimages e).mpr
    refine ⟨hi, continuous_def.mpr ?_, ?_⟩
    · intro V hV
      change e ⁻¹' V ∈ openSets tX
      rw [heq]
      exact ⟨V, hV, rfl⟩
    · intro U hU
      have hmem : U ∈ openSets tX := hU
      rw [heq] at hmem
      obtain ⟨V, hV, hVU⟩ := hmem
      exact ⟨V, hV, hVU.symm⟩

theorem compose_embeddings (e : X → Y) (j : Y → Z)
    (he : IsEmbedding e) (hj : IsEmbedding j) : IsEmbedding (j ∘ e) := hj.comp he

end Maps

theorem identity_continuous_iff_finer {X : Type u} (tau sigma : TopologicalSpace X) :
    @Continuous X X sigma tau id ↔ openSets tau ⊆ openSets sigma := by
  exact continuous_id_iff_le

theorem sierpinski_isOpen_iff (U : Set Bool) :
    IsOpen[sierpinskiTopology] U ↔ U = ∅ ∨ U = {true} ∨ U = univ := by
  change (false ∈ U → true ∈ U) ↔ _
  constructor
  · intro h
    by_cases hf : false ∈ U
    · right; right
      ext b
      cases b <;> simp_all
    · by_cases ht : true ∈ U
      · right; left
        ext b
        cases b <;> simp_all
      · left
        ext b
        cases b <;> simp_all
  · rintro (rfl | rfl | rfl) <;> simp

theorem sierpinski_opens : openSets sierpinskiTopology = {∅, {true}, univ} := by
  ext U
  exact (sierpinski_isOpen_iff U).trans (by simp)

theorem characteristic_preimage_one {X : Type u} (A : Set X) :
    characteristic A ⁻¹' {true} = A := by
  classical
  ext x
  simp [characteristic, CharacteristicMaps.chi]

theorem characteristic_preimage_zero {X : Type u} (A : Set X) :
    characteristic A ⁻¹' {false} = Aᶜ := by
  classical
  ext x
  simp [characteristic, CharacteristicMaps.chi]

theorem characteristic_continuous_iff_open {X : Type u} [tX : TopologicalSpace X]
    (A : Set X) :
    @Continuous X Bool tX sierpinskiTopology (characteristic A) ↔ IsOpen A := by
  let : TopologicalSpace Bool := sierpinskiTopology
  constructor
  · intro hc
    have ho : IsOpen ({true} : Set Bool) :=
      (sierpinski_isOpen_iff _).mpr (Or.inr (Or.inl rfl))
    simpa only [characteristic_preimage_one] using ho.preimage hc
  · intro hA
    apply continuous_def.mpr
    intro V hV
    rcases (sierpinski_isOpen_iff V).mp hV with rfl | rfl | rfl
    · simpa only [preimage_empty] using (isOpen_empty : IsOpen (∅ : Set X))
    · simpa only [characteristic_preimage_one] using hA
    · simpa only [preimage_univ] using (isOpen_univ : IsOpen (univ : Set X))

theorem characteristic_discrete_continuous_iff_clopen {X : Type u}
    [tX : TopologicalSpace X] (A : Set X) :
    @Continuous X Bool tX ⊥ (characteristic A) ↔ IsClopen A := by
  let : TopologicalSpace Bool := ⊥
  constructor
  · intro hc
    have hA : IsOpen A := by
      simpa only [characteristic_preimage_one] using
        (show IsOpen ({true} : Set Bool) from trivial).preimage hc
    have hAc : IsOpen Aᶜ := by
      simpa only [characteristic_preimage_zero] using
        (show IsOpen ({false} : Set Bool) from trivial).preimage hc
    exact ⟨isOpen_compl_iff.mp hAc, hA⟩
  · intro hA
    classical
    apply continuous_def.mpr
    intro V _
    have heq : characteristic A ⁻¹' V =
        (if true ∈ V then A else ∅) ∪ (if false ∈ V then Aᶜ else ∅) := by
      classical
      ext x
      by_cases hx : x ∈ A <;> simp [characteristic, CharacteristicMaps.chi, hx]
    rw [heq]
    classical
    split_ifs <;> simp_all only [union_empty, empty_union, union_compl_self,
      isOpen_empty, isOpen_univ, hA.isOpen, hA.isClosed.isOpen_compl]

end D10Topology.Ch02
