import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.VirtualCharacterRing
import MathGenome.Internal.AlgebraCore.P103.Ch08.RegularMultiplicity
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterConstructions
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic

noncomputable section
universe u v w
namespace P103.Ch09.VirtualCharacterRing
open P103.Ch08 VirtualCharacterSpecs

/-- The complex virtual-character ring, with the canonical pointwise operations. -/
def virtualCharacterRing : Expected.ringType.{u} := Expected.ringValue

/-- Choose finite coordinates and transport the operators. This proves that
`Ordinary` covers all finite-dimensional spaces, in every universe. -/
theorem ordinary_of_rep : Expected.ordinary_of_repType.{u,v} := by
  intro G _ V _ _ _ ρ
  let e := (Module.finBasis ℂ V).equivFun
  let σ : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
    e.conjRingEquiv.toMonoidHom.comp ρ
  refine ⟨Module.finrank ℂ V, σ, ?_⟩
  funext g
  exact LinearMap.trace_conj' (ρ g) e

theorem ordinary_zero {G : Type u} [Group G] : Ordinary G 0 := by
  have h := ordinary_of_rep (Representation.trivial ℂ G (Fin 0 → ℂ))
  convert h using 1
  funext g
  simp [CharacterSpecs.characterValue, Representation.trivial]

theorem ordinary_one {G : Type u} [Group G] : Ordinary G 1 := by
  have h := ordinary_of_rep (Representation.trivial ℂ G ℂ)
  convert h using 1
  funext g
  simp [CharacterSpecs.characterValue, Representation.trivial]

theorem ordinary_add {G : Type u} [Group G] {a b : G → ℂ}
    (ha : Ordinary G a) (hb : Ordinary G b) : Ordinary G (a + b) := by
  obtain ⟨n, ρ, rfl⟩ := ha
  obtain ⟨m, σ, rfl⟩ := hb
  convert ordinary_of_rep (CharacterSpecs.sumValue ρ σ) using 1
  funext g
  exact (character_directSum ρ σ g).symm

theorem ordinary_mul {G : Type u} [Group G] {a b : G → ℂ}
    (ha : Ordinary G a) (hb : Ordinary G b) : Ordinary G (a * b) := by
  obtain ⟨n, ρ, rfl⟩ := ha
  obtain ⟨m, σ, rfl⟩ := hb
  convert ordinary_of_rep (CharacterSpecs.tensorValue ρ σ) using 1
  funext g
  exact (character_diagonal ρ σ g).symm

/-- Ring closure introduces only formal differences: tensor products of
ordinary characters are ordinary characters. -/
theorem difference : Expected.differenceType.{u} := by
  intro G _ f
  constructor
  · intro hf
    induction hf using Subring.closure_induction with
    | mem a ha =>
      exact ⟨a, 0, ha, ordinary_zero, (sub_zero a).symm⟩
    | zero => exact ⟨0, 0, ordinary_zero, ordinary_zero, by simp⟩
    | one => exact ⟨1, 0, ordinary_one, ordinary_zero, by simp⟩
    | add a b ha hb ia ib =>
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ia
      obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := ib
      exact ⟨a₁ + b₁, a₂ + b₂, ordinary_add ha₁ hb₁,
        ordinary_add ha₂ hb₂, by ring⟩
    | neg a ha ia =>
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ia
      exact ⟨a₂, a₁, ha₂, ha₁, by ring⟩
    | mul a b ha hb ia ib =>
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ia
      obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := ib
      refine ⟨a₁ * b₁ + a₂ * b₂, a₁ * b₂ + a₂ * b₁,
        ordinary_add (ordinary_mul ha₁ hb₁) (ordinary_mul ha₂ hb₂),
        ordinary_add (ordinary_mul ha₁ hb₂) (ordinary_mul ha₂ hb₁), ?_⟩
      ring
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact (virtualSubring G).sub_mem (Subring.subset_closure ha) (Subring.subset_closure hb)

/-- The concrete ring lands in class functions, with the original complex
values and the pointwise ring operations. -/
theorem classFunctions : Expected.classFunctionsType.{u} := by
  intro G _
  apply Subring.closure_le.mpr
  rintro a ⟨n, ρ, rfl⟩ g h
  exact character_conjugate ρ g h

def classFunctionEmbedding {G : Type u} [Group G] :
    VirtualCharacterSpecs.Ring G →+* VirtualCharacterSpecs.classFunctions G :=
  (virtualSubring G).inclusion classFunctions

theorem classFunctionEmbedding_injective {G : Type u} [Group G] :
    Function.Injective (classFunctionEmbedding (G := G)) := by
  intro a b h
  exact Subtype.ext (congrArg (fun z : VirtualCharacterSpecs.classFunctions G => z.1) h)

theorem embedding : Expected.embeddingType.{u} := by
  intro G _
  exact ⟨classFunctionEmbedding, classFunctionEmbedding_injective, fun _ => rfl⟩

def actual : Expected.actualType.{u,v} := Expected.actualValue

theorem actual_add : Expected.actualAdditionType.{u,v,w} := by
  intro G _ V _ _ _ W _ _ _ ρ σ hρ hσ hs
  apply Subtype.ext
  funext g
  exact character_directSum ρ σ g

theorem actual_mul : Expected.actualProductType.{u,v,w} := by
  intro G _ V _ _ _ W _ _ _ ρ σ hρ hσ hs
  apply Subtype.ext
  funext g
  exact character_diagonal ρ σ g

theorem actual_classification : Expected.actualClassificationType.{u,v,w} := by
  intro G _ _ V _ _ _ W _ _ _ ρ σ
  exact (RegularMultiplicity.character_classification ρ σ).symm

/-- Restriction preserves the integral character lattice directly. -/
def restriction : Expected.restrictionType.{u} := by
  intro G _ H
  let r : (G → ℂ) →+* (H → ℂ) :=
    { toFun := fun f h => f h
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  have hr : ∀ f ∈ virtualSubring G, r f ∈ virtualSubring H := by
    intro f hf
    apply Subring.closure_induction (p := fun f _ => r f ∈ virtualSubring H)
      (fun a ha => ?_) (map_zero r ▸ (virtualSubring H).zero_mem)
      (map_one r ▸ (virtualSubring H).one_mem)
      (fun a b ha hb ia ib => by simpa only [map_add] using (virtualSubring H).add_mem ia ib)
      (fun a ha ia => by simpa only [map_neg] using (virtualSubring H).neg_mem ia)
      (fun a b ha hb ia ib => by simpa only [map_mul] using (virtualSubring H).mul_mem ia ib) hf
    obtain ⟨n, ρ, rfl⟩ := ha
    exact Subring.subset_closure (ordinary_of_rep (P103.Ch09.restrict H ρ))
  exact
    { toFun := fun f => ⟨r f, hr f f.2⟩
      map_zero' := Subtype.ext (map_zero r)
      map_one' := Subtype.ext (map_one r)
      map_add' := fun a b => Subtype.ext (map_add r a.1 b.1)
      map_mul' := fun a b => Subtype.ext (map_mul r a.1 b.1) }

theorem restriction_formula : Expected.restrictionFormulaType (@restriction) := by
  intro G _ H f h
  rfl

theorem restriction_agreement : Expected.restrictionExistsType.{u,v} := by
  intro G _ H
  refine ⟨restriction H, restriction_formula H, ?_⟩
  intro V _ _ _ ρ x hx
  funext h
  change x.1 h = CharacterSpecs.characterValue ρ h
  exact congrFun hx h

theorem ordinaryMonoid_iff {G : Type u} [Group G] (a : G → ℂ) :
    a ∈ ordinaryMonoid G ↔ Ordinary G a := by
  constructor
  · intro ha
    induction ha using AddSubmonoid.closure_induction with
    | mem a ha => exact ha
    | zero => exact ordinary_zero
    | add a b ha hb ia ib => exact ordinary_add ia ib
  · intro h
    exact AddSubmonoid.subset_closure h

/-- Differences determine every extension of an ordinary-character additive
map. Equality of two differences is precisely equality of the crossed sums. -/
theorem difference_well_defined {G : Type u} [Group G]
    {A : Type v} [AddCommGroup A] (F : ordinaryMonoid G →+ A)
    (a b c d : ordinaryMonoid G) (h : a.1 - b.1 = c.1 - d.1) :
    F a - F b = F c - F d := by
  apply sub_eq_sub_iff_add_eq_add.mpr
  rw [← map_add, ← map_add]
  congr 1
  apply Subtype.ext
  exact sub_eq_sub_iff_add_eq_add.mp h

/-- The concrete character ring is the group completion, not merely a ring
containing ordinary characters. -/
theorem completion : Expected.completionType.{u,v} := by
  intro G _ A _ F
  classical
  have hd (x : VirtualCharacterSpecs.Ring G) :
      ∃ a b : ordinaryMonoid G, x.1 = a.1 - b.1 := by
    obtain ⟨a, b, ha, hb, hx⟩ := (difference x.1).mp x.2
    exact ⟨⟨a, (ordinaryMonoid_iff a).mpr ha⟩,
      ⟨b, (ordinaryMonoid_iff b).mpr hb⟩, hx⟩
  choose a b hab using hd
  let L (x : VirtualCharacterSpecs.Ring G) := F (a x) - F (b x)
  have eval (x : VirtualCharacterSpecs.Ring G) (c d : ordinaryMonoid G)
      (h : x.1 = c.1 - d.1) : L x = F c - F d :=
    difference_well_defined F _ _ _ _ ((hab x).symm.trans h)
  let f : VirtualCharacterSpecs.Ring G →+ A :=
    { toFun := L
      map_zero' := by
        rw [eval 0 0 0 (by simp), map_zero, sub_self]
      map_add' := by
        intro x y
        rw [eval (x + y) (a x + a y) (b x + b y) (by
          change x.1 + y.1 = _
          rw [hab x, hab y]
          simp only [AddSubmonoid.coe_add]
          abel), map_add, map_add]
        dsimp [L]
        abel }
  have hf : f.comp (ordinaryInclusion G) = F := by
    ext c
    change L (ordinaryInclusion G c) = F c
    rw [eval _ c 0 (by simp [ordinaryInclusion]), map_zero, sub_zero]
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  ext x
  have hx : x = ordinaryInclusion G (a x) - ordinaryInclusion G (b x) :=
    Subtype.ext (hab x)
  rw [hx, map_sub, map_sub]
  have eqs (c : ordinaryMonoid G) : f' (ordinaryInclusion G c) =
      f (ordinaryInclusion G c) := by
    exact (congrArg (fun h : ordinaryMonoid G →+ A => h c) hf').trans
      (congrArg (fun h : ordinaryMonoid G →+ A => h c) hf).symm
  rw [eqs, eqs]

/-- The trace is the sum of diagonal block traces, also when the blocks have
unequal dimensions or some block spaces are zero. -/
theorem trace_pi {I : Type*} [Fintype I] [DecidableEq I] (X : I → Type*)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, FiniteDimensional ℂ (X i)] (f : (∀ i, X i) →ₗ[ℂ] (∀ i, X i)) :
    LinearMap.trace ℂ _ f = ∑ i, LinearMap.trace ℂ (X i)
      (((LinearMap.proj i).comp f).comp (LinearMap.single ℂ X i)) := by
  classical
  have hf : f = ∑ i, (LinearMap.single ℂ X i).comp ((LinearMap.proj i).comp f) := by
    ext x j
    simp [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.single_apply]
  conv_lhs => rw [hf]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact LinearMap.trace_comp_comm' _ _

theorem trace_piMap {I : Type*} [Fintype I] (X : I → Type*)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, FiniteDimensional ℂ (X i)] (f : ∀ i, X i →ₗ[ℂ] X i) :
    LinearMap.trace ℂ _ (LinearMap.piMap f) = ∑ i, LinearMap.trace ℂ _ (f i) := by
  classical
  rw [trace_pi X]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ext x
  simp [LinearMap.comp_apply, LinearMap.piMap, LinearMap.single_apply]

open scoped MonoidAlgebra
open RegularMultiplicitySpecs

/-- The actual semisimple module decomposition supplies a character expansion,
with natural-number coefficients and without a dimension-counting assumption
on the space of class functions. -/
theorem character_expansion {G : Type u} [Group G] [Fintype G]
    (C : Family G) (hEx : Exhaustive.{u,v} C)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ m : Fin C.n → ℕ, CharacterSpecs.characterValue ρ =
      ∑ i, (m i : ℂ) • CharacterSpecs.characterValue (idealRepresentation (C.space i)) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := RegularMultiplicity.exists_decomposition C hEx ρ
  let M := ∀ i : Fin C.n, Fin (m i) → C.space i
  let τ : Representation ℂ G M := Representation.ofModule' M
  let f : ρ.asModule ≃ₗ[ℂ[G]] τ.asModule :=
    (e.trans DFinsupp.linearEquivFunOnFintype).trans
      (RegularMultiplicity.ofModuleModuleEquiv M).symm
  refine ⟨m, (RegularMultiplicity.character_of_equiv
    (RegularMultiplicity.representationEquivOfModuleEquiv f)).trans ?_⟩
  funext g
  change LinearMap.trace ℂ M (LinearMap.piMap (fun i : Fin C.n =>
    LinearMap.piMap (fun _ : Fin (m i) => idealRepresentation (C.space i) g))) = _
  rw [trace_piMap]
  simp only [trace_piMap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- Pairing with a fixed function is complex-linear in its first variable. -/
def pairingLinear {G : Type u} [Fintype G] (h : G → ℂ) : (G → ℂ) →ₗ[ℂ] ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, star (h g) • LinearMap.proj g

theorem pairingLinear_apply {G : Type u} [Fintype G] (h f : G → ℂ) :
    pairingLinear h f = UnitaritySpecs.functionPairingValue f h := by
  simp [pairingLinear, UnitaritySpecs.functionPairingValue, smul_eq_mul, mul_comm]

theorem irreducible_pairing {G : Type u} [Group G] [Fintype G]
    (C : Family G) (hC : Valid C) (i j : Fin C.n) :
    pairingLinear (CharacterSpecs.characterValue (idealRepresentation (C.space i)))
      (CharacterSpecs.characterValue (idealRepresentation (C.space j))) =
      if i = j then 1 else 0 := by
  classical
  rw [pairingLinear_apply, (character_pairing _ _).1]
  let e := (Representation.IntertwiningMap.equivLinearMapAsModule
    (idealRepresentation (C.space i)) (idealRepresentation (C.space j))).trans
      (RegularMultiplicity.homCongr (RegularMultiplicity.idealModuleEquiv (C.space i))
        (RegularMultiplicity.idealModuleEquiv (C.space j)))
  rw [e.finrank_eq, RegularMultiplicity.finrank_ideal_hom C hC]
  split <;> simp

/-- Irreducible ordinary characters form an integral basis of the very subring
constructed above. The proof uses a real module decomposition for spanning and
Schur orthogonality for independence. -/
theorem irreducible_basis : Expected.irreducibleBasisType.{u} := by
  intro G _ _ C hC hEx
  classical
  let v : Fin C.n → VirtualCharacterSpecs.Ring G := fun i =>
    actual (idealRepresentation (C.space i))
  have hlin : LinearIndependent ℤ v := by
    apply Fintype.linearIndependent_iff.mpr
    intro z hz i
    have he : ∑ j, (z j : ℂ) *
        pairingLinear (CharacterSpecs.characterValue (idealRepresentation (C.space i)))
          (CharacterSpecs.characterValue (idealRepresentation (C.space j))) = 0 := by
      have hv : ∑ j, z j • CharacterSpecs.characterValue
          (idealRepresentation (C.space j)) = 0 := by
        have h := congrArg (virtualSubring G).subtype.toAddMonoidHom hz
        simp only [map_sum, map_zsmul, map_zero] at h
        exact h
      have h := congrArg (pairingLinear
        (CharacterSpecs.characterValue (idealRepresentation (C.space i)))) hv
      simp only [map_sum, map_zsmul, map_zero] at h
      simpa only [zsmul_eq_mul] using h
    simp_rw [irreducible_pairing C hC] at he
    simpa using he
  have ordinary_span (a : G → ℂ) (ha : Ordinary G a) :
      (⟨a, Subring.subset_closure ha⟩ : VirtualCharacterSpecs.Ring G) ∈
        Submodule.span ℤ (Set.range v) := by
    obtain ⟨n, ρ, rfl⟩ := ha
    obtain ⟨m, hm⟩ := character_expansion C
      (RegularMultiplicity.exhaustive_from_regular C hEx) ρ
    have he : actual ρ = ∑ i, (m i : ℤ) • v i := by
      apply Subtype.ext
      funext g
      have h := congrFun hm g
      simpa [v, actual, Expected.actualValue, Pi.smul_apply, smul_eq_mul,
        zsmul_eq_mul] using h
    change actual ρ ∈ _
    rw [he]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i)))
  have hspan : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro f hf
    obtain ⟨a, b, ha, hb, hab⟩ := (difference f.1).mp f.2
    have he : f = (⟨a, Subring.subset_closure ha⟩ : VirtualCharacterSpecs.Ring G) -
        ⟨b, Subring.subset_closure hb⟩ := Subtype.ext hab
    rw [he]
    exact Submodule.sub_mem _ (ordinary_span a ha) (ordinary_span b hb)
  refine ⟨Module.Basis.mk hlin hspan, ?_⟩
  intro i
  rw [Module.Basis.mk_apply]
  rfl

theorem free_abelian : Expected.freeAbelianType.{u} := by
  intro G _ _
  classical
  letI := Fintype.ofFinite G
  obtain ⟨C, hC, hEx⟩ := RegularMultiplicity.finite_family.{u,u} (G := G)
  exact ⟨C, hC, hEx, irreducible_basis C hC hEx⟩

namespace Induction
set_option maxHeartbeats 800000
open P103.Ch09
variable {G : Type u} [Group G] (H : Subgroup G)
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W]
attribute [local instance] inducedScalarModule rightSubgroupModule

/-- The established tensor/function comparison, bundled equivariantly. -/
def functionRepresentationEquiv (ρ : Representation ℂ H V) :
    (induction H ρ).Equiv (functionAction H ρ) :=
  Representation.Equiv.mk (functionEquiv H ρ) (by
    intro g
    apply LinearMap.ext
    intro x
    exact functionEquiv_equivariant H ρ g x)

/-- Induction carries equivariant isomorphisms to equivariant isomorphisms.
The proof uses the representative-free function model. -/
def equiv {ρ : Representation ℂ H V} {σ : Representation ℂ H W}
    (e : ρ.Equiv σ) : (induction H ρ).Equiv (induction H σ) := by
  let f : functions H ρ ≃ₗ[ℂ] functions H σ :=
    { __ := functionMap ρ e.toIntertwiningMap
      invFun := functionMap σ e.symm.toIntertwiningMap
      left_inv := by intro x; ext g; exact e.symm_apply_apply _
      right_inv := by intro x; ext g; exact e.apply_symm_apply _ }
  let ef : (functionAction H ρ).Equiv (functionAction H σ) :=
    Representation.Equiv.mk f (by
      intro g
      apply LinearMap.ext
      intro x
      exact functionMap_action ρ e.toIntertwiningMap g x)
  exact (functionRepresentationEquiv H ρ).trans
    (ef.trans (functionRepresentationEquiv H σ).symm)

/-- Finite direct sums commute with induction, as actual equivariant spaces.
The two function projections and their pointwise pairing are mutual inverses. -/
def prodEquiv (ρ : Representation ℂ H V) (σ : Representation ℂ H W) :
    (induction H (ρ.prod σ)).Equiv ((induction H ρ).prod (induction H σ)) := by
  let f : functions H (ρ.prod σ) ≃ₗ[ℂ] (functions H ρ × functions H σ) :=
    { toFun := fun x =>
        (functionMap (ρ.prod σ) (Representation.IntertwiningMap.fst ℂ ρ σ) x,
         functionMap (ρ.prod σ) (Representation.IntertwiningMap.snd ℂ ρ σ) x)
      invFun := fun x => ⟨fun g => (x.1.1 g, x.2.1 g), by
        refine ⟨?_, ?_⟩
        · intro g h
          exact Prod.ext (x.1.2.1 g h) (x.2.2.1 g h)
        · apply (x.1.2.2.union x.2.2.2).subset
          rintro q ⟨g, hg, rfl⟩
          by_cases h₁ : x.1.1 g = 0
          · right
            exact ⟨g, by simpa [Function.mem_support, h₁] using hg, rfl⟩
          · left
            exact ⟨g, h₁, rfl⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let ef : (functionAction H (ρ.prod σ)).Equiv
      ((functionAction H ρ).prod (functionAction H σ)) :=
    Representation.Equiv.mk f (by
      intro g
      apply LinearMap.ext
      intro x
      rfl)
  let ep : ((induction H ρ).prod (induction H σ)).Equiv
      ((functionAction H ρ).prod (functionAction H σ)) :=
    Representation.Equiv.mk ((functionEquiv H ρ).prodCongr (functionEquiv H σ)) (by
      intro g
      apply LinearMap.ext
      intro x
      exact Prod.ext (functionEquiv_equivariant H ρ g x.1)
        (functionEquiv_equivariant H σ g x.2))
  exact (functionRepresentationEquiv H (ρ.prod σ)).trans (ef.trans ep.symm)

variable [Fintype G]

/-- Finite dimension comes from the upstream direct-sum model. -/
instance finiteDimensional [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) :
    FiniteDimensional ℂ (Induced H ρ) := TensorCoordinates.induced_finiteDimensional H ρ

theorem character_congr [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ H V} {σ : Representation ℂ H W}
    (h : CharacterSpecs.characterValue ρ = CharacterSpecs.characterValue σ) :
    CharacterSpecs.characterValue (induction H ρ) =
      CharacterSpecs.characterValue (induction H σ) := by
  obtain ⟨e⟩ := (RegularMultiplicity.character_classification ρ σ).mpr h
  exact RegularMultiplicity.character_of_equiv (equiv H e)

theorem character_add [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ H W) :
    CharacterSpecs.characterValue (induction H (ρ.prod σ)) =
      CharacterSpecs.characterValue (induction H ρ) +
        CharacterSpecs.characterValue (induction H σ) := by
  rw [RegularMultiplicity.character_of_equiv (prodEquiv H ρ σ)]
  funext g
  exact character_directSum _ _ g

/-- A chosen representative is used only internally; classification and
functoriality prove independence of this choice. -/
def ordinaryValue (x : ordinaryMonoid H) : VirtualCharacterSpecs.Ring G := by
  let h := (ordinaryMonoid_iff x.1).mp x.2
  let ρ := h.choose_spec.choose
  exact actual (induction H ρ)

theorem ordinaryValue_formula [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (x : ordinaryMonoid H)
    (hx : x.1 = CharacterSpecs.characterValue ρ) :
    (ordinaryValue H x).1 = CharacterSpecs.characterValue (induction H ρ) := by
  dsimp only [ordinaryValue, actual, Expected.actualValue]
  exact character_congr H (((ordinaryMonoid_iff x.1).mp x.2).choose_spec.choose_spec.trans hx)

theorem ordinaryValue_add (x y : ordinaryMonoid H) :
    ordinaryValue H (x + y) = ordinaryValue H x + ordinaryValue H y := by
  obtain ⟨n, ρ, hρ⟩ := (ordinaryMonoid_iff x.1).mp x.2
  obtain ⟨m, σ, hσ⟩ := (ordinaryMonoid_iff y.1).mp y.2
  apply Subtype.ext
  change (ordinaryValue H (x + y)).1 =
    (ordinaryValue H x).1 + (ordinaryValue H y).1
  rw [ordinaryValue_formula H ρ x hρ.symm, ordinaryValue_formula H σ y hσ.symm]
  rw [ordinaryValue_formula H (ρ.prod σ) (x + y) (by
    change x.1 + y.1 = _
    rw [← hρ, ← hσ]
    funext g
    exact (character_directSum ρ σ g).symm)]
  exact character_add H ρ σ

/-- Additive induction on ordinary characters. -/
def ordinaryMap : ordinaryMonoid H →+ VirtualCharacterSpecs.Ring G where
  toFun := ordinaryValue H
  map_add' := ordinaryValue_add H
  map_zero' := by
    have h := ordinaryValue_add H 0 0
    simpa only [add_zero, left_eq_add] using h

/-- Additive induction on the full group completion. -/
def map : VirtualCharacterSpecs.Ring H →+ VirtualCharacterSpecs.Ring G :=
  (completion (ordinaryMap H)).choose

theorem map_ordinary (x : ordinaryMonoid H) :
    map H (ordinaryInclusion H x) = ordinaryMap H x :=
  congrArg (fun F : ordinaryMonoid H →+ VirtualCharacterSpecs.Ring G => F x)
    (completion (ordinaryMap H)).choose_spec.1

theorem map_actual [FiniteDimensional ℂ V] (ρ : Representation ℂ H V)
    (x : VirtualCharacterSpecs.Ring H) (hx : x.1 = CharacterSpecs.characterValue ρ) :
    (map H x).1 = CharacterSpecs.characterValue (induction H ρ) := by
  let a : ordinaryMonoid H := ⟨x.1,
    (ordinaryMonoid_iff x.1).mpr (by rw [hx]; exact ordinary_of_rep ρ)⟩
  have ha : ordinaryInclusion H a = x := Subtype.ext rfl
  rw [← ha, map_ordinary]
  exact ordinaryValue_formula H ρ a hx

/-- Any tensor-action construction in the upstream specification is
canonically equivalent to the standard one, through the identity on elementary
tensors. This also transfers finite dimension to its chosen scalar action. -/
theorem anyData [FiniteDimensional ℂ V] (ρ : Representation ℂ H V)
    (D : InductionData H ρ) :
    let χ := CharacterSpecs.characterValue (induction H ρ)
    letI := D.module
    FiniteDimensional ℂ (Induced H ρ) ∧
      χ = CharacterSpecs.characterValue D.representation := by
  rcases D with ⟨m, τ, hs, ha⟩
  have hm : m = inducedScalarModule H ρ := by
    apply Module.ext'
    intro c z
    induction z using BalancedTensor.induction_on with
    | h0 =>
      have h₁ : (letI := m; c • (0 : Induced H ρ)) = 0 := by
        letI := m
        exact smul_zero c
      have h₂ : (letI := inducedScalarModule H ρ; c • (0 : Induced H ρ)) = 0 := by
        letI := inducedScalarModule H ρ
        exact smul_zero c
      exact h₁.trans h₂.symm
    | ht a b =>
      change (letI := m; c • tensor H ρ a (ρ.asModuleEquiv b)) =
        (letI := inducedScalarModule H ρ; c • tensor H ρ a (ρ.asModuleEquiv b))
      rw [hs, inducedScalar_smul_tensor]
    | ha z z' hz hz' =>
      have h₁ := (letI := m; smul_add c z z')
      have h₂ := (letI := inducedScalarModule H ρ; smul_add c z z')
      exact h₁.trans ((congrArg₂ (· + ·) hz hz').trans h₂.symm)
  subst m
  have he : τ = P103.Ch09.induction H ρ := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.toAddMonoidHom_injective
    apply BalancedTensor.hom_ext
    intro a b
    exact ha g a (ρ.asModuleEquiv b)
  change FiniteDimensional ℂ (Induced H ρ) ∧
    CharacterSpecs.characterValue (P103.Ch09.induction H ρ) = CharacterSpecs.characterValue τ
  exact ⟨inferInstance, congrArg CharacterSpecs.characterValue he.symm⟩

end Induction

theorem induction : Expected.inductionType.{u,v} := by
  intro G _ _ H
  classical
  letI := Fintype.ofFinite G
  refine ⟨Induction.map H, ?_⟩
  intro V _ _ _ ρ D
  obtain ⟨hfin, heq⟩ := Induction.anyData H ρ D
  refine ⟨hfin, ?_⟩
  intro x hx
  exact (Induction.map_actual H ρ x hx).trans heq

end P103.Ch09.VirtualCharacterRing
