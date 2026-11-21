import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.ProductIrreducibles
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterConstructions
import MathGenome.Internal.AlgebraCore.P103.Ch08.RegularMultiplicity
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

noncomputable section
open scoped Classical
universe u v w x y z t
namespace P103.Ch08.ProductIrreducibles
open ProductSpecs
open private libraryIrreducible from MathGenome.Internal.AlgebraCore.P103.Ch08.Schur
open scoped MonoidAlgebra

def external : externalType.{u,v,w,x} := @externalValue

theorem external_apply : applyType.{u,v,w,x} := by
  intro G K _ _ V W _ _ _ _ ρ σ g k a b
  exact TensorProduct.map_tmul ..

theorem external_character : characterType.{u,v,w,x} := by
  intro G K _ _ V W _ _ _ _ _ _ ρ σ g k
  exact LinearMap.trace_tensorProduct' _ _

theorem diagonal_restriction : diagonalType.{u,w,x} := by
  intro G _ V W _ _ _ _ ρ σ
  rfl

/-- Fubini's formula for the normalized Hermitian pairing. -/
theorem pairing_product {G : Type u} {K : Type v} [Fintype G] [Fintype K]
    (f h : G → ℂ) (p q : K → ℂ) :
    UnitaritySpecs.functionPairingValue (fun a : G × K => f a.1 * p a.2)
      (fun a => h a.1 * q a.2) =
    UnitaritySpecs.functionPairingValue f h * UnitaritySpecs.functionPairingValue p q := by
  unfold UnitaritySpecs.functionPairingValue
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev, star_mul,
    Fintype.sum_prod_type]
  simp_rw [show ∀ g k, f g * p k * (star (q k) * star (h g)) =
    (f g * star (h g)) * (p k * star (q k)) by intros; ring]
  rw [← Finset.sum_mul_sum]
  ring

/-- Orthogonality in the source's first-variable-linear convention. -/
theorem pairing_irreducible {G : Type u} [Group G] [Fintype G]
    {V : Type w} {W : Type x} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : Irreducible ℂ G V ρ) (hσ : Irreducible ℂ G W σ) :
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ)
      (CharacterSpecs.characterValue σ) = if Nonempty (ρ.Equiv σ) then 1 else 0 := by
  classical
  have := libraryIrreducible ρ hρ
  have := libraryIrreducible σ hσ
  have := RegularMultiplicity.finite_dimensional ρ hρ
  have := RegularMultiplicity.finite_dimensional σ hσ
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have hh := Representation.char_orthonormal ρ σ
  have he : Nonempty (σ.Equiv ρ) ↔ Nonempty (ρ.Equiv σ) :=
    ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩
  rw [he] at hh
  unfold UnitaritySpecs.functionPairingValue
  simp_rw [← character_inverse_conjugate σ]
  simpa only [Representation.character, CharacterSpecs.characterValue,
    Fintype.card_eq_nat_card, mul_comm] using hh

/-- A semisimple module whose endomorphism space has dimension one is simple.
A projection onto any summand is scalar, hence has zero or full image. -/
theorem simple_of_finrank_end_eq_one {A : Type*} [Ring A] [Algebra ℂ A]
    {M : Type*} [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] [IsSemisimpleModule A M]
    (h : Module.finrank ℂ (Module.End A M) = 1) : IsSimpleModule A M := by
  classical
  have : Nontrivial M := by
    rcases subsingleton_or_nontrivial M with hM | hM
    · have hz : Module.finrank ℂ (Module.End A M) = 0 :=
        Module.finrank_eq_zero_of_subsingleton ℂ _
      omega
    · exact hM
  have hi : (LinearMap.id : Module.End A M) ≠ 0 := by
    intro hh
    obtain ⟨a, ha⟩ := exists_ne (0 : M)
    exact ha (by simpa using LinearMap.congr_fun hh a)
  have scalar := (finrank_eq_one_iff_of_nonzero' (LinearMap.id : Module.End A M) hi).mp h
  refine { eq_bot_or_eq_top := ?_ }
  intro U
  obtain ⟨Q, hQ⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := scalar (U.projection Q hQ)
  by_cases hz : c = 0
  · left
    rw [← U.range_projection hQ, ← hc, hz, zero_smul, LinearMap.range_zero]
  · right
    rw [← U.range_projection hQ, ← hc]
    apply LinearMap.range_eq_top.mpr
    intro a
    refine ⟨c⁻¹ • a, ?_⟩
    simp [smul_smul, hz]

/-- The norm-one criterion, without a dimension assumption hidden in
irreducibility and without fixing a universe for representation spaces. -/
theorem irreducible_of_pairing_one {G : Type u} [Group G] [Fintype G]
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (h : UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ)
      (CharacterSpecs.characterValue ρ) = 1) : Irreducible ℂ G V ρ := by
  have hf : Module.finrank ℂ (ρ.IntertwiningMap ρ) = 1 := by
    have hp := (character_pairing ρ ρ).1
    rw [h] at hp
    exact_mod_cast hp.symm
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  have hs : IsSimpleModule ℂ[G] ρ.asModule := simple_of_finrank_end_eq_one (by
    rw [← (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.finrank_eq]
    exact hf)
  have : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hs
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  exact ⟨ρ.asModuleEquiv.symm.nontrivial, fun U => eq_bot_or_eq_top U⟩

theorem external_irreducible : irreducibleType.{u,v,w,x} := by
  intro G K _ _ _ _ V W _ _ _ _ ρ σ hρ hσ
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite K
  have := RegularMultiplicity.finite_dimensional ρ hρ
  have := RegularMultiplicity.finite_dimensional σ hσ
  apply irreducible_of_pairing_one
  have he : CharacterSpecs.characterValue (externalValue ρ σ) =
      fun a : G × K => CharacterSpecs.characterValue ρ a.1 *
        CharacterSpecs.characterValue σ a.2 := funext fun a => external_character ρ σ a.1 a.2
  rw [he, pairing_product, pairing_irreducible ρ ρ hρ hρ,
    pairing_irreducible σ σ hσ hσ]
  simp only [ite_eq_left (show Nonempty (ρ.Equiv ρ) from ⟨.refl _⟩),
    ite_eq_left (show Nonempty (σ.Equiv σ) from ⟨.refl _⟩), one_mul]

theorem pairing_external {G : Type u} {K : Type v} [Group G] [Group K]
    [Fintype G] [Fintype K]
    {V : Type w} {W : Type x} {V' : Type y} {W' : Type z}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ V'] [FiniteDimensional ℂ W']
    (ρ : Representation ℂ G V) (σ : Representation ℂ K W)
    (ρ' : Representation ℂ G V') (σ' : Representation ℂ K W') :
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue (externalValue ρ σ))
      (CharacterSpecs.characterValue (externalValue ρ' σ')) =
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ)
      (CharacterSpecs.characterValue ρ') *
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue σ)
      (CharacterSpecs.characterValue σ') := by
  have hc : CharacterSpecs.characterValue (externalValue ρ σ) =
      fun a : G × K => CharacterSpecs.characterValue ρ a.1 *
        CharacterSpecs.characterValue σ a.2 := funext fun a => external_character ρ σ a.1 a.2
  have hc' : CharacterSpecs.characterValue (externalValue ρ' σ') =
      fun a : G × K => CharacterSpecs.characterValue ρ' a.1 *
        CharacterSpecs.characterValue σ' a.2 := funext fun a => external_character ρ' σ' a.1 a.2
  rw [hc, hc', pairing_product]

theorem external_equiv_iff : equivIffType.{u,v,w,x,y,z} := by
  intro G K _ _ _ _ V W V' W' _ _ _ _ _ _ _ _ ρ σ ρ' σ' hρ hσ hρ' hσ'
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite K
  have := RegularMultiplicity.finite_dimensional ρ hρ
  have := RegularMultiplicity.finite_dimensional σ hσ
  have := RegularMultiplicity.finite_dimensional ρ' hρ'
  have := RegularMultiplicity.finite_dimensional σ' hσ'
  constructor
  · rintro ⟨e⟩
    have hp : UnitaritySpecs.functionPairingValue
        (CharacterSpecs.characterValue (externalValue ρ σ))
        (CharacterSpecs.characterValue (externalValue ρ' σ')) = 1 := by
      rw [← RegularMultiplicity.character_of_equiv e,
        pairing_irreducible _ _ (external_irreducible ρ σ hρ hσ)
          (external_irreducible ρ σ hρ hσ)]
      exact ite_eq_left ⟨.refl _⟩
    rw [pairing_external, pairing_irreducible ρ ρ' hρ hρ',
      pairing_irreducible σ σ' hσ hσ'] at hp
    split_ifs at hp <;> simp_all
  · rintro ⟨⟨e⟩, ⟨f⟩⟩
    apply (RegularMultiplicity.character_classification _ _).mpr
    funext a
    rw [external_character, external_character,
      RegularMultiplicity.character_of_equiv e, RegularMultiplicity.character_of_equiv f]

/-- An injection preserving the sum of strictly positive weights is onto. -/
theorem surjective_of_weight_sum {I : Type*} {J : Type*} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (d : J → ℕ)
    (hd : ∀ j, 0 < d j) (hs : ∑ i, d (f i) = ∑ j, d j) : Function.Surjective f := by
  classical
  intro j
  by_contra hj
  have hmem : j ∉ Finset.univ.image f := by simpa using hj
  have himage : ∑ k ∈ Finset.univ.image f, d k = ∑ k, d k := by
    rw [Finset.sum_image (fun a _ b _ h => hf h)]
    exact hs
  have hle : ∑ k ∈ insert j (Finset.univ.image f), d k ≤ ∑ k, d k :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_insert hmem, himage] at hle
  have := hd j
  omega

open RegularMultiplicitySpecs in
/-- Distinct canonical ideal representatives have distinct equivariant types. -/
theorem ideal_index_eq {G : Type u} [Group G] (C : Family G) (hC : Valid C)
    (i j : Fin C.n)
    (he : Nonempty ((idealRepresentation (C.space i)).Equiv
      (idealRepresentation (C.space j)))) : i = j := by
  obtain ⟨e⟩ := he
  exact hC.2 i j ⟨(RegularMultiplicity.idealModuleEquiv (C.space i)).symm.trans
    ((RegularMultiplicity.moduleEquivOfEquiv e).trans
      (RegularMultiplicity.idealModuleEquiv (C.space j)))⟩

open RegularMultiplicitySpecs in
/-- No additional product-group type remains: the known pair types already
account for the entire regular sum of squares. -/
theorem canonical_complete {G : Type u} {K : Type v} [Group G] [Group K]
    [Fintype G] [Fintype K]
    (C : Family G) (D : Family K) (hC : Valid C) (hD : Valid D)
    (hCX : Exhaustive.{u,u} C) (hDX : Exhaustive.{v,v} D)
    {U : Type w} [AddCommGroup U] [Module ℂ U]
    (τ : Representation ℂ (G × K) U) (hτ : Irreducible ℂ (G × K) U τ) :
    ∃ p : Fin C.n × Fin D.n,
      Nonempty ((externalValue (idealRepresentation (C.space p.1))
        (idealRepresentation (D.space p.2))).Equiv τ) := by
  classical
  have ci (i : Fin C.n) : Irreducible ℂ G (C.space i)
      (idealRepresentation (C.space i)) := by
    have := hC.1 i
    exact RegularMultiplicity.ideal_irreducible _
  have di (j : Fin D.n) : Irreducible ℂ K (D.space j)
      (idealRepresentation (D.space j)) := by
    have := hD.1 j
    exact RegularMultiplicity.ideal_irreducible _
  obtain ⟨E, hE, hEX⟩ := RegularMultiplicity.finite_family.{max u v, max u v}
    (G := G × K)
  let R (p : Fin C.n × Fin D.n) :=
    externalValue (idealRepresentation (C.space p.1)) (idealRepresentation (D.space p.2))
  have ri (p : Fin C.n × Fin D.n) := external_irreducible _ _ (ci p.1) (di p.2)
  choose f he using fun p : Fin C.n × Fin D.n => hEX (R p) (ri p)
  have hf : Function.Injective f := by
    intro p q hpq
    have ep := (he p).some
    have eq := (he q).some
    rw [hpq] at ep
    have h := (external_equiv_iff _ _ _ _ (ci p.1) (di p.2) (ci q.1) (di q.2)).mp
      ⟨ep.symm.trans eq⟩
    exact Prod.ext (ideal_index_eq C hC _ _ h.1) (ideal_index_eq D hD _ _ h.2)
  have dim (p : Fin C.n × Fin D.n) :
      Module.finrank ℂ (E.space (f p)) =
        Module.finrank ℂ (C.space p.1) * Module.finrank ℂ (D.space p.2) := by
    exact (he p).some.toLinearEquiv.finrank_eq.trans (Module.finrank_tensorProduct ..)
  have hs : ∑ p : Fin C.n × Fin D.n, (Module.finrank ℂ (E.space (f p))) ^ 2 =
      ∑ i : Fin E.n, (Module.finrank ℂ (E.space i)) ^ 2 := by
    simp_rw [dim, mul_pow]
    rw [Fintype.sum_prod_type]
    change (∑ i : Fin C.n, ∑ j : Fin D.n,
      Module.finrank ℂ (C.space i) ^ 2 * Module.finrank ℂ (D.space j) ^ 2) = _
    rw [← Finset.sum_mul_sum,
      ← (RegularMultiplicity.regular_decomposition C hC hCX).2,
      ← (RegularMultiplicity.regular_decomposition D hD hDX).2,
      ← (RegularMultiplicity.regular_decomposition E hE hEX).2,
      Fintype.card_prod]
  have hpos (i : Fin E.n) : 0 < (Module.finrank ℂ (E.space i)) ^ 2 := by
    have := hE.1 i
    have : Nontrivial (E.space i) := IsSimpleModule.nontrivial ℂ[G × K] _
    exact pow_pos (Module.finrank_pos) _
  have hsurj := surjective_of_weight_sum f hf _ hpos hs
  obtain ⟨i, ⟨e⟩⟩ := (RegularMultiplicity.exhaustive_from_regular E hEX) τ hτ
  obtain ⟨p, hp⟩ := hsurj i
  have ep := (he p).some
  rw [hp] at ep
  exact ⟨p, ⟨ep.symm.trans e⟩⟩

/-- For any complete lists without repetitions, each product-group
irreducible occurs at exactly one pair of indices. -/
theorem family_classification :
  ∀ {G : Type u} {K : Type v} [Group G] [Group K] [Finite G] [Finite K]
    {I : Type y} {J : Type z} {V : I → Type w} {W : J → Type x}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (ρ : ∀ i, Representation ℂ G (V i)) (σ : ∀ j, Representation ℂ K (W j)),
    (∀ i, Irreducible ℂ G (V i) (ρ i)) →
    (∀ j, Irreducible ℂ K (W j) (σ j)) →
    (∀ i i', Nonempty ((ρ i).Equiv (ρ i')) → i = i') →
    (∀ j j', Nonempty ((σ j).Equiv (σ j')) → j = j') →
    (∀ {A : Type u} [AddCommGroup A] [Module ℂ A] (α : Representation ℂ G A),
      Irreducible ℂ G A α → ∃ i, Nonempty ((ρ i).Equiv α)) →
    (∀ {B : Type v} [AddCommGroup B] [Module ℂ B] (β : Representation ℂ K B),
      Irreducible ℂ K B β → ∃ j, Nonempty ((σ j).Equiv β)) →
    ∀ {U : Type t} [AddCommGroup U] [Module ℂ U]
      (τ : Representation ℂ (G × K) U), Irreducible ℂ (G × K) U τ →
      ∃! p : I × J, Nonempty ((externalValue (ρ p.1) (σ p.2)).Equiv τ) := by
  intro G K _ _ _ _ I J V W _ _ _ _ ρ σ hρ hσ hρuniq hσuniq hρfull hσfull U _ _ τ hτ
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite K
  obtain ⟨C, hC, hCX⟩ := RegularMultiplicity.finite_family.{u,u} (G := G)
  obtain ⟨D, hD, hDX⟩ := RegularMultiplicity.finite_family.{v,v} (G := K)
  obtain ⟨p, ⟨ep⟩⟩ := canonical_complete C D hC hD hCX hDX τ hτ
  have ci : Irreducible ℂ G (C.space p.1)
      (RegularMultiplicitySpecs.idealRepresentation (C.space p.1)) := by
    have := hC.1 p.1
    exact RegularMultiplicity.ideal_irreducible _
  have dj : Irreducible ℂ K (D.space p.2)
      (RegularMultiplicitySpecs.idealRepresentation (D.space p.2)) := by
    have := hD.1 p.2
    exact RegularMultiplicity.ideal_irreducible _
  obtain ⟨i, ⟨ei⟩⟩ := hρfull _ ci
  obtain ⟨j, ⟨ej⟩⟩ := hσfull _ dj
  obtain ⟨et⟩ := (external_equiv_iff _ _ _ _ (hρ i) (hσ j) ci dj).mpr ⟨⟨ei⟩, ⟨ej⟩⟩
  let e := et.trans ep
  refine ⟨(i,j), ⟨e⟩, ?_⟩
  intro q hq
  obtain ⟨eq⟩ := hq
  have h := (external_equiv_iff _ _ _ _ (hρ q.1) (hσ q.2) (hρ i) (hσ j)).mp
    ⟨eq.trans e.symm⟩
  exact Prod.ext (hρuniq _ _ h.1) (hσuniq _ _ h.2)

end P103.Ch08.ProductIrreducibles
