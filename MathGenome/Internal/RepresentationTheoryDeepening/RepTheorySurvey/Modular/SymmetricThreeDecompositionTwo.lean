import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeDecompositionTwo
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeModules
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.DecompositionMatrix
import Batteries.Tactic.OpenPrivate

namespace RepTheorySurvey.Modular.SymmetricThree

open IsLocalRing (ResidueField)

noncomputable abbrev modularFamilyTwo : DecompositionTwoSpec.familyType :=
  @DecompositionTwoSpec.modularFamilyValue

theorem standard_reduction_dimension_two : DecompositionTwoSpec.standardReductionDimension := by
  intro O _ _ _ K _ _ _
  have h := ordinary_dimensions (ResidueField O) (2 : Fin 3)
  exact h

private theorem regular_conjugate_two (g : PRegular Group 2) :
    IsConj g.val 1 ∨ IsConj g.val threeCycle := by
  rcases class_data.1 g.val with h | h | h
  · exact Or.inl h
  · have ht := isPRegular_iff_of_isConj h |>.mp g.property
    change (orderOf transposition).Coprime 2 at ht
    rw [representative_orders.2.1] at ht
    exact (by decide : ¬ (2 : ℕ).Coprime 2) ht |>.elim
  · exact Or.inr h

theorem regular_classes_two : DecompositionTwoSpec.regularClasses := by
  classical
  refine ⟨regular_conjugate_two, ?_⟩
  let one : PRegular Group 2 := ⟨1, by change (orderOf (1 : Group)).Coprime 2; simp⟩
  let cycle : PRegular Group 2 := ⟨threeCycle, by
    change (orderOf threeCycle).Coprime 2
    rw [representative_orders.2.2]
    decide⟩
  let f : Fin 2 → PRegularConjClasses Group 2 :=
    ![pRegularConjClass one, pRegularConjClass cycle]
  have hne : f 0 ≠ f 1 := by
    intro h
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp
      (show ConjClasses.mk (1 : Group) = ConjClasses.mk threeCycle from congrArg Subtype.val h)
    obtain ⟨a, ha⟩ := hc
    have ho := SemiconjBy.orderOf_eq (a : Group) ha
    rw [representative_orders.1, representative_orders.2.2] at ho
    omega
  have hi : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  have hs : Function.Surjective f := by
    intro c
    obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
    rcases regular_conjugate_two g with h | h
    · exact ⟨0, Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm)⟩
    · exact ⟨1, Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm)⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm.trans (Nat.card_fin 2)

theorem ordinary_regular_restrictions_two : DecompositionTwoSpec.ordinaryRegularRestrictions := by
  intro K _ g
  rw [trivial_character, sign_character]
  have hsign : ∀ {a b : Group}, IsConj a b → Equiv.Perm.sign a = Equiv.Perm.sign b := by
    intro a b h
    obtain ⟨x, rfl⟩ := isConj_iff.mp h
    simp [mul_comm, mul_left_comm]
  rcases regular_conjugate_two g with h | h
  · rw [hsign h, map_one]
    norm_num
  · rw [hsign h, sign_representatives.2]
    norm_num

open private one_dimensional_irreducible restrictModuleEquiv
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeModules
open private exists_modular_family from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.DecompositionMatrix

universe u v

theorem modular_simple_family_two : DecompositionTwoSpec.modularSimpleFamily.{u, v} := by
  intro O _ _ _ K _ _ system
  classical
  let k := ResidueField O
  let kG := MonoidAlgebra k Group
  let _ : CharP k 2 := system.residueChar
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hthree : (3 : k) ≠ 0 := by
    rw [show (3 : k) = 2 + 1 by norm_num, htwo, zero_add]
    exact one_ne_zero
  have hsimple (i : Fin 2) : IsSimpleModule kG (modularFamilyTwo k i) := by
    fin_cases i
    · exact (Representation.irreducible_iff_isSimpleModule_asModule (trivial k)).mp
        (one_dimensional_irreducible k (trivial k))
    · exact (Representation.irreducible_iff_isSimpleModule_asModule (standard k)).mp
        (standard_simple k hthree)
  have hdim (i : Fin 2) :
      Module.finrank k (RestrictScalars k kG (modularFamilyTwo k i)) = (![1, 2] : Fin 2 → ℕ) i := by
    fin_cases i
    · exact ordinary_dimensions k (0 : Fin 3)
    · exact ordinary_dimensions k (2 : Fin 3)
  have hdistinct {i j : Fin 2} (e : modularFamilyTwo k i ≃ₗ[kG] modularFamilyTwo k j) :
      i = j := by
    have h := (restrictModuleEquiv k e).finrank_eq
    rw [hdim, hdim] at h
    fin_cases i <;> fin_cases j <;> first | rfl | cases h
  refine ⟨hsimple, fun ⟨e⟩ => hdistinct e, ?_⟩
  obtain ⟨n, C, hC⟩ := exists_modular_family.{0, u, v, 0} system
  have hn : n = 2 := by
    have hcard := (card_simple_representatives system C hC).2
    exact (Nat.card_fin n).symm.trans (hcard.trans regular_classes_two.2)
  choose a ha using fun i => hC.exhaustive (modularFamilyTwo k i) (hsimple i)
  have hai : Function.Injective a := by
    intro i j h
    have e : C (a i) ≃ₗ[kG] C (a j) := h ▸ LinearEquiv.refl kG (C (a i))
    exact hdistinct ((ha i).some.trans (e.trans (ha j).some.symm))
  have has : Function.Surjective a := by
    apply ((Fintype.bijective_iff_injective_and_card a).mpr ⟨hai, ?_⟩).2
    simp [hn]
  intro M hM
  obtain ⟨j, ⟨e⟩⟩ := hC.exhaustive M hM
  obtain ⟨i, rfl⟩ := has j
  exact ⟨i, ⟨e.trans (ha i).some.symm⟩⟩

open MR04LatticeSpec
open scoped Pointwise

section Lattices

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type v} [Field K] [Algebra O K]

local notation "k" => ResidueField O
local notation "kG" => MonoidAlgebra k Group
local notation "KG" => MonoidAlgebra K Group
local notation "𝔪" => IsLocalRing.maximalIdeal O

private noncomputable def reduceEquiv {M N : Type*}
    [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] (e : M ≃ₗ[O] N) :
    ResidueQuotient O M ≃ₗ[k] ResidueQuotient O N where
  __ := reduceMap e.toLinearMap
  invFun := reduceMap e.symm.toLinearMap
  left_inv q := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule O M)) q
    change (e.symm.toLinearMap.reduceModIdeal 𝔪)
      ((e.toLinearMap.reduceModIdeal 𝔪) (Submodule.Quotient.mk x)) = _
    simp
  right_inv q := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule O N)) q
    change (e.toLinearMap.reduceModIdeal 𝔪)
      ((e.symm.toLinearMap.reduceModIdeal 𝔪) (Submodule.Quotient.mk x)) = _
    simp

private theorem reduceEquiv_mk {M N : Type*}
    [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] (e : M ≃ₗ[O] N) (x : M) :
    reduceEquiv e (reduce x) = reduce (e x) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_native_lattice_of_reduction
    {V W : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [AddCommGroup W] [Module k W]
    (ρ : Representation K Group V) (τ : Representation k Group W) :
    ∀ (L : LatticeData O ρ),
      (residueAction (integralAction O L)).Equiv τ →
      ∃ L' : NativeLatticeData O K Group ρ.asModule,
        Nonempty (nativeReduction L' ≃ₗ[kG] τ.asModule) := by
  intro L er
  let V' := RestrictScalars K KG ρ.asModule
  let _ := Module.restrictScalars O K V'
  let _ := IsScalarTower.restrictScalars O K V'
  let ρ' := MR01Spec.moduleRepresentationValue K Group ρ.asModule
  let e := MR04Spec.asModuleScalarEquiv ρ
  let f : V →ₗ[O] V' := (e.symm.restrictScalars O).toLinearMap
  have hf (g : Group) (x : V) : ρ' g (f x) = f (ρ g x) := by
    change Representation.ofModule ρ.asModule g (e.symm x) = e.symm (ρ g x)
    rw [Representation.ofModule_asModule_act]
    change e.symm (ρ g (e (e.symm x))) = e.symm (ρ g x)
    rw [e.apply_symm_apply]
  let N := L.carrier.map f
  let j : L.carrier ≃ₗ[O] N := Submodule.equivMapOfInjective f e.symm.injective L.carrier
  let _ := L.finite
  let _ := L.free
  let L' : NativeLatticeData O K Group ρ.asModule :=
    { carrier := N
      finite := Module.Finite.equiv j
      free := Module.Free.of_equiv j
      spans := by
        change Submodule.span K (e.symm '' (L.carrier : Set V)) = ⊤
        rw [Submodule.span_image_linearEquiv, L.spans, Submodule.map_top,
          LinearMap.range_eq_top.mpr e.symm.surjective]
      stable := by
        intro g z hz
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
        change ρ' g (f x) ∈ N
        rw [hf]
        exact Submodule.mem_map_of_mem (L.stable g hx) }
  have hj (g : Group) (x : L.carrier) :
      j (integralAction O L g x) = integralAction O L' g (j x) := by
    apply Subtype.ext
    exact (hf g x.val).symm
  let σ := residueAction (integralAction O L)
  let σ' := residueAction (integralAction O L')
  let q : σ.Equiv σ' := Representation.Equiv.mk (reduceEquiv j) (fun g => by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule O L.carrier)) x
    change reduceEquiv j (reduce (integralAction O L g y)) =
      reduce (integralAction O L' g (j y))
    rw [reduceEquiv_mk, hj])
  let φ := q.symm.trans er
  let F := (Representation.IntertwiningMap.equivLinearMapAsModule σ' τ) φ.toIntertwiningMap
  have hF : Function.Bijective F := φ.toLinearEquiv.bijective
  exact ⟨L', ⟨LinearEquiv.ofBijective F hF⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem rank_one_reduces_to_trivial [IsFractionRing O K]
    (ρ : Representation K Group K) (ε : Group → O)
    (hρ : ∀ g x, ρ g x = algebraMap O K (ε g) * x)
    (hε : ∀ g, IsLocalRing.residue O (ε g) = 1) :
    ∃ L : NativeLatticeData O K Group ρ.asModule,
      Nonempty ((nativeReduction L : Type v) ≃ₗ[kG] (trivial k).asModule) := by
  let emb := Algebra.linearMap O K
  let j := LinearEquiv.ofInjective emb (IsFractionRing.injective O K)
  let L : LatticeData O ρ :=
    { carrier := LinearMap.range emb
      finite := Module.Finite.equiv j
      free := Module.Free.of_equiv j
      spans := by
        apply top_unique
        rw [← Ideal.span_singleton_one]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨1, map_one (algebraMap O K)⟩)
      stable := by
        rintro g _ ⟨x, rfl⟩
        refine ⟨ε g * x, ?_⟩
        exact (map_mul (algebraMap O K) (ε g) x).trans (hρ g (emb x)).symm }
  have hsmul : 𝔪 • (⊤ : Submodule O O) = 𝔪 := by
    simp
  let q₀ : ResidueQuotient O O ≃ₗ[O] k := Submodule.quotEquivOfEq _ _ hsmul
  let q : ResidueQuotient O O ≃ₗ[k] k :=
    q₀.extendScalarsOfSurjective IsLocalRing.residue_surjective
  let e := (reduceEquiv j.symm).trans q
  have he (x : O) : e (reduce (j x)) = IsLocalRing.residue O x := by
    change q (reduceEquiv j.symm (reduce (j x))) = _
    rw [reduceEquiv_mk, j.symm_apply_apply]
    rfl
  have hj (g : Group) (x : O) : integralAction O L g (j x) = j (ε g * x) := by
    apply Subtype.ext
    change ρ g (emb x) = emb (ε g * x)
    rw [hρ]
    exact (map_mul (algebraMap O K) (ε g) x).symm
  let er : (residueAction (integralAction O L)).Equiv (trivial k) :=
    Representation.Equiv.mk e fun g => by
      apply LinearMap.ext
      intro y
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule O L.carrier)) y
      obtain ⟨x, rfl⟩ := j.surjective z
      change e (reduce (integralAction O L g (j x))) = e (reduce (j x))
      rw [hj, he, he, map_mul, hε, one_mul]
  exact exists_native_lattice_of_reduction ρ (trivial k) L er

set_option backward.isDefEq.respectTransparency false in
private theorem standard_native_reduction_two (system : SplittingSystem Group 2 O K) :
    ∃ L : NativeLatticeData O K Group (standard K).asModule,
      Nonempty (nativeReduction L ≃ₗ[kG] (standard k).asModule) := by
  let _ := Module.restrictScalars O K (Plane K)
  let _ := IsScalarTower.restrictScalars O K (Plane K)
  obtain ⟨L, _, er, -⟩ := standard_lattice_reduction system
  exact exists_native_lattice_of_reduction (standard K) (standard k) L er

private def reductionColumnTwo : Fin 3 → Fin 2 := ![0, 0, 1]

private def HasLatticeReduction (V : ModuleCat.{v} KG) (W : ModuleCat.{u} kG) : Prop :=
  ∃ L : NativeLatticeData O K Group V, Nonempty (nativeReduction L ≃ₗ[kG] W)

set_option backward.isDefEq.respectTransparency false in
private theorem row_lattice_two (system : SplittingSystem Group 2 O K) (i : Fin 3) :
    HasLatticeReduction (ordinaryFamily K i) (modularFamilyTwo k (reductionColumnTwo i)) := by
  let _ := system.fractionRing
  let _ : CharP k 2 := system.residueChar
  fin_cases i
  · exact rank_one_reduces_to_trivial (trivial K) (fun _ => (1 : O))
      (fun g x => by simp [trivial, Spec.trivialValue]) (fun _ => map_one _)
  · let ε (g : Group) : O := ((Equiv.Perm.sign g : ℤ) : O)
    have hε (g : Group) : IsLocalRing.residue O (ε g) = 1 := by
      have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
      have hneg : (-1 : k) = 1 := by
        apply (neg_eq_iff_add_eq_zero).2
        simpa only [one_add_one_eq_two] using htwo
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
      · simp [ε, h]
      · simpa [ε, h] using hneg
    exact rank_one_reduces_to_trivial (sign K) ε
      (fun g x => by
        change ((Equiv.Perm.sign g : ℤ) : K) * x = (algebraMap O K) (ε g) * x
        rw [show (algebraMap O K) (ε g) = ((Equiv.Perm.sign g : ℤ) : K) from map_intCast _ _]) hε
  · change HasLatticeReduction (MR01Spec.representationModuleValue (standard K))
      (MR01Spec.representationModuleValue (standard k))
    exact standard_native_reduction_two system

end Lattices

set_option backward.isDefEq.respectTransparency false in
theorem decomposition_matrix_two : DecompositionTwoSpec.decompositionMatrix.{u, v} := by
  intro O _ _ _ K _ _ system
  let k := ResidueField O
  have ho := ordinary_simple_family system
  have hm := modular_simple_family_two system
  change decompositionMatrix system (ordinaryFamily K) (modularFamilyTwo k) =
    (!![1, 0; 1, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℕ)
  ext i j
  obtain ⟨L, ⟨e⟩⟩ := row_lattice_two system i
  rw [decompositionMatrix_apply_eq_lattice system (ordinaryFamily K) ho (modularFamilyTwo k) hm i j L]
  let _ := hm.simple (reductionColumnTwo i)
  let _ := IsSimpleModule.congr e
  have hmul := CompositionMultiplicity.multiplicity_of_simple (F := k) (G := Group)
    (M := nativeReduction L) (S := modularFamilyTwo k j)
  have hentry : (!![1, 0; 1, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℕ) i j =
      if reductionColumnTwo i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> decide
  rw [hentry]
  split_ifs with h
  · exact hmul.1 ⟨h ▸ e⟩
  · exact hmul.2 (fun ⟨d⟩ => h (hm.eq_of_iso ⟨e.symm.trans d⟩))

end RepTheorySurvey.Modular.SymmetricThree
