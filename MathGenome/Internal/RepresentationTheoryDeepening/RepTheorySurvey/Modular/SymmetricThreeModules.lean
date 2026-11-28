import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.StableLattices
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplitMatrixColumns
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeModules
import MathGenome.Internal.AlgebraCore.P103.Ch08.S3CharacterTable
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The ordinary representations of (S_3) and the reduction of the standard lattice. -/

namespace RepTheorySurvey.Modular.SymmetricThree

noncomputable section

open Module

abbrev Group := Spec.GroupValue
abbrev transposition : Group := Spec.transpositionValue
abbrev threeCycle : Group := Spec.threeCycleValue
abbrev trivial := Spec.trivialValue
abbrev sign := Spec.signValue
abbrev permutation := Spec.permutationValue
abbrev planeSubmodule := Spec.planeSubmoduleValue
abbrev Plane := Spec.PlaneValue
abbrev standard := Spec.standardValue
abbrev ordinaryFamily := Spec.ordinaryFamilyValue
abbrev integralEmbedding := Spec.integralEmbeddingValue
abbrev coordinateReduction := Spec.coordinateReductionValue

theorem class_data : Spec.classData :=
  P103.Ch08.S3CharacterTable.class_data

theorem representative_orders : Spec.representativeOrders := by
  refine ⟨orderOf_one, ?_, ?_⟩
  · exact orderOf_eq_prime (by decide) (by decide)
  · exact orderOf_eq_prime (by decide) (by decide)

theorem sign_representatives : Spec.signRepresentatives := by
  simp [Spec.signRepresentatives, Spec.transpositionValue, Spec.threeCycleValue]

@[simp]
theorem standard_apply {R : Type*} [CommRing R] (g : Group) (x : Plane R) (i : Fin 3) :
    (standard R g x).val i = x.val (g⁻¹ i) := rfl

section Coordinates

variable (R : Type*) [CommRing R]

private def fromCoordinates (a b : R) : Plane R :=
  ⟨![a, b, -(a + b)], by
    change ∑ i : Fin 3, (![a, b, -(a + b)] : Fin 3 → R) i = 0
    simp [Fin.sum_univ_three]⟩

private theorem third_coordinate (x : Plane R) : x.val 2 = -(x.val 0 + x.val 1) := by
  have hx : ∑ i : Fin 3, x.val i = 0 := x.property
  rw [Fin.sum_univ_three] at hx
  exact eq_neg_of_add_eq_zero_right hx

private theorem plane_ext {x y : Plane R} (h₀ : x.val 0 = y.val 0)
    (h₁ : x.val 1 = y.val 1) : x = y := by
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h₀
  · exact h₁
  · change x.val 2 = y.val 2
    rw [third_coordinate R x, third_coordinate R y, h₀, h₁]

private def coordinateEquiv : Plane R ≃ₗ[R] (Fin 2 → R) where
  toFun x := ![x.val 0, x.val 1]
  invFun a := fromCoordinates R (a 0) (a 1)
  left_inv x := plane_ext R rfl rfl
  right_inv a := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' a x := by funext i; fin_cases i <;> rfl

private def coordinateBasis : Basis (Fin 2) R (Plane R) :=
  (Pi.basisFun R (Fin 2)).map (coordinateEquiv R).symm

end Coordinates

theorem standard_dimension : Spec.standardDimension := by
  intro F _
  simpa [Module.finrank_pi] using (coordinateEquiv F).finrank_eq

private def restrictionEquiv (F : Type*) [Field F] {A : Type*} [Ring A] [Algebra F A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M] :
    RestrictScalars F A M ≃ₗ[F] M where
  __ := RestrictScalars.addEquiv F A M
  map_smul' r x := (RestrictScalars.addEquiv_map_smul F A M r x).trans (algebraMap_smul A r _)

private theorem representation_finrank (F : Type*) [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F Group V) :
    Module.finrank F (RestrictScalars F (MonoidAlgebra F Group) ρ.asModule) =
      Module.finrank F V :=
  (restrictionEquiv F).finrank_eq.trans ρ.asModuleEquiv.finrank_eq

theorem ordinary_dimensions : Spec.ordinaryDimensions := by
  intro F _ i
  fin_cases i
  · exact (representation_finrank F (trivial F)).trans (Module.finrank_self F)
  · exact (representation_finrank F (sign F)).trans (Module.finrank_self F)
  · exact (representation_finrank F (standard F)).trans (standard_dimension F)

theorem trivial_character : Spec.trivialCharacter := by
  intro F _ g
  change LinearMap.trace F F LinearMap.id = 1
  simp

theorem sign_character : Spec.signCharacter := by
  intro F _ g
  change LinearMap.trace F F (((Equiv.Perm.sign g : ℤ) : F) • LinearMap.id) = _
  simp

private theorem trace_in_coordinates (F : Type*) [Field F] (g : Group) :
    (standard F).character g =
      (standard F g (fromCoordinates F 1 0)).val 0 +
        (standard F g (fromCoordinates F 0 1)).val 1 := by
  change LinearMap.trace F (Plane F) (standard F g) = _
  classical
  rw [LinearMap.trace_eq_matrix_trace F (coordinateBasis F)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Fin.sum_univ_two,
    coordinateBasis, Basis.map_repr, Basis.map_apply, Pi.basisFun_apply]
  have h₀ : Pi.single (0 : Fin 2) (1 : F) = ![1, 0] := by
    funext i; fin_cases i <;> simp
  have h₁ : Pi.single (1 : Fin 2) (1 : F) = ![0, 1] := by
    funext i; fin_cases i <;> simp
  rw [h₀, h₁]
  rfl

theorem standard_character : Spec.standardCharacter := by
  intro F _
  have ht₀ : transposition⁻¹ (0 : Fin 3) = 1 := by decide
  have ht₁ : transposition⁻¹ (1 : Fin 3) = 0 := by decide
  have hc₀ : threeCycle⁻¹ (0 : Fin 3) = 2 := by decide
  have hc₁ : threeCycle⁻¹ (1 : Fin 3) = 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [Representation.char_one, standard_dimension F]
    norm_num
  · rw [trace_in_coordinates, standard_apply, standard_apply, ht₀, ht₁]
    change (0 : F) + 0 = 0
    simp
  · rw [trace_in_coordinates, standard_apply, standard_apply, hc₀, hc₁]
    change (-(1 + 0) : F) + 0 = -1
    simp

private theorem one_dimensional_irreducible (F : Type*) [Field F]
    (ρ : Representation F Group F) : Representation.IsIrreducible ρ := by
  have hnt : Nontrivial (Subrepresentation ρ) := nontrivial_of_ne ⊤ ⊥ fun h =>
    top_ne_bot (congrArg Subrepresentation.toSubmodule h)
  refine ⟨fun U => ?_⟩
  rcases eq_bot_or_eq_top U.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem standard_simple : Spec.standardSimple := by
  intro F _ hthree
  have hdim := standard_dimension F
  have : Nontrivial (Plane F) :=
    Module.nontrivial_of_finrank_pos (R := F) (by rw [hdim]; decide)
  have : Nontrivial (Subrepresentation (standard F)) := nontrivial_of_ne ⊤ ⊥ fun h =>
    top_ne_bot (congrArg Subrepresentation.toSubmodule h)
  apply IsSimpleOrder.of_forall_eq_top
  intro U hU
  have hUne : U.toSubmodule ≠ ⊥ := fun h =>
    hU (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have ht₀ : transposition⁻¹ (0 : Fin 3) = 1 := by decide
  have ht₁ : transposition⁻¹ (1 : Fin 3) = 0 := by decide
  let s : Group := Equiv.swap 1 2
  have hs₀ : s⁻¹ (0 : Fin 3) = 0 := by decide
  have hs₁ : s⁻¹ (1 : Fin 3) = 2 := by decide
  let r : Group := Equiv.swap 0 2
  have hr₀ : r⁻¹ (0 : Fin 3) = 2 := by decide
  have hr₁ : r⁻¹ (1 : Fin 3) = 1 := by decide
  have extract (g : Group) (j : Fin 3) (hg : g⁻¹ (0 : Fin 3) = j)
      (hneq : x.val 0 ≠ x.val j) (b : F)
      (hb : x.val 1 - x.val (g⁻¹ 1) = (x.val 0 - x.val j) * b) :
      fromCoordinates F 1 b ∈ U.toSubmodule := by
    let a := x.val 0 - x.val j
    have ha : a ≠ 0 := sub_ne_zero.mpr hneq
    have hm := U.toSubmodule.smul_mem a⁻¹
      (U.toSubmodule.sub_mem hx (U.apply_mem_toSubmodule g hx))
    convert hm using 1
    apply plane_ext F
    · change (1 : F) = a⁻¹ * (x.val 0 - x.val (g⁻¹ 0))
      rw [hg, ← show a = x.val 0 - x.val j from rfl, inv_mul_cancel₀ ha]
    · change b = a⁻¹ * (x.val 1 - x.val (g⁻¹ 1))
      rw [hb, ← show a = x.val 0 - x.val j from rfl, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have he₀ : fromCoordinates F 1 0 ∈ U.toSubmodule := by
    by_cases h : x.val 0 = x.val 1
    · have hh : x.val 0 ≠ x.val 2 := by
        intro hh
        apply hx₀
        have hz : ∑ i : Fin 3, x.val i = 0 := x.property
        rw [Fin.sum_univ_three, ← h, ← hh] at hz
        have hprod : 3 * x.val 0 = 0 := by linear_combination hz
        have hz₀ := (mul_eq_zero.mp hprod).resolve_left hthree
        exact plane_ext F hz₀ (h ▸ hz₀)
      exact extract r 2 hr₀ hh 0 (by simp [hr₁])
    · have hm := U.apply_mem_toSubmodule s
        (extract transposition 1 ht₀ h (-1) (by rw [ht₁]; ring))
      convert hm using 1
      exact plane_ext F (by rw [standard_apply, hs₀]; rfl)
        (by rw [standard_apply, hs₁]; change (0 : F) = -(1 + -1); simp)
  have he₁ : fromCoordinates F 0 1 ∈ U.toSubmodule := by
    have hm := U.apply_mem_toSubmodule transposition he₀
    convert hm using 1
    exact plane_ext F (by rw [standard_apply, ht₀]; rfl)
      (by rw [standard_apply, ht₁]; rfl)
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro y _
  have hy := U.toSubmodule.add_mem (U.toSubmodule.smul_mem (y.val 0) he₀)
    (U.toSubmodule.smul_mem (y.val 1) he₁)
  convert hy using 1
  exact plane_ext F (by change y.val 0 = y.val 0 * 1 + y.val 1 * 0; simp)
    (by change y.val 1 = y.val 0 * 0 + y.val 1 * 1; simp)


private def restrictModuleEquiv (F : Type*) [Field F] {A : Type*} [Ring A] [Algebra F A]
    {M : Type*} [AddCommGroup M] [Module A M] {N : Type*} [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) : RestrictScalars F A M ≃ₗ[F] RestrictScalars F A N where
  __ := e.toAddEquiv
  map_smul' r x := e.map_smul (algebraMap F A r) x

private theorem trivial_sign_distinct (F : Type*) [Field F] [CharZero F]
    (e : (trivial F).asModule ≃ₗ[MonoidAlgebra F Group] (sign F).asModule) : False := by
  let f := (Representation.IntertwiningMap.equivLinearMapAsModule
    (trivial F) (sign F)).symm e.toLinearMap
  have hf : Function.Bijective f := by
    change Function.Bijective (fun x : F => e x)
    exact e.bijective
  have h := congrFun (Representation.char_iso (f.ofBijective hf)) transposition
  rw [trivial_character F transposition, sign_character F transposition,
    sign_representatives.1] at h
  norm_num at h

private theorem ordinary_simple (F : Type*) [Field F] [CharZero F] (i : Fin 3) :
    IsSimpleModule (MonoidAlgebra F Group) (ordinaryFamily F i) := by
  fin_cases i
  · exact (Representation.irreducible_iff_isSimpleModule_asModule (trivial F)).mp
      (one_dimensional_irreducible F (trivial F))
  · exact (Representation.irreducible_iff_isSimpleModule_asModule (sign F)).mp
      (one_dimensional_irreducible F (sign F))
  · exact (Representation.irreducible_iff_isSimpleModule_asModule (standard F)).mp
      (standard_simple F (by norm_num))

private theorem ordinary_eq_of_iso (F : Type*) [Field F] [CharZero F]
    {i j : Fin 3} (e : ordinaryFamily F i ≃ₗ[MonoidAlgebra F Group] ordinaryFamily F j) :
    i = j := by
  have hrank := (restrictModuleEquiv F e).finrank_eq
  rw [ordinary_dimensions F i, ordinary_dimensions F j] at hrank
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | solve | norm_num at hrank
    | exact (trivial_sign_distinct F e).elim
    | exact (trivial_sign_distinct F e.symm).elim

private theorem group_card : Fintype.card Group = 6 := by decide

theorem ordinary_simple_family : Spec.ordinarySimpleFamily := by
  intro O _ _ _ K _ _ p S
  let := S.charZero
  refine ⟨ordinary_simple K, (fun ⟨e⟩ => ordinary_eq_of_iso K e), ?_⟩
  obtain ⟨n, d, hd, e, hC⟩ := ordinary_columns_exist S.ordinarySplit
  let C := columnModule e.toAlgHom
  choose a ha using fun i => hC.exhaustive (ordinaryFamily K i) (ordinary_simple K i)
  let equivToColumn (i : Fin 3) := (ha i).some
  have hainj : Function.Injective a := by
    intro i j hij
    have h : Nonempty (C (a i) ≃ₗ[MonoidAlgebra K Group] C (a j)) := by
      rw [hij]
      exact ⟨LinearEquiv.refl _ _⟩
    exact ordinary_eq_of_iso K ((equivToColumn i).trans (h.some.trans (equivToColumn j).symm))
  have hdims (i : Fin 3) : d (a i) = (![1, 1, 2] : Fin 3 → ℕ) i := by
    calc
      _ = Module.finrank K (C (a i)) := (column_finrank e.toAlgHom _).symm
      _ = Module.finrank K (RestrictScalars K (MonoidAlgebra K Group) (C (a i))) :=
        (restrictionEquiv K).finrank_eq.symm
      _ = _ := (restrictModuleEquiv K (equivToColumn i)).finrank_eq.symm.trans
        (ordinary_dimensions K i)
  have hsum : ∑ i : Fin n, d i ^ 2 = 6 := by
    calc
      _ = Module.finrank K ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) K) := by
        rw [Module.finrank_pi_fintype]
        simp [Module.finrank_matrix, pow_two]
      _ = Module.finrank K (MonoidAlgebra K Group) := e.toLinearEquiv.symm.finrank_eq
      _ = 6 := (Module.finrank_eq_card_basis (MonoidAlgebra.basis Group K)).trans group_card
  classical
  let image := Finset.univ.image a
  have himage : ∑ i ∈ image, d i ^ 2 = 6 := by
    rw [Finset.sum_image (fun _ _ _ _ h => hainj h)]
    simp [hdims, Fin.sum_univ_three]
  have hsurj : Function.Surjective a := by
    intro j
    by_contra hj
    have hj' : j ∉ image := by
      simpa [image] using hj
    have hle : d j ^ 2 + 6 ≤ 6 := by
      calc
        _ = ∑ i ∈ insert j image, d i ^ 2 := by rw [Finset.sum_insert hj', himage]
        _ ≤ ∑ i : Fin n, d i ^ 2 := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = 6 := hsum
    have := hd j
    nlinarith
  intro M hM
  obtain ⟨j, ⟨f⟩⟩ := hC.exhaustive M hM
  obtain ⟨i, rfl⟩ := hsurj j
  exact ⟨i, ⟨f.trans (equivToColumn i).symm⟩⟩


private theorem coordinate_expansion (R : Type*) [CommRing R] (x : Plane R) :
    x = x.val 0 • fromCoordinates R 1 0 + x.val 1 • fromCoordinates R 0 1 :=
  plane_ext R (by change x.val 0 = x.val 0 * 1 + x.val 1 * 0; simp)
    (by change x.val 1 = x.val 0 * 0 + x.val 1 * 1; simp)

open scoped Pointwise

private theorem residue_equiv_of_coordinates
    (O : Type*) [CommRing O] [IsLocalRing O] {M : Type*} [AddCommGroup M] [Module O M]
    (σ : Representation O Group M) (j : Plane O ≃ₗ[O] M)
    (hjg : ∀ g x, σ g (j x) = j (standard O g x)) :
    ∃ e : (residueRepresentation σ).Equiv (standard (IsLocalRing.ResidueField O)),
      ∀ x, e (reduce (O := O) (j x)) = coordinateReduction O x := by
  let k := IsLocalRing.ResidueField O
  let := Module.restrictScalars O k (Plane k)
  let := IsScalarTower.restrictScalars O k (Plane k)
  let f : M →ₗ[O] Plane k := (coordinateReduction O).comp j.symm.toLinearMap
  have hf (x : Plane O) : f (j x) = coordinateReduction O x := by
    change coordinateReduction O (j.symm (j x)) = _
    rw [j.symm_apply_apply]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (y.val 0)
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (y.val 1)
    refine ⟨j (fromCoordinates O a b), ?_⟩
    rw [hf]
    exact plane_ext k ha hb
  let I := IsLocalRing.maximalIdeal O
  have inIdeal {r : O} : IsLocalRing.residue O r = 0 ↔ r ∈ I := by
    change IsLocalRing.residue O r = 0 ↔ r ∈ IsLocalRing.maximalIdeal O
    rw [← IsLocalRing.ker_residue (R := O)]
    exact RingHom.mem_ker.symm
  have hker : LinearMap.ker f = I • (⊤ : Submodule O M) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := j.surjective y
      have hz := LinearMap.mem_ker.mp hy
      rw [hf] at hz
      have ha (i : Fin 3) : x.val i ∈ I :=
        inIdeal.mp (congrArg (fun z : Plane k => z.val i) hz)
      have he : j x = x.val 0 • j (fromCoordinates O 1 0) +
          x.val 1 • j (fromCoordinates O 0 1) := by
        conv_lhs => rw [coordinate_expansion O x]
        rw [map_add, map_smul, map_smul]
      rw [he]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul (ha 0) Submodule.mem_top)
        (Submodule.smul_mem_smul (ha 1) Submodule.mem_top)
    · apply Submodule.smul_le.mpr
      intro r hr y _
      apply LinearMap.mem_ker.mpr
      rw [map_smul]
      change (IsLocalRing.residue O r : k) • f y = 0
      rw [inIdeal.mpr hr, zero_smul]
  let q₀ : ResidueQuotient O M ≃ₗ[O] Plane k :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)
  let q : ResidueQuotient O M ≃ₗ[k] Plane k :=
    q₀.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := O))
  have hq (x : M) : q (reduce (O := O) x) = f x := rfl
  let e : (residueRepresentation σ).Equiv (standard k) := Representation.Equiv.mk q (by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
      (I • (⊤ : Submodule O M)) y
    obtain ⟨z, rfl⟩ := j.surjective x
    change q (residueRepresentation σ g (reduce (O := O) (j z))) =
      standard k g (q (reduce (O := O) (j z)))
    rw [residueRepresentation_reduce, hjg, hq, hq, hf, hf]
    rfl)
  exact ⟨e, fun x => (hq (j x)).trans (hf x)⟩

set_option backward.isDefEq.respectTransparency false in
theorem standard_lattice_reduction : Spec.standardLatticeReduction := by
  intro O _ _ _ K _ _ p S
  let := Module.restrictScalars O K (Plane K)
  let := IsScalarTower.restrictScalars O K (Plane K)
  let := S.fractionRing
  let emb := integralEmbedding O K
  have hemb : Function.Injective emb := by
    intro x y h
    apply Subtype.ext
    funext i
    apply IsFractionRing.injective O K
    exact congrArg (fun z : Plane K => z.val i) h
  let j := LinearEquiv.ofInjective emb hemb
  have hj (x : Plane O) : (j x : Plane K) = emb x := rfl
  have spans : Submodule.span K (LinearMap.range emb : Set (Plane K)) = ⊤ := by
    apply top_unique
    intro y _
    have h₀ : fromCoordinates K 1 0 ∈ LinearMap.range emb := by
      refine ⟨fromCoordinates O 1 0, plane_ext K ?_ ?_⟩
      · exact map_one (algebraMap O K)
      · exact map_zero (algebraMap O K)
    have h₁ : fromCoordinates K 0 1 ∈ LinearMap.range emb := by
      refine ⟨fromCoordinates O 0 1, plane_ext K ?_ ?_⟩
      · exact map_zero (algebraMap O K)
      · exact map_one (algebraMap O K)
    rw [coordinate_expansion K y]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span h₀))
      (Submodule.smul_mem _ _ (Submodule.subset_span h₁))
  let b := (coordinateBasis O).map j
  let L : StableLattice O (standard K) := {
    carrier := LinearMap.range emb
    finite := Module.Finite.of_basis b
    free := Module.Free.of_basis b
    spans := spans
    stable := by
      rintro g v ⟨x, rfl⟩
      exact ⟨standard O g x, rfl⟩ }
  let σ := MR04LatticeSpec.integralAction O L
  have hjg (g : Group) (x : Plane O) : σ g (j x) = j (standard O g x) := by
    apply Subtype.ext
    rfl
  obtain ⟨e, he⟩ := residue_equiv_of_coordinates O (M := L.carrier) σ j hjg
  exact ⟨L, j, e, hj, he⟩

end
end RepTheorySurvey.Modular.SymmetricThree
