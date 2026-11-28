import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.CartanMatrix
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeBlocksTwo
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeBlocksThree
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeDecompositionThree
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeExample

/-! The symmetric group of degree three at two and at three. -/

namespace RepTheorySurvey.Modular.SymmetricThree

universe u v

open IsLocalRing (ResidueField)
open CompositionMultiplicity (GroundFinite multiplicity)
open SplitMatrixColumnsSpec (columnModule modularColumnMap)
open ExampleSpec (HasCartanMatrix IsProjectiveCover)

open private exists_brauer_basis from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.DecompositionMatrix
open private ordinaryRestriction_congr decompositionMultiplicity_eq_coordinate
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.CartanMatrix

set_option backward.isDefEq.respectTransparency false

private theorem cover_equiv {A : Type u} [Ring A] {P Q S : ModuleCat.{u} A}
    (hP : IsProjectiveCover P S) (hQ : IsProjectiveCover Q S) : Nonempty (P ≃ₗ[A] Q) := by
  obtain ⟨hP, f, hf, hfmin⟩ := hP
  obtain ⟨hQ, g, hg, hgmin⟩ := hQ
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g f hg
  have hlRange : LinearMap.range l = ⊤ := by
    apply hgmin
    rw [← Submodule.map_top, ← Submodule.map_comp, hl, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  obtain ⟨s, hs⟩ := l.exists_rightInverse_of_surjective hlRange
  have hsRange : LinearMap.range s = ⊤ := by
    apply hfmin
    have hfs : f.comp s = g := by
      rw [← hl, LinearMap.comp_assoc, hs, LinearMap.comp_id]
    rw [← Submodule.map_top, ← Submodule.map_comp, hfs, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hg
  have hlInjective : Function.Injective l := by
    have hsSurjective := LinearMap.range_eq_top.mp hsRange
    intro x y hxy
    obtain ⟨x, rfl⟩ := hsSurjective x
    obtain ⟨y, rfl⟩ := hsSurjective y
    have hleft (z : Q) : l (s z) = z := LinearMap.congr_fun hs z
    rw [hleft, hleft] at hxy
    rw [hxy]
  exact ⟨LinearEquiv.ofBijective l ⟨hlInjective, LinearMap.range_eq_top.mp hlRange⟩⟩

section Cartan

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type v} [Field K] [Algebra O K] {p : ℕ}

local notation "k" => ResidueField O
local notation "A" => MonoidAlgebra k Group
local notation "KG" => MonoidAlgebra K Group

-- MR09 takes the ordinary modules in a universe at least as large as the residue field.
private noncomputable abbrev LiftedOrdinary (K : Type v) [Field K] :
    Fin 3 → ModuleCat.{max u v} (MonoidAlgebra K Group) :=
  fun χ => ModuleCat.of _ (ULift.{u} (ordinaryFamily K χ))

private theorem lifted_ordinary_family (system : SplittingSystem Group p O K) :
    IsSimpleRepresentativeFamily (LiftedOrdinary.{u, v} K) := by
  have hV := ordinary_simple_family system
  let E (χ : Fin 3) : LiftedOrdinary.{u, v} K χ ≃ₗ[KG] ordinaryFamily K χ := ULift.moduleEquiv
  refine ⟨fun χ => (E χ).isSimpleModule_iff.mpr (hV.simple χ), ?_, ?_⟩
  · rintro i j ⟨f⟩
    exact hV.eq_of_iso ⟨(E i).symm.trans (f.trans (E j))⟩
  · intro M hM
    obtain ⟨r, d, hd, split, hT⟩ := ordinary_columns_exist system.ordinarySplit
    have hker : RingHom.ker split.toRingHom ≤ Ring.jacobson KG := by
      intro a ha
      have hz : split a = 0 := RingHom.mem_ker.mp ha
      rw [(map_eq_zero_iff split split.injective).mp hz]
      exact (Ring.jacobson KG).zero_mem
    obtain ⟨j, ⟨f⟩⟩ := column_exhaustive split.toAlgHom hd split.surjective hker M hM
    obtain ⟨χ, ⟨e⟩⟩ := hV.exhaustive (columnModule split.toAlgHom j) (hT.simple j)
    exact ⟨χ, ⟨f.trans (e.trans (E χ).symm)⟩⟩

private theorem cartan_in_simple_order (system : SplittingSystem Group p O K)
    (S : Fin 2 → ModuleCat.{u} A) (hS : IsSimpleRepresentativeFamily S) :
    let D := decompositionMatrix system (ordinaryFamily K) S
    HasCartanMatrix S (D.transpose * D) := by
  classical
  intro D
  let : CharZero K := system.charZero
  obtain ⟨r, d, hd, split, hT⟩ := modular_columns_exist system.modularSplit
  let q := modularColumnMap split
  let T := columnModule q
  -- Match the split factors to the prescribed modular column order.
  choose a ha using fun i => hT.exhaustive (S i) (hS.simple i)
  let F (i : Fin 2) : S i ≃ₗ[A] T (a i) := (ha i).some

  let s (j : Fin r) : Fin (d j) := ⟨0, hd j⟩
  let E (j : Fin r) : Matrix (Fin (d j)) (Fin (d j)) k :=
    Matrix.diagonal (Pi.single (s j) 1)
  have hE (j : Fin r) : IsIdempotentElem (E j) := by
    change E j * E j = E j
    dsimp only [E]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext x
    by_cases hx : x = s j <;> simp [hx]
  have hrankE (j : Fin r) : (E j).rank = 1 := by
    dsimp only [E]
    rw [Matrix.rank_diagonal, Fintype.card_eq_one_iff]
    refine ⟨⟨s j, by simp⟩, ?_⟩
    rintro ⟨x, hx⟩
    apply Subtype.ext
    by_contra hne
    exact hx (by simp [hne])
  choose eBar heBar hEBar using
    fun j => exists_modular_rank_one_idempotent_lift split j (E j) (hE j) (hrankE j)
  choose e he hred using fun j => exists_integral_idempotent_lift system (eBar j) (heBar j)
  have hrank (j : Fin r) : (q (eBar j) j).rank = 1 := by
    rw [hEBar j, Pi.single_eq_same, hrankE]
  have hzero (i j : Fin r) (hj : j ≠ i) : q (eBar i) j = 0 := by
    rw [hEBar i, Pi.single_eq_of_ne hj]

  let V := ordinaryFamily K
  let VL := LiftedOrdinary.{u, v} K
  have hV : IsSimpleRepresentativeFamily V := ordinary_simple_family system
  have hVL : IsSimpleRepresentativeFamily VL := lifted_ordinary_family system
  obtain ⟨hcover, _, hcartan⟩ :=
    cartanMatrix_formula.{0, u, v, 0, 0} system split hd VL hVL
      eBar e heBar he hred hrank hzero
  let P₀ (j : Fin r) : ModuleCat.{u} A :=
    ModuleCat.of A (MR09CoversSpec.principalLeftIdealValue (eBar j))
  have hP₀ (j : Fin 2) : IsProjectiveCover (P₀ (a j)) (S j) := by
    obtain ⟨hP, top, hsurj, hmin⟩ := hcover (a j)
    let f := top.toLinearMap.comp
      (Ring.jacobson A • (⊤ : Submodule A (P₀ (a j)))).mkQ
    let g := (F j).symm.toLinearMap
    refine ⟨hP, g.comp f, (F j).symm.surjective.comp hsurj, ?_⟩
    intro U hU
    apply hmin
    apply (Submodule.map_injective_of_injective (F j).symm.injective)
    rw [← Submodule.map_comp, hU, Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr (F j).symm.surjective).symm

  -- The universe lift preserves the ordinary character. The same lattice then
  -- computes the multiplicities for either representative of each modular simple.
  obtain ⟨b, hb⟩ := exists_brauer_basis system T hT
  have hentry (χ : Fin 3) (i : Fin 2) :
      decompositionMatrix system VL T χ (a i) = D χ i := by
    let := hV.simple χ
    let := hVL.simple χ
    let := hS.simple i
    let := hT.simple (a i)
    let : GroundFinite K Group (V χ) := CompositionMultiplicity.groundFinite_of_simple
    let : GroundFinite K Group (VL χ) := CompositionMultiplicity.groundFinite_of_simple
    have hLift :
        decompositionMultiplicity system (VL χ) (T (a i)) =
          decompositionMultiplicity system (V χ) (T (a i)) := by
      let l : VL χ ≃ₗ[KG] V χ := ULift.moduleEquiv
      apply Nat.cast_injective (R := K)
      rw [← decompositionMultiplicity_eq_coordinate system T hT b hb (VL χ) (a i),
        ← decompositionMultiplicity_eq_coordinate system T hT b hb (V χ) (a i),
        ordinaryRestriction_congr (p := p) l]
    let : Module.Finite K (RestrictScalars K KG (V χ)) := ‹GroundFinite K Group (V χ)›
    obtain ⟨L⟩ := exists_nativeStableLattice system (V χ)
    let : GroundFinite k Group (NativeStableLattice.reduction L) :=
      MR04Spec.nativeReductionFinite (V χ) L
    calc
      _ = decompositionMultiplicity system (V χ) (T (a i)) := hLift
      _ = multiplicity k Group (NativeStableLattice.reduction L) (T (a i)) :=
        decompositionMultiplicity_eq_lattice system (V χ) (T (a i)) L
      _ = multiplicity k Group (NativeStableLattice.reduction L) (S i) :=
        CompositionMultiplicity.multiplicity_congr (LinearEquiv.refl A _) (F i).symm
      _ = _ := (decompositionMultiplicity_eq_lattice system (V χ) (S i) L).symm

  refine ⟨⟨fun j => P₀ (a j), hP₀⟩, ?_⟩
  intro P hP i j
  obtain ⟨equiv⟩ := cover_equiv (hP j) (hP₀ j)
  let : GroundFinite k Group A := CompositionMultiplicity.groundFinite_groupAlgebra
  let : GroundFinite k Group (P₀ (a j)) :=
    CompositionMultiplicity.groundFinite_of_injective
      (MR09CoversSpec.principalLeftIdealValue (eBar (a j))).subtype Subtype.val_injective
  let : GroundFinite k Group (P j) :=
    CompositionMultiplicity.groundFinite_of_injective equiv.toLinearMap equiv.injective
  calc
    _ = multiplicity k Group (P₀ (a j)) (T (a i)) :=
      CompositionMultiplicity.multiplicity_congr equiv (F i)
    _ = ∑ χ, decompositionMatrix system VL T χ (a i) * decompositionMatrix system VL T χ (a j) :=
      congrFun (congrFun hcartan (a i)) (a j)
    _ = _ := by simp only [Matrix.mul_apply, Matrix.transpose_apply, hentry]

end Cartan

/-- The ordered decomposition and Cartan matrices and the two blocks in characteristic two. -/
theorem example_at_two : ExampleSpec.atTwo.{u, v} := by
  intro O _ _ _ K _ _ system k V S
  have hS := modular_simple_family_two system
  have hD : decompositionMatrix system V S = !![1, 0; 1, 0; 0, 1] :=
    decomposition_matrix_two system
  have hC := cartan_in_simple_order system S hS
  change HasCartanMatrix S
    ((decompositionMatrix system V S).transpose * decompositionMatrix system V S) at hC
  rw [hD] at hC
  have hm :
      (!![1, 0; 1, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℕ).transpose * !![1, 0; 1, 0; 0, 1] =
        !![2, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [hm] at hC
  obtain ⟨b, bPrincipal, _, _, hne, hall, _, _, hp, hb, hd⟩ := blocks_two system
  exact ⟨ordinary_simple_family system, hS, hD, hC, b, bPrincipal, hp, hne, hall, hb, hd⟩

/-- The ordered decomposition and Cartan matrices and the unique block in characteristic three. -/
theorem example_at_three : ExampleSpec.atThree.{u, v} := by
  intro O _ _ _ K _ _ system k V S
  have hS := modular_simple_family_three system
  have hD : decompositionMatrix system V S = !![1, 0; 0, 1; 1, 1] :=
    decomposition_matrix_three system
  have hC := cartan_in_simple_order system S hS
  change HasCartanMatrix S
    ((decompositionMatrix system V S).transpose * decompositionMatrix system V S) at hC
  rw [hD] at hC
  have hm :
      (!![1, 0; 0, 1; 1, 1] : Matrix (Fin 3) (Fin 2) ℕ).transpose * !![1, 0; 0, 1; 1, 1] =
        !![2, 1; 1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [hm] at hC
  exact ⟨ordinary_simple_family system, hS, hD, hC, blocks_three system⟩

end RepTheorySurvey.Modular.SymmetricThree
