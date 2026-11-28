import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Affine.NoCartanDisjointIdeals
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.WeightExtraction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces
import Batteries.Tactic.OpenPrivate

namespace LieNotes.Affine

open RepTheorySurvey.Affine
open Specs.RepTheorySurvey.Affine.TriangularRootSpaces (coordinates homogeneousLinear)
open LieAlgebrasAndRepresentations (rootSet rootSpace)

open private cartanMaximalToral from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra
open private rootSpace_pairing_separating from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition
open private coordinates_homogeneous coordinates_K from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces

universe u

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
  [LieAlgebra.IsSimple ℂ G]

private theorem exists_opposite_root_bracket (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (α : rootSet H) {x : G} (hx : x ∈ rootSpace H α.val) (hx₀ : x ≠ 0) :
    ∃ y ∈ rootSpace H (-α.val), ⁅x, y⁆ ∈ H ∧ ⁅x, y⁆ ≠ 0 := by
  open LieAlgebrasAndRepresentations in
  have hss : IsSemisimple ℂ G := LieAlgebra.radical_eq_bot
  have hH := cartanMaximalToral H
  obtain ⟨y, hy, hpair⟩ :
      ∃ y ∈ rootSpace H (-α.val), LieAlgebrasAndRepresentations.killingForm ℂ G x y ≠ 0 := by
    by_contra! hz
    exact hx₀ (rootSpace_pairing_separating hss H hH α.val x hx hz)
  have hbr := LieAlgebrasAndRepresentations.opposite_root_bracket hss H hH α.val x y hx hy
  have ht : (LieAlgebrasAndRepresentations.tAlpha H α.val : G) ≠ 0 := by
    intro he
    apply α.property.1
    ext h
    rw [← LieAlgebrasAndRepresentations.tAlpha_pairing hss H hH, he]
    simp
  refine ⟨y, hy, ?_, ?_⟩
  · rw [hbr]
    exact H.smul_mem _ (LieAlgebrasAndRepresentations.tAlpha H α.val).property
  · rw [hbr]
    exact smul_ne_zero hpair ht

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] in
private theorem homogeneous_opposite_bracket (B : InvariantForm G) (m : ℤ) (x y : G) :
    ⁅homogeneous B m x, homogeneous B (-m) y⁆ =
      homogeneous B 0 ⁅x, y⁆ + ((m : ℂ) * B.form x y) • K B := by
  rw [homogeneousBracket]
  simp

/-- Every nonzero ideal of the normalized untwisted affine loop model meets
the Cartan consisting of the constant finite Cartan, the center, and the degree line. -/
theorem nonzeroIdeal_meets_affineCartan (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (hB : B.IsNormalized H) (I : LieIdeal ℂ (AffineAlgebra B))
    (hI : I ≠ ⊥) : I.toSubmodule ⊓ affineCartan B H ≠ ⊥ := by
  classical
  let A := affineCartan B H
  let : LieRing (Module.End ℂ (AffineAlgebra B)) := LieRing.ofAssociativeRing
  let ρ : A →ₗ[ℂ] Module.End ℂ (AffineAlgebra B) :=
    (LieModule.toEnd ℂ (AffineAlgebra B) (AffineAlgebra B)).toLinearMap.comp A.subtype
  have hweight (χ : Module.Dual ℂ A) :
      Contragredient.weightSpace ρ χ = affineWeightSpace B H χ := by
    ext x
    rfl
  have hstable (h : A) ⦃x : AffineAlgebra B⦄ (hx : x ∈ I.toSubmodule) :
      ρ h x ∈ I.toSubmodule :=
    lie_mem_right ℂ (AffineAlgebra B) I h x hx
  have hspan : (⨆ χ, Contragredient.weightSpace ρ χ) = ⊤ := by
    simp only [hweight]
    exact (adjointWeightDecomposition B H).submodule_iSup_eq_top
  have hsplit := Contragredient.iSup_inf_weightSpace_eq ρ I.toSubmodule hstable id
    Function.injective_id hspan
  have hnonzero : ∃ χ : Module.Dual ℂ A, I.toSubmodule ⊓ affineWeightSpace B H χ ≠ ⊥ := by
    by_contra! h
    apply hI
    apply (LieSubmodule.toSubmodule_eq_bot I).mp
    rw [← hsplit]
    simp only [id_eq, hweight, h, iSup_bot]
  obtain ⟨χ, hχ⟩ := hnonzero
  obtain ⟨v, ⟨hvI, hvχ⟩, hv₀⟩ := (Submodule.ne_bot_iff _).mp hχ
  by_cases hz : χ = 0
  · rw [hz, affineWeightSpace_zero B H] at hvχ
    exact (Submodule.ne_bot_iff _).mpr ⟨v, ⟨hvI, hvχ⟩, hv₀⟩
  obtain (⟨α, m, rfl⟩ | ⟨m, hm, rfl⟩) :=
    (nonzeroWeights B H χ).mp ⟨hz, v, hv₀, (mem_affineWeightSpace B H χ v).mp hvχ⟩
  · rw [affineWeightSpace_real B H α m] at hvχ
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hvχ
    have hx₀ : x ≠ 0 := fun he => hv₀ (he ▸ (homogeneousLinear B m).map_zero)
    obtain ⟨y, -, hxyH, hxy₀⟩ := exists_opposite_root_bracket H α hx hx₀
    have hbI := lie_mem_left ℂ (AffineAlgebra B) I (homogeneous B m x) (homogeneous B (-m) y) hvI
    rw [homogeneous_opposite_bracket] at hbI
    refine (Submodule.ne_bot_iff _).mpr ⟨_, ⟨hbI, ?_⟩, ?_⟩
    · exact A.add_mem (cartanIncl B H ⟨_, hxyH⟩).property
        (A.smul_mem _ (cartanK B H).property)
    · intro he
      apply hxy₀
      have hc := congrArg (fun z : AffineAlgebra B => (coordinates B z).1.1 0) he
      simpa only [map_add, map_smul, map_zero, coordinates_homogeneous, coordinates_K,
        Prod.fst_add, Prod.smul_mk, Prod.fst_smul, Prod.fst_zero, Finsupp.add_apply,
        Finsupp.smul_apply,
        Finsupp.single_eq_same, Finsupp.zero_apply, smul_zero, add_zero] using hc
  · rw [affineWeightSpace_imaginary B H m hm] at hvχ
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hvχ
    let h : H := ⟨x, hx⟩
    have hh₀ : h ≠ 0 := by
      intro he
      have hx₀ : x = 0 := congrArg Subtype.val he
      exact hv₀ (hx₀ ▸ (homogeneousLinear B m).map_zero)
    obtain ⟨h', hh'⟩ : ∃ h' : H, B.form (h : G) (h' : G) ≠ 0 := by
      by_contra! hn
      exact hh₀ ((cartanNondegenerate H B hB.1).1 h hn)
    have hcomm : ⁅(h : G), (h' : G)⁆ = 0 := by
      let : IsLieAbelian H := cartanAbelian H
      exact congrArg Subtype.val (trivial_lie_zero H H h h')
    have hbI := lie_mem_left ℂ (AffineAlgebra B) I (homogeneous B m (h : G)) (homogeneous B (-m) (h' : G)) hvI
    rw [homogeneous_opposite_bracket, hcomm] at hbI
    change homogeneousLinear B 0 0 + _ ∈ I at hbI
    rw [map_zero, zero_add] at hbI
    refine (Submodule.ne_bot_iff _).mpr ⟨_, ⟨hbI, A.smul_mem _ (cartanK B H).property⟩, ?_⟩
    apply smul_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hm) hh')
    intro he
    have hc := congrArg (fun z : AffineAlgebra B => (coordinates B z).1.2) he
    simp only [map_zero, coordinates_K, Prod.fst_zero, Prod.snd_zero, one_ne_zero] at hc

end LieNotes.Affine
