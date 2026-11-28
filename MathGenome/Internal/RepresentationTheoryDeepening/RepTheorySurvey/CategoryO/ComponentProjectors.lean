import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ComponentProjectors
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.FiniteLength
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CentralCharacters
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open scoped Classical ModuleCat.Algebra

namespace RepTheorySurvey.CategoryO.ComponentProjectors
attribute [local instance 100] LieRing.ofAssociativeRing

open Specs.RepTheorySurvey.CategoryO.ComponentProjectors
export Specs.RepTheorySurvey.CategoryO.ComponentProjectors
  (Center CentralCharacter Coset Index)

abbrev coset := @Specs.RepTheorySurvey.CategoryO.ComponentProjectors.coset
abbrev centralPart := @Specs.RepTheorySurvey.CategoryO.ComponentProjectors.centralPart
abbrev cosetPart := @Specs.RepTheorySurvey.CategoryO.ComponentProjectors.cosetPart
abbrev component := @Specs.RepTheorySurvey.CategoryO.ComponentProjectors.component
abbrev componentMap := @Specs.RepTheorySurvey.CategoryO.ComponentProjectors.componentMap
abbrev ambientFunctor := @Specs.RepTheorySurvey.CategoryO.ComponentProjectors.ambientFunctor
abbrev componentFunctor := @Specs.RepTheorySurvey.CategoryO.ComponentProjectors.componentFunctor
abbrev projection := @Specs.RepTheorySurvey.CategoryO.ComponentProjectors.projection

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g]

theorem centralPart_membership : CentralPartType.{u, v} := by
  intro g _ _ X χ x
  exact centerPart_mem X

-- The ideal of central elements with zero evaluation under a character.
private abbrev characterIdeal (χ : CentralCharacter g) : Ideal (Center g) :=
  RingHom.ker χ.toRingHom

private theorem difference_mem (χ : CentralCharacter g) (z : Center g) :
    difference χ z ∈ characterIdeal χ := by
  change χ (z - algebraMap ℂ (Center g) (χ z)) = 0
  simp

private theorem characterIdeal_coprime {χ ψ : CentralCharacter g} (h : χ ≠ ψ) :
    IsCoprime (characterIdeal χ) (characterIdeal ψ) := by
  obtain ⟨z, hz⟩ := Function.ne_iff.mp (fun he => h (DFunLike.coe_injective he))
  let d := difference χ z
  have hd : ψ d ≠ 0 := by
    change ψ (z - algebraMap ℂ (Center g) (χ z)) ≠ 0
    simpa [sub_eq_zero] using Ne.symm hz
  let a := algebraMap ℂ (Center g) (ψ d)⁻¹ * d
  have ha : ψ a = 1 := by simp [a, hd]
  exact Ideal.isCoprime_iff_exists.mpr
    ⟨a, (characterIdeal χ).mul_mem_left _ (difference_mem χ z), 1 - a,
      by change ψ (1 - a) = 0; simp [ha], by abel⟩


section RootCosets

open Specs.LieAlgebrasAndRepresentations
open private positiveRoot_mem_cone from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open private neg_root_mem from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations

variable [FiniteDimensional ℂ g] (D : Setup g)

theorem positiveCone_mem_rootLattice {α : D.Weight} (h : α ∈ QPlus D) : α ∈ Q D := by
  change α ∈ Submodule.span ℕ (Set.range D.alpha) at h
  induction h using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact (Q D).zero_mem
  | add x y _ _ hx hy => exact (Q D).add_mem hx hy
  | smul n x _ hx =>
    simpa only [Nat.cast_smul_eq_nsmul] using (Q D).smul_mem (n : ℤ) hx

private theorem root_mem_rootLattice {α : D.Weight} (h : α ∈ RootDecomposition.rootSet_value D.cartan)
    (hreg : D.direction α ≠ 0) : α ∈ Q D := by
  rcases lt_or_gt_of_ne hreg with hneg | hpos
  · have ht := _root_.LieAlgebrasAndRepresentations.RealRootSpace.cartan_isMaximalToral
      D.semisimple D.cartan
    have hm : -α ∈ Q D := positiveCone_mem_rootLattice D
      (positiveRoot_mem_cone D.cartan D.direction D.semisimple
        ⟨-α, neg_root_mem D.cartan D.semisimple ht h, by simpa using neg_pos.mpr hneg⟩)
    simpa using (Q D).neg_mem hm
  · exact positiveCone_mem_rootLattice D
      (positiveRoot_mem_cone D.cartan D.direction D.semisimple ⟨α, h, hpos⟩)

private theorem coset_add_rootLattice (μ α : D.Weight) (h : α ∈ Q D) :
    coset D (μ + α) = coset D μ := by
  change (Q D).mkQ (μ + α) = (Q D).mkQ μ
  rw [map_add, show (Q D).mkQ α = 0 from (Submodule.Quotient.mk_eq_zero _).2 h, add_zero]

private abbrev weightSum (X : ModuleCat.{v} (U g)) (ξ : Coset D) :
    Submodule ℂ X :=
  ⨆ μ : D.Weight, ⨆ (_ : coset D μ = ξ), weightSpace D.cartan X μ

private theorem weightSpace_le_weightSum (X : ModuleCat.{v} (U g)) {ξ : Coset D}
    {μ : D.Weight} (hμ : coset D μ = ξ) :
    weightSpace D.cartan X μ ≤ weightSum D X ξ :=
  (le_iSup (fun _ : coset D μ = ξ => weightSpace D.cartan X μ) hμ).trans 
    (le_iSup (fun ν : D.Weight => ⨆ (_ : coset D ν = ξ), weightSpace D.cartan X ν) μ)

private theorem generator_preserves_weightSum (X : ModuleCat.{v} (U g)) (ξ : Coset D)
    (a : g) (x : X) (hx : x ∈ weightSum D X ξ) :
    (ι ℂ a) • x ∈ weightSum D X ξ := by
  let P := weightSum D X ξ
  let act : g →ₗ[ℂ] Module.End ℂ X :=
    (Algebra.lsmul ℂ ℂ X : U g →ₐ[ℂ] Module.End ℂ X).toLinearMap.comp (ι ℂ).toLinearMap
  let A : Submodule ℂ g :=
    { carrier := { a | P ≤ P.comap (act a) }
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb y hy
        change act (a + b) y ∈ P
        rw [map_add, LinearMap.add_apply]
        exact P.add_mem (ha hy) (hb hy)
      smul_mem' := by
        intro c a ha y hy
        change act (c • a) y ∈ P
        rw [map_smul, LinearMap.smul_apply]
        exact P.smul_mem c (ha hy) }
  have htest (z : g) (hz : ∀ μ, coset D μ = ξ →
      ∀ y ∈ weightSpace D.cartan X μ, (ι ℂ z) • y ∈ P) : z ∈ A := by
    show P ≤ P.comap (act z)
    exact iSup_le fun μ => iSup_le fun hμ y hy => hz μ hμ y hy
  have hcartan : D.cartan.toSubmodule ≤ A := by
    intro z hz
    apply htest
    intro μ hμ y hy
    rw [(mem_weightSpace D.cartan X μ y).1 hy ⟨z, hz⟩]
    exact weightSpace_le_weightSum D X hμ ((weightSpace D.cartan X μ).smul_mem _ hy)
  have hroot (α : D.Weight) (hα : D.direction α ≠ 0) :
      RootDecomposition.rootSpace_value D.cartan α ≤ A := by
    by_cases hzero : RootDecomposition.rootSpace_value D.cartan α = ⊥
    · rw [hzero]
      exact bot_le
    have hα₀ : α ≠ 0 := fun e => hα (by simp [e])
    have hQ := root_mem_rootLattice D (show α ∈ RootDecomposition.rootSet_value D.cartan from
      ⟨hα₀, hzero⟩) hα
    intro z hz
    apply htest
    intro μ hμ y hy
    let := restrictedLieRingModule X (g := g)
    let := restrictedLieModule X (g := g)
    exact weightSpace_le_weightSum D X ((coset_add_rootLattice D μ α hQ).trans hμ)
      (_root_.LieAlgebrasAndRepresentations.HighestWeight.root_action X D.cartan α μ z y hz hy)
  obtain ⟨hB, _, hcompl⟩ := cartan_borel D
  obtain ⟨hpos, hneg⟩ := root_parts D
  have hA : A = ⊤ := by
    apply top_unique
    rw [← hcompl.sup_eq_top, hB, hpos, hneg]
    exact sup_le (iSup_le fun α => hroot α.1 α.2.ne)
      (sup_le hcartan (iSup_le fun α => hroot α.1 α.2.ne'))
  have ha : a ∈ A := hA ▸ Submodule.mem_top
  exact ha hx

theorem cosetPart_eq_weight_sum : CosetPartType.{u, v} := by
  intro g _ _ _ D X ξ
  let P := weightSum D X ξ
  have hstable (a : U g) : ∀ x ∈ P, a • x ∈ P := by
    induction a using _root_.Shared.Lie.enveloping_induction ℂ g with
    | scalar c => intro x hx; rw [algebraMap_smul]; exact P.smul_mem c hx
    | generator a => exact generator_preserves_weightSum D X ξ a
    | add a b ha hb => intro x hx; rw [add_smul]; exact P.add_mem (ha x hx) (hb x hx)
    | mul a b ha hb => intro x hx; rw [mul_smul]; exact ha _ (hb _ hx)
  let T : Submodule (U g) X :=
    { carrier := P
      zero_mem' := P.zero_mem
      add_mem' := P.add_mem
      smul_mem' := hstable }
  have hle : cosetPart D X ξ ≤ T := by
    apply Submodule.span_le.mpr
    rintro x ⟨μ, hμ, hx⟩
    exact weightSpace_le_weightSum D X hμ hx
  refine le_antisymm (Submodule.restrictScalars_mono ℂ hle) ?_
  exact iSup_le fun μ => iSup_le fun hμ x hx => Submodule.subset_span ⟨μ, hμ, hx⟩

end RootCosets

open private submodule_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects

theorem component_in_O : ComponentInOType.{u, v} := by
  intro g _ _ _ D k X
  have : IsNoetherian (U g) X.obj :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (categoryO_finiteLength D X)).1
  exact submodule_mem_O D X.obj X.property _ (IsNoetherian.noetherian _)

/-- The endofunctor whose object and morphism maps are the actual component restrictions. -/
def projectorFunctor [FiniteDimensional ℂ g] (D : Setup g) (k : Index D) :
    O.{u, v} D ⥤ O.{u, v} D :=
  componentFunctor D k (component_in_O D k)

theorem projection_on_summands : ProjectionOnSummandsType.{u, v} := by
  intro g _ _ _ D X hX k
  constructor
  · apply LinearMap.ext
    intro x
    exact hX.ofBijective_coeLinearMap_same x
  · intro j hj
    apply LinearMap.ext
    intro x
    exact hX.ofBijective_coeLinearMap_of_ne hj x

section CentralDecomposition

variable (X : ModuleCat.{v} (U g))

private theorem centralParts_independent : iSupIndep (centralPart X) := by
  let act : Center g →ₐ[ℂ] Module.End ℂ X :=
    (Algebra.lsmul ℂ ℂ X : U g →ₐ[ℂ] Module.End ℂ X).comp (Subalgebra.val _)
  have hcomm (a b : Center g) : Commute (act a) (act b) :=
    (Commute.all a b).map act
  have heq (χ : CentralCharacter g) : (centralPart X χ).restrictScalars ℂ =
      ⨅ z : Center g, (act z).maxGenEigenspace (χ z) := by
    ext x
    rw [Submodule.restrictScalars_mem, centerPart_mem, Submodule.mem_iInf]
    apply forall_congr'
    intro z
    have hd : act (difference χ z) = act z - χ z • 1 := by
      rw [difference, map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rw [Module.End.mem_maxGenEigenspace, ← hd]
    simp only [← map_pow]
    rfl
  have hind := (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo act
    (fun a b c => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) c)).comp
      (show Function.Injective (fun χ : CentralCharacter g => (χ : Center g → ℂ)) from
        DFunLike.coe_injective)
  rw [iSupIndep_def]
  intro χ
  rw [← Submodule.disjoint_restrictScalars_iff ℂ]
  simpa only [Submodule.restrictScalars_iSup, heq, Function.comp_apply] using (iSupIndep_def.mp hind χ)

variable [FiniteDimensional ℂ g] (D : Setup g)

private theorem simple_scalar_character (Y : O.{u, v} D) (hs : IsSimpleModule (U g) Y.obj) :
    ∃ χ : CentralCharacter g, ∀ (z : Center g) (y : Y.obj), z.val • y = χ z • y := by
  obtain ⟨μ, ⟨e⟩, _⟩ := (simpleClassification D Y).mp
    ((simple_iff_isSimpleModule D Y).mpr hs)
  obtain ⟨_, _, _, χ, _, _, _, hscalar, _, _⟩ :=
    _root_.LieAlgebrasAndRepresentations.CentralCharacters.central_characters.{u, u}
      D.semisimple D.cartan D.direction D.regular
  refine ⟨χ μ, fun z y => e.injective ?_⟩
  rw [e.map_smul]
  change z.val • e y = e.toLinearMap (χ μ z • y)
  rw [e.toLinearMap.map_smul_of_tower]
  obtain ⟨m, hm⟩ := quotientMap_surjective D μ (e y)
  have hz : (z.val : U g) • m = χ μ z • m :=
    (hscalar μ (character D μ) (character_unique D μ).1 z).1 m
  calc
    z.val • e y = z.val • quotientMap D μ m := congrArg (z.val • ·) hm.symm
    _ = quotientMap D μ (z.val • m) := ((quotientMap D μ).map_smul _ _).symm
    _ = quotientMap D μ (χ μ z • m) := congrArg (quotientMap D μ) hz
    _ = χ μ z • e y := ((quotientMap D μ).map_smul_of_tower _ _).trans
      (congrArg (χ μ z • ·) hm)

open private surjective_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects

private theorem centralParts_span (Y : O.{u, v} D) : ⨆ χ, centralPart Y.obj χ = ⊤ := by
  let X := Y.obj
  have hlen := categoryO_finiteLength D Y
  have : IsNoetherian (U g) X := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).1
  obtain ⟨s, hhead, hlast⟩ := isFiniteLength_iff_exists_compositionSeries.mp hlen
  let A (i : Fin s.length) := (s i.castSucc).comap (s i.succ).subtype
  let F (i : Fin s.length) := ModuleCat.of (U g) (s i.succ ⧸ A i)
  have hf (i : Fin s.length) : objects D (F i) := by
    have ht := submodule_mem_O D X Y.property (s i.succ) (IsNoetherian.noetherian _)
    exact surjective_mem_O D ht (A i).mkQ (Submodule.mkQ_surjective _)
  have hs (i : Fin s.length) : IsSimpleModule (U g) (F i) :=
    (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
  choose χ hχ using (fun i => simple_scalar_character D ⟨F i, hf i⟩ (hs i))
  let chars := Finset.univ.image χ
  let J : Ideal (Center g) := ⨅ ψ ∈ chars, characterIdeal ψ
  have hstep (i : Fin s.length) :
      J • (s i.succ).restrictScalars (Center g) ≤ (s i.castSucc).restrictScalars (Center g) := by
    refine Submodule.smul_le.mpr fun z hz x hx => ?_
    have hi : χ i ∈ chars := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hzχ : χ i z = 0 :=
      ((iInf_le (fun ψ => ⨅ _ : ψ ∈ chars, characterIdeal ψ) (χ i)).trans
        (iInf_le _ hi)) hz
    let y : s i.succ := ⟨x, hx⟩
    change (z.val : U g) • x ∈ s i.castSucc
    have hy : (A i).mkQ ((z.val : U g) • y) = 0 := by
      rw [LinearMap.map_smul]
      exact (hχ i z ((A i).mkQ y)).trans (by rw [hzχ, zero_smul])
    exact (Submodule.Quotient.mk_eq_zero (A i)).mp hy
  have hkill (i : Fin (s.length + 1)) :
      J ^ (i : ℕ) • (s i).restrictScalars (Center g) ≤ ⊥ := by
    induction i using Fin.induction with
    | zero =>
      change J ^ (0 : ℕ) • s.head.restrictScalars (Center g) ≤ ⊥
      rw [hhead]
      simp
    | succ i ih =>
      change J ^ ((i : ℕ) + 1) • (s i.succ).restrictScalars (Center g) ≤ ⊥
      rw [pow_succ, Submodule.mul_smul]
      exact (smul_le_smul_left (J ^ (i : ℕ)) (hstep i)).trans ih
  have hkilltop : J ^ s.length • (⊤ : Submodule (Center g) X) ≤ ⊥ := by
    have h := hkill (Fin.last s.length)
    change J ^ s.length • s.last.restrictScalars (Center g) ≤ ⊥ at h
    simpa only [hlast, Submodule.restrictScalars_top] using h
  have hcp : (chars : Set (CentralCharacter g)).Pairwise (fun a b =>
      IsCoprime (characterIdeal a) (characterIdeal b)) := fun _ _ _ _ hab => characterIdeal_coprime hab
  have hpow : J ^ s.length = ⨅ ψ ∈ chars, characterIdeal ψ ^ s.length := by
    rw [show J = ∏ ψ ∈ chars, characterIdeal ψ from
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime hcp).symm, ← Finset.prod_pow]
    exact Ideal.prod_eq_iInf_of_pairwise_isCoprime (fun a ha b hb hab => (hcp ha hb hab).pow)
  let p (ψ : CentralCharacter g) := characterIdeal ψ ^ s.length
  have hfull : (⨆ ψ ∈ chars, Submodule.torsionBySet (Center g) X (p ψ)) = ⊤ := by
    rw [Submodule.iSup_torsionBySet_ideal_eq_torsionBySet_iInf
      (fun a ha b hb hab => (hcp ha hb hab).pow.sup_eq), ← hpow]
    apply (Module.isTorsionBySet_iff_torsionBySet_eq_top _).mp
    intro x z
    exact (Submodule.mem_bot _).mp <| hkilltop <|
      Submodule.smul_mem_smul z.property (Submodule.mem_top (x := x))
  apply (Submodule.restrictScalars_eq_top_iff (Center g) (U g) X).mp
  rw [Submodule.restrictScalars_iSup]
  apply top_unique
  rw [← hfull]
  refine iSup_le fun ψ => iSup_le fun _ x hx => Submodule.mem_iSup_of_mem ψ ?_
  apply (centerPart_mem X).2
  intro z
  refine ⟨s.length, (Submodule.mem_torsionBySet_iff (p ψ : Set (Center g)) x).1 hx ⟨_, ?_⟩⟩
  exact Ideal.pow_mem_pow (difference_mem ψ z) _

end CentralDecomposition

section JointDecomposition

variable [FiniteDimensional ℂ g] (D : Setup g) (X : ModuleCat.{v} (U g))

private theorem cosetParts_independent : iSupIndep (cosetPart D X) := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  have hind : iSupIndep (weightSpace D.cartan X) :=
    WeightExactness.weightSpaces_independent (H := D.cartan) (X := X)
  rw [iSupIndep_def]
  intro ξ
  rw [← Submodule.disjoint_restrictScalars_iff ℂ]
  have hcoset (η : Coset D) : (cosetPart D X η).restrictScalars ℂ =
      ⨆ μ : D.Weight, ⨆ (_ : coset D μ = η), weightSpace D.cartan X μ :=
    cosetPart_eq_weight_sum D X η
  simp only [Submodule.restrictScalars_iSup, hcoset]
  let s : Set D.Weight := {μ | coset D μ = ξ}
  let t : Set D.Weight := {μ | coset D μ ≠ ξ}
  have hst : Disjoint s t := Set.disjoint_left.mpr fun _ hs ht => ht hs
  refine (hind.disjoint_biSup_biSup hst).mono_right ?_
  refine iSup_le fun η => iSup_le fun hη => iSup_le fun μ => iSup_le fun hμ => ?_
  have ht : μ ∈ t := fun he => hη (hμ.symm.trans he)
  exact (le_iSup (fun _ : μ ∈ t => weightSpace D.cartan X μ) ht).trans
    (le_iSup (fun ν => ⨆ _ : ν ∈ t, weightSpace D.cartan X ν) μ)

private theorem components_independent : iSupIndep (component D X) := by
  let I : Bool → Type u := fun | false => CentralCharacter g | true => Coset D
  let V : (b : Bool) → I b → Submodule (U g) X :=
    fun | false => centralPart X | true => cosetPart D X
  let f (k : Index D) : (b : Bool) → I b :=
    fun | false => k.1 | true => k.2
  have hinj : Function.Injective f := fun a b h =>
    Prod.ext (congrFun h false) (congrFun h true)
  have hV (b : Bool) : iSupIndep (V b) := by
    cases b
    · exact centralParts_independent X
    · exact cosetParts_independent D X
  have heq (k : Index D) : (⨅ b, V b (f k b)) = component D X k := by
    rw [iInf_bool_eq, inf_comm]
    rfl
  have hind : iSupIndep (fun k : Index D => ⨅ b, V b (f k b)) :=
    (iSupIndep.iInf V hV).comp hinj
  exact (funext heq) ▸ hind

open private cartanSubmodule from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects

private theorem components_span (Y : O.{u, v} D) : ⨆ k, component D Y.obj k = ⊤ := by
  let X := Y.obj
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  have hspan (χ : CentralCharacter g) :
      (⨆ μ, (centralPart X χ).restrictScalars ℂ ⊓ weightSpace D.cartan X μ) =
        (centralPart X χ).restrictScalars ℂ :=
    (WeightExactness.stableSubspace (cartanSubmodule D X (centralPart X χ)) Y.property.2.1).2.2
  apply (Submodule.restrictScalars_eq_top_iff ℂ (U g) X).mp
  rw [Submodule.restrictScalars_iSup]
  apply top_unique
  calc
    ⊤ = (⨆ χ, (centralPart X χ).restrictScalars ℂ) := by
      rw [← Submodule.restrictScalars_iSup, centralParts_span D Y, Submodule.restrictScalars_top]
    _ ≤ ⨆ k, (component D X k).restrictScalars ℂ := by
      apply iSup_le
      intro χ
      rw [← hspan χ]
      apply iSup_le
      intro μ
      refine le_trans ?_
        (le_iSup (fun k => (component D X k).restrictScalars ℂ) (χ, coset D μ))
      intro x hx
      exact ⟨hx.1, Submodule.subset_span ⟨μ, rfl, hx.2⟩⟩

theorem component_decomposition : DecompositionType.{u, v} := by
  intro g _ _ _ D X
  have hind := components_independent D X.obj
  have : IsNoetherian (U g) X.obj :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (categoryO_finiteLength D X)).1
  exact ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind (components_span D X),
    Submodule.finite_ne_bot_of_iSupIndep hind⟩

end JointDecomposition

section Projection

variable [FiniteDimensional ℂ g] (D : Setup g)
variable {X : ModuleCat.{v} (U g)} (hX : DirectSum.IsInternal (component D X))

private theorem projection_apply_same {k : Index D} (x : component D X k) :
    projection D hX k (x : X) = x :=
  hX.ofBijective_coeLinearMap_same x

private theorem projection_apply_other {j k : Index D} (h : j ≠ k) (x : component D X j) :
    projection D hX k (x : X) = 0 :=
  hX.ofBijective_coeLinearMap_of_ne h x

end Projection

theorem projection_naturality : ProjectionNaturalityType.{u, v} := by
  intro g _ _ _ D X Y hX hY f k
  have hsurj : Function.Surjective (DirectSum.coeLinearMap (component D X.obj)) := hX.2
  apply (LinearMap.cancel_right hsurj).mp
  apply DirectSum.linearMap_ext
  intro j
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
  let y : component D Y.obj j := componentMap f.hom.hom j x
  change projection D hY k (y : Y.obj) = componentMap f.hom.hom k (projection D hX k x)
  by_cases hj : j = k
  · subst j
    rw [projection_apply_same, projection_apply_same]
  · rw [projection_apply_other D hY hj, projection_apply_other D hX hj, map_zero]

theorem cross_component_vanishing : CrossComponentVanishingType.{u, v} := by
  intro g _ _ _ D X Y k j hkj f
  let hX := (component_decomposition D X).1
  let F : X.obj →ₗ[U g] Y.obj :=
    (component D Y.obj j).subtype.comp (f.comp (projection D hX k))
  apply LinearMap.ext
  intro x
  have hx := component_map_mem F k x.property
  have hfx : (f x : Y.obj) ∈ component D Y.obj k := by
    change F (x : X.obj) ∈ component D Y.obj k at hx
    simpa only [F, LinearMap.comp_apply, Submodule.subtype_apply, projection_apply_same] using hx
  have hd := (components_independent D Y.obj).pairwiseDisjoint hkj
  exact Subtype.ext (Submodule.disjoint_def.mp hd _ hfx (f x).property)

theorem projector_exact : ProjectorExactType.{u, v} := by
  intro g _ _ _ D k X Y Z f q hf hExact hq
  have hX := (component_decomposition D X).1
  have hY := (component_decomposition D Y).1
  have hZ := (component_decomposition D Z).1
  refine ⟨fun x y h => Subtype.ext (hf (congrArg Subtype.val h)), ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hy' : q.hom.hom (y : Y.obj) = 0 := congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := (hExact (y : Y.obj)).mp hy'
      refine ⟨projection D hX k x, ?_⟩
      have hn := DFunLike.congr_fun (projection_naturality D hX hY f k) x
      change projection D hY k (f.hom.hom x) =
        componentMap f.hom.hom k (projection D hX k x) at hn
      rw [← hn, hx, projection_apply_same]
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (hExact.apply_apply_eq_zero (x : X.obj))
  · intro z
    obtain ⟨y, hy⟩ := hq (z : Z.obj)
    refine ⟨projection D hY k y, ?_⟩
    have hn := DFunLike.congr_fun (projection_naturality D hY hZ q k) y
    change projection D hZ k (q.hom.hom y) =
      componentMap q.hom.hom k (projection D hY k y) at hn
    rw [← hn, hy, projection_apply_same]

section CategoricalExactness

open CategoryTheory.Limits

variable [FiniteDimensional ℂ g] (D : Setup g) (k : Index D)

instance projectorFunctor_additive : (projectorFunctor.{u, v} D k).Additive where
  map_add := by
    intro X Y f h
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The projector sends short exact complexes in category O to short exact complexes. -/
theorem projector_shortExact (S : ShortComplex (O.{u, v} D)) (hS : S.ShortExact) :
    (S.map (projectorFunctor D k)).ShortExact := by
  let I : O.{u, v} D ⥤ ModuleCat.{v} (U g) := (objects D).ι
  have hker {X Y : O.{u, v} D} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) I :=
    (objects D).preservesKernels_ι f
  have hcoker {X Y : O.{u, v} D} (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) I :=
    (objects D).preservesCokernels_ι f
  have : I.PreservesHomology := by
    constructor
    · intro X Y f; exact hker f
    · intro X Y f; exact hcoker f
  have : I.PreservesMonomorphisms :=
    NormalEpiCategory.preservesMonomorphisms_of_preservesKernels I
  have : I.PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels I
  have := hS.mono_f
  have := hS.epi_g
  have hM := hS.map I
  obtain ⟨hf, he, hg⟩ := projector_exact D k S.f S.g hM.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map I)).1 hM.exact)
    hM.moduleCat_surjective_g
  let T := S.map (projectorFunctor D k)
  have hTe : (T.map I).Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (T.map I)).2 he
  exact ShortComplex.ShortExact.mk' ((T.exact_map_iff_of_faithful I).1 hTe)
    (I.mono_of_mono_map ((ModuleCat.mono_iff_injective (I.map T.f)).2 hf))
    (I.epi_of_epi_map ((ModuleCat.epi_iff_surjective (I.map T.g)).2 hg))

instance projectorFunctor_preservesHomology :
    (projectorFunctor.{u, v} D k).PreservesHomology :=
  ((projectorFunctor.{u, v} D k).exact_tfae.out 1 3).mp (projector_shortExact D k)

end CategoricalExactness

end RepTheorySurvey.CategoryO.ComponentProjectors
