import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Orthogonality
import Mathlib.Topology.Instances.Rat
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.RootData.BorelsAndChambers

open _root_.LinearAlgebraicGroups.Specs
open Specs.BorelsAndChambers
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors pairing characterValue)
open Specs.GeometricBorelConjugacy (IsBorel ConjugatesSubgroups subgroupOfSubgroup)
open Specs.GeometricRadicals (IsMaximalTorus IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints dualMap constants scale)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition lieImage)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

private theorem preservesSignsOnFiniteSet
    {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {A : Type*} [Finite A] (root : A → X) (f : X →ₗ[ℤ] ℝ)
    (hf : ∀ a, f (root a) ≠ 0) :
    ∃ g : X →ₗ[ℤ] ℤ, (∀ a, g (root a) ≠ 0) ∧
      ∀ a, (0 < g (root a) ↔ 0 < f (root a)) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let I := Module.Free.ChooseBasisIndex ℤ X
  let qeval (a : A) (r : I → ℝ) : ℝ :=
    ∑ i, (b.equivFun (root a) i : ℝ) * r i
  have hq (a : A) : qeval a (fun i => f (b i)) = f (root a) := by
    have h := congrArg f (b.sum_equivFun (root a))
    simpa only [map_sum, map_smul, zsmul_eq_mul] using h
  let C : A → Set (I → ℝ) := fun a =>
    if 0 < f (root a) then {r | 0 < qeval a r} else {r | qeval a r < 0}
  have hC (a : A) : IsOpen (C a) := by
    have hc : Continuous (qeval a) := continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_apply i)
    unfold C
    split
    · exact isOpen_lt continuous_const hc
    · exact isOpen_lt hc continuous_const
  have hmem : (fun i => f (b i)) ∈ ⋂ a, C a := by
    apply Set.mem_iInter.mpr
    intro a
    by_cases h : 0 < f (root a)
    · simp only [C, ite_eq_left h]
      change 0 < qeval a (fun i => f (b i))
      rwa [hq]
    · simp only [C, ite_eq_right h]
      change qeval a (fun i => f (b i)) < 0
      rw [hq]
      exact lt_of_le_of_ne (le_of_not_gt h) (hf a)
  have hdense : DenseRange (fun r : I → ℚ => fun i => (r i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨q, hqC⟩ :=
    hdense.exists_mem_open (isOpen_iInter_of_finite hC) ⟨_, hmem⟩
  let N : ℕ := ∏ i : I, (q i).den
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
  let z (i : I) : ℤ := (q i).num * (∏ j ∈ Finset.univ.erase i, (q j).den : ℕ)
  have hz (i : I) : (z i : ℝ) = N * (q i : ℝ) := by
    have h := Finset.prod_erase_mul Finset.univ (fun j => (q j).den) (Finset.mem_univ i)
    have hn : ((q i).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q i).den_nz
    unfold z N
    rw [← h, Rat.cast_def, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    field_simp
  let g : X →ₗ[ℤ] ℤ := b.constr ℤ z
  have hg (a : A) : (g (root a) : ℝ) = N * qeval a (fun i => (q i : ℝ)) := by
    change ((b.constr ℤ z (root a) : ℤ) : ℝ) = _
    rw [b.constr_apply_fintype ℤ z (root a), Int.cast_sum]
    simp only [zsmul_eq_mul, Int.cast_id, Int.cast_mul, hz, qeval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsign (a : A) : (0 < f (root a) ∧ 0 < g (root a)) ∨
      (f (root a) < 0 ∧ g (root a) < 0) := by
    have h := Set.mem_iInter.mp hqC a
    by_cases hpos : 0 < f (root a)
    · refine Or.inl ⟨hpos, ?_⟩
      simp only [C, ite_eq_left hpos, Set.mem_ofPred_eq] at h
      exact_mod_cast (hg a).symm ▸ mul_pos hN h
    · refine Or.inr ⟨lt_of_le_of_ne (le_of_not_gt hpos) (hf a), ?_⟩
      simp only [C, ite_eq_right hpos, Set.mem_ofPred_eq] at h
      exact_mod_cast (hg a).symm ▸ mul_neg_of_pos_of_neg hN h
  refine ⟨g, fun a => ?_, fun a => ?_⟩
  · rcases hsign a with h | h
    · exact ne_of_gt h.2
    · exact ne_of_lt h.2
  · rcases hsign a with h | h
    · exact iff_of_true h.2 h.1
    · exact iff_of_false (not_lt_of_gt h.2) (not_lt_of_gt h.1)

/-- A real chamber of the split torus is realized by an integral cocharacter. -/
theorem positiveSystemsFromCocharacters : PositiveSystemsFromCocharacters.{u} := by
  classical
  intro k _ G _ T hT _ S
  obtain ⟨hComm, hFree, hFinite, _, _, P, hP, hpair⟩ :=
    CharacterPairing.perfectCharacterPairing T.group hT
  letI := hComm
  letI := hFree
  letI := hFinite
  letI := hP
  haveI : Finite ↥(absoluteRoots T) :=
    CharacterPairing.finiteAbsoluteRoots G T hT
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hsign⟩ := preservesSignsOnFiniteSet
      (fun α : ↥(absoluteRoots T) => Additive.ofMul α.val) f hf
    let cochar : Cocharacter T.group := (P.flip.toPerfPair.symm g).toMul
    have hc (α : Character T.group) : pairing T.group α cochar = g (Additive.ofMul α) := by
      rw [← hpair]
      exact P.apply_toPerfPair_flip g _
    exact ⟨cochar, fun α => (hc α.val).symm ▸ hg α, Set.ext fun α => by
      change 0 < pairing T.group α.val cochar ↔ 0 < f (Additive.ofMul α.val)
      rw [hc]
      exact hsign α⟩
  · rintro ⟨cochar, hcochar, rfl⟩
    let f : Additive (Character T.group) →ₗ[ℤ] ℝ :=
      (Int.castAddHom ℝ).toIntLinearMap.comp (P.flip (Additive.ofMul cochar))
    have hf (α : Character T.group) : f (Additive.ofMul α) = (pairing T.group α cochar : ℝ) :=
      congrArg (fun n : ℤ => (n : ℝ)) (hpair α cochar)
    refine ⟨f, fun α => ?_, Set.ext fun α => ?_⟩
    · rw [hf]
      exact_mod_cast hcochar α
    · change 0 < pairing T.group α.val cochar ↔ 0 < f (Additive.ofMul α.val)
      rw [hf]
      exact_mod_cast Iff.rfl


variable {k : Type u} [Field k] {G H : GroupScheme k}

private theorem differential_comp {A B C : GroupScheme k} (f : A ⟶ B) (g : B ⟶ C)
    (v : Lie k A) : mapPointKernel (f ≫ g) v = mapPointKernel g (mapPointKernel f v) :=
  (lieFunctoriality k).2.2 A B C f g v

private theorem lieImage_mono {A B : ClosedSubgroup G} (h : IsSubgroupOf A B) :
    lieImage A ⊆ lieImage B := by
  obtain ⟨f, hf⟩ := h
  rintro _ ⟨v, rfl⟩
  exact ⟨mapPointKernel f v, by rw [← differential_comp, hf]⟩

private theorem lieImage_eq_of_same {A B : ClosedSubgroup G} (h : SameSubgroup A B) :
    lieImage A = lieImage B :=
  Set.Subset.antisymm (lieImage_mono h.1) (lieImage_mono h.2)

private theorem differential_injective (f : G ⟶ H) [Mono f.hom.hom] :
    Function.Injective (mapPointKernel f) := by
  intro v w h
  apply Subtype.ext
  apply (cancel_mono f.hom.hom).mp
  exact congrArg (fun v : Lie k H => v.toMul.val) h

private theorem hom_commutes_with_weight_formula
    (f : G ⟶ H) {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    (a : T.group ⟶ S.group) (ha : T.inclusion ≫ f = a ≫ S.inclusion)
    {χ : Character S.group} {v : Lie k G} (R : TestAlgebra k) (t : GroupPoints T.group R) :
    let u : GroupPoints S.group R := t ≫ a.hom.hom
    let p := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
    let h := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
    let p' := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R)))
      (mapPointKernel f v).toMul.val
    let h' := mapPoints (constants R) (u ≫ S.inclusion.hom.hom)
    (h * p * h⁻¹) ≫ f.hom.hom = h' * p' * h'⁻¹ ∧
      (mapPoints (scale R (characterValue (a ≫ χ) R t)) p) ≫ f.hom.hom =
        mapPoints (scale R (characterValue χ R u)) p' := by
  dsimp only
  have heval : characterValue (a ≫ χ) R t = characterValue χ R (t ≫ a.hom.hom) := by
    unfold characterValue
    dsimp only
    have hcomp : t ≫ (a ≫ χ).hom.hom = (t ≫ a.hom.hom) ≫ χ.hom.hom :=
      (Category.assoc t a.hom.hom χ.hom.hom).symm
    rw [hcomp]
  have he : T.inclusion.hom.hom ≫ f.hom.hom = a.hom.hom ≫ S.inclusion.hom.hom :=
    congrArg (fun b : T.group ⟶ H => b.hom.hom) ha
  constructor
  · rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    have hconst : mapPoints (constants R) (t ≫ T.inclusion.hom.hom) ≫ f.hom.hom =
        mapPoints (constants R) ((t ≫ a.hom.hom) ≫ S.inclusion.hom.hom) := by
      change ((testSpec k).map (constants R).op ≫ (t ≫ T.inclusion.hom.hom)) ≫ f.hom.hom = _
      rw [Category.assoc, Category.assoc, he]
      change _ = (testSpec k).map (constants R).op ≫ (t ≫ a.hom.hom) ≫ S.inclusion.hom.hom
      rw [Category.assoc t]
    rw [hconst]
    rfl
  · rw [heval]
    simp only [mapPoints, Category.assoc]
    rfl

private theorem map_weightVector (f : G ⟶ H) {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    (a : T.group ≅ S.group) (ha : T.inclusion ≫ f = a.hom ≫ S.inclusion) {χ : Character S.group}
    {v : Lie k G} (hv : v ∈ adjointWeightVectors T (a.hom ≫ χ)) :
    mapPointKernel f v ∈ adjointWeightVectors S χ := by
  intro R t
  let t₀ : GroupPoints T.group R := t ≫ a.inv.hom.hom
  obtain ⟨h₁, h₂⟩ := hom_commutes_with_weight_formula f a.hom ha (χ := χ) (v := v) R t₀
  have ht : t₀ ≫ a.hom.hom.hom = t := by
    have hi : a.inv.hom.hom ≫ a.hom.hom.hom = 𝟙 _ :=
      (Grp.forget (SchemeOver k)).congr_map a.inv_hom_id
    change (t ≫ a.inv.hom.hom) ≫ a.hom.hom.hom = t
    rw [Category.assoc, hi, Category.comp_id]
  dsimp only at h₁ h₂
  rw [ht] at h₁ h₂
  exact h₁.symm.trans ((congrArg (fun p => p ≫ f.hom.hom) (hv R t₀)).trans h₂)

private theorem weightVector_of_map (f : G ⟶ H) [Mono f.hom.hom]
    {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    (a : T.group ⟶ S.group) (ha : T.inclusion ≫ f = a ≫ S.inclusion) {χ : Character S.group}
    {v : Lie k G} (hv : mapPointKernel f v ∈ adjointWeightVectors S χ) :
    v ∈ adjointWeightVectors T (a ≫ χ) := by
  intro R t
  obtain ⟨h₁, h₂⟩ := hom_commutes_with_weight_formula f a ha (χ := χ) (v := v) R t
  apply (cancel_mono f.hom.hom).mp
  rw [h₁, h₂]
  exact hv R (t ≫ a.hom.hom)

private theorem isIso_of_closedImmersion_of_dimension
    {X Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y] (f : X ⟶ Y)
    [IsClosedImmersion f] {n : ℕ} (hX : topologicalKrullDim X = n)
    (hY : topologicalKrullDim Y = n) : IsIso f := by
  have ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
  letI := hAff
  have dim (Z : Scheme.{u}) [IsAffine Z] :
      topologicalKrullDim Z = ringKrullDim Γ(Z, ⊤) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.isoSpec Z).hom.homeomorph.isHomeomorph]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  apply IsClosedImmersion.isIso_of_injective_of_isAffine (f := f)
  haveI : IsDomain Γ(Y, ⊤) := inferInstance
  by_contra hn
  have hn' : ¬ ∀ r, f.appTop.hom r = 0 → r = 0 :=
    (injective_iff_map_eq_zero f.appTop.hom).not.mp hn
  obtain ⟨r, hr⟩ := not_forall.mp hn'
  obtain ⟨hr, hr₀⟩ := not_imp.mp hr
  have h := ringKrullDim_succ_le_of_surjective f.appTop.hom hsurj
    (mem_nonZeroDivisors_iff_ne_zero.mpr hr₀) hr
  rw [← dim X, ← dim Y, hX, hY] at h
  exact (not_le_of_gt (show (n : WithBot ℕ∞) < (n : WithBot ℕ∞) + 1 by exact_mod_cast Nat.lt_succ_self n)) h

private theorem differential_surjective (f : G ≅ H) :
    Function.Surjective (mapPointKernel f.hom) := by
  intro v
  refine ⟨mapPointKernel f.inv v, ?_⟩
  rw [← differential_comp, f.inv_hom_id]
  exact (lieFunctoriality k).2.1 H v

private theorem mapWeightVectors_iff (F : G ≅ H)
    {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    (c : T.group ≅ S.group) (hc : T.inclusion ≫ F.hom = c.hom ≫ S.inclusion)
    (χ : Character S.group) (v : Lie k G) :
    mapPointKernel F.hom v ∈ adjointWeightVectors S χ ↔
      v ∈ adjointWeightVectors T (c.hom ≫ χ) := by
  letI : IsIso F.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso F.hom
  exact ⟨weightVector_of_map F.hom c.hom hc, map_weightVector F.hom c hc⟩

private theorem rootsOfIso (F : G ≅ H)
    {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    (c : T.group ≅ S.group) (hc : T.inclusion ≫ F.hom = c.hom ≫ S.inclusion)
    (χ : Character S.group) :
    (c.hom ≫ χ) ∈ absoluteRoots T ↔ χ ∈ absoluteRoots S := by
  letI : IsIso F.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso F.hom
  have c_one : c.hom ≫ (1 : Character S.group) = 1 := by
    apply Grp.hom_ext
    exact MonObj.comp_one _
  have c_inj : Function.Injective (fun χ : Character S.group => c.hom ≫ χ) :=
    fun _ _ h => (cancel_epi c.hom).mp h
  constructor
  · rintro ⟨hne, v, hv, hv0⟩
    refine ⟨fun h => hne (h ▸ c_one), mapPointKernel F.hom v,
      (mapWeightVectors_iff F c hc χ v).mpr hv, ?_⟩
    intro h
    apply hv0
    apply differential_injective F.hom
    simpa only [map_zero] using h
  · rintro ⟨hne, w, hv, hv0⟩
    obtain ⟨v, rfl⟩ := differential_surjective F w
    refine ⟨fun h => hne (c_inj (h.trans c_one.symm)), v,
      (mapWeightVectors_iff F c hc χ v).mp hv, ?_⟩
    intro h
    exact hv0 (by simp only [h, map_zero])

private theorem lieImageOfIso_iff (F : G ≅ H) {B : ClosedSubgroup G} {C : ClosedSubgroup H}
    (e : B.group ≅ C.group) (he : B.inclusion ≫ F.hom = e.hom ≫ C.inclusion)
    (v : Lie k G) : mapPointKernel F.hom v ∈ lieImage C ↔ v ∈ lieImage B := by
  letI : IsIso F.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso F.hom
  have h (w : Lie k B.group) :
      mapPointKernel C.inclusion (mapPointKernel e.hom w) =
        mapPointKernel F.hom (mapPointKernel B.inclusion w) := by
    rw [← differential_comp, ← differential_comp, he]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := differential_surjective e z
    exact ⟨w, differential_injective F.hom ((h w).symm.trans hz)⟩
  · rintro ⟨w, rfl⟩
    exact ⟨mapPointKernel e.hom w, h w⟩

private theorem weightSpace_le_lieImage_iff (F : G ≅ H)
    {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    (c : T.group ≅ S.group) (hc : T.inclusion ≫ F.hom = c.hom ≫ S.inclusion)
    {B : ClosedSubgroup G} {C : ClosedSubgroup H}
    (e : B.group ≅ C.group) (he : B.inclusion ≫ F.hom = e.hom ≫ C.inclusion)
    (χ : Character S.group) :
    (adjointWeightVectors T (c.hom ≫ χ) ⊆ lieImage B) ↔
      adjointWeightVectors S χ ⊆ lieImage C := by
  constructor
  · intro h w hw
    obtain ⟨v, rfl⟩ := differential_surjective F w
    exact (lieImageOfIso_iff F e he v).mpr (h ((mapWeightVectors_iff F c hc χ v).mp hw))
  · intro h v hv
    exact (lieImageOfIso_iff F e he v).mp (h ((mapWeightVectors_iff F c hc χ v).mpr hv))

private theorem subgroupRootsOfIso (F : G ≅ H)
    {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    (c : T.group ≅ S.group) (hc : T.inclusion ≫ F.hom = c.hom ≫ S.inclusion)
    {B : ClosedSubgroup G} {C : ClosedSubgroup H}
    (e : B.group ≅ C.group) (he : B.inclusion ≫ F.hom = e.hom ≫ C.inclusion) :
    (fun α : ↥(absoluteRoots T) ↦ c.inv ≫ α.val) '' subgroupRoots T B =
      Subtype.val '' subgroupRoots S C := by
  ext χ
  constructor
  · rintro ⟨α, hα, rfl⟩
    have hcomp : c.hom ≫ c.inv ≫ α.val = α.val := c.hom_inv_id_assoc _
    have hroot := (rootsOfIso F c hc (c.inv ≫ α.val)).mp (hcomp.symm ▸ α.property)
    exact ⟨⟨_, hroot⟩, (weightSpace_le_lieImage_iff F c hc e he _).mp (hcomp.symm ▸ hα), rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    have hroot := (rootsOfIso F c hc β.val).mpr β.property
    exact ⟨⟨_, hroot⟩, (weightSpace_le_lieImage_iff F c hc e he _).mpr hβ,
      c.inv_hom_id_assoc _⟩

private theorem coordinate_space_eq_iSup
    {F V I X : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype I]
    (b : Module.Basis I F V) (n : I → ℤ) (m : X → ℤ)
    (W : X → Submodule F V) (hW : ⨆ a, W a = ⊤)
    (hcoords : ∀ a v, v ∈ W a → ∀ j, n j ≠ m a → b.equivFun v j = 0)
    (P : ℤ → Prop) :
    ((⨆ a : {a : X // P (m a)}, W a.val : Submodule F V) : Set V) =
      {v | ∀ j, ¬ P (n j) → b.equivFun v j = 0} := by
  classical
  let M : Submodule F V := ⨆ a : {a : X // P (m a)}, W a.val
  let mproj : (I → F) →ₗ[F] I → F :=
    LinearMap.pi fun j => if P (n j) then LinearMap.proj j else 0
  let proj : V →ₗ[F] V := b.equivFun.symm.toLinearMap.comp (mproj.comp b.equivFun.toLinearMap)
  have hp (v : V) (j : I) : b.equivFun (proj v) j =
      if P (n j) then b.equivFun v j else 0 := by
    change b.equivFun (b.equivFun.symm (mproj (b.equivFun v))) j = _
    rw [b.equivFun.apply_symm_apply]
    by_cases h : P (n j)
    · simp [mproj, h]
    · simp [mproj, h]
  have hmem (v : V) : proj v ∈ M := by
    have hle : (⨆ a, W a) ≤ M.comap proj := by
      apply iSup_le
      intro a u hu
      change proj u ∈ M
      by_cases ha : P (m a)
      · have hu' : proj u = u := by
          apply b.equivFun.injective
          funext j
          rw [hp]
          by_cases hj : P (n j)
          · rw [ite_eq_left hj]
          · rw [ite_eq_right hj, hcoords a u hu j (fun h => hj (h.symm ▸ ha))]
        rw [hu']
        exact (le_iSup (fun a : {a : X // P (m a)} => W a.val) ⟨a, ha⟩) hu
      · have hu' : proj u = 0 := by
          apply b.equivFun.injective
          funext j
          rw [hp, map_zero]
          change (if P (n j) then b.equivFun u j else 0) = 0
          by_cases hj : P (n j)
          · rw [ite_eq_left hj, hcoords a u hu j (fun h => ha (h ▸ hj))]
          · rw [ite_eq_right hj]
        exact hu' ▸ M.zero_mem
    rw [hW] at hle
    exact hle Submodule.mem_top
  ext v
  constructor
  · intro hv j hj
    have hk : M ≤ (LinearMap.proj j ∘ₗ b.equivFun.toLinearMap).ker := by
      apply iSup_le
      intro a w hw
      exact hcoords a.val w hw j (fun h => hj (h.symm ▸ a.property))
    exact hk hv
  · intro hv
    have he : proj v = v := by
      apply b.equivFun.injective
      ext j
      rw [hp]
      by_cases h : P (n j)
      · rw [ite_eq_left h]
      · rw [ite_eq_right h, hv j h]
    exact he ▸ hmem v

open Specs.GeometricRadicals (GeometricGroup IsTorus)
open Specs.GeometricBorelConjugacy (IsKBorel IsSmoothConnectedSolvable)
open Specs.RootGroups (IsRootSubgroup)
open CocharacterDynamics (centralizerLieInvariants contractingSubgroupUnipotent
  existsLimitDecomposition geometricallyConnectedLimitSubgroups lieWeights limitSubgroupsSmooth)
open private mono_over centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private factor_closed isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private subgroupOf_trans factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private restrictSubgroup compose_restrict local_maximal_of_ambient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private irreducible_of_geometricallyConnected geometricallyConnected_of_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private group_dimension_eq_lie_finrank smooth_coordinate_hopf eigenvector_coordinates
  restrictedCocharacterEigenvector positive_root_space_comparison
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private zeroWeightVectors_iff_centralizes from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private conjugationAction isFixedBy_conjugation_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private centralizes_iff_in_ambient map_limit_contracting parabolic_of_cast extendSubgroup
  extend_subgroupOf subgroupOf_of_extend subgroupIso_of_same same_subgroup_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

private theorem connected_of_geometricallyConnected {X : SchemeOver k}
    (h : GeometricallyConnected X.hom) : ConnectedSpace X.left :=
  self_of_isIntegral_of_geometrically h.geometrically_connectedSpace

private theorem smoothConnectedGroup_integral (A : AffineAlgebraicGroup k)
    (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left) : IsIntegral A.val.X.left := by
  letI := hc
  letI := A.property.2.1
  letI := A.property.2.2
  letI := geometricallyConnected_of_connected A
  letI : IrreducibleSpace A.val.X.left := irreducible_of_geometricallyConnected A.val
  letI : IsReduced A.val.X.left := isReduced_of_smooth_over_field A.val.X.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced _

private theorem smoothGroup_dimension (A : AffineAlgebraicGroup k)
    (hs : Smooth A.val.X.hom) (hi : IsIntegral A.val.X.left) (s : IdentityLieStructure A.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    topologicalKrullDim A.val.X.left = (Module.finrank k (Lie k A.val) : WithBot ℕ∞) := by
  let C : AffineGroupCategory k := ⟨A.val, A.property.1⟩
  let D := coordinateHopf C
  let e : hopfSpectrum D ≅ A.val := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso C)
  let e' := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
  letI : IsIntegral ((Grp.forget (SchemeOver k) ⋙ Over.forget _).obj A.val) := hi
  letI : IsDomain D := (affine_isIntegral_iff (.of D)).mp (IsIntegral.of_isIso e'.inv)
  letI : Algebra.Smooth k D := smooth_coordinate_hopf e hs
  exact group_dimension_eq_lie_finrank e s

private theorem isIso_of_closedImmersion_of_differential
    {A B : AffineAlgebraicGroup k} (f : A.val ⟶ B.val)
    (hf : IsClosedImmersion f.hom.hom.left)
    (hAs : Smooth A.val.X.hom) (hAc : ConnectedSpace A.val.X.left)
    (hBs : Smooth B.val.X.hom) (hBc : ConnectedSpace B.val.X.left)
    (h : Function.Surjective (mapPointKernel f)) : IsIso f := by
  letI := hf
  letI := A.property.1
  letI := B.property.1
  letI := mono_over f.hom.hom hf
  let sA := identityLieStructure A
  let sB := identityLieStructure B
  letI := sA.lieRing
  letI := sA.lieAlgebra
  letI := sB.lieRing
  letI := sB.lieAlgebra
  letI : AddCommGroup (Lie k A.val) := sA.lieRing.toAddCommGroup
  letI : AddCommGroup (Lie k B.val) := sB.lieRing.toAddCommGroup
  letI : Module k (Lie k A.val) := sA.lieAlgebra.toModule
  letI : Module k (Lie k B.val) := sB.lieAlgebra.toModule
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k A.val B.val f sA sB
  let e := LinearEquiv.ofBijective d.toLinearMap
    ⟨fun x y hxy => differential_injective f ((hd x).symm.trans (hxy.trans (hd y))),
      fun y => by obtain ⟨x, hx⟩ := h y; exact ⟨x, (hd x).trans hx⟩⟩
  let hAi := smoothConnectedGroup_integral A hAs hAc
  letI : IsIntegral B.val.X.left := smoothConnectedGroup_integral B hBs hBc
  have hdimA := smoothGroup_dimension A hAs hAi sA
  have hdimB := smoothGroup_dimension B hBs ‹IsIntegral B.val.X.left› sB
  rw [e.finrank_eq] at hdimA
  haveI : IsIso f.hom.hom.left :=
    isIso_of_closedImmersion_of_dimension f.hom.hom.left hdimA hdimB
  exact isIso_of_schemeIso f

private theorem subgroupOf_of_lieImage
    {A : AffineAlgebraicGroup k} {B C : ClosedSubgroup A.val}
    (hBC : IsSubgroupOf B C)
    (hBs : Smooth B.group.X.hom) (hBc : ConnectedSpace B.group.X.left)
    (hCs : Smooth C.group.X.hom) (hCc : ConnectedSpace C.group.X.left)
    (hLie : lieImage C ⊆ lieImage B) : IsSubgroupOf C B := by
  obtain ⟨f, hf⟩ := hBC
  letI := mono_over C.inclusion.hom.hom C.isClosedImmersion
  have hsurj : Function.Surjective (mapPointKernel f) := by
    intro v
    obtain ⟨w, hw⟩ := hLie (show mapPointKernel C.inclusion v ∈ lieImage C from ⟨v, rfl⟩)
    refine ⟨w, differential_injective C.inclusion ?_⟩
    rw [← differential_comp, hf, hw]
  letI : IsIso f := isIso_of_closedImmersion_of_differential
    (A := closedSubgroupAlgebraicGroup B) (B := closedSubgroupAlgebraicGroup C) f
    (factor_closed hf) hBs hBc hCs hCc hsurj
  exact ⟨inv f, by rw [← hf, IsIso.inv_hom_id_assoc]⟩

private theorem map_contracting_of_comp (hAff : IsAffine G.X.left) (f : G ⟶ H)
    {c : Cocharacter G} {d : Cocharacter H} (h : c ≫ f = d)
    (D : LimitDecomposition c) (E : LimitDecomposition d) :
    ∃ j : D.contracting.group ⟶ E.contracting.group,
      j ≫ E.contracting.inclusion = D.contracting.inclusion ≫ f := by
  subst d
  exact map_limit_contracting hAff f D E

private theorem rootSubgroup_containedOfWeight
    (A : AffineAlgebraicGroup k) {T B : ClosedSubgroup A.val}
    (hB : Smooth B.group.X.hom) (hBc : ConnectedSpace B.group.X.left)
    (hT : IsSplitTorus T.group) (hTB : IsSubgroupOf T B)
    (α : ↥(absoluteRoots T)) (C : Specs.RankOneFlag.Centralizer T α.val)
    (cochar : Cocharacter T.group) (hpos : 0 < pairing T.group α.val cochar)
    (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (hDs : Smooth D.contracting.group.X.hom) (hDa : Specs.RankOneFlag.IsSplitAdditive D.contracting.group)
    (hC : IsReductive (closedSubgroupAlgebraicGroup C.subgroup))
    (hweight : adjointWeightVectors T α.val ⊆ lieImage B) :
    IsSubgroupOf (subgroupOfSubgroup C.subgroup D.contracting) B := by
  obtain ⟨tB, htB⟩ := hTB
  let Balg := closedSubgroupAlgebraicGroup B
  let H := closedSubgroupAlgebraicGroup C.subgroup
  let T_B := restrictSubgroup T B tB htB
  let S_B := subgroupOfSubgroup T_B C.kernelTorus
  let S := subgroupOfSubgroup T C.kernelTorus
  have hS : S_B.inclusion ≫ B.inclusion = S.inclusion := by
    change (C.kernelTorus.inclusion ≫ tB) ≫ B.inclusion = C.kernelTorus.inclusion ≫ T.inclusion
    rw [Category.assoc, htB]
  letI : Smooth Balg.val.X.hom := hB
  letI : ConnectedSpace Balg.val.X.left := hBc
  obtain ⟨CB, hCB, hCBs, hCBc, hCBL⟩ := CocharacterDynamics.torusCentralizer Balg S_B
    (show CocharacterDynamics.IsTorusSubgroup S_B from by
      obtain ⟨F, _, _, hf, r, e⟩ := C.kernelTorus_largest.1
      exact ⟨F, inferInstance, inferInstance, hf, r, e⟩)
  have hCBC : IsSubgroupOf (subgroupOfSubgroup B CB) C.subgroup := by
    have hcen : Centralizes S_B.inclusion CB.inclusion.hom.hom :=
      (hCB _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
    have hcen' := (centralizes_iff_in_ambient B S_B.inclusion CB.inclusion.hom.hom).mpr hcen
    rw [hS] at hcen'
    obtain ⟨j, hj⟩ := (C.centralizes _ _).mp hcen'
    exact factor_group_through_subgroup C.subgroup (CB.inclusion ≫ B.inclusion) j hj
  obtain ⟨f, hf⟩ := hCBC
  obtain ⟨hComm, _⟩ := CharacterPairing.perfectCharacterPairing T.group hT
  have htcentral : Centralizes S_B.inclusion T_B.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X t s
    change Commute (t ≫ tB.hom.hom) (s ≫ C.kernelTorus.inclusion.hom.hom ≫ tB.hom.hom)
    letI : IsMulCommutative (X ⟶ T_B.group.X) :=
      (isCommMonObj_iff_isMulCommutative T.group.X).mp hComm X
    have h : Commute t (s ≫ C.kernelTorus.inclusion.hom.hom) := mul_comm' _ _
    exact h.map (IsMonHom.monoidHom tB.hom.hom X)
  obtain ⟨a₀, ha₀⟩ := (hCB _ _).mp htcentral
  obtain ⟨a, ha⟩ := factor_group_through_subgroup CB tB a₀ ha₀
  have haC : a ≫ f = C.torusIso.hom ≫ C.torus.inclusion := by
    letI := mono_over C.subgroup.inclusion.hom.hom C.subgroup.isClosedImmersion
    letI : Mono C.subgroup.inclusion :=
      (Grp.forget (SchemeOver k)).mono_of_mono_map
        (inferInstanceAs (Mono C.subgroup.inclusion.hom.hom))
    apply (cancel_mono C.subgroup.inclusion).mp
    calc
      (a ≫ f) ≫ C.subgroup.inclusion = (a ≫ CB.inclusion) ≫ B.inclusion := by
        simp only [Category.assoc, hf]
        rfl
      _ = T.inclusion := by rw [ha, htB]
      _ = (C.torusIso.hom ≫ C.torus.inclusion) ≫ C.subgroup.inclusion := by
        rw [Category.assoc, C.torus_inclusion]
  let HB := closedSubgroupAlgebraicGroup (G := Balg) CB
  obtain ⟨E⟩ := existsLimitDecomposition HB (cochar ≫ a)
  have heq : (cochar ≫ a) ≫ f = cochar ≫ C.torusIso.hom ≫ C.torus.inclusion := by
    rw [Category.assoc, haC]
  obtain ⟨j, hj⟩ := map_contracting_of_comp HB.property.1 f heq E D
  let U := subgroupOfSubgroup C.subgroup D.contracting
  let V := subgroupOfSubgroup B (subgroupOfSubgroup CB E.contracting)
  have hVU : IsSubgroupOf V U := by
    refine ⟨j, ?_⟩
    change j ≫ D.contracting.inclusion ≫ C.subgroup.inclusion =
      (E.contracting.inclusion ≫ CB.inclusion) ≫ B.inclusion
    rw [← Category.assoc j, hj, Category.assoc, hf, Category.assoc]
    rfl
  have hVLie : lieImage U ⊆ lieImage V := by
    rw [show lieImage U = adjointWeightVectors T α.val from
      (positive_root_space_comparison A T α.val α.property C cochar hpos D hDa
        (identityLieStructure A)).2]
    intro v hv
    obtain ⟨vB, hvB⟩ := hweight hv
    letI := mono_over B.inclusion.hom.hom B.isClosedImmersion
    have hvS : vB ∈ adjointWeightVectors S_B 1 := by
      have hS' : S_B.inclusion ≫ B.inclusion = C.kernelTorus.inclusion ≫ T.inclusion := hS
      have hh := weightVector_of_map B.inclusion (T := S_B) (S := T) C.kernelTorus.inclusion hS'
        (show mapPointKernel B.inclusion vB ∈ adjointWeightVectors T α.val from hvB.symm ▸ hv)
      rwa [C.kernelTorus_largest.2.1] at hh
    have hvCB : vB ∈ lieImage CB := by
      rw [hCBL]
      change IsFixedBy (conjugationAction S_B.inclusion).smul vB.toMul.val
      apply (isFixedBy_conjugation_iff S_B.inclusion vB.toMul.val).mpr
      exact (zeroWeightVectors_iff_centralizes S_B
        (closedSubgroupAlgebraicGroup (G := Balg) S_B).property.1 vB).mp hvS
    obtain ⟨w, hw⟩ := hvCB
    have wroot : mapPointKernel CB.inclusion w ∈ adjointWeightVectors T_B α.val := by
      have hTB' : T_B.inclusion ≫ B.inclusion = 𝟙 T.group ≫ T.inclusion := by
        rw [Category.id_comp]
        exact htB
      have hh := weightVector_of_map B.inclusion (T := T_B) (S := T) (𝟙 T.group) hTB'
        (show mapPointKernel B.inclusion vB ∈ adjointWeightVectors T α.val from hvB.symm ▸ hv)
      have hid : (𝟙 T.group) ≫ α.val = α.val := Category.id_comp _
      exact hw.symm ▸ (hid ▸ hh)
    let s := identityLieStructure HB
    letI := s.lieRing
    letI := s.lieAlgebra
    obtain ⟨W, _, hW, _⟩ := lieWeights HB _ E s
    have he := restrictedCocharacterEigenvector T_B CB a ha cochar α.val w wroot
    have hmem : w ∈ lieImage E.contracting := by
      rw [hW]
      intro i hi
      have hpos' : 0 < pairing T_B.group α.val cochar := hpos
      exact eigenvector_coordinates _ W w _ he i (by omega)
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, ?_⟩
    change mapPointKernel ((E.contracting.inclusion ≫ CB.inclusion) ≫ B.inclusion) z = v
    rw [differential_comp, differential_comp, hz]
    exact (congrArg (fun u : Lie k B.group => mapPointKernel B.inclusion u) hw).trans hvB
  letI : Smooth HB.val.X.hom := hCBs
  letI : ConnectedSpace HB.val.X.left := connected_of_geometricallyConnected hCBc
  letI : Smooth H.val.X.hom := hC.1
  letI : ConnectedSpace H.val.X.left := connected_of_geometricallyConnected hC.2.1
  have hUV : IsSubgroupOf U V :=
    subgroupOf_of_lieImage (A := A) hVU (limitSubgroupsSmooth HB _ E).2.1
      (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups HB _ E).2.1)
      hDs (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups H _ D).2.1)
      hVLie
  exact subgroupOf_trans hUV ⟨E.contracting.inclusion ≫ CB.inclusion, rfl⟩

private theorem rootContainment_iff (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T B : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (hBs : Smooth B.group.X.hom) (hBc : ConnectedSpace B.group.X.left) (hTB : IsSubgroupOf T B)
    (α : ↥(absoluteRoots T)) (U : ClosedSubgroup A.val) (hU : IsRootSubgroup T U α.val) :
    α ∈ subgroupRoots T B ↔ IsSubgroupOf U B := by
  obtain ⟨_, _, V, _, _, hVL, _, hV⟩ := (RootGroups.rootSubgroups A hA T hT hTm).2 α.val α.property
  constructor
  · intro hw
    obtain ⟨C, cochar, hC, hpos, D, E, hpair, Q, F, P, L, p, n, hroot, _⟩ :=
      RootGroups.rankOneRootGroups A hA T hT hTm α.val α.property
    have h := rootSubgroup_containedOfWeight A hBs hBc hT hTB α C cochar hpos D
      hpair.2.2.2.1 hpair.2.2.2.2.2.2.2.1 hC hw
    exact subgroupOf_trans (hV U hU).2 (subgroupOf_trans (hV _ hroot).1 h)
  · intro h
    change adjointWeightVectors T α.val ⊆ lieImage B
    rw [← hVL]
    exact lieImage_mono (subgroupOf_trans (hV U hU).1 h)

/-- For a geometric Borel, containment of a root line is equivalent to
containment of its root subgroup. -/
theorem geometricBorelRootSubgroups : GeometricBorelRootSubgroups.{u} := by
  intro k _ _ A hA T hT hTm B hB hTB α U hU
  exact rootContainment_iff A hA T B hT hTm hB.1.1 hB.1.2.1 hTB α U hU

open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private torus_baseChange_algClosure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private conjugationIso conjugate comp_conjugate normalizes_of_conjugates_self
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem maximalTorus_of_geometricallyMaximal (A : AffineAlgebraicGroup k)
    (T : ClosedSubgroup A.val) (hT : IsTorus T.group) (hTm : IsGeometricallyMaximal T) :
    IsMaximalTorus T := by
  let K := AlgebraicClosure k
  obtain ⟨_, hm⟩ := hTm
  refine ⟨hT, fun S hS hTS => ?_⟩
  have h : IsSubgroupOf (extendSubgroup K S) (extendSubgroup K T) :=
    hm.2 (extendSubgroup K S)
      (torus_baseChange_algClosure (closedSubgroupAlgebraicGroup S) hS) (extend_subgroupOf hTS)
  exact subgroupOf_of_extend h

private theorem conjugateBorelPairWithFixedTorus [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hAs : Smooth A.val.X.hom) (hAc : ConnectedSpace A.val.X.left)
    (T : ClosedSubgroup A.val) (hTm : IsMaximalTorus T)
    {B C : ClosedSubgroup A.val} (hB : IsBorel B) (hC : IsBorel C)
    (hTB : IsSubgroupOf T B) (hTC : IsSubgroupOf T C) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ A.val.X, ConjugatesSubgroups n B C ∧ ConjugatesSubgroups n T T := by
  obtain ⟨f, hf⟩ := hTB
  obtain ⟨g, hg⟩ := hTC
  have h₁ := compose_restrict T B f hf
  have h₂ := compose_restrict T C g hg
  obtain ⟨n, hn, ht⟩ := MaximalToriConjugate.borelPairsConjugate A hAs hAc B C hB hC
    (restrictSubgroup T B f hf) (restrictSubgroup T C g hg)
    (local_maximal_of_ambient _ _ (h₁.symm ▸ hTm)) (local_maximal_of_ambient _ _ (h₂.symm ▸ hTm))
  exact ⟨n, hn, by simpa only [h₁,h₂] using ht⟩

private theorem conjugatesSubgroups_square (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    {B C : ClosedSubgroup G} (e : B.group ≅ C.group)
    (he : (e.hom ≫ C.inclusion).hom.hom = conjugate n B.inclusion.hom.hom) :
    B.inclusion ≫ (conjugationIso n).hom = e.hom ≫ C.inclusion := by
  apply Grp.hom_ext
  change B.inclusion.hom.hom ≫ conjugate n (𝟙 G.X) = (e.hom ≫ C.inclusion).hom.hom
  rw [comp_conjugate, Category.comp_id, he]

/-- Conjugation by a torus normalizer transports Borel chambers by inverse pullback. -/
theorem geometricBorelChamberConjugacy : GeometricBorelChamberConjugacy.{u} := by
  intro k _ _ A hA T hT hTm B C hB hC hTB hTC
  obtain ⟨n, hn, ht⟩ := conjugateBorelPairWithFixedTorus A hA.1
    (connected_of_geometricallyConnected hA.2.1) T
    (maximalTorus_of_geometricallyMaximal A T (lattice_torus_of_split hT) hTm) hB hC hTB hTC
  obtain ⟨c, hc⟩ := ht
  obtain ⟨e, he⟩ := hn
  exact ⟨n, c, normalizes_of_conjugates_self T ⟨c, hc⟩, ⟨e, he⟩, hc,
    subgroupRootsOfIso (conjugationIso n) c (conjugatesSubgroups_square n c hc) e
      (conjugatesSubgroups_square n e he)⟩

private def inverseBaseChangeIso {K : Type u} [Field K] [Algebra k K] [Algebra K k]
    (h : ∀ x : k, algebraMap K k (algebraMap k K x) = x) :
    groupBaseChange k K ⋙ groupBaseChange K k ≅ 𝟭 (GroupScheme k) := by
  have hc : CommRingCat.ofHom (algebraMap k K) ≫ CommRingCat.ofHom (algebraMap K k) = 𝟙 _ := by
    ext x
    exact h x
  have hs : fieldSpecMap K k ≫ fieldSpecMap k K = 𝟙 _ := by
    rw [← Spec.map_comp, hc, Spec.map_id]
  let e : Over.pullback (fieldSpecMap K k ≫ fieldSpecMap k K) ≅ 𝟭 (SchemeOver k) := by
    rw [hs]
    exact Over.pullbackId
  exact Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso
    ((Over.pullbackComp (fieldSpecMap K k) (fieldSpecMap k K)).symm ≪≫ e) ≪≫
    Functor.mapGrpIdIso

private def groupBaseChangeEquivalence {K : Type u} [Field K] [Algebra k K] [Algebra K k]
    (h : ∀ x : k, algebraMap K k (algebraMap k K x) = x)
    (h' : ∀ y : K, algebraMap k K (algebraMap K k y) = y) :
    GroupScheme k ≌ GroupScheme K :=
  CategoryTheory.Equivalence.mk _ _ (inverseBaseChangeIso h).symm (inverseBaseChangeIso h')

private theorem trivialGroup_of_trivial_baseChange {K : Type u} [Field K] [Algebra k K]
    [Algebra K k] (h : ∀ x : k, algebraMap K k (algebraMap k K x) = x)
    (h' : ∀ y : K, algebraMap k K (algebraMap K k y) = y)
    {N : GroupScheme k}
    (e : (groupBaseChange k K).obj N ≅ Grp.trivial (SchemeOver K)) :
    Nonempty (N ≅ Grp.trivial (SchemeOver k)) := by
  let E := groupBaseChangeEquivalence h h'
  letI : (groupBaseChange k K).IsEquivalence := E.isEquivalence_functor
  let h₁ := (Grp.isZero_trivial (SchemeOver K)).isTerminal.ofIso e.symm
  let h₂ := Limits.IsTerminal.isTerminalOfObj (groupBaseChange k K) N h₁
  exact ⟨h₂.uniqueUpToIso (Grp.isZero_trivial (SchemeOver k)).isTerminal⟩

open Specs.GeometricRadicals (IsTrivialSubgroup geometricUnipotentRadical)
open Specs.Unipotent (IsUnipotent baseChangedAlgebraicGroup)
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
open private trivial_of_subgroup_of_trivial from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

private theorem splitTorus_baseChange {K : Type u} [Field K] [Algebra k K]
    {T : GroupScheme k} (h : IsSplitTorus T) : IsSplitTorus ((groupBaseChange k K).obj T) := by
  obtain ⟨r, ⟨s⟩⟩ := splitPresentation h
  let M := Specs.CharacterDescent.StandardLattice.{u} r
  let A := Specs.DiagonalizableGroups.groupAlgebra k M
  let B := Specs.DiagonalizableGroups.groupAlgebra K M
  let e : extendedHopf K A ≅ B :=
    CommHopfAlgCat.isoMk (_root_.LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k K M)
  obtain ⟨j⟩ := _root_.LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) r
  exact ⟨r, ⟨((groupBaseChange k K).mapIso s).symm ≪≫ (extendedGroupIso K A).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso e.symm.op ≪≫ j⟩⟩

private theorem smooth_baseChangedGroup {K : Type u} [Field K] [Algebra k K]
    {A : GroupScheme k} (hs : Smooth A.X.hom) : Smooth ((groupBaseChange k K).obj A).X.hom :=
  MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback A.X.hom (fieldSpecMap k K)) hs

private theorem geomConnected_baseChangedGroup {K : Type u} [Field K] [Algebra k K]
    {A : GroupScheme k} (hc : GeometricallyConnected A.X.hom) :
    GeometricallyConnected ((groupBaseChange k K).obj A).X.hom :=
  MorphismProperty.of_isPullback (P := @GeometricallyConnected)
    (IsPullback.of_hasPullback A.X.hom (fieldSpecMap k K)) hc

private theorem connected_baseChangedGroup {K : Type u} [Field K] [Algebra k K]
    (A : AffineAlgebraicGroup k) (hc : ConnectedSpace A.val.X.left) :
    ConnectedSpace ((groupBaseChange k K).obj A.val).X.left := by
  letI := hc
  exact pullback_of_geometrically (geometricallyConnected_of_connected A).geometrically_connectedSpace
    K (fieldSpecMap k K)

private theorem reductive_geometricGroup (A : AffineAlgebraicGroup k) (hA : IsReductive A) :
    IsReductive (GeometricGroup A) := by
  let K := AlgebraicClosure k
  let L := AlgebraicClosure K
  let H := GeometricGroup A
  let e : K ≃+* L := RingEquiv.ofBijective (algebraMap K L) IsAlgClosed.algebraMap_bijective_of_isIntegral
  letI : Algebra L K := e.symm.toRingHom.toAlgebra
  have hKL (x : K) : algebraMap L K (algebraMap K L x) = x := e.symm_apply_apply x
  have hLK (y : L) : algebraMap K L (algebraMap L K y) = y := e.apply_symm_apply y
  refine ⟨smooth_baseChangedGroup hA.1, geomConnected_baseChangedGroup hA.2.1, ?_⟩
  let N := geometricUnipotentRadical H
  let φ := (inverseBaseChangeIso hKL).app H.val
  let M := extendSubgroup K N
  let V := transportSubgroup φ M
  have hN := _root_.LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest H
  have hR := _root_.LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest A
  have hVs : Smooth V.group.X.hom := smooth_baseChangedGroup hN.1.1
  have hVc : ConnectedSpace V.group.X.left :=
    connected_baseChangedGroup (closedSubgroupAlgebraicGroup N) hN.1.2.1
  have hVn : IsNormalSubgroup V.inclusion := by
    apply normalSubgroup_of_iso φ.symm (Iso.refl M.group)
      (i := M.inclusion) (i' := V.inclusion)
    · change (M.inclusion ≫ φ.hom) ≫ φ.inv = 𝟙 _ ≫ M.inclusion
      rw [Category.assoc, φ.hom_inv_id, Category.id_comp]
      exact Category.comp_id _
    · exact baseChangeNormalSubgroup L K N.inclusion hN.1.2.2
  have hVu : IsUnipotent (closedSubgroupAlgebraicGroup (G := H) V) := by
    obtain ⟨D, eD, hD⟩ := (Unipotent.unipotenceFieldExtension
      (K := K) (closedSubgroupAlgebraicGroup N)).mpr hN.2.1
    exact ⟨D, eD, hD⟩
  obtain ⟨eV⟩ := trivial_of_subgroup_of_trivial
    (hR.2.2 V ⟨hVs, hVc, hVn⟩ hVu) hA.2.2
  exact trivialGroup_of_trivial_baseChange hLK hKL eV

private theorem geometricallyMaximal_of_maximal_split [IsAlgClosed k]
    (A : AffineAlgebraicGroup k) (T : ClosedSubgroup A.val)
    (hTm : IsMaximalTorus T) (hTs : IsSplitTorus T.group) : IsGeometricallyMaximal T := by
  let K := AlgebraicClosure k
  let TK := extendSubgroup K T
  let e : k ≃+* K := RingEquiv.ofBijective (algebraMap k K) IsAlgClosed.algebraMap_bijective_of_isIntegral
  letI : Algebra K k := e.symm.toRingHom.toAlgebra
  let R := groupBaseChange K k
  have hback (x : k) : algebraMap K k (algebraMap k K x) = x := e.symm_apply_apply x
  let q := inverseBaseChangeIso (K := K) hback
  let qG := q.app A.val
  let qT := q.app T.group
  have hq : R.map TK.inclusion ≫ qG.hom = qT.hom ≫ T.inclusion := q.hom.naturality T.inclusion
  refine ⟨TK.isClosedImmersion, lattice_torus_of_split (splitTorus_baseChange (K := K) hTs), ?_⟩
  intro S hS hTS
  let SK := extendSubgroup k S
  let S' := transportSubgroup qG SK
  have hS' : IsTorus S'.group :=
    lattice_torus_of_split (splitTorus_baseChange (K := k)
      (split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup (G := GeometricGroup A) S)).mp hS)))
  obtain ⟨f, hf⟩ := hTS
  have hf' : R.map f ≫ R.map S.inclusion = R.map TK.inclusion := by
    rw [← Functor.map_comp]
    exact congrArg R.map (show f ≫ S.inclusion = TK.inclusion from hf)
  have hT' : IsSubgroupOf T S' := by
    refine ⟨qT.inv ≫ R.map f, ?_⟩
    change (qT.inv ≫ R.map f) ≫ (R.map S.inclusion ≫ qG.hom) = _
    simp only [Category.assoc]
    rw [← Category.assoc (R.map f), hf', hq, qT.inv_hom_id_assoc]
  obtain ⟨g, hg⟩ := hTm.2 S' hS' hT'
  apply subgroupOf_of_extend (K := k)
  refine ⟨g ≫ qT.inv, ?_⟩
  apply (cancel_mono qG.hom).mp
  change ((g ≫ qT.inv) ≫ R.map TK.inclusion) ≫ qG.hom = R.map S.inclusion ≫ qG.hom
  simp only [Category.assoc]
  rw [hq, qT.inv_hom_id_assoc]
  exact hg

open Specs.CharacterPairing (adjointWeightSpace)
open CocharacterDynamics (cocharacterPoint)
open private adjointWeightsInternal root_weight_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private canonicalZero_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private standardLatticeDomain from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private splitTorus_sectionsCommute from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

private theorem splitTorus_connected {T : GroupScheme k} (hT : IsSplitTorus T) :
    ConnectedSpace T.X.left := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let M := Specs.CharacterDescent.StandardLattice.{u} r
  let A := Specs.DiagonalizableGroups.groupAlgebra k M
  letI : IsDomain A := standardLatticeDomain r
  let e := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso i
  exact e.hom.homeomorph.connectedSpace_iff.mp (inferInstanceAs (ConnectedSpace (PrimeSpectrum A)))

private theorem pairing_one (T : GroupScheme k) (hT : IsSplitTorus T) (c : Cocharacter T) :
    pairing T 1 c = 0 := by
  obtain ⟨hComm, _, _, _, _, P, _, hP⟩ := CharacterPairing.perfectCharacterPairing T hT
  letI := hComm
  rw [← hP]
  change P 0 (Additive.ofMul c) = 0
  rw [map_zero, LinearMap.zero_apply]

private theorem pairing_inv (T : GroupScheme k) (hT : IsSplitTorus T)
    (χ : Character T) (c : Cocharacter T) : pairing T χ⁻¹ c = -pairing T χ c := by
  obtain ⟨hComm, _, _, _, _, P, _, hP⟩ := CharacterPairing.perfectCharacterPairing T hT
  letI := hComm
  rw [← hP, ← hP]
  change P (-Additive.ofMul χ) (Additive.ofMul c) = -P (Additive.ofMul χ) (Additive.ofMul c)
  rw [map_neg, LinearMap.neg_apply]

private theorem cocharacter_weight_coordinates {A : AffineAlgebraicGroup k}
    (T : ClosedSubgroup A.val) (c : Cocharacter T.group)
    (s : IdentityLieStructure A.val) (W : CocharacterDynamics.AdjointWeightBasis (c ≫ T.inclusion) s)
    {χ : Character T.group} {v : Lie k A.val} (hv : v ∈ adjointWeightVectors T χ) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ j, W.weight j ≠ pairing T.group χ c → W.basis.equivFun v j = 0 := by
  apply eigenvector_coordinates
  intro R t
  have h := hv R (cocharacterPoint c R t)
  rw [(CharacterPairing.characterPairingComposition T.group χ c).2 R t] at h
  have hpt : cocharacterPoint (c ≫ T.inclusion) R t =
      cocharacterPoint c R t ≫ T.inclusion.hom.hom := by
    change CocharacterDynamics.unitPoint R t ≫ (c.hom.hom ≫ T.inclusion.hom.hom) =
      (CocharacterDynamics.unitPoint R t ≫ c.hom.hom) ≫ T.inclusion.hom.hom
    exact (Category.assoc _ _ _).symm
  dsimp only
  rw [hpt]
  exact h

private theorem limitLie_weightSpans (A : AffineAlgebraicGroup k)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group)
    (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ T.inclusion))
    (s : IdentityLieStructure A.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    lieImage D.parabolic =
        ((⨆ χ : {χ : Character T.group // 0 ≤ pairing T.group χ c},
          adjointWeightSpace T χ.val s : Submodule k (Lie k A.val)) : Set (Lie k A.val)) ∧
    lieImage D.centralizer =
        ((⨆ χ : {χ : Character T.group // pairing T.group χ c = 0},
          adjointWeightSpace T χ.val s : Submodule k (Lie k A.val)) : Set (Lie k A.val)) := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W, hW, _, hZ⟩ := lieWeights A _ D s
  have htop := (adjointWeightsInternal A T hT s).submodule_iSup_eq_top
  have hcoords (χ : Character T.group) (v : Lie k A.val) (hv : v ∈ adjointWeightSpace T χ s) :
      ∀ j, W.weight j ≠ pairing T.group χ c → W.basis.equivFun v j = 0 := by
    have h := CharacterPairing.adjointWeightSpaceVectors A T s χ
    exact cocharacter_weight_coordinates T c s W (h ▸ hv)
  have h (P : ℤ → Prop) := coordinate_space_eq_iSup W.basis W.weight (fun χ => pairing T.group χ c)
    (fun χ => adjointWeightSpace T χ s) htop hcoords P
  exact ⟨hW.trans (by simpa only [not_le] using (h (fun n => 0 ≤ n)).symm),
    hZ.trans (h (fun n => n = 0)).symm⟩

private theorem torus_subgroupOf_centralizer {T : ClosedSubgroup G}
    (hT : IsSplitTorus T.group) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion)) : IsSubgroupOf T D.centralizer := by
  have h : Centralizes (c ≫ T.inclusion) T.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X t a
    letI := splitTorus_sectionsCommute hT X
    have ha : Commute t (a ≫ c.hom.hom) := mul_comm' _ _
    have hm := ha.map (IsMonHom.monoidHom T.inclusion.hom.hom X)
    change Commute (t ≫ T.inclusion.hom.hom) (a ≫ c.hom.hom ≫ T.inclusion.hom.hom)
    rw [← Category.assoc a]
    exact hm
  obtain ⟨f, hf⟩ := (D.centralizer_points _ _).mp h
  exact factor_group_through_subgroup D.centralizer T.inclusion f hf

private theorem centralizer_of_regular (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (c : Cocharacter T.group) (hr : IsRegular T c) (D : LimitDecomposition (c ≫ T.inclusion)) :
    SameSubgroup D.centralizer T := by
  letI := hA.1
  letI : ConnectedSpace A.val.X.left := connected_of_geometricallyConnected hA.2.1
  let s := identityLieStructure A
  letI := s.lieRing
  letI := s.lieAlgebra
  have hz := (CharacterPairing.zeroWeightSpace A hA T hT hTm s).2
  have hsub : IsSubgroupOf T D.centralizer := torus_subgroupOf_centralizer hT c D
  refine ⟨subgroupOf_of_lieImage (A := A) hsub (splitTorusSmooth hT) (splitTorus_connected hT)
    (limitSubgroupsSmooth A _ D).2.2
    (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups A _ D).2.2)
    ?_, hsub⟩
  change lieImage D.centralizer ⊆ Set.range (mapPointKernel T.inclusion)
  rw [← hz, (limitLie_weightSpans A T hT c D s).2]
  change (⨆ χ : {χ : Character T.group // pairing T.group χ c = 0},
    adjointWeightSpace T χ.val s) ≤ adjointWeightSpace T 1 s
  apply iSup_le
  intro χ
  by_cases h : χ.val = 1
  · rw [h]
  have hw : adjointWeightSpace T χ.val s = ⊥ := by
    by_contra hw
    have hroot := (CharacterPairing.absoluteRootWeights T s χ.val).mpr ⟨h, hw⟩
    exact hr ⟨χ.val, hroot⟩ χ.property
  rw [hw]
  exact bot_le

private theorem regular_of_centralizer (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ T.inclusion))
    (hZ : SameSubgroup D.centralizer T) :
    IsRegular T c := by
  intro α hα
  obtain ⟨_, v, hv, hv0⟩ := α.property
  let s := identityLieStructure A
  letI := s.lieRing
  letI := s.lieAlgebra
  have hvZ : v ∈ lieImage D.centralizer := by
    rw [(limitLie_weightSpans A T hT c D s).2]
    apply (le_iSup (fun χ : {χ : Character T.group // pairing T.group χ c = 0} =>
      adjointWeightSpace T χ.val s) ⟨α.val, hα⟩)
    change v ∈ (adjointWeightSpace T α.val s : Set (Lie k A.val))
    rwa [CharacterPairing.adjointWeightSpaceVectors A T s α.val]
  have hvT : v ∈ adjointWeightVectors T 1 := by
    rw [← CharacterPairing.adjointWeightSpaceVectors A T s 1,
      (CharacterPairing.zeroWeightSpace A hA T hT hTm s).2]
    exact lieImage_mono hZ.1 hvZ
  exact α.property.1 (root_weight_unique A T hT hv0 hv hvT)

private theorem subgroupRoots_of_regular (A : AffineAlgebraicGroup k)
    (T : ClosedSubgroup A.val) (c : Cocharacter T.group) (hc : IsRegular T c)
    (D : LimitDecomposition (c ≫ T.inclusion)) :
    subgroupRoots T D.parabolic = positiveRoots T c := by
  ext α
  change (adjointWeightVectors T α.val ⊆ lieImage D.parabolic) ↔ 0 < pairing T.group α.val c
  let s := identityLieStructure A
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W, hW, _, _⟩ := lieWeights A _ D s
  constructor
  · intro h
    by_contra hn
    have hneg : pairing T.group α.val c < 0 := lt_of_le_of_ne (le_of_not_gt hn) (hc α)
    obtain ⟨_, v, hv, hv0⟩ := α.property
    have hvW := h hv
    rw [hW] at hvW
    apply hv0
    have hzero (j : ULift.{u} (Fin W.dimension)) : W.basis.equivFun v j = 0 := by
      by_cases hj : W.weight j = pairing T.group α.val c
      · exact hvW j (hj.symm ▸ hneg)
      · exact cocharacter_weight_coordinates T c s W hv j hj
    exact (W.basis.equivFun.injective
      ((funext hzero).trans W.basis.equivFun.map_zero.symm)).trans (canonicalZero_eq s).symm
  · intro h v hv
    rw [hW]
    intro j hj
    exact cocharacter_weight_coordinates T c s W hv j (by omega)

open Specs.SchemeDerivedGroup (IsSolvable)
open private exists_borel_above from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private normalOfSchemeKernel liftToSchemeKernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private torus_multiplicativeType from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private rationalMap rationalSections solvable_iff_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private solvable_of_smooth_connected_unipotent from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private map_limit_parabolic from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private normalizerInBorelCentralizes from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint

private theorem radical_of_torus_kernel {A L : AffineAlgebraicGroup k}
    (U : ClosedSubgroup A.val) (q : A.val ⟶ L.val) (hq : IsSchemeKernel q U)
    (hL : IsSplitTorus L.val) (hUs : Smooth U.group.X.hom) (hUc : ConnectedSpace U.group.X.left)
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup U)) :
    Specs.GeometricRadicals.IsUnipotentRadical A U := by
  have hmult := torus_multiplicativeType ((isTorus_iff_coordinates L).mp (lattice_torus_of_split hL))
  refine ⟨⟨hUs, hUc, normalOfSchemeKernel hq⟩, hU, fun V _ hV => ?_⟩
  exact liftToSchemeKernel hq V.inclusion
    (Unipotent.homFromUnipotentToMultiplicativeType (closedSubgroupAlgebraicGroup V) L
      (V.inclusion ≫ q) hV hmult)

private theorem solvable_of_torus_kernel [IsAlgClosed k] {A L : AffineAlgebraicGroup k}
    (U : ClosedSubgroup A.val) (q : A.val ⟶ L.val) (hq : IsSchemeKernel q U)
    (hL : IsSplitTorus L.val) (hAs : Smooth A.val.X.hom) (hAc : ConnectedSpace A.val.X.left)
    (hUs : Smooth U.group.X.hom) (hUc : ConnectedSpace U.group.X.left)
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup U)) : IsSolvable A.val := by
  let Q := closedSubgroupAlgebraicGroup U
  letI : Group.IsSolvable (rationalSections U.group) := (solvable_iff_sections Q hUs hUc).mp
    (solvable_of_smooth_connected_unipotent Q hUs hUc hU)
  letI := splitTorus_sectionsCommute hL (𝟙_ (SchemeOver k))
  apply (solvable_iff_sections A hAs hAc).mpr
  apply Group.isSolvable_of_ker_le_range (rationalMap U.inclusion) (rationalMap q)
  intro b hb
  have hb' : b ≫ q.hom.hom = toUnit _ ≫ η[L.val.X] := hb
  exact ⟨hq.lift b (toUnit _) hb', hq.lift_fst _ _ _⟩

private theorem rankOneWord_comp {L : Specs.RootGroups.AdditiveLine k}
    (x y : L.group ⟶ G) (f : G ⟶ H) (R : TestAlgebra k) (z : Rˣ) :
    Specs.RootGroups.rankOneWord x y R z ≫ f.hom.hom =
      Specs.RootGroups.rankOneWord (x ≫ f) (y ≫ f) R z := by
  let F := ((groupPointsFunctor k).map f).app R
  change F (Specs.RootGroups.rankOneWord x y R z) =
    Specs.RootGroups.rankOneWord (x ≫ f) (y ≫ f) R z
  unfold Specs.RootGroups.rankOneWord
  rw [map_mul, map_mul]
  have h (t : L.group ⟶ G) (r : R) :
      F (Specs.RootGroups.rootPoint t R r) = Specs.RootGroups.rootPoint (t ≫ f) R r :=
    (rootPoint_comp t f R r).symm
  rw [h, h]

private theorem root_and_opposite_not_in_borel [IsAlgClosed k]
    (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T B : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (hB : IsBorel B) (hTB : IsSubgroupOf T B) (α β : ↥(absoluteRoots T))
    (hβ : β.val = α.val⁻¹) (hαB : α ∈ subgroupRoots T B) (hβB : β ∈ subgroupRoots T B) : False := by
  obtain ⟨C, c, _, _, D, E, _, Q, F, P, L, p, n, hDp, hEn, hp, hn, ⟨r⟩⟩ :=
    RootGroups.rankOneRootGroups A hA T hT hTm α.val α.property
  let U := subgroupOfSubgroup C.subgroup D.contracting
  let V := subgroupOfSubgroup C.subgroup E.contracting
  obtain ⟨a, ha⟩ := (rootContainment_iff A hA T B hT hTm hB.1.1 hB.1.2.1 hTB α U hDp).mp hαB
  obtain ⟨b, hb⟩ := (rootContainment_iff A hA T B hT hTm hB.1.1 hB.1.2.1 hTB β V (hβ.symm ▸ hEn)).mp hβB
  let x : L.group ⟶ B.group := p.root.hom ≫ a
  let y : L.group ⟶ B.group := n.root.hom ≫ b
  let R := CommAlgCat.of k k
  let S := (testSpec k).obj (Opposite.op R)
  let e : S ≅ 𝟙_ (SchemeOver k) :=
    (affineBaseTerminal k).uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  let w : S ⟶ B.group.X := Specs.RootGroups.rankOneWord x y R 1
  have hw : w ≫ B.inclusion.hom.hom = e.hom ≫ r.representative := by
    have hrword : toUnit S ≫ r.representative =
        Specs.RootGroups.rankOneWord
          (p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion)
          (n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion) R 1 := r.representative_word
    change w ≫ B.inclusion.hom.hom = toUnit S ≫ r.representative
    rw [hrword]
    have hx : x ≫ B.inclusion = p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion := by
      rw [show x = p.root.hom ≫ a from rfl, Category.assoc, ha]
      rfl
    have hy : y ≫ B.inclusion = n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion := by
      rw [show y = n.root.hom ≫ b from rfl, Category.assoc, hb]
      rfl
    exact (rankOneWord_comp x y B.inclusion R 1).trans (congrArg₂
      (fun f g => Specs.RootGroups.rankOneWord f g R 1) hx hy)
  let z := e.inv ≫ w
  have hz : z ≫ B.inclusion.hom.hom = r.representative := by
    change (e.inv ≫ w) ≫ B.inclusion.hom.hom = _
    rw [Category.assoc, hw, e.inv_hom_id_assoc]
  have hcent := normalizerInBorelCentralizes
    (maximalTorus_of_geometricallyMaximal A T (lattice_torus_of_split hT) hTm) hB hTB
    (b := z) (hz.symm ▸ r.normalizes)
  rw [hz] at hcent
  have he : r.conjugation.hom ≫ T.inclusion = T.inclusion := by
    apply Grp.hom_ext
    rw [r.conjugates]
    have ht := (centralizes_iff _ _).mp hcent T.group.X (toUnit T.group.X) (𝟙 T.group.X)
    change Commute (toUnit T.group.X ≫ r.representative) ((𝟙 T.group.X) ≫ T.inclusion.hom.hom) at ht
    rw [Category.id_comp] at ht
    rw [mul_inv_eq_iff_eq_mul]
    exact ht.eq
  letI : Mono T.inclusion :=
    (Grp.forget (SchemeOver k)).mono_of_mono_map (mono_over _ T.isClosedImmersion)
  have hid : r.conjugation.hom = 𝟙 _ := (cancel_mono T.inclusion).mp (he.trans (Category.id_comp _).symm)
  have hid' : r.conjugation.inv = 𝟙 _ := by
    have h := r.conjugation.inv_hom_id
    rw [hid, Category.comp_id] at h
    exact h
  have hα : α.val = α.val⁻¹ := by
    have h := r.reflection α.val
    rw [hid', Category.id_comp, r.root_pairing] at h
    exact h.trans (by group)
  have h := pairing_inv T.group hT α.val r.coroot
  rw [← hα, r.root_pairing] at h
  omega

private theorem map_parabolic_of_comp (hAff : IsAffine G.X.left) (f : G ⟶ H)
    {c : Cocharacter G} {d : Cocharacter H} (h : c ≫ f = d)
    (D : LimitDecomposition c) (E : LimitDecomposition d) :
    ∃ j : D.parabolic.group ⟶ E.parabolic.group, j ≫ E.parabolic.inclusion = D.parabolic.inclusion ≫ f := by
  subst d
  exact map_limit_parabolic hAff f D E

/-- A smooth connected subgroup through the torus lies in the limit parabolic
when all of its Lie roots pair nonnegatively with the cocharacter. -/
private theorem subgroupOf_limit_of_rootSigns (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T B : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (hBs : Smooth B.group.X.hom) (hBc : ConnectedSpace B.group.X.left) (hTB : IsSubgroupOf T B)
    (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ T.inclusion))
    (hsign : ∀ α ∈ subgroupRoots T B, 0 ≤ pairing T.group α.val c) :
    IsSubgroupOf B D.parabolic := by
  classical
  obtain ⟨j, hj⟩ := hTB
  let H := closedSubgroupAlgebraicGroup B
  let S := restrictSubgroup T B j hj
  obtain ⟨E⟩ := existsLimitDecomposition H (c ≫ j)
  let s := identityLieStructure A
  let t := identityLieStructure H
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := t.lieRing
  letI := t.lieAlgebra
  letI : AddCommGroup (Lie k A.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k A.val) := s.lieAlgebra.toModule
  letI : AddCommGroup (Lie k B.group) := t.lieRing.toAddCommGroup
  letI : Module k (Lie k B.group) := t.lieAlgebra.toModule
  letI := A.property.1
  letI := H.property.1
  letI := mono_over B.inclusion.hom.hom B.isClosedImmersion
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k H.val A.val B.inclusion t s
  have hpreserve (χ : Character T.group) (v : Lie k H.val) (hv : v ∈ adjointWeightVectors S χ) :
      mapPointKernel B.inclusion v ∈ adjointWeightVectors T χ := by
    have hj' : S.inclusion ≫ B.inclusion = (Iso.refl T.group).hom ≫ T.inclusion :=
      hj.trans (Category.id_comp T.inclusion).symm
    have hv' : v ∈ adjointWeightVectors S ((Iso.refl T.group).hom ≫ χ) := by
      exact (show (Iso.refl T.group).hom ≫ χ = χ from Category.id_comp χ).symm ▸ hv
    exact map_weightVector B.inclusion (T := S) (S := T) (Iso.refl T.group) hj' hv'
  let W (χ : Character T.group) := adjointWeightSpace S χ t
  let I := {χ : Character T.group // 0 ≤ pairing T.group χ c}
  have htop : (⨆ χ : I, W χ.val) = ⊤ := by
    apply top_unique
    rw [← (adjointWeightsInternal H S hT t).submodule_iSup_eq_top]
    apply iSup_le
    intro χ
    by_cases hχ : 0 ≤ pairing T.group χ c
    · exact le_iSup (fun χ : I => W χ.val) ⟨χ, hχ⟩
    have heq : W χ = ⊥ := by
      by_contra hw
      obtain ⟨v, hv, hv0⟩ := ((W χ).ne_bot_iff).mp hw
      have hwv : v ∈ adjointWeightVectors S χ :=
        (CharacterPairing.adjointWeightSpaceVectors H S t χ) ▸ hv
      let w : Lie k A.val := d v
      have hwv' : w ∈ adjointWeightVectors T χ := Eq.mp
        (congrArg (fun a : Lie k A.val => a ∈ adjointWeightVectors T χ) (hd v).symm)
        (hpreserve χ v hwv)
      have hw0 : w ≠ 0 := by
        intro he
        apply hv0
        have hh : d v = d 0 := by simpa only [map_zero] using he
        exact differential_injective B.inclusion ((hd v).symm.trans (hh.trans (hd 0)))
      have hχ1 : χ ≠ 1 := by
        rintro rfl
        exact hχ (by rw [pairing_one _ hT])
      let α : ↥(absoluteRoots T) := ⟨χ, hχ1, w, hwv', (canonicalZero_eq s).symm ▸ hw0⟩
      have hr := (RootGroups.rootSubgroups A hA T hT hTm).2 χ α.property
      have hwmem : w ∈ adjointWeightSpace T χ s := Eq.mp
        (congrArg (fun M : Set (Lie k A.val) => w ∈ M)
          (CharacterPairing.adjointWeightSpaceVectors A T s χ).symm) hwv'
      have hrange : adjointWeightSpace T χ s ≤ LinearMap.range d.toLinearMap := by
        rw [eq_span_singleton_of_mem_of_finrank_eq_one (hr.1 s) hwmem hw0]
        apply Submodule.span_le.mpr
        intro x hx
        exact ⟨v, (Set.mem_singleton_iff.mp hx).symm⟩
      apply hχ
      apply hsign α
      intro v' hv'
      have hv'' : v' ∈ adjointWeightSpace T χ s := Eq.mp
        (congrArg (fun M : Set (Lie k A.val) => v' ∈ M)
          (CharacterPairing.adjointWeightSpaceVectors A T s χ).symm) hv'
      obtain ⟨w', hw'⟩ := hrange hv''
      exact ⟨w', (hd w').symm.trans hw'⟩
    change W χ ≤ ⨆ χ : I, W χ.val
    rw [heq]
    exact bot_le
  have he : lieImage E.parabolic = Set.univ := by
    rw [(limitLie_weightSpans H S hT c E t).1]
    change ((⨆ χ : I, W χ.val : Submodule k (Lie k H.val)) : Set (Lie k H.val)) = _
    rw [htop, Submodule.top_coe]
  letI : Smooth H.val.X.hom := hBs
  letI : ConnectedSpace H.val.X.left := hBc
  let Ealg := closedSubgroupAlgebraicGroup (G := H) E.parabolic
  letI : IsIso E.parabolic.inclusion := isIso_of_closedImmersion_of_differential
    (A := Ealg) (B := H) E.parabolic.inclusion E.parabolic.isClosedImmersion
    (limitSubgroupsSmooth H _ E).1
    (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups H _ E).1)
    hBs hBc (Set.range_eq_univ.mp he)
  have hcomp : (c ≫ j) ≫ B.inclusion = c ≫ T.inclusion := by rw [Category.assoc, hj]
  obtain ⟨f, hf⟩ := map_parabolic_of_comp H.property.1 B.inclusion hcomp E D
  exact ⟨inv E.parabolic.inclusion ≫ f, by rw [Category.assoc, hf, IsIso.inv_hom_id_assoc]⟩

private theorem regular_isBorel [IsAlgClosed k] (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (c : Cocharacter T.group) (hc : IsRegular T c) (D : LimitDecomposition (c ≫ T.inclusion))
    (hZ : SameSubgroup D.centralizer T) : IsBorel D.parabolic := by
  letI := hA.1
  letI : ConnectedSpace A.val.X.left := connected_of_geometricallyConnected hA.2.1
  let B := closedSubgroupAlgebraicGroup D.parabolic
  let U := contractingSubgroup D
  let L := closedSubgroupAlgebraicGroup D.centralizer
  obtain ⟨e, _⟩ := subgroupIso_of_same hZ
  have hL : IsSplitTorus L.val := by
    obtain ⟨r, ⟨f⟩⟩ := hT
    exact ⟨r, ⟨e ≪≫ f⟩⟩
  obtain ⟨hBs, hUs, _⟩ := limitSubgroupsSmooth A _ D
  obtain ⟨hBc, hUc, _⟩ := geometricallyConnectedLimitSubgroups A _ D
  let hBu : IsUnipotent (closedSubgroupAlgebraicGroup (G := B) U) := by
    obtain ⟨M, i, hM⟩ := contractingSubgroupUnipotent A _ D
    exact ⟨M, i, hM⟩
  have hsol : IsSolvable B.val := solvable_of_torus_kernel (A := B) (L := L) U D.limit D.isKernel hL hBs
    (connected_of_geometricallyConnected hBc) hUs (connected_of_geometricallyConnected hUc) hBu
  have hB : IsSmoothConnectedSolvable D.parabolic :=
    ⟨hBs, connected_of_geometricallyConnected hBc, hsol⟩
  obtain ⟨C, hC, hBC⟩ := exists_borel_above A D.parabolic hB
  have hTC := subgroupOf_trans (subgroupOf_trans hZ.2 ⟨D.sectionMap, D.section_in_G⟩) hBC
  have hCB : IsSubgroupOf C D.parabolic := by
    apply subgroupOf_limit_of_rootSigns A hA T C hT hTm hC.1.1 hC.1.2.1 hTC c D
    intro α hα
    by_contra h
    have hneg : pairing T.group α.val c < 0 := lt_of_not_ge h
    have hroot := (RootGroups.rootSubgroups A hA T hT hTm).2 α.val α.property
    let β : ↥(absoluteRoots T) := ⟨α.val⁻¹, (hroot.2.1 _).mpr (Or.inr rfl) |>.1⟩
    have hpos : 0 < pairing T.group β.val c := by
      change 0 < pairing T.group α.val⁻¹ c
      rw [pairing_inv _ hT]
      omega
    have hβ : β ∈ subgroupRoots T D.parabolic := by
      rw [subgroupRoots_of_regular A T c hc D]
      exact hpos
    exact root_and_opposite_not_in_borel A hA T C hT hTm hC hTC α β rfl hα
      (fun v hv => lieImage_mono hBC (hβ hv))
  exact ⟨hB, fun H hH hBH => subgroupOf_trans (hC.2 H hH (subgroupOf_trans hCB hBH)) hCB⟩

open private limits_subgroups_extend borel_of_same
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private baseChangeKernelSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components

private theorem centralizer_of_cast {c d : Cocharacter G}
    (h : c = d) (D : LimitDecomposition c) :
    (h ▸ D : LimitDecomposition d).centralizer = D.centralizer := by
  subst d
  rfl

/-- The limit subgroups for a regular cocharacter give a Borel and its radical. -/
theorem regularCocharacterBorel : RegularCocharacterBorel.{u} := by
  intro k _ A hA T hT hTm c hc D
  letI := hA.1
  letI : ConnectedSpace A.val.X.left := connected_of_geometricallyConnected hA.2.1
  have hZ := centralizer_of_regular A hA T hT hTm c hc D
  have hTB : IsSubgroupOf T D.parabolic := subgroupOf_trans hZ.2 ⟨D.sectionMap, D.section_in_G⟩
  let B := closedSubgroupAlgebraicGroup D.parabolic
  let U := contractingSubgroup D
  let L := closedSubgroupAlgebraicGroup D.centralizer
  obtain ⟨e, _⟩ := subgroupIso_of_same hZ
  have hL : IsSplitTorus L.val := by
    obtain ⟨r, ⟨f⟩⟩ := hT
    exact ⟨r, ⟨e ≪≫ f⟩⟩
  have hUs := (limitSubgroupsSmooth A _ D).2.1
  have hUc := (geometricallyConnectedLimitSubgroups A _ D).2.1
  have hU : IsUnipotent (closedSubgroupAlgebraicGroup (G := B) U) := by
    obtain ⟨M, f, hM⟩ := contractingSubgroupUnipotent A _ D
    exact ⟨M, f, hM⟩
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let U' := extendSubgroup K U
  have hR : Specs.GeometricRadicals.IsUnipotentRadical B U :=
    radical_of_torus_kernel (A := B) (L := L) U D.limit D.isKernel hL hUs (connected_of_geometricallyConnected hUc) hU
  have hUg : IsUnipotent (closedSubgroupAlgebraicGroup (G := GeometricGroup B) U') := by
    obtain ⟨M, f, hM⟩ := (Unipotent.unipotenceFieldExtension (K := K)
      (closedSubgroupAlgebraicGroup (G := B) U)).mpr hU
    exact ⟨M, f, hM⟩
  have hRg : Specs.GeometricRadicals.IsUnipotentRadical (GeometricGroup B) U' :=
    radical_of_torus_kernel (A := GeometricGroup B) (L := GeometricGroup L) U' (F.map D.limit) (baseChangeKernelSquare D.limit _ D.isKernel)
      (splitTorus_baseChange hL) (smooth_baseChangedGroup hUs)
      (connected_of_geometricallyConnected (geomConnected_baseChangedGroup hUc)) hUg
  refine ⟨hZ, ?_, hTB, subgroupRoots_of_regular A T c hc D, hR, ⟨U'.isClosedImmersion, hRg⟩⟩
  let J := GeometricGroup A
  let S := extendSubgroup K T
  have hJ : IsReductive J := reductive_geometricGroup A hA
  have hS : IsSplitTorus S.group := splitTorus_baseChange hT
  have hSm : IsGeometricallyMaximal S :=
    geometricallyMaximal_of_maximal_split J S hTm.choose_spec hS
  obtain ⟨g, hg, _⟩ := CocharacterDynamics.limitSubgroupsBaseChange (K := K)
    A (c ≫ T.inclusion) D
  let c' := g.hom ≫ F.map c
  let d := g.hom ≫ F.map (c ≫ T.inclusion)
  have hd : d = c' ≫ S.inclusion := by
    change g.hom ≫ F.map (c ≫ T.inclusion) = (g.hom ≫ F.map c) ≫ F.map T.inclusion
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨E₀⟩ := existsLimitDecomposition J d
  obtain ⟨hP, _, hZ'⟩ := limits_subgroups_extend A D g hg E₀
  let E := hd ▸ E₀
  have hES : SameSubgroup E.centralizer S := by
    change SameSubgroup (hd ▸ E₀ : LimitDecomposition (c' ≫ S.inclusion)).centralizer S
    rw [centralizer_of_cast hd E₀]
    exact same_subgroup_trans hZ' ⟨extend_subgroupOf hZ.1, extend_subgroupOf hZ.2⟩
  have hcreg : IsRegular S c' := regular_of_centralizer J hJ S hS hSm c' E hES
  have hEB : IsBorel E.parabolic := regular_isBorel J hJ S hS hSm c' hcreg E hES
  refine ⟨(extendSubgroup K D.parabolic).isClosedImmersion, borel_of_same (H := J) hEB ?_⟩
  change SameSubgroup (hd ▸ E₀ : LimitDecomposition (c' ≫ S.inclusion)).parabolic _
  rw [parabolic_of_cast hd E₀]
  exact hP

private theorem exists_avoiding_zero_forms
    {Y I : Type*} [AddCommGroup Y] [Finite I] (p : I → Y →ₗ[ℤ] ℤ)
    (h : ∀ i, ∃ y, p i y ≠ 0) : ∃ y, ∀ i, p i y ≠ 0 := by
  classical
  letI := Fintype.ofFinite I
  suffices ∀ s : Finset I, ∃ y, ∀ i ∈ s, p i y ≠ 0 by
    obtain ⟨y, hy⟩ := this Finset.univ
    exact ⟨y, fun i => hy i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, hz⟩ := h a
    let bad := (insert a s).image (fun i => -p i y / p i z)
    obtain ⟨n, hn⟩ := bad.exists_notMem
    refine ⟨y + n • z, fun i hi he => ?_⟩
    have he : p i y + n * p i z = 0 := by
      simpa only [map_add, map_smul, zsmul_eq_mul, Int.cast_id] using he
    by_cases hzero : p i z = 0
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hz hzero
      · rw [hzero, mul_zero, add_zero] at he
        exact hy i hi he
    · have hm : -p i y = n * p i z := by omega
      apply hn
      exact Finset.mem_image.mpr ⟨i, hi, by rw [hm, Int.mul_ediv_cancel _ hzero]⟩

private theorem exists_regular_cocharacter (A : AffineAlgebraicGroup k) (T : ClosedSubgroup A.val)
    (hT : IsSplitTorus T.group) : ∃ c : Cocharacter T.group, IsRegular T c := by
  obtain ⟨hComm, _, _, _, _, P, hP, hpair⟩ := CharacterPairing.perfectCharacterPairing T.group hT
  letI := hComm
  letI := hP
  letI : Finite ↥(absoluteRoots T) := CharacterPairing.finiteAbsoluteRoots A T hT
  obtain ⟨y, hy⟩ := exists_avoiding_zero_forms
    (fun α : ↥(absoluteRoots T) => P (Additive.ofMul α.val)) (by
      intro α
      by_contra! hα
      apply α.property.1
      have hz : P (Additive.ofMul α.val) = 0 := LinearMap.ext hα
      have he : P.toPerfPair (Additive.ofMul α.val) = P.toPerfPair 0 :=
        hz.trans P.toPerfPair.map_zero.symm
      exact congrArg Additive.toMul (P.toPerfPair.injective he))
  refine ⟨y.toMul, fun α => ?_⟩
  rw [← hpair]
  exact hy α

open private conjugateLe_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private conjugate_comp conjugate_inv_cancel conjugates_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private constant_sections_after_scalar_extension scalarExtendedPoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

private theorem conjugates_by_normalizing_point {T : ClosedSubgroup G}
    (n : 𝟙_ (SchemeOver k) ⟶ G.X) (hn : Normalizes T.inclusion n) :
    ConjugatesSubgroups n T T := by
  let e := conjugationIso n
  let S := transportSubgroup e T
  have h (m : 𝟙_ (SchemeOver k) ⟶ G.X) (hm : ConjugateLe T.inclusion m) :
      ∃ j : T.group ⟶ T.group, j ≫ T.inclusion = T.inclusion ≫ (conjugationIso m).hom := by
    obtain ⟨a, ha⟩ := (conjugateLe_iff _ _).mp hm T.group.X (toUnit _) (𝟙 _)
    apply factor_group_through_subgroup T _ a
    change a ≫ T.inclusion.hom.hom = T.inclusion.hom.hom ≫ conjugate m (𝟙 G.X)
    rw [comp_conjugate, Category.comp_id]
    simpa only [conjugate, Category.id_comp] using ha
  obtain ⟨hn₁, hn₂⟩ := (normalizesIff k T.inclusion T.isClosedImmersion _ _).mp hn
  obtain ⟨j, hj⟩ := h n hn₁
  obtain ⟨l, hl⟩ := h n⁻¹ hn₂
  have hcancel : (conjugationIso n⁻¹).hom ≫ e.hom = 𝟙 G := by
    apply Grp.hom_ext
    change conjugate n⁻¹ (𝟙 G.X) ≫ conjugate n (𝟙 G.X) = 𝟙 G.X
    rw [comp_conjugate, Category.comp_id]
    simpa only [inv_inv] using conjugate_inv_cancel n⁻¹ (𝟙 G.X)
  have h₂ : IsSubgroupOf T S := by
    refine ⟨l, ?_⟩
    change l ≫ T.inclusion ≫ e.hom = T.inclusion
    rw [← Category.assoc, hl, Category.assoc, hcancel, Category.comp_id]
  obtain ⟨a, ha⟩ := subgroupIso_of_same (A := S) ⟨⟨j, hj⟩, h₂⟩
  refine ⟨a, ?_⟩
  rw [ha]
  change T.inclusion.hom.hom ≫ conjugate n (𝟙 G.X) = conjugate n T.inclusion.hom.hom
  rw [comp_conjugate, Category.comp_id]

private theorem conjugates_by_subgroup_point (B : ClosedSubgroup G)
    (b : 𝟙_ (SchemeOver k) ⟶ B.group.X) :
    ConjugatesSubgroups (b ≫ B.inclusion.hom.hom) B B := by
  refine ⟨conjugationIso b, ?_⟩
  change conjugate b (𝟙 B.group.X) ≫ B.inclusion.hom.hom =
    conjugate (b ≫ B.inclusion.hom.hom) B.inclusion.hom.hom
  rw [conjugate_comp, Category.id_comp]

private theorem conjugates_baseChange (K : Type u) [Field K] [Algebra k K]
    {B C : ClosedSubgroup G} {n : 𝟙_ (SchemeOver k) ⟶ G.X} (h : ConjugatesSubgroups n B C) :
    ConjugatesSubgroups (scalarExtendedRationalPoint K n) (extendSubgroup K B) (extendSubgroup K C) := by
  obtain ⟨e, he⟩ := h
  let F := baseChange k K
  let Fg := groupBaseChange k K
  letI : GrpObj (F.obj G.X) := (Fg.obj G).grp
  refine ⟨Fg.mapIso e, ?_⟩
  change F.map e.hom.hom.hom ≫ F.map C.inclusion.hom.hom =
    conjugate (G := Fg.obj G) (scalarExtendedRationalPoint K n) (F.map B.inclusion.hom.hom)
  change (e.hom ≫ C.inclusion).hom.hom = conjugate n B.inclusion.hom.hom at he
  rw [← Functor.map_comp, show e.hom.hom.hom ≫ C.inclusion.hom.hom =
    (e.hom ≫ C.inclusion).hom.hom from rfl, he]
  have hc : F.map (toUnit B.group.X ≫ n) =
      toUnit (F.obj B.group.X) ≫ scalarExtendedRationalPoint K n := by
    simp only [Functor.map_comp, scalarExtendedRationalPoint, ← Category.assoc]
    rw [Functor.Monoidal.toUnit_ε F B.group.X]
  simp only [conjugate, F.map_mul, F.map_inv', hc]

private theorem same_conjugate_subgroups {B C D : ClosedSubgroup G}
    {n : 𝟙_ (SchemeOver k) ⟶ G.X} (hC : ConjugatesSubgroups n B C)
    (hD : ConjugatesSubgroups n B D) : SameSubgroup C D := by
  obtain ⟨e, he⟩ := hC
  obtain ⟨f, hf⟩ := hD
  have h : e.hom ≫ C.inclusion = f.hom ≫ D.inclusion := Grp.hom_ext _ _ (he.trans hf.symm)
  exact ⟨⟨e.inv ≫ f.hom, by rw [Category.assoc, ← h, e.inv_hom_id_assoc]⟩,
    ⟨f.inv ≫ e.hom, by rw [Category.assoc, h, f.inv_hom_id_assoc]⟩⟩

/-- Every geometric normalizer point differs from a rational lift of its
constant Weyl class by a point of the extended torus. -/
private theorem normalization_lifts_mod_torus (K : Type u) [Field K] [Algebra k K]
    (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (g : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj A.val).X)
    (hg : Normalizes (extendSubgroup K T).inclusion g) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ A.val.X, Normalizes T.inclusion n ∧
      ∃ t : 𝟙_ (SchemeOver K) ⟶ (extendSubgroup K T).group.X,
        (show 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj A.val).X from
          scalarExtendedRationalPoint K n)⁻¹ * g = t ≫ (extendSubgroup K T).inclusion.hom.hom := by
  obtain ⟨N, j, hj, W, q, hN, hjn, hq, _, _, _, hW⟩ :=
    Reductive.WeylScheme.weylScheme A hA T (lattice_torus_of_split hT) hTm
  obtain ⟨⟨I⟩, hLift⟩ := hW hT
  obtain ⟨_, hN'⟩ := normalizerSchemeBaseChange k K T.inclusion N T.isClosedImmersion hN
  obtain ⟨b₀, hb₀⟩ := (hN' _ _).mp hg
  let F := groupBaseChange k K
  let q' := (F.map q).hom.hom
  let d := (F.map N.inclusion).hom.hom
  let j' := (F.map j).hom.hom
  let b : 𝟙_ (SchemeOver K) ⟶ (F.obj N.group).X := b₀
  letI : IsMonHom q' := inferInstanceAs (IsMonHom (F.map q).hom.hom)
  letI : IsMonHom d := inferInstanceAs (IsMonHom (F.map N.inclusion).hom.hom)
  have hb : b ≫ d = g := hb₀
  have hj' : j' ≫ d = (extendSubgroup K T).inclusion.hom.hom := by
    change (F.map j ≫ F.map N.inclusion).hom.hom = (F.map T.inclusion).hom.hom
    rw [← Functor.map_comp, hjn]
  have hp : IsPullback j' (toUnit _) q' η[(F.obj W.val).X] := baseChangeKernelSquare q j hq.1
  obtain ⟨w, hw⟩ := constant_sections_after_scalar_extension I.constantGroup K (b ≫ q')
  obtain ⟨_, a, ha⟩ := hLift (I.constantGroup.sectionPoint w)
  let n := a ≫ N.inclusion.hom.hom
  let a' : 𝟙_ (SchemeOver K) ⟶ (F.obj N.group).X := scalarExtendedRationalPoint K a
  have hq' : a' ≫ q' = b ≫ q' := by
    change scalarExtendedRationalPoint K a ≫ (baseChange k K).map q.hom.hom = _
    rw [← scalarExtendedPoint_natural, ha, hw]
  have hker : (a'⁻¹ * b) ≫ q' = toUnit _ ≫ η[(F.obj W.val).X] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq', inv_mul_cancel]
    rfl
  refine ⟨n, (hN _ _).mpr ⟨a, rfl⟩, hp.lift _ _ hker, ?_⟩
  let n' : 𝟙_ (SchemeOver K) ⟶ (F.obj A.val).X := scalarExtendedRationalPoint K n
  change n'⁻¹ * g = hp.lift _ _ hker ≫ _
  have hn' : n' = a' ≫ d := scalarExtendedPoint_natural K a N.inclusion.hom.hom
  rw [hn', ← hb, ← GrpObj.inv_comp, ← MonObj.mul_comp, ← hj', ← Category.assoc, hp.lift_fst]

private theorem precomp_pairing {T : GroupScheme k}
    (e : T ≅ T) (χ : Character T) (c : Cocharacter T) :
    pairing T χ (c ≫ e.hom) = pairing T (e.hom ≫ χ) c := by
  apply ((CharacterPairing.characterPairingComposition T χ (c ≫ e.hom)).1 _).mp
  simpa only [Specs.CharacterDescent.compositionPairing, Category.assoc] using
    ((CharacterPairing.characterPairingComposition T (e.hom ≫ χ) c).1 _).mpr rfl

private theorem regular_parabolic_conjugates
    (A : AffineAlgebraicGroup k) {T : ClosedSubgroup A.val}
    (c : Cocharacter T.group) (hc : IsRegular T c) (D : LimitDecomposition (c ≫ T.inclusion))
    (n : 𝟙_ (SchemeOver k) ⟶ A.val.X) (hn : Normalizes T.inclusion n) :
    ∃ (c' : Cocharacter T.group) (E : LimitDecomposition (c' ≫ T.inclusion)),
      IsRegular T c' ∧ ConjugatesSubgroups n D.parabolic E.parabolic := by
  obtain ⟨e, he⟩ := conjugates_by_normalizing_point n hn
  let f := conjugationIso n
  have ht := conjugatesSubgroups_square n e he
  let c' := c ≫ e.hom
  obtain ⟨E⟩ := existsLimitDecomposition A (c' ≫ T.inclusion)
  have hc' : IsRegular T c' := by
    intro α
    rw [show c' = c ≫ e.hom from rfl, precomp_pairing]
    exact hc ⟨_, (rootsOfIso f e ht α.val).mpr α.property⟩
  have hf : (c ≫ T.inclusion) ≫ f.hom = c' ≫ T.inclusion := by
    have ht' : T.inclusion ≫ f.hom = e.hom ≫ T.inclusion := ht
    rw [Category.assoc, ht', ← Category.assoc]
  have hi : (c' ≫ T.inclusion) ≫ f.inv = c ≫ T.inclusion := by
    rw [← hf, Category.assoc, f.hom_inv_id, Category.comp_id]
  obtain ⟨j, hj⟩ := map_parabolic_of_comp A.property.1 f.hom hf D E
  obtain ⟨l, hl⟩ := map_parabolic_of_comp A.property.1 f.inv hi E D
  let S := transportSubgroup f D.parabolic
  have h : SameSubgroup S E.parabolic := ⟨⟨j, hj⟩, ⟨l, by
    change l ≫ D.parabolic.inclusion ≫ f.hom = E.parabolic.inclusion
    calc
      l ≫ D.parabolic.inclusion ≫ f.hom = (l ≫ D.parabolic.inclusion) ≫ f.hom :=
        (Category.assoc l D.parabolic.inclusion f.hom).symm
      _ = (E.parabolic.inclusion ≫ f.inv) ≫ f.hom := congrArg (· ≫ f.hom) hl
      _ = E.parabolic.inclusion := (Category.assoc _ _ _).trans
        ((congrArg (E.parabolic.inclusion ≫ ·) f.inv_hom_id).trans (Category.comp_id _))⟩⟩
  obtain ⟨a, ha⟩ := subgroupIso_of_same h
  refine ⟨c', E, hc', a, ?_⟩
  rw [ha]
  change D.parabolic.inclusion.hom.hom ≫ conjugate n (𝟙 A.val.X) = _
  rw [comp_conjugate, Category.comp_id]
  rfl

private theorem borel_of_regular_cocharacter (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (B : ClosedSubgroup A.val) (hB : IsKBorel B) (hTB : IsSubgroupOf T B) :
    ∃ (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ T.inclusion)),
      IsRegular T c ∧ SameSubgroup B D.parabolic ∧ subgroupRoots T B = positiveRoots T c := by
  obtain ⟨c, hc⟩ := exists_regular_cocharacter A T hT
  obtain ⟨D⟩ := existsLimitDecomposition A (c ≫ T.inclusion)
  have hreg := regularCocharacterBorel A hA T hT hTm c hc D
  let K := AlgebraicClosure k
  let H := GeometricGroup A
  let S := extendSubgroup K T
  let P := extendSubgroup K D.parabolic
  let Q := extendSubgroup K B
  have hS : IsMaximalTorus S := hTm.choose_spec
  have hP : IsBorel P := hreg.2.1.choose_spec
  have hQ : IsBorel Q := hB.choose_spec
  have hSP : IsSubgroupOf S P := extend_subgroupOf hreg.2.2.1
  obtain ⟨g, hg, hconj⟩ := MaximalToriConjugate.normalizerTransitiveOnBorels H
    (smooth_baseChangedGroup hA.1)
    (connected_of_geometricallyConnected (geomConnected_baseChangedGroup hA.2.1))
    S hS P Q hP hQ hSP (extend_subgroupOf hTB)
  obtain ⟨n, hn, t, ht⟩ := normalization_lifts_mod_torus K A hA T hT hTm g hg
  obtain ⟨j, hj⟩ := hSP
  let v := t ≫ j.hom.hom
  let n' : 𝟙_ (SchemeOver K) ⟶ H.val.X := scalarExtendedRationalPoint K n
  have hv : v ≫ P.inclusion.hom.hom = n'⁻¹ * g := by
    rw [show v = t ≫ j.hom.hom from rfl, Category.assoc, ← show
      (j ≫ P.inclusion).hom.hom = j.hom.hom ≫ P.inclusion.hom.hom from rfl, hj, ← ht]
  have hv' : v⁻¹ ≫ P.inclusion.hom.hom = g⁻¹ * n' := by
    rw [GrpObj.inv_comp, hv, mul_inv_rev, inv_inv]
  have hconj' : ConjugatesSubgroups (scalarExtendedRationalPoint K n) P Q := by
    have h := conjugates_trans (conjugates_by_subgroup_point P v⁻¹) hconj
    rwa [hv', ← mul_assoc, mul_inv_cancel, one_mul] at h
  obtain ⟨c', E, hc', hE⟩ := regular_parabolic_conjugates A c hc D n hn
  have hsameK := same_conjugate_subgroups hconj' (conjugates_baseChange K hE)
  have hsame : SameSubgroup B E.parabolic :=
    ⟨subgroupOf_of_extend hsameK.1, subgroupOf_of_extend hsameK.2⟩
  refine ⟨c', E, hc', hsame, ?_⟩
  unfold subgroupRoots
  rw [lieImage_eq_of_same hsame]
  exact subgroupRoots_of_regular A T c' hc' E

open private smooth_of_smooth_after_fieldExtension from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private fieldSpecMap_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem kBorel_smooth_connected (A : AffineAlgebraicGroup k) (B : ClosedSubgroup A.val)
    (hB : IsKBorel B) : Smooth B.group.X.hom ∧ ConnectedSpace B.group.X.left := by
  let K := AlgebraicClosure k
  obtain ⟨_, h⟩ := hB
  letI : Surjective (fieldSpecMap k K) := fieldSpecMap_surjective K
  letI : ConnectedSpace ↥(pullback B.group.X.hom (fieldSpecMap k K)) := h.1.2.1
  let p := pullback.fst B.group.X.hom (fieldSpecMap k K)
  have hp : Surjective p := inferInstanceAs (Surjective (pullback.fst _ _))
  exact ⟨smooth_of_smooth_after_fieldExtension (K := K) B.group.X.hom h.1.1,
    p.surjective.connectedSpace p.continuous⟩

/-- The Borels containing the split torus are classified by their positive systems. -/
theorem borelsThroughT : BorelsThroughT.{u} := by
  intro k _ A hA T hT hTm
  refine ⟨borel_of_regular_cocharacter A hA T hT hTm, fun S => ?_⟩
  constructor
  · intro hS
    obtain ⟨c, hc, hpos⟩ := (positiveSystemsFromCocharacters A hA T hT hTm S).mp hS
    obtain ⟨D⟩ := existsLimitDecomposition A (c ≫ T.inclusion)
    obtain ⟨_, hB, hTB, hroots, _, _⟩ := regularCocharacterBorel A hA T hT hTm c hc D
    refine ⟨D.parabolic, hB, hTB, hroots.trans hpos, fun B' hB' hTB' hroots' => ?_⟩
    obtain ⟨c', E, hc', hsame, hpos'⟩ := borel_of_regular_cocharacter A hA T hT hTm B' hB' hTB'
    obtain ⟨hBs, hBc⟩ := kBorel_smooth_connected A D.parabolic hB
    obtain ⟨hB's, hB'c⟩ := kBorel_smooth_connected A B' hB'
    refine ⟨subgroupOf_trans (subgroupOf_limit_of_rootSigns A hA T D.parabolic hT hTm
      hBs hBc hTB c' E ?_) hsame.2,
      subgroupOf_limit_of_rootSigns A hA T B' hT hTm hB's hB'c hTB' c D ?_⟩
    · intro α hα
      have hp : α ∈ positiveRoots T c' := by rwa [← hpos', hroots', ← hpos, ← hroots]
      exact (show 0 < pairing T.group α.val c' from hp).le
    · intro α hα
      have hp : α ∈ positiveRoots T c := by rwa [hpos, ← hroots']
      exact (show 0 < pairing T.group α.val c from hp).le
  · rintro ⟨B, hB, hTB, hBS, _⟩
    obtain ⟨c, D, hc, _, hpos⟩ := borel_of_regular_cocharacter A hA T hT hTm B hB hTB
    exact (positiveSystemsFromCocharacters A hA T hT hTm S).mpr ⟨c, hc, hpos.symm.trans hBS⟩


end

end LinearAlgebraicGroups.RootData.BorelsAndChambers
