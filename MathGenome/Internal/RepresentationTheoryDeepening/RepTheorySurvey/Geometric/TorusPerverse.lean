import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusPerverse
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusStages
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SheafModels
import Mathlib.Analysis.Complex.Convex
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite
open scoped BigOperators Classical Topology

namespace RepTheorySurvey.Geometric.TorusPerverse

open Analytic BoundedLatticeSpecs LatticeModelSpecs TorusStageSpecs TorusPerverseSpecs

private theorem stageGeometry (points : TorusPoints) (r : ℕ) : StageGeometry r := by
  obtain ⟨_, _, _, _, _, hex, hd, _, _⟩ := points r
  refine ⟨hd, ?_⟩
  intro x
  obtain ⟨n, B, hB⟩ := hex x
  refine ⟨n, ?_⟩
  change (show TorusLattice r from x) ∈ stageSet r n
  rw [← hB]
  exact fun i ↦ (B i).property

private theorem positiveLoopAction (points : TorusPoints) (r : ℕ) (g : StageGeometry r)
    (c : ContinuousJets r) : IsPositiveLoopAction r g c := by
  obtain ⟨_, _, _, _, _, _, _, _, hfix⟩ := points r
  intro n k u x
  let v : PositiveTorus r := ⟨positiveTorusMap r u, ⟨u, rfl⟩⟩
  exact (hfix v x.val).symm

private theorem monomialPoint_bijective (r : ℕ) : Function.Bijective (monomialPoint r) := by
  obtain ⟨e, _, he, _⟩ := TorusStages.torusPoints r
  have he' : (e : Coweight r → torusSpace r) = monomialPoint r := funext he
  rw [← he']
  exact e.bijective

private theorem stageSet_finite (r n : ℕ) : (stageSet r n).Finite := by
  obtain ⟨e, _, hf, _⟩ := TorusStages.boundedTorusPoints r
  have : Finite (BoundedCoweight r n) := (hf n).1
  have : Finite (BoundedTorus r n) := Finite.of_equiv _ (e n)
  have he : Set.range (forgetTorusBound (r := r) (N := n)) = stageSet r n := by
    ext L
    exact ⟨fun ⟨B, hB⟩ ↦ hB ▸ fun i ↦ (B i).property,
      fun h ↦ ⟨fun i ↦ ⟨L i, h i⟩, rfl⟩⟩
  rw [← he]
  exact Set.finite_range _

private def jetRepresentative {n : ℕ} (a : JetRing n) : O :=
  PowerSeries.mk fun m ↦ if h : m < n then jetCoefficients n a ⟨m, h⟩ else 0

private theorem reduce_jetRepresentative {n : ℕ} (a : JetRing n) :
    jetReduction n (jetRepresentative a) = a := by
  apply (jetCoefficients n).injective
  funext j
  simp [jetRepresentative, j.isLt]

private theorem jetConstant_ne_zero {n : ℕ} (hn : 0 < n) (a : (JetRing n)ˣ) :
    PowerSeries.constantCoeff (jetRepresentative a.val) ≠ 0 := by
  let constant : JetRing n →+* ℂ :=
    Ideal.Quotient.lift _ PowerSeries.constantCoeff (by
      have hker : jetIdeal n ≤ RingHom.ker (PowerSeries.constantCoeff (R := ℂ)) := by
        apply Ideal.span_le.mpr
        rintro f (rfl : f = t ^ n)
        rw [SetLike.mem_coe, RingHom.mem_ker]
        simp [t, zero_pow hn.ne']
      exact fun f hf ↦ RingHom.mem_ker.mp (hker hf))
  have h := (a.isUnit.map constant).ne_zero
  rw [← reduce_jetRepresentative a.val] at h
  exact h

private theorem jet_isUnit_of_coeff_ne_zero {k : ℕ} {a : JetRing (k + 1)}
    (h : jetCoefficients (k + 1) a 0 ≠ 0) : IsUnit a := by
  rw [← reduce_jetRepresentative a]
  apply IsUnit.map (jetReduction (k + 1))
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  exact isUnit_iff_ne_zero.mpr (by
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, jetRepresentative] using h)

private theorem unitJet_coeff_ne_zero {k : ℕ} (a : (JetRing (k + 1))ˣ) :
    jetCoefficients (k + 1) a.val 0 ≠ 0 := by
  simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, jetRepresentative] using
    jetConstant_ne_zero (Nat.succ_pos k) a

private theorem continuous_jetCoefficient {r k : ℕ} (i : Fin r) (j : Fin (k + 1)) :
    Continuous (fun a : PositiveJet r k ↦ jetCoefficients (k + 1) (a i).val j) := by
  have hv : Continuous (fun a : PositiveJet r k ↦ fun i : Fin r ↦ (a i).val) :=
    continuous_induced_dom
  have hc : Continuous (jetCoefficients (k + 1) : JetRing (k + 1) → Fin (k + 1) → ℂ) :=
    continuous_induced_dom
  exact (continuous_apply j).comp (hc.comp ((continuous_apply i).comp hv))

private theorem continuous_into_jet_iff {A : Type*} [TopologicalSpace A] {r k : ℕ}
    (f : A → PositiveJet r k) :
    Continuous f ↔ ∀ i : Fin r, ∀ j : Fin (k + 1),
      Continuous (fun x ↦ jetCoefficients (k + 1) (f x i).val j) := by
  constructor
  · intro hf i j
    exact (continuous_jetCoefficient i j).comp hf
  · intro hf
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    apply continuous_induced_rng.mpr
    exact continuous_pi (hf i)

private def jetCoordinatesHomeomorph (r k : ℕ) : PositiveJet r k ≃ₜ JetCoordinates r k where
  toFun a :=
    (fun i ↦ ⟨jetCoefficients (k + 1) (a i).val 0, unitJet_coeff_ne_zero (a i)⟩,
      fun i j ↦ jetCoefficients (k + 1) (a i).val j.succ)
  invFun z i := (jet_isUnit_of_coeff_ne_zero
    (a := (jetCoefficients (k + 1)).symm (Fin.cons (z.1 i).val (z.2 i)))
    (by simpa using (z.1 i).property)).unit
  left_inv a := by
    funext i
    apply Units.ext
    change (jetCoefficients (k + 1)).symm _ = (a i).val
    apply (jetCoefficients (k + 1)).injective
    rw [LinearEquiv.apply_symm_apply]
    funext j
    refine Fin.cases ?_ (fun j' ↦ ?_) j <;> simp
  right_inv z := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      change jetCoefficients (k + 1) ((jetCoefficients (k + 1)).symm
        (Fin.cons (z.1 i).val (z.2 i))) 0 = (z.1 i).val
      rw [LinearEquiv.apply_symm_apply, Fin.cons_zero]
    · funext i j
      change jetCoefficients (k + 1) ((jetCoefficients (k + 1)).symm
        (Fin.cons (z.1 i).val (z.2 i))) j.succ = z.2 i j
      rw [LinearEquiv.apply_symm_apply, Fin.cons_succ]
  continuous_toFun :=
    (continuous_pi fun i ↦ (continuous_jetCoefficient (k := k) i 0).subtype_mk
      (fun a ↦ unitJet_coeff_ne_zero (a i))).prodMk
      (continuous_pi fun i ↦ continuous_pi fun (j : Fin k) ↦
        continuous_jetCoefficient (k := k) i j.succ)
  continuous_invFun := by
    apply (continuous_into_jet_iff _).mpr
    intro i j
    change Continuous (fun z : JetCoordinates r k ↦
      jetCoefficients (k + 1) ((jetCoefficients (k + 1)).symm
        (Fin.cons (z.1 i).val (z.2 i))) j)
    simp only [LinearEquiv.apply_symm_apply]
    refine Fin.cases ?_ (fun j' ↦ ?_) j
    · simpa only [Fin.cons_zero, Function.comp_def] using
        (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst))
    · simpa only [Fin.cons_succ, Function.comp_def] using
        ((continuous_apply j').comp ((continuous_apply i).comp continuous_snd))

private theorem jet_coordinates (r k : ℕ) :
    HasJetCoordinates r k ∧ @ConnectedSpace (PositiveJet r k) (positiveJetTopology r k) := by
  have : PathConnectedSpace {z : ℂ // z ≠ 0} :=
    (unitsHomeomorphNeZero (G₀ := ℂ)).surjective.pathConnectedSpace
      (unitsHomeomorphNeZero (G₀ := ℂ)).continuous
  let e := jetCoordinatesHomeomorph r k
  exact ⟨⟨e, fun _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩,
    e.symm.surjective.connectedSpace e.symm.continuous⟩

private theorem continuous_representative_coeff {r k : ℕ} (i : Fin r) (m : ℕ) :
    Continuous (fun a : PositiveJet r k ↦ PowerSeries.coeff m (jetRepresentative (a i).val)) := by
  by_cases h : m < k + 1
  · simpa only [jetRepresentative, PowerSeries.coeff_mk, dite_eq_left h] using
      continuous_jetCoefficient (k := k) i ⟨m, h⟩
  · simp only [jetRepresentative, PowerSeries.coeff_mk, dite_eq_right h]
    exact continuous_const

private theorem continuous_representative_inv_coeff {r k : ℕ} (i : Fin r) (m : ℕ) :
    Continuous (fun a : PositiveJet r k ↦ PowerSeries.coeff m (jetRepresentative (a i).val)⁻¹) := by
  let p : PositiveJet r k → O := fun a ↦ jetRepresentative (a i).val
  have hc : Continuous (fun a ↦ PowerSeries.constantCoeff (p a)) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact continuous_representative_coeff (k := k) i 0
  have invConstant : Continuous (fun a ↦ (PowerSeries.constantCoeff (p a))⁻¹) :=
    hc.inv₀ fun a ↦ jetConstant_ne_zero (Nat.succ_pos k) (a i)
  change Continuous (fun a ↦ PowerSeries.coeff m (p a)⁻¹)
  induction m using Nat.strong_induction_on with
  | h m ih =>
    simp only [PowerSeries.coeff_inv m]
    by_cases hm : m = 0
    · simpa only [ite_eq_left hm] using invConstant
    · simp only [ite_eq_right hm]
      apply invConstant.neg.mul
      apply continuous_finsetSum
      intro x _
      by_cases hx : x.2 < m
      · simp only [ite_eq_left hx]
        exact (continuous_representative_coeff (k := k) i x.1).mul (ih _ hx)
      · simp only [ite_eq_right hx]
        exact continuous_const

private theorem jetUnit_inv_val {k : ℕ} (a : (JetRing (k + 1))ˣ) :
    a.inv = jetReduction (k + 1) (jetRepresentative a.val)⁻¹ := by
  have h := congrArg (jetReduction (k + 1))
    (PowerSeries.mul_inv_cancel _ (jetConstant_ne_zero (Nat.succ_pos k) a))
  rw [map_mul, map_one, reduce_jetRepresentative] at h
  calc
    a.inv = a.inv * 1 := (mul_one _).symm
    _ = _ := by
      rw [← h, ← mul_assoc]
      change ((↑a⁻¹ : JetRing (k + 1)) * ↑a) * _ = _
      rw [Units.inv_mul, one_mul]

private theorem continuousJets (r : ℕ) : ContinuousJets r where
  topologicalGroup k := by
    refine @IsTopologicalGroup.mk (PositiveJet r k) (positiveJetTopology r k) _ ⟨?_⟩ ⟨?_⟩
    · apply (continuous_into_jet_iff _).mpr
      intro i j
      have h (p : PositiveJet r k × PositiveJet r k) :
          jetCoefficients (k + 1) ((p.1 * p.2) i).val j =
            PowerSeries.coeff j.val
              (jetRepresentative (p.1 i).val * jetRepresentative (p.2 i).val) := by
        rw [← jetCoefficients_reduce, map_mul, reduce_jetRepresentative, reduce_jetRepresentative]
        rfl
      simp only [h, PowerSeries.coeff_mul]
      exact continuous_finsetSum _ fun a _ ↦
        ((continuous_representative_coeff i a.1).comp continuous_fst).mul
          ((continuous_representative_coeff i a.2).comp continuous_snd)
    · apply (continuous_into_jet_iff _).mpr
      intro i j
      change Continuous (fun p : PositiveJet r k ↦ jetCoefficients (k + 1) (p i).inv j)
      simp only [jetUnit_inv_val, jetCoefficients_reduce]
      exact continuous_representative_inv_coeff i j.val
  truncation {k l} h := by
    apply (continuous_into_jet_iff _).mpr
    intro i j
    have h' (a : PositiveJet r l) :
        jetCoefficients (k + 1) (jetTruncation h a i).val j =
          jetCoefficients (l + 1) (a i).val (Fin.castLE (Nat.succ_le_succ h) j) := by
      change jetCoefficients (k + 1) (truncateJet (Nat.succ_le_succ h) (a i).val) j = _
      rw [← reduce_jetRepresentative (a i).val]
      rfl
    simpa only [h'] using continuous_jetCoefficient (k := l) i
      (Fin.castLE (Nat.succ_le_succ h) j)

open private trivialJetAction trivialStageActions from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusPerverse

private theorem pullbackMorphism_id {W Y X : TopCat.{0}} (k : W ⟶ Y)
    (f : Y ⟶ X) (F : Derived X) {f' : W ⟶ X} (hf : k ≫ f = f') :
    pullbackMorphism k hf hf (𝟙 ((derivedInverseImage f).obj F)) = 𝟙 _ := by
  subst f'
  simp [pullbackMorphism]

private def identityEquivariance (H : AnalyticGroup.{0}) (X : TopCat.{0}) (F : Derived X) :
    (trivialAction H X).Equivariance F where
  iso := Iso.refl _
  identity := pullbackMorphism_id _ _ _ _
  multiplication := by
    let A := trivialAction H X
    let p := AnalyticAction.projection H X
    have e₁ := pullbackMorphism_id (AnalyticAction.multiplyParameters H X) p F rfl
    have e₂ := pullbackMorphism_id A.firstAfterSecond p F (AnalyticAction.multiply_act A)
    have e₃ := pullbackMorphism_id (AnalyticAction.secondParameter H X) p F
      (AnalyticAction.multiply_projection (H := H) (X := X))
    exact e₁.trans ((congrArg₂ CategoryStruct.comp e₂ e₃).trans (Category.id_comp _)).symm

private def identityJetEquivariance (J : JetSystem.{0}) (X : TopCat.{0}) (F : Derived X) :
    (trivialJetAction J X).Equivariance F where
  datum k _ := identityEquivariance (J.group k) X F
  compatibility _hk _h := pullbackMorphism_id _ _ _ _

private def identityStageEquivariance {X : TopCat.{0}} (J : JetSystem.{0})
    (A : ClosedStages X) (F : Derived X) :
    (trivialStageActions J A).Equivariance F where
  datum n := identityJetEquivariance J (A.space n) ((derivedInverseImage (A.inclusion n)).obj F)
  compatibility := by
    intro n m k h hn hm
    let G := (derivedInverseImage (A.inclusion m)).obj F
    let p := AnalyticAction.projection (J.group k) (A.space n)
    let q := AnalyticAction.projection (J.group k) (A.space m)
    let t := A.transition h
    let v := J.parameterMap (le_refl k) t
    have hv : v ≫ q = p ≫ t := TopCat.ext (fun _ ↦ rfl)
    let d := derivedInverseImage p
    let e := (derivedInverseImageComposition p t).app G
    let c := StageJetActions.restrictionComparison (A := A) F h
    change d.map c.hom ≫ e.inv ≫ pullbackMorphism v hv hv (𝟙 ((derivedInverseImage q).obj G)) ≫
      e.hom ≫ d.map c.inv = 𝟙 _
    rw [pullbackMorphism_id v q G hv, Category.id_comp, Iso.inv_hom_id_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]

private def singletonOpen {X : TopCat.{0}} [DiscreteTopology X] (x : X) : Opens X :=
  ⟨{x}, isOpen_discrete _⟩

private theorem germ_minimal_isIso {X : TopCat.{0}} (F : Sheaves X) (x : X)
    (U : Opens X) (hx : x ∈ U) (hU : ∀ V : Opens X, x ∈ V → U ≤ V) :
    IsIso (F.presheaf.germ U x hx) := by
  let N : OpenNhds x := ⟨U, hx⟩
  have h : IsTerminal (op N) :=
    IsTerminal.ofUniqueHom (fun V ↦ (homOfLE
      (show N ≤ V.unop from hU _ V.unop.property)).op) (fun _ _ ↦ Subsingleton.elim _ _)
  exact (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F.obj)).isIso_ι_app_of_isTerminal (op N) h

private theorem germ_singleton_isIso {X : TopCat.{0}} [DiscreteTopology X] (F : Sheaves X)
    (x : X) : IsIso (F.presheaf.germ (singletonOpen x) x (Set.mem_singleton x)) :=
  germ_minimal_isIso F x _ _ (fun _ h ↦ Set.singleton_subset_iff.mpr h)

private def singletonSectionsIso {X : TopCat.{0}} [DiscreteTopology X] (x : X) :
    sectionsOn (singletonOpen x) ≅ stalk x :=
  NatIso.ofComponents
    (fun F ↦ by
      letI : IsIso (F.presheaf.germ (singletonOpen x) x (Set.mem_singleton x)) :=
        germ_singleton_isIso F x
      change F.presheaf.obj (op (singletonOpen x)) ≅ F.presheaf.stalk x
      exact @asIso _ _ _ _ _ (germ_singleton_isIso F x))
    (fun f ↦ (TopCat.Presheaf.stalkFunctor_map_germ (singletonOpen x) x
      (Set.mem_singleton x) f.1).symm)

private theorem sheaf_hom_ext_stalk {X : TopCat.{0}} {F G : Sheaves X} {f g : F ⟶ G}
    (h : ∀ x : X, (stalk x).map f = (stalk x).map g) : f = g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  ext s
  apply TopCat.Presheaf.section_ext G U.unop
  intro x hx
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hx f.1,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hx g.1]
  exact congrArg (fun u : (stalk x).obj F ⟶ (stalk x).obj G ↦
    u (F.presheaf.germ U.unop x hx s)) (h x)

private lemma sectionsOn_preserves_product {I : Type} {X : TopCat.{0}} (U : Opens X)
    (F : I → Sheaves X) : PreservesLimit (Discrete.functor F) (sectionsOn U) := by
  change PreservesLimit (Discrete.functor F)
    (sheafToPresheaf (Opens.grothendieckTopology X) Coeff.{0} ⋙
      (evaluation (Opens X)ᵒᵖ Coeff.{0}).obj (op U))
  let R := sheafToPresheaf (Opens.grothendieckTopology X) Coeff.{0}
  let ev := (evaluation (Opens X)ᵒᵖ Coeff.{0}).obj (op U)
  let adj := sheafificationAdjunction (Opens.grothendieckTopology X) Coeff.{0}
  let hR : PreservesLimitsOfSize.{0, 0} R := adj.rightAdjoint_preservesLimits
  have hshape : PreservesLimitsOfShape (Discrete I) R := hR.preservesLimitsOfShape
  have : PreservesLimit (Discrete.functor F) R := hshape.preservesLimit
  have : PreservesLimit (Discrete.functor F ⋙ R) ev :=
    evaluation_preservesLimitsOfShape (J := Discrete I) (op U) |>.preservesLimit
  exact comp_preservesLimit (K := Discrete.functor F) R ev

private theorem stalk_product_isZero {I : Type} {X : TopCat.{0}} [DiscreteTopology X]
    (x : X) (F : I → Sheaves X) (h : ∀ i, IsZero ((stalk x).obj (F i))) :
    IsZero ((stalk x).obj (∏ᶜ F)) := by
  let ev := sectionsOn (singletonOpen x)
  have := sectionsOn_preserves_product (singletonOpen x) F
  let e := (PreservesProduct.iso ev F).symm ≪≫ (singletonSectionsIso x).app (∏ᶜ F)
  refine (IsZero.of_iso ?_ e.symm)
  rw [IsZero.iff_id_eq_zero]
  apply Pi.hom_ext
  intro i
  rw [Category.id_comp, zero_comp]
  exact ((h i).of_iso ((singletonSectionsIso x).app (F i))).eq_of_tgt _ _

private theorem skyscraperStalk_isZero_of_ne {X : TopCat.{0}} [DiscreteTopology X]
    {x y : X} (h : y ≠ x) (A : Coeff.{0}) :
    IsZero ((stalk x).obj (skyscraperSheaf y A)) := by
  let U := singletonOpen x
  let e := (singletonSectionsIso x).app (skyscraperSheaf y A)
  let ht := isTerminalSkyscraperSheafObjObjOfNotMem (A := A) (U := op U)
    (show y ∉ U from h)
  exact (isZero_zero Coeff.{0}).of_iso
    (e.symm ≪≫ ht.uniqueUpToIso (isZero_zero Coeff.{0}).isTerminal)

private theorem skyscraperProduct_supported (r : ℕ) (g : StageGeometry r) (V : Families r) :
    SupportedOn (monomialPoint r '' familySupport V) ((skyscraperProduct r).obj V) := by
  let X := torusSpace r
  have : DiscreteTopology X := g.discrete
  intro x hx
  apply stalk_product_isZero (X := X) x
  intro w
  by_cases hw : monomialPoint r w = x
  · have hz : IsZero (V.obj (Discrete.mk w)) := by
      by_contra h
      exact hx ⟨w, h, hw⟩
    let T := skyscraperSheafFunctor (X := X) (C := Coeff.{0}) (monomialPoint r w)
    have hT : IsZero (T.obj (V.obj (Discrete.mk w))) := by
      let ht := hz.isTerminal.isTerminalObj T _
      exact (isZero_zero (Sheaves X)).of_iso
        (ht.uniqueUpToIso (isZero_zero (Sheaves X)).isTerminal)
    exact (stalk x).map_isZero hT
  · exact skyscraperStalk_isZero_of_ne hw _

private theorem supportedExtension (r : ℕ) (g : StageGeometry r) (V : Graded r) :
    SupportedExtension r V := by
  have : DiscreteTopology (torusSpace r) := g.discrete
  exact closedInverseDirectUnit_isIso (isClosed_discrete _) _
    (skyscraperProduct_supported r g V.obj)

private def exactDerivedCohomologyIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ D) [PreservesFiniteLimits P] [PreservesFiniteColimits P] [P.Additive]
    (F : DerivedCategory C) (n : ℤ) :
    (DerivedCategory.homologyFunctor D n).obj (P.mapDerivedCategory.obj F) ≅
      P.obj ((DerivedCategory.homologyFunctor C n).obj F) := by
  let K := (DerivedCategory.Q (C := C)).objPreimage F
  let e : DerivedCategory.Q.obj K ≅ F := DerivedCategory.Q.objObjPreimageIso F
  let d := P.mapDerivedCategory.mapIso e.symm ≪≫ P.mapDerivedCategoryFactors.app K
  exact (DerivedCategory.homologyFunctor D n).mapIso d ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app _ ≪≫
    (K.sc n).mapHomologyIso P ≪≫
    P.mapIso ((DerivedCategory.homologyFunctorFactors C n).app K).symm ≪≫
    P.mapIso ((DerivedCategory.homologyFunctor C n).mapIso e)

private def degreeZeroIso {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : DerivedCategory C) (h : ∀ n : ℤ, n ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor C n).obj F)) :
    (DerivedCategory.singleFunctor C 0).obj ((DerivedCategory.homologyFunctor C 0).obj F) ≅ F := by
  letI : F.IsGE 0 := (DerivedCategory.isGE_iff F 0).mpr (fun i hi ↦ h i (ne_of_lt hi))
  letI : F.IsLE 0 := (DerivedCategory.isLE_iff F 0).mpr (fun i hi ↦ h i (ne_of_gt hi))
  let ex := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE F 0
  let V := Classical.choose ex
  let e := (Classical.choose_spec ex).some
  let h₀ := (DerivedCategory.homologyFunctor C 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app V
  exact (DerivedCategory.singleFunctor C 0).mapIso h₀ ≪≫ e.symm

private theorem productProjection_isIso {I C : Type*} [Category C]
    (F : I → C) [HasProduct F] (i : I) (h : ∀ j, j ≠ i → IsTerminal (F j)) :
    IsIso (Pi.π F i) := by
  classical
  let v (j : I) : F i ⟶ F j :=
    if hij : j = i then eqToHom (congrArg F hij.symm) else (h j hij).from _
  have hi : v i = 𝟙 _ := by simp [v]
  refine ⟨⟨Pi.lift v, ?_, ?_⟩⟩
  · apply Pi.hom_ext
    intro j
    by_cases hj : j = i
    · subst j
      simp [hi]
    · exact (h j hj).hom_ext _ _
  · rwa [Pi.lift_comp_π]

private abbrev gradedSkyscraper (r : ℕ) (V : Families r) (w : Coweight r) :
    Sheaves (torusSpace r) :=
  (skyscraperSheafFunctor (monomialPoint r w)).obj (V.obj (Discrete.mk w))

private theorem skyscraperProduct_stalkProjection_isIso (r : ℕ) (g : StageGeometry r)
    (hinj : Function.Injective (monomialPoint r)) (V : Families r) (w : Coweight r) :
    IsIso ((stalk (monomialPoint r w)).map (Pi.π (gradedSkyscraper r V) w)) := by
  let X := torusSpace r
  have : DiscreteTopology X := g.discrete
  let x : X := monomialPoint r w
  let U := singletonOpen x
  let ev := sectionsOn U
  let Fs := gradedSkyscraper r V
  have := sectionsOn_preserves_product U Fs
  let C := PreservesProduct.iso ev Fs
  have projection_isIso : IsIso (Pi.π (fun j ↦ ev.obj (Fs j)) w) := by
    apply productProjection_isIso
    intro j hj
    exact isTerminalSkyscraperSheafObjObjOfNotMem (U := op U)
      (show monomialPoint r j ∉ U from fun h ↦ hj (hinj h))
  have eq : C.hom ≫ Pi.π (fun j ↦ ev.obj (Fs j)) w = ev.map (Pi.π Fs w) :=
    piComparison_comp_π ev Fs w
  have : IsIso (ev.map (Pi.π Fs w)) := by
    rw [← eq]
    infer_instance
  exact (NatIso.isIso_map_iff (singletonSectionsIso x) (Pi.π Fs w)).mp this

private def sheafStalkFamilies (r : ℕ) : Sheaves (torusSpace r) ⥤ Families r where
  obj F := Discrete.functor fun w ↦ (stalk (monomialPoint r w)).obj F
  map v := Discrete.natTrans fun w ↦ (stalk (monomialPoint r w.as)).map v
  map_id F := by
    apply NatTrans.ext
    funext w
    exact (stalk (monomialPoint r w.as)).map_id F
  map_comp f h := by
    apply NatTrans.ext
    funext w
    exact (stalk (monomialPoint r w.as)).map_comp f h

set_option backward.isDefEq.respectTransparency false in
private def stalkProductUnit (r : ℕ) :
    𝟭 (Sheaves (torusSpace r)) ⟶ sheafStalkFamilies r ⋙ skyscraperProduct r where
  app F := Pi.lift fun w ↦ (stalkSkyscraperSheafAdjunction (monomialPoint r w)).unit.app F
  naturality F G f := by
    apply Pi.hom_ext
    intro w
    let a := stalkSkyscraperSheafAdjunction (C := Coeff.{0}) (monomialPoint r w)
    let uF (j : Coweight r) : F ⟶ gradedSkyscraper r ((sheafStalkFamilies r).obj F) j :=
      (stalkSkyscraperSheafAdjunction (monomialPoint r j)).unit.app F
    let uG (j : Coweight r) : G ⟶ gradedSkyscraper r ((sheafStalkFamilies r).obj G) j :=
      (stalkSkyscraperSheafAdjunction (monomialPoint r j)).unit.app G
    change (f ≫ Pi.lift uG) ≫ Pi.π _ w =
      (Pi.lift uF ≫ CategoryTheory.Limits.Pi.map _) ≫ Pi.π _ w
    simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, Pi.map_π]
    exact a.unit.naturality f

set_option backward.isDefEq.respectTransparency false in
private def stalkProductCounit (r : ℕ) :
    skyscraperProduct r ⋙ sheafStalkFamilies r ⟶ 𝟭 (Families r) where
  app V := Discrete.natTrans fun w ↦
    (stalk (monomialPoint r w.as)).map (Pi.π (gradedSkyscraper r V) w.as) ≫
      (stalkSkyscraperSheafAdjunction (monomialPoint r w.as)).counit.app (V.obj w)
  naturality V W f := by
    apply NatTrans.ext
    funext w
    let S := stalk (monomialPoint r w.as)
    let T := skyscraperSheafFunctor (C := Coeff.{0}) (monomialPoint r w.as)
    let a : S ⊣ T := stalkSkyscraperSheafAdjunction (monomialPoint r w.as)
    change S.map ((skyscraperProduct r).map f) ≫ S.map (Pi.π (gradedSkyscraper r W) w.as) ≫
      a.counit.app (W.obj w) =
      (S.map (Pi.π (gradedSkyscraper r V) w.as) ≫ a.counit.app (V.obj w)) ≫ f.app w
    change S.map (CategoryTheory.Limits.Pi.map _) ≫ S.map (Pi.π (gradedSkyscraper r W) w.as) ≫
      _ = _
    erw [← S.map_comp_assoc]
    erw [Pi.map_π, S.map_comp, Category.assoc, Category.assoc]
    exact congrArg (S.map (Pi.π (gradedSkyscraper r V) w.as) ≫ ·) (a.counit.naturality (f.app w))

private theorem skyscraper_counit_isIso {X : TopCat.{0}} (x : X) (V : Coeff.{0}) :
    IsIso ((stalkSkyscraperSheafAdjunction x).counit.app V) :=
  (skyscraperPresheafStalkOfSpecializes x V specializes_rfl).isIso_hom

set_option backward.isDefEq.respectTransparency false in
private theorem stalkProductCounit_isIso (r : ℕ) (g : StageGeometry r)
    (hinj : Function.Injective (monomialPoint r)) : IsIso (stalkProductCounit r) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro V
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro w
  change IsIso ((stalk (monomialPoint r w.as)).map (Pi.π (gradedSkyscraper r V) w.as) ≫
      (stalkSkyscraperSheafAdjunction (monomialPoint r w.as)).counit.app (V.obj w))
  have := skyscraperProduct_stalkProjection_isIso r g hinj V w.as
  have := skyscraper_counit_isIso (monomialPoint r w.as) (V.obj w)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem stalkProductUnit_isIso (r : ℕ) (g : StageGeometry r)
    (hbij : Function.Bijective (monomialPoint r)) : IsIso (stalkProductUnit r) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro F
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  obtain ⟨w, rfl⟩ := hbij.surjective x
  let a := stalkSkyscraperSheafAdjunction (C := Coeff.{0}) (monomialPoint r w)
  let S := stalk (monomialPoint r w)
  let t := Pi.π (gradedSkyscraper r ((sheafStalkFamilies r).obj F)) w
  let v : F ⟶ ∏ᶜ gradedSkyscraper r ((sheafStalkFamilies r).obj F) :=
    (stalkProductUnit r).app F
  change IsIso (S.map v)
  have hp : v ≫ t = a.unit.app F := Pi.lift_comp_π _ w
  have ht : S.map v ≫ (S.map t ≫ a.counit.app (S.obj F)) = 𝟙 _ := by
    erw [← S.map_comp_assoc, hp]
    exact a.left_triangle_components F
  have : IsIso (S.map t) :=
    skyscraperProduct_stalkProjection_isIso r g hbij.injective ((sheafStalkFamilies r).obj F) w
  have := skyscraper_counit_isIso (monomialPoint r w) (S.obj F)
  have : IsIso (S.map v ≫ (S.map t ≫ a.counit.app (S.obj F))) := by rw [ht]; infer_instance
  exact IsIso.of_isIso_comp_right _ (S.map t ≫ a.counit.app (S.obj F))

private def sheafFamiliesEquiv (r : ℕ) (g : StageGeometry r)
    (hbij : Function.Bijective (monomialPoint r)) : Sheaves (torusSpace r) ≌ Families r :=
  letI := stalkProductUnit_isIso r g hbij
  letI := stalkProductCounit_isIso r g hbij.injective
  CategoryTheory.Equivalence.mk (sheafStalkFamilies r) (skyscraperProduct r) (asIso (stalkProductUnit r))
    (asIso (stalkProductCounit r))

private theorem openComplementStalk_isZero {X : TopCat.{0}} [DiscreteTopology X]
    {Z : Set X} (hZ : IsClosed Z) (x : Z)
    (F : Sheaves (TopCat.of (complementOpen Z hZ))) :
    IsZero ((stalk (X := X) x.val).obj
      ((directImage (openInclusion (complementOpen Z hZ))).obj F)) := by
  let U := singletonOpen (X := X) x.val
  let j := openInclusion (complementOpen Z hZ)
  let G := (directImage j).obj F
  have hU : (Opens.map j).obj U = ⊥ := by
    ext z
    change (z.val = x.val) ↔ False
    exact ⟨fun e ↦ z.property (e ▸ x.property), False.elim⟩
  let e := (singletonSectionsIso (X := X) x.val).app G
  exact (isZero_zero Coeff.{0}).of_iso
    (e.symm ≪≫ (F.isTerminalOfEqEmpty hU).uniqueUpToIso (isZero_zero Coeff.{0}).isTerminal)

set_option backward.isDefEq.respectTransparency false in
private def extraordinaryIsoInverseImage {X : TopCat.{0}} [DiscreteTopology X]
    {Z : Set X} (hZ : IsClosed Z) :
    extraordinaryInverseImage hZ ≅ inverseImage (closedInclusion (X := X) Z) := by
  let P := inverseImage (closedInclusion (X := X) Z)
  let η : extraordinaryInverseImage hZ ⟶ P :=
    Functor.whiskerRight (sectionsWithSupportInclusion hZ) P ≫ (Functor.leftUnitor P).hom
  letI : ∀ F, IsIso (η.app F) := by
    intro F
    let j := openInclusion (complementOpen Z hZ)
    let a := inverseDirectAdjunction j
    let v := a.unit.app F
    let G := (directImage j).obj ((inverseImage j).obj F)
    have hG : IsZero (P.obj G) := by
      apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
      intro x
      exact (openComplementStalk_isZero hZ x ((inverseImage j).obj F)).of_iso
        (inverseImageStalkIso (closedInclusion Z) G x).symm
    have hz : P.map v = 0 := hG.eq_of_tgt _ _
    let e := PreservesKernel.iso P v
    change IsIso (P.map (kernel.ι v))
    have he : e.hom ≫ kernel.ι (P.map v) = P.map (kernel.ι v) := by
      rw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rw [← he]
    have := kernel.ι_of_zero hz
    infer_instance
  exact @asIso _ _ _ _ η (NatIso.isIso_of_isIso_app η)

private def rightDerivedPlusIso {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {P Q : C ⥤ D} [P.Additive] [Q.Additive] (e : P ≅ Q) :
    P.rightDerivedFunctorPlus ≅ Q.rightDerivedFunctorPlus where
  hom := e.hom.rightDerivedFunctorPlus
  inv := e.inv.rightDerivedFunctorPlus
  hom_inv_id := by rw [← NatTrans.rightDerivedFunctorPlus_comp, e.hom_inv_id,
    NatTrans.rightDerivedFunctorPlus_id]
  inv_hom_id := by rw [← NatTrans.rightDerivedFunctorPlus_comp, e.inv_hom_id,
    NatTrans.rightDerivedFunctorPlus_id]

private def rightDerivedPlusCohomologicalIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (F : DerivedCategory.Plus C) :
    (DerivedCategory.Plus.ι (C := D)).obj (P.rightDerivedFunctorPlus.obj F) ≅
      P.mapDerivedCategory.obj F.obj := by
  let n := Classical.choose F.property
  letI : F.IsGE n := (F.isGE_ι_obj_iff n).mp (Classical.choose_spec F.property)
  let ex := DerivedCategory.Plus.exists_injective_nonempty_iso F n
  let K := Classical.choose ex
  let L := (InjectiveObject.ι C).mapCochainComplexPlus.obj K
  have he := Classical.choose_spec ex
  let e : DerivedCategory.Plus.Q.obj L ≅ F := (Classical.choose_spec he).some
  let u := P.rightDerivedFunctorPlusUnit.app L
  letI : IsIso u := inferInstanceAs (IsIso (P.rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι C).mapCochainComplexPlus.obj K)))
  let I := DerivedCategory.Plus.ι (C := D)
  let e₁ := (P.rightDerivedFunctorPlus ⋙ I).mapIso e.symm
  let e₂ := I.mapIso (asIso u).symm
  let e₃ := (DerivedCategory.Plus.QCompιIso D).app (P.mapCochainComplexPlus.obj L)
  let e₄ := (P.mapDerivedCategoryFactors.app L.obj).symm
  let e₅ := P.mapDerivedCategory.mapIso ((DerivedCategory.Plus.QCompιIso C).symm.app L ≪≫
    (DerivedCategory.Plus.ι (C := C)).mapIso e)
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅

set_option backward.isDefEq.respectTransparency false in
private def shriekStarIso {X : TopCat.{0}} (S : Stratum X)
    [DiscreteTopology (TopCat.of S.ambientOpen)] (F : BoundedBelow X) :
    (DerivedCategory.Plus.ι (C := Sheaves S.space)).obj (S.shriek.obj F) ≅
      S.star.obj F.obj := by
  let U := TopCat.of S.ambientOpen
  let j := openInclusion S.ambientOpen
  let i := closedInclusion (X := U) S.subset
  let G := (boundedBelowInverseImage j).obj F
  let EX := extraordinaryInverseImage (X := U) S.closed
  let e₀ : EX ≅ inverseImage i := extraordinaryIsoInverseImage (X := U) S.closed
  letI : EX.Additive := CategoryTheory.Functor.additive_of_iso e₀.symm
  let e := rightDerivedPlusIso e₀
  exact (DerivedCategory.Plus.ι (C := Sheaves S.space)).mapIso (e.app G) ≪≫
    rightDerivedPlusCohomologicalIso (inverseImage i) G ≪≫
    (derivedInverseImageComposition i j).symm.app F.obj

private theorem middlePerverse_degreeZero {X : TopCat.{0}} [DiscreteTopology X]
    {F : Derived X} (h : IsMiddlePerverse (pointStratification X) F) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((cohomology X n).obj F) := by
  obtain ⟨_, hb, h⟩ := h
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  let S := (pointStratification X).stratum x
  let y : S.space := ⟨⟨x, by trivial⟩, rfl⟩
  let e :=
    inverseImageStalkIso S.inclusion ((cohomology X n).obj F) y ≪≫
      (stalk y).mapIso (exactDerivedCohomologyIso (inverseImage S.inclusion) F n).symm
  have hzero : IsZero ((cohomology S.space n).obj (S.star.obj F)) := by
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact ((h x).2 n (by simpa [S, pointStratification] using hn)).of_iso
        ((cohomology S.space n).mapIso (shriekStarIso S ⟨F, hb⟩)).symm
    · exact (h x).1 n (by simpa [S, pointStratification] using hn)
  exact ((stalk y).map_isZero hzero).of_iso e

private def constantPresheafGermIso (X : TopCat.{0}) (x : X) (V : Coeff.{0}) :
    V ≅ TopCat.Presheaf.stalk (X := X) ((CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj V) x := by
  let P : X.Presheaf Coeff.{0} := (CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj V
  let C : Cocone ((OpenNhds.inclusion x).op ⋙ P) :=
    { pt := V
      ι := { app := fun _ ↦ 𝟙 V
             naturality := fun _ _ _ ↦ Category.id_comp _ } }
  let v : P.stalk x ⟶ V := colimit.desc ((OpenNhds.inclusion x).op ⋙ P) C
  have hv (U : Opens X) (h : x ∈ U) : P.germ U x h ≫ v = 𝟙 V :=
    colimit.ι_desc C (op ⟨U, h⟩)
  refine ⟨P.Γgerm x, v, hv ⊤ trivial, ?_⟩
  apply TopCat.Presheaf.stalk_hom_ext P
  intro U h
  change P.germ U x h ≫ v ≫ P.Γgerm x = P.germ U x h ≫ 𝟙 (P.stalk x)
  erw [← Category.assoc, hv, Category.id_comp, Category.comp_id]
  exact (P.germ_res (homOfLE le_top) x h).symm.trans (Category.id_comp _)

private def constantStalkIso (X : TopCat.{0}) (x : X) (V : Coeff.{0}) :
    V ≅ (stalk x).obj (constant X V) := by
  let P : X.Presheaf Coeff.{0} := (CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj V
  let m := (TopCat.Presheaf.stalkFunctor Coeff.{0} x).map
    (toSheafify (Opens.grothendieckTopology X) P)
  exact constantPresheafGermIso X x V ≪≫
    @asIso _ _ _ _ m (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Coeff.{0} P)

private theorem constantStalkIso_germ (X : TopCat.{0}) (x : X) (V : Coeff.{0}) :
    (constantStalkIso X x V).hom =
      (toSheafify (Opens.grothendieckTopology X)
        ((CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj V)).app (op ⊤) ≫
          (constant X V).presheaf.Γgerm x :=
  TopCat.Presheaf.stalkFunctor_map_germ (C := Coeff.{0}) ⊤ x trivial
    (toSheafify (Opens.grothendieckTopology X) ((CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj V))

set_option backward.isDefEq.respectTransparency false in
private def constantOfSubsingleton (X : TopCat.{0}) [Subsingleton X] (F : Sheaves X) :
    constant X (F.presheaf.obj (op ⊤)) ≅ F := by
  let J := Opens.grothendieckTopology X
  let A := F.presheaf.obj (op ⊤)
  let P : X.Presheaf Coeff.{0} := (CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj A
  let adj := sheafificationAdjunction J Coeff.{0}
  let v : P ⟶ F.presheaf := (constantPresheafAdj Coeff.{0} (Preorder.isTerminalTop (Opens X))).counit.app F.presheaf
  let u : constant X A ⟶ F := (adj.homEquiv P F).symm v
  have hu : toSheafify J P ≫ u.hom = v :=
    (adj.homEquiv_unit P F ((adj.homEquiv P F).symm v)).symm.trans
      ((adj.homEquiv P F).apply_symm_apply v)
  letI : IsIso u := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro x
    let S := TopCat.Presheaf.stalkFunctor Coeff.{0} x
    have hv : (constantStalkIso X x A).hom ≫ S.map u.hom = F.presheaf.Γgerm x := by
      rw [constantStalkIso_germ, Category.assoc]
      change (toSheafify J P).app (op ⊤) ≫
        ((constant X A).presheaf.germ ⊤ x trivial ≫ S.map u.hom) = _
      erw [TopCat.Presheaf.stalkFunctor_map_germ (C := Coeff.{0}) ⊤ x trivial u.hom,
        ← Category.assoc]
      change ((toSheafify J P ≫ u.hom).app (op ⊤)) ≫ _ = _
      rw [hu]
      change F.presheaf.map (show op ⊤ ⟶ op ⊤ from ((Preorder.isTerminalTop (Opens X)).from ⊤).op) ≫ _ = _
      rw [Subsingleton.elim ((Preorder.isTerminalTop (Opens X)).from ⊤) (𝟙 ⊤),
        op_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
    have hG : IsIso (F.presheaf.Γgerm x) :=
      germ_minimal_isIso F x ⊤ trivial fun W hx y _ ↦ (Subsingleton.elim x y) ▸ hx
    have : IsIso ((constantStalkIso X x A).hom ≫ S.map u.hom) := hv.symm ▸ hG
    exact IsIso.of_isIso_comp_left (constantStalkIso X x A).hom _
  exact asIso u

open private stalkPushforward_naturality from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

private def pullbackSections {X Y : TopCat.{0}} (p : Y ⟶ X) (F : Sheaves X) (U : Opens X) :
    F.presheaf.obj (op U) ⟶ ((inverseImage p).obj F).presheaf.obj (op ((Opens.map p).obj U)) :=
  ((inverseDirectAdjunction p).unit.app F).hom.app (op U)

set_option backward.isDefEq.respectTransparency false in
private theorem inverseImageStalkMap_germ {X Y : TopCat.{0}} (p : Y ⟶ X) (F : Sheaves X)
    (U : Opens X) (y : Y) (hy : p y ∈ U) :
    F.presheaf.germ U (p y) hy ≫ inverseImageStalkMap p F y =
      pullbackSections p F U ≫ ((inverseImage p).obj F).presheaf.germ
        ((Opens.map p).obj U) y hy := by
  let G := (inverseImage p).obj F
  let a := (inverseDirectAdjunction p).unit.app F
  change F.presheaf.germ U (p y) hy ≫ (TopCat.Presheaf.stalkFunctor Coeff.{0} (p y)).map a.hom ≫
    G.presheaf.stalkPushforward Coeff.{0} p y = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc U (p y) hy a.hom,
    TopCat.Presheaf.stalkPushforward_germ]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem inverseImageStalkMap_naturality {X Y : TopCat.{0}} (p : Y ⟶ X)
    {F G : Sheaves X} (f : F ⟶ G) (y : Y) :
    (stalk (p y)).map f ≫ inverseImageStalkMap p G y =
      inverseImageStalkMap p F y ≫ (stalk y).map ((inverseImage p).map f) := by
  let adj := inverseDirectAdjunction p
  have hu : f ≫ adj.unit.app G = adj.unit.app F ≫
      (directImage p).map ((inverseImage p).map f) := adj.unit.naturality f
  unfold inverseImageStalkMap
  erw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hu,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg ((stalk (p y)).map (adj.unit.app F) ≫ ·)
    (stalkPushforward_naturality p ((inverseImage p).map f).hom y)

set_option backward.isDefEq.respectTransparency false in
private theorem germAlongFiber_locallyConstant (H : AnalyticGroup.{0}) {X : TopCat.{0}}
    [DiscreteTopology X] (F : Sheaves X) (x : X)
    (t : ((inverseImage (AnalyticAction.projection H X)).obj F).presheaf.obj
      (op ((Opens.map (AnalyticAction.projection H X)).obj (singletonOpen x)))) :
    IsLocallyConstant (fun (a : H.space) ↦ (show (stalk x).obj F from
      (inverseImageStalkIso (AnalyticAction.projection H X) F (a, x)).inv
        (((inverseImage (AnalyticAction.projection H X)).obj F).presheaf.germ _ (a, x)
          (Set.mem_singleton x) t))) := by
  let p := AnalyticAction.projection H X
  let U := singletonOpen x
  let V := (Opens.map p).obj U
  let G := (inverseImage p).obj F
  let y (a : H.space) : AnalyticAction.Parameters H X := (a, x)
  let hy (a : H.space) : y a ∈ V := Set.mem_singleton x
  let e (a : H.space) := inverseImageStalkIso p F (y a)
  let f (a : H.space) : (stalk x).obj F := (e a).inv (G.presheaf.germ V (y a) (hy a) t)
  change IsLocallyConstant f
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  let g := F.presheaf.germ U x (Set.mem_singleton x)
  have : IsIso g := germ_singleton_isIso F x
  let s := (inv g) (f a)
  have hs : g s = f a := by
    change g ((inv g) (f a)) = f a
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  let u := pullbackSections p F U s
  have hFormula (b : H.space) :
      G.presheaf.germ V (y b) (hy b) u = (e b).hom (f a) := by
    have hb := inverseImageStalkMap_germ p F U (y b) (hy b)
    have hEq := congrArg (fun k : F.presheaf.obj (op U) ⟶ (stalk (y b)).obj G ↦ k s) hb
    simp only [ConcreteCategory.comp_apply] at hEq
    change (e b).hom (g s) = G.presheaf.germ V (y b) (hy b) u at hEq
    rw [hs] at hEq
    exact hEq.symm
  have heq : G.presheaf.germ V (y a) (hy a) t = G.presheaf.germ V (y a) (hy a) u := by
    rw [hFormula]
    change _ = (e a).hom ((e a).inv (G.presheaf.germ V (y a) (hy a) t))
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  obtain ⟨W, ha, ι, ι', hsec⟩ := G.presheaf.germ_eq (y a) (hy a) (hy a) t u heq
  have hycont : Continuous y := continuous_id.prodMk continuous_const
  have hN : y ⁻¹' (W : Set (AnalyticAction.Parameters H X)) ∈ 𝓝 a :=
    (W.isOpen.preimage hycont).mem_nhds ha
  refine Filter.Eventually.mono hN ?_
  intro b hb
  have hW : y b ∈ W := hb
  have hg : G.presheaf.germ V (y b) (hy b) t = G.presheaf.germ V (y b) (hy b) u := by
    rw [← G.presheaf.germ_res_apply ι (y b) hW t, ← G.presheaf.germ_res_apply ι' (y b) hW u, hsec]
  change (e b).inv (G.presheaf.germ V (y b) (hy b) t) = f a
  rw [hg, hFormula, ← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem projectionHom_ext (H : AnalyticGroup.{0}) {X : TopCat.{0}}
    [DiscreteTopology X] [PreconnectedSpace H.space] (F G : Sheaves X)
    {f g : (inverseImage (AnalyticAction.projection H X)).obj F ⟶
      (inverseImage (AnalyticAction.projection H X)).obj G}
    (h : (inverseImage (AnalyticAction.identitySection H X)).map f =
      (inverseImage (AnalyticAction.identitySection H X)).map g) : f = g := by
  apply sheaf_hom_ext_stalk
  rintro ⟨a, x⟩
  let p := AnalyticAction.projection H X
  let i := AnalyticAction.identitySection H X
  let U := singletonOpen x
  let V := (Opens.map p).obj U
  let A := (inverseImage p).obj F
  let B := (inverseImage p).obj G
  let y (b : H.space) : AnalyticAction.Parameters H X := (b, x)
  let hy (b : H.space) : y b ∈ V := Set.mem_singleton x
  let e (b : H.space) := inverseImageStalkIso p F (y b)
  let e' (b : H.space) := inverseImageStalkIso p G (y b)
  have h₁ : (stalk (y 1)).map f = (stalk (y 1)).map g := by
    apply (cancel_mono (inverseImageStalkMap i B x)).mp
    change (stalk (i x)).map f ≫ inverseImageStalkMap i B x =
      (stalk (i x)).map g ≫ inverseImageStalkMap i B x
    rw [inverseImageStalkMap_naturality, inverseImageStalkMap_naturality, h]
  apply (cancel_epi (e a).hom).mp
  apply (cancel_mono (e' a).inv).mp
  ext s
  let q := F.presheaf.germ U x (Set.mem_singleton x)
  have : IsIso q := germ_singleton_isIso F x
  let v := (inv q) s
  let u := pullbackSections p F U v
  have hv : q v = s := by
    change q ((inv q) s) = s
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  have eq (b : H.space) :
      A.presheaf.germ V (y b) (hy b) u = (e b).hom s := by
    have hb := inverseImageStalkMap_germ p F U (y b) (hy b)
    have hh := congrArg (fun k : F.presheaf.obj (op U) ⟶ (stalk (y b)).obj A ↦ k v) hb
    simp only [ConcreteCategory.comp_apply] at hh
    change (e b).hom (q v) = A.presheaf.germ V (y b) (hy b) u at hh
    rw [hv] at hh
    exact hh.symm
  have hconst (m : A ⟶ B) (b : H.space) :
      (e' b).inv ((stalk (y b)).map m ((e b).hom s)) =
      (e' 1).inv ((stalk (y 1)).map m ((e 1).hom s)) := by
    rw [← eq b, ← eq 1]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ (hy b) m.hom,
      TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ (hy 1) m.hom]
    exact (germAlongFiber_locallyConstant H G x (m.hom.app (op V) u)).apply_eq_of_preconnectedSpace b 1
  change (e' a).inv ((stalk (y a)).map f ((e a).hom s)) =
    (e' a).inv ((stalk (y a)).map g ((e a).hom s))
  rw [hconst f a, hconst g a, h₁]

private def topGermIso {X : TopCat.{0}} [Subsingleton X] (F : Sheaves X) (x : X) :
    F.presheaf.obj (op ⊤) ≅ (stalk x).obj F := by
  exact @asIso _ _ _ _ (F.presheaf.Γgerm x)
    (germ_minimal_isIso F x ⊤ trivial fun _ hx y _ ↦ (Subsingleton.elim x y) ▸ hx)

private theorem finiteStalk_of_locallyConstant {X : TopCat.{0}} {F : Sheaves X}
    (h : LocallyConstantFiniteRank F) (x : X) : Module.Finite ℚ ((stalk x).obj F) := by
  obtain ⟨U, hx, V, hV, ⟨e⟩⟩ := h x
  let y : U := ⟨x, hx⟩
  let e' := constantStalkIso (TopCat.of U) y V ≪≫ (stalk y).mapIso e.symm ≪≫
    (inverseImageStalkIso (openInclusion U) F y).symm
  exact Module.Finite.equiv e'.toLinearEquiv

private theorem locallyConstant_of_finiteStalks {X : TopCat.{0}} [DiscreteTopology X]
    (F : Sheaves X) (h : ∀ x, Module.Finite ℚ ((stalk x).obj F)) :
    LocallyConstantFiniteRank F := by
  intro x
  let U := singletonOpen x
  let y : U := ⟨x, Set.mem_singleton x⟩
  have : Subsingleton U := ⟨fun a b ↦ Subtype.ext (a.property.trans b.property.symm)⟩
  let G := (inverseImage (openInclusion U)).obj F
  let v := G.presheaf.obj (op ⊤)
  let e := inverseImageStalkIso (openInclusion U) F y ≪≫ (topGermIso G y).symm
  have : Module.Finite ℚ ((stalk x).obj F) := h x
  exact ⟨U, y.property, v, Module.Finite.equiv e.toLinearEquiv,
    ⟨(constantOfSubsingleton (TopCat.of U) G).symm⟩⟩

private theorem moduleFinite_of_isZero (A : Coeff.{0}) (h : IsZero A) : Module.Finite ℚ A := by
  have eq : 𝟙 A = 0 := h.eq_of_src _ _
  have : Subsingleton A := ⟨fun x y ↦ by
    have hz (z : A) : z = 0 :=
      congrArg (fun f : A ⟶ A ↦ f z) eq
    exact (hz x).trans (hz y).symm⟩
  infer_instance

private theorem singleCohomology_isZero {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (G : C) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj ((DerivedCategory.singleFunctor C 0).obj G)) := by
  let F := (DerivedCategory.singleFunctor C 0).obj G
  rcases lt_or_gt_of_ne hn with hn | hn
  · exact (DerivedCategory.isGE_iff F 0).mp inferInstance n hn
  · exact (DerivedCategory.isLE_iff F 0).mp inferInstance n hn

private theorem middlePerverse_finiteStalk {X : TopCat.{0}} [DiscreteTopology X]
    {F : Derived X} (h : IsMiddlePerverse (pointStratification X) F) (x : X) :
    Module.Finite ℚ ((stalk x).obj ((cohomology X 0).obj F)) := by
  let S := (pointStratification X).stratum x
  let y : S.space := ⟨⟨x, by trivial⟩, rfl⟩
  have hfin := finiteStalk_of_locallyConstant (h.1.2 x 0) y
  exact Module.Finite.equiv (inverseImageStalkIso S.inclusion ((cohomology X 0).obj F) y).symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
private theorem single_middlePerverse {X : TopCat.{0}} [DiscreteTopology X]
    (G : Sheaves X) (h : ∀ x, Module.Finite ℚ ((stalk x).obj G)) :
    IsMiddlePerverse (pointStratification X) ((DerivedCategory.singleFunctor (Sheaves X) 0).obj G) := by
  let F := (DerivedCategory.singleFunctor (Sheaves X) 0).obj G
  have hZ (n : ℤ) (hn : n ≠ 0) : IsZero ((cohomology X n).obj F) :=
    singleCohomology_isZero G n hn
  have hb : DerivedCategory.TStructure.t.plus F := ⟨0, inferInstance⟩
  refine ⟨⟨(Set.finite_singleton (0 : ℤ)).subset (fun n hn ↦ ?_), ?_⟩, hb, ?_⟩
  · exact by_contra fun (he : n ≠ 0) ↦ hn (hZ n he)
  · intro x n
    let S := (pointStratification X).stratum x
    have : DiscreteTopology S.space := inferInstance
    apply locallyConstant_of_finiteStalks
    intro y
    let e := inverseImageStalkIso S.inclusion ((cohomology X n).obj F) y
    by_cases hn : n = 0
    · subst n
      let e₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves X) 0).app G
      let e₁ : (stalk (S.inclusion y)).obj G ≅
          (stalk y).obj ((inverseImage S.inclusion).obj ((cohomology X 0).obj F)) :=
        (stalk (S.inclusion y)).mapIso e₀.symm ≪≫ e
      have := h (S.inclusion y)
      exact Module.Finite.equiv e₁.toLinearEquiv
    · exact moduleFinite_of_isZero _ (((stalk (S.inclusion y)).map_isZero (hZ n hn)).of_iso e.symm)
  · intro x
    let S := (pointStratification X).stratum x
    have hstar (n : ℤ) (hn : n ≠ 0) : IsZero ((cohomology S.space n).obj (S.star.obj F)) :=
      ((inverseImage S.inclusion).map_isZero (hZ n hn)).of_iso
        (exactDerivedCohomologyIso (inverseImage S.inclusion) F n)
    constructor
    · intro n hn
      exact hstar n (ne_of_gt (show 0 < n from hn))
    · intro n hn
      exact (hstar n (ne_of_lt (show n < 0 from hn))).of_iso
        ((cohomology S.space n).mapIso (shriekStarIso S ⟨F, hb⟩))

private def stageSingleExtensionIso {X : TopCat.{0}} (A : ClosedStages X) (n : ℕ)
    (G : Sheaves (A.space n)) :
    (A.extension n).obj ((DerivedCategory.singleFunctor (Sheaves (A.space n)) 0).obj G) ≅
      (DerivedCategory.singleFunctor (Sheaves X) 0).obj ((directImage (A.inclusion n)).obj G) := by
  let P := directImage (A.inclusion n)
  letI : P.IsLeftAdjoint := (extraordinaryAdjunction (A.closed n)).isLeftAdjoint
  exact (P.mapDerivedCategorySingleFunctor 0).app G

set_option backward.isDefEq.respectTransparency false in
private theorem finiteStagePerverse_sheafWitness {r : ℕ} (g : StageGeometry r) {F : Derived (torusSpace r)}
    (h : IsFiniteStagePerverse (stages r g) (stageStratifications r g) F) :
    ∃ (n : ℕ) (G : Sheaves ((stages r g).space n)),
      (∀ x, Module.Finite ℚ ((stalk x).obj G)) ∧
      Nonempty ((DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0).obj
        ((directImage ((stages r g).inclusion n)).obj G) ≅ F) := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  let X := torusSpace r
  have : DiscreteTopology X := g.discrete
  let A := stages r g
  let Y := A.space n
  have : DiscreteTopology Y := inferInstanceAs (DiscreteTopology (TopCat.of (A.stage n)))
  have hG : IsMiddlePerverse (pointStratification Y) G.obj := G.property
  let H := (cohomology Y 0).obj G.obj
  let e₀ : (DerivedCategory.singleFunctor (Sheaves Y) 0).obj H ≅ G.obj :=
    degreeZeroIso G.obj (middlePerverse_degreeZero hG)
  exact ⟨n, H, middlePerverse_finiteStalk hG,
    ⟨(stageSingleExtensionIso A n H).symm ≪≫ (A.extension n).mapIso e₀ ≪≫ e⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem derivedProjectionHom_ext (H : AnalyticGroup.{0}) {X : TopCat.{0}}
    [DiscreteTopology X] [PreconnectedSpace H.space] {F : Derived X} {G : Sheaves X}
    (e : (DerivedCategory.singleFunctor (Sheaves X) 0).obj G ≅ F)
    {f g : (derivedInverseImage (AnalyticAction.projection H X)).obj F ⟶
      (derivedInverseImage (AnalyticAction.projection H X)).obj F}
    (h : (derivedInverseImage (AnalyticAction.identitySection H X)).map f =
      (derivedInverseImage (AnalyticAction.identitySection H X)).map g) : f = g := by
  let Y := AnalyticAction.Parameters H X
  let p := AnalyticAction.projection H X
  let i := AnalyticAction.identitySection H X
  let S := DerivedCategory.singleFunctor (Sheaves Y) 0
  let T := DerivedCategory.singleFunctor (Sheaves X) 0
  let P := (inverseImage p).obj G
  let a : S.obj P ≅ (derivedInverseImage p).obj F :=
    ((inverseImage p).mapDerivedCategorySingleFunctor 0).symm.app G ≪≫
      (derivedInverseImage p).mapIso e
  obtain ⟨f₀, hf⟩ := S.map_surjective (a.hom ≫ f ≫ a.inv)
  obtain ⟨g₀, hg⟩ := S.map_surjective (a.hom ≫ g ≫ a.inv)
  have hmap : (derivedInverseImage i).map (S.map f₀) =
      (derivedInverseImage i).map (S.map g₀) := by
    rw [hf, hg]
    change (derivedInverseImage i).map f = (derivedInverseImage i).map g at h
    simp only [Functor.map_comp, h]
  have h₀ : f₀ = g₀ := by
    apply projectionHom_ext H G G
    apply T.map_injective
    let b := (inverseImage i).mapDerivedCategorySingleFunctor 0
    apply (cancel_epi (b.hom.app P)).mp
    calc
      b.hom.app P ≫ T.map ((inverseImage i).map f₀) =
          (derivedInverseImage i).map (S.map f₀) ≫ b.hom.app P :=
        (b.hom.naturality f₀).symm
      _ = (derivedInverseImage i).map (S.map g₀) ≫ b.hom.app P := by rw [hmap]
      _ = b.hom.app P ≫ T.map ((inverseImage i).map g₀) := b.hom.naturality g₀
  have heq : a.hom ≫ f ≫ a.inv = a.hom ≫ g ≫ a.inv := by rw [← hf, ← hg, h₀]
  exact (cancel_mono a.inv).mp ((cancel_epi a.hom).mp heq)

set_option backward.isDefEq.respectTransparency false in
private theorem trivialEquivariance_unique (H : AnalyticGroup.{0}) {X : TopCat.{0}}
    [DiscreteTopology X] [PreconnectedSpace H.space] {F : Derived X} {G : Sheaves X}
    (e : (DerivedCategory.singleFunctor (Sheaves X) 0).obj G ≅ F)
    (v : (trivialAction H X).Equivariance F) :
    v = identityEquivariance H X F := by
  let p := AnalyticAction.projection H X
  let i := AnalyticAction.identitySection H X
  let hi : i ≫ p = 𝟙 X := AnalyticAction.identity_projection
  have hv : v.iso.hom = 𝟙 ((derivedInverseImage p).obj F) := by
    apply derivedProjectionHom_ext H e
    have hn : pullbackMorphism i hi hi v.iso.hom =
        pullbackMorphism i hi hi (𝟙 ((derivedInverseImage p).obj F)) :=
      v.identity.trans (pullbackMorphism_id i p F hi).symm
    let u := eqToHom (congrArg (fun t ↦ (derivedInverseImage t).obj F) hi.symm)
    let w := eqToHom (congrArg (fun t ↦ (derivedInverseImage t).obj F) hi)
    let a := (derivedInverseImageComposition i p).app F
    change u ≫ a.hom ≫ (derivedInverseImage i).map v.iso.hom ≫ a.inv ≫ w =
      u ≫ a.hom ≫ (derivedInverseImage i).map (𝟙 ((derivedInverseImage p).obj F)) ≫ a.inv ≫ w at hn
    have h := (cancel_epi a.hom).mp ((cancel_epi u).mp hn)
    exact (cancel_mono (a.inv ≫ w)).mp h
  obtain ⟨v, _, _⟩ := v
  change v.hom = 𝟙 _ at hv
  have : v = Iso.refl _ := Iso.ext hv
  subst v
  rfl

private theorem jetEquivariance_ext {X : TopCat.{0}} {J : JetSystem.{0}} {A : JetAction J X}
    {F : Derived X} {a b : A.Equivariance F} (h : a.datum = b.datum) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem stageEquivariance_ext {X : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {F : Derived X} {a b : B.Equivariance F}
    (h : a.datum = b.datum) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem stageEquivariance_eq (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r)
    {F : Derived (torusSpace r)}
    (hF : IsFiniteStagePerverse (stages r g) (stageStratifications r g) F)
    (v : (stageActions r g c).Equivariance F) :
    v = identityStageEquivariance (jetSystem r c) (stages r g) F := by
  let A := stages r g
  let J := jetSystem r c
  have : DiscreteTopology (torusSpace r) := g.discrete
  obtain ⟨m, G, _, ⟨e⟩⟩ := finiteStagePerverse_sheafWitness g hF
  apply stageEquivariance_ext
  funext n
  apply jetEquivariance_ext
  funext k hk
  let H := J.group k
  have : PreconnectedSpace H.space := (jet_coordinates r k).2.toPreconnectedSpace
  have : DiscreteTopology (A.space n) :=
    inferInstanceAs (DiscreteTopology (TopCat.of (A.stage n)))
  let p := A.inclusion n
  let P := (directImage (A.inclusion m)).obj G
  let d := ((inverseImage p).mapDerivedCategorySingleFunctor 0).symm.app P ≪≫
    (derivedInverseImage p).mapIso e
  exact trivialEquivariance_unique H d _

private theorem finiteSubset_stage {X : TopCat.{0}} (A : ClosedStages X) {Z : Set X}
    (hZ : Z.Finite) : ∃ n, Z ⊆ A.stage n := by
  have h : Directed (· ⊆ ·) A.stage := fun n m ↦
    ⟨max n m, A.monotone (le_max_left n m), A.monotone (le_max_right n m)⟩
  have hcover : (hZ.toFinset : Set X) ⊆ ⋃ n, A.stage n :=
    fun x _ ↦ Set.mem_iUnion.mpr (A.exhaustive x)
  simpa only [Set.Finite.coe_toFinset] using
    h.exists_mem_subset_of_finset_subset_biUnion hcover

private def closedStageStalkIso {X : TopCat.{0}} (A : ClosedStages X) (n : ℕ)
    (G : Sheaves (A.space n)) (y : A.space n) :
    (stalk (A.inclusion n y)).obj ((directImage (A.inclusion n)).obj G) ≅
      (stalk y).obj G :=
  @asIso _ _ _ _ (G.presheaf.stalkPushforward Coeff.{0} (A.inclusion n) y)
    (TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Coeff.{0}
      (f := A.inclusion n) IsInducing.subtypeVal G.presheaf y)

set_option backward.isDefEq.respectTransparency false in
private theorem perverse_hasFiniteStalkFamily (r : ℕ) (g : StageGeometry r)
    {F : Derived (torusSpace r)}
    (hF : IsFiniteStagePerverse (stages r g) (stageStratifications r g) F) :
    IsFiniteFamily r ((degreeZeroStalks r).obj F) := by
  obtain ⟨n, G, hG, ⟨e⟩⟩ := finiteStagePerverse_sheafWitness g hF
  let X := torusSpace r
  let A := stages r g
  let P := (directImage (A.inclusion n)).obj G
  let H := cohomology X 0
  let e₀ : P ≅ H.obj F :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves X) 0).symm.app P ≪≫
      H.mapIso e
  have hz (x : X) (hx : x ∉ A.stage n) : IsZero ((stalk x).obj (H.obj F)) :=
    (closedDirectImage_supported (A.closed n) G x hx).of_iso ((stalk x).mapIso e₀).symm
  constructor
  · intro w
    let x := monomialPoint r w
    change Module.Finite ℚ ((stalk x).obj (H.obj F))
    by_cases hx : x ∈ A.stage n
    · let y : A.space n := ⟨x, hx⟩
      have := hG y
      exact Module.Finite.equiv
        ((closedStageStalkIso A n G y).symm ≪≫ (stalk x).mapIso e₀).toLinearEquiv
    · exact moduleFinite_of_isZero _ (hz x hx)
  · refine (Set.Finite.preimage (monomialPoint_bijective r).injective.injOn
      (stageSet_finite r n)).subset ?_
    intro w hw
    by_contra hx
    exact hw (hz (monomialPoint r w) hx)

set_option backward.isDefEq.respectTransparency false in
private theorem extension_isFiniteStagePerverse (r : ℕ) (g : StageGeometry r) (V : Graded r) :
    IsFiniteStagePerverse (stages r g) (stageStratifications r g) ((extendByZero r).obj V) := by
  let X := torusSpace r
  have : DiscreteTopology X := g.discrete
  let A := stages r g
  let F := (skyscraperProduct r).obj V.obj
  let Z := monomialPoint r '' familySupport V.obj
  have hZ : Z.Finite := V.property.2.image _
  obtain ⟨n, hn⟩ := finiteSubset_stage A hZ
  have hF : SupportedOn (A.stage n) F :=
    fun x hx ↦ skyscraperProduct_supported r g V.obj x (fun h ↦ hx (hn h))
  obtain ⟨G, ⟨e⟩⟩ := (SheafModels.supportedEssentialImage (A.closed n) F).mpr hF
  have := stalkProductCounit_isIso r g (monomialPoint_bijective r).injective
  have hFin (x : X) : Module.Finite ℚ ((stalk x).obj F) := by
    obtain ⟨w, rfl⟩ := (monomialPoint_bijective r).surjective x
    let d : (stalk (monomialPoint r w)).obj F ≅ V.obj.obj (Discrete.mk w) :=
      ((asIso (stalkProductCounit r)).app V.obj).app (Discrete.mk w)
    have := V.property.1 w
    exact Module.Finite.equiv d.symm.toLinearEquiv
  have hG (y : A.space n) : Module.Finite ℚ ((stalk y).obj G) := by
    let d := ((stalk (A.inclusion n y)).mapIso e).symm ≪≫ closedStageStalkIso A n G y
    have := hFin (A.inclusion n y)
    exact Module.Finite.equiv d.toLinearEquiv
  have : DiscreteTopology (A.space n) :=
    inferInstanceAs (DiscreteTopology (TopCat.of (A.stage n)))
  refine ⟨n, ⟨_, single_middlePerverse G hG⟩, ⟨?_⟩⟩
  exact stageSingleExtensionIso A n G ≪≫
    (DerivedCategory.singleFunctor (Sheaves X) 0).mapIso e

set_option backward.isDefEq.respectTransparency false in
private def identityEquivariant (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Derived (torusSpace r) ⥤ (stageActions r g c).Object where
  obj F := ⟨F, identityStageEquivariance (jetSystem r c) (stages r g) F⟩
  map f := ⟨f, by
    intro n k _
    let A := stages r g
    let p := AnalyticAction.projection ((jetSystem r c).group k) (A.space n)
    let u := (derivedInverseImage p).map ((derivedInverseImage (A.inclusion n)).map f)
    exact (Category.comp_id u).trans (Category.id_comp u).symm⟩
  map_id _ := StageJetActions.Hom.ext rfl
  map_comp _ _ := StageJetActions.Hom.ext rfl

private def forgetPerverseFullyFaithful (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    (forgetPerverse r g c).FullyFaithful where
  preimage {F G} f := ObjectProperty.homMk
    ⟨f, by
      intro n k hk
      have hF := stageEquivariance_eq r g c F.property F.obj.equivariance
      have hG := stageEquivariance_eq r g c G.property G.obj.equivariance
      rw [hF, hG]
      exact ((identityEquivariant r g c).map f).comm n k hk⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

private def perverseStalks (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Perverse r g c ⥤ Graded r :=
  (IsFiniteFamily r).lift (forgetPerverse r g c ⋙ degreeZeroStalks r)
    (fun F ↦ perverse_hasFiniteStalkFamily r g F.property)

private def perverseExtension (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Graded r ⥤ Perverse r g c :=
  let P : ObjectProperty ((stageActions r g c).Object) :=
    fun F ↦ IsFiniteStagePerverse (stages r g) (stageStratifications r g) F.obj
  P.lift (extendByZero r ⋙ identityEquivariant r g c)
    (fun V ↦ extension_isFiniteStagePerverse r g V)

set_option backward.isDefEq.respectTransparency false in
private def extensionStalkIso (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    perverseExtension r g c ⋙ perverseStalks r g c ≅ 𝟭 (Graded r) := by
  let I := gradedInclusion r
  letI : I.Full := inferInstanceAs ((IsFiniteFamily r).ι.Full)
  letI : I.Faithful := inferInstanceAs ((IsFiniteFamily r).ι.Faithful)
  apply Functor.fullyFaithfulCancelRight I
  let T := sheafStalkFamilies r
  let K := skyscraperProduct r
  letI := stalkProductCounit_isIso r g (monomialPoint_bijective r).injective
  let S := DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0
  let H := cohomology (torusSpace r) 0
  change I ⋙ K ⋙ (S ⋙ H) ⋙ T ≅ (𝟭 (Graded r)) ⋙ I
  calc
    _ ≅ I ⋙ K ⋙ (𝟭 _) ⋙ T :=
      Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft K (Functor.isoWhiskerRight
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves (torusSpace r)) 0) T))
    _ ≅ I ⋙ K ⋙ T := Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft K T.leftUnitor)
    _ ≅ I ⋙ 𝟭 _ := Functor.isoWhiskerLeft I (asIso (stalkProductCounit r))
    _ ≅ _ := I.rightUnitor ≪≫ I.leftUnitor.symm

set_option backward.isDefEq.respectTransparency false in
private def perverseExtensionFullyFaithful (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    (perverseExtension r g c).FullyFaithful := by
  letI := (forgetPerverseFullyFaithful r g c).faithful
  apply Functor.FullyFaithful.ofCompFaithful (G := forgetPerverse r g c)
  change (extendByZero r).FullyFaithful
  exact (IsFiniteFamily r).fullyFaithfulι.comp
    ((sheafFamiliesEquiv r g (monomialPoint_bijective r)).fullyFaithfulInverse.comp
      (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor _ 0)))

set_option backward.isDefEq.respectTransparency false in
private theorem perverseExtension_essSurj (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    (perverseExtension r g c).EssSurj := by
  constructor
  intro F
  obtain ⟨n, G, _, ⟨e⟩⟩ := finiteStagePerverse_sheafWitness g F.property
  let X := torusSpace r
  let P := (directImage ((stages r g).inclusion n)).obj G
  let S := DerivedCategory.singleFunctor (Sheaves X) 0
  let H := cohomology X 0
  let H₀ := H.obj F.obj.obj
  let e₀ : S.obj H₀ ≅ F.obj.obj := S.mapIso (H.mapIso e.symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves X) 0).app P) ≪≫ e
  have := stalkProductUnit_isIso r g (monomialPoint_bijective r)
  let d := (asIso (stalkProductUnit r)).app H₀
  refine ⟨(perverseStalks r g c).obj F, ⟨(forgetPerverseFullyFaithful r g c).preimageIso ?_⟩⟩
  change S.obj ((skyscraperProduct r).obj ((sheafStalkFamilies r).obj H₀)) ≅ F.obj.obj
  exact S.mapIso d.symm ≪≫ e₀

private def perverseEquivalence (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Perverse r g c ≌ Graded r := by
  let F := perverseStalks r g c
  let G := perverseExtension r g c
  let hG : G.FullyFaithful := perverseExtensionFullyFaithful r g c
  letI : G.IsEquivalence := ⟨hG.faithful, hG.full, perverseExtension_essSurj r g c⟩
  let E := G.asEquivalence.symm
  let e : G ⋙ F ≅ 𝟭 (Graded r) := extensionStalkIso r g c
  let d : E.functor ≅ F := E.functor.rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft E.functor e.symm ≪≫ E.funInvIdAssoc F
  exact CategoryTheory.Equivalence.mk F G (E.unitIso ≪≫ Functor.isoWhiskerRight d G) e

/-- Degree-zero stalks and extension by zero give the equivalence for the split torus. -/
theorem torusPerverseEquivalence : TorusPerverseEquivalence := by
  intro r
  let g := stageGeometry TorusStages.torusPoints r
  let c := continuousJets r
  refine ⟨g, c, jet_coordinates r, positiveLoopAction TorusStages.torusPoints r g c,
    ?_, supportedExtension r g, perverseEquivalence r g c, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  intro F hF
  exact ⟨identityStageEquivariance (jetSystem r c) (stages r g) F, trivial,
    fun v _ ↦ stageEquivariance_eq r g c hF v⟩

end RepTheorySurvey.Geometric.TorusPerverse
