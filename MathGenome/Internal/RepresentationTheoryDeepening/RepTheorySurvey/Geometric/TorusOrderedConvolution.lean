import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusOrderedConvolution
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusPerverse
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory TopologicalSpace Topology Opposite
open scoped Classical MonoidalCategory ZeroObject

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace RepTheorySurvey.Geometric.TorusOrderedConvolution

open Analytic LatticeModelSpecs TorusStageSpecs TorusPerverseSpecs TorusOrderedConvolutionSpecs

variable {r : ℕ}

private def coordinatesAtRank (r : ℕ) : CoordinatesAtRank r := by
  choose e q he hq hmon _ _ _ hfix using TorusStages.torusPoints
  refine ⟨(e r).trans (q r).symm, e r, ?_, he r, ?_, hfix r⟩
  · intro a
    change (q r).symm (e r a) = _
    rw [← hmon r a, Equiv.symm_apply_apply]
  · intro g
    change e r ((e r).symm (q r (coset (PositiveTorus r) g))) = _
    rw [Equiv.apply_symm_apply, hq]

private theorem coset_mul_positive (g : Loops r) (u : PositiveTorus r) :
    coset (PositiveTorus r) (g * (u : Loops r)) = coset (PositiveTorus r) g := by
  symm
  exact (LatticeModels.cosetRelation (PositiveTorus r) _ _).mpr
    ⟨by simp [← mul_assoc], ⟨u, rfl⟩⟩

private def loopLabel (c : CoordinatesAtRank r) (g : Loops r) : Labels r :=
  c.quotient.symm (coset (PositiveTorus r) g)

private theorem loopLabel_monomial (c : CoordinatesAtRank r) (a : Labels r) :
    loopLabel c (torusMonomial r a) = a := by
  simp [loopLabel, ← c.quotient_monomial]

private theorem loopLabel_mul_positive (c : CoordinatesAtRank r) (g : Loops r)
    (u : PositiveTorus r) : loopLabel c (g * (u : Loops r)) = loopLabel c g := by
  rw [loopLabel, coset_mul_positive]
  rfl

private theorem loop_factor (c : CoordinatesAtRank r) (g : Loops r) :
    ∃ u : PositiveTorus r, g = torusMonomial r (loopLabel c g) * (u : Loops r) := by
  have h : coset (PositiveTorus r) (torusMonomial r (loopLabel c g)) =
      coset (PositiveTorus r) g := by
    rw [← c.quotient_monomial, loopLabel, Equiv.apply_symm_apply]
  exact ((LatticeModels.cosetRelation (PositiveTorus r) _ _).mp h).2

private theorem torusMonomial_add (a b : Labels r) :
    torusMonomial r (a + b) = torusMonomial r a * torusMonomial r b := by
  funext i
  apply Units.ext
  exact monomial_add (a i) (b i)

private theorem loopLabel_mul (c : CoordinatesAtRank r) (g h : Loops r) :
    loopLabel c (g * h) = loopLabel c g + loopLabel c h := by
  obtain ⟨u, hu⟩ := loop_factor c g
  obtain ⟨v, hv⟩ := loop_factor c h
  have eq : g * h = torusMonomial r (loopLabel c g + loopLabel c h) *
      ((u * v : PositiveTorus r) : Loops r) := by
    rw [torusMonomial_add, Subgroup.coe_mul]
    exact (congrArg₂ (fun x y : Loops r ↦ x * y) hu hv).trans (by
      simp only [mul_assoc]
      rw [← mul_assoc (u : Loops r), mul_comm (u : Loops r), mul_assoc])
  rw [eq, loopLabel_mul_positive, loopLabel_monomial]

private theorem monomial_smul_base (c : CoordinatesAtRank r) (a : Labels r) :
    torusMonomial r a • (fun _ : Fin r ↦ standardLattice 1) = c.lattice a := by
  rw [← c.relate, ← c.quotient_monomial, Equiv.symm_apply_apply]

private theorem loop_smul_lattice (c : CoordinatesAtRank r) (g : Loops r) (b : Labels r) :
    g • c.lattice b = c.lattice (loopLabel c g + b) := by
  conv_lhs => rw [← monomial_smul_base c b, ← mul_smul, ← c.relate]
  rw [← loopLabel, loopLabel_mul, loopLabel_monomial]

private def pairLabels (c : CoordinatesAtRank r) {A B : Set (Labels r)}
    (p : OrderedRepresentatives c A B) : A × B :=
  (⟨loopLabel c p.val.1, by
    rcases p.property.1 with ⟨a, ha, e⟩
    simpa [loopLabel, ← e] using ha⟩,
   ⟨c.lattice.symm p.val.2, by
    rcases p.property.2 with ⟨b, hb, e⟩
    simpa [← e] using hb⟩)

private theorem pairLabels_monomial (c : CoordinatesAtRank r) {A B : Set (Labels r)}
    (p : A × B) : pairLabels c (monomialPair c p.1 p.2) = p := by
  apply Prod.ext <;> apply Subtype.ext
  · exact loopLabel_monomial c p.1
  · exact c.lattice.symm_apply_apply p.2

private theorem monomialPair_quotient (c : CoordinatesAtRank r) {A B : Set (Labels r)}
    (p : OrderedRepresentatives c A B) :
    orderedMk (monomialPair c (pairLabels c p).1 (pairLabels c p).2) = orderedMk p := by
  obtain ⟨u, hu⟩ := loop_factor c p.val.1
  apply Quotient.sound
  refine ⟨u, hu, ?_⟩
  change p.val.2 = ((u⁻¹ : PositiveTorus r) : Loops r) • c.lattice (c.lattice.symm p.val.2)
  rw [c.fixes, Equiv.apply_symm_apply]

private def orderedLabels (c : CoordinatesAtRank r) (A B : Set (Labels r)) :
    OrderedStage c A B ≃ A × B where
  toFun := Quotient.lift (pairLabels c) (by
    rintro p q ⟨u, hu, hv⟩
    apply Prod.ext <;> apply Subtype.ext
    · change loopLabel c p.val.1 = loopLabel c q.val.1
      rw [hu, loopLabel_mul_positive]
    · change c.lattice.symm p.val.2 = c.lattice.symm q.val.2
      rw [hv, c.fixes])
  invFun p := orderedMk (monomialPair c p.1 p.2)
  left_inv := Quotient.ind (monomialPair_quotient c)
  right_inv := pairLabels_monomial c

private theorem lattice_bounded (c : CoordinatesAtRank r) (N : ℕ) (a : Labels r) :
    c.lattice a ∈ stageSet r N ↔ ∀ i, -(N : ℤ) ≤ a i ∧ a i ≤ N := by
  obtain ⟨e, he, _, _⟩ := TorusStages.boundedTorusPoints r
  constructor
  · intro h
    let L : BoundedTorus r N := fun i ↦ ⟨c.lattice a i, h i⟩
    let b := (e N).symm L
    have hb : c.lattice b.val = c.lattice a := by
      rw [c.lattice_monomial, ← he N b, Equiv.apply_symm_apply]
      rfl
    rw [← c.lattice.injective hb]
    exact b.property
  · intro h
    let b : BoundedCoweight r N := ⟨a, h⟩
    have hb : forgetTorusBound (e N b) = c.lattice a := (he N b).trans (c.lattice_monomial a).symm
    rw [← hb]
    exact fun i ↦ (e N b i).property

private def tripleLabels (c : CoordinatesAtRank r) :
    TripleStage r ≃ Labels r × Labels r × Labels r where
  toFun := Quotient.lift (fun p : Loops r × Loops r × TorusLattice r ↦
      (loopLabel c p.1, loopLabel c p.2.1, c.lattice.symm p.2.2)) (by
    rintro p q ⟨u, v, hu, hv, hx⟩
    rw [hu, hv, hx, c.fixes, loopLabel_mul_positive,
      mul_comm ((u⁻¹ : PositiveTorus r) : Loops r) p.2.1,
      loopLabel_mul_positive, loopLabel_mul_positive])
  invFun p := tripleMk (torusMonomial r p.1) (torusMonomial r p.2.1) (c.lattice p.2.2)
  left_inv := by
    refine Quotient.ind ?_
    rintro ⟨g, h, x⟩
    obtain ⟨u, hu⟩ := loop_factor c g
    obtain ⟨v, hv⟩ := loop_factor c h
    apply Quotient.sound
    refine ⟨u, u * v, hu, ?_, ?_⟩
    · change h = ((u⁻¹ : PositiveTorus r) : Loops r) *
        torusMonomial r (loopLabel c h) * ((u * v : PositiveTorus r) : Loops r)
      calc
        h = torusMonomial r (loopLabel c h) * (v : Loops r) := hv
        _ = torusMonomial r (loopLabel c h) * ((u : Loops r)⁻¹ * ((u : Loops r) * (v : Loops r))) := by simp
        _ = _ := by rw [Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc, ← mul_assoc,
          mul_comm (torusMonomial r (loopLabel c h)) ((u : Loops r)⁻¹), mul_assoc]
    · change x = _ • c.lattice (c.lattice.symm x)
      rw [c.fixes, Equiv.apply_symm_apply]
  right_inv := by
    intro p
    change (loopLabel c (torusMonomial r p.1), loopLabel c (torusMonomial r p.2.1),
      c.lattice.symm (c.lattice p.2.2)) = p
    simp [loopLabel_monomial]

private def orderedGeometry (c : CoordinatesAtRank r) : OrderedGeometry r where
  coordinates := c
  labels := orderedLabels c
  label_mk _ := rfl
  terminal_label := by
    intro A B
    refine Quotient.ind ?_
    intro p
    change p.val.1 • p.val.2 =
      torusLatticeAt r (loopLabel c p.val.1 + c.lattice.symm p.val.2)
    rw [← c.lattice_monomial]
    conv_lhs => rw [← c.lattice.apply_symm_apply p.val.2, loop_smul_lattice]
  bounded := lattice_bounded c
  triples := tripleLabels c
  triple_mk _ _ _ := rfl
  triple_terminal := by
    refine Quotient.ind ?_
    rintro ⟨g, h, x⟩
    change (g * h) • x = torusLatticeAt r (loopLabel c g + loopLabel c h + c.lattice.symm x)
    rw [← c.lattice_monomial]
    conv_lhs => rw [← c.lattice.apply_symm_apply x, loop_smul_lattice, loopLabel_mul]

private theorem geometry_tripleMaps (c : CoordinatesAtRank r) :
    (orderedGeometry c).TripleMaps := by
  let D := orderedGeometry c
  intro g h x
  have hm (g' : Loops r) (x' : TorusLattice r) :
      D.wholePair (loopLabel c g') (c.lattice.symm x') = D.wholeMk g' x' :=
    monomialPair_quotient c (A := Set.univ) (B := Set.univ)
      ⟨(g', x'), ⟨_, trivial, c.quotient.apply_symm_apply _⟩,
        ⟨_, trivial, c.lattice.apply_symm_apply _⟩⟩
  change D.wholePair (loopLabel c g + loopLabel c h) (c.lattice.symm x) =
      D.wholeMk (g * h) x ∧
    D.wholePair (loopLabel c g) (loopLabel c h + c.lattice.symm x) = D.wholeMk g (h • x)
  rw [← loopLabel_mul, hm]
  constructor
  · rfl
  · have hx : c.lattice.symm (h • x) = loopLabel c h + c.lattice.symm x := by
      apply c.lattice.injective
      rw [Equiv.apply_symm_apply]
      conv_lhs => rw [← c.lattice.apply_symm_apply x, loop_smul_lattice]
    rw [← hx, hm]

private theorem positiveMap_injective (r : ℕ) :
    Function.Injective (positiveTorusMap r) := by
  intro u v h
  funext i
  apply Units.ext
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  exact congrArg (fun w : Loops r ↦ (w i).val) h

private theorem geometry_representatives (c : CoordinatesAtRank r) (A B : Set (Labels r)) :
    (orderedGeometry c).representatives A B := by
  let D := orderedGeometry c
  let make : (Fin r → Oˣ) × D.space A B → OrderedRepresentatives c A B := fun (u, z) ↦
    let p := D.labels A B z
    ⟨(torusMonomial r p.1.val * positiveTorusMap r u, c.lattice p.2.val),
      ⟨p.1.val, p.1.property, by
        rw [c.quotient_monomial]
        exact (coset_mul_positive _ ⟨positiveTorusMap r u, ⟨u, rfl⟩⟩).symm⟩,
      ⟨p.2.val, p.2.property, rfl⟩⟩
  have hmk : ∀ u z, orderedMk (make (u, z)) = z := by
    intro u z
    conv_rhs => rw [← (D.labels A B).symm_apply_apply z]
    change orderedMk (make (u, z)) =
      orderedMk (monomialPair c (D.labels A B z).1 (D.labels A B z).2)
    apply Quotient.sound
    exact ⟨(⟨positiveTorusMap r u, ⟨u, rfl⟩⟩ : PositiveTorus r)⁻¹,
      by
        change torusMonomial r (D.labels A B z).1.val =
          (torusMonomial r (D.labels A B z).1.val * positiveTorusMap r u) *
            (positiveTorusMap r u)⁻¹
        simp,
      by rw [c.fixes]; rfl⟩
  have hinj : Function.Injective make := by
    rintro ⟨u, z⟩ ⟨v, w⟩ eq
    have hzw : z = w := (hmk u z).symm.trans ((congrArg orderedMk eq).trans (hmk v w))
    subst w
    have hu := congrArg (fun p : OrderedRepresentatives c A B ↦ p.val.1) eq
    exact Prod.ext (positiveMap_injective r (mul_left_cancel hu)) rfl
  have hsurj : Function.Surjective make := by
    intro p
    obtain ⟨⟨_, u, rfl⟩, hu⟩ := loop_factor c p.val.1
    refine ⟨(u, orderedMk p), Subtype.ext (Prod.ext hu.symm ?_)⟩
    exact c.lattice.apply_symm_apply p.val.2
  exact ⟨Equiv.ofBijective make ⟨hinj, hsurj⟩, fun u z ↦ ⟨rfl, hmk u z⟩⟩

open private singletonOpen singletonSectionsIso
  sectionsOn_preserves_product productProjection_isIso skyscraper_counit_isIso
  identityJetEquivariance trivialEquivariance_unique jetEquivariance_ext
  inverseImageStalkMap_naturality
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusPerverse
open private skyscrapersProjection directImageGerm
  from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusOrderedConvolution
open private stalkPushforward_naturality from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

private theorem skyscrapersProjection_isIso (X : TopCat.{0}) [DiscreteTopology X]
    {C : Type*} [Category C] (F : X → C ⥤ Coeff.{0}) (x : X) (V : C) :
    IsIso (skyscrapersProjection X F x V) := by
  let Fs := fun y : X ↦ (skyscraperSheafFunctor y).obj ((F y).obj V)
  let U := singletonOpen x
  let ev := sectionsOn U
  have := sectionsOn_preserves_product U Fs
  have hπ : IsIso (Pi.π (fun j ↦ ev.obj (Fs j)) x) :=
    productProjection_isIso _ _ fun j hj ↦ isTerminalSkyscraperSheafObjObjOfNotMem
      (U := op U) (show j ∉ U from hj)
  have he : IsIso (ev.map (Pi.π Fs x)) := by
    rw [← piComparison_comp_π ev Fs x]
    infer_instance
  have hs := (NatIso.isIso_map_iff (singletonSectionsIso x) (Pi.π Fs x)).mp he
  have hc := skyscraper_counit_isIso x ((F x).obj V)
  change IsIso ((stalk x).map (Pi.π Fs x) ≫
    (stalkSkyscraperSheafAdjunction x).counit.app ((F x).obj V))
  infer_instance

@[reassoc]
private theorem skyscrapersProjection_naturality (X : TopCat.{0})
    {C : Type*} [Category C] (F : X → C ⥤ Coeff.{0}) (x : X) {V W : C} (f : V ⟶ W) :
    (stalk x).map ((skyscrapers X F).map f) ≫ skyscrapersProjection X F x W =
      skyscrapersProjection X F x V ≫ (F x).map f := by
  dsimp only [skyscrapersProjection, id]
  rw [← Functor.map_comp_assoc]
  change (stalk x).map (CategoryTheory.Limits.Pi.map _ ≫ Pi.π _ x) ≫ _ = _
  rw [Pi.map_π, Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg ((stalk x).map (Pi.π _ x) ≫ ·)
    ((stalkSkyscraperSheafAdjunction x).counit.naturality ((F x).map f))

private def labelDescent (D : OrderedGeometry r) (A B : Set (Labels r)) :
    exteriorOnLabels A B ⋙ inverseImage (D.labelMap A B) ≅ descendedExterior D A B := by
  let X := D.space A B
  let Y := OrderedGeometry.labelSpace A B
  let f := D.labelMap A B
  let LF : Y → Families r × Families r ⥤ Coeff.{0} :=
    fun p ↦ exteriorAt p.1.val p.2.val
  let F := skyscrapers Y LF
  haveI : DiscreteTopology X := ⟨rfl⟩
  haveI : DiscreteTopology Y := ⟨rfl⟩
  let adj := fun x : X ↦ stalkSkyscraperSheafAdjunction (C := Coeff.{0}) x
  let m (x : X) (V : Families r × Families r) :=
    (inverseImageStalkIso f (F.obj V) x).inv ≫ skyscrapersProjection Y LF (f x) V
  let η : F ⋙ inverseImage f ⟶ descendedExterior D A B :=
    { app V := Pi.lift fun x : X ↦ (adj x).homEquiv _ _ (m x V)
      naturality V W v := by
        apply Pi.hom_ext
        intro x
        simp only [Functor.comp_map, Category.assoc, Pi.lift_comp_π,
          descendedExterior, skyscrapers, Pi.map_π, Pi.lift_comp_π_assoc]
        erw [← (adj x).homEquiv_naturality_left, ← (adj x).homEquiv_naturality_right]
        congr 1
        change (stalk x).map ((inverseImage f).map (F.map v)) ≫ m x W =
          m x V ≫ (LF (f x)).map v
        dsimp only [m]
        rw [Category.assoc, ← skyscrapersProjection_naturality]
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        apply (cancel_epi (inverseImageStalkIso f (F.obj V) x).hom).mp
        simp only [Iso.hom_inv_id_assoc]
        change inverseImageStalkMap f (F.obj V) x ≫
          (stalk x).map ((inverseImage f).map (F.map v)) ≫
            (inverseImageStalkIso f (F.obj W) x).inv = _
        erw [← Category.assoc, ← inverseImageStalkMap_naturality f (F.map v) x]
        change (stalk (f x)).map (F.map v) ≫ (inverseImageStalkIso f (F.obj W) x).hom ≫
          (inverseImageStalkIso f (F.obj W) x).inv = (stalk (f x)).map (F.map v)
        simp
      }
  refine @asIso _ _ _ _ η (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ η ?_)
  intro V
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  let proj := skyscrapersProjection X (fun y ↦ LF (f y)) x V
  have h : (stalk x).map (η.app V) ≫ proj = m x V := by
    change (stalk x).map (η.app V) ≫ (stalk x).map (Pi.π _ x) ≫
      (adj x).counit.app _ = _
    rw [← Functor.map_comp_assoc]
    change (stalk x).map (Pi.lift _ ≫ Pi.π _ x) ≫ _ = _
    rw [Pi.lift_comp_π]
    let adjX := adj x
    let L := TopCat.Sheaf.forget Coeff.{0} X ⋙ TopCat.Presheaf.stalkFunctor Coeff.{0} x
    let hX := (adjX.homEquiv _ _ (m x V))
    change L.map hX ≫ adjX.counit.app _ = m x V
    exact (adjX.homEquiv_counit _ _ hX).symm.trans
      ((adjX.homEquiv _ _).symm_apply_apply _)
  haveI : IsIso proj := skyscrapersProjection_isIso X _ x V
  haveI : IsIso (m x V) := by
    have := skyscrapersProjection_isIso Y LF (f x) V
    dsimp only [m]
    infer_instance
  haveI : IsIso ((stalk x).map (η.app V) ≫ proj) := h ▸ inferInstance
  change IsIso ((stalk x).map (η.app V))
  exact IsIso.of_isIso_comp_right _ proj

private def exteriorDescent (D : OrderedGeometry r) (c : ContinuousJets r)
    (hc : ∀ k, @ConnectedSpace (PositiveJet r k) (positiveJetTopology r k)) :
    ExteriorDescent D c where
  compare A B k :=
    Functor.isoWhiskerRight (labelDescent D A B).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (inverseImageComposition (D.jetCover c A B k) (D.labelMap A B)).symm
  datum A B V W := identityJetEquivariance _ _ _
  trivial _ _ _ _ _ _ := rfl
  unique A B V W v := by
    apply jetEquivariance_ext
    funext k hk
    haveI : DiscreteTopology (D.space A B) := ⟨rfl⟩
    let H := (jetSystem r c).group k
    haveI : ConnectedSpace H.space := hc k
    exact trivialEquivariance_unique H (Iso.refl _) (v.datum k hk)
  stalk A B V W z := by
    haveI : DiscreteTopology (D.space A B) := ⟨rfl⟩
    exact skyscrapersProjection_isIso _ _ z (V, W)

/-- Sections of a sheaf on a discrete open set are specified by all their germs. -/
private def sectionsGermsIso {X : TopCat.{0}} [DiscreteTopology X] (F : Sheaves X)
    (U : Opens X) : F.obj.obj (op U) ≅ ∏ᶜ fun x : U ↦ (stalk x.val).obj F := by
  let T (x : U) := (stalk x.val).obj F
  let g : F.obj.obj (op U) ⟶ ModuleCat.of ℚ (∀ x : U, T x) :=
    ModuleCat.ofHom (LinearMap.pi fun x : U ↦ (F.presheaf.germ U x x.property).hom)
  have hg : Function.Bijective g := by
    constructor
    · intro u v h
      apply TopCat.Presheaf.section_ext F U
      exact fun x hx ↦ congrFun h ⟨x, hx⟩
    · intro v
      let S (x : U) := singletonOpen x.val
      have cover : iSup S = U := by
        apply SetLike.ext
        intro x
        rw [Opens.mem_iSup]
        exact ⟨fun ⟨i, hi⟩ ↦ (show x = i.val from hi).symm ▸ i.property,
          fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
      let t (x : U) : F.obj.obj (op (S x)) :=
        ((singletonSectionsIso x.val).app F).inv (v x)
      have ht : F.presheaf.IsCompatible S t := by
        intro i j
        by_cases h : i = j
        · subst j
          rfl
        · have he : S i ⊓ S j = ⊥ := by
            ext x
            change (x = i.val ∧ x = j.val) ↔ False
            constructor
            · rintro ⟨rfl, e⟩
              exact h (Subtype.ext e)
            · exact False.elim
          have hz : IsZero (F.obj.obj (op (S i ⊓ S j))) :=
            (isZero_zero Coeff.{0}).of_iso
              ((F.isTerminalOfEqEmpty he).uniqueUpToIso (isZero_zero Coeff.{0}).isTerminal)
          have := ModuleCat.subsingleton_of_isZero hz
          exact Subsingleton.elim _ _
      obtain ⟨s, hs, _⟩ := F.existsUnique_gluing S t ht
      let v' : F.obj.obj (op U) := F.obj.map (homOfLE cover.ge).op s
      refine ⟨v', ?_⟩
      funext x
      have hle : S x ≤ U := fun y hy ↦ (show y = x.val from hy).symm ▸ x.property
      have hv : F.obj.map (homOfLE hle).op v' = t x := by
        have heq : (homOfLE cover.ge).op ≫ (homOfLE hle).op =
            (Opens.leSupr S x).op := Subsingleton.elim _ _
        change (F.obj.map (homOfLE cover.ge).op ≫ F.obj.map (homOfLE hle).op) s = _
        rw [← Functor.map_comp, heq]
        exact hs x
      change F.presheaf.germ U x x.property v' = v x
      rw [← F.presheaf.germ_res_apply (homOfLE hle) x.val (Set.mem_singleton _), hv]
      change (((singletonSectionsIso x.val).app F).inv ≫
        ((singletonSectionsIso x.val).app F).hom) (v x) = _
      simp
  exact (LinearEquiv.ofBijective g.hom hg).toModuleIso ≪≫ (ModuleCat.piIsoPi T).symm

private theorem sectionsGermsIso_π {X : TopCat.{0}} [DiscreteTopology X]
    (F : Sheaves X) (U : Opens X) (x : U) :
    (sectionsGermsIso F U).hom ≫ Pi.π _ x = F.presheaf.germ U x x.property := by
  dsimp only [sectionsGermsIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, ModuleCat.piIsoPi_inv_kernel_ι]
  ext t
  rfl

private def directImageStalkIso {X Y : TopCat.{0}} [DiscreteTopology X] [DiscreteTopology Y]
    (f : X ⟶ Y) (F : Sheaves X) (y : Y) :
    (stalk y).obj ((directImage f).obj F) ≅
      ∏ᶜ fun x : {x : X // f x = y} ↦ (stalk x.val).obj F :=
  ((singletonSectionsIso y).app ((directImage f).obj F)).symm ≪≫
    sectionsGermsIso F ((Opens.map f).obj (singletonOpen y))

private theorem directImageStalkIso_π {X Y : TopCat.{0}} [DiscreteTopology X] [DiscreteTopology Y]
    (f : X ⟶ Y) (F : Sheaves X) (y : Y) (x : X) (h : f x = y) :
    (directImageStalkIso f F y).hom ≫ Pi.π _ ⟨x, h⟩ =
      eqToHom (congrArg (fun z ↦ (stalk z).obj ((directImage f).obj F)) h.symm) ≫
        directImageGerm f F x := by
  subst y
  simp only [eqToHom_refl, Category.id_comp, directImageStalkIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  apply (cancel_epi ((singletonSectionsIso (f x)).app ((directImage f).obj F)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  let U := (Opens.map f).obj (singletonOpen (f x))
  exact (sectionsGermsIso_π F U (⟨x, rfl⟩ : U)).trans
    (TopCat.Presheaf.stalkPushforward_germ Coeff.{0} f F.presheaf
      (singletonOpen (f x)) x rfl).symm

private abbrev SupportedFiber (A B : Set (Labels r)) (n : Labels r) :=
  {p : SumFiber n // p.val.1 ∈ A ∧ p.val.2 ∈ B}

private def geometricIndex (D : OrderedGeometry r) (A B : Set (Labels r)) (n : Labels r) :
    SupportedFiber A B n ≃ {z : D.space A B // D.terminal A B z = monomialPoint r n} := by
  let e := D.labels A B
  have hm : Function.Injective (monomialPoint r) := by
    have he : (D.coordinates.lattice : Labels r → torusSpace r) = monomialPoint r :=
      funext D.coordinates.lattice_monomial
    rw [← he]
    exact D.coordinates.lattice.injective
  refine
    { toFun := fun p ↦ ⟨e.symm (⟨p.val.val.1, p.property.1⟩, ⟨p.val.val.2, p.property.2⟩), ?_⟩
      invFun := fun p ↦ ⟨⟨((e p.val).1.val, (e p.val).2.val), ?_⟩,
        (e p.val).1.property, (e p.val).2.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · let q : A × B := (⟨p.val.val.1, p.property.1⟩, ⟨p.val.val.2, p.property.2⟩)
    exact (D.terminal_label (e.symm q)).trans
      ((congrArg (fun z : A × B ↦ monomialPoint r (z.1.val + z.2.val))
        (e.apply_symm_apply q)).trans (congrArg (monomialPoint r) p.val.property))
  · exact hm ((D.terminal_label p.val).symm.trans p.property)
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    change ((e (e.symm _)).1.val, (e (e.symm _)).2.val) = p.val.val
    rw [e.apply_symm_apply]
  · intro z
    apply Subtype.ext
    exact e.symm_apply_apply z.val

private abbrev stagePushforward (D : OrderedGeometry r) (A B : Set (Labels r)) :=
  descendedExterior D A B ⋙ directImage (D.terminal A B)

private abbrev stageFiber (D : OrderedGeometry r) (A B : Set (Labels r)) (n : Labels r) :=
  stagePushforward D A B ⋙ stalk (monomialPoint r n)

private abbrev tensorAt (V W : Families r) {n : Labels r} (p : SumFiber n) :=
  fiber V p.val.1 ⊗ fiber W p.val.2

private def stageFiberProjection (D : OrderedGeometry r) (A B : Set (Labels r))
    (V W : Families r) (n : Labels r) (p : SupportedFiber A B n) :
    (stageFiber D A B n).obj (V, W) ⟶ tensorAt V W p.val := by
  let z := geometricIndex D A B n p
  have hz : ((D.labels A B z.val).1.val, (D.labels A B z.val).2.val) = p.val.val := by
    change (((D.labels A B) ((D.labels A B).symm _)).1.val,
      ((D.labels A B) ((D.labels A B).symm _)).2.val) = _
    rw [Equiv.apply_symm_apply]
  exact orderedFiberProjection D A B V W n p.val z.val z.property hz

private def stageFiberProductIso (D : OrderedGeometry r) (A B : Set (Labels r))
    (g : StageGeometry r) (V W : Families r) (n : Labels r) :
    (stageFiber D A B n).obj (V, W) ≅ ∏ᶜ fun p : SupportedFiber A B n ↦ tensorAt V W p.val := by
  let X := D.space A B
  let f := D.terminal A B
  let F := (descendedExterior D A B).obj (V, W)
  let L (x : X) := exteriorAt (D.labels A B x).1.val (D.labels A B x).2.val
  let e := geometricIndex D A B n
  haveI : DiscreteTopology X := ⟨rfl⟩
  haveI : DiscreteTopology (torusSpace r) := g.discrete
  refine directImageStalkIso f F (monomialPoint r n) ≪≫
    (Pi.whiskerEquiv e (fun p ↦ ?_)).symm
  haveI := skyscrapersProjection_isIso X L (e p).val (V, W)
  refine asIso (skyscrapersProjection X L (e p).val (V, W)) ≪≫ eqToIso ?_
  let T (q : Labels r × Labels r) := fiber V q.1 ⊗ fiber W q.2
  change T (_, _) = T p.val.val
  apply congrArg T
  change (((D.labels A B) ((D.labels A B).symm _)).1.val,
    ((D.labels A B) ((D.labels A B).symm _)).2.val) = _
  rw [Equiv.apply_symm_apply]

private theorem stageFiberProductIso_π (D : OrderedGeometry r) (A B : Set (Labels r))
    (g : StageGeometry r) (V W : Families r) (n : Labels r) (p : SupportedFiber A B n) :
    (stageFiberProductIso D A B g V W n).hom ≫ Pi.π _ p =
      stageFiberProjection D A B V W n p := by
  letI : DiscreteTopology (D.space A B) := ⟨rfl⟩
  letI : DiscreteTopology (torusSpace r) := g.discrete
  dsimp only [stageFiberProductIso, Iso.trans_hom, Iso.symm_hom, Pi.whiskerEquiv,
    stageFiberProjection, orderedFiberProjection, asIso_hom, eqToIso.hom, id]
  rw [Category.assoc, Pi.map'_comp_π, ← Category.assoc, directImageStalkIso_π]

private def restrictProduct {I : Type} (F : I → Coeff.{0}) (S : Set I) :
    (∏ᶜ F) ⟶ ∏ᶜ fun i : S ↦ F i.val :=
  Pi.lift fun i ↦ Pi.π F i.val

private theorem restrictProduct_isIso {I : Type} (F : I → Coeff.{0}) (S : Set I)
    (hS : ∀ i, i ∉ S → IsZero (F i)) : IsIso (restrictProduct F S) := by
  let g : (∏ᶜ fun i : S ↦ F i.val) ⟶ ∏ᶜ F :=
    Pi.lift fun i ↦ if h : i ∈ S then Pi.π (fun i : S ↦ F i.val) ⟨i, h⟩ else 0
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply Pi.hom_ext
    intro i
    by_cases h : i ∈ S
    · simp [restrictProduct, g, h]
    · exact (hS i h).eq_of_tgt _ _
  · apply Pi.hom_ext
    intro i
    simp [restrictProduct, g, i.property]

private def restrictCoproduct {I : Type} (F : I → Coeff.{0}) (S : Set I) :
    (∐ F) ⟶ ∐ fun i : S ↦ F i.val :=
  Sigma.desc fun i ↦
    if h : i ∈ S then Sigma.ι (fun i : S ↦ F i.val) ⟨i, h⟩ else 0

private theorem restrictCoproduct_isIso {I : Type} (F : I → Coeff.{0}) (S : Set I)
    (hS : ∀ i, i ∉ S → IsZero (F i)) : IsIso (restrictCoproduct F S) := by
  let g : (∐ fun i : S ↦ F i.val) ⟶ ∐ F := Sigma.desc fun i ↦ Sigma.ι F i.val
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply Sigma.hom_ext
    intro i
    by_cases h : i ∈ S
    · simp [restrictCoproduct, g, h]
    · exact (hS i h).eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    simp [restrictCoproduct, g, i.property]

private def finiteSumProductIso {I : Type} (F : I → Coeff.{0}) (S : Set I)
    (hf : S.Finite) (hS : ∀ i, i ∉ S → IsZero (F i)) : (∐ F) ≅ ∏ᶜ F := by
  haveI := hf.to_subtype
  haveI := restrictProduct_isIso F S hS
  haveI := restrictCoproduct_isIso F S hS
  exact asIso (restrictCoproduct F S) ≪≫
    (biproductIso (fun i : S ↦ F i.val)).symm ≪≫ (asIso (restrictProduct F S)).symm

@[reassoc]
private theorem finiteSumProductIso_same {I : Type} (F : I → Coeff.{0}) (S : Set I)
    (hf : S.Finite) (hS : ∀ i, i ∉ S → IsZero (F i)) (i : I) :
    Sigma.ι F i ≫ (finiteSumProductIso F S hf hS).hom ≫ Pi.π F i = 𝟙 (F i) := by
  by_cases hi : i ∈ S
  · haveI := hf.to_subtype
    haveI := restrictProduct_isIso F S hS
    let B := biproductIso (fun i : S ↦ F i.val)
    have ht : inv (restrictProduct F S) ≫ Pi.π F i = Pi.π _ (⟨i, hi⟩ : S) := by
      apply (cancel_epi (restrictProduct F S)).mp
      simp [restrictProduct]
    have hb : Sigma.ι (fun i : S ↦ F i.val) (⟨i, hi⟩ : S) ≫ B.inv ≫
        Pi.π (fun i : S ↦ F i.val) (⟨i, hi⟩ : S) = 𝟙 _ := by simp [B, biproductIso]
    simpa [finiteSumProductIso, restrictCoproduct, hi, ht, Category.assoc] using hb
  · exact (hS i hi).eq_of_src _ _

private theorem finiteSumProductIso_other {I : Type} (F : I → Coeff.{0}) (S : Set I)
    (hf : S.Finite) (hS : ∀ i, i ∉ S → IsZero (F i)) (i j : I) (h : i ≠ j) :
    Sigma.ι F i ≫ (finiteSumProductIso F S hf hS).hom ≫ Pi.π F j = 0 := by
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · haveI := hf.to_subtype
      haveI := restrictProduct_isIso F S hS
      let B := biproductIso (fun i : S ↦ F i.val)
      have ht : inv (restrictProduct F S) ≫ Pi.π F j = Pi.π _ (⟨j, hj⟩ : S) := by
        apply (cancel_epi (restrictProduct F S)).mp
        simp [restrictProduct]
      have h' : (⟨i, hi⟩ : S) ≠ ⟨j, hj⟩ := fun e ↦ h (congrArg Subtype.val e)
      have hb : Sigma.ι (fun i : S ↦ F i.val) (⟨i, hi⟩ : S) ≫ B.inv ≫
          Pi.π (fun i : S ↦ F i.val) (⟨j, hj⟩ : S) = 0 := by simp [B, biproductIso, h']
      simpa [finiteSumProductIso, restrictCoproduct, hi, ht, Category.assoc] using hb
    · exact (hS j hj).eq_of_tgt _ _
  · exact (hS i hi).eq_of_src _ _

private theorem tensor_isZero_left {X Y : Coeff.{0}} (h : IsZero X) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← id_tensorHom_id, (IsZero.iff_id_eq_zero _).mp h,
    MonoidalPreadditive.zero_tensor]

private theorem tensor_isZero_right {X Y : Coeff.{0}} (h : IsZero Y) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← id_tensorHom_id, (IsZero.iff_id_eq_zero _).mp h,
    MonoidalPreadditive.tensor_zero]

private theorem supportedFiber_finite {A B : Set (Labels r)} {n : Labels r}
    (hA : A.Finite) (hB : B.Finite) : ({p : SumFiber n | p.val.1 ∈ A ∧ p.val.2 ∈ B} : Set (SumFiber n)).Finite := by
  haveI := hA.to_subtype
  haveI := hB.to_subtype
  have hfin : Finite (SupportedFiber A B n) := Finite.of_injective
    (fun p : SupportedFiber A B n ↦ ((⟨p.val.val.1, p.property.1⟩ : A), (⟨p.val.val.2, p.property.2⟩ : B)))
    (fun p q e ↦ Subtype.ext (Subtype.ext (congrArg
      (fun x : A × B ↦ (x.1.val, x.2.val)) e)))
  exact @Set.toFinite _ _ hfin

private theorem tensor_zero_outside (V W : Families r) {A B : Set (Labels r)}
    (hV : familySupport V ⊆ A) (hW : familySupport W ⊆ B) (n : Labels r)
    (p : SumFiber n) (hp : ¬ (p.val.1 ∈ A ∧ p.val.2 ∈ B)) : IsZero (tensorAt V W p) := by
  by_cases h : p.val.1 ∈ A
  · exact tensor_isZero_right (Classical.not_not.mp fun hh ↦ hp ⟨h, hW hh⟩)
  · exact tensor_isZero_left (Classical.not_not.mp fun hh ↦ h (hV hh))

private theorem module_injective (V : Coeff.{0}) : Injective V := by
  constructor
  intro X Y g f hf
  obtain ⟨s, hs⟩ := f.hom.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp hf))
  refine ⟨ModuleCat.ofHom (g.hom.comp s), ?_⟩
  apply ModuleCat.hom_ext
  change (g.hom.comp s).comp f.hom = g.hom
  rw [LinearMap.comp_assoc, hs, LinearMap.comp_id]

private theorem sheaf_injective_discrete (X : TopCat.{0}) [DiscreteTopology X]
    (F : Sheaves X) : Injective F := by
  let K (x : X) := (skyscraperSheafFunctor x).obj ((stalk x).obj F)
  let m : F ⟶ ∏ᶜ K :=
    Pi.lift fun x ↦ (stalkSkyscraperSheafAdjunction x).unit.app F
  have hm : IsIso m := (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso m).mpr (by
    intro x
    let T (z : X) : Sheaves X ⥤ Coeff.{0} := stalk z
    let p := skyscrapersProjection X T x F
    haveI : IsIso p := skyscrapersProjection_isIso X T x F
    have he : (stalk x).map m ≫ p = 𝟙 _ := by
      let a := stalkSkyscraperSheafAdjunction (C := Coeff.{0}) x
      change (stalk x).map m ≫ (stalk x).map (Pi.π K x) ≫ a.counit.app _ = _
      rw [← Functor.map_comp_assoc]
      change (stalk x).map (Pi.lift _ ≫ Pi.π K x) ≫ a.counit.app _ = _
      rw [Pi.lift_comp_π]
      exact a.left_triangle_components F
    haveI : IsIso ((stalk x).map m ≫ p) := he ▸ inferInstance
    change IsIso ((stalk x).map m)
    exact IsIso.of_isIso_comp_right _ p)
  haveI (x : X) : Injective (K x) := by
    haveI : Injective ((stalk x).obj F) := module_injective _
    haveI : PreservesMonomorphisms (TopCat.Sheaf.forget Coeff.{0} X ⋙
        TopCat.Presheaf.stalkFunctor Coeff.{0} x) :=
      ⟨fun f _ ↦ TopCat.Presheaf.stalk_mono_of_mono f x⟩
    exact Injective.injective_of_adjoint (stalkSkyscraperSheafAdjunction x) _
  exact Injective.of_iso (asIso m).symm inferInstance

private def singlePlus (C : Type*) [Category C] [HasZeroObject C] [HasZeroMorphisms C] :
    C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (HomologicalComplex.single C (.up ℤ) 0)
    (fun _ ↦ ⟨0, inferInstance⟩)

private def singlePlusMap {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    singlePlus C ⋙ F.mapCochainComplexPlus ≅ F ⋙ singlePlus D :=
  ((CochainComplex.Plus.fullyFaithfulι D).whiskeringRight C).preimageIso
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0)

private def singlePlusQIso (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] :
    singlePlus C ⋙ DerivedCategory.Plus.Q ≅ DerivedCategory.Plus.singleFunctor C 0 :=
  (ObjectProperty.fullyFaithfulι _ |>.whiskeringRight C).preimageIso
    (Functor.isoWhiskerLeft (singlePlus C) (DerivedCategory.Plus.QCompιIso C))

private def derivedImageSingleIso {X Y : TopCat.{0}} [DiscreteTopology X] (f : X ⟶ Y) :
    DerivedCategory.Plus.singleFunctor (Sheaves X) 0 ⋙ derivedDirectImage f ≅
      directImage f ⋙ DerivedCategory.Plus.singleFunctor (Sheaves Y) 0 := by
  let C := Sheaves X
  let D := Sheaves Y
  let F := directImage f
  let J : C ⥤ InjectiveObject C :=
    ObjectProperty.lift _ (𝟭 C) (sheaf_injective_discrete X)
  let I := InjectiveObject.ι C
  let U := F.rightDerivedFunctorPlusUnit
  have hu (A : C) : IsIso (U.app ((singlePlus C).obj A)) := by
    let L := (singlePlus (InjectiveObject C)).obj (J.obj A)
    let L' := I.mapCochainComplexPlus.obj L
    let i : L' ≅ (singlePlus C).obj A := (singlePlusMap I).app (J.obj A)
    haveI : IsIso (U.app L') := inferInstanceAs
      (IsIso (F.rightDerivedFunctorPlusUnit.app (I.mapCochainComplexPlus.obj L)))
    exact (NatTrans.isIso_app_iff_of_iso U i).mp inferInstance
  let u := Functor.whiskerLeft (singlePlus C) U
  haveI : IsIso u := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ u hu
  exact Functor.isoWhiskerRight (singlePlusQIso C).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    (asIso u).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singlePlusMap F) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (singlePlusQIso D)

private theorem finiteDirectImage (D : OrderedGeometry r) : FiniteDirectImage D := by
  intro A B _ _
  haveI : DiscreteTopology (D.space A B) := ⟨rfl⟩
  exact ⟨derivedImageSingleIso (D.terminal A B)⟩

private theorem directImageGerm_nat {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F G : Sheaves X} (v : F ⟶ G) (y : Y) (x : X) (h : f x = y) :
    (stalk y).map ((directImage f).map v) ≫
        eqToHom (congrArg (fun z ↦ (stalk z).obj ((directImage f).obj G)) h.symm) ≫
        directImageGerm f G x =
      eqToHom (congrArg (fun z ↦ (stalk z).obj ((directImage f).obj F)) h.symm) ≫
        directImageGerm f F x ≫ (stalk x).map v := by
  subst y
  simp only [eqToHom_refl, Category.id_comp]
  exact stalkPushforward_naturality f v.hom x

private theorem exteriorAt_cast (V W : Families r × Families r) (v : V ⟶ W)
    {p q : Labels r × Labels r} (h : p = q) :
    (exteriorAt p.1 p.2).map v ≫
        eqToHom (congrArg (fun z : Labels r × Labels r ↦ (exteriorAt z.1 z.2).obj W) h) =
      eqToHom (congrArg (fun z : Labels r × Labels r ↦ (exteriorAt z.1 z.2).obj V) h) ≫
        (exteriorAt q.1 q.2).map v := by subst q; simp

private theorem composeThreeNaturality {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    {a : A₀ ⟶ B₀} {b : A₁ ⟶ B₁} {c : A₂ ⟶ B₂} {d : A₃ ⟶ B₃}
    {f : A₀ ⟶ A₁} {g : A₁ ⟶ A₂} {h : A₂ ⟶ A₃}
    {f' : B₀ ⟶ B₁} {g' : B₁ ⟶ B₂} {h' : B₂ ⟶ B₃}
    (e₁ : a ≫ f' = f ≫ b) (e₂ : b ≫ g' = g ≫ c) (e₃ : c ≫ h' = h ≫ d) :
    a ≫ (f' ≫ g' ≫ h') = (f ≫ g ≫ h) ≫ d := by
  rw [← Category.assoc a, e₁, Category.assoc, ← Category.assoc b, e₂,
    Category.assoc, e₃]
  simp only [Category.assoc]

private theorem orderedFiberProjection_nat (D : OrderedGeometry r) (A B : Set (Labels r))
    (n : Labels r) (p : SumFiber n) (z : D.space A B)
    (hz : D.terminal A B z = monomialPoint r n)
    (h : ((D.labels A B z).1.val, (D.labels A B z).2.val) = p.val)
    {V W : Families r × Families r} (v : V ⟶ W) :
    (stageFiber D A B n).map v ≫ orderedFiberProjection D A B W.1 W.2 n p z hz h =
      orderedFiberProjection D A B V.1 V.2 n p z hz h ≫ (exteriorAt p.val.1 p.val.2).map v := by
  let f := D.terminal A B
  let F := descendedExterior D A B
  let y := monomialPoint r n
  let L (x : D.space A B) := exteriorAt (D.labels A B x).1.val (D.labels A B x).2.val
  let m (U : Families r × Families r) :=
    eqToHom (congrArg (fun t ↦ (stalk t).obj ((directImage f).obj (F.obj U))) hz.symm) ≫
      directImageGerm f (F.obj U) z
  let e (U : Families r × Families r) :=
    eqToHom (congrArg (fun q : Labels r × Labels r ↦ (exteriorAt q.1 q.2).obj U) h)
  have hm : (stalk y).map ((directImage f).map (F.map v)) ≫ m W =
      m V ≫ (stalk z).map (F.map v) := by
    exact (Category.assoc _ _ _).symm.trans
      ((directImageGerm_nat f (F.map v) y z hz).trans (Category.assoc _ _ _).symm)
  have hk : (stalk z).map (F.map v) ≫ skyscrapersProjection _ L z W =
      skyscrapersProjection _ L z V ≫ (L z).map v :=
    skyscrapersProjection_naturality _ L z v
  have he : (L z).map v ≫ e W = e V ≫ (exteriorAt p.val.1 p.val.2).map v :=
    exteriorAt_cast V W v h
  exact composeThreeNaturality hm hk he

private theorem stageFiberProjection_nat (D : OrderedGeometry r) (A B : Set (Labels r))
    (n : Labels r) (p : SupportedFiber A B n) {V W : Families r × Families r} (v : V ⟶ W) :
    (stageFiber D A B n).map v ≫ stageFiberProjection D A B W.1 W.2 n p =
      stageFiberProjection D A B V.1 V.2 n p ≫ (exteriorAt p.val.val.1 p.val.val.2).map v :=
  orderedFiberProjection_nat D A B n p.val _ (geometricIndex D A B n p).property (by
    change (((D.labels A B) ((D.labels A B).symm _)).1.val,
      ((D.labels A B) ((D.labels A B).symm _)).2.val) = _
    rw [Equiv.apply_symm_apply]) v

private abbrev indexedFiberProduct (n : Labels r) {I : Type} (idx : I → SumFiber n) :
    Families r × Families r ⥤ Coeff.{0} where
  obj V := ∏ᶜ fun p : I ↦ tensorAt V.1 V.2 (idx p)
  map v := Limits.Pi.map fun p : I ↦ (exteriorAt (idx p).val.1 (idx p).val.2).map v
  map_id V := by
    apply Pi.hom_ext
    intro i
    simp only [Pi.map_π, CategoryTheory.Functor.map_id]
    let T (p : I) := tensorAt V.1 V.2 (idx p)
    change Pi.π T i ≫ 𝟙 (T i) = Pi.π T i
    exact Category.comp_id _
  map_comp v w := by
    apply Pi.hom_ext
    intro i
    simp only [Pi.map_π, Category.assoc, Pi.map_π_assoc]
    change _ ≫ (exteriorAt _ _).map (v ≫ w) =
      _ ≫ (exteriorAt _ _).map v ≫ (exteriorAt _ _).map w
    rw [CategoryTheory.Functor.map_comp]

private def stageFiberProduct (D : OrderedGeometry r) (g : StageGeometry r)
    (A B : Set (Labels r)) (n : Labels r) :
    stageFiber D A B n ≅ indexedFiberProduct n (fun p : SupportedFiber A B n ↦ p.val) :=
  NatIso.ofComponents (fun V ↦ stageFiberProductIso D A B g V.1 V.2 n) (fun {V W} v ↦ by
    let T (X : Families r × Families r) (p : SupportedFiber A B n) := tensorAt X.1 X.2 p.val
    let a (p : SupportedFiber A B n) : T V p ⟶ T W p :=
      (exteriorAt p.val.val.1 p.val.val.2).map v
    apply Pi.hom_ext
    intro p
    change ((stageFiber D A B n).map v ≫ (stageFiberProductIso D A B g W.1 W.2 n).hom) ≫ Pi.π (T W) p =
      ((stageFiberProductIso D A B g V.1 V.2 n).hom ≫ Limits.Pi.map a) ≫ Pi.π (T W) p
    rw [Category.assoc, stageFiberProductIso_π, Category.assoc, Pi.map_π,
      ← Category.assoc, stageFiberProductIso_π]
    exact stageFiberProjection_nat D A B n p v)

private def restrictFiberProduct (A B : Set (Labels r)) (n : Labels r) :
    indexedFiberProduct n id ⟶ indexedFiberProduct n (fun p : SupportedFiber A B n ↦ p.val) where
  app V := restrictProduct (tensorAt V.1 V.2) _
  naturality V W v := by
    let T (X : Families r × Families r) := tensorAt X.1 X.2 (n := n)
    let S : Set (SumFiber n) := {p | p.val.1 ∈ A ∧ p.val.2 ∈ B}
    let a (p : SumFiber n) : T V p ⟶ T W p := (exteriorAt p.val.1 p.val.2).map v
    apply Pi.hom_ext
    intro p
    change ((Limits.Pi.map a) ≫ restrictProduct (T W) S) ≫ Pi.π _ p =
      (restrictProduct (T V) S ≫ Limits.Pi.map (fun q : SupportedFiber A B n ↦ a q.val)) ≫ Pi.π _ p
    simp only [Category.assoc, restrictProduct, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
      Pi.map_π]

private def wholeFiberProduct (D : OrderedGeometry r) (g : StageGeometry r) (n : Labels r) :
    geometricFiber D n ≅ indexedFiberProduct n id := by
  let m := restrictFiberProduct (Set.univ : Set (Labels r)) Set.univ n
  haveI : IsIso m := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ m (fun V ↦
    restrictProduct_isIso (tensorAt V.1 V.2) _ (fun p h ↦ (h ⟨trivial, trivial⟩).elim))
  exact stageFiberProduct D g Set.univ Set.univ n ≪≫ (asIso m).symm

set_option maxHeartbeats 800000 in
private theorem wholeFiberProduct_π (D : OrderedGeometry r) (g : StageGeometry r)
    (V W : Families r) (n : Labels r) (p : SumFiber n) :
    (wholeFiberProduct D g n).hom.app (V, W) ≫ Pi.π _ p = pushforwardProjection D V W n p := by
  let q : SupportedFiber Set.univ Set.univ n := ⟨p, trivial, trivial⟩
  let m := restrictFiberProduct (Set.univ : Set (Labels r)) Set.univ n
  haveI : IsIso m := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ m (fun U ↦
    restrictProduct_isIso (tensorAt U.1 U.2) _ (fun j h ↦ (h ⟨trivial, trivial⟩).elim))
  let i := (asIso m).app (V, W)
  have h : i.inv ≫ Pi.π _ p = Pi.π _ q := by
    apply (cancel_epi i.hom).mp
    rw [Iso.hom_inv_id_assoc]
    change Pi.π _ p = restrictProduct _ _ ≫ Pi.π _ q
    rw [restrictProduct, Pi.lift_comp_π]
  change ((stageFiberProduct D g Set.univ Set.univ n).app (V, W)).hom ≫ i.inv ≫ Pi.π _ p = _
  rw [h]
  change (stageFiberProductIso D Set.univ Set.univ g V W n).hom ≫ Pi.π _ q = _
  rw [stageFiberProductIso_π]
  let z := (geometricIndex D Set.univ Set.univ n q)
  let L (x : D.Whole) : Labels r × Labels r :=
    ((D.labels Set.univ Set.univ x).1.val, (D.labels Set.univ Set.univ x).2.val)
  have hz : L z.val = p.val := by
    change (((D.labels Set.univ Set.univ) ((D.labels Set.univ Set.univ).symm _)).1.val,
      ((D.labels Set.univ Set.univ) ((D.labels Set.univ Set.univ).symm _)).2.val) = _
    rw [Equiv.apply_symm_apply]
  have he : z.val = D.wholePair p.val.1 p.val.2 := by
    apply (D.labels Set.univ Set.univ).injective
    have hL := hz.trans (D.wholePair_labels p.val.1 p.val.2).symm
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hL)) (Subtype.ext (congrArg Prod.snd hL))
  change orderedFiberProjection D Set.univ Set.univ V W n p z.val z.property hz =
    orderedFiberProjection D Set.univ Set.univ V W n p (D.wholePair p.val.1 p.val.2)
      (wholePair_terminal D n p) (D.wholePair_labels _ _)
  congr

open private perverseStalks perverseExtension perverseEquivalence extensionStalkIso
  sheafStalkFamilies sheafFamiliesEquiv
  stalkProductCounit stalkProductCounit_isIso monomialPoint_bijective
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusPerverse

private def familySum (r : ℕ) : Families r × Families r ⥤ Families r where
  obj V := Discrete.functor fun n ↦ (fiberSum n).obj V
  map v := Discrete.natTrans fun n ↦ (fiberSum n.as).map v
  map_id _ := by apply NatTrans.ext; funext n; simp
  map_comp v w := by
    apply NatTrans.ext
    funext n
    exact (fiberSum n.as).map_comp v w

private theorem finiteFamily_sum (V W : Graded r) :
    IsFiniteFamily r ((familySum r).obj (V.obj, W.obj)) := by
  let A := familySupport V.obj
  let B := familySupport W.obj
  have hA := V.property.2
  have hB := W.property.2
  constructor
  · intro n
    let T : SumFiber n → Coeff.{0} := tensorAt V.obj W.obj
    let S : Set (SumFiber n) := {p | p.val.1 ∈ A ∧ p.val.2 ∈ B}
    let hS := tensor_zero_outside V.obj W.obj (A := A) (B := B) (fun _ h ↦ h) (fun _ h ↦ h) n
    let hf := supportedFiber_finite (n := n) hA hB
    haveI : Finite S := hf.to_subtype
    haveI : IsIso (restrictCoproduct T S) := restrictCoproduct_isIso T S hS
    let e := (asIso (restrictCoproduct T S)) ≪≫
      (biproductIso (fun p : S ↦ T p.val)).symm ≪≫ ModuleCat.piIsoPi _
    haveI (p : S) : Module.Finite ℚ (T p.val) := by
      haveI := V.property.1 p.val.val.1
      haveI := W.property.1 p.val.val.2
      change Module.Finite ℚ (TensorProduct ℚ (fiber V.obj p.val.val.1) (fiber W.obj p.val.val.2))
      infer_instance
    change Module.Finite ℚ ((∐ T : Coeff.{0}) : Type)
    exact Module.Finite.of_surjective e.inv.hom ((ConcreteCategory.bijective_of_isIso e.inv).2)
  · have h : ((fun p : Labels r × Labels r ↦ p.1 + p.2) '' (A ×ˢ B)).Finite :=
      (hA.prod hB).image _
    apply h.subset
    intro n hn
    by_contra h'
    apply hn
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro p
    have ht : IsZero (tensorAt V.obj W.obj p) :=
      tensor_zero_outside V.obj W.obj (A := A) (B := B) (fun _ h ↦ h) (fun _ h ↦ h) n p
        (fun hp ↦ h' ⟨p.val, hp, p.property⟩)
    exact ht.eq_of_src _ _

private def heartSum (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Heart r g c × Heart r g c ⥤ Graded r :=
  (IsFiniteFamily r).lift ((stalkFamily r g c).prod (stalkFamily r g c) ⋙ familySum r)
    (fun VW ↦ finiteFamily_sum ((perverseStalks r g c).obj VW.1)
      ((perverseStalks r g c).obj VW.2))

private def heartFiberSumProduct (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r)
    (n : Labels r) :
    (stalkFamily r g c).prod (stalkFamily r g c) ⋙ fiberSum n ≅
      (stalkFamily r g c).prod (stalkFamily r g c) ⋙ indexedFiberProduct n id := by
  let H := (stalkFamily r g c).prod (stalkFamily r g c)
  let F (VW : Heart r g c × Heart r g c) := tensorAt (H.obj VW).1 (H.obj VW).2 (n := n)
  let S (VW : Heart r g c × Heart r g c) : Set (SumFiber n) :=
    {p | p.val.1 ∈ familySupport (H.obj VW).1 ∧ p.val.2 ∈ familySupport (H.obj VW).2}
  let hS (VW : Heart r g c × Heart r g c) : ∀ p, p ∉ S VW → IsZero (F VW p) :=
    tensor_zero_outside (H.obj VW).1 (H.obj VW).2 (fun _ h ↦ h) (fun _ h ↦ h) n
  let hfin (VW : Heart r g c × Heart r g c) : (S VW).Finite := supportedFiber_finite
    ((perverseStalks r g c).obj VW.1).property.2 ((perverseStalks r g c).obj VW.2).property.2
  refine NatIso.ofComponents (fun VW ↦ finiteSumProductIso (F VW) (S VW) (hfin VW) (hS VW)) ?_
  intro V W v
  apply Pi.hom_ext
  intro q
  apply Sigma.hom_ext
  intro p
  change Sigma.ι (F V) p ≫ Limits.Sigma.map _ ≫
      (finiteSumProductIso (F W) (S W) (hfin W) (hS W)).hom ≫ Pi.π (F W) q =
    Sigma.ι (F V) p ≫
      (finiteSumProductIso (F V) (S V) (hfin V) (hS V)).hom ≫ Limits.Pi.map _ ≫ Pi.π (F W) q
  let a (j : SumFiber n) : F V j ⟶ F W j :=
    (exteriorAt j.val.1 j.val.2).map (H.map v)
  erw [Sigma.ι_map_assoc, Pi.map_π]
  change a p ≫ Sigma.ι (F W) p ≫
      (finiteSumProductIso (F W) (S W) (hfin W) (hS W)).hom ≫ Pi.π (F W) q =
    Sigma.ι (F V) p ≫ (finiteSumProductIso (F V) (S V) (hfin V) (hS V)).hom ≫ Pi.π (F V) q ≫ a q
  by_cases h : p = q
  · subst q
    rw [finiteSumProductIso_same (F W) (S W) (hfin W) (hS W) p,
      finiteSumProductIso_same_assoc (F V) (S V) (hfin V) (hS V) p (a p),
      Category.comp_id]
  · have e₂ := congrArg (fun z ↦ z ≫ a q)
      (finiteSumProductIso_other (F V) (S V) (hfin V) (hS V) p q h)
    rw [finiteSumProductIso_other (F W) (S W) (hfin W) (hS W) p q h, Limits.comp_zero]
    simpa only [Category.assoc, Limits.zero_comp] using e₂.symm

private def sumGeometricFiber (D : OrderedGeometry r) (g : StageGeometry r)
    (c : ContinuousJets r) (n : Labels r) :
    (stalkFamily r g c).prod (stalkFamily r g c) ⋙ fiberSum n ≅
      (stalkFamily r g c).prod (stalkFamily r g c) ⋙ geometricFiber D n :=
  heartFiberSumProduct r g c n ≪≫
    Functor.isoWhiskerLeft _ (wholeFiberProduct D g n).symm

private def familiesIsoOfComponents {C : Type*} [Category C] {F G : C ⥤ Families r}
    (e : ∀ n : Labels r, F ⋙ familyAt n ≅ G ⋙ familyAt n) : F ≅ G :=
  NatIso.ofComponents
    (fun X ↦ Discrete.natIso (fun n ↦ (e n.as).app X))
    (fun {X Y} f ↦ by
      apply NatTrans.ext
      funext n
      exact (e n.as).hom.naturality f)

private def sheafPushforwardIso (D : OrderedGeometry r) (g : StageGeometry r)
    (c : ContinuousJets r) :
    heartSum r g c ⋙ gradedInclusion r ⋙ skyscraperProduct r ≅
      (stalkFamily r g c).prod (stalkFamily r g c) ⋙ geometricPushforward D := by
  let T := sheafStalkFamilies r
  let E := sheafFamiliesEquiv r g (monomialPoint_bijective r)
  letI : T.Full := E.fullyFaithfulFunctor.full
  letI : T.Faithful := E.fullyFaithfulFunctor.faithful
  apply Functor.fullyFaithfulCancelRight T
  let H := heartSum r g c ⋙ gradedInclusion r
  let K := skyscraperProduct r
  haveI := stalkProductCounit_isIso r g (monomialPoint_bijective r).injective
  exact Functor.associator H K T ≪≫ Functor.isoWhiskerLeft H (asIso (stalkProductCounit r)) ≪≫
    H.rightUnitor ≪≫ familiesIsoOfComponents (sumGeometricFiber D g c)

private def geometricStalkComparison (D : OrderedGeometry r) (g : StageGeometry r)
    (A B : Families r) (hA : (familySupport A).Finite) (hB : (familySupport B).Finite)
    (n : Labels r) : FiberComparison D A B n := by
  let F := tensorAt A B (n := n)
  let S : Set (SumFiber n) := {p | p.val.1 ∈ familySupport A ∧ p.val.2 ∈ familySupport B}
  have hf : S.Finite := supportedFiber_finite hA hB
  have hz : ∀ p, p ∉ S → IsZero (F p) :=
    tensor_zero_outside A B (fun _ h ↦ h) (fun _ h ↦ h) n
  let k := finiteSumProductIso F S hf hz
  let e := (wholeFiberProduct D g n).app (A, B)
  have he (p : SumFiber n) : e.hom ≫ Pi.π F p = pushforwardProjection D A B n p :=
    wholeFiberProduct_π D g A B n p
  refine ⟨k ≪≫ e.symm, ?_, ?_⟩
  · intro p
    change Sigma.ι F p ≫ (k.hom ≫ e.inv) ≫ pushforwardProjection D A B n p = _
    rw [Category.assoc k.hom, ← he, Iso.inv_hom_id_assoc]
    exact finiteSumProductIso_same F S hf hz p
  · intro p q hp
    change Sigma.ι F p ≫ (k.hom ≫ e.inv) ≫ pushforwardProjection D A B n q = _
    rw [Category.assoc k.hom, ← he, Iso.inv_hom_id_assoc]
    exact finiteSumProductIso_other F S hf hz p q hp

private def finitePushforwardIso (D : OrderedGeometry r) (g : StageGeometry r)
    (c : ContinuousJets r) (A B : Set (Labels r)) :
    ObjectProperty.ι (supportedPairs r g c A B) ⋙
      (stalkFamily r g c).prod (stalkFamily r g c) ⋙ geometricPushforward D ≅
    ObjectProperty.ι (supportedPairs r g c A B) ⋙
      (stalkFamily r g c).prod (stalkFamily r g c) ⋙ stagePushforward D A B := by
  let I := ObjectProperty.ι (supportedPairs r g c A B)
  let H := (stalkFamily r g c).prod (stalkFamily r g c)
  let T := sheafStalkFamilies r
  let E := sheafFamiliesEquiv r g (monomialPoint_bijective r)
  haveI : T.Full := E.fullyFaithfulFunctor.full
  haveI : T.Faithful := E.fullyFaithfulFunctor.faithful
  apply Functor.fullyFaithfulCancelRight T
  apply familiesIsoOfComponents
  intro n
  let m := Functor.whiskerLeft (I ⋙ H) (restrictFiberProduct A B n)
  haveI : IsIso m := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ m (by
    intro V
    apply restrictProduct_isIso
    exact tensor_zero_outside _ _ V.property.1 V.property.2 n)
  exact Functor.isoWhiskerLeft (I ⋙ H) (wholeFiberProduct D g n) ≪≫ asIso m ≪≫
    Functor.isoWhiskerLeft (I ⋙ H) (stageFiberProduct D g A B n).symm

private def productFunctor (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Heart r g c × Heart r g c ⥤ Heart r g c :=
  heartSum r g c ⋙ perverseExtension r g c

private def productPushforward (D : OrderedGeometry r) (g : StageGeometry r)
    (c : ContinuousJets r) :
    productFunctor r g c ⋙ forgetPerverse r g c ≅
      (stalkFamily r g c).prod (stalkFamily r g c) ⋙ geometricPushforward D ⋙
        DerivedCategory.singleFunctor _ 0 := by
  let S := DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0
  change heartSum r g c ⋙ gradedInclusion r ⋙ skyscraperProduct r ⋙ S ≅ _
  exact Functor.isoWhiskerRight (sheafPushforwardIso D g c) S

private def productFiberComparison (D : OrderedGeometry r) (g : StageGeometry r)
    (c : ContinuousJets r) (n : Labels r) :
    productFunctor r g c ⋙ stalkFamily r g c ⋙ familyAt n ≅
      (stalkFamily r g c).prod (stalkFamily r g c) ⋙ geometricFiber D n := by
  let Q := productFunctor r g c ⋙ forgetPerverse r g c
  let H := (stalkFamily r g c).prod (stalkFamily r g c)
  let G := H ⋙ geometricPushforward D
  let S := DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0
  let C := cohomology (torusSpace r) 0
  let T := stalk (monomialPoint r n)
  let e : Q ≅ G ⋙ S := productPushforward D g c
  let h : S ⋙ C ≅ 𝟭 _ := DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0
  change (Q ⋙ C) ⋙ T ≅ G ⋙ T
  refine NatIso.ofComponents (fun X ↦ T.mapIso (C.mapIso (e.app X) ≪≫ h.app (G.obj X))) ?_
  intro V W v
  have he : C.map (Q.map v) ≫ C.map (e.hom.app W) =
      C.map (e.hom.app V) ≫ C.map (S.map (G.map v)) :=
    (C.map_comp _ _).symm.trans ((congrArg (fun f ↦ C.map f) (e.hom.naturality v)).trans
      (C.map_comp _ _))
  have hh : C.map (S.map (G.map v)) ≫ (h.app (G.obj W)).hom =
      (h.app (G.obj V)).hom ≫ G.map v := h.hom.naturality _
  have hr : C.map (Q.map v) ≫ C.map (e.hom.app W) ≫ (h.app (G.obj W)).hom =
      (C.map (e.hom.app V) ≫ (h.app (G.obj V)).hom) ≫ G.map v := by
    rw [← Category.assoc, he, Category.assoc, hh, Category.assoc]
  simpa only [Functor.comp_map, Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom,
    ← CategoryTheory.Functor.map_comp]
    using congrArg (fun f ↦ T.map f) hr

private theorem productFiberComparison_app (D : OrderedGeometry r) (g : StageGeometry r)
    (c : ContinuousJets r) (n : Labels r) (V W : Heart r g c) :
    (productFiberComparison D g c n).app (V, W) =
      (stalk (monomialPoint r n)).mapIso
        ((cohomology (torusSpace r) 0).mapIso ((productPushforward D g c).app (V, W)) ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves (torusSpace r)) 0).app
            ((geometricPushforward D).obj (((stalkFamily r g c).prod (stalkFamily r g c)).obj (V, W)))) :=
  rfl

private def orderedProduct (D : OrderedGeometry r) (g : StageGeometry r)
    (c : ContinuousJets r) : OrderedProduct D g c where
  convolution := productFunctor r g c
  pushforward := productPushforward D g c
  finiteSupport A B _ _ := by
    let I := ObjectProperty.ι (supportedPairs r g c A B)
    let H := (stalkFamily r g c).prod (stalkFamily r g c)
    let S := DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0
    let J := DerivedCategory.Plus.ι (C := Sheaves (torusSpace r))
    let f := D.terminal A B
    let U := directImage f
    let L := descendedExterior D A B
    letI : DiscreteTopology (D.space A B) := ⟨rfl⟩
    refine ⟨Functor.isoWhiskerLeft I (productPushforward D g c) ≪≫
      Functor.isoWhiskerRight (finitePushforwardIso D g c A B) S ≪≫ ?_⟩
    let e := DerivedCategory.Plus.singleFunctorιIso (Sheaves (torusSpace r)) 0
    let e' := Functor.isoWhiskerRight (derivedImageSingleIso f).symm J
    exact Functor.isoWhiskerLeft (I ⋙ H ⋙ L) (Functor.isoWhiskerLeft U e.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ e' ≪≫ Functor.associator _ _ _)
  stalkIso n := sumGeometricFiber D g c n ≪≫ (productFiberComparison D g c n).symm
  geometricStalkIso V W n := by
    let A := (stalkFamily r g c).obj V
    let B := (stalkFamily r g c).obj W
    let hA : (familySupport A).Finite := ((perverseStalks r g c).obj V).property.2
    let hB : (familySupport B).Finite := ((perverseStalks r g c).obj W).property.2
    refine ⟨geometricStalkComparison D g A B hA hB n, ?_⟩
    have he : (geometricStalkComparison D g A B hA hB n).iso =
        (sumGeometricFiber D g c n).app (V, W) := rfl
    let d := (sumGeometricFiber D g c n ≪≫ (productFiberComparison D g c n).symm).app (V, W)
    refine (congrArg (fun i ↦ d ≪≫ i) (productFiberComparison_app D g c n V W).symm).trans ?_
    refine Eq.trans ?_ he.symm
    let e := (productFiberComparison D g c n).app (V, W)
    change ((sumGeometricFiber D g c n).app (V, W) ≪≫ e.symm) ≪≫ e =
      (sumGeometricFiber D g c n).app (V, W)
    simp

section Constraints

open OrderedProduct (Stalk)

variable {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
variable (P : OrderedProduct D g c)

private def includeFiber (V W : Heart r g c) (n : Labels r) (p : SumFiber n) :
    Stalk V p.val.1 ⊗ Stalk W p.val.2 ⟶ Stalk (P.convolution.obj (V, W)) n :=
  summand n ((stalkFamily r g c).obj V) ((stalkFamily r g c).obj W) p ≫
    (P.stalkIso n).hom.app (V, W)

private def mapStalk {V W : Heart r g c} (f : V ⟶ W) (n : Labels r) :
    Stalk V n ⟶ Stalk W n :=
  ((stalkFamily r g c).map f).app (Discrete.mk n)

@[simp]
private theorem mapStalk_id (V : Heart r g c) (n : Labels r) :
    mapStalk (𝟙 V) n = 𝟙 (Stalk V n) := by
  unfold mapStalk
  rw [CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
private theorem includeFiber_naturality {V V' W W' : Heart r g c}
    (v : V ⟶ V') (w : W ⟶ W') (n : Labels r) (p : SumFiber n) :
    includeFiber P V W n p ≫ mapStalk (P.convolution.map (v, w)) n =
      (mapStalk v p.val.1 ⊗ₘ mapStalk w p.val.2) ≫ includeFiber P V' W' n p := by
  let N := (P.stalkIso n).hom
  have h := N.naturality (show (V, W) ⟶ (V', W') from (v, w))
  change (fiberSum n).map ((stalkFamily r g c).map v, (stalkFamily r g c).map w) ≫
    N.app (V', W') = N.app (V, W) ≫ mapStalk (P.convolution.map (v, w)) n at h
  unfold includeFiber
  rw [Category.assoc, ← h, ← Category.assoc]
  change (Sigma.ι _ p ≫ Limits.Sigma.map _) ≫ _ = _
  rw [Sigma.ι_map]
  rfl

@[reassoc]
private theorem includeFiber_cast (V W : Heart r g c) {n m : Labels r}
    (p : SumFiber n) (h : n = m) :
    includeFiber P V W n p ≫
        eqToHom (congrArg (Stalk (P.convolution.obj (V, W))) h) =
      includeFiber P V W m ⟨p.val, p.property.trans h⟩ := by
  subst m
  simp

private abbrev TripleFiber (n : Labels r) :=
  {t : Labels r × Labels r × Labels r // t.1 + t.2.1 + t.2.2 = n}

private def leftIndex (n : Labels r) :
    TripleFiber n ≃ Σ p : SumFiber n, SumFiber p.val.1 where
  toFun t := ⟨⟨(t.val.1 + t.val.2.1, t.val.2.2), t.property⟩,
    ⟨(t.val.1, t.val.2.1), rfl⟩⟩
  invFun t := ⟨(t.2.val.1, t.2.val.2, t.1.val.2),
    (congrArg (· + t.1.val.2) t.2.property).trans t.1.property⟩
  left_inv _ := rfl
  right_inv t := by
    rcases t with ⟨⟨⟨a, d⟩, hd⟩, ⟨⟨b, e⟩, he⟩⟩
    change b + e = a at he
    subst a
    rfl

private def rightIndex (n : Labels r) :
    TripleFiber n ≃ Σ p : SumFiber n, SumFiber p.val.2 where
  toFun t := ⟨⟨(t.val.1, t.val.2.1 + t.val.2.2),
      (add_assoc t.val.1 t.val.2.1 t.val.2.2).symm.trans t.property⟩,
    ⟨(t.val.2.1, t.val.2.2), rfl⟩⟩
  invFun t := ⟨(t.1.val.1, t.2.val.1, t.2.val.2),
    (add_assoc _ _ _).trans ((congrArg (t.1.val.1 + ·) t.2.property).trans t.1.property)⟩
  left_inv _ := rfl
  right_inv t := by
    rcases t with ⟨⟨⟨a, d⟩, hd⟩, ⟨⟨b, e⟩, he⟩⟩
    change b + e = d at he
    subst d
    rfl

private def coproductIsoIsColimit {I : Type} {Z : Coeff.{0}} {F : I → Coeff.{0}}
    (e : (∐ F) ≅ Z) : IsColimit (Cofan.mk Z (fun p ↦ Sigma.ι F p ≫ e.hom)) :=
  (coproductIsCoproduct F).ofIsoColimit (Cofan.ext e fun _ ↦ rfl)

private def includeFiberIsColimit (V W : Heart r g c) (n : Labels r) :
    IsColimit (Cofan.mk _ (includeFiber P V W n)) :=
  coproductIsoIsColimit ((P.stalkIso n).app (V, W))

private def tensorCofanIsColimit {I : Type} {F : I → Coeff.{0}} {X : Coeff.{0}}
    (i : ∀ t, F t ⟶ X) (hi : IsColimit (Cofan.mk X i))
    (G : Coeff.{0} ⥤ Coeff.{0}) [PreservesColimit (Discrete.functor F) G] :
    IsColimit (Cofan.mk (G.obj X) fun t ↦ G.map (i t)) :=
  isColimitCofanMkObjOfIsColimit G F _ hi

private abbrev leftTensor (U V W : Heart r g c) {n : Labels r} (p : TripleFiber n) :=
  (Stalk U p.val.1 ⊗ Stalk V p.val.2.1) ⊗ Stalk W p.val.2.2

private abbrev rightTensor (U V W : Heart r g c) {n : Labels r} (p : TripleFiber n) :=
  Stalk U p.val.1 ⊗ (Stalk V p.val.2.1 ⊗ Stalk W p.val.2.2)

private def leftTriple (U V W : Heart r g c) (n : Labels r) (p : TripleFiber n) :
    leftTensor U V W p ⟶ Stalk (P.associateLeft.obj (U, V, W)) n :=
  (P.includeSummand U V p.val.1 p.val.2.1 ⊗ₘ 𝟙 (Stalk W p.val.2.2)) ≫
    includeFiber P (P.convolution.obj (U, V)) W n (leftIndex n p).1

private def rightTriple (U V W : Heart r g c) (n : Labels r) (p : TripleFiber n) :
    rightTensor U V W p ⟶ Stalk (P.associateRight.obj (U, V, W)) n :=
  (𝟙 (Stalk U p.val.1) ⊗ₘ P.includeSummand V W p.val.2.1 p.val.2.2) ≫
    includeFiber P U (P.convolution.obj (V, W)) n (rightIndex n p).1

private def leftIteratedCofan (U V W : Heart r g c) (n : Labels r) :=
  Cofan.isColimitTrans _ (includeFiberIsColimit P (P.convolution.obj (U, V)) W n)
    (fun p q ↦ includeFiber P U V p.val.1 q ⊗ₘ 𝟙 (Stalk W p.val.2))
    (fun p ↦ tensorCofanIsColimit _ (includeFiberIsColimit P U V p.val.1)
      (tensorRight (Stalk W p.val.2)))

private def rightIteratedCofan (U V W : Heart r g c) (n : Labels r) :=
  Cofan.isColimitTrans _ (includeFiberIsColimit P U (P.convolution.obj (V, W)) n)
    (fun p q ↦ 𝟙 (Stalk U p.val.1) ⊗ₘ includeFiber P V W p.val.2 q)
    (fun p ↦ tensorCofanIsColimit _ (includeFiberIsColimit P V W p.val.2)
      (tensorLeft (Stalk U p.val.1)))

private def cofanIso {I : Type} (F : I → Coeff.{0}) {X : Coeff.{0}}
    (j : ∀ i, F i ⟶ X) (hj : IsColimit (Cofan.mk X j)) :
    (∐ F) ≅ X :=
  (coproductIsCoproduct F).coconePointUniqueUpToIso hj

@[reassoc]
private theorem cofanIso_ι {I : Type} (F : I → Coeff.{0}) {X : Coeff.{0}}
    (j : ∀ i, F i ⟶ X) (hj : IsColimit (Cofan.mk X j)) (i : I) :
    Sigma.ι F i ≫ (cofanIso F j hj).hom = j i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct F) hj (Discrete.mk i)

private abbrev leftNestedTensor (U V W : Heart r g c) {n : Labels r}
    (q : Σ p : SumFiber n, SumFiber p.val.1) : Coeff.{0} :=
  match q with
  | ⟨p, t⟩ => (Stalk U t.val.1 ⊗ Stalk V t.val.2) ⊗ Stalk W p.val.2

private abbrev rightNestedTensor (U V W : Heart r g c) {n : Labels r}
    (q : Σ p : SumFiber n, SumFiber p.val.2) : Coeff.{0} :=
  match q with
  | ⟨p, t⟩ => Stalk U p.val.1 ⊗ (Stalk V t.val.1 ⊗ Stalk W t.val.2)

private def leftTripleIso (U V W : Heart r g c) (n : Labels r) :
    (∐ fun p : TripleFiber n ↦ leftTensor U V W p) ≅
      Stalk (P.associateLeft.obj (U, V, W)) n := by
  let F := leftNestedTensor U V W (n := n)
  let e : (∐ (leftTensor U V W (n := n))) ≅ ∐ F :=
    Sigma.whiskerEquiv (f := leftTensor U V W (n := n)) (g := F)
      (leftIndex n) (fun p ↦ Iso.refl (leftTensor U V W p))
  let m := cofanIso F _ (leftIteratedCofan P U V W n)
  exact e ≪≫ m

private def rightTripleIso (U V W : Heart r g c) (n : Labels r) :
    (∐ fun p : TripleFiber n ↦ rightTensor U V W p) ≅
      Stalk (P.associateRight.obj (U, V, W)) n := by
  let F := rightNestedTensor U V W (n := n)
  let e : (∐ (rightTensor U V W (n := n))) ≅ ∐ F :=
    Sigma.whiskerEquiv (f := rightTensor U V W (n := n)) (g := F)
      (rightIndex n) (fun p ↦ Iso.refl (rightTensor U V W p))
  let m := cofanIso F _ (rightIteratedCofan P U V W n)
  exact e ≪≫ m

@[reassoc]
private theorem leftTripleIso_ι (U V W : Heart r g c) (n : Labels r) (p : TripleFiber n) :
    Sigma.ι _ p ≫ (leftTripleIso P U V W n).hom = leftTriple P U V W n p := by
  simp only [leftTripleIso, Iso.trans_hom, Sigma.whiskerEquiv_hom, Iso.refl_inv,
    Sigma.ι_comp_map'_assoc, Category.id_comp, cofanIso_ι]
  rfl

@[reassoc]
private theorem rightTripleIso_ι (U V W : Heart r g c) (n : Labels r) (p : TripleFiber n) :
    Sigma.ι _ p ≫ (rightTripleIso P U V W n).hom = rightTriple P U V W n p := by
  simp only [rightTripleIso, Iso.trans_hom, Sigma.whiskerEquiv_hom, Iso.refl_inv,
    Sigma.ι_comp_map'_assoc, Category.id_comp, cofanIso_ι]
  rfl

private def associatorAt (U V W : Heart r g c) (n : Labels r) :
    Stalk (P.associateLeft.obj (U, V, W)) n ≅ Stalk (P.associateRight.obj (U, V, W)) n :=
  (leftTripleIso P U V W n).symm ≪≫
    Sigma.whiskerEquiv (f := leftTensor U V W (n := n)) (g := rightTensor U V W (n := n))
      (Equiv.refl (TripleFiber n))
      (fun p ↦ (α_ (Stalk U p.val.1) (Stalk V p.val.2.1) (Stalk W p.val.2.2)).symm) ≪≫
    rightTripleIso P U V W n

@[reassoc]
private theorem associatorAt_ι (U V W : Heart r g c) (n : Labels r) (p : TripleFiber n) :
    leftTriple P U V W n p ≫ (associatorAt P U V W n).hom =
      (α_ (Stalk U p.val.1) (Stalk V p.val.2.1) (Stalk W p.val.2.2)).hom ≫
        rightTriple P U V W n p := by
  rw [← leftTripleIso_ι]
  simp only [associatorAt, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Sigma.whiskerEquiv_hom, Iso.symm_inv, Sigma.ι_comp_map'_assoc, Equiv.refl_apply,
    rightTripleIso_ι]

@[reassoc]
private theorem leftTriple_naturality {U V W U' V' W' : Heart r g c}
    (u : U ⟶ U') (v : V ⟶ V') (w : W ⟶ W') (n : Labels r) (p : TripleFiber n) :
    leftTriple P U V W n p ≫ mapStalk (P.convolution.map (P.convolution.map (u, v), w)) n =
      ((mapStalk u p.val.1 ⊗ₘ mapStalk v p.val.2.1) ⊗ₘ mapStalk w p.val.2.2) ≫
        leftTriple P U' V' W' n p := by
  let a := p.val.1
  let b := p.val.2.1
  let d := p.val.2.2
  let i := (leftIndex n p).1
  let t : SumFiber (a + b) := ⟨(a, b), rfl⟩
  let i₀ := includeFiber P U V (a + b) t
  let i₁ := includeFiber P U' V' (a + b) t
  let uv : P.convolution.obj (U, V) ⟶ P.convolution.obj (U', V') :=
    P.convolution.map (X := (U, V)) (Y := (U', V')) (u, v)
  let f := mapStalk uv (a + b)
  let u' := mapStalk u a
  let v' := mapStalk v b
  let w' := mapStalk w d
  have h : (i₀ ⊗ₘ 𝟙 (Stalk W d)) ≫ (f ⊗ₘ w') =
      ((u' ⊗ₘ v') ⊗ₘ w') ≫ (i₁ ⊗ₘ 𝟙 (Stalk W' d)) := by
    have hi : i₀ ≫ f = (u' ⊗ₘ v') ≫ i₁ := includeFiber_naturality P u v (a + b) t
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hi]
  change (i₀ ⊗ₘ 𝟙 (Stalk W d)) ≫ includeFiber P (P.convolution.obj (U, V)) W n i ≫
    mapStalk (P.convolution.map (P.convolution.map (u, v), w)) n =
    ((u' ⊗ₘ v') ⊗ₘ w') ≫ (i₁ ⊗ₘ 𝟙 (Stalk W' d)) ≫
      includeFiber P (P.convolution.obj (U', V')) W' n i
  rw [includeFiber_naturality P uv w n i]
  change (i₀ ⊗ₘ 𝟙 (Stalk W d)) ≫ (f ⊗ₘ w') ≫ _ = _
  exact Eq.trans (Category.assoc _ _ _).symm
    ((congrArg (fun z ↦ z ≫ includeFiber P (P.convolution.obj (U', V')) W' n i) h).trans
      (Category.assoc _ _ _))

@[reassoc]
private theorem rightTriple_naturality {U V W U' V' W' : Heart r g c}
    (u : U ⟶ U') (v : V ⟶ V') (w : W ⟶ W') (n : Labels r) (p : TripleFiber n) :
    rightTriple P U V W n p ≫ mapStalk (P.convolution.map (u, P.convolution.map (v, w))) n =
      (mapStalk u p.val.1 ⊗ₘ (mapStalk v p.val.2.1 ⊗ₘ mapStalk w p.val.2.2)) ≫
        rightTriple P U' V' W' n p := by
  let a := p.val.1
  let b := p.val.2.1
  let d := p.val.2.2
  let i := (rightIndex n p).1
  let t : SumFiber (b + d) := ⟨(b, d), rfl⟩
  let i₀ := includeFiber P V W (b + d) t
  let i₁ := includeFiber P V' W' (b + d) t
  let vw : P.convolution.obj (V, W) ⟶ P.convolution.obj (V', W') :=
    P.convolution.map (X := (V, W)) (Y := (V', W')) (v, w)
  let f := mapStalk vw (b + d)
  let u' := mapStalk u a
  let v' := mapStalk v b
  let w' := mapStalk w d
  have h : (𝟙 (Stalk U a) ⊗ₘ i₀) ≫ (u' ⊗ₘ f) =
      (u' ⊗ₘ (v' ⊗ₘ w')) ≫ (𝟙 (Stalk U' a) ⊗ₘ i₁) := by
    have hi : i₀ ≫ f = (v' ⊗ₘ w') ≫ i₁ := includeFiber_naturality P v w (b + d) t
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hi]
  change (𝟙 (Stalk U a) ⊗ₘ i₀) ≫ includeFiber P U (P.convolution.obj (V, W)) n i ≫
    mapStalk (P.convolution.map (u, P.convolution.map (v, w))) n =
    (u' ⊗ₘ (v' ⊗ₘ w')) ≫ (𝟙 (Stalk U' a) ⊗ₘ i₁) ≫
      includeFiber P U' (P.convolution.obj (V', W')) n i
  rw [includeFiber_naturality P u vw n i]
  change (𝟙 (Stalk U a) ⊗ₘ i₀) ≫ (u' ⊗ₘ f) ≫ _ = _
  exact Eq.trans (Category.assoc _ _ _).symm
    ((congrArg (fun z ↦ z ≫ includeFiber P U' (P.convolution.obj (V', W')) n i) h).trans
      (Category.assoc _ _ _))

private theorem associatorAt_natural {U V W U' V' W' : Heart r g c}
    (u : U ⟶ U') (v : V ⟶ V') (w : W ⟶ W') (n : Labels r) :
    mapStalk (P.convolution.map (P.convolution.map (u, v), w)) n ≫ (associatorAt P U' V' W' n).hom =
      (associatorAt P U V W n).hom ≫ mapStalk (P.convolution.map (u, P.convolution.map (v, w))) n := by
  apply (cancel_epi (leftTripleIso P U V W n).hom).mp
  apply Sigma.hom_ext
  intro p
  simp only [leftTripleIso_ι_assoc]
  rw [leftTriple_naturality_assoc P u v w n p, associatorAt_ι, associatorAt_ι_assoc,
    rightTriple_naturality P u v w n p, associator_naturality_assoc]

private def associatorStalks (n : Labels r) :
    P.associateLeft ⋙ stalkFamily r g c ⋙ familyAt n ≅
      P.associateRight ⋙ stalkFamily r g c ⋙ familyAt n :=
  NatIso.ofComponents (fun V ↦ associatorAt P V.1 V.2.1 V.2.2 n)
    (fun {X Y} f ↦ associatorAt_natural P (U := X.1) (V := X.2.1) (W := X.2.2)
      (U' := Y.1) (V' := Y.2.1) (W' := Y.2.2) f.1 f.2.1 f.2.2 n)

private def stalksFullyFaithful (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    (stalkFamily r g c).FullyFaithful :=
  (perverseEquivalence r g c).fullyFaithfulFunctor.comp ((IsFiniteFamily r).fullyFaithfulι)

private def isoFromStalks {C : Type*} [Category C] {L R : C ⥤ Heart r g c}
    (e : ∀ n : Labels r, L ⋙ stalkFamily r g c ⋙ familyAt n ≅
      R ⋙ stalkFamily r g c ⋙ familyAt n) : L ≅ R :=
  let S := stalkFamily r g c
  let F := stalksFullyFaithful r g c
  letI : S.Full := F.full
  letI : S.Faithful := F.faithful
  Functor.fullyFaithfulCancelRight S (familiesIsoOfComponents e)

private theorem isoFromStalks_hom {C : Type*} [Category C] {L R : C ⥤ Heart r g c}
    (e : ∀ n : Labels r, L ⋙ stalkFamily r g c ⋙ familyAt n ≅
      R ⋙ stalkFamily r g c ⋙ familyAt n) (X : C) (n : Labels r) :
    mapStalk ((isoFromStalks e).hom.app X) n = (e n).hom.app X := by
  let S := stalkFamily r g c
  let F := stalksFullyFaithful r g c
  letI : S.Full := F.full
  letI : S.Faithful := F.faithful
  change (S.map ((Functor.fullyFaithfulCancelRight S (familiesIsoOfComponents e)).hom.app X)).app
    (Discrete.mk n) = _
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  rfl

private theorem rightSummand_eq (U V W : Heart r g c) (a b d : Labels r) :
    P.rightSummand U V W a b d =
      rightTriple P U V W (a + b + d) ⟨(a, b, d), rfl⟩ := by
  change (𝟙 (Stalk U a) ⊗ₘ P.includeSummand V W b d) ≫
    includeFiber P U (P.convolution.obj (V, W)) (a + (b + d)) ⟨(a, b + d), rfl⟩ ≫
    eqToHom (congrArg (Stalk (P.convolution.obj (U, P.convolution.obj (V, W))))
      (add_assoc a b d).symm) = _
  rw [includeFiber_cast P _ _ _ (add_assoc a b d).symm]
  rfl

open private moduleFinite_of_isZero from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusPerverse

private theorem pointUnit_off_zero (a : Labels r) (h : a ≠ 0) :
    IsZero (fiber (pointUnit r) a) := by
  simpa [pointUnit, h] using isZero_zero Coeff.{0}

private def pointGraded (r : ℕ) : Graded r :=
  ⟨pointUnit r, by
    constructor
    · intro a
      by_cases h : a = 0
      · subst a
        have h0 : fiber (pointUnit r) 0 = 𝟙_ Coeff.{0} := by simp [pointUnit]
        change Module.Finite ℚ ((fiber (pointUnit r) 0) : Type)
        rw [h0]
        exact inferInstanceAs (Module.Finite ℚ ℚ)
      · exact moduleFinite_of_isZero _ (pointUnit_off_zero a h)
    · refine (Set.finite_singleton (0 : Labels r)).subset ?_
      intro a ha
      by_contra h
      exact ha (pointUnit_off_zero a h)⟩

private def unitPoint (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) : Heart r g c :=
  (perverseExtension r g c).obj (pointGraded r)

private def unitPointStalk (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    (stalkFamily r g c).obj (unitPoint r g c) ≅ pointUnit r :=
  (gradedInclusion r).mapIso ((extensionStalkIso r g c).app (pointGraded r))

private def unitScalar (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    (𝟙_ Coeff.{0}) ⟶ Stalk (unitPoint r g c) 0 :=
  eqToHom (by simp [pointUnit]) ≫ (unitPointStalk r g c).inv.app (Discrete.mk 0)

private instance unitScalar_isIso : IsIso (unitScalar r g c) := by
  unfold unitScalar
  infer_instance

private theorem unitPoint_off_zero (a : Labels r) (h : a ≠ 0) :
    IsZero (Stalk (unitPoint r g c) a) :=
  (pointUnit_off_zero a h).of_iso ((unitPointStalk r g c).app (Discrete.mk a))

private def unitPointSheaf (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    (forgetPerverse r g c).obj (unitPoint r g c) ≅
      (DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0).obj
        ((skyscraperSheafFunctor (monomialPoint r 0)).obj (𝟙_ Coeff.{0})) := by
  let K (n : Labels r) := (skyscraperSheafFunctor (monomialPoint r n)).obj (fiber (pointUnit r) n)
  haveI : IsIso (Pi.π K 0) := by
    apply productProjection_isIso
    intro j hj
    let adj := stalkSkyscraperSheafAdjunction (C := Coeff.{0}) (monomialPoint r j)
    letI : PreservesLimitsOfSize.{0, 0} (skyscraperSheafFunctor (C := Coeff.{0}) (monomialPoint r j)) :=
      adj.rightAdjoint_preservesLimits
    exact (pointUnit_off_zero j hj).isTerminal.isTerminalObj
      (skyscraperSheafFunctor (monomialPoint r j))
  apply (DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0).mapIso
  exact asIso (Pi.π K 0) ≪≫ (skyscraperSheafFunctor (monomialPoint r 0)).mapIso
    (eqToIso (by simp [pointUnit]))

private theorem coproductInclusion_isIso {I : Type} (F : I → Coeff.{0}) (i : I)
    (h : ∀ j, j ≠ i → IsZero (F j)) : IsIso (Sigma.ι F i) := by
  let f (j : I) : F j ⟶ F i :=
    if e : j = i then eqToHom (congrArg F e) else 0
  refine ⟨⟨Sigma.desc f, ?_, ?_⟩⟩
  · simp [f]
  · apply Sigma.hom_ext
    intro j
    by_cases hj : j = i
    · subst j
      simp [f]
    · exact (h j hj).eq_of_src _ _

private abbrev leftUnitFunctor : Heart r g c ⥤ Heart r g c :=
  ((Functor.const (Heart r g c)).obj (unitPoint r g c)).prod' (𝟭 _) ⋙ P.convolution

private abbrev rightUnitFunctor : Heart r g c ⥤ Heart r g c :=
  (𝟭 (Heart r g c)).prod' ((Functor.const (Heart r g c)).obj (unitPoint r g c)) ⋙ P.convolution

private def leftUnitInclusion (V : Heart r g c) (n : Labels r) :
    (𝟙_ Coeff.{0}) ⊗ Stalk V n ⟶ Stalk ((leftUnitFunctor P).obj V) n :=
  (unitScalar r g c ⊗ₘ 𝟙 (Stalk V n)) ≫
    includeFiber P (unitPoint r g c) V n ⟨(0, n), zero_add n⟩

private def rightUnitInclusion (V : Heart r g c) (n : Labels r) :
    Stalk V n ⊗ (𝟙_ Coeff.{0}) ⟶ Stalk ((rightUnitFunctor P).obj V) n :=
  (𝟙 (Stalk V n) ⊗ₘ unitScalar r g c) ≫
    includeFiber P V (unitPoint r g c) n ⟨(n, 0), add_zero n⟩

private theorem leftUnitInclusion_isIso (V : Heart r g c) (n : Labels r) :
    IsIso (leftUnitInclusion P V n) := by
  let i : SumFiber n := ⟨(0, n), zero_add n⟩
  let F (p : SumFiber n) := Stalk (unitPoint r g c) p.val.1 ⊗ Stalk V p.val.2
  haveI : IsIso (Sigma.ι F i) := coproductInclusion_isIso F i fun j hj ↦ by
    apply tensor_isZero_left
    apply unitPoint_off_zero
    intro e
    apply hj
    apply Subtype.ext
    exact Prod.ext e (by simpa [e] using j.property)
  change IsIso ((unitScalar r g c ⊗ₘ 𝟙 (Stalk V n)) ≫
    Sigma.ι F i ≫ (P.stalkIso n).hom.app (unitPoint r g c, V))
  infer_instance

private theorem rightUnitInclusion_isIso (V : Heart r g c) (n : Labels r) :
    IsIso (rightUnitInclusion P V n) := by
  let i : SumFiber n := ⟨(n, 0), add_zero n⟩
  let F (p : SumFiber n) := Stalk V p.val.1 ⊗ Stalk (unitPoint r g c) p.val.2
  haveI : IsIso (Sigma.ι F i) := coproductInclusion_isIso F i fun j hj ↦ by
    apply tensor_isZero_right
    apply unitPoint_off_zero
    intro e
    apply hj
    apply Subtype.ext
    exact Prod.ext (by simpa [e] using j.property) e
  change IsIso ((𝟙 (Stalk V n) ⊗ₘ unitScalar r g c) ≫
    Sigma.ι F i ≫ (P.stalkIso n).hom.app (V, unitPoint r g c))
  infer_instance

private def leftUnitorStalks (n : Labels r) :
    leftUnitFunctor P ⋙ stalkFamily r g c ⋙ familyAt n ≅
      (𝟭 _) ⋙ stalkFamily r g c ⋙ familyAt n :=
  (NatIso.ofComponents
    (fun V ↦ (λ_ (Stalk V n)).symm ≪≫ @asIso _ _ _ _ _ (leftUnitInclusion_isIso P V n))
    (fun {V W} v ↦ by
      change mapStalk v n ≫ (λ_ (Stalk W n)).inv ≫ leftUnitInclusion P W n =
        ((λ_ (Stalk V n)).inv ≫ leftUnitInclusion P V n) ≫
          mapStalk (P.convolution.map (𝟙 (unitPoint r g c), v)) n
      rw [leftUnitor_inv_naturality_assoc]
      simp only [leftUnitInclusion, Category.assoc]
      rw [includeFiber_naturality P (𝟙 (unitPoint r g c)) v n ⟨(0, n), zero_add n⟩,
        mapStalk_id, ← id_tensorHom, ← Category.assoc (𝟙 (𝟙_ Coeff.{0}) ⊗ₘ mapStalk v n),
        tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]
      simp only [Category.id_comp, Category.comp_id])).symm

private def rightUnitorStalks (n : Labels r) :
    rightUnitFunctor P ⋙ stalkFamily r g c ⋙ familyAt n ≅
      (𝟭 _) ⋙ stalkFamily r g c ⋙ familyAt n :=
  (NatIso.ofComponents
    (fun V ↦ (ρ_ (Stalk V n)).symm ≪≫ @asIso _ _ _ _ _ (rightUnitInclusion_isIso P V n))
    (fun {V W} v ↦ by
      change mapStalk v n ≫ (ρ_ (Stalk W n)).inv ≫ rightUnitInclusion P W n =
        ((ρ_ (Stalk V n)).inv ≫ rightUnitInclusion P V n) ≫
          mapStalk (P.convolution.map (v, 𝟙 (unitPoint r g c))) n
      rw [rightUnitor_inv_naturality_assoc]
      simp only [rightUnitInclusion, Category.assoc]
      rw [includeFiber_naturality P v (𝟙 (unitPoint r g c)) n ⟨(n, 0), add_zero n⟩,
        mapStalk_id, ← tensorHom_id, ← Category.assoc (mapStalk v n ⊗ₘ 𝟙 (𝟙_ Coeff.{0})),
        tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]
      simp only [Category.id_comp, Category.comp_id])).symm

private theorem associatorOnTriple (U V W : Heart r g c) (a b d : Labels r) :
    P.leftSummand U V W a b d ≫
      mapStalk ((isoFromStalks (associatorStalks P)).hom.app (U, V, W)) (a + b + d) =
      (α_ (Stalk U a) (Stalk V b) (Stalk W d)).hom ≫ P.rightSummand U V W a b d := by
  rw [isoFromStalks_hom, rightSummand_eq P]
  exact associatorAt_ι P U V W (a + b + d) ⟨(a, b, d), rfl⟩

private def constraints : OrderedConstraints P where
  unit := unitPoint r g c
  unitSheaf := unitPointSheaf r g c
  unitStalk := unitPointStalk r g c
  leftUnitor := isoFromStalks (leftUnitorStalks P)
  rightUnitor := isoFromStalks (rightUnitorStalks P)
  associator := isoFromStalks (associatorStalks P)
  leftUnitor_stalk V a := by
    change (unitScalar r g c ⊗ₘ 𝟙 (Stalk V a)) ≫
      includeFiber P (unitPoint r g c) V (0 + a) ⟨(0, a), rfl⟩ ≫
      eqToHom (congrArg (Stalk (P.convolution.obj (unitPoint r g c, V))) (zero_add a)) ≫
      mapStalk ((isoFromStalks (leftUnitorStalks P)).hom.app V) a = _
    rw [isoFromStalks_hom, includeFiber_cast_assoc P _ _ _ (zero_add a)]
    change leftUnitInclusion P V a ≫
      (@asIso _ _ _ _ _ (leftUnitInclusion_isIso P V a)).inv ≫ (λ_ (Stalk V a)).hom = _
    simp
  rightUnitor_stalk V a := by
    change (𝟙 (Stalk V a) ⊗ₘ unitScalar r g c) ≫
      includeFiber P V (unitPoint r g c) (a + 0) ⟨(a, 0), rfl⟩ ≫
      eqToHom (congrArg (Stalk (P.convolution.obj (V, unitPoint r g c))) (add_zero a)) ≫
      mapStalk ((isoFromStalks (rightUnitorStalks P)).hom.app V) a = _
    rw [isoFromStalks_hom, includeFiber_cast_assoc P _ _ _ (add_zero a)]
    change rightUnitInclusion P V a ≫
      (@asIso _ _ _ _ _ (rightUnitInclusion_isIso P V a)).inv ≫ (ρ_ (Stalk V a)).hom = _
    simp
  associator_stalk U V W p := by
    generalize D.triples p = q
    rcases q with ⟨a, b, d⟩
    exact associatorOnTriple P U V W a b d

end Constraints

/-- Ordered convolution for the reduced Grassmannian of every complex split torus. -/
theorem torusOrderedConvolution : TorusOrderedConvolution := by
  intro r
  obtain ⟨g, c, hc, _, _, _, _, _, _⟩ := TorusPerverse.torusPerverseEquivalence r
  let x := coordinatesAtRank r
  let D := orderedGeometry x
  exact ⟨D, g, c, geometry_representatives x, geometry_tripleMaps x, finiteDirectImage D,
    ⟨exteriorDescent D c (fun k ↦ (hc k).2)⟩, orderedProduct D g c, ⟨constraints (orderedProduct D g c)⟩⟩

end RepTheorySurvey.Geometric.TorusOrderedConvolution
