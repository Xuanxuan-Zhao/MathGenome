import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GoodTruncations
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.GoodTruncations
open Specs.AdvancedHomologicalAlgebra.DerivedCategory

namespace AdvancedHomologicalAlgebra.GoodTruncations

noncomputable def truncLE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.truncLEType :=
  fun A _ _ n => LE A n

noncomputable def truncGE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.truncGEType :=
  fun A _ _ n => GE A n

noncomputable def inclusion : Specs.AdvancedHomologicalAlgebra.GoodTruncations.inclusionType :=
  fun A _ _ n => (ComplexShape.embeddingUpIntLE n).ιTruncLENatTrans A

noncomputable def projection : Specs.AdvancedHomologicalAlgebra.GoodTruncations.projectionType :=
  fun A _ _ n => (ComplexShape.embeddingUpIntGE n).πTruncGENatTrans A

theorem termsLE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.termsLEType := by
  intro A _ _ K n i
  refine ⟨fun h => ⟨K.truncLEXIso n i h⟩, ?_, fun h => ?_⟩
  · exact ⟨K.truncLEXIsoCycles n ≪≫ ((K.cyclesIsKernel n (n + 1) (by simp)).conePointUniqueUpToIso (limit.isLimit _))⟩
  · exact (K.truncLE n).isZero_of_isStrictlyLE n i h

theorem termsGE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.termsGEType := by
  intro A _ _ K n i
  refine ⟨fun h => ?_, ?_, fun h => ⟨K.truncGEXIso n i h⟩⟩
  · exact (K.truncGE n).isZero_of_isStrictlyGE n i h
  · exact ⟨K.truncGEXIsoOpcycles n ≪≫ ((K.opcyclesIsCokernel (n - 1) n (by simp)).coconePointUniqueUpToIso (colimit.isColimit _))⟩

theorem cohomologyLE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.cohomologyLEType := by
  intro A _ _ K n i
  constructor
  · intro h
    have := K.quasiIsoAt_ιTruncLE n i h
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp this
  · intro h
    exact (K.truncLE n).isZero_of_isLE n i h

theorem cohomologyGE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.cohomologyGEType := by
  intro A _ _ K n i
  constructor
  · intro h
    have := K.quasiIsoAt_πTruncGE n i h
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp this
  · intro h
    exact (K.truncGE n).isZero_of_isGE n i h

theorem preservesQuasiIsoLE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.preservesQuasiIsoLEType := by
  intro A _ _ X Y f n h
  have := h
  exact (CochainComplex.quasiIso_truncLEMap_iff f n).mpr (fun i _ => inferInstance)

theorem preservesQuasiIsoGE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.preservesQuasiIsoGEType := by
  intro A _ _ X Y f n h
  have := h
  exact (CochainComplex.quasiIso_truncGEMap_iff f n).mpr (fun i _ => inferInstance)

theorem comparisonQuasiIso : Specs.AdvancedHomologicalAlgebra.GoodTruncations.comparisonQuasiIsoType := by
  intro A _ _ K n
  infer_instance

theorem distinguished : Specs.AdvancedHomologicalAlgebra.GoodTruncations.distinguishedType := by
  intro A _ _ _ K n
  have h := K.shortComplexTruncLE_shortExact n
  have : QuasiIso (comparison K n) := comparisonQuasiIso A K n
  apply isomorphic_distinguished _ (_root_.DerivedCategory.triangleOfSES_distinguished h)
    _ (Iso.symm ?_)
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (asIso (_root_.DerivedCategory.Q.map (comparison K n))) ?_ ?_ ?_
  · simp only [row, _root_.DerivedCategory.triangleOfSES, Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp]
    simp
    rfl
  · dsimp [row, _root_.DerivedCategory.triangleOfSES]
    rw [Category.id_comp, ← Functor.map_comp]
    exact congrArg _ (K.g_shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl)
  · simp [row, boundary, _root_.DerivedCategory.triangleOfSES]

theorem derivedDescent : Specs.AdvancedHomologicalAlgebra.GoodTruncations.derivedDescentType := by
  intro A _ _ _ n
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  have hLE : W.IsInvertedBy (LE A n ⋙ _root_.DerivedCategory.Q) := by
    intro X Y f hf
    have : QuasiIso f := hf
    have := preservesQuasiIsoLE A X Y f n this
    exact inferInstanceAs (IsIso (_root_.DerivedCategory.Q.map (CochainComplex.truncLEMap f n)))
  have hGE : W.IsInvertedBy (GE A n ⋙ _root_.DerivedCategory.Q) := by
    intro X Y f hf
    have : QuasiIso f := hf
    have := preservesQuasiIsoGE A X Y f n this
    exact inferInstanceAs (IsIso (_root_.DerivedCategory.Q.map (CochainComplex.truncGEMap f n)))
  exact ⟨Localization.lift _ hLE _root_.DerivedCategory.Q,
    Localization.lift _ hGE _root_.DerivedCategory.Q,
    ⟨(Localization.fac _ hLE _root_.DerivedCategory.Q).symm⟩,
    ⟨(Localization.fac _ hGE _root_.DerivedCategory.Q).symm⟩⟩

section RowNaturality
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {X Y : CochainComplex A ℤ}

/-- The natural map on the cokernel short exact sequences. -/
noncomputable def quotientSequenceMap (f : X ⟶ Y) (n : ℤ) :
    X.shortComplexTruncLE n ⟶ Y.shortComplexTruncLE n where
  τ₁ := CochainComplex.truncLEMap f n
  τ₂ := f
  τ₃ := cokernel.map _ _ (CochainComplex.truncLEMap f n) f
    (CochainComplex.ιTruncLE_naturality f n).symm
  comm₁₂ := CochainComplex.ιTruncLE_naturality f n
  comm₂₃ := by dsimp [CochainComplex.shortComplexTruncLE, HomologicalComplex.shortComplexTruncLE]; simp

omit [HasDerivedCategory A] in
@[reassoc]
lemma comparison_naturality (f : X ⟶ Y) (n : ℤ) :
    (quotientSequenceMap f n).τ₃ ≫ comparison Y n =
      comparison X n ≫ CochainComplex.truncGEMap f (n + 1) := by
  apply (cancel_epi (X.shortComplexTruncLE n).g).mp
  rw [← Category.assoc, ← (quotientSequenceMap f n).comm₂₃,
    Category.assoc, Y.g_shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl,
    X.g_shortComplexTruncLEX₃ToTruncGE_assoc n (n + 1) rfl]
  exact (CochainComplex.πTruncGE_naturality f (n + 1)).symm

@[reassoc]
lemma boundary_naturality (f : X ⟶ Y) (n : ℤ) :
    boundary X n ≫ (_root_.DerivedCategory.Q.map (CochainComplex.truncLEMap f n))⟦(1 : ℤ)⟧' =
      _root_.DerivedCategory.Q.map (CochainComplex.truncGEMap f (n + 1)) ≫ boundary Y n := by
  have := comparisonQuasiIso A X n
  have := comparisonQuasiIso A Y n
  apply (cancel_epi (_root_.DerivedCategory.Q.map (comparison X n))).mp
  simp only [boundary, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← _root_.DerivedCategory.Q.map_comp, ← comparison_naturality,
    _root_.DerivedCategory.Q.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact _root_.DerivedCategory.triangleOfSESδ_naturality
    (X.shortComplexTruncLE_shortExact n) (Y.shortComplexTruncLE_shortExact n)
      (quotientSequenceMap f n)

/-- The actual truncation row is a functor on complexes. -/
noncomputable def rowFunctor (n : ℤ) : CochainComplex A ℤ ⥤ Triangle (D A) where
  obj K := row K n
  map f :=
    { hom₁ := _root_.DerivedCategory.Q.map (CochainComplex.truncLEMap f n)
      hom₂ := _root_.DerivedCategory.Q.map f
      hom₃ := _root_.DerivedCategory.Q.map (CochainComplex.truncGEMap f (n + 1))
      comm₁ := by
        dsimp [row]
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg _ (CochainComplex.ιTruncLE_naturality f n).symm
      comm₂ := by
        dsimp [row]
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg _ (CochainComplex.πTruncGE_naturality f (n + 1))
      comm₃ := boundary_naturality f n }
  map_id K := by
    apply Triangle.hom_ext <;> simp [row, CochainComplex.truncLEMap, CochainComplex.truncGEMap]
  map_comp f g := by
    apply Triangle.hom_ext <;> simp [row, CochainComplex.truncLEMap, CochainComplex.truncGEMap]

end RowNaturality

theorem naturalDerivedTriangle :
    Specs.AdvancedHomologicalAlgebra.GoodTruncations.naturalDerivedTriangleType := by
  intro A _ _ _ n
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  have hR : W.IsInvertedBy (rowFunctor (A := A) n) := by
    intro X Y f hf
    have hf : QuasiIso f := hf
    have hLE := preservesQuasiIsoLE A X Y f n hf
    have hGE := preservesQuasiIsoGE A X Y f (n + 1) hf
    exact Triangle.isIso_of_isIsos _
      (inferInstanceAs (IsIso (_root_.DerivedCategory.Q.map (CochainComplex.truncLEMap f n))))
      (inferInstanceAs (IsIso (_root_.DerivedCategory.Q.map f)))
      (inferInstanceAs (IsIso (_root_.DerivedCategory.Q.map (CochainComplex.truncGEMap f (n + 1)))))
  let F := Localization.lift _ hR _root_.DerivedCategory.Q
  let e : _root_.DerivedCategory.Q ⋙ F ≅ rowFunctor n :=
    Localization.fac _ hR _root_.DerivedCategory.Q
  refine ⟨F, fun K => e.app K, ?_, ?_, ?_, ?_⟩
  · intro X
    let K := _root_.DerivedCategory.Q.objPreimage X
    let eX := e.app K
    exact isomorphic_distinguished _ (distinguished A K n) _
      ((F.mapIso (_root_.DerivedCategory.Q.objObjPreimageIso X)).symm ≪≫ eX)
  · intro X Y f
    exact congrArg (fun k => k.hom₁) (e.hom.naturality f)
  · intro X Y f
    exact congrArg (fun k => k.hom₂) (e.hom.naturality f)
  · intro X Y f
    exact congrArg (fun k => k.hom₃) (e.hom.naturality f)

section ShiftCompatibility
variable {A : Type u} [Category.{v} A] [Abelian A]
  {L K : CochainComplex A ℤ}

instance monoInclusion (K : CochainComplex A ℤ) (n : ℤ) : Mono (K.ιTruncLE n) :=
  inferInstanceAs (Mono (HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE n)))

instance epiProjection (K : CochainComplex A ℤ) (n : ℤ) : Epi (K.πTruncGE n) :=
  inferInstanceAs (Epi (HomologicalComplex.πTruncGE K (ComplexShape.embeddingUpIntGE n)))

/-- Universal factorization through the good upper truncation. -/
noncomputable def liftLE (f : L ⟶ K) (n : ℤ) [L.IsStrictlyLE n] : L ⟶ K.truncLE n :=
  inv (L.ιTruncLE n) ≫ CochainComplex.truncLEMap f n

@[reassoc (attr := simp)]
lemma liftLE_comp (f : L ⟶ K) (n : ℤ) [L.IsStrictlyLE n] :
    liftLE f n ≫ K.ιTruncLE n = f := by
  dsimp [liftLE]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

/-- Universal factorization through the good lower truncation. -/
noncomputable def descGE (f : K ⟶ L) (n : ℤ) [L.IsStrictlyGE n] : K.truncGE n ⟶ L :=
  CochainComplex.truncGEMap f n ≫ inv (L.πTruncGE n)

@[reassoc (attr := simp)]
lemma comp_descGE (f : K ⟶ L) (n : ℤ) [L.IsStrictlyGE n] :
    K.πTruncGE n ≫ descGE f n = f := by
  dsimp [descGE]
  rw [← Category.assoc, CochainComplex.πTruncGE_naturality]
  simp

noncomputable def shiftLiftLE (n m : ℤ) (f : L ⟶ K⟦m⟧) [L.IsStrictlyLE (n - m)] :
    L ⟶ (K.truncLE n)⟦m⟧ := by
  let adj := (shiftEquiv (CochainComplex A ℤ) m).symm.toAdjunction
  have : ((shiftEquiv (CochainComplex A ℤ) m).symm.functor.obj L).IsStrictlyLE n :=
    L.isStrictlyLE_shift (n - m) (-m) n (by omega)
  exact adj.homEquiv L (K.truncLE n) (liftLE ((adj.homEquiv L K).symm f) n)

@[reassoc (attr := simp)]
lemma shiftLiftLE_comp (n m : ℤ) (f : L ⟶ K⟦m⟧) [L.IsStrictlyLE (n - m)] :
    shiftLiftLE n m f ≫ (K.ιTruncLE n)⟦m⟧' = f := by
  dsimp [shiftLiftLE]
  rw [← Adjunction.homEquiv_naturality_right, liftLE_comp, Equiv.apply_symm_apply]

noncomputable def shiftDescGE (n m : ℤ) (f : K⟦m⟧ ⟶ L) [L.IsStrictlyGE (n - m)] :
    (K.truncGE n)⟦m⟧ ⟶ L := by
  let adj := (shiftEquiv (CochainComplex A ℤ) m).toAdjunction
  have : ((shiftEquiv (CochainComplex A ℤ) m).inverse.obj L).IsStrictlyGE n :=
    L.isStrictlyGE_shift (n - m) (-m) n (by omega)
  exact (adj.homEquiv (K.truncGE n) L).symm (descGE (adj.homEquiv K L f) n)

@[reassoc (attr := simp)]
lemma comp_shiftDescGE (n m : ℤ) (f : K⟦m⟧ ⟶ L) [L.IsStrictlyGE (n - m)] :
    (K.πTruncGE n)⟦m⟧' ≫ shiftDescGE n m f = f := by
  dsimp [shiftDescGE]
  rw [← Adjunction.homEquiv_naturality_left_symm, comp_descGE, Equiv.symm_apply_apply]

noncomputable def shiftLEIso (n m : ℤ) :
    LE A n ⋙ shiftFunctor (CochainComplex A ℤ) m ≅
      shiftFunctor (CochainComplex A ℤ) m ⋙ LE A (n - m) := by
  have h (K : CochainComplex A ℤ) : ((K.truncLE n)⟦m⟧).IsStrictlyLE (n - m) :=
    (K.truncLE n).isStrictlyLE_shift n m (n - m) (by omega)
  letI := h
  let hom (K : CochainComplex A ℤ) := liftLE ((CochainComplex.ιTruncLE K n)⟦m⟧') (n - m)
  let inv (K : CochainComplex A ℤ) := shiftLiftLE n m (CochainComplex.ιTruncLE (K⟦m⟧) (n - m))
  refine NatIso.ofComponents (fun (K : CochainComplex A ℤ) =>
    { hom := hom K
      inv := inv K
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  · apply (cancel_mono ((CochainComplex.ιTruncLE K n)⟦m⟧')).mp
    simp [hom, inv, Category.assoc]
  · apply (cancel_mono (CochainComplex.ιTruncLE (K⟦m⟧) (n - m))).mp
    simp [hom, inv, Category.assoc]
  · intro X Y f
    apply (cancel_mono (CochainComplex.ιTruncLE (Y⟦m⟧) (n - m))).mp
    dsimp [hom]
    simp only [Category.assoc, liftLE_comp, CochainComplex.ιTruncLE_naturality]
    rw [← Category.assoc, liftLE_comp, ← Functor.map_comp, ← Functor.map_comp,
      CochainComplex.ιTruncLE_naturality]

noncomputable def shiftGEIso (n m : ℤ) :
    GE A n ⋙ shiftFunctor (CochainComplex A ℤ) m ≅
      shiftFunctor (CochainComplex A ℤ) m ⋙ GE A (n - m) := by
  have h (K : CochainComplex A ℤ) : ((K.truncGE n)⟦m⟧).IsStrictlyGE (n - m) :=
    (K.truncGE n).isStrictlyGE_shift n m (n - m) (by omega)
  letI := h
  let hom (K : CochainComplex A ℤ) := shiftDescGE n m (CochainComplex.πTruncGE (K⟦m⟧) (n - m))
  let inv (K : CochainComplex A ℤ) := descGE ((CochainComplex.πTruncGE K n)⟦m⟧') (n - m)
  refine NatIso.ofComponents (fun (K : CochainComplex A ℤ) =>
    { hom := hom K
      inv := inv K
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  · apply (cancel_epi ((CochainComplex.πTruncGE K n)⟦m⟧')).mp
    simp [hom, inv, ← Category.assoc]
  · apply (cancel_epi (CochainComplex.πTruncGE (K⟦m⟧) (n - m))).mp
    simp [hom, inv, ← Category.assoc]
  · intro X Y f
    apply (cancel_epi ((CochainComplex.πTruncGE X n)⟦m⟧')).mp
    dsimp [hom]
    rw [← Functor.map_comp_assoc, CochainComplex.πTruncGE_naturality,
      Functor.map_comp, Category.assoc, comp_shiftDescGE, ← Category.assoc,
      comp_shiftDescGE, CochainComplex.πTruncGE_naturality]

end ShiftCompatibility

theorem shiftLE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.shiftLEType :=
  fun _ _ _ n m => ⟨shiftLEIso n m⟩

theorem shiftGE : Specs.AdvancedHomologicalAlgebra.GoodTruncations.shiftGEType :=
  fun _ _ _ n m => ⟨shiftGEIso n m⟩

section HomotopyCompatibility
variable {A : Type u} [Category.{v} A] [Abelian A]

instance monoInclusionComponent (K : CochainComplex A ℤ) (n i : ℤ) :
    Mono ((K.ιTruncLE n).f i) :=
  inferInstanceAs (Mono ((HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE n)).f i))

instance epiProjectionComponent (K : CochainComplex A ℤ) (n i : ℤ) :
    Epi ((K.πTruncGE n).f i) :=
  inferInstanceAs (Epi ((HomologicalComplex.πTruncGE K (ComplexShape.embeddingUpIntGE n)).f i))

lemma inclusionComponent_isIso (K : CochainComplex A ℤ) (n i : ℤ) (hi : i < n) :
    IsIso ((K.ιTruncLE n).f i) := by
  let e := ComplexShape.embeddingUpIntLE n
  let j := (n - i).natAbs
  have hj : e.f j = i := by
    dsimp [e, j]
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hb : ¬ e.BoundaryLE j := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    dsimp [j]
    rw [Int.natAbs_eq_zero]
    omega
  have h : IsIso ((K.op.πTruncGE e.op).f i) := by
    dsimp [HomologicalComplex.πTruncGE]
    rw [e.op.isIso_liftExtend_f_iff _ _ hj]
    exact K.op.isIso_restrictionToTruncGE' e.op j (by simpa using hb)
  exact inferInstanceAs (IsIso (((K.op.πTruncGE e.op).f i).unop))

lemma projectionComponent_isIso (K : CochainComplex A ℤ) (n i : ℤ) (hi : n < i) :
    IsIso ((K.πTruncGE n).f i) := by
  let e := ComplexShape.embeddingUpIntGE n
  let j := (i - n).natAbs
  have hj : e.f j = i := by
    dsimp [e, j]
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hb : ¬ e.BoundaryGE j := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    dsimp [j]
    rw [Int.natAbs_eq_zero]
    omega
  change IsIso ((HomologicalComplex.πTruncGE K e).f i)
  dsimp [HomologicalComplex.πTruncGE]
  rw [e.isIso_liftExtend_f_iff _ _ hj]
  exact K.isIso_restrictionToTruncGE' e j hb

variable {X Y : CochainComplex A ℤ} (n : ℤ)

noncomputable def liftHomotopyComponent [X.IsStrictlyLE n]
    {f g : X ⟶ Y.truncLE n} (h : Homotopy (f ≫ Y.ιTruncLE n) (g ≫ Y.ιTruncLE n))
    (i j : ℤ) : X.X i ⟶ (Y.truncLE n).X j :=
  if hj : j < n then
    have := inclusionComponent_isIso Y n j hj
    h.hom i j ≫ inv ((Y.ιTruncLE n).f j)
  else 0

@[reassoc (attr := simp)]
lemma liftHomotopyComponent_comp [X.IsStrictlyLE n]
    {f g : X ⟶ Y.truncLE n} (h : Homotopy (f ≫ Y.ιTruncLE n) (g ≫ Y.ιTruncLE n))
    (i j : ℤ) : liftHomotopyComponent n h i j ≫ (Y.ιTruncLE n).f j = h.hom i j := by
  by_cases hj : j < n
  · have := inclusionComponent_isIso Y n j hj
    simp [liftHomotopyComponent, hj]
  · simp only [liftHomotopyComponent, dite_eq_right hj, zero_comp]
    by_cases hij : (ComplexShape.up ℤ).Rel j i
    · exact (X.isZero_of_isStrictlyLE n i (by simpa using (show n < i by
        change j + 1 = i at hij
        omega))).eq_of_src _ _
    · exact (h.zero i j hij).symm

noncomputable def liftHomotopy [X.IsStrictlyLE n]
    {f g : X ⟶ Y.truncLE n} (h : Homotopy (f ≫ Y.ιTruncLE n) (g ≫ Y.ιTruncLE n)) :
    Homotopy f g where
  hom := liftHomotopyComponent n h
  zero i j hij := by
    apply (cancel_mono ((Y.ιTruncLE n).f j)).mp
    simp [h.zero i j hij]
  comm i := by
    apply (cancel_mono ((Y.ιTruncLE n).f i)).mp
    rw [Preadditive.add_comp, Preadditive.add_comp]
    have hn : (ComplexShape.up ℤ).Rel i (i + 1) := by simp
    have hp : (ComplexShape.up ℤ).Rel (i - 1) i := by simp
    rw [dNext_eq _ hn, prevD_eq _ hp, Category.assoc, liftHomotopyComponent_comp]
    rw [Category.assoc, ← (Y.ιTruncLE n).comm (i - 1) i,
      ← Category.assoc, liftHomotopyComponent_comp]
    simpa only [HomologicalComplex.comp_f, dNext_eq _ hn, prevD_eq _ hp] using h.comm i

noncomputable def descHomotopyComponent [Y.IsStrictlyGE n]
    {f g : X.truncGE n ⟶ Y} (h : Homotopy (X.πTruncGE n ≫ f) (X.πTruncGE n ≫ g))
    (i j : ℤ) : (X.truncGE n).X i ⟶ Y.X j :=
  if hi : n < i then
    have := projectionComponent_isIso X n i hi
    inv ((X.πTruncGE n).f i) ≫ h.hom i j
  else 0

@[reassoc (attr := simp)]
lemma comp_descHomotopyComponent [Y.IsStrictlyGE n]
    {f g : X.truncGE n ⟶ Y} (h : Homotopy (X.πTruncGE n ≫ f) (X.πTruncGE n ≫ g))
    (i j : ℤ) : (X.πTruncGE n).f i ≫ descHomotopyComponent n h i j = h.hom i j := by
  by_cases hi : n < i
  · have := projectionComponent_isIso X n i hi
    simp [descHomotopyComponent, hi]
  · simp only [descHomotopyComponent, dite_eq_right hi, comp_zero]
    by_cases hij : (ComplexShape.up ℤ).Rel j i
    · exact (Y.isZero_of_isStrictlyGE n j (by simpa using (show j < n by
        change j + 1 = i at hij
        omega))).eq_of_tgt _ _
    · exact (h.zero i j hij).symm

noncomputable def descHomotopy [Y.IsStrictlyGE n]
    {f g : X.truncGE n ⟶ Y} (h : Homotopy (X.πTruncGE n ≫ f) (X.πTruncGE n ≫ g)) :
    Homotopy f g where
  hom := descHomotopyComponent n h
  zero i j hij := by
    apply (cancel_epi ((X.πTruncGE n).f i)).mp
    simp [h.zero i j hij]
  comm i := by
    apply (cancel_epi ((X.πTruncGE n).f i)).mp
    rw [Preadditive.comp_add, Preadditive.comp_add]
    have hn : (ComplexShape.up ℤ).Rel i (i + 1) := by simp
    have hp : (ComplexShape.up ℤ).Rel (i - 1) i := by simp
    rw [dNext_eq _ hn, prevD_eq _ hp, ← Category.assoc,
      (X.πTruncGE n).comm i (i + 1), Category.assoc, comp_descHomotopyComponent]
    rw [← Category.assoc, comp_descHomotopyComponent]
    simpa only [HomologicalComplex.comp_f, dNext_eq _ hn, prevD_eq _ hp] using h.comm i

end HomotopyCompatibility

theorem preservesHomotopyLE :
    Specs.AdvancedHomologicalAlgebra.GoodTruncations.preservesHomotopyLEType := by
  intro A _ _ X Y f g n ⟨h⟩
  have h' := h.compLeft (X.ιTruncLE n)
  rw [← CochainComplex.ιTruncLE_naturality, ← CochainComplex.ιTruncLE_naturality] at h'
  exact ⟨liftHomotopy n h'⟩

theorem preservesHomotopyGE :
    Specs.AdvancedHomologicalAlgebra.GoodTruncations.preservesHomotopyGEType := by
  intro A _ _ X Y f g n ⟨h⟩
  have h' := h.compRight (Y.πTruncGE n)
  rw [← CochainComplex.πTruncGE_naturality, ← CochainComplex.πTruncGE_naturality] at h'
  exact ⟨descHomotopy n h'⟩

theorem homotopyDescent : Specs.AdvancedHomologicalAlgebra.GoodTruncations.homotopyDescentType := by
  intro A _ _ n
  let F := CategoryTheory.Quotient.lift _ (LE A n ⋙ Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.Q A)
    (fun X Y f g h => by
      obtain ⟨h'⟩ := preservesHomotopyLE A X Y f g n h
      exact HomotopyCategory.eq_of_homotopy _ _ h')
  let G := CategoryTheory.Quotient.lift _ (GE A n ⋙ Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.Q A)
    (fun X Y f g h => by
      obtain ⟨h'⟩ := preservesHomotopyGE A X Y f g n h
      exact HomotopyCategory.eq_of_homotopy _ _ h')
  exact ⟨F, G, ⟨(CategoryTheory.Quotient.lift.isLift _ _ _).symm⟩,
    ⟨(CategoryTheory.Quotient.lift.isLift _ _ _).symm⟩⟩

end AdvancedHomologicalAlgebra.GoodTruncations
