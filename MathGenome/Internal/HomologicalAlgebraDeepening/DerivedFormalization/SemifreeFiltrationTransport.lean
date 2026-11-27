import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeFiltrationTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeFlatness
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorTransport
/-! Transport of a chosen semifree filtration at a fixed module universe. -/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace DerivedFormalization.SemifreeFiltrationTransport

open Specs.DerivedFormalization
open Specs.DerivedFormalization.SemifreeFiltrationTransport
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainRingTransport
  (complexEquivalenceValue complexFunctorValue moduleEquivalenceValue rankOneValue)
open Specs.DerivedFormalization.CochainTensorTransport
  (adequateModelType closedAdjunctionType curryingType ringComparisonType representedUnit)

noncomputable section

universe u a w

variable {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A)

private def cellGeneratorIso (s : ℤ) : (cell e s).X (-s) ≅ rankOneValue e :=
  (representedUnit e).shiftFunctorObjXIso s (-s) 0 (by omega) ≪≫
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 (rankOneValue e)

private def cellGenerator (s : ℤ) : (cell e s).X (-s) :=
  (cellGeneratorIso e s).inv (show rankOneValue e from (1 : A))

private theorem cellGenerator_ne_zero [Nontrivial R] (s : ℤ) : cellGenerator e s ≠ 0 := by
  let : Nontrivial A := e.injective.nontrivial
  intro h
  have h' := congrArg (fun x => (cellGeneratorIso e s).hom x) h
  rw [map_zero] at h'
  change ((cellGeneratorIso e s).inv ≫ (cellGeneratorIso e s).hom) (1 : A) = _ at h'
  rw [Iso.inv_hom_id] at h'
  exact one_ne_zero (show (1 : A) = 0 from h')

private theorem cellIndices_small [Nontrivial R] {I : Type w} (s : I → ℤ)
    (c : Cofan (fun i => cell e (s i))) (hc : IsColimit c) : Small.{a} I := by
  classical
  let mark (i : I) : Σ n : ℤ, c.pt.X n :=
    ⟨-s i, (c.inj i).f (-s i) (cellGenerator e (s i))⟩
  apply small_of_injective (f := mark)
  intro i j heq
  by_contra hij
  let legs (k : I) : cell e (s k) ⟶ cell e (s i) :=
    if h : k = i then eqToHom (congrArg (fun t => cell e (s t)) h) else 0
  let p : c.pt ⟶ cell e (s i) := hc.desc (Cofan.mk _ legs)
  have fac (k : I) : c.inj k ≫ p = legs k := hc.fac (Cofan.mk _ legs) ⟨k⟩
  have hi : c.inj i ≫ p = 𝟙 _ := by rw [fac]; simp [legs]
  have hj : c.inj j ≫ p = 0 := by rw [fac]; simp [legs, Ne.symm hij]
  let applyP (z : Σ n : ℤ, c.pt.X n) : Σ n : ℤ, (cell e (s i)).X n :=
    ⟨z.1, p.f z.1 z.2⟩
  have h := congrArg applyP heq
  change (⟨-s i, (c.inj i ≫ p).f (-s i) (cellGenerator e (s i))⟩ :
    Σ n : ℤ, (cell e (s i)).X n) =
    ⟨-s j, (c.inj j ≫ p).f (-s j) (cellGenerator e (s j))⟩ at h
  rw [hi, hj] at h
  have hz := congrArg (fun z : Σ n : ℤ, (cell e (s i)).X n => z.2 = 0) h
  apply cellGenerator_ne_zero e (s i)
  apply Eq.mpr hz
  simp

private theorem reindexCellsProof : reindexCellsType.{u,a,w} := by
  classical
  intro R A _ _ e I s c hc
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    let k : PEmpty.{a + 1} → I := PEmpty.elim
    let α : stalkSum e (s ∘ k) ≅ c.pt :=
      { hom := 0
        inv := 0
        hom_inv_id := by
          apply HomologicalComplex.hom_ext
          intro n
          ext x
          let := Module.subsingleton R ((stalkSum e (s ∘ k)).X n)
          exact Subsingleton.elim _ _
        inv_hom_id := by
          apply HomologicalComplex.hom_ext
          intro n
          ext x
          let := Module.subsingleton R (c.pt.X n)
          exact Subsingleton.elim _ _ }
    refine ⟨PEmpty.{a + 1}, k, α, ?_, fun _ => inferInstance, fun j => j.elim⟩
    intro h
    obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
    exact (hxy (Subsingleton.elim x y)).elim
  · let := hR
    let := cellIndices_small e s c hc
    let ε : Shrink.{a} I ≃ I := (equivShrink I).symm
    let c' : Cofan (fun j => cell e (s (ε j))) := Cofan.mk c.pt (fun j => c.inj (ε j))
    let hc' : IsColimit c' := hc.whiskerEquivalence (Discrete.equivalence ε)
    let hsum := colimit.isColimit (Discrete.functor (fun j => cell e (s (ε j))))
    refine ⟨Shrink.{a} I, ε, hsum.coconePointUniqueUpToIso hc', fun _ => ε.bijective, ?_, ?_⟩
    · intro h
      obtain ⟨x, y, hxy⟩ := hR.exists_pair_ne
      exact (hxy (h.elim x y)).elim
    · intro j
      exact IsColimit.comp_coconePointUniqueUpToIso_hom hsum hc' ⟨j⟩

private theorem sumComparisonProof : sumComparisonType.{u,a} := by
  intro R A _ _ e I s i
  change (complexFunctorValue e).map
      (colimit.ι (Discrete.functor (fun j => cell e (s j))) ⟨i⟩) ≫ _ = _
  rw [Specs.DerivedFormalization.SemifreeFiltrationTransport.sumComparison, Iso.trans_hom,
    ← Category.assoc, ι_preservesColimitIso_hom, HasColimit.ι_isoOfNatIso_hom]
  rfl

local notation "E" => complexFunctorValue e
local notation "M" => Equivalence.functor (moduleEquivalenceValue e)

private def compareQuotients {X Y : compValue.{a} R} {X' Y' : compValue.{a} A}
    (f : X ⟶ Y) (g : X' ⟶ Y') (x : (E).obj X ≅ X') (y : (E).obj Y ≅ Y')
    (h : (E).map f ≫ y.hom = x.hom ≫ g) : QuotientComparison e f g y := by
  let q := PreservesCokernel.iso E f ≪≫ cokernel.mapIso ((E).map f) g x y h
  refine ⟨q, ?_, fun I s => ⟨?_, ?_⟩⟩
  · simp [q, ← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.mapIso]
  · intro α
    exact ⟨q.symm ≪≫ (E).mapIso α ≪≫
      Specs.DerivedFormalization.SemifreeFiltrationTransport.sumComparison e s, by simp⟩
  · intro β
    let α' := q ≪≫ β ≪≫ (Specs.DerivedFormalization.SemifreeFiltrationTransport.sumComparison e s).symm
    refine ⟨(E).preimageIso α', ?_⟩
    simp [Functor.preimageIso, α']

private def compareInitial {Y : compValue.{a} R} {Y' : compValue.{a} A}
    (y : (E).obj Y ≅ Y') :
    QuotientComparison e (0 : (0 : compValue.{a} R) ⟶ Y) (0 : (0 : compValue.{a} A) ⟶ Y') y :=
  compareQuotients e _ _ (E).mapZeroObject y (by simp)

private def compareStep {S : ℕ ⥤ compValue.{a} R} {T : ℕ ⥤ compValue.{a} A}
    (α : S ⋙ E ≅ T) (n : ℕ) :
    QuotientComparison e (S.map (homOfLE (Nat.le_succ n)))
      (T.map (homOfLE (Nat.le_succ n))) (α.app (n + 1)) :=
  compareQuotients e _ _ (α.app n) (α.app (n + 1)) (α.hom.naturality _)

private theorem compareSplits {S : ℕ ⥤ compValue.{a} R} {T : ℕ ⥤ compValue.{a} A}
    (α : S ⋙ E ≅ T) (n : ℕ) (i : ℤ) :
    let transport := fun (r : (S.obj (n + 1)).X i ⟶ (S.obj n).X i) =>
      (α.inv.app (n + 1)).f i ≫ (M).map r ≫ (α.hom.app n).f i
    Function.Bijective transport ∧
      ∀ r, (S.map (homOfLE (Nat.le_succ n))).f i ≫ r = 𝟙 _ ↔
        (T.map (homOfLE (Nat.le_succ n))).f i ≫ transport r = 𝟙 _ := by
  let u := (HomologicalComplex.eval (ModuleCat.{a} A) (.up ℤ) i).mapIso (α.app n)
  let v := (HomologicalComplex.eval (ModuleCat.{a} A) (.up ℤ) i).mapIso (α.app (n + 1))
  let f := (S.map (homOfLE (Nat.le_succ n))).f i
  let g := (T.map (homOfLE (Nat.le_succ n))).f i
  let hM := Functor.FullyFaithful.ofFullyFaithful M
  let ev := hM.homEquiv.trans (v.homCongr u)
  change Function.Bijective ev ∧ ∀ r, f ≫ r = 𝟙 _ ↔ g ≫ (v.inv ≫ (M).map r ≫ u.hom) = 𝟙 _
  refine ⟨ev.bijective, fun r => ?_⟩
  have square : g ≫ v.inv = u.inv ≫ (M).map f :=
    congrArg (fun k => k.f i) (α.inv.naturality (homOfLE (Nat.le_succ n)))
  rw [← Category.assoc g, square, Category.assoc, ← Category.assoc ((M).map f),
    ← Functor.map_comp]
  constructor
  · intro hr
    simp [hr]
  · intro hr
    apply (M).map_injective
    rw [(M).map_id]
    have h := congrArg (fun k => u.hom ≫ k ≫ u.inv) hr
    simpa [Category.assoc] using h

private theorem degreewiseComparison
    {S : ℕ ⥤ compValue.{a} R} {T : ℕ ⥤ compValue.{a} A}
    {F : compValue.{a} R} {G : compValue.{a} A}
    (α : S ⋙ E ≅ T) (φ : (E).obj F ≅ G)
    (L : S ⟶ (Functor.const ℕ).obj F) (L' : T ⟶ (Functor.const ℕ).obj G)
    (h : ∀ n, (E).map (L.app n) ≫ φ.hom = α.hom.app n ≫ L'.app n) :
    ((∀ n i, Function.Injective ((L.app n).f i)) ↔
      (∀ n i, Function.Injective ((L'.app n).f i))) ∧
    ((∀ (i : ℤ) (x : F.X i), ∃ (n : ℕ) (y : (S.obj n).X i), (L.app n).f i y = x) ↔
      (∀ (i : ℤ) (x : G.X i), ∃ (n : ℕ) (y : (T.obj n).X i), (L'.app n).f i y = x)) := by
  have square (n : ℕ) (i : ℤ) (x : (S.obj n).X i) :
      φ.hom.f i ((L.app n).f i x) = (L'.app n).f i ((α.hom.app n).f i x) :=
    congrArg (fun z : (E).obj (S.obj n) ⟶ G =>
      z.f i (show ((E).obj (S.obj n)).X i from x)) (h n)
  have stageBij (n : ℕ) (i : ℤ) : Function.Bijective ((α.hom.app n).f i) :=
    ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩
  have ambientBij (i : ℤ) : Function.Bijective (φ.hom.f i) :=
    ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩
  constructor
  · constructor
    · intro hL n i x y hxy
      obtain ⟨x₀, rfl⟩ := (stageBij n i).2 x
      obtain ⟨y₀, rfl⟩ := (stageBij n i).2 y
      exact congrArg _ (hL n i ((ambientBij i).1
        ((square n i x₀).trans (hxy.trans (square n i y₀).symm))))
    · intro hL n i x y hxy
      exact (stageBij n i).1 (hL n i
        ((square n i x).symm.trans ((congrArg (φ.hom.f i) hxy).trans (square n i y))))
  · constructor
    · intro hL i x
      obtain ⟨x₀, rfl⟩ := (ambientBij i).2 x
      obtain ⟨n, y, hy⟩ := hL i x₀
      exact ⟨n, (α.hom.app n).f i y,
        (square n i y).symm.trans (congrArg (φ.hom.f i) hy)⟩
    · intro hL i x
      obtain ⟨n, y, hy⟩ := hL i (φ.hom.f i x)
      obtain ⟨y₀, rfl⟩ := (stageBij n i).2 y
      exact ⟨n, y₀, (ambientBij i).1 ((square n i y₀).trans hy)⟩

private def comparison
    {F : compValue.{a} R} {G : compValue.{a} A}
    (φ : (E).obj F ≅ G) (P : Filtration e F) (T : SemifreeFiltration G)
    (α : P.stages ⋙ E ≅ T.stages)
    (h : ∀ n, (E).map (P.inclusions.app n) ≫ φ.hom = α.hom.app n ≫ T.inclusions.app n) :
    FiltrationComparison e φ P T where
  stages := α
  inclusions := h
  split := compareSplits e α
  initial := compareInitial e (α.app 0)
  successive := compareStep e α
  originalColimit := by
    have hcol := (IsColimit.precomposeHomEquiv α T.cocone).symm T.isColimit
    exact isColimitOfReflects E
      (IsColimit.ofIsoColimit hcol (Cocone.ext φ h).symm)
  diagonalColimit := T.isColimit
  augmentation p ψ n := by
    rw [(E).map_comp, Category.assoc, ← Category.assoc (α.hom.app n), ← h n,
      Category.assoc, Iso.hom_inv_id_assoc]

private theorem forwardFiltration {F : compValue.{a} R} {G : compValue.{a} A}
    (φ : (E).obj F ≅ G) (P : Filtration e F) :
    ∃ T : SemifreeFiltration G, Nonempty (FiltrationComparison e φ P T) := by
  let S := P.stages ⋙ E
  let α : P.stages ⋙ E ≅ S := Iso.refl _
  let L : S ⟶ (Functor.const ℕ).obj G :=
    Functor.whiskerRight P.inclusions E ≫ (Functor.const ℕ).map φ.hom
  have h (n : ℕ) : (E).map (P.inclusions.app n) ≫ φ.hom = α.hom.app n ≫ L.app n := by
    change _ = 𝟙 _ ≫ ((E).map (P.inclusions.app n) ≫ φ.hom)
    rw [Category.id_comp]
  have degree := degreewiseComparison e α φ P.inclusions L h
  let T : SemifreeFiltration G :=
    { stages := S
      inclusions := L
      injective := degree.1.mp P.injective
      exhaustive := degree.2.mp P.exhaustive
      split := by
        intro n i
        obtain ⟨r, hr⟩ := P.split n i
        refine ⟨(M).map r, ?_⟩
        change (M).map ((P.stages.map (homOfLE (Nat.le_succ n))).f i) ≫ (M).map r = _
        rw [← (M).map_comp, hr, (M).map_id]
        rfl
      initial := by
        obtain ⟨I, s, ⟨p⟩⟩ := P.initial
        obtain ⟨q, _⟩ := (compareInitial e (α.app 0)).presentation I s |>.1 p
        exact ⟨I, s, ⟨q⟩⟩
      successive := by
        intro n
        obtain ⟨I, s, ⟨p⟩⟩ := P.successive n
        obtain ⟨q, _⟩ := (compareStep e α n).presentation I s |>.1 p
        exact ⟨I, s, ⟨q⟩⟩ }
  exact ⟨T, ⟨comparison e φ P T α h⟩⟩

private def pullbackInclusions
    {S : ℕ ⥤ compValue.{a} R} {T : ℕ ⥤ compValue.{a} A}
    {F : compValue.{a} R} {G : compValue.{a} A}
    (α : S ⋙ E ≅ T) (φ : (E).obj F ≅ G) (L : T ⟶ (Functor.const ℕ).obj G) :
    S ⟶ (Functor.const ℕ).obj F where
  app n := (E).preimage (α.hom.app n ≫ L.app n ≫ φ.inv)
  naturality n m f := by
    apply (E).map_injective
    simp only [Functor.const_obj_map, Functor.map_comp, Functor.map_preimage]
    have hn := α.hom.naturality f
    change (E).map (S.map f) ≫ α.hom.app m = α.hom.app n ≫ T.map f at hn
    have hL : T.map f ≫ L.app m = L.app n := (L.naturality f).trans (Category.comp_id _)
    rw [← Category.assoc, hn, Category.assoc, ← Category.assoc (T.map f), hL]
    change _ = _ ≫ (E).map (𝟙 F)
    simp

private theorem backwardFiltration {F : compValue.{a} R} {G : compValue.{a} A}
    (φ : (E).obj F ≅ G) (T : SemifreeFiltration G) :
    ∃ P : Filtration e F, Nonempty (FiltrationComparison e φ P T) := by
  let B := (complexEquivalenceValue e).inverse
  let S := T.stages ⋙ B
  let α : S ⋙ E ≅ T.stages :=
    NatIso.ofComponents (fun n => (complexEquivalenceValue e).counitIso.app (T.stages.obj n))
      (fun f => (complexEquivalenceValue e).counitIso.hom.naturality (T.stages.map f))
  let L := pullbackInclusions e α φ T.inclusions
  have h (n : ℕ) : (E).map (L.app n) ≫ φ.hom = α.hom.app n ≫ T.inclusions.app n := by
    change (E).map ((E).preimage (α.hom.app n ≫ T.inclusions.app n ≫ φ.inv)) ≫ φ.hom = _
    simp
  have degree := degreewiseComparison e α φ L T.inclusions h
  let P : Filtration e F :=
    { stages := S
      inclusions := L
      injective := degree.1.mpr T.injective
      exhaustive := degree.2.mpr T.exhaustive
      split := by
        intro n i
        obtain ⟨r, hr⟩ := T.split n i
        obtain ⟨r', hrr⟩ := (compareSplits e α n i).1.2 r
        exact ⟨r', (compareSplits e α n i).2 r' |>.mpr (by simpa only [hrr] using hr)⟩
      initial := by
        obtain ⟨I, s, ⟨q⟩⟩ := T.initial
        obtain ⟨p, _⟩ := (compareInitial e (α.app 0)).presentation I s |>.2 q
        exact ⟨I, s, ⟨p⟩⟩
      successive := by
        intro n
        obtain ⟨I, s, ⟨q⟩⟩ := T.successive n
        obtain ⟨p, _⟩ := (compareStep e α n).presentation I s |>.2 q
        exact ⟨I, s, ⟨p⟩⟩ }
  exact ⟨P, ⟨comparison e φ P T α h⟩⟩

private theorem transportFiltrationProof : transportFiltrationType.{u,a} := by
  intro R A _ _ e F G φ
  exact ⟨forwardFiltration e φ, backwardFiltration e φ⟩

private theorem filtrationIsKFlatProof (h : ringComparisonType.{u,a}) :
    filtrationIsKFlatType.{u,a} := by
  intro R A _ _ e F P
  obtain ⟨T, _⟩ := forwardFiltration e (Iso.refl ((complexFunctorValue e).obj F)) P
  obtain ⟨C⟩ := h e
  exact (C.kFlat F).mp ((DerivedFormalization.CochainTensor.diagonalKFlat _).mpr T.isKFlat)

private theorem diagonalProof : diagonalType.{u} := by
  intro R _ F
  let e := RingEquiv.refl R
  let ident : (moduleEquivalenceValue e).functor ≅ 𝟭 (ModuleCat.{u} R) :=
    ModuleCat.restrictScalarsId R
  let φ : (complexFunctorValue e).obj F ≅ F :=
    (NatIso.mapHomologicalComplex ident (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (.up ℤ)).app F
  have h := transportFiltrationProof e φ
  refine ⟨⟨?_, ?_⟩, DerivedFormalization.CochainTensor.diagonalKFlat F⟩
  · rintro ⟨P⟩
    obtain ⟨T, _⟩ := h.1 P
    exact ⟨T⟩
  · rintro ⟨T⟩
    obtain ⟨P, _⟩ := h.2 T
    exact ⟨P⟩

theorem reindexCells_conditional.{ur,ar,wr}
    (_ : adequateModelType.{ur,ar}) (_ : closedAdjunctionType.{ur,ar})
    (_ : curryingType.{ur,ar}) (_ : ringComparisonType.{ur,ar}) : reindexCellsType.{ur,ar,wr} :=
  reindexCellsProof

theorem sumComparison_conditional.{ur,ar}
    (_ : adequateModelType.{ur,ar}) (_ : closedAdjunctionType.{ur,ar})
    (_ : curryingType.{ur,ar}) (_ : ringComparisonType.{ur,ar}) : sumComparisonType.{ur,ar} :=
  sumComparisonProof

theorem transportFiltration_conditional.{ur,ar}
    (_ : adequateModelType.{ur,ar}) (_ : closedAdjunctionType.{ur,ar})
    (_ : curryingType.{ur,ar}) (_ : ringComparisonType.{ur,ar}) : transportFiltrationType.{ur,ar} :=
  transportFiltrationProof

theorem filtrationIsKFlat_conditional.{ur,ar}
    (_ : adequateModelType.{ur,ar}) (_ : closedAdjunctionType.{ur,ar})
    (_ : curryingType.{ur,ar}) (h : ringComparisonType.{ur,ar}) : filtrationIsKFlatType.{ur,ar} :=
  filtrationIsKFlatProof h

theorem diagonal_conditional.{ur}
    (_ : adequateModelType.{ur,ur}) (_ : closedAdjunctionType.{ur,ur})
    (_ : curryingType.{ur,ur}) (_ : ringComparisonType.{ur,ur}) : diagonalType.{ur} :=
  diagonalProof

end

end DerivedFormalization.SemifreeFiltrationTransport

universe v8_closure_5d195dab6aef0287_u0 v8_closure_5d195dab6aef0287_u1 v8_closure_5d195dab6aef0287_u2
theorem _root_.«DerivedFormalization».«SemifreeFiltrationTransport».«diagonal» : _root_.«Specs».«DerivedFormalization».«SemifreeFiltrationTransport».«diagonalType».{v8_closure_5d195dab6aef0287_u0} :=
  @_root_.«DerivedFormalization».«SemifreeFiltrationTransport».«diagonal_conditional».{v8_closure_5d195dab6aef0287_u0} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u0})
theorem _root_.«DerivedFormalization».«SemifreeFiltrationTransport».«filtrationIsKFlat» : _root_.«Specs».«DerivedFormalization».«SemifreeFiltrationTransport».«filtrationIsKFlatType».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1} :=
  @_root_.«DerivedFormalization».«SemifreeFiltrationTransport».«filtrationIsKFlat_conditional».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1})
theorem _root_.«DerivedFormalization».«SemifreeFiltrationTransport».«reindexCells» : _root_.«Specs».«DerivedFormalization».«SemifreeFiltrationTransport».«reindexCellsType».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1, v8_closure_5d195dab6aef0287_u2} :=
  @_root_.«DerivedFormalization».«SemifreeFiltrationTransport».«reindexCells_conditional».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1, v8_closure_5d195dab6aef0287_u2} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1})
theorem _root_.«DerivedFormalization».«SemifreeFiltrationTransport».«sumComparison» : _root_.«Specs».«DerivedFormalization».«SemifreeFiltrationTransport».«sumComparisonType».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1} :=
  @_root_.«DerivedFormalization».«SemifreeFiltrationTransport».«sumComparison_conditional».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1})
theorem _root_.«DerivedFormalization».«SemifreeFiltrationTransport».«transportFiltration» : _root_.«Specs».«DerivedFormalization».«SemifreeFiltrationTransport».«transportFiltrationType».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1} :=
  @_root_.«DerivedFormalization».«SemifreeFiltrationTransport».«transportFiltration_conditional».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_5d195dab6aef0287_u0, v8_closure_5d195dab6aef0287_u1})
