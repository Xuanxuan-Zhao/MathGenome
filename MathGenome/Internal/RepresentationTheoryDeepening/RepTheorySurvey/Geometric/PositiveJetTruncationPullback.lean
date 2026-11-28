import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.PositiveJetTruncationPullback
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.PositiveJetTruncationPullback

open Analytic BoundedLatticeSpecs EquivariantIntersectionComplexesSpecs
open LatticeModelSpecs PositiveJetTruncationPullbackSpecs

open private jetConstantCoeff isUnit_jetReduction from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

private theorem constantCoeff_apply {k : ℕ} (x : JetRing (k + 1)) :
    jetConstantCoeff (k + 1) (Nat.succ_pos k) x = jetCoefficients (k + 1) x 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (PowerSeries.coeff_zero_eq_constantCoeff_apply f).symm

private def constantMatrix {k : ℕ} (C : JetMatrixCoefficients 2 (k + 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  C.map (fun x => x 0)

private theorem isUnit_det_iff {k : ℕ} (A : Matrix (Fin 2) (Fin 2) (JetRing (k + 1))) :
    IsUnit A.det ↔ IsUnit (constantMatrix (jetMatrixCoefficients A)).det := by
  let e := jetConstantCoeff (k + 1) (Nat.succ_pos k)
  have he : A.map e = constantMatrix (jetMatrixCoefficients A) :=
    Matrix.ext fun i j => constantCoeff_apply (A i j)
  rw [← he]
  change IsUnit A.det ↔ IsUnit (e.mapMatrix A).det
  rw [← e.map_det]
  constructor
  · exact fun hu => hu.map e
  · obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective A.det
    change jetReduction (k + 1) f = A.det at hf
    rw [← hf]
    exact fun hu => (isUnit_jetReduction (Nat.succ_pos k) f).mpr
      (PowerSeries.isUnit_iff_constantCoeff.mpr hu)

private def jetOfCoefficients {k : ℕ} (C : JetMatrixCoefficients 2 (k + 1))
    (hC : IsUnit (constantMatrix C).det) : PositiveJet k :=
  Matrix.GeneralLinearGroup.mk'' (C.map (jetCoefficients (k + 1)).symm)
    (by
      apply (isUnit_det_iff _).mpr
      have h : jetMatrixCoefficients (C.map (jetCoefficients (k + 1)).symm) = C :=
        Matrix.ext fun i j => (jetCoefficients (k + 1)).apply_symm_apply (C i j)
      rwa [h])

private theorem coefficients_jetOfCoefficients {k : ℕ} (C : JetMatrixCoefficients 2 (k + 1))
    (hC : IsUnit (constantMatrix C).det) :
    jetMatrixCoefficients (jetOfCoefficients C hC).val = C :=
  Matrix.ext fun i j => (jetCoefficients (k + 1)).apply_symm_apply (C i j)

private theorem coefficients_truncation {k l : ℕ} (h : k ≤ l) (g : PositiveJet l)
    (a b : Fin 2) (i : Fin (k + 1)) :
    jetMatrixCoefficients (jetTruncation h g).val a b i =
      jetMatrixCoefficients g.val a b (i.castLE (Nat.succ_le_succ h)) := by
  change jetCoefficients (k + 1) (truncateJet (Nat.succ_le_succ h) (g.val a b)) i =
    jetCoefficients (l + 1) (g.val a b) (i.castLE (Nat.succ_le_succ h))
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (g.val a b)
  change jetReduction (l + 1) f = g.val a b at hf
  rw [← hf]
  rfl

private theorem continuous_coefficient {k : ℕ} (c : ContinuousJets) (a b : Fin 2)
    (i : Fin (k + 1)) :
    Continuous (fun g : PositiveJet k => jetMatrixCoefficients g.val a b i) :=
  (continuous_apply i).comp ((continuous_apply b).comp
    ((continuous_apply a).comp (c.coefficientOpen k).continuous))

/-- Zero-padding and scaling the discarded coefficients both preserve
invertibility, since they leave the constant matrix unchanged. -/
theorem truncationGeometry : TruncationGeometry := by
  intro c k l h
  let pad (g : PositiveJet k) : JetMatrixCoefficients 2 (l + 1) :=
    fun a b i => if hi : i.val < k + 1 then jetMatrixCoefficients g.val a b ⟨i.val, hi⟩ else 0
  let deform (p : unitInterval × PositiveJet l) : JetMatrixCoefficients 2 (l + 1) :=
    fun a b i => if i.val < k + 1 then jetMatrixCoefficients p.2.val a b i
      else (1 - (p.1.val : ℂ)) * jetMatrixCoefficients p.2.val a b i
  have hpad (g : PositiveJet k) : IsUnit (constantMatrix (pad g)).det := by
    have he : constantMatrix (pad g) = constantMatrix (jetMatrixCoefficients g.val) := by
      ext a b
      change pad g a b 0 = jetMatrixCoefficients g.val a b 0
      exact dite_eq_left (show (0 : Fin (l + 1)).val < k + 1 from Nat.succ_pos k)
    rw [he]
    exact (isUnit_det_iff g.val).mp (Matrix.isUnits_det_units g)
  have hdeform (p : unitInterval × PositiveJet l) :
      IsUnit (constantMatrix (deform p)).det := by
    have he : constantMatrix (deform p) = constantMatrix (jetMatrixCoefficients p.2.val) := by
      ext a b
      change deform p a b 0 = jetMatrixCoefficients p.2.val a b 0
      exact ite_eq_left (show (0 : Fin (l + 1)).val < k + 1 from Nat.succ_pos k)
    rw [he]
    exact (isUnit_det_iff p.2.val).mp (Matrix.isUnits_det_units p.2)
  let s (g : PositiveJet k) : PositiveJet l := jetOfCoefficients (pad g) (hpad g)
  let D (p : unitInterval × PositiveJet l) : PositiveJet l :=
    jetOfCoefficients (deform p) (hdeform p)
  have hs (g : PositiveJet k) : jetMatrixCoefficients (s g).val = pad g :=
    coefficients_jetOfCoefficients _ _
  have hD (p : unitInterval × PositiveJet l) : jetMatrixCoefficients (D p).val = deform p :=
    coefficients_jetOfCoefficients _ _
  have hs_cont : Continuous s := by
    apply (c.coefficientOpen l).toIsEmbedding.continuous_iff.mpr
    have he : (fun g : PositiveJet k => jetMatrixCoefficients (s g).val) = pad := funext hs
    change Continuous (fun g : PositiveJet k => jetMatrixCoefficients (s g).val)
    rw [he]
    refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    by_cases hi : i.val < k + 1
    · simpa only [pad, dite_eq_left hi] using continuous_coefficient c a b ⟨i.val, hi⟩
    · simpa only [pad, dite_eq_right hi] using
        (continuous_const : Continuous (fun _ : PositiveJet k => (0 : ℂ)))
  have hD_cont : Continuous D := by
    apply (c.coefficientOpen l).toIsEmbedding.continuous_iff.mpr
    have he : (fun p : unitInterval × PositiveJet l => jetMatrixCoefficients (D p).val) =
        deform := funext hD
    change Continuous (fun p : unitInterval × PositiveJet l => jetMatrixCoefficients (D p).val)
    rw [he]
    refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    have hg : Continuous (fun p : unitInterval × PositiveJet l =>
        jetMatrixCoefficients p.2.val a b i) :=
      (continuous_coefficient c a b i).comp continuous_snd
    by_cases hi : i.val < k + 1
    · simpa only [deform, ite_eq_left hi] using hg
    · have ht : Continuous (fun p : unitInterval × PositiveJet l => (p.1.val : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      have hprod : Continuous (fun p : unitInterval × PositiveJet l =>
          (1 - (p.1.val : ℂ)) * jetMatrixCoefficients p.2.val a b i) :=
        (continuous_const.sub ht).mul hg
      simpa only [deform, ite_eq_right hi] using hprod
  refine ⟨TopCat.ofHom ⟨s, hs_cont⟩, TopCat.ofHom ⟨D, hD_cont⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply TopCat.ext
    intro (g : PositiveJet k)
    change jetTruncation h (s g) = g
    apply (c.coefficientOpen k).injective
    ext a b i
    change jetMatrixCoefficients (jetTruncation h (s g)).val a b i =
      jetMatrixCoefficients g.val a b i
    rw [coefficients_truncation, hs]
    exact dite_eq_left i.isLt
  · intro (g : PositiveJet l)
    change D (0, g) = g
    apply (c.coefficientOpen l).injective
    ext a b i
    change jetMatrixCoefficients (D (0, g)).val a b i = jetMatrixCoefficients g.val a b i
    rw [hD]
    simp [deform]
  · intro (g : PositiveJet l)
    change D (1, g) = s (jetTruncation h g)
    apply (c.coefficientOpen l).injective
    ext a b i
    change jetMatrixCoefficients (D (1, g)).val a b i =
      jetMatrixCoefficients (s (jetTruncation h g)).val a b i
    rw [hD, hs]
    by_cases hi : i.val < k + 1
    · simp only [deform, pad, ite_eq_left hi, dite_eq_left hi, coefficients_truncation]
      rfl
    · simp only [deform, pad, ite_eq_right hi, dite_eq_right hi, Set.Icc.coe_one,
        Complex.ofReal_one, sub_self, zero_mul]
  · intro t (g : PositiveJet l)
    change jetTruncation h (D (t, g)) = jetTruncation h g
    apply (c.coefficientOpen k).injective
    ext a b i
    change jetMatrixCoefficients (jetTruncation h (D (t, g))).val a b i =
      jetMatrixCoefficients (jetTruncation h g).val a b i
    rw [coefficients_truncation, coefficients_truncation, hD]
    exact ite_eq_left i.isLt
  · intro g a b i
    exact congrFun (congrFun (congrFun (hs g) a) b) i
  · intro t g a b i
    exact congrFun (congrFun (congrFun (hD (t, g)) a) b) i

open IntersectionComplex (boundedBelowPullbackComposition pullbackSquare)

private def intervalProjection (Y : TopCat.{0}) : TopCat.of (unitInterval × Y) ⟶ Y :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

private def intervalEndpoint (Y : TopCat.{0}) (t : unitInterval) :
    Y ⟶ TopCat.of (unitInterval × Y) :=
  TopCat.ofHom ⟨fun y => (t, y), continuous_const.prodMk continuous_id⟩

private def sectionPullbackIso {Y X : TopCat.{0}} {q : Y ⟶ X} {s : X ⟶ Y}
    (hs : s ≫ q = 𝟙 X) :
    boundedBelowInverseImage q ⋙ boundedBelowInverseImage s ≅ 𝟭 (BoundedBelow X) :=
  (boundedBelowPullbackComposition s q).symm ≪≫
    eqToIso (congrArg (fun f => boundedBelowInverseImage f) hs) ≪≫
    NatIso.ofComponents
      (fun F => ObjectProperty.isoMk _
        ((DerivedPullbackPasting.derivedInverseImageIdentity X).app F.obj))
      (fun f => by
        apply ObjectProperty.hom_ext
        exact (DerivedPullbackPasting.derivedInverseImageIdentity X).hom.naturality f.hom)

private theorem map_eq_of_iso {C E : Type*} [Category* C] [Category* E]
    {F G : C ⥤ E} (e : F ≅ G) {A B : C} {f g : A ⟶ B}
    (h : F.map f = F.map g) : G.map f = G.map g := by
  apply (cancel_epi (e.hom.app A)).mp
  rw [← e.hom.naturality f, ← e.hom.naturality g, h]

/-- Restriction to the section is inverse to pullback on morphisms. To verify
injectivity of restriction, compare the two endpoint restrictions of the
deformation pullback using full faithfulness of the interval projection. -/
private theorem fullyFaithfulOfDeformation
    (hInterval : ∀ Z : TopCat.{0}, Nonempty ((boundedBelowInverseImage
      (intervalProjection Z)).FullyFaithful))
    {Y X : TopCat.{0}} (q : Y ⟶ X) (s : X ⟶ Y)
    (D : TopCat.of (unitInterval × Y) ⟶ Y) (hs : s ≫ q = 𝟙 X)
    (h0 : ∀ y, D (0, y) = y) (h1 : ∀ y, D (1, y) = s (q y))
    (hD : ∀ t y, q (D (t, y)) = q y) :
    Nonempty ((boundedBelowInverseImage q).FullyFaithful) := by
  let Q := boundedBelowInverseImage q
  let S := boundedBelowInverseImage s
  let P := boundedBelowInverseImage (intervalProjection Y)
  let H := boundedBelowInverseImage D
  let E0 := boundedBelowInverseImage (intervalEndpoint Y 0)
  let E1 := boundedBelowInverseImage (intervalEndpoint Y 1)
  let qs : (Q ⋙ S).FullyFaithful :=
    (Functor.FullyFaithful.id _).ofIso (sectionPullbackIso hs).symm
  let d0 : (H ⋙ E0).FullyFaithful :=
    (Functor.FullyFaithful.id _).ofIso (sectionPullbackIso (TopCat.ext h0)).symm
  let p1 : (P ⋙ E1).FullyFaithful :=
    (Functor.FullyFaithful.id _).ofIso
      (sectionPullbackIso (q := intervalProjection Y) (s := intervalEndpoint Y 1) rfl).symm
  let d1 : H ⋙ E1 ≅ S ⋙ Q := pullbackSquare (TopCat.ext h1)
  let e : Q ⋙ H ≅ Q ⋙ P := pullbackSquare (TopCat.ext fun p => hD p.1 p.2)
  obtain ⟨pFull⟩ := hInterval Y
  have restr_injective {A B : BoundedBelow X} {f g : Q.obj A ⟶ Q.obj B}
      (hfg : S.map f = S.map g) : f = g := by
    have ht : E1.map (H.map f) = E1.map (H.map g) :=
      map_eq_of_iso d1.symm (congrArg (fun b => Q.map b) hfg)
    let f' := e.inv.app A ≫ H.map f ≫ e.hom.app B
    let g' := e.inv.app A ≫ H.map g ≫ e.hom.app B
    have ht' : E1.map f' = E1.map g' := by
      simp only [f', g', Functor.map_comp, ht]
    obtain ⟨u, hu⟩ := pFull.map_surjective f'
    obtain ⟨v, hv⟩ := pFull.map_surjective g'
    have huv : u = v := p1.map_injective (by
      change E1.map (P.map u) = E1.map (P.map v)
      rw [hu, hv, ht'])
    have hfg' : f' = g' := by rw [← hu, ← hv, huv]
    apply d0.map_injective
    change E0.map (H.map f) = E0.map (H.map g)
    apply congrArg (fun a => E0.map a)
    apply (cancel_epi (e.inv.app A)).mp
    apply (cancel_mono (e.hom.app B)).mp
    simpa only [Category.assoc] using hfg'
  refine ⟨{
    preimage := fun f => qs.preimage (S.map f)
    map_preimage := fun f => restr_injective (qs.map_preimage (S.map f))
    preimage_map := fun f => qs.preimage_map f }⟩

private def productMap {U V X Y : TopCat.{0}} (f : U ⟶ V) (g : X ⟶ Y) :
    TopCat.of (U × X) ⟶ TopCat.of (V × Y) :=
  TopCat.ofHom ⟨fun p => (f p.1, g p.2),
    (f.hom.continuous.comp continuous_fst).prodMk (g.hom.continuous.comp continuous_snd)⟩

private theorem parameterMap_eq (J : JetSystem.{0}) {k l : ℕ} (h : k ≤ l)
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    J.parameterMap h f = productMap (J.truncate k l h) f := rfl

private structure SectionDeformation {Y X : TopCat.{0}} (q : Y ⟶ X) where
  sectionMap : X ⟶ Y
  deform : TopCat.of (unitInterval × Y) ⟶ Y
  section_comp : sectionMap ≫ q = 𝟙 X
  zero (y : Y) : deform (0, y) = y
  one (y : Y) : deform (1, y) = sectionMap (q y)
  over (t : unitInterval) (y : Y) : q (deform (t, y)) = q y

private def SectionDeformation.id (X : TopCat.{0}) : SectionDeformation (𝟙 X) where
  sectionMap := 𝟙 X
  deform := intervalProjection X
  section_comp := Category.id_comp _
  zero _ := rfl
  one _ := rfl
  over _ _ := rfl

private def SectionDeformation.prod {U V X Y : TopCat.{0}} {f : U ⟶ V} {g : X ⟶ Y}
    (d : SectionDeformation f) (e : SectionDeformation g) :
    SectionDeformation (productMap f g) where
  sectionMap := productMap d.sectionMap e.sectionMap
  deform := TopCat.ofHom
    ⟨fun p => (d.deform (p.1, p.2.1), e.deform (p.1, p.2.2)),
      (d.deform.hom.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (e.deform.hom.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩
  section_comp := TopCat.ext fun p => Prod.ext
    (congrArg (fun t : V ⟶ V => t p.1) d.section_comp)
    (congrArg (fun t : Y ⟶ Y => t p.2) e.section_comp)
  zero p := Prod.ext (d.zero p.1) (e.zero p.2)
  one p := Prod.ext (d.one p.1) (e.one p.2)
  over t p := Prod.ext (d.over t p.1) (e.over t p.2)

private theorem SectionDeformation.fullyFaithful
    {Y X : TopCat.{0}} {q : Y ⟶ X} (d : SectionDeformation q)
    (hInterval : ∀ Z : TopCat.{0}, Nonempty ((boundedBelowInverseImage
      (intervalProjection Z)).FullyFaithful)) :
    Nonempty ((boundedBelowInverseImage q).FullyFaithful) :=
  fullyFaithfulOfDeformation hInterval q d.sectionMap d.deform d.section_comp
    d.zero d.one d.over

/-- Use the same deformation parameter on both jet factors. -/
theorem truncationPullback : TruncationPullback := by
  intro hInterval c k l h X
  simp only [parameterMap_eq]
  obtain ⟨s, D, hs, h0, h1, hD, _, _⟩ := truncationGeometry c k l h
  let q := (jetSystem c).truncate k l h
  let d : SectionDeformation q := ⟨s, D, hs, h0, h1, hD⟩
  let d₁ := d.prod (SectionDeformation.id X)
  exact ⟨d₁.fullyFaithful hInterval, (d.prod d₁).fullyFaithful hInterval⟩

end RepTheorySurvey.Geometric.PositiveJetTruncationPullback
