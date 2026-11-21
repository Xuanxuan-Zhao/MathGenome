import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FilteredPageFunctoriality
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence

/-! HA-S01 (source lines 404–450). Stabilization of the actual cycle and
boundary subobjects is uniform in each total degree. The limiting comparison
uses generalized closed representatives and epic covers, and hence applies
to arbitrary abelian categories without projectivity or infinite limits. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace FiniteFiltrationConvergence
open FilteredPage
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

/-- Pulling back the zero subobject gives the kernel subobject. -/
theorem pullback_bot_eq_kernel {X Y : A} (f : X ⟶ Y) :
    (Subobject.pullback f).obj ⊥ = kernelSubobject f := by
  apply le_antisymm
  · apply le_kernelSubobject
    rw [← (Subobject.isPullback f (⊥ : Subobject Y)).w]
    simp
  · apply Subobject.le_of_factors
    apply pullback_factors
    rw [kernelSubobject_arrow_comp]
    exact Subobject.factors_zero

/-- The numerator is closed as soon as the outgoing filtration step is zero. -/
theorem almost_eq_closed (r p n : ℤ) (h : F.piece (p+r) (n+1) = ⊥) :
    almost F r p n = closed F p n := by
  dsimp only [almost, closed]
  rw [h, pullback_bot_eq_kernel]

/-- The boundary source is all ambient boundaries in the step as soon as the
incoming filtration step is the entire preceding term. -/
theorem boundarySource_eq_exactPart (r p n : ℤ)
    (h : F.piece (p-r+1) (n-1) = ⊤) : boundarySource F r p n = exactPart F p n := by
  have : IsIso (F.piece (p-r+1) (n-1)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 h
  dsimp only [boundarySource, exactPart]
  rw [imageSubobject_iso_comp]

/-- Equality of adjacent filtration steps annihilates the graded projection. -/
theorem projection_eq_zero_of_eq (p n : ℤ) (h : F.piece (p+1) n = F.piece p n) :
    (F.projection p).f n = 0 := by
  let i := (F.transition p).f n
  let j := Subobject.ofLE _ _ h.ge
  have hj : j ≫ i = 𝟙 _ := by
    dsimp [j, i, Filtration.transition]
    rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]
  have hi : Epi i := by
    exact epi_of_epi_fac hj
  apply (cancel_epi i).1
  change i ≫ cokernel.π i = i ≫ 0
  simp

/-- Every representative vanishes in a zero graded piece. -/
theorem gradedRepresentative_eq_zero_of_eq (p n : ℤ)
    (h : F.piece (p+1) n = F.piece p n)
    (S : Subobject (K.X n)) (hS : S ≤ F.piece p n) :
    gradedRepresentative F p n S hS = 0 := by
  dsimp only [gradedRepresentative]
  rw [projection_eq_zero_of_eq F p n h, comp_zero]

/-- Outside the effective interval every page and stable subobject is zero. -/
theorem stabilized_of_adjacent_eq (r p n : ℤ)
    (h : F.piece (p+1) n = F.piece p n) : Stabilized F r p n := by
  constructor <;> dsimp only [cycles, boundaries, stableCycles, stableBoundaries] <;>
    simp only [gradedRepresentative_eq_zero_of_eq F p n h, imageSubobject_zero]

theorem gradedImage_eq (p n : ℤ) {S T : Subobject (K.X n)}
    (hS : S ≤ F.piece p n) (hT : T ≤ F.piece p n) (h : S = T) :
    imageSubobject (gradedRepresentative F p n S hS) =
      imageSubobject (gradedRepresentative F p n T hT) := by
  subst T
  rfl

/-- Inside the effective interval the adjacent-degree bounds give stabilization. -/
theorem stabilized_of_bounds (r p n : ℤ)
    (hout : F.piece (p+r) (n+1) = ⊥)
    (hin : F.piece (p-r+1) (n-1) = ⊤) : Stabilized F r p n := by
  constructor
  · exact gradedImage_eq F p n _ _ (almost_eq_closed F r p n hout)
  · exact gradedImage_eq F p n _ _ (boundarySource_eq_exactPart F r p n hin)

/-- An explicit bound, using only degrees n-1, n, and n+1, works for all
filtration degrees on the diagonal of total degree n. -/
theorem uniform_stabilization (hF : DegreewiseFinite F) (n : ℤ) :
    ∃ R : ℤ, 0 ≤ R ∧ ∀ r, R ≤ r → ∀ p, Stabilized F r p n := by
  obtain ⟨a, b, ha, hb⟩ := hF n
  obtain ⟨aPrev, bPrev, haPrev, hbPrev⟩ := hF (n-1)
  obtain ⟨aNext, bNext, haNext, hbNext⟩ := hF (n+1)
  let R := max 1 (max (bNext-a) (b-aPrev+1))
  refine ⟨R, by dsimp [R]; omega, ?_⟩
  intro r hr p
  by_cases hlo : p < a
  · apply stabilized_of_adjacent_eq
    rw [ha (p+1) (by omega), ha p (by omega)]
  by_cases hhi : b ≤ p
  · apply stabilized_of_adjacent_eq
    rw [hb (p+1) (by omega), hb p hhi]
  apply stabilized_of_bounds
  · exact hbNext _ (by dsimp [R] at hr; omega)
  · exact haPrev _ (by dsimp [R] at hr; omega)

/-- The source's lower bound in degree n already gives the lower bound
on cohomology; no bound in degree n-1 is required. -/
theorem cohomologyPiece_eq_top (p n : ℤ) (h : F.piece p n = ⊤) :
    cohomologyPiece F p n = ⊤ := by
  have : IsIso ((F.inclusion p).f n) :=
    (Subobject.isIso_arrow_iff_eq_top _).2 h
  have : IsIso (HomologicalComplex.cyclesMap (F.inclusion p) n) := by
    dsimp only [HomologicalComplex.cyclesMap]
    apply ShortComplex.isIso_cyclesMap_of_isIso_of_mono'
    · exact inferInstanceAs (IsIso ((F.inclusion p).f n))
    · change Mono ((F.inclusion p).f _)
      dsimp only [Filtration.inclusion]
      infer_instance
  have : Epi (HomologicalComplex.homologyMap (F.inclusion p) n) := by
    exact epi_of_epi_fac (HomologicalComplex.homologyπ_naturality (F.inclusion p) n)
  have : Epi (cohomologyPiece F p n).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp
      (HomologicalComplex.homologyMap (F.inclusion p) n))
  exact (Subobject.isIso_arrow_iff_eq_top _).1 (isIso_of_mono_of_epi _)

/-- The upper bound also descends in the same degree. -/
theorem cohomologyPiece_eq_bot (p n : ℤ) (h : F.piece p n = ⊥) :
    cohomologyPiece F p n = ⊥ := by
  have hi : (F.inclusion p).f n = 0 :=
    Subobject.mk_eq_bot_iff_zero.mp (by simpa only [Filtration.inclusion, Subobject.mk_arrow] using h)
  have hc : HomologicalComplex.cyclesMap (F.inclusion p) n = 0 := by
    apply (cancel_mono (K.iCycles n)).1
    rw [HomologicalComplex.cyclesMap_i, zero_comp]
    rw [hi, comp_zero]
  have hh : HomologicalComplex.homologyMap (F.inclusion p) n = 0 := by
    apply (cancel_epi ((F.step p).homologyπ n)).1
    rw [HomologicalComplex.homologyπ_naturality, hc, zero_comp, comp_zero]
  simpa only [cohomologyPiece, hh] using
    (imageSubobject_zero : imageSubobject (0 : (F.step p).homology n ⟶ K.homology n) = ⊥)

/-- A finite decreasing filtration is complete: compatible quotient maps
are determined by a step at which the filtration is zero. -/
theorem complete_of_eventually_bot {H : A} (P : ℤ → Subobject H)
    (hP : ∃ b : ℤ, ∀ p, b ≤ p → P p = ⊥) : Complete P := by
  obtain ⟨b, hb⟩ := hP
  intro T z hz
  have hπ (p : ℤ) (hp : b ≤ p) : IsIso (cokernel.π (P p).arrow) := by
    apply cokernel.π_of_zero
    exact Subobject.mk_eq_bot_iff_zero.mp (by simpa only [Subobject.mk_arrow] using hb p hp)
  have := hπ b le_rfl
  let f := z b ≫ inv (cokernel.π (P b).arrow)
  refine ⟨f, ?_, ?_⟩
  · intro p
    let c := max b p
    have hbc : b ≤ c := le_max_left _ _
    have hpc : p ≤ c := le_max_right _ _
    have := hπ c hbc
    have hcb : P c ≤ P b := by simp only [hb c hbc, bot_le]
    have hcp : P c ≤ P p := by simp only [hb c hbc, bot_le]
    have hc (j : ℤ) (hj : P c ≤ P j) :
        inv (cokernel.π (P c).arrow) ≫ cokernel.π (P j).arrow = quotientMap P hj := by
      apply (cancel_epi (cokernel.π (P c).arrow)).1
      simp [quotientMap]
    have heq : z c ≫ inv (cokernel.π (P c).arrow) = f := by
      apply (cancel_mono (cokernel.π (P b).arrow)).1
      dsimp only [f]
      simp only [Category.assoc, IsIso.inv_hom_id, comp_id, hc b hcb]
      exact hz b c hbc hcb
    rw [← heq, Category.assoc, hc p hcp]
    exact hz p c hpc hcp
  · intro g hg
    apply (cancel_mono (cokernel.π (P b).arrow)).1
    simpa only [f, Category.assoc, IsIso.inv_hom_id, comp_id] using hg b

/-- All the claimed filtration properties, with exactly the degreewise bounds
of the original filtration. -/
theorem cohomology_filtration (hF : DegreewiseFinite F) : CohomologyFiltrationData F := by
  have hf : ∀ n, ∃ a b : ℤ,
      (∀ p, p ≤ a → cohomologyPiece F p n = ⊤) ∧
      (∀ p, b ≤ p → cohomologyPiece F p n = ⊥) := by
    intro n
    obtain ⟨a, b, ha, hb⟩ := hF n
    exact ⟨a, b, fun p hp => cohomologyPiece_eq_top F p n (ha p hp),
      fun p hp => cohomologyPiece_eq_bot F p n (hb p hp)⟩
  refine ⟨cohomologyPiece_decreasing F, hf, ?_, ?_, ?_⟩
  · intro n S hS
    obtain ⟨a, b, ha, hb⟩ := hf n
    exact top_le_iff.mp (by simpa only [ha a le_rfl] using hS a)
  · intro n S hS
    obtain ⟨a, b, ha, hb⟩ := hf n
    exact le_bot_iff.mp (by simpa only [hb b le_rfl] using hS b)
  · intro n
    obtain ⟨a, b, ha, hb⟩ := hf n
    exact complete_of_eventually_bot _ ⟨b, hb⟩

/-- Closed representatives have zero ambient differential. -/
@[reassoc (attr := simp)]
theorem closed_d (p n : ℤ) : (closed F p n).arrow ≫ K.d n (n+1) = 0 := by
  rw [← Subobject.ofLE_arrow (inf_le_right : closed F p n ≤ kernelSubobject (K.d n (n+1))),
    Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- Factor a closed representative of a filtration step into the intersection. -/
def liftClosed {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X n)
    (hx : x ≫ (F.step p).d n (n+1) = 0) : T ⟶ (closed F p n : A) :=
  (closed F p n).factorThru (x ≫ (F.piece p n).arrow) (by
    apply (Subobject.inf_factors _).2
    refine ⟨Subobject.factors_comp_arrow x, ?_⟩
    apply kernelSubobject_factors
    rw [Category.assoc, ← Filtration.differential_arrow, ← Category.assoc]
    change (x ≫ (F.step p).d n (n+1)) ≫ _ = 0
    rw [hx, zero_comp])

@[reassoc (attr := simp)]
theorem liftClosed_arrow {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X n)
    (hx : x ≫ (F.step p).d n (n+1) = 0) :
    liftClosed F p n x hx ≫ (closed F p n).arrow = x ≫ (F.piece p n).arrow :=
  Subobject.factorThru_arrow _ _ _

@[reassoc (attr := simp)]
theorem liftClosed_step {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X n)
    (hx : x ≫ (F.step p).d n (n+1) = 0) :
    liftClosed F p n x hx ≫ Subobject.ofLE _ _ inf_le_left = x := by
  apply (cancel_mono (F.piece p n).arrow).1
  simp [Category.assoc]

abbrev closedCycles (p n : ℤ) : (closed F p n : A) ⟶ (F.step p).cycles n :=
  (F.step p).liftCycles (Subobject.ofLE _ _ inf_le_left) (n+1) (by simp) (closed_step_d F p n)

instance closedCycles_epi (p n : ℤ) : Epi (closedCycles F p n) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro T z
  refine ⟨T, 𝟙 _, inferInstance, liftClosed F p n (z ≫ (F.step p).iCycles n) (by simp), ?_⟩
  apply (cancel_mono ((F.step p).iCycles n)).1
  simp [closedCycles, Category.assoc]

instance closedClass_epi (p n : ℤ) : Epi (closedClass F p n) := by
  change Epi (closedCycles F p n ≫ (F.step p).homologyπ n ≫ _)
  infer_instance

instance gradedClass_epi (p n : ℤ) : Epi (gradedClass F p n) := by
  dsimp only [gradedClass]
  infer_instance

/-- Closed classes computed in the step agree with ambient cohomology. -/
@[reassoc (attr := simp)]
theorem closedClass_arrow (p n : ℤ) :
    closedClass F p n ≫ (cohomologyPiece F p n).arrow =
      K.liftCycles (closed F p n).arrow (n+1) (by simp) (closed_d F p n) ≫ K.homologyπ n := by
  dsimp only [closedClass]
  rw [Category.assoc, Category.assoc, imageSubobject_arrow_comp,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  apply (cancel_mono (K.iCycles n)).1
  simp [Filtration.inclusion]

theorem closed_decreasing (p n : ℤ) : closed F (p+1) n ≤ closed F p n :=
  inf_le_inf_right _ (F.decreasing p n)

/-- Inclusion of closed representatives agrees with inclusion in cohomology. -/
@[reassoc (attr := simp)]
theorem closedClass_inclusion (p n : ℤ) :
    Subobject.ofLE _ _ (closed_decreasing F p n) ≫ closedClass F p n =
      closedClass F (p+1) n ≫ Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n) := by
  apply (cancel_mono (cohomologyPiece F p n).arrow).1
  simp only [Category.assoc, Subobject.ofLE_arrow]
  rw [closedClass_arrow F p n, closedClass_arrow F (p+1) n,
    ← Category.assoc, HomologicalComplex.comp_liftCycles]
  simp only [Subobject.ofLE_arrow]

@[reassoc (attr := simp)]
theorem gradedClass_next (p n : ℤ) :
    Subobject.ofLE _ _ (closed_decreasing F p n) ≫ gradedClass F p n = 0 := by
  dsimp only [gradedClass]
  rw [← Category.assoc, closedClass_inclusion, Category.assoc, cokernel.condition, comp_zero]

/-- An ambient boundary has zero class in the cohomology filtration. -/
theorem closedClass_zero_of_boundary (p n : ℤ) {T : A} (x : T ⟶ (closed F p n : A))
    (hx : (imageSubobject (K.d (n-1) n)).Factors (x ≫ (closed F p n).arrow)) :
    x ≫ closedClass F p n = 0 := by
  let t := (imageSubobject (K.d (n-1) n)).factorThru _ hx
  obtain ⟨T', e, he, y, hy⟩ := surjective_up_to_refinements_of_epi
    (factorThruImageSubobject (K.d (n-1) n)) t
  have hxy : (e ≫ x) ≫ (closed F p n).arrow = y ≫ K.d (n-1) n := by
    rw [Category.assoc, ← Subobject.factorThru_arrow _ _ hx, ← Category.assoc, hy,
      Category.assoc, imageSubobject_arrow_comp]
  apply (cancel_epi e).1
  apply (cancel_mono (cohomologyPiece F p n).arrow).1
  simp only [Category.assoc, zero_comp, comp_zero]
  rw [closedClass_arrow F p n, ← Category.assoc, HomologicalComplex.comp_liftCycles_assoc]
  exact K.liftCycles_homologyπ_eq_zero_of_boundary _ (n+1) (by simp) y hxy

/-- Equal closed representatives modulo an ambient boundary have equal
classes in the image filtration of cohomology. -/
theorem closedClass_eq_of_boundary (p n : ℤ) {T : A}
    (x y : T ⟶ (closed F p n : A)) (z : T ⟶ K.X (n-1))
    (h : x ≫ (closed F p n).arrow = y ≫ (closed F p n).arrow + z ≫ K.d (n-1) n) :
    x ≫ closedClass F p n = y ≫ closedClass F p n := by
  apply sub_eq_zero.mp
  rw [← Preadditive.sub_comp]
  apply closedClass_zero_of_boundary
  rw [Preadditive.sub_comp, h, add_sub_cancel_left]
  exact imageSubobject_factors_comp_self _ _

/-- Representatives in the next filtration step are zero on every page. -/
@[reassoc (attr := simp)]
theorem closedToPage_next (D : F03Specs.PageData F) (r p n : ℤ) :
    Subobject.ofLE _ _ (closed_decreasing F p n) ≫ closedToPage F D r p n = 0 := by
  dsimp only [closedToPage]
  rw [← Category.assoc]
  apply PageCohomology.toPage_zero_of_next
  simp only [Category.assoc, Subobject.ofLE_arrow]
  exact Subobject.factors_of_le _ inf_le_left (Subobject.factors_self _)

/-- The closed representatives cover a page whenever its cycle subobject
has stabilized. -/
theorem closedToPage_epi (D : F03Specs.PageData F) (r p n : ℤ)
    (h : cycles F r p n = stableCycles F p n) : Epi (closedToPage F D r p n) := by
  let i := (Subobject.isoOfEq _ _ h).inv
  have : IsIso i := (Subobject.isoOfEq _ _ h).isIso_inv
  have hw : Subobject.ofLE _ _ (closed_le_almost F r p n) ≫
      factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left) =
      factorThruImageSubobject (gradedRepresentative F p n (closed F p n) inf_le_left) ≫ i := by
    apply (cancel_mono (cycles F r p n).arrow).1
    simp [i, Category.assoc]
  change Epi (Subobject.ofLE _ _ (closed_le_almost F r p n) ≫
    (factorThruImageSubobject _ ≫ cokernel.π _))
  rw [← Category.assoc, hw]
  infer_instance

/-- A page representative whose graded value is a boundary is zero. -/
theorem toPage_zero_of_graded_boundary (D : F03Specs.PageData F) (r p n : ℤ)
    {T : A} (x : T ⟶ (almost F r p n : A))
    (hx : (boundaries F r p n).Factors
      (x ≫ gradedRepresentative F p n (almost F r p n) inf_le_left)) :
    x ≫ toPage F r p n (D.containment r p n) = 0 := by
  obtain ⟨b, hb⟩ := (Subobject.factors_iff _ _).1 hx
  change b ≫ (boundaries F r p n).arrow =
    x ≫ gradedRepresentative F p n (almost F r p n) inf_le_left at hb
  have hw : x ≫ factorThruImageSubobject
      (gradedRepresentative F p n (almost F r p n) inf_le_left) =
      b ≫ Subobject.ofLE _ _ (D.containment r p n) := by
    apply (cancel_mono (cycles F r p n).arrow).1
    simpa only [Category.assoc, imageSubobject_arrow_comp, Subobject.ofLE_arrow] using hb.symm
  dsimp only [toPage]
  rw [← Category.assoc, hw, Category.assoc, cokernel.condition, comp_zero]

/-- Once boundaries have stabilized, every closed ambient boundary vanishes
on the page. -/
theorem closedToPage_zero_of_boundary (D : F03Specs.PageData F) (r p n : ℤ)
    (h : boundaries F r p n = stableBoundaries F p n) {T : A}
    (x : T ⟶ (closed F p n : A))
    (hx : (imageSubobject (K.d (n-1) n)).Factors (x ≫ (closed F p n).arrow)) :
    x ≫ closedToPage F D r p n = 0 := by
  change x ≫ Subobject.ofLE _ _ (closed_le_almost F r p n) ≫ toPage F r p n _ = 0
  rw [← Category.assoc]
  apply toPage_zero_of_graded_boundary F D r p n
  rw [Category.assoc, gradedRepresentative_naturality]
  have hf : (exactPart F p n).Factors (x ≫ (closed F p n).arrow) :=
    (Subobject.inf_factors _).2 ⟨Subobject.factors_of_le _ inf_le_left
      (Subobject.factors_comp_arrow x), hx⟩
  let b := (exactPart F p n).factorThru _ hf
  have hw : b ≫ Subobject.ofLE _ _ (inf_le_left : exactPart F p n ≤ F.piece p n) =
      x ≫ Subobject.ofLE _ _ (inf_le_left : closed F p n ≤ F.piece p n) := by
    apply (cancel_mono (F.piece p n).arrow).1
    simp [b, Category.assoc]
  rw [h]
  apply (Subobject.factors_iff _ _).2
  refine ⟨b ≫ factorThruImageSubobject
    (gradedRepresentative F p n (exactPart F p n) inf_le_left), ?_⟩
  change (b ≫ factorThruImageSubobject
    (gradedRepresentative F p n (exactPart F p n) inf_le_left)) ≫
      (imageSubobject (gradedRepresentative F p n (exactPart F p n) inf_le_left)).arrow = _
  rw [Category.assoc, imageSubobject_arrow_comp]
  dsimp only [gradedRepresentative]
  rw [← Category.assoc, hw, Category.assoc]

/-- A closed representative zero on a page has zero class in graded
cohomology, with no boundedness assumption. -/
theorem gradedClass_zero_of_page_zero (D : F03Specs.PageData F) (r p n : ℤ)
    {T : A} (x : T ⟶ (closed F p n : A)) (hx : x ≫ closedToPage F D r p n = 0) :
    x ≫ gradedClass F p n = 0 := by
  obtain ⟨T', e, he, u, v, huv⟩ := PageCohomology.decompose_page_zero F r p n
    (D.containment r p n) (x ≫ Subobject.ofLE _ _ (closed_le_almost F r p n))
      (by simpa only [closedToPage, Category.assoc] using hx)
  have heq : (e ≫ x) ≫ (closed F p n).arrow =
      u ≫ (almost F (r-1) (p+1) n).arrow +
        (v ≫ (almost F (r-1) (p-r+1) (n-1)).arrow) ≫ K.d (n-1) n := by
    simpa only [Category.assoc, Subobject.ofLE_arrow] using huv
  have hud : (u ≫ (almost F (r-1) (p+1) n).arrow) ≫ K.d n (n+1) = 0 := by
    have hh := congrArg (fun t => t ≫ K.d n (n+1)) heq
    simpa only [Category.assoc, closed_d, comp_zero, Preadditive.add_comp,
      HomologicalComplex.d_comp_d, add_zero] using hh.symm
  have huf : (closed F (p+1) n).Factors (u ≫ (almost F (r-1) (p+1) n).arrow) := by
    apply (Subobject.inf_factors _).2
    exact ⟨Subobject.factors_of_le _ inf_le_left (Subobject.factors_comp_arrow u),
      kernelSubobject_factors _ _ hud⟩
  let uc := (closed F (p+1) n).factorThru _ huf
  let y := uc ≫ Subobject.ofLE _ _ (closed_decreasing F p n)
  have hy : y ≫ (closed F p n).arrow = u ≫ (almost F (r-1) (p+1) n).arrow := by
    simp [y, uc, Category.assoc]
  have hc := closedClass_eq_of_boundary F p n (e ≫ x) y
    (v ≫ (almost F (r-1) (p-r+1) (n-1)).arrow) (by rw [hy]; exact heq)
  apply (cancel_epi e).1
  rw [comp_zero, ← Category.assoc]
  change (e ≫ x) ≫ closedClass F p n ≫ cokernel.π _ = 0
  rw [← Category.assoc, hc, Category.assoc]
  change (uc ≫ Subobject.ofLE _ _ (closed_decreasing F p n)) ≫ gradedClass F p n = 0
  rw [Category.assoc, gradedClass_next, comp_zero]

/-- Once boundaries have stabilized, a closed representative zero in graded
cohomology is zero on the actual page. The proof uses two epic covers. -/
theorem page_zero_of_gradedClass_zero (D : F03Specs.PageData F) (r p n : ℤ)
    (hB : boundaries F r p n = stableBoundaries F p n) {T : A}
    (x : T ⟶ (closed F p n : A)) (hx : x ≫ gradedClass F p n = 0) :
    x ≫ closedToPage F D r p n = 0 := by
  let i := Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n)
  let y := Abelian.monoLift i (x ≫ closedClass F p n)
    (by simpa only [gradedClass, Category.assoc] using hx)
  have hy : y ≫ i = x ≫ closedClass F p n := Abelian.monoLift_comp _ _ _
  obtain ⟨T₁, e₁, he₁, u, hu⟩ := surjective_up_to_refinements_of_epi (closedClass F (p+1) n) y
  let xi := e₁ ≫ x
  let yi := u ≫ Subobject.ofLE _ _ (closed_decreasing F p n)
  have hclass : xi ≫ closedClass F p n = yi ≫ closedClass F p n := by
    dsimp only [xi, yi]
    rw [Category.assoc, ← hy, ← Category.assoc, hu]
    simp only [Category.assoc, closedClass_inclusion]
    rfl
  have hamb : K.liftCycles (xi ≫ (closed F p n).arrow) (n+1) (by simp) (by simp) ≫
        K.homologyπ n =
      K.liftCycles (yi ≫ (closed F p n).arrow) (n+1) (by simp) (by simp) ≫ K.homologyπ n := by
    have hh := congrArg (fun t => t ≫ (cohomologyPiece F p n).arrow) hclass
    simpa only [Category.assoc, closedClass_arrow,
      HomologicalComplex.comp_liftCycles_assoc] using hh
  obtain ⟨T₂, e₂, he₂, w, hw⟩ :=
    (K.liftCycles_comp_homologyπ_eq_iff_up_to_refinements (n-1) n (n+1) (by simp) (by simp)
      (xi ≫ (closed F p n).arrow) (yi ≫ (closed F p n).arrow) (by simp) (by simp)).1 hamb
  simp only [xi, yi, Category.assoc] at hw
  let b := e₂ ≫ xi - e₂ ≫ yi
  have hb : b ≫ closedToPage F D r p n = 0 := by
    apply closedToPage_zero_of_boundary F D r p n hB
    dsimp only [b]
    simp only [xi, yi, Preadditive.sub_comp, Category.assoc]
    rw [hw, add_sub_cancel_left]
    exact imageSubobject_factors_comp_self _ _
  have hyPage : yi ≫ closedToPage F D r p n = 0 := by
    dsimp only [yi]
    rw [Category.assoc, closedToPage_next, comp_zero]
  have hxi : (e₂ ≫ xi) ≫ closedToPage F D r p n = 0 := by
    dsimp only [b] at hb
    simp only [Preadditive.sub_comp, Category.assoc, hyPage, comp_zero, sub_zero] at hb
    simpa only [Category.assoc] using hb
  apply (cancel_epi (e₂ ≫ e₁)).1
  simpa only [xi, Category.assoc, comp_zero] using hxi

/-- The canonical limiting isomorphism, assembled from equality of the two
relations on closed representatives. -/
def limitIso (D : F03Specs.PageData F) (r p n : ℤ) (h : Stabilized F r p n) :
    LimitIso F D r p n := by
  have := closedToPage_epi F D r p n h.1
  let q := closedToPage F D r p n
  let g := Abelian.epiDesc q (gradedClass F p n)
    (gradedClass_zero_of_page_zero F D r p n (kernel.ι q) (kernel.condition q))
  have hq : q ≫ g = gradedClass F p n := Abelian.comp_epiDesc _ _ _
  have : Epi g := epi_of_epi_fac hq
  have : Mono g := by
    apply Preadditive.mono_of_cancel_zero
    intro T z hz
    obtain ⟨T', e, he, x, hx⟩ := surjective_up_to_refinements_of_epi q z
    apply (cancel_epi e).1
    rw [comp_zero, hx]
    apply page_zero_of_gradedClass_zero F D r p n h.2
    rw [← hq, ← Category.assoc, ← hx, Category.assoc, hz, comp_zero]
  have : IsIso g := isIso_of_mono_of_epi _
  exact ⟨asIso g, hq⟩

/-- Closed representatives have zero differential on every page. -/
theorem closedToPage_differential (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    closedToPage F D r p n ≫ D.differential r hr p n = 0 := by
  dsimp only [closedToPage]
  rw [Category.assoc, D.representative_formula, ← Category.assoc]
  have hz : Subobject.ofLE _ _ (closed_le_almost F r p n) ≫ D.restriction r hr p n = 0 := by
    apply (cancel_mono (almost F r (p+r) (n+1)).arrow).1
    rw [Category.assoc, D.restriction_arrow, ← Category.assoc, Subobject.ofLE_arrow,
      closed_d, zero_comp]
  rw [hz, zero_comp]

theorem differential_zero_of_stabilized (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (h : Stabilized F r p n) : D.differential r hr p n = 0 := by
  have := closedToPage_epi F D r p n h.1
  apply (cancel_epi (closedToPage F D r p n)).1
  rw [closedToPage_differential, comp_zero]

section Naturality
variable {X Y : FilteredComplex A}

/-- The map on filtered cohomology takes each closed representative to its
image under the ambient cochain map. -/
@[reassoc (attr := simp)]
theorem closedClass_naturality (f : FilteredMap X Y) (p n : ℤ) :
    closedClass X.filtration p n ≫ cohomologyStepMap f p n =
      closedMap f p n ≫ closedClass Y.filtration p n := by
  apply (cancel_mono (cohomologyPiece Y.filtration p n).arrow).1
  simp only [Category.assoc, cohomologyStepMap_arrow]
  rw [← Category.assoc, closedClass_arrow X.filtration p n,
    closedClass_arrow Y.filtration p n, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc, ← Category.assoc]
  congr 1
  apply (cancel_mono (Y.complex.iCycles n)).1
  simp [Category.assoc]

@[reassoc (attr := simp)]
theorem gradedClass_naturality (f : FilteredMap X Y) (p n : ℤ) :
    gradedClass X.filtration p n ≫ gradedCohomologyMap f p n =
      closedMap f p n ≫ gradedClass Y.filtration p n := by
  dsimp only [gradedClass, gradedCohomologyMap]
  simp only [Category.assoc, cokernel.map, cokernel.π_desc]
  rw [← Category.assoc, closedClass_naturality, Category.assoc]

/-- Restriction to closed representatives commutes with the upstream page
maps, for every map data satisfying its canonical representative formula. -/
@[reassoc (attr := simp)]
theorem closedToPage_naturality (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E) (r p n : ℤ) :
    closedToPage X.filtration D r p n ≫ M.map r p n =
      closedMap f p n ≫ closedToPage Y.filtration E r p n := by
  have hw : Subobject.ofLE _ _ (closed_le_almost X.filtration r p n) ≫
      FilteredPageFunctoriality.almostMap f r p n =
      closedMap f p n ≫ Subobject.ofLE _ _ (closed_le_almost Y.filtration r p n) := by
    apply (cancel_mono (almost Y.filtration r p n).arrow).1
    simp [Category.assoc]
  dsimp only [closedToPage]
  rw [Category.assoc, M.representative_formula, ← Category.assoc, hw, Category.assoc]

/-- Naturality of any representative-compatible limiting isomorphisms. -/
theorem limitIso_naturality (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E) (r p n : ℤ)
    (L : LimitIso X.filtration D r p n) (L' : LimitIso Y.filtration E r p n)
    (h : Stabilized X.filtration r p n) :
    M.map r p n ≫ L'.iso.hom = L.iso.hom ≫ gradedCohomologyMap f p n := by
  have := closedToPage_epi X.filtration D r p n h.1
  apply (cancel_epi (closedToPage X.filtration D r p n)).1
  rw [← Category.assoc, closedToPage_naturality, Category.assoc, L'.representative_formula,
    ← Category.assoc, L.representative_formula, gradedClass_naturality]
end Naturality

end FiniteFiltrationConvergence

/-- Stabilization is uniform over all bidegrees with fixed total degree. -/
theorem filtered_uniform_stabilization : S01Specs.UniformStabilization.{v,u} := by
  intro A _ _ K F hF
  exact FiniteFiltrationConvergence.uniform_stabilization F hF

/-- The induced filtration is finite, exhaustive, separated and complete. -/
theorem filtered_cohomology_filtration : S01Specs.CohomologyFiltration.{v,u} := by
  intro A _ _ K F hF
  exact FiniteFiltrationConvergence.cohomology_filtration F hF

theorem filtered_canonical_limit : S01Specs.CanonicalLimit.{v,u} := by
  intro A _ _ K F hF D r p n hr h
  exact ⟨FiniteFiltrationConvergence.limitIso F D r p n h⟩

theorem filtered_differential_stabilization : S01Specs.DifferentialStabilization.{v,u} := by
  intro A _ _ K F hF D n
  obtain ⟨R, hR, h⟩ := FiniteFiltrationConvergence.uniform_stabilization F hF n
  exact ⟨R, hR, fun r hr hRr p =>
    FiniteFiltrationConvergence.differential_zero_of_stabilized F D r hr p n (h r hRr p)⟩

theorem filtered_limit_naturality : S01Specs.Naturality.{v,u} := by
  intro A _ _ X Y f hX hY D E M r p n L L' h h'
  exact FiniteFiltrationConvergence.limitIso_naturality f D E M r p n L L' h

/-- HA-S01 in its full degreewise finite, arbitrary abelian-category scope. -/
theorem finite_filtration_convergence : S01Specs.FullStatement.{v,u} :=
  ⟨filtered_uniform_stabilization, filtered_cohomology_filtration,
    filtered_canonical_limit, filtered_differential_stabilization, filtered_limit_naturality⟩

end AdvancedHomologicalAlgebra
