import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiltrationExactCouple
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedExactCouples
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.PageCohomology

/-! The exact couple of a decreasing filtration, HA-F05. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace FiltrationExactCouple
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

@[simp]
theorem stepInclusion_refl (p : ℤ) : stepInclusion F p p le_rfl = 𝟙 _ := by
  ext n
  exact Subobject.ofLE_refl _

@[simp]
theorem stepInclusion_succ (p : ℤ) : stepInclusion F p (p+1) (by omega) = F.transition p := by
  ext n
  rfl

@[reassoc]
theorem stepInclusion_comp (p q a : ℤ) (hpq : p ≤ q) (hqa : q ≤ a) :
    stepInclusion F q a hqa ≫ stepInclusion F p q hpq =
      stepInclusion F p a (hpq.trans hqa) := by
  ext n
  apply (cancel_mono (F.piece p n).arrow).1
  simp [stepInclusion]

/-- The canonical tower of the general derived-couple construction. -/
def tower (h : ∀ p, (F.firstSequence p).ShortExact) : Tower F h where
  family := (initial F h).iterate
  start := rfl
  step t := ⟨((initial F h).iterate t).2.derivation, rfl⟩
  degree t := by simpa only [zero_add] using (initial F h).iterate_degree t

variable (h : ∀ p, (F.firstSequence p).ShortExact)

/-- The D-comparison at a single stage. Endpoint equalities make the induction
independent of associativity choices in integer filtration indices. -/
structure DStage (t : ℕ) where
  inclusion : ∀ p n, ((initial F h).iterate t).2.D p n ⟶ (F.step p).homology n
  projection : ∀ p q n, q = p+(t:ℤ) →
    ((F.step q).homology n ⟶ ((initial F h).iterate t).2.D p n)
  mono : ∀ p n, Mono (inclusion p n)
  epi : ∀ p q n (hq : q = p+(t:ℤ)), Epi (projection p q n hq)
  factorization : ∀ p q n (hq : q = p+(t:ℤ)),
    projection p q n hq ≫ inclusion p n =
      HomologicalComplex.homologyMap (stepInclusion F p q (by omega)) n
  i_formula : ∀ p n,
    ((initial F h).iterate t).2.i p (p+1) n rfl ≫ inclusion p n =
      inclusion (p+1) n ≫ HomologicalComplex.homologyMap (F.transition p) n

/-- Initially D is H(F^p) itself, the image of its identity map. -/
def dStageZero : DStage F h 0 where
  inclusion p n := 𝟙 _
  projection p q n hq := by
    have heq : q = p := by omega
    subst heq
    exact 𝟙 _
  mono p n := inferInstance
  epi p q n hq := by
    have heq : q = p := by omega
    subst heq
    exact inferInstanceAs (Epi (𝟙 _))
  factorization p q n hq := by
    have heq : q = p := by omega
    subst heq
    simp
  i_formula p n := by simp [ExactCouple.iterate, initial, initialI]

/-- Derivation replaces D by the image of i. Its embedding in H(F^p) and
its projection from the deeper H are the composites of the previous ones. -/
def DStage.succ {t : ℕ} (S : DStage F h t) : DStage F h (t+1) where
  inclusion p n := ((initial F h).iterate t).2.inclusion p n ≫ S.inclusion p n
  projection p q n hq := S.projection (p+1) q n (by omega) ≫
    ((initial F h).iterate t).2.projection p n
  mono p n := by
    have := S.mono p n
    exact mono_comp _ _
  epi p q n hq := by
    have := S.epi (p+1) q n (by omega)
    exact epi_comp _ _
  factorization p q n hq := by
    change (S.projection (p+1) q n (by omega) ≫
      ((initial F h).iterate t).2.projection p n) ≫
      (((initial F h).iterate t).2.inclusion p n ≫ S.inclusion p n) = _
    rw [Category.assoc, ExactCouple.projection_inclusion_assoc, S.i_formula,
      ← Category.assoc, S.factorization, ← HomologicalComplex.homologyMap_comp]
    congr 1
    rw [← stepInclusion_succ F p, stepInclusion_comp]
  i_formula p n := by
    change ((initial F h).iterate t).2.derivedI p (p+1) n rfl ≫
      (((initial F h).iterate t).2.inclusion p n ≫ S.inclusion p n) = _
    rw [← Category.assoc, ExactCouple.derivedI_inclusion, Category.assoc, S.i_formula,
      ← Category.assoc]

/-- The image formula is valid after every finite number of derivations. -/
def dStage : (t : ℕ) → DStage F h t
  | 0 => dStageZero F h
  | t+1 => (dStage t).succ F h

/-- Assemble the componentwise factorization into the full D-comparison. -/
def dComparison : DComparison (tower F h) where
  inclusion t := (dStage F h t).inclusion
  projection t p n := (dStage F h t).projection p (p+(t:ℤ)) n rfl
  mono t := (dStage F h t).mono
  epi t p n := (dStage F h t).epi p (p+(t:ℤ)) n rfl
  factorization t p n := (dStage F h t).factorization p (p+(t:ℤ)) n rfl
  i_formula t := (dStage F h t).i_formula

/-- The stated factorization gives the actual categorical image, compatibly
with the inclusion into H(F^p). -/
def DComparison.imageIso {h : ∀ p, (F.firstSequence p).ShortExact}
    {T : Tower F h} (D : DComparison T) (t : ℕ) (p n : ℤ) :
    (T.family t).2.D p n ≅
      image (HomologicalComplex.homologyMap (stepInclusion F p (p+(t:ℤ)) (by omega)) n) := by
  have := D.mono t p n
  have := D.epi t p n
  have := strongEpi_of_epi (D.projection t p n)
  exact image.isoStrongEpiMono _ _ (D.factorization t p n)

/-- The first filtration sequence maps naturally to the two-step quotient
sequence, by projecting the kernel and middle terms. -/
def firstToSecond (p : ℤ) : F.firstSequence p ⟶ F.secondSequence p where
  τ₁ := F.projection (p+1)
  τ₂ := F.twoStepProjection p
  τ₃ := 𝟙 _
  comm₁₂ := F.projection_gradedToTwoStep p
  comm₂₃ := by
    change F.twoStepProjection p ≫ F.twoStepToGraded p = F.projection p ≫ 𝟙 _
    rw [F.twoStepProjection_toGraded, Category.comp_id]

/-- Projecting the connecting map of the first sequence gives the connecting
map of the second sequence, with the same cochain sign. -/
@[reassoc]
theorem connecting_projection (p n : ℤ) :
    (h p).δ n (n+1) (by simp) ≫
      HomologicalComplex.homologyMap (F.projection (p+1)) (n+1) =
    (F.secondSequence_shortExact p).δ n (n+1) (by simp) := by
  simpa only [firstToSecond, HomologicalComplex.homologyMap_id, Category.id_comp] using
    HomologicalComplex.HomologySequence.δ_naturality (firstToSecond F p)
      (h p) (F.secondSequence_shortExact p) n (n+1) (by simp)

/-- The initial exact-couple differential is the connecting map of the
second sequence. -/
theorem initial_d (p n : ℤ) :
    (initial F h).d p (p+1) n (n+1) (by omega) rfl =
      (F.secondSequence_shortExact p).δ n (n+1) (by simp) := by
  simpa only [ExactCouple.d, initial, initialK, initialJ, eqToHom_refl,
    Category.comp_id] using connecting_projection F h p n

/-- The first differential comparison uses the actual HA-F03 page, not an
unrelated spectral sequence with an isomorphic first object. -/
theorem initial_d_page (P : F03Specs.PageData F) (p n : ℤ) :
    (initial F h).d p (p+1) n (n+1) (by omega) rfl ≫
      (PageCohomology.firstIso F (p+1) (n+1) (P.containment 1 (p+1) (n+1))).inv =
    (PageCohomology.firstIso F p n (P.containment 1 p n)).inv ≫
      P.differential 1 (by omega) p n := by
  apply (cancel_mono (PageCohomology.firstIso F (p+1) (n+1)
    (P.containment 1 (p+1) (n+1))).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [PageCohomology.first_differential F P p n (F.secondSequence_shortExact p)]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, initial_d]

/-- Mapping the cohomology class of a generalized cycle applies the cochain
map to that cycle. -/
@[reassoc]
theorem cycleClass_map {L M : CochainComplex A ℤ} (f : L ⟶ M) (n : ℤ) {U : A}
    (x : U ⟶ L.X n) (hx : x ≫ L.d n (n+1) = 0) :
    L.liftCycles x (n+1) (by simp) hx ≫ L.homologyπ n ≫
        HomologicalComplex.homologyMap f n =
      M.liftCycles (x ≫ f.f n) (n+1) (by simp)
        (by rw [Category.assoc, f.comm, ← Category.assoc, hx, zero_comp]) ≫ M.homologyπ n := by
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]

/-- On the first couple j sends a closed representative to its page class. -/
theorem initial_j_representative (P : F03Specs.PageData F) (p n : ℤ) {U : A}
    (x : U ⟶ (F.step p).X n) (hx : x ≫ (F.step p).d n (n+1) = 0)
    (z : U ⟶ (FilteredPage.almost F 1 p n : A))
    (hz : z ≫ (FilteredPage.almost F 1 p n).arrow = x ≫ (F.piece p n).arrow) :
    (F.step p).liftCycles x (n+1) (by simp) hx ≫ (F.step p).homologyπ n ≫
      HomologicalComplex.homologyMap (F.projection p) n ≫
      (PageCohomology.firstIso F p n (P.containment 1 p n)).inv =
    z ≫ FilteredPage.toPage F 1 p n (P.containment 1 p n) := by
  have hrep : z ≫ FilteredPage.gradedRepresentative F p n
      (FilteredPage.almost F 1 p n) inf_le_left = x ≫ (F.projection p).f n := by
    dsimp only [FilteredPage.gradedRepresentative]
    rw [← Category.assoc]
    congr 1
    apply (cancel_mono (F.piece p n).arrow).1
    simpa only [Category.assoc, Subobject.ofLE_arrow] using hz
  apply (cancel_mono (PageCohomology.firstIso F p n (P.containment 1 p n)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = (F.graded p).liftCycles (x ≫ (F.projection p).f n) (n+1) (by simp)
        (by rw [Category.assoc, (F.projection p).comm, ← Category.assoc, hx, zero_comp]) ≫
          (F.graded p).homologyπ n := cycleClass_map (F.projection p) n x hx
    _ = z ≫ PageCohomology.firstClass F p n := by
      dsimp only [PageCohomology.firstClass]
      rw [HomologicalComplex.comp_liftCycles_assoc]
      congr 1
      apply (cancel_mono ((F.graded p).iCycles n)).1
      simp only [HomologicalComplex.liftCycles_i]
      exact hrep.symm
    _ = z ≫ FilteredPage.toPage F 1 p n (P.containment 1 p n) ≫
        (PageCohomology.firstIso F p n (P.containment 1 p n)).hom := by
      simpa only [FilteredPage.toPage, Category.assoc] using
        congrArg (fun f => z ≫ f) (PageCohomology.toPage_firstIso F p n _).symm
  all_goals simp only [FilteredPage.toPage, Category.assoc]

/-- The first-couple connecting map takes [x] to [dx] in H(F^(p+1)).
No projectivity of the test object is used. -/
theorem initial_k_representative (P : F03Specs.PageData F) (p n : ℤ) {U : A}
    (x : U ⟶ (FilteredPage.almost F 1 p n : A))
    (y : U ⟶ (F.step (p+1)).X (n+1))
    (hy : y ≫ (F.piece (p+1) (n+1)).arrow =
      x ≫ (FilteredPage.almost F 1 p n).arrow ≫ K.d n (n+1))
    (hdy : y ≫ (F.step (p+1)).d (n+1) (n+1+1) = 0) :
    x ≫ FilteredPage.toPage F 1 p n (P.containment 1 p n) ≫
      (PageCohomology.firstIso F p n (P.containment 1 p n)).hom ≫
        (h p).δ n (n+1) (by simp) =
    (F.step (p+1)).liftCycles y (n+1+1) (by simp) hdy ≫ (F.step (p+1)).homologyπ (n+1) := by
  let a : U ⟶ (F.step p).X n := x ≫ Subobject.ofLE _ _
    (inf_le_left : FilteredPage.almost F 1 p n ≤ F.piece p n)
  have ha : y ≫ (F.transition p).f (n+1) = a ≫ (F.step p).d n (n+1) := by
    apply (cancel_mono (F.piece p (n+1)).arrow).1
    simpa only [a, Filtration.transition, Filtration.step, Category.assoc,
      Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc, Filtration.differential_arrow] using hy
  have hx : (x ≫ FilteredPage.gradedRepresentative F p n
      (FilteredPage.almost F 1 p n) inf_le_left) ≫ (F.graded p).d n (n+1) = 0 := by
    rw [Category.assoc, PageCohomology.firstRepresentative_cycle, comp_zero]
  have hh := (h p).δ_eq n (n+1) (by simp)
    (x ≫ FilteredPage.gradedRepresentative F p n (FilteredPage.almost F 1 p n) inf_le_left)
    hx a (by dsimp [a, FilteredPage.gradedRepresentative, Filtration.firstSequence]; rw [Category.assoc]) y ha (n+1+1) (by simp)
  calc
    _ = x ≫ PageCohomology.firstClass F p n ≫ (h p).δ n (n+1) (by simp) := by
      simpa only [Category.assoc] using
        congrArg (fun f => x ≫ f ≫ (h p).δ n (n+1) (by simp))
          (PageCohomology.toPage_firstIso F p n (P.containment 1 p n))
    _ = _ := by
      dsimp only [PageCohomology.firstClass]
      rw [← Category.assoc, HomologicalComplex.comp_liftCycles_assoc]
      convert hh using 1 <;> simp [Filtration.firstSequence, Category.assoc]

/-- The actual differential of an almost cycle, factored through the required
filtration step. This supplies the representatives used in the all-page k formula. -/
def almostDifferential (r p n : ℤ) :
    (FilteredPage.almost F r p n : A) ⟶ (F.step (p+r)).X (n+1) :=
  Subobject.ofLE _ _ inf_le_right ≫
    Subobject.pullbackπ (K.d n (n+1)) (F.piece (p+r) (n+1))

@[reassoc (attr := simp)]
theorem almostDifferential_arrow (r p n : ℤ) :
    almostDifferential F r p n ≫ (F.piece (p+r) (n+1)).arrow =
      (FilteredPage.almost F r p n).arrow ≫ K.d n (n+1) := by
  dsimp only [almostDifferential]
  rw [Category.assoc, (Subobject.isPullback (K.d n (n+1))
    (F.piece (p+r) (n+1))).w, ← Category.assoc, Subobject.ofLE_arrow]

/-- The factored differential is closed. -/
theorem almostDifferential_closed (r p n : ℤ) :
    almostDifferential F r p n ≫ (F.step (p+r)).d (n+1) (n+1+1) = 0 := by
  apply (cancel_mono (F.piece (p+r) (n+1+1)).arrow).1
  simp [Filtration.step, Category.assoc]

/-- For r≥1, dx also has a unique closed representative in F^(p+1).
This exists on the same test object; no projective test object is needed. -/
theorem almost_differential_lifts (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    ∃ y : (FilteredPage.almost F r p n : A) ⟶ (F.step (p+1)).X (n+1),
      y ≫ (F.piece (p+1) (n+1)).arrow =
        (FilteredPage.almost F r p n).arrow ≫ K.d n (n+1) ∧
      y ≫ (F.step (p+1)).d (n+1) (n+1+1) = 0 := by
  let g := stepInclusion F (p+1) (p+r) (by omega)
  refine ⟨almostDifferential F r p n ≫ g.f (n+1), ?_, ?_⟩
  · dsimp only [g, stepInclusion]
    rw [Category.assoc, Subobject.ofLE_arrow, almostDifferential_arrow]
  · rw [Category.assoc, g.comm, ← Category.assoc, almostDifferential_closed, zero_comp]

/-- Every closed representative belongs to every almost-cycle subobject at
its own filtration step. This supplies the representatives used in j. -/
def closedToAlmost (r p n : ℤ) {U : A} (x : U ⟶ (F.step p).X n)
    (hx : x ≫ (F.step p).d n (n+1) = 0) : U ⟶ (FilteredPage.almost F r p n : A) :=
  (FilteredPage.almost F r p n).factorThru (x ≫ (F.piece p n).arrow) (by
    apply (Subobject.inf_factors _).2
    refine ⟨Subobject.factors_comp_arrow x, ?_⟩
    apply pullback_factors
    have hz : (x ≫ (F.piece p n).arrow) ≫ K.d n (n+1) = 0 := by
      rw [Category.assoc, ← F.differential_arrow, ← Category.assoc]
      change (x ≫ (F.step p).d n (n+1)) ≫ _ = 0
      rw [hx, zero_comp]
    rw [hz]
    exact Subobject.factors_zero)

@[reassoc (attr := simp)]
theorem closedToAlmost_arrow (r p n : ℤ) {U : A} (x : U ⟶ (F.step p).X n)
    (hx : x ≫ (F.step p).d n (n+1) = 0) :
    closedToAlmost F r p n x hx ≫ (FilteredPage.almost F r p n).arrow =
      x ≫ (F.piece p n).arrow := Subobject.factorThru_arrow _ _ _


/-- Representative-compatible comparison at a single derived stage. -/
structure EStage (P : F03Specs.PageData F) (t : ℕ) where
  pageIso : ∀ (p n : ℤ), ((initial F h).iterate t).2.E p n ≅
    FilteredPage.page F ((t:ℤ)+1) p n (P.containment ((t:ℤ)+1) p n)
  j_formula : ∀ (p n : ℤ) {U : A}
    (x : U ⟶ (F.step (p+(t:ℤ))).X n)
    (hx : x ≫ (F.step (p+(t:ℤ))).d n (n+1) = 0)
    (z : U ⟶ (FilteredPage.almost F ((t:ℤ)+1) (p+(t:ℤ)) n : A))
    (hz : z ≫ (FilteredPage.almost F ((t:ℤ)+1) (p+(t:ℤ)) n).arrow =
      x ≫ (F.piece (p+(t:ℤ)) n).arrow),
    (F.step (p+(t:ℤ))).liftCycles x (n+1) (by simp) hx ≫
      (F.step (p+(t:ℤ))).homologyπ n ≫ (dStage F h t).projection p (p+(t:ℤ)) n rfl ≫
      ((initial F h).iterate t).2.j p (p+(t:ℤ)) n (by rw [(initial F h).iterate_degree]; omega) ≫
      (pageIso (p+(t:ℤ)) n).hom =
    z ≫ FilteredPage.toPage F ((t:ℤ)+1) (p+(t:ℤ)) n
      (P.containment ((t:ℤ)+1) (p+(t:ℤ)) n)
  k_formula : ∀ (p n : ℤ) {U : A}
    (x : U ⟶ (FilteredPage.almost F ((t:ℤ)+1) p n : A))
    (y : U ⟶ (F.step (p+1)).X (n+1))
    (hy : y ≫ (F.piece (p+1) (n+1)).arrow =
      x ≫ (FilteredPage.almost F ((t:ℤ)+1) p n).arrow ≫ K.d n (n+1))
    (hdy : y ≫ (F.step (p+1)).d (n+1) (n+1+1) = 0),
    x ≫ FilteredPage.toPage F ((t:ℤ)+1) p n (P.containment ((t:ℤ)+1) p n) ≫
      (pageIso p n).inv ≫ ((initial F h).iterate t).2.k p (p+1) n (n+1) rfl rfl ≫
        (dStage F h t).inclusion (p+1) (n+1) =
      (F.step (p+1)).liftCycles y (n+1+1) (by simp) hdy ≫
        (F.step (p+1)).homologyπ (n+1)

/-- The stage-zero j equation with independent endpoint. -/
theorem initial_j_at (P : F03Specs.PageData F) (p q n : ℤ)
    (hq : q = p+((0 : ℕ) : ℤ)) {U : A}
    (x : U ⟶ (F.step q).X n) (hx : x ≫ (F.step q).d n (n+1) = 0)
    (z : U ⟶ (FilteredPage.almost F 1 q n : A))
    (hz : z ≫ (FilteredPage.almost F 1 q n).arrow = x ≫ (F.piece q n).arrow) :
    (F.step q).liftCycles x (n+1) (by simp) hx ≫ (F.step q).homologyπ n ≫
      (dStage F h 0).projection p q n hq ≫
      (initial F h).j p q n (by omega) ≫
      (PageCohomology.firstIso F q n (P.containment 1 q n)).inv =
    z ≫ FilteredPage.toPage F 1 q n (P.containment 1 q n) := by
  have hqp : q = p := by omega
  subst hqp
  simpa only [dStage, dStageZero, initial, initialJ, eqToHom_refl,
    Category.comp_id, Category.id_comp] using initial_j_representative F P q n x hx z hz

variable (P : F03Specs.PageData F)

/-- The initial comparison is the first-page cohomology identification. -/
def eStageZero : EStage F h P 0 where
  pageIso p n := (PageCohomology.firstIso F p n (P.containment 1 p n)).symm
  j_formula p n U x hx z hz := initial_j_at F h P p (p+((0 : ℕ) : ℤ)) n rfl x hx z hz
  k_formula p n U x y hy hdy := by
    simpa [dStage, dStageZero, ExactCouple.iterate, initial, initialK] using
      initial_k_representative F h P p n x y hy hdy


variable {F h P}

/-- Endpoint-independent form of the j representative equation. -/
theorem EStage.j_at {t : ℕ} (S : EStage F h P t) (p q n : ℤ)
    (hq : q = p+(t:ℤ)) {U : A} (x : U ⟶ (F.step q).X n)
    (hx : x ≫ (F.step q).d n (n+1) = 0)
    (z : U ⟶ (FilteredPage.almost F ((t:ℤ)+1) q n : A))
    (hz : z ≫ (FilteredPage.almost F ((t:ℤ)+1) q n).arrow =
      x ≫ (F.piece q n).arrow) :
    (F.step q).liftCycles x (n+1) (by simp) hx ≫ (F.step q).homologyπ n ≫
      (dStage F h t).projection p q n hq ≫
      ((initial F h).iterate t).2.j p q n (by rw [(initial F h).iterate_degree]; omega) ≫
      (S.pageIso q n).hom =
    z ≫ FilteredPage.toPage F ((t:ℤ)+1) q n (P.containment _ _ _) := by
  subst q
  exact S.j_formula p n x hx z hz

/-- The representative formulas force the differential to be [x] ↦ [dx]. -/
theorem EStage.differential_formula {t : ℕ} (S : EStage F h P t) (p n : ℤ) :
    ((initial F h).iterate t).2.d p (p+((t:ℤ)+1)) n (n+1)
      (by rw [(initial F h).iterate_degree]; omega) rfl ≫
        (S.pageIso (p+((t:ℤ)+1)) (n+1)).hom =
      (S.pageIso p n).hom ≫ P.differential ((t:ℤ)+1) (by omega) p n := by
  let r : ℤ := (t:ℤ)+1
  let q : ℤ := p+r
  let a := almostDifferential F r p n
  have ha := almostDifferential_closed F r p n
  let g := stepInclusion F (p+1) q (by dsimp [q, r]; omega)
  let y := a ≫ g.f (n+1)
  have hy : y ≫ (F.piece (p+1) (n+1)).arrow =
      (FilteredPage.almost F r p n).arrow ≫ K.d n (n+1) := by
    dsimp only [y, g, stepInclusion]
    rw [Category.assoc, Subobject.ofLE_arrow]
    exact almostDifferential_arrow F r p n
  have hdy : y ≫ (F.step (p+1)).d (n+1) (n+1+1) = 0 := by
    dsimp only [y]
    rw [Category.assoc, g.comm, ← Category.assoc, ha, zero_comp]
  have hk : FilteredPage.toPage F r p n (P.containment r p n) ≫
      (S.pageIso p n).inv ≫ ((initial F h).iterate t).2.k p (p+1) n (n+1) rfl rfl =
      (F.step q).liftCycles a (n+1+1) (by simp) ha ≫ (F.step q).homologyπ (n+1) ≫
        (dStage F h t).projection (p+1) q (n+1) (by dsimp [q, r]; omega) := by
    have := (dStage F h t).mono (p+1) (n+1)
    apply (cancel_mono ((dStage F h t).inclusion (p+1) (n+1))).1
    simp only [Category.assoc]
    rw [(dStage F h t).factorization]
    have hc := cycleClass_map g (n+1) a ha
    calc
      _ = (F.step (p+1)).liftCycles y (n+1+1) (by simp) hdy ≫
          (F.step (p+1)).homologyπ (n+1) := by
        simpa only [id_comp, Category.assoc] using
          S.k_formula p n (𝟙 _) y (by simpa using hy) hdy
      _ = _ := hc.symm
  apply (cancel_epi (FilteredPage.toPage F r p n (P.containment r p n) ≫
    (S.pageIso p n).inv)).1
  dsimp only [ExactCouple.d]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

  have hj := S.j_at (p+1) q (n+1) (by dsimp [q, r]; omega)
    a ha (P.restriction r (by dsimp [r]; omega) p n)
    (by simpa only [a, q, ← almostDifferential_arrow] using
      P.restriction_arrow r (by dsimp [r]; omega) p n)
  calc
    _ = (FilteredPage.toPage F r p n (P.containment r p n) ≫
        (S.pageIso p n).inv ≫ ((initial F h).iterate t).2.k p (p+1) n (n+1) rfl rfl) ≫
        ((initial F h).iterate t).2.j (p+1) q (n+1) (by rw [(initial F h).iterate_degree]; dsimp [q, r]; omega) ≫
        (S.pageIso q (n+1)).hom := by simp only [Category.assoc]; rfl
    _ = _ := by
      rw [hk]
      simpa only [Category.assoc] using hj.trans (P.representative_formula r (by dsimp [r]; omega) p n).symm


def nextAlmostInclusion (t : ℕ) (p n : ℤ) :
    (FilteredPage.almost F (((t+1:ℕ):ℤ)+1) p n : A) ⟶
      (FilteredPage.almost F ((t:ℤ)+1) p n : A) :=
  Subobject.ofLE _ _ (by
    have he : (((t+1:ℕ):ℤ)+1) = (t:ℤ)+1+1 := by omega
    rw [he]
    exact PageCohomology.almost_succ_le F ((t:ℤ)+1) p n)

variable {t : ℕ} (S : EStage F h P t)
variable (I : ∀ p n, ((initial F h).iterate t).2.derivedE p n ≅
  FilteredPage.page F (((t+1:ℕ):ℤ)+1) p n (P.containment (((t+1:ℕ):ℤ)+1) p n))
variable (cyc : ∀ p n,
  ((nextAlmostInclusion (F := F) t p n ≫ FilteredPage.toPage F ((t:ℤ)+1) p n (P.containment _ _ _)) ≫ (S.pageIso p n).inv) ≫
    (((initial F h).iterate t).2.pageComplex p n).g = 0)
variable (can : ∀ p n,
  (((initial F h).iterate t).2.pageComplex p n).liftCycles
    ((nextAlmostInclusion (F := F) t p n ≫ FilteredPage.toPage F ((t:ℤ)+1) p n (P.containment _ _ _)) ≫ (S.pageIso p n).inv)
    (cyc p n) ≫ (((initial F h).iterate t).2.pageComplex p n).homologyπ =
    FilteredPage.toPage F (((t+1:ℕ):ℤ)+1) p n (P.containment _ _ _) ≫ (I p n).inv)

include S cyc can in
theorem propagation_j (p q n : ℤ) (hq : q = p+(t:ℤ)+1) {U : A}
    (x : U ⟶ (F.step q).X n) (hx : x ≫ (F.step q).d n (n+1) = 0)
    (z : U ⟶ (FilteredPage.almost F (((t+1:ℕ):ℤ)+1) q n : A))
    (hz : z ≫ (FilteredPage.almost F (((t+1:ℕ):ℤ)+1) q n).arrow =
      x ≫ (F.piece q n).arrow) :
    (F.step q).liftCycles x (n+1) (by simp) hx ≫ (F.step q).homologyπ n ≫
      (dStage F h t).projection (p+1) q n (by omega) ≫
      ((initial F h).iterate t).2.projection p n ≫
      ((initial F h).iterate t).2.derivedJ p q n
        (by rw [(initial F h).iterate_degree]; omega) ≫ (I q n).hom =
    z ≫ FilteredPage.toPage F (((t+1:ℕ):ℤ)+1) q n (P.containment _ _ _) := by
  let u := (F.step q).liftCycles x (n+1) (by simp) hx ≫ (F.step q).homologyπ n ≫
    (dStage F h t).projection (p+1) q n (by omega)
  let a := (nextAlmostInclusion (F := F) t q n ≫ FilteredPage.toPage F ((t:ℤ)+1) q n (P.containment _ _ _)) ≫ (S.pageIso q n).inv
  have hj : u ≫ ((initial F h).iterate t).2.j (p+1) q n
      (by rw [(initial F h).iterate_degree]; omega) = z ≫ a := by
    apply (cancel_mono (S.pageIso q n).hom).1
    simp only [Category.assoc, a, Iso.inv_hom_id, Category.comp_id]
    simpa only [u, nextAlmostInclusion, Category.assoc] using
      S.j_at (p+1) q n (by omega) x hx
        (z ≫ nextAlmostInclusion (F := F) t q n)
        (by simpa only [nextAlmostInclusion, Category.assoc, Subobject.ofLE_arrow] using hz)
  have hl : u ≫ ((initial F h).iterate t).2.jCycles (p+1) q n
      (by rw [(initial F h).iterate_degree]; omega) =
    z ≫ (((initial F h).iterate t).2.pageComplex q n).liftCycles a (cyc q n) := by
    apply (cancel_mono (((initial F h).iterate t).2.pageComplex q n).iCycles).1
    simpa only [Category.assoc, ExactCouple.jCycles_i, ShortComplex.liftCycles_i] using hj
  suffices hh : u ≫ ((initial F h).iterate t).2.projection p n ≫
      ((initial F h).iterate t).2.derivedJ p q n
        (by rw [(initial F h).iterate_degree]; omega) ≫ (I q n).hom =
      z ≫ FilteredPage.toPage F (((t+1:ℕ):ℤ)+1) q n (P.containment _ _ _) by
    simpa only [u, Category.assoc] using hh
  rw [ExactCouple.projection_derivedJ_assoc]
  dsimp only [ExactCouple.jClass]
  simp only [Category.assoc]
  rw [reassoc_of% hl]
  simpa only [a, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun f => z ≫ f ≫ (I q n).hom) (can q n)

include S cyc can in
theorem propagation_k (p n : ℤ) {U : A}
    (x : U ⟶ (FilteredPage.almost F (((t+1:ℕ):ℤ)+1) p n : A))
    (y : U ⟶ (F.step (p+1)).X (n+1))
    (hy : y ≫ (F.piece (p+1) (n+1)).arrow =
      x ≫ (FilteredPage.almost F (((t+1:ℕ):ℤ)+1) p n).arrow ≫ K.d n (n+1))
    (hdy : y ≫ (F.step (p+1)).d (n+1) (n+1+1) = 0) :
    x ≫ FilteredPage.toPage F (((t+1:ℕ):ℤ)+1) p n (P.containment _ _ _) ≫
      (I p n).inv ≫ ((initial F h).iterate t).2.derivedK p (p+1) n (n+1) rfl rfl ≫
        (((initial F h).iterate t).2.inclusion (p+1) (n+1) ≫
          (dStage F h t).inclusion (p+1) (n+1)) =
      (F.step (p+1)).liftCycles y (n+1+1) (by simp) hdy ≫
        (F.step (p+1)).homologyπ (n+1) := by
  calc
    _ = x ≫ (((initial F h).iterate t).2.pageComplex p n).liftCycles
        ((nextAlmostInclusion (F := F) t p n ≫ FilteredPage.toPage F ((t:ℤ)+1) p n (P.containment _ _ _)) ≫ (S.pageIso p n).inv)
        (cyc p n) ≫ (((initial F h).iterate t).2.pageComplex p n).homologyπ ≫
        ((initial F h).iterate t).2.derivedK p (p+1) n (n+1) rfl rfl ≫
        ((initial F h).iterate t).2.inclusion (p+1) (n+1) ≫
        (dStage F h t).inclusion (p+1) (n+1) := by
      simpa only [Category.assoc] using
        congrArg (fun f => x ≫ f ≫
          ((initial F h).iterate t).2.derivedK p (p+1) n (n+1) rfl rfl ≫
          ((initial F h).iterate t).2.inclusion (p+1) (n+1) ≫
          (dStage F h t).inclusion (p+1) (n+1)) (can p n).symm
    _ = _ := by
      simp only [ExactCouple.homologyπ_derivedK_inclusion_assoc,
        ShortComplex.liftCycles_i_assoc]
      simpa only [nextAlmostInclusion, Category.assoc] using
        S.k_formula p n
          (x ≫ nextAlmostInclusion (F := F) t p n)
          y (by simpa only [nextAlmostInclusion, Category.assoc, Subobject.ofLE_arrow_assoc] using hy) hdy

include S cyc can in
def EStage.succWith : EStage F h P (t+1) where
  pageIso p n := I p n
  j_formula p n U x hx z hz := by
    have hj := propagation_j S I cyc can p (p+((t+1:ℕ):ℤ)) n (by omega) x hx z hz
    simpa only [dStage, DStage.succ, ExactCouple.iterate, ExactCouple.derivation,
      ExactCouple.Derivation.toExactCouple, Category.assoc] using hj
  k_formula p n U x y hy hdy := by
    have hk := propagation_k S I cyc can p n x y hy hdy
    simpa only [dStage, DStage.succ, ExactCouple.iterate, ExactCouple.derivation,
      ExactCouple.Derivation.toExactCouple, Category.assoc] using hk


theorem d_index_transport {s : ℤ} (Q : ExactCouple A s)
    (p q n m p' q' n' m' : ℤ) (hp : p = p') (hq : q = q')
    (hn : n = n') (hm : m = m')
    (hqp : q = p+s+1) (hmn : m = n+1)
    (hqp' : q' = p'+s+1) (hmn' : m' = n'+1) :
    eqToHom (congrArg₂ Q.E hp hn) ≫ Q.d p' q' n' m' hqp' hmn' =
      Q.d p q n m hqp hmn ≫ eqToHom (congrArg₂ Q.E hq hm) := by
  subst p' q' n' m'
  simp

def EStage.pageComplexIsoAt {t : ℕ} (S : EStage F h P t) (p n : ℤ) :
    (((initial F h).iterate t).2.pageComplex (p+((t:ℤ)+1)) (n+1)) ≅
      PageCohomology.shortComplex F P ((t:ℤ)+1) (by omega) p n := by
  let Q := ((initial F h).iterate t).2
  have ha : p+((t:ℤ)+1)-((initial F h).iterate t).1-1 = p := by
    rw [(initial F h).iterate_degree]; omega
  have hb : p+((t:ℤ)+1)+((initial F h).iterate t).1+1 =
      p+((t:ℤ)+1)+((t:ℤ)+1) := by
    rw [(initial F h).iterate_degree]; omega
  let hn : n+1-1 = n := by omega
  let e1 := eqToIso (congrArg₂ Q.E ha hn) ≪≫ S.pageIso p n
  let e3 := eqToIso (congrArg₂ Q.E hb (rfl : n+1+1 = n+1+1)) ≪≫
    S.pageIso (p+((t:ℤ)+1)+((t:ℤ)+1)) (n+1+1)
  refine ShortComplex.isoMk e1 (S.pageIso (p+((t:ℤ)+1)) (n+1)) e3 ?_ ?_
  · change (eqToHom (congrArg₂ Q.E ha hn) ≫ (S.pageIso p n).hom) ≫
      P.differential ((t:ℤ)+1) (by omega) p n =
      Q.d _ _ _ _ (by omega) (by omega) ≫ (S.pageIso _ _).hom
    rw [assoc, ← S.differential_formula, ← assoc]
    rw [d_index_transport Q _ _ _ _ _ _ _ _ ha rfl hn rfl (by omega) (by omega) (by omega) (by omega)]
    simp
  · change (S.pageIso _ _).hom ≫ P.differential ((t:ℤ)+1) (by omega) _ _ =
      Q.d _ _ _ _ (by omega) (by omega) ≫ (eqToHom (congrArg₂ Q.E hb rfl) ≫ (S.pageIso _ _).hom)
    rw [← S.differential_formula, ← assoc]
    rw [← d_index_transport Q _ _ _ _ _ _ _ _ rfl hb rfl rfl (by omega) (by omega) (by omega) (by omega)]
    simp only [eqToHom_refl, id_comp]
    rfl


def EStage.nextPageIsoAt {t : ℕ} (S : EStage F h P t) (p n : ℤ) :
    ((initial F h).iterate t).2.derivedE (p+((t:ℤ)+1)) (n+1) ≅
      FilteredPage.page F ((t:ℤ)+1+1) (p+((t:ℤ)+1)) (n+1) (P.containment _ _ _) :=
  ShortComplex.homologyMapIso (S.pageComplexIsoAt p n) ≪≫
    (PageCohomology.nextIso F P ((t:ℤ)+1) (by omega) p n).symm

theorem EStage.nextCycleAt {t : ℕ} (S : EStage F h P t) (p n : ℤ) :
    (PageCohomology.nextRepresentative F P ((t:ℤ)+1) (p+((t:ℤ)+1)) (n+1) ≫
      (S.pageIso (p+((t:ℤ)+1)) (n+1)).inv) ≫
        (((initial F h).iterate t).2.pageComplex (p+((t:ℤ)+1)) (n+1)).g = 0 := by
  let e := S.pageComplexIsoAt p n
  apply (cancel_mono e.hom.τ₃).1
  rw [zero_comp, assoc, ← e.hom.comm₂₃, ← assoc]
  change ((PageCohomology.nextRepresentative F P ((t:ℤ)+1) (p+((t:ℤ)+1)) (n+1) ≫
    (S.pageIso _ _).inv) ≫ (S.pageIso _ _).hom) ≫ P.differential _ _ _ _ = 0
  simp only [assoc, Iso.inv_hom_id, comp_id]
  simpa only [PageCohomology.nextRepresentative, FilteredPage.toPage, assoc] using
    PageCohomology.next_cycle_at F P ((t:ℤ)+1) (by omega) (p+((t:ℤ)+1)) (n+1)

theorem EStage.nextPageIso_formulaAt {t : ℕ} (S : EStage F h P t) (p n : ℤ) :
    (((initial F h).iterate t).2.pageComplex (p+((t:ℤ)+1)) (n+1)).liftCycles
      (PageCohomology.nextRepresentative F P ((t:ℤ)+1) (p+((t:ℤ)+1)) (n+1) ≫
        (S.pageIso (p+((t:ℤ)+1)) (n+1)).inv) (S.nextCycleAt p n) ≫
      (((initial F h).iterate t).2.pageComplex (p+((t:ℤ)+1)) (n+1)).homologyπ =
    FilteredPage.toPage F ((t:ℤ)+1+1) (p+((t:ℤ)+1)) (n+1) (P.containment _ _ _) ≫
      (S.nextPageIsoAt p n).inv := by
  let e := S.pageComplexIsoAt p n
  apply (cancel_mono (S.nextPageIsoAt p n).hom).1
  simp only [assoc, Iso.inv_hom_id, comp_id]
  dsimp only [EStage.nextPageIsoAt, Iso.trans_hom, ShortComplex.homologyMapIso]
  change _ ≫ _ ≫ (ShortComplex.homologyMap e.hom ≫
    (PageCohomology.nextIso F P ((t:ℤ)+1) (by omega) p n).inv) = _
  erw [ShortComplex.homologyπ_naturality_assoc,
    ← assoc, ShortComplex.liftCycles_comp_cyclesMap]
  apply (cancel_mono (PageCohomology.nextIso F P ((t:ℤ)+1) (by omega) p n).hom).1
  simp only [assoc, Iso.inv_hom_id, comp_id]
  have ht := PageCohomology.toPage_nextIso F P ((t:ℤ)+1) (by omega) p n
  simp only [FilteredPage.toPage, assoc] at ht
  refine Eq.trans ?_ ht.symm
  unfold PageCohomology.nextClass
  congr 1
  apply (cancel_mono (PageCohomology.shortComplex F P ((t:ℤ)+1) (by omega) p n).iCycles).1
  simp only [ShortComplex.liftCycles_i]
  have he : e.hom.τ₂ = (S.pageIso (p+((t:ℤ)+1)) (n+1)).hom := rfl
  rw [he]
  simp only [PageCohomology.nextRepresentative, FilteredPage.toPage, Iso.inv_hom_id, comp_id]


def nextInclusionAtIndex (t : ℕ) (R : ℤ) (hR : R = (t:ℤ)+1+1) (p n : ℤ) :
    (FilteredPage.almost F R p n : A) ⟶ (FilteredPage.almost F ((t:ℤ)+1) p n : A) :=
  Subobject.ofLE _ _ (by rw [hR]; exact PageCohomology.almost_succ_le F ((t:ℤ)+1) p n)

def EStage.nextPageIsoAtIndex {t : ℕ} (S : EStage F h P t)
    (R : ℤ) (hR : R = (t:ℤ)+1+1) (p n : ℤ) :
    ((initial F h).iterate t).2.derivedE (p+((t:ℤ)+1)) (n+1) ≅
      FilteredPage.page F R (p+((t:ℤ)+1)) (n+1) (P.containment _ _ _) := by
  subst R
  exact S.nextPageIsoAt p n

theorem EStage.nextCycleAtIndex {t : ℕ} (S : EStage F h P t)
    (R : ℤ) (hR : R = (t:ℤ)+1+1) (p n : ℤ) :
    ((nextInclusionAtIndex (F := F) t R hR (p+((t:ℤ)+1)) (n+1) ≫
      FilteredPage.toPage F ((t:ℤ)+1) (p+((t:ℤ)+1)) (n+1) (P.containment _ _ _)) ≫
        (S.pageIso (p+((t:ℤ)+1)) (n+1)).inv) ≫
          (((initial F h).iterate t).2.pageComplex (p+((t:ℤ)+1)) (n+1)).g = 0 := by
  subst R
  exact S.nextCycleAt p n

theorem EStage.nextPageIso_formulaAtIndex {t : ℕ} (S : EStage F h P t)
    (R : ℤ) (hR : R = (t:ℤ)+1+1) (p n : ℤ) :
    (((initial F h).iterate t).2.pageComplex (p+((t:ℤ)+1)) (n+1)).liftCycles
      ((nextInclusionAtIndex (F := F) t R hR (p+((t:ℤ)+1)) (n+1) ≫
        FilteredPage.toPage F ((t:ℤ)+1) (p+((t:ℤ)+1)) (n+1) (P.containment _ _ _)) ≫
          (S.pageIso (p+((t:ℤ)+1)) (n+1)).inv) (S.nextCycleAtIndex R hR p n) ≫
      (((initial F h).iterate t).2.pageComplex (p+((t:ℤ)+1)) (n+1)).homologyπ =
    FilteredPage.toPage F R (p+((t:ℤ)+1)) (n+1) (P.containment _ _ _) ≫
      (S.nextPageIsoAtIndex R hR p n).inv := by
  subst R
  exact S.nextPageIso_formulaAt p n

structure EStage.NextData {t : ℕ} (S : EStage F h P t) (p n : ℤ) where
  iso : ((initial F h).iterate t).2.derivedE p n ≅
    FilteredPage.page F (((t+1:ℕ):ℤ)+1) p n (P.containment _ _ _)
  cyc : ((nextAlmostInclusion (F := F) t p n ≫
    FilteredPage.toPage F ((t:ℤ)+1) p n (P.containment _ _ _)) ≫ (S.pageIso p n).inv) ≫
      (((initial F h).iterate t).2.pageComplex p n).g = 0
  can : (((initial F h).iterate t).2.pageComplex p n).liftCycles
    ((nextAlmostInclusion (F := F) t p n ≫
      FilteredPage.toPage F ((t:ℤ)+1) p n (P.containment _ _ _)) ≫ (S.pageIso p n).inv) cyc ≫
        (((initial F h).iterate t).2.pageComplex p n).homologyπ =
      FilteredPage.toPage F (((t+1:ℕ):ℤ)+1) p n (P.containment _ _ _) ≫ iso.inv

def EStage.nextDataAt {t : ℕ} (S : EStage F h P t) (p n : ℤ) :
    S.NextData (p+((t:ℤ)+1)) (n+1) where
  iso := S.nextPageIsoAtIndex (((t+1:ℕ):ℤ)+1) (by omega) p n
  cyc := S.nextCycleAtIndex (((t+1:ℕ):ℤ)+1) (by omega) p n
  can := S.nextPageIso_formulaAtIndex (((t+1:ℕ):ℤ)+1) (by omega) p n

def EStage.nextData {t : ℕ} (S : EStage F h P t) (p n : ℤ) : S.NextData p n := by
  have hp : p = (p-((t:ℤ)+1))+((t:ℤ)+1) := by omega
  have hn : n = (n-1)+1 := by omega
  rw [hp, hn]
  exact S.nextDataAt (p-((t:ℤ)+1)) (n-1)


/-- The canonical cohomology comparison preserves both couple representatives. -/
def EStage.succ {t : ℕ} (S : EStage F h P t) : EStage F h P (t+1) :=
  S.succWith (fun p n => (S.nextData p n).iso)
    (fun p n => (S.nextData p n).cyc) (fun p n => (S.nextData p n).can)

/-- The exact-couple and filtered-page comparisons at every stage. -/
def eStage : (t : ℕ) → EStage F h P t
  | 0 => eStageZero F h P
  | t+1 => (eStage t).succ

/-- Assemble the representative-compatible stage comparisons. -/
def comparisonOfStages (E : ∀ t, EStage F h P t) :
    Comparison (tower F h) (dComparison F h) P where
  pageIso t := (E t).pageIso
  j_formula t := (E t).j_formula
  k_formula t := (E t).k_formula
  differential_formula t := (E t).differential_formula

end FiltrationExactCouple

/-- HA-F05: the first filtration sequence gives an exact couple, and the
couple can be derived indefinitely. -/
theorem filtered_initial_exact_couple : F05Specs.InitialStatement.{v,u} := by
  intro A _ _ K F
  exact ⟨F.firstSequence_shortExact, ⟨FiltrationExactCouple.tower F F.firstSequence_shortExact⟩⟩

/-- HA-F05: after r-1 derivations, D is the image of H(F^(p+r-1)) in H(F^p). -/
theorem filtered_derived_D_terms : F05Specs.DTerms.{v,u} := by
  intro A _ _ K F
  exact ⟨F.firstSequence_shortExact, FiltrationExactCouple.tower F F.firstSequence_shortExact,
    ⟨FiltrationExactCouple.dComparison F F.firstSequence_shortExact⟩⟩

/-- HA-F05: the derived exact couples have the actual filtered pages,
with their differentials, image terms, and generalized representative formulas. -/
theorem filtered_exact_couple : F05Specs.FullStatement.{v,u} := by
  intro A _ _ K F
  let h := F.firstSequence_shortExact
  let P := FilteredPage.pageData F
  exact ⟨h, FiltrationExactCouple.tower F h, FiltrationExactCouple.dComparison F h, P,
    ⟨FiltrationExactCouple.comparisonOfStages
      (FiltrationExactCouple.eStage (F := F) (h := h) (P := P))⟩⟩

end AdvancedHomologicalAlgebra
