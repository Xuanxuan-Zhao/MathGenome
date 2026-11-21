import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FilteredComplexes
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredPages

/-! HA-F03. All subobjects and morphisms are taken in an arbitrary abelian
category. `(p,n)` denotes filtration and total degree. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra

def pageAlmostCycles : F03Specs.AlmostSubobjectType.{v,u} := F03Specs.AlmostValue
def pageBoundarySource : F03Specs.AlmostSubobjectType.{v,u} := F03Specs.BoundarySourceValue
def pageCycles : F03Specs.GradedSubobjectType.{v,u} := F03Specs.CyclesValue
def pageBoundaries : F03Specs.GradedSubobjectType.{v,u} := F03Specs.BoundariesValue
def filteredPage : F03Specs.PageType.{v,u} := F03Specs.PageValue

namespace FilteredPage
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

/-- The image of a restricted map onto an intersection. This is the finite,
abelian-category form of the epic-pullback argument in the source. -/
def imageInfPullbackMap {X Y : A} (f : X ⟶ Y) (S : Subobject X) (T : Subobject Y) :
    Subobject.underlying.obj (S ⊓ (Subobject.pullback f).obj T) ⟶
      Subobject.underlying.obj (imageSubobject (S.arrow ≫ f) ⊓ T) :=
  (Subobject.inf_isPullback (imageSubobject (S.arrow ≫ f)) T).flip.lift
    (Subobject.ofLE _ _ inf_le_right ≫ Subobject.pullbackπ f T)
    (Subobject.ofLE _ _ inf_le_left ≫ factorThruImageSubobject (S.arrow ≫ f))
    (by simp [Category.assoc, (Subobject.isPullback f T).w])

theorem imageInfPullbackMap_isPullback {X Y : A}
    (f : X ⟶ Y) (S : Subobject X) (T : Subobject Y) :
    IsPullback (imageInfPullbackMap f S T)
      (Subobject.ofLE _ _ (inf_le_left : S ⊓ (Subobject.pullback f).obj T ≤ S))
      (Subobject.ofLE _ _ (inf_le_left : imageSubobject (S.arrow ≫ f) ⊓ T ≤ _))
      (factorThruImageSubobject (S.arrow ≫ f)) := by
  apply IsPullback.of_right
    (t := (Subobject.inf_isPullback (imageSubobject (S.arrow ≫ f)) T).flip)
    (p := by simp [imageInfPullbackMap])
  simpa [imageInfPullbackMap, IsPullback.lift_fst,
    (Subobject.isPullback f T).paste_horiz_iff] using
    (Subobject.inf_isPullback S ((Subobject.pullback f).obj T)).flip

instance imageInfPullbackMap_epi {X Y : A}
    (f : X ⟶ Y) (S : Subobject X) (T : Subobject Y) : Epi (imageInfPullbackMap f S T) :=
  Abelian.epi_fst_of_isLimit _ _ (imageInfPullbackMap_isPullback f S T).isLimit

@[reassoc (attr := simp)]
theorem imageInfPullbackMap_arrow {X Y : A}
    (f : X ⟶ Y) (S : Subobject X) (T : Subobject Y) :
    imageInfPullbackMap f S T ≫ (imageSubobject (S.arrow ≫ f) ⊓ T).arrow =
      (S ⊓ (Subobject.pullback f).obj T).arrow ≫ f := by
  rw [imageInfPullbackMap, ← Subobject.inf_comp_left, ← Category.assoc,
    (Subobject.inf_isPullback (imageSubobject (S.arrow ≫ f)) T).flip.lift_snd]
  simp [Category.assoc]

theorem image_inf_pullback {X Y : A} (f : X ⟶ Y) (S : Subobject X) (T : Subobject Y) :
    imageSubobject ((S ⊓ (Subobject.pullback f).obj T).arrow ≫ f) =
      imageSubobject (S.arrow ≫ f) ⊓ T := by
  have : StrongEpi (imageInfPullbackMap f S T) := strongEpi_of_epi _
  simpa only [Subobject.mk_arrow] using (Subobject.mk_eq_imageSubobject_of_mono (imageInfPullbackMap f S T)
    (imageSubobject (S.arrow ≫ f) ⊓ T).arrow
    (imageInfPullbackMap_arrow f S T)).symm

/-- Every boundary is killed by the next ambient differential. -/
theorem boundarySource_d (r p n : ℤ) :
    (boundarySource F r p n).arrow ≫ K.d n (n+1) = 0 := by
  have h : imageSubobject ((F.piece (p-r+1) (n-1)).arrow ≫ K.d (n-1) n) ≤
      kernelSubobject (K.d n (n+1)) := by
    apply imageSubobject_le
      ((F.piece (p-r+1) (n-1)).arrow ≫ K.d (n-1) n)
      (factorThruKernelSubobject (K.d n (n+1))
        ((F.piece (p-r+1) (n-1)).arrow ≫ K.d (n-1) n) (by simp [Category.assoc]))
    exact factorThruKernelSubobject_comp_arrow _ _ _
  have hh : boundarySource F r p n ≤ kernelSubobject (K.d n (n+1)) :=
    le_trans inf_le_right h
  rw [← Subobject.ofLE_arrow hh, Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- The source's boundary containment already holds before quotienting. -/
theorem boundarySource_le_almost (r p n : ℤ) :
    boundarySource F r p n ≤ almost F r p n := by
  apply le_inf inf_le_left
  apply Subobject.le_of_factors
  apply pullback_factors
  change (F.piece (p+r) (n+1)).Factors ((boundarySource F r p n).arrow ≫ K.d n (n+1))
  rw [boundarySource_d]
  exact Subobject.factors_zero

@[reassoc (attr := simp)]
theorem gradedRepresentative_naturality (p n : ℤ) {S T : Subobject (K.X n)}
    (hST : S ≤ T) (hT : T ≤ F.piece p n) :
    Subobject.ofLE _ _ hST ≫ gradedRepresentative F p n T hT =
      gradedRepresentative F p n S (hST.trans hT) := by
  dsimp [gradedRepresentative]
  rw [← Category.assoc, Subobject.ofLE_comp_ofLE]

theorem boundaries_le_cycles (r p n : ℤ) : boundaries F r p n ≤ cycles F r p n := by
  unfold boundaries cycles
  simpa only [gradedRepresentative_naturality] using
    imageSubobject_comp_le (Subobject.ofLE _ _ (boundarySource_le_almost F r p n))
      (gradedRepresentative F p n (almost F r p n) inf_le_left)

instance toPage_epi (r p n : ℤ) (h : boundaries F r p n ≤ cycles F r p n) :
    Epi (toPage F r p n h) := by
  change Epi (factorThruImageSubobject _ ≫ cokernel.π _)
  exact epi_comp _ _

/-- The differential maps almost cycles to almost cycles at the new bidegree. -/
theorem differential_factors (r p n : ℤ) :
    (almost F r (p+r) (n+1)).Factors ((almost F r p n).arrow ≫ K.d n (n+1)) := by
  apply (Subobject.inf_factors _).2
  constructor
  · exact (pullback_factors_iff _ _ _).1
      (Subobject.factors_of_le _ inf_le_right (Subobject.factors_self _))
  · apply pullback_factors
    simp only [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
    exact Subobject.factors_zero

def restriction (r p n : ℤ) :
    (almost F r p n : A) ⟶ (almost F r (p+r) (n+1) : A) :=
  (almost F r (p+r) (n+1)).factorThru _ (differential_factors F r p n)

@[reassoc (attr := simp)]
theorem restriction_arrow (r p n : ℤ) :
    restriction F r p n ≫ (almost F r (p+r) (n+1)).arrow =
      (almost F r p n).arrow ≫ K.d n (n+1) :=
  Subobject.factorThru_arrow _ _ _

theorem restriction_square_zero (r p n : ℤ) :
    restriction F r p n ≫ restriction F r (p+r) (n+1) = 0 := by
  apply (cancel_mono (almost F r (p+r+r) (n+1+1)).arrow).1
  simp [Category.assoc]

/-- Vanishing of a morphism to the page can be checked by factoring its
ambient representative through the boundary subobject. -/
theorem toPage_zero_of_boundary (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) {W : A}
    (x : W ⟶ (almost F r p n : A))
    (hx : (boundarySource F r p n).Factors (x ≫ (almost F r p n).arrow)) :
    x ≫ toPage F r p n h = 0 := by
  let b := (boundarySource F r p n).factorThru _ hx
  have hb : b ≫ Subobject.ofLE _ _ (boundarySource_le_almost F r p n) = x := by
    apply (cancel_mono (almost F r p n).arrow).1
    simp [b, Category.assoc]
  rw [← hb, Category.assoc]
  have hw : Subobject.ofLE _ _ (boundarySource_le_almost F r p n) ≫
      factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left) =
      factorThruImageSubobject (gradedRepresentative F p n (boundarySource F r p n) inf_le_left) ≫
        Subobject.ofLE _ _ h := by
    apply (cancel_mono (cycles F r p n).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow,
      cycles, imageSubobject_arrow_comp, gradedRepresentative_naturality]
  change b ≫ (Subobject.ofLE _ _ (boundarySource_le_almost F r p n) ≫
    factorThruImageSubobject _ ≫ cokernel.π _) = 0
  rw [← Category.assoc (Subobject.ofLE _ _ _) (factorThruImageSubobject _) _, hw]
  rw [Category.assoc (factorThruImageSubobject _) _ _, cokernel.condition, comp_zero, comp_zero]

/-- Changing a representative by the next filtration step changes its
differential by a boundary on the target page. -/
theorem restriction_toPage_zero (r p n : ℤ)
    (h : boundaries F r (p+r) (n+1) ≤ cycles F r (p+r) (n+1))
    {W : A} (x : W ⟶ (almost F r p n : A))
    (hx : x ≫ gradedRepresentative F p n (almost F r p n) inf_le_left = 0) :
    x ≫ restriction F r p n ≫ toPage F r (p+r) (n+1) h = 0 := by
  let y : W ⟶ (F.piece p n : A) := x ≫ Subobject.ofLE _ _ (inf_le_left : almost F r p n ≤ _)
  have hy : y ≫ cokernel.π ((F.transition p).f n) = 0 := by
    simpa only [y, gradedRepresentative, Filtration.projection, Category.assoc] using hx
  have : Mono ((F.transition p).f n) := inferInstanceAs (Mono (Subobject.ofLE _ _ _))
  let t := Abelian.monoLift ((F.transition p).f n) y hy
  have ht : t ≫ (F.piece (p+1) n).arrow = x ≫ (almost F r p n).arrow := by
    calc
      t ≫ (F.piece (p+1) n).arrow =
          (t ≫ (F.transition p).f n) ≫ (F.piece p n).arrow := by
        simp [Filtration.transition, Category.assoc]
      _ = y ≫ (F.piece p n).arrow := by rw [Abelian.monoLift_comp]
      _ = x ≫ (almost F r p n).arrow := by simp [y, Category.assoc]
  rw [← Category.assoc]
  apply toPage_zero_of_boundary
  change ((F.piece (p+r) (n+1) ⊓ imageSubobject
    ((F.piece ((p+r)-r+1) ((n+1)-1)).arrow ≫ K.d ((n+1)-1) (n+1))) : Subobject _).Factors _
  apply (Subobject.inf_factors _).2
  constructor
  · exact Subobject.factors_of_le _ inf_le_left (Subobject.factors_comp_arrow _)
  · rw [Category.assoc, restriction_arrow, ← Category.assoc, ← ht, Category.assoc]
    have hp : p+r-r+1 = p+1 := by omega
    have hn : n+1-1 = n := by omega
    rw [hp, hn]
    exact imageSubobject_factors_comp_self
      ((F.piece (p+1) n).arrow ≫ K.d n (n+1)) t


/-- Descend the representative differential to the cycle subobject. -/
def cyclesDifferential (r p n : ℤ)
    (h : boundaries F r (p+r) (n+1) ≤ cycles F r (p+r) (n+1)) :
    (cycles F r p n : A) ⟶ page F r (p+r) (n+1) h :=
  Abelian.epiDesc
    (factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left))
    (restriction F r p n ≫ toPage F r (p+r) (n+1) h) (by
      apply restriction_toPage_zero
      calc
        kernel.ι _ ≫ gradedRepresentative F p n (almost F r p n) inf_le_left =
            kernel.ι _ ≫ (factorThruImageSubobject _ ≫ (cycles F r p n).arrow) := by
          rw [imageSubobject_arrow_comp]
        _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
theorem toCycles_cyclesDifferential (r p n : ℤ)
    (h : boundaries F r (p+r) (n+1) ≤ cycles F r (p+r) (n+1)) :
    factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left) ≫
      cyclesDifferential F r p n h = restriction F r p n ≫ toPage F r (p+r) (n+1) h :=
  Abelian.comp_epiDesc _ _ _

theorem boundaries_cyclesDifferential (r p n : ℤ)
    (h₀ : boundaries F r p n ≤ cycles F r p n)
    (h₁ : boundaries F r (p+r) (n+1) ≤ cycles F r (p+r) (n+1)) :
    Subobject.ofLE _ _ h₀ ≫ cyclesDifferential F r p n h₁ = 0 := by
  apply (cancel_epi (factorThruImageSubobject
    (gradedRepresentative F p n (boundarySource F r p n) inf_le_left))).1
  rw [comp_zero]
  have hw : factorThruImageSubobject
      (gradedRepresentative F p n (boundarySource F r p n) inf_le_left) ≫
        Subobject.ofLE _ _ h₀ =
      Subobject.ofLE _ _ (boundarySource_le_almost F r p n) ≫
        factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left) := by
    apply (cancel_mono (cycles F r p n).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, cycles,
      imageSubobject_arrow_comp, gradedRepresentative_naturality]
  rw [← Category.assoc, hw, Category.assoc, toCycles_cyclesDifferential, ← Category.assoc]
  have hz : Subobject.ofLE _ _ (boundarySource_le_almost F r p n) ≫
      restriction F r p n = 0 := by
    apply (cancel_mono (almost F r (p+r) (n+1)).arrow).1
    simp [Category.assoc, boundarySource_d]
  rw [hz, zero_comp]

/-- The required map on `Z_r/B_r`, induced by the ambient differential. -/
def differential (r p n : ℤ)
    (h₀ : boundaries F r p n ≤ cycles F r p n)
    (h₁ : boundaries F r (p+r) (n+1) ≤ cycles F r (p+r) (n+1)) :
    page F r p n h₀ ⟶ page F r (p+r) (n+1) h₁ :=
  cokernel.desc _ (cyclesDifferential F r p n h₁)
    (boundaries_cyclesDifferential F r p n h₀ h₁)

@[reassoc (attr := simp)]
theorem toPage_differential (r p n : ℤ)
    (h₀ : boundaries F r p n ≤ cycles F r p n)
    (h₁ : boundaries F r (p+r) (n+1) ≤ cycles F r (p+r) (n+1)) :
    toPage F r p n h₀ ≫ differential F r p n h₀ h₁ =
      restriction F r p n ≫ toPage F r (p+r) (n+1) h₁ := by
  dsimp only [toPage, differential]
  rw [Category.assoc, cokernel.π_desc, toCycles_cyclesDifferential]

theorem differential_square_zero (r p n : ℤ)
    (h₀ : boundaries F r p n ≤ cycles F r p n)
    (h₁ : boundaries F r (p+r) (n+1) ≤ cycles F r (p+r) (n+1))
    (h₂ : boundaries F r (p+r+r) (n+1+1) ≤ cycles F r (p+r+r) (n+1+1)) :
    differential F r p n h₀ h₁ ≫ differential F r (p+r) (n+1) h₁ h₂ = 0 := by
  apply (cancel_epi (toPage F r p n h₀)).1
  calc
    toPage F r p n h₀ ≫
        (differential F r p n h₀ h₁ ≫ differential F r (p+r) (n+1) h₁ h₂) =
      (restriction F r p n ≫ toPage F r (p+r) (n+1) h₁) ≫
        differential F r (p+r) (n+1) h₁ h₂ := by
          rw [← Category.assoc]
          exact congrArg (fun f => f ≫ differential F r (p+r) (n+1) h₁ h₂)
            (toPage_differential F r p n h₀ h₁)
    _ = restriction F r p n ≫
        (restriction F r (p+r) (n+1) ≫ toPage F r (p+r+r) (n+1+1) h₂) := by
          rw [Category.assoc]
          exact congrArg (fun f => restriction F r p n ≫ f)
            (toPage_differential F r (p+r) (n+1) h₁ h₂)
    _ = toPage F r p n h₀ ≫ 0 := by
      rw [← Category.assoc, restriction_square_zero, zero_comp, comp_zero]

/-- On page zero all elements of the filtration step are almost cycles. -/
theorem almost_zero (p n : ℤ) : almost F 0 p n = F.piece p n := by
  apply inf_eq_left.mpr
  apply Subobject.le_of_factors
  apply pullback_factors
  simpa only [add_zero] using
    ((Subobject.factors_iff _ _).2 (F.preserved p n (n+1)))

theorem boundaries_zero (p n : ℤ) : boundaries F 0 p n = ⊥ := by
  have h : boundarySource F 0 p n ≤ F.piece (p+1) n := by
    change F.piece p n ⊓ imageSubobject
      ((F.piece (p-0+1) (n-1)).arrow ≫ K.d (n-1) n) ≤ _
    rw [sub_zero]
    exact inf_le_right.trans (imageSubobject_le _
      (F.differential (p+1) (n-1) n) (F.differential_arrow (p+1) (n-1) n))

  have hz : gradedRepresentative F p n (boundarySource F 0 p n) inf_le_left = 0 := by
    have hw : Subobject.ofLE _ _ (inf_le_left : boundarySource F 0 p n ≤ F.piece p n) =
        Subobject.ofLE _ _ h ≫ (F.transition p).f n := by
      apply (cancel_mono (F.piece p n).arrow).1
      simp [Filtration.transition]
    dsimp only [gradedRepresentative, Filtration.projection]
    rw [hw, Category.assoc, cokernel.condition, comp_zero]
  exact (congrArg (fun f => imageSubobject f) hz).trans (imageSubobject_zero)

theorem cycles_zero (p n : ℤ) : cycles F 0 p n = ⊤ := by
  have hi : IsIso (Subobject.ofLE _ _ (inf_le_left : almost F 0 p n ≤ F.piece p n)) :=
    (Subobject.isoOfEq _ _ (almost_zero F p n)).isIso_hom
  have : Epi (gradedRepresentative F p n (almost F 0 p n) inf_le_left) := by
    dsimp only [gradedRepresentative, Filtration.projection]
    infer_instance
  have : Epi (cycles F 0 p n).arrow := epi_of_epi_fac (imageSubobject_arrow_comp _)
  exact (Subobject.isIso_arrow_iff_eq_top _).1 (isIso_of_mono_of_epi _)

/-- Zeroth-page identification, keeping its action on representatives. -/
def zeroPageIso (p n : ℤ) (h : boundaries F 0 p n ≤ cycles F 0 p n) :
    page F 0 p n h ≅ (F.graded p).X n := by
  let b := Subobject.ofLE _ _ h
  have hb : b = 0 := by
    apply (cancel_mono (cycles F 0 p n).arrow).1
    rw [Subobject.ofLE_arrow, zero_comp]
    rw [boundaries_zero, Subobject.bot_arrow]
  have : IsIso (cokernel.π b) := by rw [hb]; infer_instance
  have : IsIso (cycles F 0 p n).arrow := by
    rw [cycles_zero]; infer_instance
  exact (asIso (cokernel.π b)).symm ≪≫ asIso (cycles F 0 p n).arrow

@[reassoc (attr := simp)]
theorem toPage_zeroPageIso (p n : ℤ) (h : boundaries F 0 p n ≤ cycles F 0 p n) :
    toPage F 0 p n h ≫ (zeroPageIso F p n h).hom =
      gradedRepresentative F p n (almost F 0 p n) inf_le_left := by
  dsimp only [zeroPageIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, toPage]
  rw [Category.assoc, ← Category.assoc (cokernel.π _) _ _, IsIso.hom_inv_id,
    Category.id_comp, imageSubobject_arrow_comp]

/-- The first summand of the alternate denominator is the intersection with
the next filtration step. -/
theorem almost_inter_next (r p n : ℤ) :
    almost F (r-1) (p+1) n = almost F r p n ⊓ F.piece (p+1) n := by
  have hp : p+1+(r-1) = p+r := by omega
  dsimp only [almost]
  rw [hp]
  apply le_antisymm
  · exact le_inf (le_inf (inf_le_left.trans (F.decreasing p n)) inf_le_right) inf_le_left
  · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)

/-- The other summand is exactly the boundary subobject before projection. -/
theorem boundarySource_eq_image (r p n : ℤ) :
    boundarySource F r p n =
      imageSubobject ((almost F (r-1) (p-r+1) (n-1)).arrow ≫ K.d (n-1) n) := by
  have hp : p-r+1+(r-1) = p := by omega
  have hn : n-1+1 = n := by omega
  dsimp only [almost, boundarySource]
  change F.piece p n ⊓ imageSubobject ((F.piece (p-r+1) (n-1)).arrow ≫ K.d (n-1) n) =
    imageSubobject ((F.piece (p-r+1) (n-1) ⊓
      (Subobject.pullback (K.d (n-1) (n-1+1))).obj
        (F.piece (p-r+1+(r-1)) (n-1+1))).arrow ≫ K.d (n-1) n)
  rw [hp, hn]
  rw [image_inf_pullback, inf_comm]

theorem denominator_le (r p n : ℤ) : denominator F r p n ≤ almost F r p n := by
  rw [denominator, ← boundarySource_eq_image, almost_inter_next]
  exact sup_le inf_le_left (boundarySource_le_almost F r p n)


/-- A zero graded representative factors through the next filtration step.
This uses the kernel property of the monic filtration transition, without
assuming that epimorphisms admit sections. -/
theorem graded_zero_factors_next (r p n : ℤ) {W : A}
    (x : W ⟶ (almost F r p n : A))
    (hx : x ≫ gradedRepresentative F p n (almost F r p n) inf_le_left = 0) :
    (almost F r p n ⊓ F.piece (p+1) n).Factors (x ≫ (almost F r p n).arrow) := by
  apply (Subobject.inf_factors _).2
  refine ⟨Subobject.factors_comp_arrow _, ?_⟩
  have : Mono ((F.transition p).f n) := inferInstanceAs (Mono (Subobject.ofLE _ _ _))
  let y := x ≫ Subobject.ofLE _ _ (inf_le_left : almost F r p n ≤ F.piece p n)
  have hy : y ≫ cokernel.π ((F.transition p).f n) = 0 := by
    simpa only [y, gradedRepresentative, Filtration.projection, Category.assoc] using hx
  let t := Abelian.monoLift ((F.transition p).f n) y hy
  refine (Subobject.factors_iff _ _).2 ⟨t, ?_⟩
  calc
    t ≫ (F.piece (p+1) n).arrow =
        (t ≫ (F.transition p).f n) ≫
          (F.piece p n).arrow := by simp [Filtration.transition, Category.assoc]
    _ = y ≫ (F.piece p n).arrow := by rw [Abelian.monoLift_comp]
    _ = x ≫ (almost F r p n).arrow := by simp [y, Category.assoc]

/-- A map from a sum vanishes when its restrictions to both summands vanish. -/
theorem sup_restriction_zero {X Y : A} (U V S : Subobject X)
    (h : U ⊔ V ≤ S) (g : (S : A) ⟶ Y)
    (hU : Subobject.ofLE _ _ (le_sup_left.trans h) ≫ g = 0)
    (hV : Subobject.ofLE _ _ (le_sup_right.trans h) ≫ g = 0) :
    Subobject.ofLE _ _ h ≫ g = 0 := by
  have : StrongEpi (Subobject.supMonoFactorisation U V).e :=
    strongEpi_of_strongEpiMonoFactorisation
      (Abelian.imageStrongEpiMonoFactorisation _) (Subobject.supIsImage U V)
  apply (cancel_epi (Subobject.supMonoFactorisation U V).e).1
  apply coprod.hom_ext
  · simpa only [Subobject.supMonoFactorisation, comp_zero, ← Category.assoc,
      coprod.inl_desc, Subobject.ofLE_comp_ofLE] using hU
  · simpa only [Subobject.supMonoFactorisation, comp_zero, ← Category.assoc,
      coprod.inr_desc, Subobject.ofLE_comp_ofLE] using hV

/-- A map to the page vanishes if its graded representative is zero. -/
theorem toPage_zero_of_graded_zero (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) {W : A}
    (x : W ⟶ (almost F r p n : A))
    (hx : x ≫ gradedRepresentative F p n (almost F r p n) inf_le_left = 0) :
    x ≫ toPage F r p n h = 0 := by
  have hz : x ≫ factorThruImageSubobject
      (gradedRepresentative F p n (almost F r p n) inf_le_left) = 0 := by
    apply (cancel_mono (cycles F r p n).arrow).1
    simpa only [Category.assoc, imageSubobject_arrow_comp, zero_comp] using hx
  change x ≫ (factorThruImageSubobject _ ≫ cokernel.π _) = 0
  rw [← Category.assoc, hz, zero_comp]

theorem next_toPage_zero (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) :
    Subobject.ofLE _ _ (inf_le_left : almost F r p n ⊓ F.piece (p+1) n ≤ _) ≫
      toPage F r p n h = 0 := by
  apply toPage_zero_of_graded_zero
  have hw : Subobject.ofLE _ _ (inf_le_left : almost F r p n ⊓ F.piece (p+1) n ≤ _) ≫
      Subobject.ofLE _ _ (inf_le_left : almost F r p n ≤ F.piece p n) =
      Subobject.ofLE _ _ (inf_le_right : almost F r p n ⊓ F.piece (p+1) n ≤ _) ≫
        (F.transition p).f n := by
    apply (cancel_mono (F.piece p n).arrow).1
    simp [Filtration.transition]
  dsimp only [gradedRepresentative, Filtration.projection]
  rw [← Category.assoc, hw, Category.assoc, cokernel.condition, comp_zero]

theorem denominator_toPage_zero (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) :
    Subobject.ofLE _ _ (denominator_le F r p n) ≫ toPage F r p n h = 0 := by
  suffices ∀ (D : Subobject (K.X n)) (hD : D ≤ almost F r p n),
      D = (almost F r p n ⊓ F.piece (p+1) n) ⊔ boundarySource F r p n →
        Subobject.ofLE _ _ hD ≫ toPage F r p n h = 0 by
    apply this
    rw [denominator, almost_inter_next, ← boundarySource_eq_image]
  intro D hD he
  subst D
  apply sup_restriction_zero
  · exact next_toPage_zero F r p n h
  · apply toPage_zero_of_boundary
    rw [Subobject.ofLE_arrow]
    exact Subobject.factors_self _

abbrev alternateQuotient (r p n : ℤ) : A :=
  cokernel (Subobject.ofLE _ _ (denominator_le F r p n))

/-- Any representative lying in the denominator is zero in the alternate quotient. -/
theorem toAlternate_zero_of_factors (r p n : ℤ) {W : A}
    (x : W ⟶ (almost F r p n : A))
    (hx : (denominator F r p n).Factors (x ≫ (almost F r p n).arrow)) :
    x ≫ cokernel.π (Subobject.ofLE _ _ (denominator_le F r p n)) = 0 := by
  let b := (denominator F r p n).factorThru _ hx
  have hb : b ≫ Subobject.ofLE _ _ (denominator_le F r p n) = x := by
    apply (cancel_mono (almost F r p n).arrow).1
    simp [b, Category.assoc]
  rw [← hb, Category.assoc, cokernel.condition, comp_zero]

theorem toAlternate_zero_of_graded_zero (r p n : ℤ) {W : A}
    (x : W ⟶ (almost F r p n : A))
    (hx : x ≫ gradedRepresentative F p n (almost F r p n) inf_le_left = 0) :
    x ≫ cokernel.π (Subobject.ofLE _ _ (denominator_le F r p n)) = 0 := by
  apply toAlternate_zero_of_factors
  apply Subobject.factors_of_le _
    (show almost F r p n ⊓ F.piece (p+1) n ≤ denominator F r p n from ?_)
    (graded_zero_factors_next F r p n x hx)
  rw [denominator, almost_inter_next]
  exact le_sup_left

/-- The alternate quotient map first descends to the cycle image. -/
def cyclesToAlternate (r p n : ℤ) : (cycles F r p n : A) ⟶ alternateQuotient F r p n :=
  Abelian.epiDesc
    (factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left))
    (cokernel.π (Subobject.ofLE _ _ (denominator_le F r p n))) (by
      apply toAlternate_zero_of_graded_zero
      calc
        kernel.ι _ ≫ gradedRepresentative F p n (almost F r p n) inf_le_left =
            kernel.ι _ ≫ (factorThruImageSubobject _ ≫ (cycles F r p n).arrow) := by
          rw [imageSubobject_arrow_comp]
        _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
theorem toCycles_cyclesToAlternate (r p n : ℤ) :
    factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left) ≫
      cyclesToAlternate F r p n =
        cokernel.π (Subobject.ofLE _ _ (denominator_le F r p n)) :=
  Abelian.comp_epiDesc _ _ _

theorem boundaries_cyclesToAlternate (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) :
    Subobject.ofLE _ _ h ≫ cyclesToAlternate F r p n = 0 := by
  apply (cancel_epi (factorThruImageSubobject
    (gradedRepresentative F p n (boundarySource F r p n) inf_le_left))).1
  rw [comp_zero]
  have hw : factorThruImageSubobject
      (gradedRepresentative F p n (boundarySource F r p n) inf_le_left) ≫
        Subobject.ofLE _ _ h =
      Subobject.ofLE _ _ (boundarySource_le_almost F r p n) ≫
        factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left) := by
    apply (cancel_mono (cycles F r p n).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, cycles,
      imageSubobject_arrow_comp, gradedRepresentative_naturality]
  rw [← Category.assoc, hw, Category.assoc, toCycles_cyclesToAlternate]
  apply toAlternate_zero_of_factors
  rw [Subobject.ofLE_arrow]
  apply Subobject.factors_of_le _ _ (Subobject.factors_self _)
  rw [denominator, ← boundarySource_eq_image]
  exact le_sup_right

/-- The alternate presentation is canonically isomorphic to `Z_r/B_r`.
Both maps are specified on the common almost-cycle representatives. -/
def quotientIso (r p n : ℤ) (h : boundaries F r p n ≤ cycles F r p n) :
    alternateQuotient F r p n ≅ page F r p n h where
  hom := cokernel.desc _ (toPage F r p n h) (denominator_toPage_zero F r p n h)
  inv := cokernel.desc _ (cyclesToAlternate F r p n) (boundaries_cyclesToAlternate F r p n h)
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (denominator_le F r p n)))).1
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    change (factorThruImageSubobject _ ≫ cokernel.π _) ≫ cokernel.desc _ _ _ = _
    rw [Category.assoc, cokernel.π_desc, toCycles_cyclesToAlternate]
  inv_hom_id := by
    apply (cancel_epi (toPage F r p n h)).1
    change (factorThruImageSubobject _ ≫ cokernel.π _) ≫
      (cokernel.desc _ _ _ ≫ cokernel.desc _ _ _) = _
    rw [Category.assoc, cokernel.π_desc_assoc, ← Category.assoc,
      toCycles_cyclesToAlternate, cokernel.π_desc, Category.comp_id]

@[reassoc (attr := simp)]
theorem toAlternate_quotientIso (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) :
    cokernel.π (Subobject.ofLE _ _ (denominator_le F r p n)) ≫
      (quotientIso F r p n h).hom = toPage F r p n h :=
  cokernel.π_desc _ _ _


/-- The zeroth-page identification respects equality of filtration indices.
The explicit equality permits the bidegree `(p+0,n+1)` to be identified with
`(p,n+1)` without unfolding the quotient construction. -/
theorem toPage_zeroPageIso_reindex (p p' n : ℤ) (hp : p = p')
    (h : boundaries F 0 p n ≤ cycles F 0 p n)
    (h' : boundaries F 0 p' n ≤ cycles F 0 p' n) {W : A}
    (x : W ⟶ (almost F 0 p n : A)) (y : W ⟶ (F.piece p' n : A))
    (hxy : x ≫ (almost F 0 p n).arrow = y ≫ (F.piece p' n).arrow) :
    x ≫ toPage F 0 p n h ≫
      (eqToIso (by cases hp; rfl : page F 0 p n h = page F 0 p' n h')).hom ≫
        (zeroPageIso F p' n h').hom = y ≫ (F.projection p').f n := by
  subst p'
  rw [eqToIso_refl, Iso.refl_hom, Category.id_comp, toPage_zeroPageIso]
  change x ≫ (Subobject.ofLE _ _ _ ≫ (F.projection p).f n) = _
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (F.piece p n).arrow).1
  simpa only [Category.assoc, Subobject.ofLE_arrow] using hxy

/-- All the constructions, with their defining formulas, in the original
abelian-category scope. -/
def pageData : F03Specs.PageData F where
  containment := boundaries_le_cycles F
  differential r _ p n := differential F r p n _ _
  restriction r _ p n := restriction F r p n
  restriction_arrow r _ p n := restriction_arrow F r p n
  representative_formula r _ p n := toPage_differential F r p n _ _
  square_zero r _ p n := differential_square_zero F r p n _ _ _
  almost_zero := almost_zero F
  boundaries_zero := boundaries_zero F
  cycles_zero := cycles_zero F
  zeroPageIso p n := zeroPageIso F p n _
  zeroPageIso_formula p n := toPage_zeroPageIso F p n _
  zero_differential := by
    intro p n
    apply (cancel_epi (toPage F 0 p n (boundaries_le_cycles F 0 p n))).1
    rw [← Category.assoc, toPage_differential, Category.assoc]
    let y : (almost F 0 p n : A) ⟶ (F.step p).X (n+1) :=
      Subobject.ofLE _ _ (inf_le_left : almost F 0 p n ≤ F.piece p n) ≫
        (F.step p).d n (n+1)
    trans y ≫ (F.projection p).f (n+1)
    · apply toPage_zeroPageIso_reindex F (p+0) p (n+1) (add_zero p)
      simp [y, Category.assoc, Filtration.step]
    · dsimp only [y]
      rw [Category.assoc, ← (F.projection p).comm n (n+1)]
      rw [← Category.assoc (toPage F 0 p n _) _ _, toPage_zeroPageIso]
      exact (Category.assoc _ _ _).symm
  denominator_le r _ p n := denominator_le F r p n
  quotientIso r _ p n := quotientIso F r p n _
  quotientIso_formula r _ p n := toAlternate_quotientIso F r p n _

end FilteredPage

/-- Boundaries are contained in cycles on every page. -/
theorem page_boundaries_le_cycles : F03Specs.BoundaryContainment.{v,u} := by
  intro A _ _ K F r p n
  exact FilteredPage.boundaries_le_cycles F r p n

/-- HA-F03, including page zero and the equivalent almost-cycle quotient. -/
theorem filtered_pages : F03Specs.FullStatement.{v,u} := by
  intro A _ _ K F
  exact ⟨FilteredPage.pageData F⟩
end AdvancedHomologicalAlgebra
