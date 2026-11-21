import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.DoubleCover
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Equivalences
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.CoveringStructure
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.ProductsAndSigns
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Topology

namespace SmoothManifolds.OrientationCover
open ModelData AtlasData MapData TangentData DifferentialData
  OrientationData OrientationProductData OrientationCoverData OrientationResults
  CoveringData Set Filter
open TangentBundleData (FiberCoordinates)
universe u

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- The two rays in a determinant fiber give the two actual points over p. -/
def fiberEquiv (S : SmoothManifold n a M) (p : M) :
    (projection S ⁻¹' {p}) ≃ Bool := by
  let K := Classical.choice (TangentBundle.fiberCoordinates_exists S)
  let c := Classical.choose (S.smoothStructure.property.1.1 p)
  have hc := (Classical.choose_spec (S.smoothStructure.property.1.1 p)).1
  have hp := (Classical.choose_spec (S.smoothStructure.property.1.1 p)).2
  let e := coordinateRayEquiv K c hc ⟨p, hp⟩
  let f : Bool → ↥(projection S ⁻¹' {p}) := fun b => ⟨⟨p, e b⟩, rfl⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro b d h
    have he : e b = e d := by
      have h' := congrArg Subtype.val h
      exact eq_of_heq (Sigma.mk.inj h').2
    exact e.injective he
  · rintro ⟨⟨q, r⟩, hq⟩
    have hqp : q = p := hq
    subst q
    refine ⟨e.symm r, ?_⟩
    apply Subtype.ext
    change Sigma.mk p (e (e.symm r)) = Sigma.mk p r
    rw [e.apply_symm_apply]

/-- Negation preserves local continuity in every determinant chart. -/
def negateLocal (L : LocalOrientation S) : LocalOrientation S where
  domain := L.domain
  isOpen_domain := L.isOpen_domain
  ray p := -L.ray p
  continuous K c hc := by
    have h := (L.continuous K c hc).comp (fun r => -r)
    convert h using 1
    funext p
    exact Module.Ray.map_neg _ _

/-- A global orientation is, in particular, a local orientation on all of M. -/
def globalLocal (o : Orientation S) : LocalOrientation S where
  domain := univ
  isOpen_domain := isOpen_univ
  ray p := o.val p.val
  continuous K c hc := by
    let incl : ↥((univ : Set M) ∩ c.source) → c.source := fun p => ⟨p.val, p.property.2⟩
    exact (o.property K c hc).comp_continuous (continuous_subtype_val.subtype_mk _ : Continuous incl)

theorem continuous_lift (L : LocalOrientation S) : Continuous L.lift := by
  exact continuous_iSup_rng (i := L) continuous_coinduced_rng

theorem continuous_projection : Continuous (projection S) := by
  change @Continuous _ _ (⨆ L : LocalOrientation S,
    TopologicalSpace.coinduced L.lift inferInstance) _ _
  rw [continuous_iSup_dom]
  intro L
  rw [continuous_coinduced_dom]
  exact continuous_subtype_val

theorem deck_involutive : Function.Involutive (deck S) := by
  rintro ⟨p, r⟩
  exact congrArg (Sigma.mk p) (neg_neg r)

theorem deck_fixedPointFree (z : Space S) : deck S z ≠ z := by
  intro h
  have he : -z.2 = z.2 := eq_of_heq (Sigma.mk.inj h).2
  exact Module.Ray.ne_neg_self z.2 he.symm

theorem continuous_deck : Continuous (deck S) := by
  change @Continuous _ _ (⨆ L : LocalOrientation S,
    TopologicalSpace.coinduced L.lift inferInstance) _ _
  rw [continuous_iSup_dom]
  intro L
  rw [continuous_coinduced_dom]
  exact continuous_lift (negateLocal L)

def deckHomeomorph : Space S ≃ₜ Space S where
  toFun := deck S
  invFun := deck S
  left_inv := deck_involutive
  right_inv := deck_involutive
  continuous_toFun := continuous_deck
  continuous_invFun := continuous_deck

theorem continuous_section (o : Orientation S) : Continuous (sectionOf o) := by
  exact (continuous_lift (globalLocal o)).comp (continuous_id.subtype_mk (fun _ => mem_univ _))

/-- The coordinate determinant wedge is smooth in all determinant charts. -/
theorem coordinate_section_smooth (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    IsSmoothDeterminantSection c.source c.open_source (coordinateVector K c hc) := by
  intro L d hd
  have h := transitionDeterminant_smooth S L c d hc hd
  convert h using 1
  funext p
  rw [coordinateVector_independent K L, coefficient_coordinateVector_transition]

/-- Actual local continuous orientations exist about every base point. -/
def coordinateLocal (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) : LocalOrientation S where
  domain := c.source
  isOpen_domain := c.open_source
  ray p := rayOfNeZero ℝ (coordinateVector K c hc p) (coordinateVector_ne_zero K c hc p)
  continuous L d hd := smooth_section_ray_locallyConstant c.source c.open_source
    (coordinateVector K c hc) (coordinateVector_ne_zero K c hc)
    (coordinate_section_smooth K c hc) L d hd

theorem local_exists (p : M) : ∃ L : LocalOrientation S, p ∈ L.domain := by
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  exact ⟨coordinateLocal K c hc, hp⟩

/-- The comparison of two local fields is locally constant on the overlap. -/
def localComparison (L Q : LocalOrientation S) (p : ↥(L.domain ∩ Q.domain)) : Bool :=
  if L.ray ⟨p.val, p.property.1⟩ = Q.ray ⟨p.val, p.property.2⟩ then true else false

theorem localComparison_locallyConstant (L Q : LocalOrientation S) :
    IsLocallyConstant (localComparison L Q) := by
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  apply locallyConstant_of_open_cover _
    (fun c : S.smoothStructure.val => {p : ↥(L.domain ∩ Q.domain) | p.val ∈ c.val.source})
    (fun c => c.val.open_source.preimage continuous_subtype_val)
    (fun p => by
      obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
      exact ⟨⟨c, hc⟩, hp⟩)
  intro c
  let X := {p : ↥(L.domain ∩ Q.domain) | p.val ∈ c.val.source}
  let iL : X → ↥(L.domain ∩ c.val.source) := fun p => ⟨p.val.val, p.val.property.1, p.property⟩
  let iQ : X → ↥(Q.domain ∩ c.val.source) := fun p => ⟨p.val.val, p.val.property.2, p.property⟩
  have hL := (L.continuous K c.val c.property).comp_continuous
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ : Continuous iL)
  have hQ := (Q.continuous K c.val c.property).comp_continuous
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ : Continuous iQ)
  have h := (hL.prodMk hQ).comp (fun z => if z.1 = z.2 then true else false)
  convert h using 1
  funext p
  simp only [Function.comp_apply, localComparison]
  congr 1
  exact propext (Module.Ray.map (determinantCoordinates K c.val c.property
    ⟨p.val.val, p.property⟩)).injective.eq_iff.symm

/-- Every open part of a local sheet is open in the final topology. This
identifies the final topology with the manuscript's local sheet topology. -/
theorem isOpen_lift_image (L : LocalOrientation S) {V : Set L.domain} (hV : IsOpen V) :
    IsOpen (L.lift '' V) := by
  change IsOpen[⨆ Q : LocalOrientation S, TopologicalSpace.coinduced Q.lift inferInstance] _
  rw [isOpen_iSup_iff]
  intro Q
  rw [isOpen_coinduced]
  let iL : ↥(L.domain ∩ Q.domain) → L.domain := fun p => ⟨p.val, p.property.1⟩
  let iQ : ↥(L.domain ∩ Q.domain) → Q.domain := fun p => ⟨p.val, p.property.2⟩
  have ho : IsOpen {p : ↥(L.domain ∩ Q.domain) | localComparison L Q p = true} :=
    (localComparison_locallyConstant L Q).isOpen_fiber true
  have hiL : Continuous iL := continuous_subtype_val.subtype_mk _
  have hiQ : IsOpenMap iQ :=
    (L.isOpen_domain.inter Q.isOpen_domain).isOpenMap_inclusion inter_subset_right
  have he : Q.lift ⁻¹' (L.lift '' V) =
      iQ '' ({p | localComparison L Q p = true} ∩ iL ⁻¹' V) := by
    ext p
    constructor
    · rintro ⟨q, hq, he⟩
      have hpq : q.val = p.val := congrArg Sigma.fst he
      have hpd : p.val ∈ L.domain := hpq ▸ q.property
      refine ⟨⟨p.val, hpd, p.property⟩, ⟨?_, ?_⟩, rfl⟩
      · have hqp : q = ⟨p.val, hpd⟩ := Subtype.ext hpq
        subst q
        have hr : L.ray ⟨p.val, hpd⟩ = Q.ray p := eq_of_heq (Sigma.mk.inj he).2
        simp [localComparison, hr]
      · change (⟨p.val, hpd⟩ : L.domain) ∈ V
        simpa only [← hpq] using hq
    · rintro ⟨q, ⟨he, hq⟩, rfl⟩
      have hr : L.ray ⟨q.val, q.property.1⟩ = Q.ray ⟨q.val, q.property.2⟩ := by
        simpa [localComparison] using he
      exact ⟨iL q, hq, by simp only [LocalOrientation.lift, iL, iQ, hr]⟩
  rw [he]
  exact hiQ _ (ho.inter (hV.preimage hiL))

theorem isOpen_range_lift (L : LocalOrientation S) : IsOpen (range L.lift) := by
  simpa only [image_univ] using isOpen_lift_image L isOpen_univ

theorem lift_injective (L : LocalOrientation S) : Function.Injective L.lift := by
  intro p q h
  exact Subtype.ext (congrArg Sigma.fst h)

/-- Each local continuous choice gives a homeomorphism onto its open sheet. -/
def sheetHomeomorph (L : LocalOrientation S) : L.domain ≃ₜ range L.lift :=
  (Equiv.ofInjective L.lift (lift_injective L)).toHomeomorphOfContinuousOpen
    ((continuous_lift L).subtype_mk _) (IsOpenMap.subtype_mk (fun V hV => isOpen_lift_image L hV) _)

/-- Two local sheets, with the positive reference sheet labeled true. -/
def sheetPair (L : LocalOrientation S) (x : L.domain × Bool) : Space S :=
  if x.2 then L.lift x.1 else (negateLocal L).lift x.1

@[simp] theorem projection_sheetPair (L : LocalOrientation S) (x : L.domain × Bool) :
    projection S (sheetPair L x) = x.1.val := by
  rcases x with ⟨p, b⟩
  cases b <;> rfl

theorem continuous_sheetPair (L : LocalOrientation S) : Continuous (sheetPair L) := by
  apply continuous_prod_of_discrete_right.mpr
  intro b
  cases b
  · exact continuous_lift (negateLocal L)
  · exact continuous_lift L

theorem isOpenMap_sheetPair (L : LocalOrientation S) : IsOpenMap (sheetPair L) := by
  intro V hV
  have he : sheetPair L '' V =
      L.lift '' ((fun p => (p, true)) ⁻¹' V) ∪
      (negateLocal L).lift '' ((fun p => (p, false)) ⁻¹' V) := by
    ext z
    constructor
    · rintro ⟨⟨p, b⟩, hp, rfl⟩
      cases b
      · exact Or.inr ⟨p, hp, rfl⟩
      · exact Or.inl ⟨p, hp, rfl⟩
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · exact ⟨(p, true), hp, rfl⟩
      · exact ⟨(p, false), hp, rfl⟩
  rw [he]
  exact (isOpen_lift_image L (hV.preimage (continuous_id.prodMk continuous_const))).union
    (isOpen_lift_image (negateLocal L) (hV.preimage (continuous_id.prodMk continuous_const)))

def sheetPairEquiv (L : LocalOrientation S) :
    L.domain × Bool ≃ ↥(projection S ⁻¹' L.domain) := by
  let f : L.domain × Bool → ↥(projection S ⁻¹' L.domain) :=
    fun x => ⟨sheetPair L x, by simpa only [mem_preimage, projection_sheetPair] using x.1.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨p, b⟩ ⟨q, d⟩ he
    have hpq : p = q := Subtype.ext (by
      have h := congrArg (fun z => projection S z.val) he
      simpa only [f, projection_sheetPair] using h)
    subst q
    have hr := congrArg Subtype.val he
    cases b <;> cases d
    · rfl
    · have hne : -L.ray p = L.ray p := eq_of_heq (Sigma.mk.inj hr).2
      exact False.elim (Module.Ray.ne_neg_self (L.ray p) hne.symm)
    · have hne : L.ray p = -L.ray p := eq_of_heq (Sigma.mk.inj hr).2
      exact False.elim (Module.Ray.ne_neg_self (L.ray p) hne)
    · rfl
  · rintro ⟨⟨p, r⟩, hp⟩
    rcases determinant_ray_eq_or_neg S p r (L.ray ⟨p, hp⟩) with hr | hr
    · refine ⟨(⟨p, hp⟩, true), ?_⟩
      apply Subtype.ext
      exact congrArg (Sigma.mk p) hr.symm
    · refine ⟨(⟨p, hp⟩, false), ?_⟩
      apply Subtype.ext
      exact congrArg (Sigma.mk p) hr.symm

/-- Actual two-sheet trivialization of the prescribed topology. -/
def sheetPairHomeomorph (L : LocalOrientation S) :
    L.domain × Bool ≃ₜ ↥(projection S ⁻¹' L.domain) :=
  (sheetPairEquiv L).toHomeomorphOfContinuousOpen
    ((continuous_sheetPair L).subtype_mk _) ((isOpenMap_sheetPair L).subtype_mk _)

@[simp] theorem sheetPairHomeomorph_apply (L : LocalOrientation S) (x : L.domain × Bool) :
    (sheetPairHomeomorph L x).val = sheetPair L x := rfl

theorem isCovering_projection : IsCoveringMap (projection S) := by
  intro p
  obtain ⟨L, hp⟩ := local_exists (S := S) p
  have he : IsEvenlyCovered (projection S) p Bool := by
    refine ⟨inferInstance, L.domain, hp, L.isOpen_domain,
      L.isOpen_domain.preimage continuous_projection, (sheetPairHomeomorph L).symm, ?_⟩
    intro z
    have h := congrArg (projection S) (congrArg Subtype.val
      ((sheetPairHomeomorph L).apply_symm_apply z))
    simpa only [sheetPairHomeomorph_apply, projection_sheetPair] using h
  exact he.to_isEvenlyCovered_preimage

theorem countable_fibers (p : M) : (projection S ⁻¹' {p}).Countable := by
  haveI : Countable ↥(projection S ⁻¹' {p}) :=
    (fiberEquiv S p).injective.countable
  exact Set.to_countable _

theorem smoothCovering_localDiffeomorphism (T : SmoothManifold n a (Space S))
    (hT : IsSmoothCovering T S (projection S)) :
    IsLocalDiffeomorphism T S (projection S) := by
  intro z
  obtain ⟨e, hz, he⟩ := hT.1.isLocalHomeomorph z
  have heq : EqOn e (projection S) e.source := fun x _ => congrFun he.symm x
  obtain ⟨hsm, hinv⟩ := CoveringStructure.smooth_branch T S (projection S) hT e heq
  exact ⟨e, hz, heq, hsm, hinv⟩

theorem construction_conditional
    (_determinant_directSum : Specs.SmoothManifolds.Orientations.ProductsAndSigns.determinant_directSumType.{u})
    (_local_differential : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_differentialType.{u})
    (_local_sign : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_signType.{u})
    (_ordinary_product : Specs.SmoothManifolds.Orientations.ProductsAndSigns.ordinary_productType.{u})
    (_product_orientation : Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u})
    (_sign_comp : Specs.SmoothManifolds.Orientations.ProductsAndSigns.sign_compType.{u}) :
    Specs.SmoothManifolds.Orientations.DoubleCover.constructionType.{u} := by
  intro n a M _ S
  have hp := isCovering_projection (S := S)
  obtain ⟨T, hA, hT, hb, hu⟩ := CoveringStructure.exists_canonical_smooth_covering S
    (projection S) hp (Or.inl countable_fibers)
  exact ⟨T.topologicalManifold.hausdorff, T.topologicalManifold.secondCountable,
    T, hA, hT, smoothCovering_localDiffeomorphism T hT, hb, hu⟩

theorem isOpenMap_section (o : Orientation S) : IsOpenMap (sectionOf o) := by
  have hL : IsOpenMap (globalLocal o).lift := fun V hV => isOpen_lift_image (globalLocal o) hV
  exact hL.comp (Homeomorph.Set.univ M).symm.isOpenMap

theorem smooth_deck (T : SmoothManifold n a (Space S))
    (hT : IsSmoothCovering T S (projection S)) : IsSmoothMap T T (deck S) := by
  exact CoveringStructure.smooth_lift T S T (projection S) hT (projection S) (deck S)
    hT.2.1 continuous_deck rfl

theorem smooth_section (T : SmoothManifold n a (Space S))
    (hT : IsSmoothCovering T S (projection S)) (o : Orientation S) :
    IsSmoothMap S T (sectionOf o) := by
  exact CoveringStructure.smooth_lift T S S (projection S) hT id (sectionOf o)
    (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1) (continuous_section o) rfl

/-- The two sheets are globally M itself whenever a global orientation exists. -/
def orientedSumEquiv (o : Orientation S) : (M ⊕ M) ≃ Space S := by
  let f : M ⊕ M → Space S := Sum.elim (sectionOf o) (deck S ∘ sectionOf o)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    have hp := congrArg Sigma.fst h
    cases x with
    | inl p =>
      cases y with
      | inl q => exact congrArg Sum.inl hp
      | inr q =>
        change p = q at hp
        subst q
        exact False.elim (Module.Ray.ne_neg_self (o.val p) (eq_of_heq (Sigma.mk.inj h).2))
    | inr p =>
      cases y with
      | inl q =>
        change p = q at hp
        subst q
        exact False.elim (Module.Ray.ne_neg_self (o.val p) (eq_of_heq (Sigma.mk.inj h).2).symm)
      | inr q => exact congrArg Sum.inr hp
  · rintro ⟨p, r⟩
    rcases determinant_ray_eq_or_neg S p r (o.val p) with hr | hr
    · exact ⟨Sum.inl p, congrArg (Sigma.mk p) hr.symm⟩
    · exact ⟨Sum.inr p, congrArg (Sigma.mk p) hr.symm⟩

def orientedSumHomeomorph (o : Orientation S) : (M ⊕ M) ≃ₜ Space S :=
  (orientedSumEquiv o).toHomeomorphOfContinuousOpen
    ((continuous_section o).sumElim (continuous_deck.comp (continuous_section o)))
    ((isOpenMap_section o).sumElim (deckHomeomorph.isOpenMap.comp (isOpenMap_section o)))

theorem oriented_decomposition_conditional
    (_determinant_directSum : Specs.SmoothManifolds.Orientations.ProductsAndSigns.determinant_directSumType.{u})
    (_local_differential : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_differentialType.{u})
    (_local_sign : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_signType.{u})
    (_ordinary_product : Specs.SmoothManifolds.Orientations.ProductsAndSigns.ordinary_productType.{u})
    (_product_orientation : Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u})
    (_sign_comp : Specs.SmoothManifolds.Orientations.ProductsAndSigns.sign_compType.{u}) :
    Specs.SmoothManifolds.Orientations.DoubleCover.oriented_decompositionType.{u} := by
  intro n a M _ S T hT o
  refine ⟨smooth_section T hT o, ?_, rfl, orientedSumHomeomorph o,
    (fun _ => rfl), (fun _ => rfl), (isOpenMap_section o).isOpen_range,
    (deckHomeomorph.isOpenMap.comp (isOpenMap_section o)).isOpen_range, ?_⟩
  · exact CoveringStructure.smooth_lift T S S (projection S) hT id
      (deck S ∘ sectionOf o) (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1)
      (continuous_deck.comp (continuous_section o)) rfl
  · apply Set.disjoint_left.mpr
    rintro z ⟨p, hp⟩ ⟨q, hq⟩
    have h : orientedSumEquiv o (Sum.inl p) = orientedSumEquiv o (Sum.inr q) := hp.trans hq.symm
    have hbad := (orientedSumEquiv o).injective h
    cases hbad

/-- Restriction changes only the open domain, retaining all coordinate tests. -/
def restrictLocal (L : LocalOrientation S) (U : Set M) (hU : IsOpen U) (hUL : U ⊆ L.domain) :
    LocalOrientation S where
  domain := U
  isOpen_domain := hU
  ray p := L.ray ⟨p.val, hUL p.property⟩
  continuous K c hc := by
    let incl : ↥(U ∩ c.source) → ↥(L.domain ∩ c.source) :=
      fun p => ⟨p.val, hUL p.property.1, p.property.2⟩
    exact (L.continuous K c hc).comp_continuous (f := incl)
      (continuous_subtype_val.subtype_mk _ : Continuous incl)

def signedLocal (L : LocalOrientation S) (b : Bool) : LocalOrientation S where
  domain := L.domain
  isOpen_domain := L.isOpen_domain
  ray p := if b then L.ray p else -L.ray p
  continuous K c hc := by
    cases b
    · exact (negateLocal L).continuous K c hc
    · exact L.continuous K c hc

theorem continuous_of_local_fields (r : RayField S)
    (h : ∀ p, ∃ L : LocalOrientation S, p ∈ L.domain ∧
      ∀ q : L.domain, L.ray q = r q.val) : IsContinuousRayField r := by
  choose L hp he using h
  intro K c hc
  apply locallyConstant_of_open_cover _
    (fun p : M => {q : c.source | q.val ∈ (L p).domain})
    (fun p => (L p).isOpen_domain.preimage continuous_subtype_val)
    (fun p => ⟨p.val, hp p.val⟩)
  intro p
  let incl : {q : c.source | q.val ∈ (L p).domain} → ↥((L p).domain ∩ c.source) :=
    fun q => ⟨q.val.val, q.property, q.val.property⟩
  have hcont := ((L p).continuous K c hc).comp_continuous
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ : Continuous incl)
  convert hcont using 1
  funext q
  exact congrArg (Module.Ray.map (determinantCoordinates K c hc q.val))
    (he p ⟨q.val.val, q.property⟩).symm

theorem lifted_chart_mem (T : SmoothManifold n a (Space S))
    (hT : IsSmoothCovering T S (projection S)) (q : OpenPartialHomeomorph (Space S) M)
    (hq : EqOn q (projection S) q.source) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) : q.trans c ∈ T.smoothStructure.val := by
  obtain ⟨T', hA, hT', _, _⟩ := CoveringStructure.exists_canonical_smooth_covering S
    (projection S) hT.1 (Or.inl countable_fibers)
  have hEq := CoveringStructure.smooth_covering_unique T T' S (projection S) hT hT'
  rw [hEq, hA]
  exact subset_maximalExtension (CoveringStructure.liftedAtlas_isContDiffAtlas _ _
    S.smoothStructure.property.1 hT.1.isLocalHomeomorph) ⟨q, hq, c, hc, rfl⟩

/-- In a lifted chart π has the identity Jacobian, also at boundary points. -/
theorem differential_coordinateVector (T : SmoothManifold n a (Space S))
    (hT : IsSmoothCovering T S (projection S))
    (E : ∀ z : Space S, TangentData.TangentSpace T z ≃ₗ[ℝ] TangentData.TangentSpace S z.1)
    (hE : ∀ z, IsDifferential T S (projection S) z (E z).toLinearMap)
    (K : FiberCoordinates S) (J : FiberCoordinates T)
    (q : OpenPartialHomeomorph (Space S) M) (hq : EqOn q (projection S) q.source)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (z : Space S) (hz : z ∈ (q.trans c).source) (hp : z.1 ∈ c.source) :
    determinantMap n (E z)
      (coordinateVector J (q.trans c) (lifted_chart_mem T hT q hq c hc) ⟨z, hz⟩) =
      coordinateVector K c hc ⟨z.1, hp⟩ := by
  let he := lifted_chart_mem T hT q hq c hc
  have hcoord (v : TangentData.TangentSpace T z) :
      K.equiv c hc z.1 hp ((E z).toLinearMap v) = J.equiv (q.trans c) he z hz v := by
    have h := differential_jacobian T S (projection S) hT.2.1 z (E z).toLinearMap (hE z)
      (q.trans c) c he hc hz hp (J.equiv (q.trans c) he z hz) (K.equiv c hc z.1 hp)
      (J.isCoordinates _ _ _ _) (K.isCoordinates _ _ _ _)
      univ id isOpen_univ (mem_univ _) contDiffOn_id
      (CoveringStructure.lifted_chart_germ (projection S) hq c hz.1) v
    change K.equiv c hc z.1 hp ((E z).toLinearMap v) = _
    convert h using 1 <;> simp only [fderiv_id, ContinuousLinearMap.id_apply]
  change exteriorPower.map n _ (exteriorPower.ιMulti ℝ n _) = exteriorPower.ιMulti ℝ n _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  apply (K.equiv c hc z.1 hp).injective
  change K.equiv c hc z.1 hp ((E z).toLinearMap ((J.equiv (q.trans c) he z hz).symm _)) = _
  rw [hcoord, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Pulling back the tautological ray through the actual dπ is continuous.
On each open sheet it is precisely a signed coordinate wedge in a lifted chart. -/
theorem tautological_continuous (T : SmoothManifold n a (Space S))
    (hT : IsSmoothCovering T S (projection S))
    (E : ∀ z : Space S, TangentData.TangentSpace T z ≃ₗ[ℝ] TangentData.TangentSpace S z.1)
    (hE : ∀ z, IsDifferential T S (projection S) z (E z).toLinearMap) :
    IsContinuousRayField (fun z => (Module.Ray.map (determinantMap
      (V := TangentData.TangentSpace T z) (W := TangentData.TangentSpace S z.1) n (E z))).symm z.2) := by
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨J⟩ := TangentBundle.fiberCoordinates_exists T
  apply continuous_of_local_fields (S := T)
  intro z
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 z.1
  let L := coordinateLocal K c hc
  obtain ⟨b, hb⟩ : ∃ b : Bool, z ∈ range (signedLocal L b).lift := by
    rcases determinant_ray_eq_or_neg S z.1 z.2 (L.ray ⟨z.1, hp⟩) with hr | hr
    · exact ⟨true, ⟨⟨z.1, hp⟩, Sigma.ext rfl (heq_of_eq hr.symm)⟩⟩
    · exact ⟨false, ⟨⟨z.1, hp⟩, Sigma.ext rfl (heq_of_eq hr.symm)⟩⟩
  obtain ⟨q, hzq, hqe, _, _⟩ := (smoothCovering_localDiffeomorphism (S := S) T hT) z
  let e := q.trans c
  have he := lifted_chart_mem (S := S) T hT q hqe c hc
  have hze : z ∈ e.source := ⟨hzq, by change q z ∈ c.source; rw [hqe hzq]; exact hp⟩
  let U : Set (Space S) := range (signedLocal L b).lift ∩ e.source
  let H := signedLocal (coordinateLocal J e he) b
  refine ⟨restrictLocal H U ((isOpen_range_lift (signedLocal L b)).inter e.open_source)
    (by intro y hy; exact hy.2), ⟨hb, hze⟩, ?_⟩
  intro y
  apply (Module.Ray.map (determinantMap
    (V := TangentData.TangentSpace T y.val)
    (W := TangentData.TangentSpace S y.val.1) n (E y.val))).eq_symm_apply.mpr
  let p := Classical.choose y.property.1
  have hyp := Classical.choose_spec y.property.1
  have hpy : p.val = y.val.1 := congrArg Sigma.fst hyp
  have hpc : y.val.1 ∈ c.source := hpy ▸ p.property
  have hr : (signedLocal L b).ray ⟨y.val.1, hpc⟩ = y.val.2 := by
    have hpp : p = ⟨y.val.1, hpc⟩ := Subtype.ext hpy
    have hyp' := (congrArg (signedLocal L b).lift hpp).symm.trans hyp
    exact eq_of_heq (Sigma.mk.inj hyp').2
  change Module.Ray.map (determinantMap (V := TangentData.TangentSpace T y.val) (W := TangentData.TangentSpace S y.val.1) n (E y.val))
    (if b then (coordinateLocal J e he).ray ⟨y.val, y.property.2⟩
      else -(coordinateLocal J e he).ray ⟨y.val, y.property.2⟩) = y.val.2
  refine Eq.trans ?_ hr
  have hd := differential_coordinateVector (S := S) T hT E hE K J q hqe c hc y.val y.property.2 hpc
  have hpos : Module.Ray.map (determinantMap (V := TangentData.TangentSpace T y.val) (W := TangentData.TangentSpace S y.val.1) n (E y.val))
      ((coordinateLocal J e he).ray ⟨y.val, y.property.2⟩) = L.ray ⟨y.val.1, hpc⟩ := by
    dsimp only [coordinateLocal, L]
    rw [Module.Ray.map_apply]
    congr 1
  cases b
  · simpa only [signedLocal, Bool.false_eq_true, ↓reduceIte, Module.Ray.map_neg]
      using congrArg Neg.neg hpos
  · exact hpos


theorem canonical_orientation_conditional
    (_determinant_directSum : Specs.SmoothManifolds.Orientations.ProductsAndSigns.determinant_directSumType.{u})
    (_local_differential : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_differentialType.{u})
    (_local_sign : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_signType.{u})
    (_ordinary_product : Specs.SmoothManifolds.Orientations.ProductsAndSigns.ordinary_productType.{u})
    (_product_orientation : Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u})
    (_sign_comp : Specs.SmoothManifolds.Orientations.ProductsAndSigns.sign_compType.{u}) :
    Specs.SmoothManifolds.Orientations.DoubleCover.canonical_orientationType.{u} := by
  intro n a M _ S T hT
  obtain ⟨E, hE, huniq⟩ := _local_differential T S (projection S)
    (smoothCovering_localDiffeomorphism (S := S) T hT)
  let o : Orientation T := ⟨fun z => (Module.Ray.map (determinantMap (V := TangentData.TangentSpace T z)
      (W := TangentData.TangentSpace S z.1) n (E z))).symm z.2,
    tautological_continuous (S := S) T hT E hE⟩
  refine ⟨o, ?_, ?_⟩
  · intro F hF z
    have hFE := huniq F hF
    subst F
    exact (Module.Ray.map (determinantMap (V := TangentData.TangentSpace T z)
      (W := TangentData.TangentSpace S z.1) n (E z))).apply_symm_apply z.2
  · intro o' ho'
    apply Subtype.ext
    funext z
    apply (Module.Ray.map (determinantMap (V := TangentData.TangentSpace T z)
      (W := TangentData.TangentSpace S z.1) n (E z))).injective
    exact (ho' E hE z).trans ((Module.Ray.map (determinantMap (V := TangentData.TangentSpace T z)
      (W := TangentData.TangentSpace S z.1) n (E z))).apply_symm_apply z.2).symm

/-- Functoriality of ray transport, for actual exterior-power maps. -/
theorem determinant_ray_comp {V W Q : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup Q] [Module ℝ Q]
    (m : ℕ) (A : V ≃ₗ[ℝ] W) (B : W ≃ₗ[ℝ] Q) (C : V ≃ₗ[ℝ] Q)
    (hC : B.toLinearMap.comp A.toLinearMap = C.toLinearMap) (r : Module.Ray ℝ (⋀[ℝ]^m V)) :
    Module.Ray.map (determinantMap m B) (Module.Ray.map (determinantMap m A) r) =
      Module.Ray.map (determinantMap m C) r := by
  induction r using Module.Ray.ind with | h v hv =>
  simp only [Module.Ray.map_apply]
  apply (ray_eq_iff _ _).mpr
  have he : determinantMap m B (determinantMap m A v) = determinantMap m C v := by
    change exteriorPower.map m B.toLinearMap (exteriorPower.map m A.toLinearMap v) =
      exteriorPower.map m C.toLinearMap v
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hC]
  exact he ▸ SameRay.rfl

section
-- Keep transport maps opaque here so elaboration uses their declared types
-- rather than expanding the exterior-algebra quotient construction.
attribute [local irreducible] OrientationProductData.determinantMap Module.Ray.map

theorem deck_conditional
    (_determinant_directSum : Specs.SmoothManifolds.Orientations.ProductsAndSigns.determinant_directSumType.{u})
    (_local_differential : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_differentialType.{u})
    (_local_sign : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_signType.{u})
    (_ordinary_product : Specs.SmoothManifolds.Orientations.ProductsAndSigns.ordinary_productType.{u})
    (_product_orientation : Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u})
    (_sign_comp : Specs.SmoothManifolds.Orientations.ProductsAndSigns.sign_compType.{u}) :
    Specs.SmoothManifolds.Orientations.DoubleCover.deckType.{u} := by
  intro n a M _ S T hT
  refine ⟨deck_involutive, deck_fixedPointFree, rfl, smooth_deck (S := S) T hT, ?_⟩
  intro o ho F hF z
  obtain ⟨E, hE, _⟩ := _local_differential T S (projection S)
    (smoothCovering_localDiffeomorphism (S := S) T hT)
  have hcomp := differential_comp T T S (deck S) (projection S) (smooth_deck (S := S) T hT) hT.2.1
    z (F z).toLinearMap (E (deck S z)).toLinearMap (hF z) (hE (deck S z))
  obtain ⟨L, _, hu⟩ := differential_exists T S (projection S) hT.2.1 z
  have heq : (E (deck S z)).toLinearMap.comp (F z).toLinearMap = (E z).toLinearMap :=
    (hu _ hcomp).trans (hu _ (hE z)).symm
  let A : DeterminantRay T z ≃ DeterminantRay T (deck S z) :=
    Module.Ray.map (determinantMap (V := TangentData.TangentSpace T z)
      (W := TangentData.TangentSpace T (deck S z)) n (F z))
  let B : DeterminantRay T (deck S z) ≃ DeterminantRay S z.1 :=
    Module.Ray.map (determinantMap (V := TangentData.TangentSpace T (deck S z))
      (W := TangentData.TangentSpace S z.1) n (E (deck S z)))
  let C : DeterminantRay T z ≃ DeterminantRay S z.1 :=
    Module.Ray.map (determinantMap (V := TangentData.TangentSpace T z)
      (W := TangentData.TangentSpace S z.1) n (E z))
  change A (o.val z) = -o.val (deck S z)
  have htrans : B (A (o.val z)) = C (o.val z) :=
    determinant_ray_comp (V := TangentData.TangentSpace T z)
      (W := TangentData.TangentSpace T (deck S z))
      (Q := TangentData.TangentSpace S z.1)
      n (F z) (E (deck S z)) (E z) heq (o.val z)
  have hz : C (o.val z) = z.2 := ho E hE z
  have hd : B (o.val (deck S z)) = -z.2 := ho E hE (deck S z)
  apply B.injective
  calc
    B (A (o.val z)) = z.2 := htrans.trans hz
    _ = -(-z.2) := (neg_neg z.2).symm
    _ = -(B (o.val (deck S z))) := congrArg Neg.neg hd.symm
    _ = B (-o.val (deck S z)) := (Module.Ray.map_neg _ _).symm

end

/-- The final sheet topology detects exactly the original continuous ray fields. -/
theorem rayField_continuous_of_section (r : RayField S)
    (hs : Continuous (fun p => (⟨p, r p⟩ : Space S))) : IsContinuousRayField r := by
  apply continuous_of_local_fields
  intro p
  obtain ⟨L, hp⟩ := local_exists (S := S) p
  obtain ⟨b, hb⟩ : ∃ b : Bool, (⟨p, r p⟩ : Space S) ∈ range (signedLocal L b).lift := by
    rcases determinant_ray_eq_or_neg S p (r p) (L.ray ⟨p, hp⟩) with hr | hr
    · exact ⟨true, ⟨⟨p, hp⟩, congrArg (Sigma.mk p) hr.symm⟩⟩
    · exact ⟨false, ⟨⟨p, hp⟩, congrArg (Sigma.mk p) hr.symm⟩⟩
  let Q := signedLocal L b
  let U : Set M := (fun p => (⟨p, r p⟩ : Space S)) ⁻¹' range Q.lift
  have hU : IsOpen U := (isOpen_range_lift Q).preimage hs
  have hUL : U ⊆ Q.domain := by
    intro x hx
    obtain ⟨q, hq⟩ := hx
    have h := congrArg Sigma.fst hq
    change q.val = x at h
    exact h ▸ q.property
  refine ⟨restrictLocal Q U hU hUL, hb, ?_⟩
  intro q
  obtain ⟨t, ht⟩ := q.property
  have hbase : t.val = q.val := congrArg Sigma.fst ht
  have hsub : t = ⟨q.val, hUL q.property⟩ := Subtype.ext hbase
  subst t
  exact eq_of_heq (Sigma.mk.inj ht).2

theorem orientation_of_section (s : M → Space S) (hs : Continuous s)
    (hp : projection S ∘ s = id) : Nonempty (Orientation S) := by
  have hx (p : M) : ∃ r : DeterminantRay S p, (⟨p, r⟩ : Space S) = s p := by
    have he := congrFun hp p
    rcases hz : s p with ⟨q, r⟩
    have hqp : q = p := by simpa only [Function.comp_apply, hz, projection, id_eq] using he
    subst q
    exact ⟨r, rfl⟩
  choose r hr using hx
  have hc : Continuous (fun p => (⟨p, r p⟩ : Space S)) := by
    convert hs using 1
    exact funext hr
  exact ⟨⟨r, rayField_continuous_of_section r hc⟩⟩

theorem fiber_eq_or_deck (x y : Space S) (h : projection S x = projection S y) :
    x = y ∨ x = deck S y := by
  rcases x with ⟨p, r⟩
  rcases y with ⟨q, s⟩
  change p = q at h
  subst q
  rcases determinant_ray_eq_or_neg S p r s with h | h
  · exact Or.inl (congrArg (Sigma.mk p) h)
  · exact Or.inr (congrArg (Sigma.mk p) h)

theorem component_projection_surjective [ConnectedSpace M]
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (z : Space S) : Function.Surjective
      (fun x : connectedComponent z => projection S x.val) := by
  letI := TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  letI : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  intro p
  obtain ⟨x, hx⟩ := hT.1.comp_subtypeVal_pathComponent_surjective z p
  exact ⟨⟨x.val, pathComponent_subset_component z x.property⟩, hx⟩

/-- A disconnected two-sheet orientation cover has a component projecting
bijectively to M. Its continuous inverse gives the required orientation. -/
theorem orientation_of_not_connected [ConnectedSpace M]
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (hn : ¬ ConnectedSpace (Space S)) : Nonempty (Orientation S) := by
  haveI : Nonempty (Space S) := by
    let p : M := Classical.choice inferInstance
    exact ⟨((fiberEquiv S p).symm true).val⟩
  have hnon : ¬ PreconnectedSpace (Space S) := by
    intro h
    exact hn { toPreconnectedSpace := h, toNonempty := inferInstance }
  have hfail : ¬ ∀ x : Space S, connectedComponent x = univ :=
    fun h => hnon (preconnectedSpace_iff_connectedComponent.mpr h)
  obtain ⟨x, hx⟩ := not_forall.mp hfail
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).mp hx
  have hdisj : Disjoint (connectedComponent x) (connectedComponent y) :=
    connectedComponent_disjoint (by
      intro he
      apply hy
      rw [he]
      exact mem_connectedComponent)
  have hinj : Function.Injective (fun v : connectedComponent x => projection S v.val) := by
    intro v w hvw
    by_contra hne
    have hvne : v.val ≠ w.val := fun h => hne (Subtype.ext h)
    have hvwd : v.val = deck S w.val := (fiber_eq_or_deck v.val w.val hvw).resolve_left hvne
    obtain ⟨d, hd⟩ := component_projection_surjective T hT y (projection S v.val)
    rcases fiber_eq_or_deck d.val v.val hd with h | h
    · exact Set.disjoint_left.mp hdisj v.property (h ▸ d.property)
    · have h' : d.val = w.val := by rw [h, hvwd, deck_involutive]
      exact Set.disjoint_left.mp hdisj w.property (h' ▸ d.property)
  let e : connectedComponent x ≃ M := Equiv.ofBijective _
    ⟨hinj, component_projection_surjective T hT x⟩
  let H : connectedComponent x ≃ₜ M := e.toHomeomorphOfContinuousOpen
    (continuous_projection.comp continuous_subtype_val)
    (hT.1.isOpenMap.comp (TopologicalManifold.isOpen_connectedComponent T.topologicalManifold x).isOpenMap_subtype_val)
  exact orientation_of_section (fun p => (H.symm p).val)
    (continuous_subtype_val.comp H.symm.continuous) (funext H.apply_symm_apply)

theorem section_ranges_disjoint (o : Orientation S) :
    Disjoint (range (sectionOf o)) (range (deck S ∘ sectionOf o)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨p, hp⟩ ⟨q, hq⟩
  have h : orientedSumEquiv o (Sum.inl p) = orientedSumEquiv o (Sum.inr q) := hp.trans hq.symm
  have hbad := (orientedSumEquiv o).injective h
  cases hbad

theorem section_ranges_compl (o : Orientation S) :
    (range (sectionOf o))ᶜ = range (deck S ∘ sectionOf o) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := (orientedSumEquiv o).surjective z
    cases x with
    | inl p => exact False.elim (hz ⟨p, rfl⟩)
    | inr p => exact ⟨p, rfl⟩
  · intro hz hp
    exact Set.disjoint_left.mp (section_ranges_disjoint o) hp hz

theorem components_two_of_orientation [ConnectedSpace M] (o : Orientation S) :
    Nonempty (ConnectedComponents (Space S) ≃ Bool) := by
  let A := range (sectionOf o)
  have hA : IsClopen A := ⟨by
    rw [← isOpen_compl_iff, section_ranges_compl o]
    exact (deckHomeomorph.isOpenMap.comp (isOpenMap_section o)).isOpen_range,
    (isOpenMap_section o).isOpen_range⟩
  let U : Bool → Set (Space S) := fun b => if b then A else Aᶜ
  have hcl : ∀ b, IsClopen (U b) := by
    intro b
    cases b
    · exact hA.compl
    · exact hA
  have hdis : Pairwise (fun b d => Disjoint (U b) (U d)) := by
    intro b d hbd
    cases b <;> cases d
    · exact False.elim (hbd rfl)
    · exact disjoint_compl_left
    · exact disjoint_compl_right
    · exact False.elim (hbd rfl)
  have hcov : ⋃ b, U b = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases hx : x ∈ A
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  have hc : ∀ b, IsConnected (U b) := by
    intro b
    cases b
    · change IsConnected Aᶜ
      rw [show Aᶜ = range (deck S ∘ sectionOf o) from section_ranges_compl o]
      exact isConnected_range (continuous_deck.comp (continuous_section o))
    · exact isConnected_range (continuous_section o)
  exact ⟨ConnectedComponents.equivOfIsClopenOfIsConnected hcl hdis hcov hc⟩

theorem not_connected_of_two_components
    (he : Nonempty (ConnectedComponents (Space S) ≃ Bool)) : ¬ ConnectedSpace (Space S) := by
  intro h
  letI := h
  obtain ⟨e⟩ := he
  have hbad := congrArg e (Subsingleton.elim (e.symm true) (e.symm false))
  simpa only [e.apply_symm_apply, Bool.true_eq_false] using hbad

theorem connected_classification_conditional
    (_determinant_directSum : Specs.SmoothManifolds.Orientations.ProductsAndSigns.determinant_directSumType.{u})
    (_local_differential : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_differentialType.{u})
    (_local_sign : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_signType.{u})
    (_ordinary_product : Specs.SmoothManifolds.Orientations.ProductsAndSigns.ordinary_productType.{u})
    (_product_orientation : Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u})
    (_sign_comp : Specs.SmoothManifolds.Orientations.ProductsAndSigns.sign_compType.{u}) :
    Specs.SmoothManifolds.Orientations.DoubleCover.connected_classificationType.{u} := by
  intro n a M _ _ S
  obtain ⟨T, _, hT, _, _⟩ := CoveringStructure.exists_canonical_smooth_covering S
    (projection S) isCovering_projection (Or.inl countable_fibers)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro he
    exact orientation_of_not_connected T hT (not_connected_of_two_components he)
  · rintro ⟨o⟩
    exact components_two_of_orientation o
  · intro hc ho
    obtain ⟨o⟩ := ho
    exact not_connected_of_two_components (components_two_of_orientation o) hc
  · intro ho
    by_contra hn
    exact ho (orientation_of_not_connected T hT hn)

/-- Public conditional helper: original target, with the exact ordered pending
premises. None of the pending implementations is imported. -/
theorem two_sheets_conditional
    (_determinant_directSum : Specs.SmoothManifolds.Orientations.ProductsAndSigns.determinant_directSumType.{u})
    (_local_differential : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_differentialType.{u})
    (_local_sign : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_signType.{u})
    (_ordinary_product : Specs.SmoothManifolds.Orientations.ProductsAndSigns.ordinary_productType.{u})
    (_product_orientation : Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u})
    (_sign_comp : Specs.SmoothManifolds.Orientations.ProductsAndSigns.sign_compType.{u}) :
    Specs.SmoothManifolds.Orientations.DoubleCover.two_sheetsType.{u} := by
  intro n a M _ S p
  exact ⟨fiberEquiv S p⟩

end SmoothManifolds.OrientationCover

universe v8_closure_15c81c9bba5b0aea_u0
theorem _root_.«SmoothManifolds».«OrientationCover».«canonical_orientation» : _root_.«Specs».«SmoothManifolds».«Orientations».«DoubleCover».«canonical_orientationType».{v8_closure_15c81c9bba5b0aea_u0} :=
  @_root_.«SmoothManifolds».«OrientationCover».«canonical_orientation_conditional».{v8_closure_15c81c9bba5b0aea_u0} (@_root_.«SmoothManifolds».«OrientationProducts».«determinant_directSum».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_differential».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_sign».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«ordinary_product».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«product_orientation».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«sign_comp».{v8_closure_15c81c9bba5b0aea_u0})
theorem _root_.«SmoothManifolds».«OrientationCover».«connected_classification» : _root_.«Specs».«SmoothManifolds».«Orientations».«DoubleCover».«connected_classificationType».{v8_closure_15c81c9bba5b0aea_u0} :=
  @_root_.«SmoothManifolds».«OrientationCover».«connected_classification_conditional».{v8_closure_15c81c9bba5b0aea_u0} (@_root_.«SmoothManifolds».«OrientationProducts».«determinant_directSum».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_differential».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_sign».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«ordinary_product».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«product_orientation».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«sign_comp».{v8_closure_15c81c9bba5b0aea_u0})
theorem _root_.«SmoothManifolds».«OrientationCover».«construction» : _root_.«Specs».«SmoothManifolds».«Orientations».«DoubleCover».«constructionType».{v8_closure_15c81c9bba5b0aea_u0} :=
  @_root_.«SmoothManifolds».«OrientationCover».«construction_conditional».{v8_closure_15c81c9bba5b0aea_u0} (@_root_.«SmoothManifolds».«OrientationProducts».«determinant_directSum».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_differential».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_sign».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«ordinary_product».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«product_orientation».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«sign_comp».{v8_closure_15c81c9bba5b0aea_u0})
theorem _root_.«SmoothManifolds».«OrientationCover».«deck» : _root_.«Specs».«SmoothManifolds».«Orientations».«DoubleCover».«deckType».{v8_closure_15c81c9bba5b0aea_u0} :=
  @_root_.«SmoothManifolds».«OrientationCover».«deck_conditional».{v8_closure_15c81c9bba5b0aea_u0} (@_root_.«SmoothManifolds».«OrientationProducts».«determinant_directSum».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_differential».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_sign».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«ordinary_product».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«product_orientation».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«sign_comp».{v8_closure_15c81c9bba5b0aea_u0})
theorem _root_.«SmoothManifolds».«OrientationCover».«oriented_decomposition» : _root_.«Specs».«SmoothManifolds».«Orientations».«DoubleCover».«oriented_decompositionType».{v8_closure_15c81c9bba5b0aea_u0} :=
  @_root_.«SmoothManifolds».«OrientationCover».«oriented_decomposition_conditional».{v8_closure_15c81c9bba5b0aea_u0} (@_root_.«SmoothManifolds».«OrientationProducts».«determinant_directSum».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_differential».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_sign».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«ordinary_product».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«product_orientation».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«sign_comp».{v8_closure_15c81c9bba5b0aea_u0})
theorem _root_.«SmoothManifolds».«OrientationCover».«two_sheets» : _root_.«Specs».«SmoothManifolds».«Orientations».«DoubleCover».«two_sheetsType».{v8_closure_15c81c9bba5b0aea_u0} :=
  @_root_.«SmoothManifolds».«OrientationCover».«two_sheets_conditional».{v8_closure_15c81c9bba5b0aea_u0} (@_root_.«SmoothManifolds».«OrientationProducts».«determinant_directSum».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_differential».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«local_sign».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«ordinary_product».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«product_orientation».{v8_closure_15c81c9bba5b0aea_u0}) (@_root_.«SmoothManifolds».«OrientationProducts».«sign_comp».{v8_closure_15c81c9bba5b0aea_u0})
