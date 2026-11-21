import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsCohomology
import MathGenome.Internal.AlgebraCore.P103.Ch02.Projective
import MathGenome.Internal.AlgebraCore.P103.Ch11.DimensionShifting

namespace P103.Ch11.UniversalCoefficientsCohomology
open CategoryTheory
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.Horseshoe
open P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.UniversalCoefficientsCohomology
noncomputable section
set_option maxHeartbeats 800000
universe u v w
variable {R : Type u} [Ring R]

/-- The first basic short exact sequence, including the degree-zero case. -/
theorem cycles_boundary_exact (C : Ordinary.{u,v} R) (n : ℕ) :
    Function.Exact (cycles C n).subtype (boundaryProjection C n) := by
  cases n with
  | zero =>
    intro x
    constructor
    · intro _
      refine ⟨⟨x, ?_⟩, rfl⟩
      change (C.d 0 ((ComplexShape.down ℕ).next 0)).hom x = 0
      rw [ChainComplex.next_nat_zero]
      rw [C.shape 0 0 (by decide)]
      rfl
    · intro _
      rfl
  | succ n =>
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change (C.d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom x = 0
      rw [ChainComplex.next_nat_succ]
      exact congrArg Subtype.val hx
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      have hz := z.property
      change (C.d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom z.val = 0 at hz
      rw [ChainComplex.next_nat_succ] at hz
      exact hz

theorem boundaryProjection_surjective (C : Ordinary.{u,v} R) (n : ℕ) :
    Function.Surjective (boundaryProjection C n) := by
  cases n with
  | zero =>
    intro x
    refine ⟨0, ?_⟩
    apply Subtype.ext
    exact (show x.val = 0 from x.property).symm
  | succ n =>
    intro x
    have hx := x.property
    change ∃ y, (C.d ((ComplexShape.down ℕ).prev n) n).hom y = x.val at hx
    rw [ChainComplex.prev] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩

/-- Projectivity of the boundary at zero is the projectivity of the zero module. -/
theorem previousBoundary_projective (C : Ordinary.{u,v} R)
    (hC : ProjectiveTermsAndBoundaries C) (n : ℕ) :
    Module.Projective R (previousBoundary C n) := by
  cases n with
  | zero =>
      change Module.Projective R (⊥ : Submodule R (C.X 0))
      infer_instance
  | succ n =>
      exact hC.2 n

theorem projective_cycles : projective_cyclesType.{u,v} := by
  intro R _ C hC n
  letI := hC.1 n
  letI := previousBoundary_projective C hC n
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (boundaryProjection C n) LinearMap.id (boundaryProjection_surjective C n)
  refine ⟨⟨s, hs⟩, ?_⟩
  obtain ⟨r, hr⟩ :=
    (P103.Ch01.SplitSequences.section_iff_retraction R (cycles C n) (C.X n)
      (previousBoundary C n) (cycles C n).subtype (boundaryProjection C n)
      Subtype.val_injective (boundaryProjection_surjective C n)
      (cycles_boundary_exact C n)).mp ⟨s, hs⟩
  exact Module.Projective.of_split (cycles C n).subtype r hr

/-- A cocycle annihilates every incoming boundary. -/
theorem cocycle_kills_boundary (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ)
    (z : cycles (homComplex C M) n)
    (b : boundaries C n) : homTerm C M n z.val b.val = 0 := by
  have hb := b.property
  change ∃ y, (C.d ((ComplexShape.down ℕ).prev n) n).hom y = b.val at hb
  rw [ChainComplex.prev] at hb
  obtain ⟨y, hy⟩ := hb
  have hz := z.property
  change ((homComplex C M).d n
    ((ComplexShape.up ℕ).next n)).hom z.val = 0 at hz
  rw [CochainComplex.next] at hz
  change (homTerm C M n z.val).comp (C.d (n+1) n).hom = 0 at hz
  rw [← hy]
  exact LinearMap.congr_fun hz y

/-- First restrict to Z, then descend along Z ↠ H. -/
def cocycleOnHomology (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ)
    (z : cycles (homComplex C M) n) :
    Homology C n →ₗ[R] M :=
  (cycleBoundaries C n).liftQ
    ((homTerm C M n z.val).comp (cycles C n).subtype) (by
      intro x hx
      exact cocycle_kills_boundary C M n z ⟨x.val, hx⟩)

def cocycleRestriction (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :
    cycles (homComplex C M) n →ₗ[ℤ]
      (Homology C n →ₗ[R] M) :=
  AddMonoidHom.toIntLinearMap {
    toFun := cocycleOnHomology C M n
    map_zero' := by
      apply (cycleBoundaries C n).quot_hom_ext
      intro x
      rfl
    map_add' := by
      intro z z'
      apply (cycleBoundaries C n).quot_hom_ext
      intro x
      rfl }

theorem coboundary_restriction_zero (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ)
    (z : cycles (homComplex C M) n)
    (hz : z ∈ cycleBoundaries (homComplex C M) n) :
    cocycleRestriction C M n z = 0 := by
  apply (cycleBoundaries C n).quot_hom_ext
  intro x
  change ∃ h, ((homComplex C M).d
    ((ComplexShape.up ℕ).prev n) n).hom h = z.val at hz
  cases n with
  | zero =>
    rw [CochainComplex.prev_nat_zero] at hz
    obtain ⟨h, hh⟩ := hz
    have hd := (homComplex C M).shape 0 0 (by decide)
    rw [hd] at hh
    have he : z = 0 := Subtype.ext hh.symm
    rw [he, map_zero]
  | succ n =>
    rw [CochainComplex.prev_nat_succ] at hz
    obtain ⟨h, hh⟩ := hz
    change (homTerm C M (n+1) z.val) x.val = 0
    rw [← hh]
    change (homTerm C M n h) ((C.d (n+1) n).hom x.val) = 0
    have hx := x.property
    change (C.d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom x.val = 0 at hx
    rw [ChainComplex.next_nat_succ] at hx
    rw [hx, map_zero]

/-- The right arrow in universal coefficients, defined on the actual quotient. -/
def cohomologyRestriction (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :
    Homology (homComplex C M) n →ₗ[ℤ]
      (Homology C n →ₗ[R] M) :=
  (cycleBoundaries (homComplex C M) n).liftQ
    (cocycleRestriction C M n) (fun z hz => coboundary_restriction_zero C M n z hz)

theorem cohomologyRestriction_formula (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :
    IsRestriction C M n (cohomologyRestriction C M n) := by
  intro z x
  rfl

/-- The representative formula determines the right arrow uniquely. -/
theorem restriction_unique (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ)
    (β : Homology (homComplex C M) n →ₗ[ℤ]
      (Homology C n →ₗ[R] M)) (hβ : IsRestriction C M n β) :
    β = cohomologyRestriction C M n := by
  apply (cycleBoundaries (homComplex C M) n).quot_hom_ext
  intro z
  apply (cycleBoundaries C n).quot_hom_ext
  intro x
  exact hβ z x

theorem homologyClass_boundary (C : Ordinary.{u,v} R) (n : ℕ) (b : boundaries C n) :
    homologyClass C n (j C n b) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero (cycleBoundaries C n)).mpr b.property

theorem cycle_retraction (C : Ordinary.{u,v} R) (hC : ProjectiveTermsAndBoundaries C) (n : ℕ) :
    ∃ r : C.X n →ₗ[R] cycles C n, r.comp (cycles C n).subtype = LinearMap.id := by
  exact (P103.Ch01.SplitSequences.section_iff_retraction R (cycles C n) (C.X n)
    (previousBoundary C n) (cycles C n).subtype (boundaryProjection C n)
    Subtype.val_injective (boundaryProjection_surjective C n)
    (cycles_boundary_exact C n)).mp (projective_cycles C hC n).1

/-- A split inclusion Zₙ → Cₙ extends a functional on Hₙ to a cocycle. -/
theorem cohomologyRestriction_surjective (C : Ordinary.{u,v} R)
    (hC : ProjectiveTermsAndBoundaries C) (M : ModuleCat.{w} R) (n : ℕ) :
    Function.Surjective (cohomologyRestriction C M n) := by
  obtain ⟨r, hr⟩ := cycle_retraction C hC n
  intro h
  let φ : C.X n →ₗ[R] M := h.comp ((homologyClass C n).comp r)
  have hφ : φ ∈ cycles (homComplex C M) n := by
    change ((homComplex C M).d n ((ComplexShape.up ℕ).next n)).hom φ = 0
    rw [CochainComplex.next]
    change φ.comp (C.d (n+1) n).hom = 0
    ext y
    let b : boundaries C n := incomingProjection C n y
    have hrb : r b.val = j C n b := LinearMap.congr_fun hr (j C n b)
    change h (homologyClass C n (r b.val)) = 0
    rw [hrb, homologyClass_boundary, map_zero]
  refine ⟨homologyClass _ n ⟨φ,hφ⟩, ?_⟩
  apply (cycleBoundaries C n).quot_hom_ext
  intro x
  change h (homologyClass C n (r x.val)) = h (homologyClass C n x)
  rw [show r x.val = x from LinearMap.congr_fun hr x]

/-- Naturality of restriction needs no projectivity assumptions. -/
theorem restriction_natural {C D : Ordinary.{u,v} R} (f : D ⟶ C)
    (M M' : ModuleCat.{w} R) (g : M ⟶ M') (n : ℕ)
    (β : Homology (homComplex C M) n →ₗ[ℤ] (Homology C n →ₗ[R] M))
    (β' : Homology (homComplex D M') n →ₗ[ℤ] (Homology D n →ₗ[R] M'))
    (hβ : IsRestriction C M n β) (hβ' : IsRestriction D M' n β')
    (x : Homology (homComplex C M) n) :
    β' (homologyMap (homPreMap f M ≫ homPostMap D g.hom) n x) =
      g.hom.comp ((β x).comp (homologyMap f n)) := by
  obtain ⟨z,rfl⟩ := (cycleBoundaries (homComplex C M) n).mkQ_surjective x
  apply (cycleBoundaries D n).quot_hom_ext
  intro y
  change β' (homologyClass _ n
    (cyclesMap (homPreMap f M ≫ homPostMap D g.hom) n z)) (homologyClass D n y) =
      g.hom (β (homologyClass _ n z) (homologyClass C n (cyclesMap f n y)))
  rw [hβ', hβ]
  rfl

theorem degree_zero_natural : degree_zero_naturalType.{u,v,w} := by
  intro R _ C D f M M' g β β' hβ hβ' x
  exact restriction_natural f M M' g 0 β β' hβ hβ' x

/-- The inclusion Z₀ → C₀ is an isomorphism because the outgoing d₀ is zero. -/
def toZeroCycles (C : Ordinary.{u,v} R) : C.X 0 →ₗ[R] cycles C 0 :=
  (LinearMap.id : C.X 0 →ₗ[R] C.X 0).codRestrict _ (by
    intro x
    change (C.d 0 ((ComplexShape.down ℕ).next 0)).hom x = 0
    rw [ChainComplex.next_nat_zero, C.shape 0 0 (by decide)]
    rfl)

theorem degree_zero : degree_zeroType.{u,v,w} := by
  intro R _ C M
  let β := cohomologyRestriction C M 0
  have hi : Function.Injective β := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    obtain ⟨z,rfl⟩ := (cycleBoundaries (homComplex C M) 0).mkQ_surjective x
    have hz : z = 0 := by
      apply Subtype.ext
      apply LinearMap.ext
      intro y
      have hh := LinearMap.congr_fun hx (homologyClass C 0 (toZeroCycles C y))
      exact hh
    rw [hz, map_zero]
  have hs : Function.Surjective β := by
    intro h
    let φ : C.X 0 →ₗ[R] M := h.comp ((homologyClass C 0).comp (toZeroCycles C))
    have hφ : φ ∈ cycles (homComplex C M) 0 := by
      change ((homComplex C M).d 0 ((ComplexShape.up ℕ).next 0)).hom φ = 0
      rw [CochainComplex.next]
      change φ.comp (C.d 1 0).hom = 0
      ext y
      change h (homologyClass C 0 (toZeroCycles C ((C.d 1 0).hom y))) = 0
      have he : toZeroCycles C ((C.d 1 0).hom y) = j C 0 (incomingProjection C 0 y) := rfl
      rw [he, homologyClass_boundary, map_zero]
    refine ⟨homologyClass _ 0 ⟨φ,hφ⟩, ?_⟩
    apply (cycleBoundaries C 0).quot_hom_ext
    intro x
    rfl
  exact ⟨LinearEquiv.ofBijective β ⟨hi,hs⟩, cohomologyRestriction_formula C M 0⟩

/-- Precomposing a boundary functional with d yields a cocycle. -/
def boundaryToCycles (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :
    (boundaries C n →ₗ[R] M) →ₗ[ℤ] cycles (homComplex C M) (n+1) :=
  (P103.HomTensorExactness.pre (Q := M) (incomingProjection C n)).toIntLinearMap.codRestrict _ (by
    intro h
    change ((homComplex C M).d (n+1) ((ComplexShape.up ℕ).next (n+1))).hom
      (h.comp (incomingProjection C n)) = 0
    rw [CochainComplex.next]
    change (h.comp (incomingProjection C n)).comp (C.d (n+1+1) (n+1)).hom = 0
    ext y
    have h0 : incomingProjection C n ((C.d (n+1+1) (n+1)).hom y) = 0 := by
      apply Subtype.ext
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (C.d_comp_d (n+1+1) (n+1) n)) y
    change h (incomingProjection C n ((C.d (n+1+1) (n+1)).hom y)) = 0
    rw [h0, map_zero])

def boundaryClass (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :
    (boundaries C n →ₗ[R] M) →ₗ[ℤ] Homology (homComplex C M) (n+1) :=
  (homologyClass _ (n+1)).comp (boundaryToCycles C M n)

theorem boundaryClass_formula (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :
    IsBoundaryClass C M n (boundaryClass C M n) := by
  intro h z hz
  exact congrArg (homologyClass _ (n+1)) (Subtype.ext hz.symm)

/-- Exactness at Hom cohomology is just factorization through im d. -/
theorem boundaryClass_restriction_exact (C : Ordinary.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :
    Function.Exact (boundaryClass C M n) (cohomologyRestriction C M (n+1)) := by
  intro x
  constructor
  · intro hx
    obtain ⟨z,rfl⟩ := (cycleBoundaries (homComplex C M) (n+1)).mkQ_surjective x
    have hk : LinearMap.ker (incomingProjection C n) ≤ LinearMap.ker (homTerm C M (n+1) z.val) := by
      intro y hy
      have hy' : y ∈ cycles C (n+1) := by
        change (C.d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom y = 0
        rw [ChainComplex.next_nat_succ]
        exact congrArg Subtype.val hy
      exact LinearMap.congr_fun hx (homologyClass C (n+1) ⟨y,hy'⟩)
    let h := (incomingProjection C n).liftOfSurjective
      (boundaryProjection_surjective C (n+1)) ⟨homTerm C M (n+1) z.val,hk⟩
    refine ⟨h, ?_⟩
    apply congrArg (homologyClass _ (n+1))
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    exact (incomingProjection C n).equivOfSurjective_apply _ hk
  · rintro ⟨h,rfl⟩
    apply (cycleBoundaries C (n+1)).quot_hom_ext
    intro z
    change h (incomingProjection C n z.val) = 0
    have hz := z.property
    change (C.d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom z.val = 0 at hz
    rw [ChainComplex.next_nat_succ] at hz
    rw [show incomingProjection C n z.val = 0 from Subtype.ext hz, map_zero]

/-- A boundary class is zero precisely when it extends to cycles. The reverse
implication uses the given splitting of Zₙ → Cₙ. -/
theorem restriction_boundaryClass_exact (C : Ordinary.{u,v} R)
    (hC : ProjectiveTermsAndBoundaries C) (M : ModuleCat.{w} R) (n : ℕ) :
    Function.Exact (restriction C M n) (boundaryClass C M n) := by
  intro h
  constructor
  · intro hh
    have hz : boundaryToCycles C M n h ∈ cycleBoundaries (homComplex C M) (n+1) :=
      (Submodule.Quotient.mk_eq_zero _).mp hh
    change ∃ φ, ((homComplex C M).d ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom φ = _ at hz
    rw [CochainComplex.prev_nat_succ] at hz
    obtain ⟨φ,hφ⟩ := hz
    refine ⟨(homTerm C M n φ).comp (cycles C n).subtype, ?_⟩
    ext b
    obtain ⟨y,hy⟩ := boundaryProjection_surjective C (n+1) b
    have hp := LinearMap.congr_fun hφ y
    change homTerm C M n φ ((C.d (n+1) n).hom y) = h (incomingProjection C n y) at hp
    change homTerm C M n φ b.val = h b
    have hy' : incomingProjection C n y = b := hy
    rw [hy'] at hp
    rw [← congrArg Subtype.val hy']
    exact hp
  · rintro ⟨k,rfl⟩
    obtain ⟨r,hr⟩ := cycle_retraction C hC n
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change ∃ φ, ((homComplex C M).d ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom φ = _
    rw [CochainComplex.prev_nat_succ]
    refine ⟨k.comp r, ?_⟩
    apply LinearMap.ext
    intro y
    have he : r ((C.d (n+1) n).hom y) = j C n (incomingProjection C n y) :=
      LinearMap.congr_fun hr (j C n (incomingProjection C n y))
    change k (r ((C.d (n+1) n).hom y)) = k (j C n (incomingProjection C n y))
    rw [he]

/-- Descent to the coker of restriction along Bₙ → Zₙ. -/
def cokerInclusion (C : Ordinary.{u,v} R) (hC : ProjectiveTermsAndBoundaries C)
    (M : ModuleCat.{w} R) (n : ℕ) :
    BoundaryCoker C M n →ₗ[ℤ] Homology (homComplex C M) (n+1) :=
  (LinearMap.range (restriction C M n)).liftQ (boundaryClass C M n) (by
    rintro h ⟨k,rfl⟩
    exact (restriction_boundaryClass_exact C hC M n _).mpr ⟨k,rfl⟩)

theorem coker_sequence : coker_sequenceType.{u,v,w} := by
  intro R _ C hC M n
  let α := cokerInclusion C hC M n
  let β := cohomologyRestriction C M (n+1)
  refine ⟨α, β, ?_, cohomologyRestriction_formula C M (n+1), ?_, ?_,
    cohomologyRestriction_surjective C hC M (n+1)⟩
  · exact boundaryClass_formula C M n
  · apply LinearMap.ker_eq_bot.mp
    apply Submodule.ker_liftQ_eq_bot
    intro h hh
    exact (restriction_boundaryClass_exact C hC M n h).mp hh
  · intro x
    constructor
    · intro hx
      obtain ⟨h,hh⟩ := (boundaryClass_restriction_exact C M n x).mp hx
      exact ⟨Submodule.Quotient.mk h, hh⟩
    · rintro ⟨q,rfl⟩
      obtain ⟨h,rfl⟩ := (LinearMap.range (restriction C M n)).mkQ_surjective q
      exact (boundaryClass_restriction_exact C M n _).mpr ⟨h,rfl⟩

/-- The other basic short exact sequence Bₙ → Zₙ → Hₙ. -/
theorem boundaries_cycles_exact (C : Ordinary.{u,v} R) (n : ℕ) :
    Function.Exact (j C n) (homologyClass C n) := by
  intro z
  constructor
  · intro hz
    have hb : z ∈ cycleBoundaries C n := (Submodule.Quotient.mk_eq_zero _).mp hz
    exact ⟨⟨z.val,hb⟩, rfl⟩
  · rintro ⟨b,rfl⟩
    exact homologyClass_boundary C n b

theorem ext_coker : ext_cokerType.{u,v,w} := by
  intro R _ C hC M n N hN
  obtain ⟨L,hL⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution R (boundaries C n)
  obtain ⟨hH,hs⟩ := P103.Ch11.DimensionShifting.ext_first R
    (ModuleCat.of R (boundaries C n)) (ModuleCat.of R (cycles C n))
    (ModuleCat.of R (Homology C n)) (ModuleCat.ofHom (j C n))
    (ModuleCat.ofHom (homologyClass C n))
    (by intro x y h; exact Subtype.ext (congrArg (fun z : cycles C n => z.val) h))
    (boundaries_cycles_exact C n) (cycleBoundaries C n).mkQ_surjective
    (projective_cycles C hC n).2 M L N hL hN
  obtain ⟨H⟩ := hH
  obtain ⟨δ,hδ,_,e,he⟩ := hs H
  exact ⟨e,L,hL,H,δ 0,hδ 0,he⟩

theorem universal_coefficients : universal_coefficientsType.{u,v,w} := by
  intro R _ C hC M n N hN
  obtain ⟨e,he⟩ := ext_coker C hC M n N hN
  obtain ⟨α,β,h⟩ := coker_sequence C hC M n
  refine ⟨e,α,β,he,h,h.2.2.1.comp e.injective,?_,h.2.2.2.2⟩
  intro x
  rw [h.2.2.2.1 x]
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨e.symm y, ?_⟩
    change α (e (e.symm y)) = x
    rw [e.apply_symm_apply]
    exact hy
  · rintro ⟨y,hy⟩
    exact ⟨e y,hy⟩

theorem right_modules : right_modulesType.{u,v,w} := by
  intro R _ C hC M n N hN
  exact universal_coefficients C hC M n N hN

/-- The inclusion of the zero-differential cycles complex. -/
def cyclesInclusion (C : Ordinary.{u,v} R) : zeroCycles C ⟶ C where
  f n := ModuleCat.ofHom (cycles C n).subtype
  comm' a b hab := by
    change b+1=a at hab
    subst a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (C.d (b+1) b).hom z.val = 0
    have hz := z.property
    change (C.d (b+1) ((ComplexShape.down ℕ).next (b+1))).hom z.val = 0 at hz
    rw [ChainComplex.next_nat_succ] at hz
    exact hz

/-- The quotient complex C/Z, identified degreewise with the preceding boundaries. -/
def boundariesProjection (C : Ordinary.{u,v} R) : C ⟶ zeroPreviousBoundaries C where
  f n := ModuleCat.ofHom (boundaryProjection C n)
  comm' a b hab := by
    change b+1=a at hab
    subst a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change 0 = boundaryProjection C b ((C.d (b+1) b).hom x)
    cases b with
    | zero => rfl
    | succ b =>
      apply Subtype.ext
      exact (LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (C.d_comp_d (b+1+1) (b+1) b)) x).symm

theorem hom_degreewise_exact (C : Ordinary.{u,v} R) (hC : ProjectiveTermsAndBoundaries C)
    (M : ModuleCat.{w} R) :
    DegreewiseExact (homPreMap (boundariesProjection C) M) (homPreMap (cyclesInclusion C) M) := by
  intro n
  obtain ⟨hi,he⟩ := P103.HomTensorExactness.homContravariant R
    (cycles C n) (C.X n) (previousBoundary C n) M
    (cycles C n).subtype (boundaryProjection C n)
    (cycles_boundary_exact C n) (boundaryProjection_surjective C n)
  refine ⟨hi,he,?_⟩
  intro h
  obtain ⟨r,hr⟩ := cycle_retraction C hC n
  refine ⟨(homTerm (zeroCycles C) M n h).comp r, ?_⟩
  apply LinearMap.ext
  intro x
  change homTerm (zeroCycles C) M n h (r x.val) = homTerm (zeroCycles C) M n h x
  rw [show r x.val=x from LinearMap.congr_fun hr x]

theorem hom_sequence : hom_sequenceType.{u,v,w} := by
  intro R _ C hC
  refine ⟨cyclesInclusion C,boundariesProjection C,fun _ => rfl,fun _ => rfl,?_,?_⟩
  · intro n
    exact ⟨Subtype.val_injective,cycles_boundary_exact C n,boundaryProjection_surjective C n⟩
  · intro M
    have hd := hom_degreewise_exact C hC M
    refine ⟨hd,?_⟩
    intro n
    obtain ⟨δ,hδ,_⟩ := P103.Ch10.HomologySequence.sequence
      (homPreMap (boundariesProjection C) M) (homPreMap (cyclesInclusion C) M) hd n (n+1) rfl
    refine ⟨δ,hδ.1,hδ.2,?_⟩
    intro h k hk
    obtain ⟨r,hr⟩ := cycle_retraction C hC n
    let φ : C.X n →ₗ[R] M := (homTerm (zeroCycles C) M n h.val).comp r
    apply hδ.1 h φ k
    · apply LinearMap.ext
      intro z
      change homTerm (zeroCycles C) M n h.val (r z.val) = homTerm (zeroCycles C) M n h.val z
      rw [show r z.val=z from LinearMap.congr_fun hr z]
    · apply LinearMap.ext
      intro y
      change homTerm (zeroPreviousBoundaries C) M (n+1) k.val (incomingProjection C n y) =
        homTerm (zeroCycles C) M n h.val (r ((C.d (n+1) n).hom y))
      have he : r ((C.d (n+1) n).hom y) = j C n (incomingProjection C n y) :=
        LinearMap.congr_fun hr (j C n (incomingProjection C n y))
      exact (hk (incomingProjection C n y)).trans
        (congrArg (homTerm (zeroCycles C) M n h.val) he.symm)

/-- The map on actual boundary submodules induced by a chain map. -/
def boundaryMap {C D : Ordinary.{u,v} R} (f : D ⟶ C) (n : ℕ) :
    boundaries D n →ₗ[R] boundaries C n :=
  ((f.f n).hom.comp (boundaries D n).subtype).codRestrict _ (by
    intro b
    exact P103.Ch10.Complexes.map_boundaries f n b.property)

theorem boundaryClass_natural {C D : Ordinary.{u,v} R} (f : D ⟶ C)
    (M M' : ModuleCat.{w} R) (g : M ⟶ M') (n : ℕ) (h : boundaries C n →ₗ[R] M) :
    homologyMap (homPreMap f M ≫ homPostMap D g.hom) (n+1) (boundaryClass C M n h) =
      boundaryClass D M' n (g.hom.comp (h.comp (boundaryMap f n))) := by
  apply congrArg (homologyClass _ (n+1))
  apply Subtype.ext
  apply LinearMap.ext
  intro y
  change g.hom (h (incomingProjection C n ((f.f (n+1)).hom y))) =
    g.hom (h (boundaryMap f n (incomingProjection D n y)))
  congr 2
  apply Subtype.ext
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.comm (n+1) n)) y

theorem extCoker_natural {C D : Ordinary.{u,v} R} (f : D ⟶ C)
    (M M' : ModuleCat.{w} R) (g : M ⟶ M') (n : ℕ) (E : ExtMaps.{u,v,w} R 1)
    (N : LeftResolution R (Homology C n)) (N' : LeftResolution R (Homology D n))
    (hN : N.IsProjective) (hN' : N'.IsProjective)
    (e : ExtWith N M 1 ≃ₗ[ℤ] BoundaryCoker C M n)
    (e' : ExtWith N' M' 1 ≃ₗ[ℤ] BoundaryCoker D M' n)
    (he : IsExtCoker C M n N e) (he' : IsExtCoker D M' n N' e')
    (h : boundaries C n →ₗ[R] M) :
    E.map ⟨N,hN⟩ ⟨N',hN'⟩ (ModuleCat.ofHom (homologyMap f n)) g
      (e.symm (Submodule.Quotient.mk h)) =
      e'.symm (Submodule.Quotient.mk (g.hom.comp (h.comp (boundaryMap f n)))) := by
  obtain ⟨L,hL,H,δ,hδ,he⟩ := he
  obtain ⟨L',hL',H',δ',hδ',he'⟩ := he'
  obtain ⟨E₀⟩ := P103.Ch11.ExtTorDefinitions.ext_bifunctorial R 0
  exact P103.Ch11.DimensionShifting.ext_first_edge_natural R E₀ E
    (ModuleCat.of R (boundaries C n)) (ModuleCat.of R (cycles C n)) (ModuleCat.of R (Homology C n))
    (ModuleCat.of R (boundaries D n)) (ModuleCat.of R (cycles D n)) (ModuleCat.of R (Homology D n))
    (ModuleCat.ofHom (j C n)) (ModuleCat.ofHom (homologyClass C n))
    (ModuleCat.ofHom (j D n)) (ModuleCat.ofHom (homologyClass D n))
    (ModuleCat.ofHom (boundaryMap f n)) (ModuleCat.ofHom (cyclesMap f n))
    (ModuleCat.ofHom (homologyMap f n))
    (by intro x y h; exact Subtype.ext (congrArg (fun z : cycles C n => z.val) h))
    (boundaries_cycles_exact C n) (cycleBoundaries C n).mkQ_surjective
    (by intro x y h; exact Subtype.ext (congrArg (fun z : cycles D n => z.val) h))
    (boundaries_cycles_exact D n) (cycleBoundaries D n).mkQ_surjective
    (by ext b; rfl) (by ext z; rfl)
    L N L' N' hL hN hL' hN' H H' M M' g δ δ' e e' hδ hδ' he he' h

theorem cokerSequence_left_formula {C : Ordinary.{u,v} R} {M : ModuleCat.{w} R} {n : ℕ}
    {α : BoundaryCoker C M n →ₗ[ℤ] Homology (homComplex C M) (n+1)}
    {β : Homology (homComplex C M) (n+1) →ₗ[ℤ] (Homology C (n+1) →ₗ[R] M)}
    (h : CokerSequence C M n α β) (φ : boundaries C n →ₗ[R] M) :
    α (Submodule.Quotient.mk φ) = boundaryClass C M n φ :=
  h.1 φ (boundaryToCycles C M n φ) rfl

theorem naturality : P103.Specs.Ch11.UniversalCoefficientsCohomology.naturalityType.{u,v,w} := by
  intro R _ C D hC hD f M M' g n E N N' hN hN' e e' α β α' β' he he' h h'
  constructor
  · intro x
    obtain ⟨φ,hφ⟩ := (LinearMap.range (restriction C M n)).mkQ_surjective (e x)
    have hx : x = e.symm (Submodule.Quotient.mk φ) :=
      (e.symm_apply_apply x).symm.trans (congrArg e.symm hφ.symm)
    rw [hx, e.apply_symm_apply, cokerSequence_left_formula h,
      boundaryClass_natural f M M' g n φ,
      extCoker_natural f M M' g n E N N' hN hN' e e' he he' φ,
      e'.apply_symm_apply, cokerSequence_left_formula h']
  · exact restriction_natural f M M' g (n+1) β β' h.2.1 h'.2.1

/-- The coefficient action on cohomology is the action on the functional. -/
theorem restriction_smul {K : Type u} [CommRing K] (C : Ordinary.{u,v} K)
    (M : ModuleCat.{w} K) (n : ℕ)
    (β : Homology (homComplex C M) n →ₗ[ℤ] (Homology C n →ₗ[K] M))
    (hβ : IsRestriction C M n β) (r : K) (x : Homology (homComplex C M) n) :
    letI := cohomologyModule C M n
    β (r • x) = r • β x := by
  letI := cohomologyModule C M n
  obtain ⟨z,rfl⟩ := (cycleBoundaries (homComplex C M) n).mkQ_surjective x
  apply (cycleBoundaries C n).quot_hom_ext
  intro y
  change β (homologyClass _ n (cyclesMap (homPostMap C (scalarMap M r).hom) n z))
      (homologyClass C n y) = r • β (homologyClass _ n z) (homologyClass C n y)
  rw [hβ,hβ]
  rfl

theorem scalar_compatibility : scalar_compatibilityType.{u,v,w} := by
  intro K _ C hC M n E N hN
  letI := extModule E (A := ModuleCat.of K (Homology C n)) ⟨N,hN⟩ M
  letI := cohomologyModule C M (n+1)
  constructor
  · intro e α β he h
    let a : ExtWith N M 1 →ₗ[K] Homology (homComplex C M) (n+1) := {
      toFun := fun x => α (e x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := by
        intro r x
        have hn := (naturality C C hC hC (𝟙 C) M M (scalarMap M r) n E
          N N hN hN e e α β α β he he h h).1 x
        have hid : homPreMap (𝟙 C) M ≫ homPostMap C (scalarMap M r).hom =
            homPostMap C (scalarMap M r).hom := by
          ext i φ
          rfl
        have hidH : homologyMap (𝟙 C) n = LinearMap.id :=
          P103.Ch10.Complexes.homologyMap_id C n
        rw [hid, hidH] at hn
        exact hn.symm }
    let b : Homology (homComplex C M) (n+1) →ₗ[K] (Homology C (n+1) →ₗ[K] M) := {
      toFun := β
      map_add' := β.map_add
      map_smul' := restriction_smul C M (n+1) β h.2.1 }
    exact ⟨a,b,rfl,rfl⟩
  · letI := cohomologyModule C M 0
    intro β hβ
    let b : Homology (homComplex C M) 0 →ₗ[K] (Homology C 0 →ₗ[K] M) := {
      toFun := β
      map_add' := β.map_add
      map_smul' := restriction_smul C M 0 β hβ }
    exact ⟨b,rfl⟩

end
end P103.Ch11.UniversalCoefficientsCohomology
