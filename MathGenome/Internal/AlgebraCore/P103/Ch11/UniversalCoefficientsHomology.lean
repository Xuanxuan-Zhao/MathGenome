import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsHomology
import MathGenome.Internal.AlgebraCore.P103.Ch11.DimensionShifting
import MathGenome.Internal.AlgebraCore.P103.Ch11.FlatResolutions

namespace P103.Ch11.UniversalCoefficientsHomology
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence P103.Specs.Ch10.Horseshoe
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch02.FlatnessTests
open P103.Specs.Ch11.UniversalCoefficientsHomology
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w x
variable {R : Type u} [Ring R]

/-- Flatness is independent of the auxiliary universe used for testing. -/
theorem rightFlat_change_universe {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (h : RightFlat.{u,v,w} R A) : RightFlat.{u,v,x} R A :=
  (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R A).mpr
    (P103.Ch11.VanishingAndFlatness.flat_change_universe
      ((P103.Ch02.FlatnessTests.rightFlat_iff_opposite R A).mp h))

/-- Kernels of epimorphisms between flat modules are flat; no splitting
is used. This is the Tor₂/Tor₁ argument from paper.tex 2963–2968. -/
theorem rightFlat_of_shortExact (A F Q : ModuleCat.{v} Rᵐᵒᵖ)
    (i : A ⟶ F) (p : F ⟶ Q) (hi : Function.Injective i.hom)
    (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
    (hF : RightFlat.{u,v,w} R F) (hQ : RightFlat.{u,v,w} R Q) :
    RightFlat.{u,v,w} R A := by
  apply (P103.Ch11.VanishingAndFlatness.right_flat_iff_tor_one R A).mpr
  intro M _ _ P hP
  obtain ⟨N, hN⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution Rᵐᵒᵖ Q
  obtain ⟨hH, hs⟩ := P103.Ch11.DimensionShifting.tor_first R A F Q i p hi he hp
    (rightFlat_change_universe hF) (ModuleCat.of R M) P N hP hN
  obtain ⟨H⟩ := hH
  obtain ⟨_, _, heq, _⟩ := hs H
  obtain ⟨e, _⟩ := heq 0
  letI := P103.Ch11.VanishingAndFlatness.tor_right_flat R Q M
    (rightFlat_change_universe hQ) N hN 1
  exact e.symm.injective.subsingleton

instance shiftedBoundary_zero_subsingleton (C : Complex.{u,v} R) :
    Subsingleton (shiftedBoundaryTerms C 0) := by
  change Subsingleton (↥(⊥ : Submodule Rᵐᵒᵖ (C.X 0)))
  infer_instance

/-- The first basic sequence, including its actual zero-degree endpoint. -/
theorem cycle_boundary_shortExact (C : Complex.{u,v} R) (n : ℕ) :
    Function.Injective (cycles C n).subtype ∧
    Function.Exact (cycles C n).subtype (boundaryProjectionTerm C n) ∧
    Function.Surjective (boundaryProjectionTerm C n) := by
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · intro c
    have hmem : c ∈ cycles C n ↔ boundaryProjectionTerm C n c = 0 := by
      cases n with
      | zero =>
        have hd : C.d 0 0 = 0 := C.shape 0 0 (by simp [ComplexShape.down_Rel])
        simp [cycles, ChainComplex.next_nat_zero, hd, boundaryProjectionTerm]
      | succ n =>
        change (C.d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom c = 0 ↔ _
        rw [ChainComplex.next_nat_succ]
        constructor
        · intro hc
          exact Subtype.ext hc
        · intro hc
          exact congrArg Subtype.val hc
    exact hmem.symm.trans ⟨fun hc => ⟨⟨c, hc⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.property⟩
  · cases n with
    | zero =>
      intro z
      exact ⟨0, Subsingleton.elim _ _⟩
    | succ n =>
      intro b
      have hb := b.property
      change ∃ c, (C.d ((ComplexShape.down ℕ).prev n) n).hom c = b.val at hb
      rw [ChainComplex.prev] at hb
      obtain ⟨c, hc⟩ := hb
      refine ⟨c, Subtype.ext ?_⟩
      change (C.d (n+1) n).hom c = b.val
      exact hc

/-- The second basic exact sequence 0 → Bₙ → Zₙ → Hₙ → 0. -/
theorem boundary_cycle_homology_shortExact (C : Complex.{u,v} R) (n : ℕ) :
    Function.Injective (boundaryToCycles C n) ∧
    Function.Exact (boundaryToCycles C n) (homologyClass C n) ∧
    Function.Surjective (homologyClass C n) := by
  refine ⟨fun a b h => Subtype.ext (congrArg (fun z : cycles C n => z.val) h), ?_,
    (cycleBoundaries C n).mkQ_surjective⟩
  intro z
  rw [P103.Ch10.HomologySequence.class_zero_iff]
  exact ⟨fun hz => ⟨⟨z.val, hz⟩, Subtype.ext rfl⟩,
    by rintro ⟨b, rfl⟩; exact b.property⟩

/-- All cycles are flat under precisely the original two flatness assumptions. -/
theorem cycles_flat : cycles_flatType.{u,v,w} := by
  intro R _ C hC n
  have hs := cycle_boundary_shortExact C n
  apply rightFlat_of_shortExact (cycleTerms C n) (C.X n) (shiftedBoundaryTerms C n)
    (ModuleCat.ofHom (cycles C n).subtype) (ModuleCat.ofHom (boundaryProjectionTerm C n))
    hs.1 hs.2.1 hs.2.2 (hC.1 n)
  cases n with
  | zero => exact P103.Ch11.FlatResolutions.rightFlat_of_subsingleton _
  | succ n => exact hC.2 n

/-- Tensoring the first basic sequence stays short exact. The middle and
quotient flatness suffice; there is no chosen section. -/
theorem tensor_shortExact_of_flat (A F Q : ModuleCat.{v} Rᵐᵒᵖ)
    (i : A ⟶ F) (p : F ⟶ Q) (hi : Function.Injective i.hom)
    (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
    (hF : RightFlat.{u,v,w} R F) (hQ : RightFlat.{u,v,w} R Q)
    (M : ModuleCat.{w} R) :
    Function.Injective (tensorMap i.hom (LinearMap.id : M →ₗ[R] M)) ∧
    Function.Exact (tensorMap i.hom (LinearMap.id : M →ₗ[R] M))
      (tensorMap p.hom (LinearMap.id : M →ₗ[R] M)) ∧
    Function.Surjective (tensorMap p.hom (LinearMap.id : M →ₗ[R] M)) := by
  obtain ⟨L, hL⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution Rᵐᵒᵖ A
  obtain ⟨N, hN⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution Rᵐᵒᵖ Q
  obtain ⟨⟨H⟩, hs⟩ := P103.Ch11.DimensionShifting.tor_first R A F Q i p hi he hp hF M L N hL hN
  obtain ⟨_, _, _, _, e, _, _⟩ := hs H
  letI := P103.Ch11.VanishingAndFlatness.tor_right_flat R Q M hQ N hN 0
  have hk : Subsingleton (LinearMap.ker (tensorMap i.hom (LinearMap.id : M →ₗ[R] M))) :=
    e.symm.injective.subsingleton
  refine ⟨?_, ?_⟩
  · intro a b hab
    let z : LinearMap.ker (tensorMap i.hom (LinearMap.id : M →ₗ[R] M)) :=
      ⟨a - b, by change tensorMap i.hom (LinearMap.id : M →ₗ[R] M) (a-b) = 0
                 rw [map_sub, hab, sub_self]⟩
    exact sub_eq_zero.mp (congrArg Subtype.val (hk.elim z 0))
  · exact P103.HomTensorExactness.tensor_first_rightExact i.hom p.hom he hp
      (tensorMap i.hom (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom (by intros; rfl)
      (tensorMap p.hom LinearMap.id).toAddMonoidHom (by intros; rfl)

/-- The source's short exact sequence of tensored complexes. -/
theorem tensor_degreewise_exact : tensor_degreewise_exactType.{u,v,w} := by
  intro R _ C hC M n
  have hs := cycle_boundary_shortExact C n
  have hQ : RightFlat.{u,v,w} R (shiftedBoundaryTerms C n) := by
    cases n with
    | zero => exact P103.Ch11.FlatResolutions.rightFlat_of_subsingleton _
    | succ n => exact hC.2 n
  exact tensor_shortExact_of_flat (cycleTerms C n) (C.X n) (shiftedBoundaryTerms C n)
    (ModuleCat.ofHom (cycles C n).subtype) (ModuleCat.ofHom (boundaryProjectionTerm C n))
    hs.1 hs.2.1 hs.2.2 (hC.1 n) hQ M

/-- Zero differentials identify homology with the actual term by its class map. -/
theorem tensorZeroClass_bijective (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (M : ModuleCat.{w} R) (n : ℕ) : Function.Bijective (tensorZeroClass X M n) := by
  constructor
  · intro a b hab
    have hh := (P103.Ch10.Complexes.homologyClass_eq_iff
      (tensorComplex (zeroDifferentialComplex X) M) n
      (tensorZeroCycle X M n a) (tensorZeroCycle X M n b)).mp hab
    obtain ⟨c, hc⟩ := hh
    rw [tensorZero_d] at hc
    exact sub_eq_zero.mp hc.symm
  · intro q
    obtain ⟨z, rfl⟩ := (cycleBoundaries (tensorComplex (zeroDifferentialComplex X) M) n).mkQ_surjective q
    exact ⟨z.val, rfl⟩

/-- Canonical equivalence used in the homology sequence calculation. -/
def tensorZeroEquiv (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R) (n : ℕ) :=
  LinearEquiv.ofBijective (tensorZeroClass X M n) (tensorZeroClass_bijective X M n)

/-- The connecting map, evaluated on all tensors, is the boundary inclusion. -/
theorem tensor_connector : tensor_connectorType.{u,v,w} := by
  intro R _ C hC M n
  obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence
    (tensorFirstMap (cycleInclusion C) M) (tensorFirstMap (boundaryProjection C) M)
    (tensor_degreewise_exact R C hC M) (n+1) n (by rfl)
  refine ⟨δ, hδ.1, hδ.2, ?_⟩
  have hh : δ.comp (tensorZeroClass (shiftedBoundaryTerms C) M (n+1)) =
      (tensorZeroClass (cycleTerms C) M n).comp (jTensor C M n) := by
    apply tensor_hom_ext
    intro b m
    have hb := b.property
    change ∃ c, (C.d ((ComplexShape.down ℕ).prev n) n).hom c = b.val at hb
    rw [ChainComplex.prev] at hb
    obtain ⟨c, hc'⟩ := hb
    apply hδ.1 (tensorZeroCycle (shiftedBoundaryTerms C) M (n+1) (tmul R b m))
      (tmul R c m) (tensorZeroCycle (cycleTerms C) M n (jTensor C M n (tmul R b m)))
    · change tmul R (boundaryProjectionTerm C (n+1) c) m = tmul R b m
      exact congrArg (fun b => tmul R b m) (Subtype.ext hc')
    · change tmul R b.val m = tmul R ((C.d (n+1) n).hom c) m
      rw [hc']
  exact LinearMap.congr_fun hh

/-- The canonical Tor₁ identification for the second basic exact sequence. -/
theorem torKernelIdentification (C : Complex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (M : ModuleCat.{w} R) (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n))) :
    ∃ e : TorWith P.val M 1 ≃ₗ[ℤ] LinearMap.ker (jTensor C M n),
      TorKernelIdentification C M n P e := by
  have hs := boundary_cycle_homology_shortExact C n
  obtain ⟨L, hL⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution
    Rᵐᵒᵖ (boundaries C n)
  obtain ⟨⟨H⟩, hh⟩ := P103.Ch11.DimensionShifting.tor_first R
    (ModuleCat.of Rᵐᵒᵖ (boundaries C n)) (cycleTerms C n)
    (ModuleCat.of Rᵐᵒᵖ (Homology C n))
    (ModuleCat.ofHom (boundaryToCycles C n)) (ModuleCat.ofHom (homologyClass C n))
    hs.1 hs.2.1 hs.2.2 (cycles_flat R C hC n) M L P.val hL P.property
  obtain ⟨δ, hδ, _, z, e, hz, he⟩ := hh H
  exact ⟨e, ⟨⟨L, hL⟩, H, δ 0, z, hδ 0, hz, he⟩⟩

/-- An exact five-term sequence yields its cokernel/kernel short exact sequence. -/
theorem shortExact_of_fiveTerm
    {U V Q W T S E : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup Q] [AddCommGroup W]
    [AddCommGroup T] [AddCommGroup S] [AddCommGroup E]
    (j : U →ₗ[ℤ] V) (q : V →ₗ[ℤ] Q) (a : V →ₗ[ℤ] W)
    (b : W →ₗ[ℤ] T) (k : T →ₗ[ℤ] S)
    (hq : Function.Exact j q) (sq : Function.Surjective q)
    (ha : Function.Exact j a) (hab : Function.Exact a b) (hbk : Function.Exact b k)
    (e : E ≃ₗ[ℤ] LinearMap.ker k) :
    ∃ (α : Q →ₗ[ℤ] W) (β : W →ₗ[ℤ] E),
      Function.Injective α ∧ Function.Exact α β ∧ Function.Surjective β ∧
      (∀ v, α (q v) = a v) ∧ ∀ x, (e (β x)).val = b x := by
  let eq := hq.linearEquivOfSurjective sq
  let aq := (LinearMap.range j).liftQ a (by
    rintro _ ⟨u, rfl⟩
    exact ha.apply_apply_eq_zero u)
  let α := aq.comp eq.symm.toLinearMap
  have hα (v : V) : α (q v) = a v := by
    change aq (eq.symm (q v)) = a v
    rw [Function.Exact.linearEquivOfSurjective_symm_apply]
    rfl
  let bk := b.codRestrict (LinearMap.ker k) (by
    intro x
    exact (hbk (b x)).mpr ⟨x, rfl⟩)
  let β := e.symm.toLinearMap.comp bk
  have hβ (x : W) : (e (β x)).val = b x := by
    change (e (e.symm (bk x))).val = b x
    rw [e.apply_symm_apply]
    rfl
  have hz (x : W) : β x = 0 ↔ b x = 0 := by
    constructor
    · intro hx
      rw [← hβ, hx, map_zero]
      rfl
    · intro hx
      apply e.injective
      apply Subtype.ext
      rw [hβ, hx, map_zero]
      rfl
  refine ⟨α, β, ?_, ?_, ?_, hα, hβ⟩
  · exact (LinearMap.injective_range_liftQ_of_exact ha).comp eq.symm.injective
  · intro x
    rw [hz]
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := (hab x).mp hx
      exact ⟨q v, (hα v).trans hv⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨v, rfl⟩ := sq y
      rw [hα]
      exact hab.apply_apply_eq_zero v
  · intro y
    obtain ⟨x, hx⟩ := (hbk (e y).val).mp (e y).property
    refine ⟨x, e.injective (Subtype.ext ?_)⟩
    rw [hβ, hx]


/-- Map from tensored cycles into homology of the tensored complex. -/
def cycleTensorHomology (C : Complex.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :=
  (homologyMap (tensorFirstMap (cycleInclusion C) M) n).comp
    (tensorZeroClass (cycleTerms C) M n)

/-- Map to the shifted boundary term, before restricting to the kernel. -/
def homologyBoundaryTensor (C : Complex.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :=
  (tensorZeroEquiv (shiftedBoundaryTerms C) M (n+1)).symm.toLinearMap.comp
    (homologyMap (tensorFirstMap (boundaryProjection C) M) (n+1))

/-- The incoming part of the homology sequence presents the cokernel of j⊗1. -/
theorem exact_j_cycleTensorHomology (C : Complex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (M : ModuleCat.{w} R) (n : ℕ) :
    Function.Exact (jTensor C M n) (cycleTensorHomology C M n) := by
  obtain ⟨δ, _, hs, hc⟩ := tensor_connector R C hC M n
  intro z
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := (hs.2.2 (tensorZeroClass (cycleTerms C) M n z)).mp hz
    obtain ⟨t, rfl⟩ := (tensorZeroClass_bijective (shiftedBoundaryTerms C) M (n+1)).2 t
    exact ⟨t, (tensorZeroClass_bijective (cycleTerms C) M n).1 ((hc t).symm.trans ht)⟩
  · rintro ⟨t, rfl⟩
    change homologyMap (tensorFirstMap (cycleInclusion C) M) n
      (tensorZeroClass (cycleTerms C) M n (jTensor C M n t)) = 0
    rw [← hc]
    exact hs.2.2.apply_apply_eq_zero _

/-- All three relevant exact terms of the homology sequence in tensor coordinates. -/
theorem tensor_fiveTerm (C : Complex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (M : ModuleCat.{w} R) (n : ℕ) :
    Function.Exact (jTensor C M (n+1)) (cycleTensorHomology C M (n+1)) ∧
    Function.Exact (cycleTensorHomology C M (n+1)) (homologyBoundaryTensor C M n) ∧
    Function.Exact (homologyBoundaryTensor C M n) (jTensor C M n) := by
  obtain ⟨δ, _, hs, hc⟩ := tensor_connector R C hC M n
  let eL := tensorZeroEquiv (shiftedBoundaryTerms C) M (n+1)
  let eZ := tensorZeroEquiv (cycleTerms C) M (n+1)
  refine ⟨exact_j_cycleTensorHomology C hC M (n+1), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx' : homologyMap (tensorFirstMap (boundaryProjection C) M) (n+1) x = 0 := by
        apply eL.symm.injective
        exact hx.trans (map_zero eL.symm).symm
      obtain ⟨z, hz⟩ := (hs.1 x).mp hx'
      obtain ⟨z, rfl⟩ := eZ.surjective z
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      change eL.symm (homologyMap (tensorFirstMap (boundaryProjection C) M) (n+1)
        (homologyMap (tensorFirstMap (cycleInclusion C) M) (n+1) (eZ z))) = 0
      rw [hs.1.apply_apply_eq_zero, map_zero]
  · intro t
    constructor
    · intro ht
      have ht' : δ (eL t) = 0 := by
        change δ (tensorZeroClass (shiftedBoundaryTerms C) M (n+1) t) = 0
        rw [hc, ht, map_zero]
      obtain ⟨x, hx⟩ := (hs.2.1 (eL t)).mp ht'
      refine ⟨x, ?_⟩
      change eL.symm _ = t
      rw [hx, eL.symm_apply_apply]
    · rintro ⟨x, rfl⟩
      apply (tensorZeroClass_bijective (cycleTerms C) M n).1
      rw [map_zero, ← hc]
      change δ (eL (eL.symm _)) = 0
      rw [eL.apply_symm_apply]
      exact hs.2.1.apply_apply_eq_zero _

/-- Construct the sequence in every positive degree. -/
theorem positiveSequence_exists (C : Complex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (M : ModuleCat.{w} R) (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n))) :
    Nonempty (PositiveSequence C M n P) := by
  have hH := boundary_cycle_homology_shortExact C (n+1)
  let q := tensorMap (homologyClass C (n+1)) (LinearMap.id : M →ₗ[R] M)
  have hq : Function.Exact (jTensor C M (n+1)) q ∧ Function.Surjective q :=
    P103.HomTensorExactness.tensor_first_rightExact
      (boundaryToCycles C (n+1)) (homologyClass C (n+1)) hH.2.1 hH.2.2
      (jTensor C M (n+1)).toAddMonoidHom (by intros; rfl)
      q.toAddMonoidHom (by intros; rfl)
  obtain ⟨e, he⟩ := torKernelIdentification C hC M n P
  have hs := tensor_fiveTerm C hC M n
  obtain ⟨α, β, hα, hαβ, hβ, hαq, heβ⟩ := shortExact_of_fiveTerm
    (jTensor C M (n+1)) q (cycleTensorHomology C M (n+1))
    (homologyBoundaryTensor C M n) (jTensor C M n)
    hq.1 hq.2 hs.1 hs.2.1 hs.2.2 e
  refine ⟨⟨α, β, hα, hαβ, hβ, ?_, e, he, ?_⟩⟩
  · intro z m
    change α (q (tmul R z m)) = _
    rw [hαq]
    rfl
  · intro x
    rw [heβ]
    exact (tensorZeroEquiv (shiftedBoundaryTerms C) M (n+1)).apply_symm_apply _

/-- At degree zero the right endpoint vanishes and α is an isomorphism. -/
theorem zeroSequence_exists (C : Complex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (M : ModuleCat.{w} R) :
    Nonempty (ZeroSequence C M) := by
  have hH := boundary_cycle_homology_shortExact C 0
  let q := tensorMap (homologyClass C 0) (LinearMap.id : M →ₗ[R] M)
  have hq : Function.Exact (jTensor C M 0) q ∧ Function.Surjective q :=
    P103.HomTensorExactness.tensor_first_rightExact
      (boundaryToCycles C 0) (homologyClass C 0) hH.2.1 hH.2.2
      (jTensor C M 0).toAddMonoidHom (by intros; rfl)
      q.toAddMonoidHom (by intros; rfl)
  let a := cycleTensorHomology C M 0
  have ha : Function.Exact (jTensor C M 0) a := exact_j_cycleTensorHomology C hC M 0
  let eq := hq.1.linearEquivOfSurjective hq.2
  let aq := (LinearMap.range (jTensor C M 0)).liftQ a (by
    rintro _ ⟨u, rfl⟩
    exact ha.apply_apply_eq_zero u)
  let α := aq.comp eq.symm.toLinearMap
  have hα (v) : α (q v) = a v := by
    change aq (eq.symm (q v)) = a v
    rw [Function.Exact.linearEquivOfSurjective_symm_apply]
    rfl
  have hzero (x : Homology (tensorComplex (shiftedBoundaryComplex C) M) 0) : x = 0 := by
    obtain ⟨z, rfl⟩ := (cycleBoundaries _ 0).mkQ_surjective x
    have hz : z = 0 := Subtype.ext (eq_zero_of_subsingleton_left (A := shiftedBoundaryTerms C 0) z.val)
    rw [hz, map_zero]
  letI : Subsingleton (Homology (tensorComplex (shiftedBoundaryComplex C) M) 0) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  have hs := P103.Ch10.HorseshoeNaturality.chain_bottom_exact
    (tensorFirstMap (cycleInclusion C) M) (tensorFirstMap (boundaryProjection C) M)
    (tensor_degreewise_exact R C hC M)
  have sa : Function.Surjective a :=
    (P103.Ch10.HomologySequence.exact_surjective_of_subsingleton _ _ hs.1).comp
      (tensorZeroClass_bijective (cycleTerms C) M 0).2
  refine ⟨⟨α, ⟨(LinearMap.injective_range_liftQ_of_exact ha).comp eq.symm.injective, ?_⟩,
    ?_, ?_⟩⟩
  · intro x
    obtain ⟨v, rfl⟩ := sa x
    exact ⟨q v, hα v⟩
  · intro z m
    change α (q (tmul R z m)) = _
    rw [hα]
    rfl
  · intro P
    exact P103.Ch11.VanishingAndFlatness.tor_right_flat R (shiftedBoundaryTerms C 0) M
      (P103.Ch11.FlatResolutions.rightFlat_of_subsingleton _) P.val P.property 0


/-- A chain map restricts to the actual boundary submodules. -/
def boundaryMap {C D : Complex.{u,v} R} (f : C ⟶ D) (n : ℕ) :
    boundaries C n →ₗ[Rᵐᵒᵖ] boundaries D n :=
  ((f.f n).hom.comp (boundaries C n).subtype).codRestrict (boundaries D n)
    (fun b => P103.Ch10.Complexes.map_boundaries f n b.property)

/-- Normalized kernel identifications commute with all chain and coefficient maps. -/
theorem torKernelIdentification_natural {C D : Complex.{u,v} R}
    (f : C ⟶ D) (M M' : ModuleCat.{w} R) (g : M ⟶ M') (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n)))
    (P' : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology D n)))
    (T : TorMaps.{u,v,w} R 1)
    (e : TorWith P.val M 1 ≃ₗ[ℤ] LinearMap.ker (jTensor C M n))
    (e' : TorWith P'.val M' 1 ≃ₗ[ℤ] LinearMap.ker (jTensor D M' n))
    (he : TorKernelIdentification C M n P e) (he' : TorKernelIdentification D M' n P' e') :
    ∀ x, (e' (T.map P P' (ModuleCat.ofHom (homologyMap f n)) g x)).val =
      tensorMap (boundaryMap f n) g.hom (e x).val := by
  obtain ⟨L, H, δ, z, hδ, hz, he⟩ := he
  obtain ⟨L', H', δ', z', hδ', hz', he'⟩ := he'
  have hs := boundary_cycle_homology_shortExact C n
  have hs' := boundary_cycle_homology_shortExact D n
  obtain ⟨T0⟩ := P103.Ch11.ExtTorDefinitions.tor_bifunctorial R 0
  apply P103.Ch11.DimensionShifting.tor_first_edge_natural R
    (ModuleCat.of Rᵐᵒᵖ (boundaries C n)) (cycleTerms C n)
    (ModuleCat.of Rᵐᵒᵖ (Homology C n))
    (ModuleCat.of Rᵐᵒᵖ (boundaries D n)) (cycleTerms D n)
    (ModuleCat.of Rᵐᵒᵖ (Homology D n))
    (ModuleCat.ofHom (boundaryToCycles C n)) (ModuleCat.ofHom (homologyClass C n))
    (ModuleCat.ofHom (boundaryToCycles D n)) (ModuleCat.ofHom (homologyClass D n))
    (ModuleCat.ofHom (boundaryMap f n)) (ModuleCat.ofHom (cyclesMap f n))
    (ModuleCat.ofHom (homologyMap f n))
    hs.1 hs.2.1 hs.2.2 hs'.1 hs'.2.1 hs'.2.2
    (by ext b; rfl) (by ext b; rfl)
    L P L' P' H H' M M' g T T0 δ δ' z z' e e' hδ hδ' hz hz' he he'

/-- Naturality of α follows on generators from its representative formula. -/
theorem alpha_natural {C D : Complex.{u,v} R} (f : C ⟶ D)
    (M M' : ModuleCat.{w} R) (g : M ⟶ M') (n : ℕ)
    (α : Tensor R (Homology C n) M →ₗ[ℤ] Homology (tensorComplex C M) n)
    (α' : Tensor R (Homology D n) M' →ₗ[ℤ] Homology (tensorComplex D M') n)
    (hα : ∀ (z : cycles C n) m, α (tmul R (homologyClass C n z) m) =
      homologyClass (tensorComplex C M) n (tensorCycle C M n z m))
    (hα' : ∀ (z : cycles D n) m, α' (tmul R (homologyClass D n z) m) =
      homologyClass (tensorComplex D M') n (tensorCycle D M' n z m)) :
    (homologyMap (tensorFirstMap f M ≫ tensorSecondMap D g.hom) n).comp α =
      α'.comp (tensorMap (homologyMap f n) g.hom) := by
  apply tensor_hom_ext
  intro h m
  obtain ⟨z, rfl⟩ := (cycleBoundaries C n).mkQ_surjective h
  change homologyMap (tensorFirstMap f M ≫ tensorSecondMap D g.hom) n
    (α (tmul R (homologyClass C n z) m)) =
    α' (tmul R (homologyMap f n (homologyClass C n z)) (g.hom m))
  rw [hα, P103.Ch10.Complexes.homologyMap_apply,
    P103.Ch10.Complexes.homologyMap_apply, hα']
  rfl

/-- The normalized β formula, before passing to the zero-complex homology class. -/
theorem beta_class_formula {C : Complex.{u,v} R} {M : ModuleCat.{w} R} {n : ℕ}
    {P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n))}
    (S : PositiveSequence C M n P) (z : cycles (tensorComplex C M) (n+1)) :
    (S.kernelIso (S.β (homologyClass _ (n+1) z))).val =
      tensorMap (boundaryProjectionTerm C (n+1)) (LinearMap.id : M →ₗ[R] M) z.val := by
  apply (tensorZeroClass_bijective (shiftedBoundaryTerms C) M (n+1)).1
  exact S.β_formula (homologyClass _ (n+1) z)

/-- The two β arrows commute with the canonical action on Tor. -/
theorem beta_natural {C D : Complex.{u,v} R} (f : C ⟶ D)
    (M M' : ModuleCat.{w} R) (g : M ⟶ M') (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n)))
    (P' : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology D n)))
    (T : TorMaps.{u,v,w} R 1)
    (S : PositiveSequence C M n P) (S' : PositiveSequence D M' n P') :
    (T.map P P' (ModuleCat.ofHom (homologyMap f n)) g).comp S.β =
      S'.β.comp (homologyMap (tensorFirstMap f M ≫ tensorSecondMap D g.hom) (n+1)) := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (cycleBoundaries (tensorComplex C M) (n+1)).mkQ_surjective x
  have hh : (tensorMap (boundaryMap f n) g.hom).comp
      (tensorMap (boundaryProjectionTerm C (n+1)) (LinearMap.id : M →ₗ[R] M)) =
      (tensorMap (boundaryProjectionTerm D (n+1)) (LinearMap.id : M' →ₗ[R] M')).comp
        ((tensorMap (LinearMap.id : D.X (n+1) →ₗ[Rᵐᵒᵖ] D.X (n+1)) g.hom).comp
          (tensorMap (f.f (n+1)).hom (LinearMap.id : M →ₗ[R] M))) := by
    apply tensor_hom_ext
    intro c m
    change tmul R (boundaryMap f n (boundaryProjectionTerm C (n+1) c)) (g.hom m) =
      tmul R (boundaryProjectionTerm D (n+1) ((f.f (n+1)).hom c)) (g.hom m)
    apply congrArg (fun b => tmul R b (g.hom m))
    apply Subtype.ext
    exact (P103.Ch10.HomologySequence.comm_apply f (n+1) n c).symm
  apply S'.kernelIso.injective
  apply Subtype.ext
  change (S'.kernelIso (T.map P P' (ModuleCat.ofHom (homologyMap f n)) g
    (S.β (homologyClass _ (n+1) z)))).val =
    (S'.kernelIso (S'.β (homologyClass _ (n+1)
      (cyclesMap (tensorFirstMap f M ≫ tensorSecondMap D g.hom) (n+1) z)))).val
  exact (torKernelIdentification_natural f M M' g n P P' T S.kernelIso S'.kernelIso
    S.kernelIso_canonical S'.kernelIso_canonical _).trans
    ((congrArg (tensorMap (boundaryMap f n) g.hom) (beta_class_formula S z)).trans
      ((LinearMap.congr_fun hh z.val).trans
        (beta_class_formula S' (cyclesMap
          (tensorFirstMap f M ≫ tensorSecondMap D g.hom) (n+1) z)).symm))

/-- The universal coefficient sequences with their naturality in both variables. -/
theorem universal_coefficients : universal_coefficientsType.{u,v,w} := by
  intro R _
  classical
  let Z (C : Complex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C) (M : ModuleCat.{w} R) :=
    Classical.choice (zeroSequence_exists C hC M)
  let S (C : Complex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C) (M : ModuleCat.{w} R)
      (n : ℕ) (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n))) :=
    Classical.choice (positiveSequence_exists C hC M n P)
  refine ⟨⟨Z, S, ?_, ?_⟩⟩
  · intro C D hC hD f M M' g
    exact alpha_natural f M M' g 0 (Z C hC M).α (Z D hD M').α
      (Z C hC M).α_formula (Z D hD M').α_formula
  · intro C D hC hD f M M' g n P P' T
    exact ⟨alpha_natural f M M' g (n+1) (S C hC M n P).α (S D hD M' n P').α
      (S C hC M n P).α_formula (S D hD M' n P').α_formula,
      beta_natural f M M' g n P P' T (S C hC M n P) (S D hD M' n P')⟩


/-- The actual sequence at degree zero, including its right arrow. -/
theorem zero_sequence_exact : zero_sequence_exactType.{u,v,w} := by
  intro R _ C M S P
  refine ⟨S.bijective_α.1, ?_, ?_⟩
  · intro x
    constructor
    · intro _
      exact S.bijective_α.2 x
    · intro _
      rfl
  · letI := S.zero_tor P
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-- The degree-zero tail is natural because its target is zero. -/
theorem zero_tail_natural : zero_tail_naturalType.{u,v,w} := by
  intro R _ C D f M M' g S S' P P' T
  ext x
  change (T.map P P' 0 g) 0 = 0
  exact map_zero _

/-- Both arrows respect the natural scalar actions over a commutative ring. -/
theorem scalar_compatibility : scalar_compatibilityType.{u,v,w} := by
  intro K _ U C hC M
  constructor
  · intro r
    simpa only [P103.Ch11.TorExactSequences.tensorFirstMap_id, Category.id_comp,
      P103.Ch10.Complexes.homologyMap_id] using
      U.natural_zero C C hC hC (𝟙 C) M M (scalarMap M r)
  · intro n P T
    constructor
    · intro r
      simpa only [P103.Ch11.TorExactSequences.tensorFirstMap_id, Category.id_comp,
        P103.Ch10.Complexes.homologyMap_id] using
        (U.natural_positive C C hC hC (𝟙 C) M M (scalarMap M r) n P P T).1
    · intro r x
      have hh := LinearMap.congr_fun
        (U.natural_positive C C hC hC (𝟙 C) M M (scalarMap M r) n P P T).2 x
      change (U.positive C hC M n P).β
          (homologyMap (tensorSecondMap C (scalarMap M r).hom) (n+1) x) =
        T.map P P (𝟙 _) (scalarMap M r) ((U.positive C hC M n P).β x)
      simpa only [LinearMap.comp_apply, P103.Ch11.TorExactSequences.tensorFirstMap_id,
        Category.id_comp, P103.Ch10.Complexes.homologyMap_id, ModuleCat.ofHom_id] using hh.symm

end
end P103.Ch11.UniversalCoefficientsHomology
