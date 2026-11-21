import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LieExtensionOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.LieHochschildSerre

noncomputable section

open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes

namespace AdvancedHomologicalAlgebra.LieHochschildSerre.Original

universe u v w a b c s t r

attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

section Quotients

variable {R : Type u} [Ring R]
  {A : CochainComplex (ModuleCat.{s} R) ℕ} {B : CochainComplex (ModuleCat.{t} R) ℕ}
  {C : CochainComplex (ModuleCat.{r} R) ℕ}

theorem CochainMap.induced (f : CochainMap A B) :
    Induced f.term f.homology :=
  fun n z => ⟨f.onCycles n z, rfl, f.homology_class n z⟩

theorem CochainMap.homology_square {D : CochainComplex (ModuleCat.{a} R) ℕ}
    (f : CochainMap A B) (g : CochainMap B D) (f' : CochainMap A C) (g' : CochainMap C D)
    (h : ∀ n x, g.term n (f.term n x) = g'.term n (f'.term n x)) (n : ℕ) :
    (g.homology n).comp (f.homology n) = (g'.homology n).comp (f'.homology n) := by
  apply (cycleBoundaries A n).quot_hom_ext
  intro z
  change g.homology n (f.homology n (homologyClass A n z)) =
    g'.homology n (f'.homology n (homologyClass A n z))
  simp only [CochainMap.homology_class]
  exact congrArg (homologyClass D n) (Subtype.ext (h n z.val))

theorem CochainMap.homology_ofHom {B : CochainComplex (ModuleCat.{s} R) ℕ}
    (f : A ⟶ B) (n : ℕ) : (CochainMap.ofHom f).homology n = homologyMap f n := rfl

end Quotients

section Exterior

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}

private theorem coefficient_action (y : g) (m : (underlying k g).obj M) :
    coefficientRepresentation k g M y m = inclusion k g y • (show M from m) := rfl

@[simp] theorem exteriorEquiv_apply (e : M ≃ₗ[U k g] N)
    (n : ℕ) (t : CE.W k g n →ₗ[k] (underlying k g).obj M) (z : CE.W k g n) :
    exteriorEquiv e n t z = e (t z) := rfl

@[simp] theorem exteriorEquiv_symm_apply (e : M ≃ₗ[U k g] N)
    (n : ℕ) (t : CE.W k g n →ₗ[k] (underlying k g).obj N) (z : CE.W k g n) :
    (exteriorEquiv e n).symm t z = e.symm (t z) := rfl

variable {N : ModuleCat.{max u v w} (U k g)}

private theorem original_formula (D : CochainTheory.{u,v,w} k g) (e : M ≃ₗ[U k g] N) :
    IsCEDifferential (coefficientRepresentation k g M) (differential D e) := by
  intro n t x
  change (exteriorEquiv e (n+1)).symm
    (D.d N n (exteriorEquiv e n t)) (CE.wedge k g (n+1) x) = _
  rw [exteriorEquiv_symm_apply, D.formula]
  change e.symm (_ + _) = _
  rw [map_add]
  congr 1
  · simp only [coefficient_action, exteriorEquiv_apply, map_sum, map_zsmul, map_smul,
      LinearEquiv.symm_apply_apply]
  · cases n <;> simp only [CE.cochainBracketSum, exteriorEquiv_apply, map_zero, map_sum,
      map_zsmul, LinearEquiv.symm_apply_apply]

theorem exterior_transport (D : CochainTheory.{u,v,w} k g) (e : M ≃ₗ[U k g] N) :
    ExteriorTransport D e :=
  ⟨original_formula D e, fun _ _ _ => rfl, fun _ _ _ => rfl,
    exteriorHomologyEquiv D e, (exteriorLiftMap D e).induced,
    ((exteriorLiftMap D e).inverse _ (fun _ => rfl)).induced⟩

end Exterior


section CommonLift

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)} {P : ModuleCat.{c} (U k g)}

theorem common_sequence_exact : CommonSequenceExact.{u,v,w,a,b,c} M N P := by
  intro i p h hi hp
  exact ModuleCat.shortComplexOfConj_shortExact _ _ _ _ _ h hi hp

end CommonLift

section Boundaries

variable {k : Type u} [Field k]
  {A : CochainComplex (ModuleCat.{a} k) ℕ}
  {B : CochainComplex (ModuleCat.{b} k) ℕ}
  {C : CochainComplex (ModuleCat.{c} k) ℕ}
  {A' B' C' : CochainComplex (ModuleCat.{s} k) ℕ}
  (i : CochainMap A B) (p : CochainMap B C)
  (i' : A' ⟶ B') (p' : B' ⟶ C')
  (eA : CochainMap A A') (eB : CochainMap B B') (eC : CochainMap C C')
  (eAt : ∀ n, A.X n ≃ₗ[k] A'.X n)
  (eBt : ∀ n, B.X n ≃ₗ[k] B'.X n)
  (eCt : ∀ n, C.X n ≃ₗ[k] C'.X n)
  (eAh : ∀ n, Homology A n ≃ₗ[k] Homology A' n)
  (eCh : ∀ n, Homology C n ≃ₗ[k] Homology C' n)
  (δ : ∀ n, Homology C' n →ₗ[k] Homology A' (n+1))

theorem connector_transport :
    ConnectorTransport i p i' p' eA eB eC eAt eBt eCt eAh eCh δ := by
  intro hA hB hC heA heC hi hp hex hδ n
  have ha (j : ℕ) : Function.Bijective (eA.term j) := by
    rw [hA j]
    exact (eAt j).bijective
  have hb (j : ℕ) : Function.Bijective (eB.term j) := by
    rw [hB j]
    exact (eBt j).bijective
  have hc (j : ℕ) : Function.Bijective (eC.term j) := by
    rw [hC j]
    exact (eCt j).bijective
  obtain ⟨hi', he', hp'⟩ := hex n
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x y h
      exact (ha n).1 (hi' ((hi n x).symm.trans ((congrArg (eB.term n) h).trans (hi n y))))
    · intro y
      have hz : (p'.f n).hom (eB.term n y) = 0 ↔ p.term n y = 0 := by
        rw [← hp n y]
        exact (map_eq_zero_iff _ (hc n).1)
      rw [← hz, he' (eB.term n y)]
      constructor
      · rintro ⟨x', hx'⟩
        obtain ⟨x, rfl⟩ := (ha n).2 x'
        exact ⟨x, (hb n).1 ((hi n x).trans hx')⟩
      · rintro ⟨x, rfl⟩
        exact ⟨eA.term n x, (hi n x).symm⟩
    · intro z
      obtain ⟨y', hy'⟩ := hp' (eC.term n z)
      obtain ⟨y, rfl⟩ := (hb n).2 y'
      exact ⟨y, (hc n).1 ((hp n y).trans hy')⟩
  · intro z y x hpy hix
    obtain ⟨z', hz', hzc⟩ := heC n z
    obtain ⟨x', hx', hxc⟩ := heA (n+1) x
    apply (eAh (n+1)).injective
    change eAh (n+1) ((eAh (n+1)).symm (δ n (eCh n (homologyClass C n z)))) =
      eAh (n+1) (homologyClass A (n+1) x)
    rw [LinearEquiv.apply_symm_apply]
    change eCh n (homologyClass C n z) = homologyClass C' n z' at hzc
    change eAh (n+1) (homologyClass A (n+1) x) = homologyClass A' (n+1) x' at hxc
    rw [hzc, hxc]
    exact hδ n z' (eB.term n y) x'
      ((hp n y).symm.trans ((congrArg (eC.term n) hpy).trans hz'.symm))
      (by rw [hx', ← hi, hix, eB.comm])

end Boundaries


section Naturality

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (D : CochainTheory.{u,v,w} k g)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}
  {M' N' : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] M') (e' : N ≃ₗ[U k g] N')
  (f : M →ₗ[U k g] N)

theorem ce_map_apply {X Y : ModuleCat.{max u v w} (U k g)} (a : X ⟶ Y)
    (n : ℕ) (t : CE.W k g n →ₗ[k] (underlying k g).obj X) (z : CE.W k g n) :
    (show CE.W k g n →ₗ[k] (underlying k g).obj Y from
      ((D.functor.map a).f n).hom t) z = a (t z) := by
  change a (t (exteriorPower.map n (LinearMap.id (R := k)) z)) = _
  rw [exteriorPower.map_id, LinearMap.id_apply]

def exteriorMap : CochainMap (complex D e) (complex D e') :=
  ((exteriorLiftMap D e').inverse _ (fun _ => rfl)).comp
    ((CochainMap.ofHom (D.functor.map (conjugateMap e e' f))).comp (exteriorLiftMap D e))

theorem exteriorMap_apply (n : ℕ)
    (t : CE.W k g n →ₗ[k] (underlying k g).obj M) (z : CE.W k g n) :
    (show CE.W k g n →ₗ[k] (underlying k g).obj N from
      (exteriorMap D e e' f).term n t) z = f (t z) := by
  change (exteriorEquiv e' n).symm
    (((D.functor.map (conjugateMap e e' f)).f n).hom (exteriorEquiv e n t)) z = _
  rw [exteriorEquiv_symm_apply, ce_map_apply, exteriorEquiv_apply]
  change e'.symm (e' (f (e.symm (e (t z))))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem exteriorMap_term (n : ℕ) : (exteriorMap D e e' f).term n = exteriorPost f n := by
  apply LinearMap.ext
  intro t
  apply LinearMap.ext
  intro z
  exact exteriorMap_apply D e e' f n t z

theorem exteriorMap_square (n : ℕ) (t : (complex D e).X n) :
    exteriorEquiv e' n ((exteriorMap D e e' f).term n t) =
      ((D.functor.map (conjugateMap e e' f)).f n).hom (exteriorEquiv e n t) :=
  (exteriorEquiv e' n).apply_symm_apply _

theorem exterior_naturality : ExteriorNaturality D e e' f := by
  refine ⟨exteriorMap D e e' f, exteriorMap_term D e e' f, exteriorMap_square D e e' f,
    exteriorHomologyEquiv D e, exteriorHomologyEquiv D e',
    (exteriorLiftMap D e).induced, (exteriorLiftMap D e').induced, ?_⟩
  intro n
  exact CochainMap.homology_square (exteriorMap D e e' f) (exteriorLiftMap D e')
    (exteriorLiftMap D e) (CochainMap.ofHom (D.functor.map (conjugateMap e e' f)))
    (exteriorMap_square D e e' f) n

end Naturality

section Augmentations

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  {X : Type r} [Category X]
  (T : X ⥤ ModuleCat.{max u v w} (U k g)) (D : CochainTheory.{u,v,w} k g)
  {F V : X ⥤ ModuleCat.{max u v w} k} (unit : F ⟶ V)
  (evaluate : ∀ M : X, F.obj M → (underlying k g).obj (T.obj M))
  (J : V ≅ T ⋙ D.cohomology 0)

theorem augmentation_transport :
    AugmentationTransport.{u,v,w,a,r,_} T D unit evaluate J := by
  intro hJ M M₀ e m
  let H := exteriorHomologyEquiv D e
  let f := (exteriorLiftMap D e).inverse _ (fun _ => rfl)
  obtain ⟨z, hz, hc⟩ := hJ M m
  refine ⟨f.onCycles 0 z, ?_, ?_⟩
  · change (exteriorEquiv e 0).symm z.val (CE.wedge k g 0 Fin.elim0) = _
    rw [exteriorEquiv_symm_apply, hz]
  · change (H 0).symm ((J.hom.app M).hom ((unit.app M).hom m)) = _
    rw [hc]
    exact f.homology_class 0 z

end Augmentations


section Ideal

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g) {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (Dh : CochainTheory.{u,v,w} k h) (e : M ≃ₗ[U k g] N)
  (Q : ℕ → ModuleCat.{max u v w} (U k (g ⧸ h)))
  (J : ∀ n, (underlying k (g ⧸ h)).obj (Q n) ≃ₗ[k]
    Homology (Dh.complex (restrictOriginal h N)) n)

theorem ideal_action_transport : IdealActionTransport h Dh e Q J := by
  intro hj n y z
  let E := exteriorLiftMap Dh (restrictEquiv h e)
  let B := E.inverse _ (fun _ => rfl)
  obtain ⟨t, ht, hc⟩ := hj n y (E.onCycles n z)
  refine ⟨B.onCycles n t, ?_, ?_⟩
  · intro x
    change e.symm (t.val (CE.wedge k h n x)) = _
    rw [ht]
    change e.symm (inclusion k g y • (e (z.val (CE.wedge k h n x))) -
      ∑ i : Fin n, e (z.val (CE.wedge k h n (Function.update x i ⁅y, x i⁆)))) =
      inclusion k g y • (show M from z.val (CE.wedge k h n x)) -
        ∑ i : Fin n, (show M from z.val (CE.wedge k h n (Function.update x i ⁅y, x i⁆)))
    simp only [map_sub, map_smul, map_sum, LinearEquiv.symm_apply_apply]
  · let H := exteriorHomologyEquiv Dh (restrictEquiv h e) n
    change (J n).symm (H (homologyClass _ n (B.onCycles n t))) =
      _ • (J n).symm (H (homologyClass _ n z))
    have hl : H (homologyClass _ n (B.onCycles n t)) = homologyClass _ n t := by
      rw [← B.homology_class]
      exact H.apply_symm_apply _
    rw [hl]
    exact hc

end Ideal

section Rebase

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
  {V : Type a} [AddCommGroup V] [Module k V]
  (N : ModuleCat.{b} (U k L)) (e : V ≃ₗ[k] (underlying k L).obj N)

theorem rebase_scalar_action : RebaseScalarAction N e := by
  intro r x
  change e.symm (r • e x) = r • x
  rw [← e.map_smul, LinearEquiv.symm_apply_apply]

end Rebase


section OriginalEdges

open LieQuotientAction

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  (Dg : CochainTheory.{u,v,w} k g) (Dh : CochainTheory.{u,v,w} k h)
  (Dq : CochainTheory.{u,v,w} k (g ⧸ h)) (E : EdgeCochains h Dg Dh Dq)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N) (j : InvariantComparison h (M := M) (N := N))

def originalInflation : CochainMap (invariantComplex h Dq j) (complex Dg e) :=
  ((exteriorLiftMap Dg e).inverse _ (fun _ => rfl)).comp
    ((CochainMap.ofHom (E.inflation.app N)).comp (exteriorLiftMap Dq (rebaseEquiv _ j)))

def originalRestriction : CochainMap (complex Dg e) (idealComplex h Dh e) :=
  ((exteriorLiftMap Dh (restrictEquiv h e)).inverse _ (fun _ => rfl)).comp
    ((CochainMap.ofHom (E.restriction.app N)).comp (exteriorLiftMap Dg e))

theorem edge_transport : EdgeTransport h Dg Dh Dq E e j := by
  intro hj
  let I := originalInflation h Dg Dh Dq E e j
  let R := originalRestriction h Dg Dh Dq E e
  refine ⟨I, R, ?_, ?_, ?_, ?_⟩
  · intro n t x
    change (exteriorEquiv e n).symm
      (((E.inflation.app N).f n).hom (exteriorEquiv (rebaseEquiv _ j) n t))
        (CE.wedge k g n x) = _
    rw [exteriorEquiv_symm_apply, E.inflation_formula, exteriorEquiv_apply]
    change e.symm ((show (idealInvariants.{u,v,w} h).obj N from
      j (t (CE.wedge k (g ⧸ h) n (quotientMap k g h ∘ x)))) (1 : U k (g ⧸ h))) = _
    rw [hj, LinearEquiv.symm_apply_apply]
  · intro n t x
    change (exteriorEquiv (restrictEquiv h e) n).symm
      (((E.restriction.app N).f n).hom (exteriorEquiv e n t)) (CE.wedge k h n x) = _
    rw [exteriorEquiv_symm_apply, E.restriction_formula, exteriorEquiv_apply]
    exact e.symm_apply_apply _
  · intro n
    exact CochainMap.homology_square I (exteriorLiftMap Dg e)
      (exteriorLiftMap Dq (rebaseEquiv _ j)) (CochainMap.ofHom (E.inflation.app N))
      (fun m t => (exteriorEquiv e m).apply_symm_apply _) n
  · intro n
    exact CochainMap.homology_square R (exteriorLiftMap Dh (restrictEquiv h e))
      (exteriorLiftMap Dg e) (CochainMap.ofHom (E.restriction.app N))
      (fun m t => (exteriorEquiv (restrictEquiv h e) m).apply_symm_apply _) n

end OriginalEdges

section ResolutionFormula

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (D : CochainTheory.{u,v,w} k g) (e : M ≃ₗ[U k g] N)

local instance : IsScalarTower k (U k g) ((underlying k g).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem resolution_differential : ResolutionDifferential D e := by
  intro B C n
  apply LinearMap.ext
  intro t
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change differential D e n t (CE.wedge k g (n+1) x) =
    C.differential n t (CE.wedge k g (n+1) x)
  rw [original_formula D e, C.formula]
  rfl

/-- The differential is the one obtained from the actual HA-A06 resolution
by evaluation at the unit tensor, in the original carrier. -/
theorem differential_eq_coboundary (n : ℕ) :
    differential D e n =
      CE.coboundary k g ((underlying k g).obj M) (CE.boundary k g) n := by
  apply LinearMap.ext
  intro t
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change differential D e n t (CE.wedge k g (n+1) x) =
    CE.coboundary k g ((underlying k g).obj M) (CE.boundary k g) n t (CE.wedge k g (n+1) x)
  rw [original_formula D e, CE.coboundary_formula _ _ _ _ (CE.boundary_formula k g)]
  rfl

end ResolutionFormula


private theorem exact_conjugate {k : Type u} [Field k]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*}
    [AddCommGroup X₁] [Module k X₁] [AddCommGroup X₂] [Module k X₂]
    [AddCommGroup X₃] [Module k X₃] [AddCommGroup Y₁] [Module k Y₁]
    [AddCommGroup Y₂] [Module k Y₂] [AddCommGroup Y₃] [Module k Y₃]
    {f : X₁ →ₗ[k] X₂} {g : X₂ →ₗ[k] X₃} {f' : Y₁ →ₗ[k] Y₂} {g' : Y₂ →ₗ[k] Y₃}
    (e₁ : X₁ ≃ₗ[k] Y₁) (e₂ : X₂ ≃ₗ[k] Y₂) (e₃ : X₃ ≃ₗ[k] Y₃)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (hg : ∀ x, e₃ (g x) = g' (e₂ x))
    (hex : Function.Exact f' g') : Function.Exact f g := by
  intro x
  have hz : g x = 0 ↔ g' (e₂ x) = 0 := by
    rw [← hg x]
    exact (map_eq_zero_iff _ e₃.injective).symm
  rw [hz, hex]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := e₁.surjective y
    exact ⟨z, e₂.injective ((hf z).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e₁ y, (hf y).symm⟩

section Spectrum

open GrothendieckSpectralSequence GrothendieckEdges
open HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.Comparison

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]
  {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
  {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
  {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
  {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
  (J : CEComparison h Dg Dh Dq E P O)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N)

theorem finite_filtration : FiniteFiltration h J e := by
  intro n
  let X := (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v w} (U k g)) 0).obj N
  constructor
  · intro p _ hx
    obtain ⟨x, rfl⟩ := hx
    refine ⟨((sequenceDiagram h (P := P) (N := N)).down p n).hom x, ?_⟩
    apply congrArg (targetCoordinates h J e n)
    exact congrArg (fun f => f.hom x) (P.down_inclusion X p n)
  · obtain ⟨l, r, hl, hr⟩ := P.finite X (n : ℤ)
    refine ⟨l, r, ?_, ?_⟩
    · intro p hp
      let f := (sequenceDiagram h (P := P) (N := N)).inclusion p (n : ℤ)
      have : IsIso f := hl p hp
      exact LinearMap.range_eq_top.mpr
        ((targetCoordinates h J e n).surjective.comp (asIso f).toLinearEquiv.surjective)
    · intro p hp
      let : Subsingleton ((sequenceDiagram h (P := P) (N := N)).step p (n : ℤ)) :=
        ModuleCat.isZero_iff_subsingleton.1 (hr p hp)
      apply le_antisymm _ bot_le
      rintro _ ⟨x, rfl⟩
      rw [show x = 0 from Subsingleton.elim x 0, map_zero]
      exact Submodule.zero_mem _

open CategoryTheory.Limits in
theorem graded_convergence : GradedConvergence h J e := by
  intro n
  let Y := (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v w} (U k g)) 0).obj N
  let S := sequenceDiagram h (P := P) (N := N)
  obtain ⟨R, hR⟩ := P.convergence Y (n : ℤ)
  refine ⟨R, ?_⟩
  intro r hr p
  obtain ⟨hd, ⟨E⟩⟩ := hR r hr p
  let d := S.down p (n : ℤ)
  let L : S.page r p (n : ℤ) ≃ₗ[k] ((cokernel d : ModuleCat k) : Type _) := E.toLinearEquiv
  let a := S.inclusion p (n : ℤ)
  let b := S.inclusion (p+1) (n : ℤ)
  let T := targetCoordinates h J e n
  let f : S.step p (n : ℤ) →ₗ[k] Homology (complex Dg e) n :=
    T.toLinearMap.comp a.hom
  let g' : S.step (p+1) (n : ℤ) →ₗ[k] Homology (complex Dg e) n :=
    T.toLinearMap.comp b.hom
  let dₗ : S.step (p+1) (n : ℤ) →ₗ[k] S.step p (n : ℤ) := d.hom
  have hcomp : f.comp dₗ = g' := by
    apply LinearMap.ext
    intro x
    apply congrArg T
    exact congrArg (fun m => m.hom x) (P.down_inclusion Y p (n : ℤ))
  have ha : Function.Injective a.hom :=
    (ModuleCat.mono_iff_injective a).1 (P.inclusion_mono Y p (n : ℤ))
  let F := LinearEquiv.ofInjective f (T.injective.comp ha)
  have hmap : (LinearMap.range d.hom).map F.toLinearMap =
      (LinearMap.range g').comap (LinearMap.range f).subtype := by
    apply Submodule.ext
    intro z
    rw [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨x, ⟨y, rfl⟩, hzy⟩
      exact ⟨y, (LinearMap.congr_fun hcomp y).symm.trans (congrArg Subtype.val hzy)⟩
    · rintro ⟨y, hzy⟩
      exact ⟨d.hom y, ⟨y, rfl⟩, Subtype.ext ((LinearMap.congr_fun hcomp y).trans hzy)⟩
  let Q : ((cokernel d : ModuleCat k) : Type _) ≃ₗ[k]
      (S.step p (n : ℤ) ⧸ LinearMap.range dₗ) :=
    (ModuleCat.cokernelIsoRangeQuotient d).toLinearEquiv
  let K : (S.step p (n : ℤ) ⧸ LinearMap.range dₗ) ≃ₗ[k] targetGraded h J e p n :=
    Submodule.Quotient.equiv _ _ F hmap
  exact ⟨hd, ⟨L.trans (Q.trans K)⟩⟩

theorem mem_fixedClasses (n : ℕ) (x : Homology (idealComplex h Dh e) n) :
    x ∈ fixedClasses h J e n ↔
      ∀ y : g ⧸ h, coefficientRepresentation k (g ⧸ h) (idealDerived h (N := N) n) y
        (idealCoordinates h J e n x) = 0 :=
  J.quotientInclusion.range _ _

theorem fixed_classes_formula : FixedClassesFormula h J e := by
  intro n x
  rw [mem_fixedClasses h J e]
  apply forall_congr'
  intro y
  let A := rebaseEquiv _ (idealCoordinates h J e n)
  change inclusion k (g ⧸ h) y • A (show idealCoefficient h J e n from x) = 0 ↔ _
  rw [← A.map_smul]
  exact map_eq_zero_iff _ A.injective

variable (j : InvariantComparison h (M := M) (N := N))

open CategoryTheory.Functor

theorem row_augmentation (hj : InvariantEvaluation h e j) : RowAugmentation h J e j := by
  intro m
  let f := (exteriorLiftMap Dh (restrictEquiv h e)).inverse _ (fun _ => rfl)
  obtain ⟨z, hz, hc⟩ := J.ideal_augmentation N (j m)
  refine ⟨f.onCycles 0 z, ?_, ?_⟩
  · change e.symm (z.val (CE.wedge k h 0 Fin.elim0)) = _
    rw [hz]
    have he := hj m
    change (show (idealInvariants.{u,v,w} h).obj N from j m) (1 : U k (g ⧸ h)) = e m.val at he
    exact (congrArg e.symm he).trans (e.symm_apply_apply _)
  · change (exteriorHomologyEquiv Dh (restrictEquiv h e) 0).symm
      (((J.ideal 0).hom.app N).hom ((O.degreeZeroF.hom.app N).hom (j m))) = _
    rw [O.degreeZeroF_hom]
    change (exteriorHomologyEquiv Dh (restrictEquiv h e) 0).symm
      (((J.ideal 0).hom.app N).hom
        (((whiskerRight (degreeZeroUnit (idealInvariants.{u,v,w} h))
          (underlying k (g ⧸ h))).app N).hom (j m))) = _
    rw [hc]
    exact f.homology_class 0 z

theorem row_axis : RowAxis h J e j := by
  intro n x
  let H := exteriorHomologyEquiv Dq (rebaseEquiv _ (idealCoordinates h J e 0)) n
  let K := exteriorHomologyEquiv Dq (rebaseEquiv _ j) n
  change H (H.symm ((J.secondPageIso h n 0).hom.app N x)) =
    homologyMap (Dq.functor.map (O.degreeZeroF.hom.app N)) n
      (K (K.symm ((J.rowIso h n).hom.app N ((rowIndexIso _ _ P n).hom.app N x))))
  rw [H.apply_symm_apply, K.apply_symm_apply]
  have hn := (J.quotient n).hom.naturality (O.degreeZeroF.hom.app N)
  simp only [CEComparison.secondPageIso, CEComparison.rowIso, O.row_identification,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, ModuleCat.comp_apply]
  exact congrArg (fun f => f.hom ((O.rowPage n).hom.app N ((rowIndexIso _ _ P n).hom.app N x))) hn

theorem column_axis : ColumnAxis h J e := by
  intro n x
  let Q := idealDerived h (N := N) n
  let A := rebaseEquiv Q (idealCoordinates h J e n)
  let H := exteriorHomologyEquiv Dq A 0
  let f := (exteriorLiftMap Dq A).inverse _ (fun _ => rfl)
  let m : (quotientInvariants.{u,v,w} h).obj Q :=
    (O.columnPage n).hom.app N ((columnIndexIso _ _ P n).hom.app N x)
  obtain ⟨z, hz, hc⟩ := J.quotient_augmentation Q m
  refine ⟨f.onCycles 0 z, ?_, ?_⟩
  · change (idealCoordinates h J e n).symm (z.val (CE.wedge k (g ⧸ h) 0 Fin.elim0)) =
      (idealCoordinates h J e n).symm ((J.quotientInclusion.evaluation.app Q).hom m)
    rw [hz, J.quotientInclusion.formula]
  · change H.symm ((J.secondPageIso h 0 n).hom.app N x) = _
    rw [← f.homology_class]
    change H.symm ((J.secondPageIso h 0 n).hom.app N x) = H.symm (homologyClass _ 0 z)
    apply congrArg H.symm
    refine Eq.trans ?_ hc
    simp only [CEComparison.secondPageIso, O.column_identification, Iso.trans_hom,
      NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app, Iso.symm_hom,
      O.degreeZero_hom, ModuleCat.comp_apply, m]
    rfl

theorem filtered_edge_equations
    (inf : CochainMap (invariantComplex h Dq j) (complex Dg e))
    (res : CochainMap (complex Dg e) (idealComplex h Dh e))
    (H : ExteriorEdges h Dg Dh Dq E e j inf res) :
    FilteredEdgeEquations h J e j inf := by
  constructor
  · intro n x
    let G := exteriorHomologyEquiv Dg e n
    let Q := exteriorHomologyEquiv Dq (rebaseEquiv _ j) n
    let F := idealInvariants.{u,v,w} h
    let V := quotientInvariants.{u,v,w} h
    apply G.injective
    calc
      G (inf.homology n (rowCoordinates h J j n x)) =
          homologyMap (E.inflation.app N) n (Q (rowCoordinates h J j n x)) :=
        LinearMap.congr_fun (H.2.2.1 n) _
      _ = homologyMap (E.inflation.app N) n
          ((J.quotient n).hom.app (F.obj N) ((O.rowPage n).hom.app N x)) := by
        change homologyMap (E.inflation.app N) n (Q (Q.symm _)) = _
        rw [Q.apply_symm_apply]
        rfl
      _ = (J.ambient n).hom.app N ((derivedFirstEdge F V P n).app N ((O.rowPage n).hom.app N x)) :=
        congrArg (fun m => m.hom ((O.rowPage n).hom.app N x)) (J.inflation_edge N n)
      _ = G (targetCoordinates h J e n ((O.filtered N).row n x)) := by
        change (J.ambient n).hom.app N ((derivedFirstEdge F V P n).app N
          ((O.rowPage n).hom.app N x)) = G (G.symm _)
        rw [G.apply_symm_apply]
        exact congrArg ((J.ambient n).hom.app N)
          (congrArg (fun m => m.hom x) (O.first_comparison n N))
  · intro n x
    let G := exteriorHomologyEquiv Dg e n
    let K := fixedClassEquiv h J e n
    apply K.symm.injective
    change K.symm (K ((J.restrictToInvariants h n).app N (G (targetCoordinates h J e n x)))) =
      K.symm (K ((O.columnPage n).hom.app N ((O.filtered N).column n x)))
    rw [K.symm_apply_apply, K.symm_apply_apply]
    change (J.restrictToInvariants h n).app N (G (G.symm _)) = _
    rw [G.apply_symm_apply]
    have ha (y : (sequenceDiagram h (P := P) (N := N)).target (n : ℤ)) :
        (J.ambient n).inv.app N ((J.targetIso h n).hom.app N y) =
          (O.objectCase.targetIso n).hom.app N y := by
      change (J.ambient n).inv.app N ((J.ambient n).hom.app N
        ((O.objectCase.targetIso n).hom.app N y)) = _
      exact ((J.ambient n).app N).toLinearEquiv.symm_apply_apply _
    change (classicalColumn _ _ (O.truncation n) O.degreeZero).app N
      ((J.ambient n).inv.app N ((J.targetIso h n).hom.app N x)) = _
    rw [ha]
    exact congrArg (fun m => m.hom x) (O.second_comparison n N)

theorem five_terms_transport
    (inf : CochainMap (invariantComplex h Dq j) (complex Dg e))
    (res : CochainMap (complex Dg e) (idealComplex h Dh e)) :
    FiveTermsTransport h J e j inf res := by
  intro H hi hr
  let G := exteriorHomologyEquiv Dg e
  let Q := exteriorHomologyEquiv Dq (rebaseEquiv _ j)
  let I := exteriorHomologyEquiv Dh (restrictEquiv h e)
  let K := fixedClassEquiv h J e
  constructor
  · intro n
    apply LinearMap.ext
    intro x
    apply (I n).injective
    change I n ((idealCoordinates h J e n).symm
      ((J.quotientInclusion.evaluation.app (idealDerived h (N := N) n)).hom
        ((J.restrictToInvariants h n).app N (G n x)))) = I n (res.homology n x)
    have hx := LinearMap.congr_fun (hr n) x
    change I n (res.homology n x) = homologyMap (E.restriction.app N) n (G n x) at hx
    rw [hx]
    change I n ((I n).symm (((J.ideal n).app N).hom
      ((J.quotientInclusion.evaluation.app (idealDerived h (N := N) n)).hom
        ((J.restrictToInvariants h n).app N (G n x))))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (fun f => f.hom (((J.ambient n).app N).inv (G n x)))
      (J.restriction_edge N n)).symm.trans (by rfl) |>.trans (by
        change homologyMap (E.restriction.app N) n
          (((J.ambient n).app N).hom (((J.ambient n).app N).inv (G n x))) = _
        rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply])
  have hf (n : ℕ) (x : Homology (invariantComplex h Dq j) n) :
      G n (inf.homology n x) = homologyMap (E.inflation.app N) n (Q n x) :=
    LinearMap.congr_fun (hi n) x
  have hg (x : Homology (complex Dg e) 1) :
      (K 1).symm (restrictionEdge h J e 1 x) = (J.restrictToInvariants h 1).app N (G 1 x) :=
    (K 1).symm_apply_apply _
  have hd (x : fixedClasses h J e 1) :
      Q 2 (transgression h J e j x) = J.transgression h N ((K 1).symm x) :=
    (Q 2).apply_symm_apply _
  have hmono := (ModuleCat.mono_iff_injective _).mp H.mono
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply (Q 1).injective
    exact hmono ((hf 1 x).symm.trans ((congrArg (G 1) hxy).trans (hf 1 y)))
  · exact exact_conjugate (Q 1) (G 1) (K 1).symm (hf 1) hg
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp H.exact_f_g)
  · exact exact_conjugate (G 1) (K 1).symm (Q 2) hg hd
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp H.exact_g_d)
  · exact exact_conjugate (K 1).symm (Q 2) (G 2) hd (hf 2)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp H.exact_d_h)

end Spectrum


section Invariants

open LieQuotientAction

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g) {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N)

def invariantCarrierEquiv : Invariants h M ≃ₗ[k] Invariants h N := by
  let f := underlyingEquiv e
  have hf (m : (underlying k g).obj M) :
      f m ∈ Invariants h N ↔ m ∈ Invariants h M := by
    constructor
    · intro hm a
      apply e.injective
      change e (inclusion k g (a : g) • m) = e 0
      rw [e.map_smul, map_zero]
      exact hm a
    · intro hm a
      change inclusion k g (a : g) • e m = 0
      rw [← e.map_smul]
      exact (congrArg e (hm a)).trans (map_zero e)
  exact LinearEquiv.ofBijective
    ((f.toLinearMap.comp (Invariants h M).subtype).codRestrict _ (fun z => (hf z.val).2 z.property))
    ⟨fun _ _ he => Subtype.ext (f.injective (congrArg Subtype.val he)), by
      intro z
      obtain ⟨m, hm⟩ := f.surjective z.val
      have hz : m ∈ Invariants h M := (hf m).1 (hm ▸ z.property)
      exact ⟨⟨m, hz⟩, Subtype.ext hm⟩⟩

def invariantComparison : InvariantComparison h (M := M) (N := N) :=
  (invariantCarrierEquiv h e).trans (idealInvariantEquiv h N).symm

theorem invariant_evaluation : InvariantEvaluation h e (invariantComparison h e) := by
  intro z
  let j := invariantComparison.{u,v,w,a} h e
  change (idealInvariantEquiv h N (j z)).val = e z.val
  change ((idealInvariantEquiv h N)
    ((idealInvariantEquiv h N).symm (invariantCarrierEquiv h e z))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem invariant_comparison_action : InvariantAction h (invariantComparison h e) := by
  let j := invariantComparison.{u,v,w,a} h e
  have hj := invariant_evaluation h e
  intro y z
  let z' : rebase _ j :=
    inclusion k (g ⧸ h) (quotientMap k g h y) • (show rebase _ j from z)
  change z'.val = coefficientRepresentation k g M y z.val
  apply e.injective
  rw [← hj z']
  change (show (idealInvariants.{u,v,w} h).obj N from j z') (1 : U k (g ⧸ h)) = _
  have hsmul := (rebaseEquiv _ j).map_smul
    (inclusion k (g ⧸ h) (quotientMap k g h y)) (show rebase _ j from z)
  change (show (idealInvariants.{u,v,w} h).obj N from j z') =
    inclusion k (g ⧸ h) (quotientMap k g h y) •
      (show (idealInvariants.{u,v,w} h).obj N from j z) at hsmul
  rw [hsmul]
  change _ = e (inclusion k g y • (show M from z.val))
  rw [e.map_smul]
  let t : (idealInvariants.{u,v,w} h).obj N := j z
  change t (1 * inclusion k (g ⧸ h) (quotientMap k g h y)) =
    inclusion k g y • e z.val
  erw [one_mul, ← envelopingQuotient_inclusion, idealCoextend_apply]
  exact congrArg (inclusion k g y • ·) (hj z)

theorem invariant_transport : InvariantTransport h e :=
  ⟨invariantComparison h e, invariant_evaluation h e, invariant_comparison_action h e⟩

theorem invariant_naturality
    {M' : ModuleCat.{b} (U k g)} {N' : ModuleCat.{max u v w} (U k g)}
    (e' : M' ≃ₗ[U k g] N') (f : M →ₗ[U k g] M')
    (j : InvariantComparison h (M := M) (N := N))
    (j' : InvariantComparison h (M := M') (N := N')) :
    InvariantNaturality h e j e' f j' := by
  intro hj hj'
  let α := conjugateMap e e' f
  let β := (idealInvariants.{u,v,w} h).map α
  let A := rebaseEquiv _ j
  let B := rebaseEquiv _ j'
  let F := B.symm.toLinearMap.comp (β.hom.comp A.toLinearMap)
  have hF (z : Invariants h M) : j' (F z) = β (j z) := B.apply_symm_apply _
  refine ⟨F, fun z => ⟨?_, hF z⟩⟩
  apply e'.injective
  rw [← hj' (F z), hF z]
  change α ((show (idealInvariants.{u,v,w} h).obj N from j z) (1 : U k (g ⧸ h))) = _
  rw [hj z]
  change e' (f (e.symm (e z.val))) = e' (f z.val)
  rw [LinearEquiv.symm_apply_apply]

end Invariants


section NormalizedConnectors

open P103.Specs.Ch10.Comparison

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  {X : Type r} [Category X] [Abelian X]
  (T : X ⥤ ModuleCat.{max u v w} (U k g))
  (D : CochainTheory.{u,v,w} k g)
  (V : ℕ → X ⥤ ModuleCat.{max u v w} k)
  (δ : ∀ {S : ShortComplex X}, S.ShortExact → ∀ n : ℕ,
    (V n).obj S.X₃ ⟶ (V (n+1)).obj S.X₁)
  (J : ∀ n, V n ≅ (T ⋙ D.functor) ⋙ quotientHomology (.up ℕ) n)

theorem normalized_connectors :
    NormalizedConnectors.{u,v,w,a,b,c,r,_} T D V δ J := by
  intro H S hs A B C eA eB eC i p hi hp
  let I := exteriorMap D eA eB i
  let P := exteriorMap D eB eC p
  refine ⟨I, P, exteriorMap_term D eA eB i, exteriorMap_term D eB eC p, ?_⟩
  obtain ⟨hex, hδ⟩ := H hs
  exact connector_transport I P ((T ⋙ D.functor).map S.f) ((T ⋙ D.functor).map S.g)
    (exteriorLiftMap D eA) (exteriorLiftMap D eB) (exteriorLiftMap D eC)
    (exteriorEquiv eA) (exteriorEquiv eB) (exteriorEquiv eC)
    (exteriorHomologyEquiv D eA) (exteriorHomologyEquiv D eC)
    (fun n => ((J n).inv.app S.X₃ ≫ δ hs n ≫ (J (n+1)).hom.app S.X₁).hom)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (exteriorLiftMap D eA).induced (exteriorLiftMap D eC).induced
    (by
      intro n x
      change exteriorEquiv eB n (I.term n x) =
        ((D.functor.map (T.map S.f)).f n).hom (exteriorEquiv eA n x)
      rw [← hi]
      exact exteriorMap_square D eA eB i n x)
    (by
      intro n y
      change exteriorEquiv eC n (P.term n y) =
        ((D.functor.map (T.map S.g)).f n).hom (exteriorEquiv eB n y)
      rw [← hp]
      exact exteriorMap_square D eB eC p n y)
    hex hδ

end NormalizedConnectors


section NaturalCoordinates

open P103.Specs.Ch10.Comparison

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (D : CochainTheory.{u,v,w} k g)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}
  {X : Type r} [Category X]
  (T : X ⥤ ModuleCat.{max u v w} (U k g)) (V : X ⥤ ModuleCat.{max u v w} k)
  {X₁ X₂ : X} (α : X₁ ⟶ X₂) (n : ℕ) (J : V ≅ T ⋙ D.cohomology n)
  (e : M ≃ₗ[U k g] T.obj X₁) (e' : N ≃ₗ[U k g] T.obj X₂) (f : M →ₗ[U k g] N)

theorem natural_coordinate_apply (h : conjugateMap e e' f = T.map α) (x : V.obj X₁) :
    (exteriorMap D e e' f).homology n
      ((exteriorHomologyEquiv D e n).symm ((J.hom.app X₁).hom x)) =
      (exteriorHomologyEquiv D e' n).symm ((J.hom.app X₂).hom ((V.map α).hom x)) := by
  let K := exteriorMap D e e' f
  let H₁ := exteriorHomologyEquiv D e n
  let H₂ := exteriorHomologyEquiv D e' n
  have hK := CochainMap.homology_square K (exteriorLiftMap D e') (exteriorLiftMap D e)
    (CochainMap.ofHom (D.functor.map (conjugateMap e e' f))) (exteriorMap_square D e e' f) n
  have hx := LinearMap.congr_fun hK (H₁.symm ((J.hom.app X₁).hom x))
  change H₂ (K.homology n (H₁.symm ((J.hom.app X₁).hom x))) =
    homologyMap (D.functor.map (conjugateMap e e' f)) n
      (H₁ (H₁.symm ((J.hom.app X₁).hom x))) at hx
  rw [H₁.apply_symm_apply, h] at hx
  apply H₂.injective
  change H₂ (K.homology n (H₁.symm ((J.hom.app X₁).hom x))) =
    H₂ (H₂.symm ((J.hom.app X₂).hom ((V.map α).hom x)))
  rw [H₂.apply_symm_apply, hx]
  exact (congrArg (fun m => m.hom x) (J.hom.naturality α)).symm

theorem natural_coordinates : NaturalCoordinates D T V α n J e e' f := by
  intro h
  exact ⟨exteriorMap D e e' f, exteriorMap_term D e e' f,
    natural_coordinate_apply D T V α n J e e' f h⟩

end NaturalCoordinates


section SpectralNaturality

open GrothendieckSpectralSequence GrothendieckEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]
  {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
  {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
  {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
  {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
  (J : CEComparison h Dg Dh Dq E P O)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  {M' : ModuleCat.{b} (U k g)} {N' : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N) (e' : M' ≃ₗ[U k g] N') (f : M →ₗ[U k g] M')

theorem spectral_edge_naturality :
    SpectralEdgeNaturality h (O := O) e e' f := by
  let F := idealInvariants.{u,v,w} h
  let G := quotientInvariants.{u,v,w} h
  let S := objectSequence F G P
  let α := conjugateMap e e' f
  constructor
  · intro n
    let A := O.rowPage n
    let B := derivedFirstEdge F G P n
    let C := O.objectCase.targetIso n
    apply (cancel_mono (C.hom.app N')).mp
    calc
      ((S.map α).page 0 n n ≫ (O.filtered N').row n) ≫ C.hom.app N' =
          (S.map α).page 0 n n ≫ (A.hom.app N' ≫ B.app N') := by
        rw [Category.assoc, ← O.first_comparison n N']
      _ = A.hom.app N ≫ (F ⋙ rightValue G n).map α ≫ B.app N' := by
        rw [← Category.assoc]
        exact (congrArg (· ≫ B.app N') (A.hom.naturality α)).trans (Category.assoc _ _ _)
      _ = A.hom.app N ≫ B.app N ≫ (rightValue (F ⋙ G) n).map α := by
        rw [B.naturality]
      _ = (O.filtered N).row n ≫ C.hom.app N ≫ (rightValue (F ⋙ G) n).map α := by
        rw [← Category.assoc, O.first_comparison, Category.assoc]
      _ = ((O.filtered N).row n ≫ (S.map α).target n) ≫ C.hom.app N' := by
        rw [Category.assoc]
        exact congrArg ((O.filtered N).row n ≫ ·) (C.hom.naturality α).symm
  · intro n
    let A := O.objectCase.targetIso n
    let B := classicalColumn F G (O.truncation n) O.degreeZero
    let C := O.columnPage n
    apply (cancel_mono (C.hom.app N')).mp
    calc
      ((S.map α).target n ≫ (O.filtered N').column n) ≫ C.hom.app N' =
          (S.map α).target n ≫ (A.hom.app N' ≫ B.app N') := by
        rw [Category.assoc, ← O.second_comparison n N']
      _ = A.hom.app N ≫ (rightValue (F ⋙ G) n).map α ≫ B.app N' := by
        rw [← Category.assoc]
        exact (congrArg (· ≫ B.app N') (A.hom.naturality α)).trans (Category.assoc _ _ _)
      _ = A.hom.app N ≫ B.app N ≫ (rightValue F n ⋙ G).map α := by
        rw [B.naturality]
      _ = (O.filtered N).column n ≫ C.hom.app N ≫ (rightValue F n ⋙ G).map α := by
        rw [← Category.assoc, O.second_comparison, Category.assoc]
      _ = ((O.filtered N).column n ≫ (S.map α).page 0 0 n) ≫ C.hom.app N' := by
        rw [Category.assoc]
        exact congrArg ((O.filtered N).column n ≫ ·) (C.hom.naturality α).symm

theorem ideal_coefficient_naturality : IdealCoefficientNaturality h J e e' f := by
  intro q fQ hfQ
  let T := restrictIdeal.{u,v,w} h
  let V := rightValue (idealInvariants.{u,v,w} h) q ⋙ underlying k (g ⧸ h)
  let α := conjugateMap e e' f
  let eh := restrictEquiv h e
  let eh' := restrictEquiv h e'
  let fh := restrictOriginalMap h f
  have hrestrict : conjugateMap eh eh' fh = T.map α := by
    apply ModuleCat.hom_ext
    rfl
  refine ⟨exteriorMap Dh eh eh' fh, exteriorMap_term Dh eh eh' fh, ?_⟩
  intro x
  let I := idealCoordinates h J e q
  let I' := idealCoordinates h J e' q
  have hmap := natural_coordinate_apply Dh T V α q (J.ideal q)
    eh eh' fh hrestrict (I x)
  change (exteriorMap Dh eh eh' fh).homology q (I.symm (I x)) =
    I'.symm ((rightValue (idealInvariants.{u,v,w} h) q).map α (I x)) at hmap
  rw [I.symm_apply_apply, ← hfQ x, I'.symm_apply_apply] at hmap
  exact hmap

theorem spectral_naturality : SpectralNaturality h J e e' f := by
  let α := conjugateMap e e' f
  let S := objectSequence (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P
  let K := exteriorMap Dg e e' f
  have ht (n : ℕ) (x : (S.obj N).target (n : ℤ)) :
      K.homology n (targetCoordinates h J e n x) =
        targetCoordinates h J e' n ((S.map α).target (n : ℤ) x) :=
    natural_coordinate_apply Dg (𝟭 _) (S ⋙ targetEval (n : ℤ)) α n (J.targetIso h n) e e' f rfl x
  refine ⟨⟨K, exteriorMap_term Dg e e' f, ht, ?_⟩, ?_⟩
  · intro n p x hx
    obtain ⟨y, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_map.mp hx
    refine ⟨(S.map α).step p (n : ℤ) z, ?_⟩
    change targetCoordinates h J e' n ((S.obj N').inclusion p (n : ℤ) ((S.map α).step p (n : ℤ) z)) =
      K.homology n (targetCoordinates h J e n ((S.obj N).inclusion p (n : ℤ) z))
    rw [ht]
    exact congrArg (targetCoordinates h J e' n)
      (congrArg (fun m => m.hom z) ((S.map α).inclusion_comm p (n : ℤ)))
  · intro q
    let Q := rightValue (idealInvariants.{u,v,w} h) q
    let A := rebaseEquiv _ (idealCoordinates h J e q)
    let B := rebaseEquiv _ (idealCoordinates h J e' q)
    let fQ := B.symm.toLinearMap.comp ((Q.map α).hom.comp A.toLinearMap)
    have hf : conjugateMap A B fQ = Q.map α := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change B (B.symm ((Q.map α).hom (A (A.symm x)))) = _
      rw [A.apply_symm_apply, B.apply_symm_apply]
    refine ⟨fQ, fun x => B.apply_symm_apply _, exteriorMap Dq A B fQ,
      exteriorMap_term Dq A B fQ, ?_⟩
    intro p x
    exact natural_coordinate_apply Dq Q (S ⋙ pageEval 0 (p : ℤ) ((p : ℤ)+(q : ℤ)))
      α p (J.secondPageIso h p q) A B fQ hf x

end SpectralNaturality


section LiftedConnectors

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (D : CochainTheory.{u,v,max w a b c} k g)
  (V : ℕ → ModuleCat.{max u v w a b c} (U k g) ⥤ ModuleCat.{max u v w a b c} k)
  (δ : ∀ {S : ShortComplex (ModuleCat.{max u v w a b c} (U k g))}, S.ShortExact → ∀ n : ℕ,
    (V n).obj S.X₃ ⟶ (V (n+1)).obj S.X₁)
  (J : ∀ n, V n ≅ D.cohomology n)

theorem lifted_connectors : LiftedConnectors.{u,v,w,a,b,c} D V δ J := by
  intro H A B C i p hi hex hp
  let S := commonSequence.{u,v,w,a,b,c} i p hex
  let eA := up.{u,v,max u v w a b c,a} A
  let eB := up.{u,v,max u v w a b c,b} B
  let eC := up.{u,v,max u v w a b c,c} C
  have hS : S.ShortExact := common_sequence_exact.{u,v,w,a,b,c} i p hex hi hp
  refine ⟨hS, ?_⟩
  exact normalized_connectors (𝟭 _) D V δ J H hS A B C eA eB eC i p rfl rfl

end LiftedConnectors


section OriginalNormalization

open CategoryTheory.Functor P103.Specs.Ch10.Comparison
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w a b c) + 1} (ModuleCat.{max u v w a b c} (U k g))]
  [HasDerivedCategory.{(max u v w a b c) + 1} (ModuleCat.{max u v w a b c} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w a b c) + 1} (ModuleCat.{max u v w a b c} k)]
  {Dg : CochainTheory.{u,v,max w a b c} k g}
  {Dh : CochainTheory.{u,v,max w a b c} k h}
  {Dq : CochainTheory.{u,v,max w a b c} k (g ⧸ h)}
  (J : CohomologyComparison.{u,v,max w a b c} h Dg Dh Dq)

theorem lifted_ideal_connector_formula : LiftedIdealConnectorFormula.{u,v,w,a,b,c} h J := by
  intro A B C i p hi hex hp
  let S := commonSequence.{u,v,w,a,b,c} i p hex
  let eA := restrictEquiv h (up.{u,v,max u v w a b c,a} A)
  let eB := restrictEquiv h (up.{u,v,max u v w a b c,b} B)
  let eC := restrictEquiv h (up.{u,v,max u v w a b c,c} C)
  have hS : S.ShortExact := common_sequence_exact.{u,v,w,a,b,c} i p hex hi hp
  refine ⟨hS, ?_⟩
  refine normalized_connectors (restrictIdeal.{u,v,max w a b c} h) Dh _ _ J.ideal J.ideal_connectors
    hS _ _ _ eA eB eC (restrictOriginalMap h i) (restrictOriginalMap h p) ?_ ?_
  all_goals
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

theorem original_normalizations : OriginalNormalizations.{u,v,w,a,b,c} h J := by
  exact ⟨augmentation_transport (𝟭 _) Dg _ _ (J.ambient 0) J.ambient_augmentation,
    augmentation_transport (restrictIdeal.{u,v,max w a b c} h) Dh _ _ (J.ideal 0) J.ideal_augmentation,
    augmentation_transport (𝟭 _) Dq _ _ (J.quotient 0) J.quotient_augmentation,
    lifted_connectors.{u,v,w,a,b,c} Dg _ _ J.ambient J.ambient_connectors,
    lifted_ideal_connector_formula.{u,v,w,a,b,c} h J,
    lifted_connectors.{u,v,w,a,b,c} Dq _ _ J.quotient J.quotient_connectors⟩

end OriginalNormalization


section LieDerivative

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g) {N : ModuleCat.{max u v w} (U k g)} {M : ModuleCat.{a} (U k g)}
  (D : CochainTheory.{u,v,w} k h) (e : M ≃ₗ[U k g] N) (y : g)

private def restrictedUnderlyingEquiv (N : ModuleCat.{max u v w} (U k g)) :
    (underlying k g).obj N ≃ₗ[k] (underlying k h).obj (restrictOriginal h N) :=
  { (restrictionCoefficient.{u,v,w} h N).hom with
    invFun := fun m => m
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private def restrictedRepresentation (N : ModuleCat.{max u v w} (U k g)) :
    Representation k g ((underlying k h).obj (restrictOriginal h N)) :=
  (restrictedUnderlyingEquiv h N).lieConj.toLieHom.comp (coefficientRepresentation k g N)

private theorem restrictedRepresentation_apply (y : g)
    (m : (underlying k h).obj (restrictOriginal h N)) :
    restrictedRepresentation h N y m =
      (show (underlying k h).obj (restrictOriginal h N) from inclusion k g y • (show N from m)) := rfl

local instance : IsScalarTower k (U k h) ((underlying k h).obj (restrictOriginal h N)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private theorem ambientDifferential_eq (n : ℕ) :
    D.d (restrictOriginal h N) n =
      LieQuotientAction.differential h (M := (underlying k h).obj (restrictOriginal h N)) n := by
  apply LinearMap.ext
  intro t
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change D.d (restrictOriginal h N) n t (CE.wedge k h (n+1) x) =
    CE.coboundary k h ((underlying k h).obj (restrictOriginal h N)) (CE.boundary k h) n t
      (CE.wedge k h (n+1) x)
  rw [D.formula, CE.coboundary_formula _ _ _ _ (CE.boundary_formula k h)]
  rfl

private def ambientDerivative :
    CochainMap (D.complex (restrictOriginal h N)) (D.complex (restrictOriginal h N)) :=
  CochainMap.ofSucc (fun n => LieQuotientAction.derivative h (restrictedRepresentation h N) n y) (by
    intro n f
    simp only [CochainTheory.complex, CochainComplex.of_d, ModuleCat.hom_ofHom]
    change D.d (restrictOriginal h N) n
      (LieQuotientAction.derivative h (restrictedRepresentation h N) n y f) =
      LieQuotientAction.derivative h (restrictedRepresentation h N) (n+1) y
        (D.d (restrictOriginal h N) n f)
    rw [ambientDifferential_eq h D]
    apply LieQuotientAction.differential_derivative
    intro a m
    rw [restrictedRepresentation_apply]
    change IdealEnveloping.inducedMap k g h (inclusion k h a) • (show N from m) =
      inclusion k g (a : g) • (show N from m)
    rw [IdealEnveloping.inducedMap_inclusion])

theorem cochain_derivative : CochainDerivative h D e := by
  intro y
  let L' := ambientDerivative.{u,v,w} h (N := N) D y
  let E := exteriorLiftMap D (restrictEquiv h e)
  let L := (E.inverse _ (fun _ => rfl)).comp (L'.comp E)
  refine ⟨L, L', ?_, ?_, ?_⟩
  · intro n t x
    change e.symm (LieQuotientAction.derivative h (restrictedRepresentation h N) n y
      (exteriorEquiv (restrictEquiv h e) n t) (CE.wedge k h n x)) = _
    rw [LieQuotientAction.derivative_formula, restrictedRepresentation_apply]
    change e.symm (inclusion k g y • e (t (CE.wedge k h n x)) -
      ∑ i : Fin n, e (t (CE.wedge k h n (Function.update x i ⁅y, x i⁆)))) =
      inclusion k g y • (show M from t (CE.wedge k h n x)) -
      ∑ i : Fin n, (show M from t (CE.wedge k h n (Function.update x i ⁅y, x i⁆)))
    simp only [map_sub, map_smul, map_sum, LinearEquiv.symm_apply_apply]
  · intro n t x
    change LieQuotientAction.derivative h (restrictedRepresentation h N) n y t (CE.wedge k h n x) = _
    rw [LieQuotientAction.derivative_formula, restrictedRepresentation_apply]
    rfl
  · intro n t
    exact (exteriorEquiv (restrictEquiv h e) n).apply_symm_apply _

end LieDerivative

section OriginalSequence

open GrothendieckSpectralSequence GrothendieckEdges
open P103.Specs.Ch10.Comparison

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]
  {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
  {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
  {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
  {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
  (J : CEComparison h Dg Dh Dq E P O)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N)

private theorem object_transport
    (hquad : ∀ r p n, p < 0 ∨ n < p → CategoryTheory.Limits.IsZero
      ((sequenceDiagram h (P := P) (N := N)).page r p n))
    (hfive : ClassicalFiveTerms
      ((quotientHomology (.up ℕ) 1).map (E.inflation.app N))
      ((J.restrictToInvariants h 1).app N) (J.transgression h N)
      ((quotientHomology (.up ℕ) 2).map (E.inflation.app N))) :
    ObjectTransport h J e := by
  let X := (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v w} (U k g)) 0).obj N
  let j := invariantComparison h e
  have hj : InvariantEvaluation h e j := invariant_evaluation h e
  obtain ⟨I, R, H⟩ := edge_transport h Dg Dh Dq E e j hj
  obtain ⟨hf, he⟩ := five_terms_transport h J e j I R hfive H.2.2.1 H.2.2.2
  exact ⟨hquad, P.convergence X, finite_filtration h J e, graded_convergence h J e,
    exterior_transport Dg e, resolution_differential Dg e,
    exterior_transport Dh (restrictEquiv h e), resolution_differential Dh (restrictEquiv h e),
    fun q =>
      let i := idealCoordinates h J e q
      ⟨exterior_transport Dq (rebaseEquiv _ i), resolution_differential Dq (rebaseEquiv _ i),
        rebase_scalar_action _ i⟩,
    ideal_action_transport h Dh e (idealDerived h (N := N))
      (fun n => ((J.ideal n).app N).toLinearEquiv) (J.ideal_action N),
    cochain_derivative h Dh e, fixed_classes_formula h J e,
    j, hj, invariant_comparison_action h e, exterior_transport Dq (rebaseEquiv _ j),
    resolution_differential Dq (rebaseEquiv _ j), rebase_scalar_action _ j,
    row_augmentation h J e j hj, row_axis h J e j, column_axis h J e, I, R, H,
    filtered_edge_equations h J e j I R H, hf, he⟩

theorem original_spectral_sequence : OriginalSequenceStatement.{u,v,w,a,b,c} := by
  intro k g _ _ _ h
  let := HasDerivedCategory.standard (ModuleCat.{max u v w a b c} (U k g))
  let := HasDerivedCategory.standard (ModuleCat.{max u v w a b c} (U k (g ⧸ h)))
  let := HasDerivedCategory.standard (ModuleCat.{max u v w a b c} k)
  obtain ⟨Dg, Dh, Dq, E, P, O, J, hquad, hfive⟩ :=
    hochschild_serre.{u,v,max w a b c} k g h
  refine ⟨Dg, Dh, Dq, E, P, O, J,
    original_normalizations.{u,v,w,a,b,c} h J.toCohomologyComparison, ?_, ?_, ?_⟩
  · intro M
    let e := up.{u,v,max u v w a b c,a} M
    exact object_transport h J e (hquad _) (hfive _)
  · intro N
    let e := up.{u,v,max u v w a b c,b} N
    exact object_transport h J e (hquad _) (hfive _)
  · intro M N f
    let e := up.{u,v,max u v w a b c,a} M
    let e' := up.{u,v,max u v w a b c,b} N
    exact ⟨exterior_naturality Dg e e' f,
      exterior_naturality Dh (restrictEquiv h e) (restrictEquiv h e') (restrictOriginalMap h f),
      spectral_naturality h J e e' f, ideal_coefficient_naturality h J e e' f,
      spectral_edge_naturality.{u,v,max w a b c,a,b} h (O := O) e e' f,
      fun j j' => invariant_naturality.{u,v,max w a b c,a,b} h e e' f j j'⟩

end OriginalSequence

end AdvancedHomologicalAlgebra.LieHochschildSerre.Original
