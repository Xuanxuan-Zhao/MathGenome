import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethSequence
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.P103.Ch11.KunnethTotalConnector
import MathGenome.Internal.AlgebraCore.P103.Ch11.KunnethOppositeInterchange

namespace P103.Ch11.KunnethSequence
open CategoryTheory DirectSum
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.KunnethSequence
noncomputable section
universe u v w
variable {R : Type u} [Ring R]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Extension by zero carries an ordinary cycle to an integer cycle,
including degree zero, where the outgoing differential vanishes. -/
theorem extended_cycle_d_zero {S : Type u} [Ring S]
    (C : ChainComplex (ModuleCat.{v} S) ℕ) (p : ℕ) (c : cycles C p) :
    ((extendNonnegativeChain C).d p ((p : ℤ)-1)).hom
      ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom c.val) = 0 := by
  cases p with
  | zero =>
    have hd := C.extend_d_from_eq_zero nonnegativeChainEmbedding 0 (-1) 0 rfl
      (by simp [ComplexShape.down])
    change ((C.extend nonnegativeChainEmbedding).d 0 (-1)).hom _ = 0
    rw [hd]
    rfl
  | succ p =>
    have hp : ((p+1 : ℕ) : ℤ)-1 = (p : ℤ) := by omega
    rw [hp]
    change ((C.extend nonnegativeChainEmbedding).d _ _).hom _ = 0
    erw [C.extend_d_eq nonnegativeChainEmbedding (i := p+1) (j := p) rfl rfl]
    have hc : (C.d (p+1) p).hom c.val = 0 := by
      have h := c.property
      change (C.d (p+1) ((ComplexShape.down ℕ).next (p+1))).hom c.val = 0 at h
      erw [ChainComplex.next_nat_succ] at h
      exact h
    change (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom
      ((C.d (p+1) p).hom
        ((C.extendXIso nonnegativeChainEmbedding (i := p+1) rfl).hom.hom
          ((C.extendXIso nonnegativeChainEmbedding (i := p+1) rfl).inv.hom c.val))) = 0
    have hi := congrArg (fun f => f.hom c.val)
      (C.extendXIso nonnegativeChainEmbedding (i := p+1) rfl).inv_hom_id
    change (C.extendXIso nonnegativeChainEmbedding (i := p+1) rfl).hom.hom
      ((C.extendXIso nonnegativeChainEmbedding (i := p+1) rfl).inv.hom c.val) = c.val at hi
    rw [hi, hc, map_zero]

/-- The elementary tensor cycle formula uses exactly the established signed
coproduct total, not a separate substitute complex. -/
theorem pure_tensor_cycle : pure_tensor_cycleType.{u,v,w} := by
  intro R _ C D p q n h c x
  let a := (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom c.val
  let b := (D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom x.val
  have hd := P103.Ch11.TorBalance.tensorTotal_d
    (extendNonnegativeChain C) (extendNonnegativeChain D)
    (p : ℤ) (q : ℤ) (n : ℤ) (by exact_mod_cast h) a b
  have ha := extended_cycle_d_zero C p c
  have hb := extended_cycle_d_zero D q x
  dsimp only [a, b] at hd
  simp only [ha, hb, zero_tmul, tmul_zero, map_zero, Units.smul_def, zsmul_zero, zero_add] at hd
  unfold P103.Specs.Ch10.Complexes.cycles
  rw [LinearMap.mem_ker]
  cases n with
  | zero =>
    rw [ChainComplex.next_nat_zero]
    rw [(ordinaryTotal C D).shape 0 0 (by simp [ComplexShape.down])]
    rfl
  | succ n =>
    rw [ChainComplex.next_nat_succ]
    have hn : ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) := by omega
    rw [hn] at hd
    exact hd

theorem pure_tensor_natural : pure_tensor_naturalType.{u,v,w} := by
  intro R _ C C' D D' f g p q n h c x
  exact P103.Ch11.TorBalance.ordinaryTotalMap_inclusion f g p q n h c.val x.val

/-- Once α has descended through both homology quotients, its source
formula forces naturality in both complex variables. -/
theorem alpha_natural : alpha_naturalType.{u,v,w} := by
  classical
  intro R _ C C' D D' f g n α α' hα hα'
  apply DirectSum.linearMap_ext
  intro i
  apply tensor_hom_ext
  intro c x
  obtain ⟨c, rfl⟩ := (cycleBoundaries C i.val.1).mkQ_surjective c
  obtain ⟨x, rfl⟩ := (cycleBoundaries D i.val.2).mkQ_surjective x
  let z : cycles (ordinaryTotal C D) n :=
    ⟨_, pure_tensor_cycle R C D i.val.1 i.val.2 n i.property c x⟩
  let z' : cycles (ordinaryTotal C' D') n :=
    ⟨_, pure_tensor_cycle R C' D' i.val.1 i.val.2 n i.property
      (cyclesMap f i.val.1 c) (cyclesMap g i.val.2 x)⟩
  have hz : cyclesMap (ordinaryTotalMap f g) n z = z' := by
    apply Subtype.ext
    exact pure_tensor_natural R C C' D D' f g i.val.1 i.val.2 n i.property c x
  change homologyMap (ordinaryTotalMap f g) n
    (α (DirectSum.lof ℤ _ _ i (tmul R (homologyClass C i.val.1 c)
      (homologyClass D i.val.2 x)))) =
    α' (tensorDiagonalMap f g n (DirectSum.lof ℤ _ _ i
      (tmul R (homologyClass C i.val.1 c) (homologyClass D i.val.2 x))))
  rw [hα i c x z rfl]
  erw [P103.Ch10.Complexes.homologyMap_apply, hz]
  simp only [tensorDiagonalMap, DirectSum.lmap_lof, tensorMap_tmul]
  erw [P103.Ch10.Complexes.homologyMap_apply, P103.Ch10.Complexes.homologyMap_apply]
  exact (hα' i (cyclesMap f i.val.1 c) (cyclesMap g i.val.2 x) z' rfl).symm

theorem tor_diagonal_zero : tor_diagonal_zeroType.{u,v,w} := by
  intro R _ C D P
  let : IsEmpty (TailDiagonal 0) := ⟨by rintro ⟨⟨p,q⟩, h⟩; omega⟩
  infer_instance

theorem cycles_flat : cycles_flatType.{u,v,w} :=
  P103.Ch11.UniversalCoefficientsHomology.cycles_flat


open P103.Specs.Ch11.UniversalCoefficientsHomology
namespace Columns
variable {S : Type*} [Ring S]
variable {ι : Type a} {M : ι → Type b} {N : ι → Type c} {P : ι → Type d}
  [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] [∀ i, AddCommGroup (P i)]
  [∀ i, Module S (M i)] [∀ i, Module S (N i)] [∀ i, Module S (P i)]
theorem exact_lmap (f : ∀ i, M i →ₗ[S] N i) (g : ∀ i, N i →ₗ[S] P i)
    (h : ∀ i, Function.Exact (f i) (g i)) : Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  apply LinearMap.exact_iff.mpr
  rw [DirectSum.ker_lmap, DirectSum.range_lmap]
  simp_rw [LinearMap.exact_iff.mp (h _)]

def directSumKernelEquiv (f : ∀ i, M i →ₗ[S] N i) :
    (⨁ i, LinearMap.ker (f i)) ≃ₗ[S] LinearMap.ker (DirectSum.lmap f) := by
  let s := DirectSum.lmap (fun i => (LinearMap.ker (f i)).subtype)
  have he : Function.Exact s (DirectSum.lmap f) :=
    exact_lmap _ _ (fun i => LinearMap.exact_subtype_ker_map (f i))
  let sk := s.codRestrict (LinearMap.ker (DirectSum.lmap f)) he.apply_apply_eq_zero
  apply LinearEquiv.ofBijective sk
  constructor
  · intro a b h
    apply (DirectSum.lmap_injective (fun i => (LinearMap.ker (f i)).subtype)).mpr (fun _ => Subtype.val_injective)
    exact congrArg Subtype.val h
  · intro k
    obtain ⟨v,hv⟩ := (he k.val).mp k.property
    exact ⟨v, Subtype.ext hv⟩

open P103.Specs.Ch11.KunnethFlatColumns
open P103.Ch11.KunnethFlatColumns

abbrev BoundaryDiagonal (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :=
  ⨁ i : P103.Specs.Ch11.KunnethSequence.Diagonal n, Tensor R (boundaries C i.val.1) (Homology D i.val.2)

/-- Insert the shifted boundary diagonal, omitting its zero column. -/
def boundaryShift (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    BoundaryDiagonal C D n →ₗ[ℤ] DiagonalTensor (shiftedBoundaryTerms C) D (n+1) :=
  DirectSum.toModule ℤ _ _ (fun i : P103.Specs.Ch11.KunnethSequence.Diagonal n => DirectSum.lof ℤ _ (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal (n+1) => Tensor R (shiftedBoundaryTerms C j.val.1) (Homology D j.val.2)) (⟨(i.val.1+1,i.val.2),by omega⟩ : P103.Specs.Ch11.KunnethSequence.Diagonal (n+1)))

def boundaryUnshift (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    DiagonalTensor (shiftedBoundaryTerms C) D (n+1) →ₗ[ℤ] BoundaryDiagonal C D n :=
  DirectSum.toModule ℤ _ _ (fun i : P103.Specs.Ch11.KunnethSequence.Diagonal (n+1) => match i with
    | ⟨(0,q),h⟩ => 0
    | ⟨(p+1,q),h⟩ => DirectSum.lof ℤ _ (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n => Tensor R (boundaries C j.val.1) (Homology D j.val.2)) (⟨(p,q),by omega⟩ : P103.Specs.Ch11.KunnethSequence.Diagonal n))

def boundaryShiftEquiv (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    BoundaryDiagonal C D n ≃ₗ[ℤ] DiagonalTensor (shiftedBoundaryTerms C) D (n+1) := by
  classical
  apply LinearEquiv.ofLinearMap (boundaryShift C D n) (boundaryUnshift C D n)
  · apply DirectSum.linearMap_ext
    rintro ⟨⟨p,q⟩,h⟩
    apply LinearMap.ext
    intro x
    cases p with
    | zero =>
      have hx : x = 0 := eq_zero_of_subsingleton_left (A := shiftedBoundaryTerms C 0) x
      subst x
      simp
    | succ p => simp [boundaryShift, boundaryUnshift]
  · apply DirectSum.linearMap_ext
    rintro ⟨⟨p,q⟩,h⟩
    apply LinearMap.ext
    intro x
    simp [boundaryShift, boundaryUnshift]


abbrev CycleDiagonal (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :=
  DiagonalTensor (cycleTerms C) D n

def cycleEquiv (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    CycleDiagonal C D n ≃ₗ[ℤ] Homology (ordinaryTotal (cycleComplex C) D) n :=
  diagonalEquiv (cycleTerms C) (cycles_flat R C hC) D n

def shiftedEquiv (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    DiagonalTensor (shiftedBoundaryTerms C) D n ≃ₗ[ℤ]
      Homology (ordinaryTotal (shiftedBoundaryComplex C) D) n :=
  diagonalEquiv (shiftedBoundaryTerms C) (fun p => by
    cases p with
    | zero => exact P103.Ch11.FlatResolutions.rightFlat_of_subsingleton _
    | succ p => exact hC.2 p) D n

def boundaryEquiv (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    BoundaryDiagonal C D n ≃ₗ[ℤ] Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1) :=
  (boundaryShiftEquiv C D n).trans (shiftedEquiv C hC D (n+1))

theorem cycleEquiv_formula (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    DiagonalFormula (cycleTerms C) D n (cycleEquiv C hC D n) :=
  diagonalEquiv_formula _ _ _ _

theorem shiftedEquiv_formula (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    DiagonalFormula (shiftedBoundaryTerms C) D n (shiftedEquiv C hC D n) :=
  diagonalEquiv_formula _ _ _ _

open P103.Specs.Ch11.KunnethTotalConnector

/-- The total connector in unshifted boundary coordinates is the sum of j⊗1. -/
theorem connector_diagonal (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ)
    (δ : Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1) →ₗ[ℤ]
      Homology (ordinaryTotal (cycleComplex C) D) n)
    (hδ : ConnectorFormula C D n δ) :
    δ.comp (boundaryEquiv C hC D n).toLinearMap =
      (cycleEquiv C hC D n).toLinearMap.comp (jDiagonal C D n) := by
  classical
  apply DirectSum.linearMap_ext
  rintro ⟨⟨p,q⟩,h⟩
  apply tensor_hom_ext
  intro b x
  have hh := hδ (cycleEquiv C hC D n) (shiftedEquiv C hC D (n+1))
    (cycleEquiv_formula C hC D n) (shiftedEquiv_formula C hC D (n+1)) p q h b x
  simpa [boundaryEquiv, boundaryShiftEquiv, boundaryShift, jDiagonal] using hh

def aDiagonal (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    CycleDiagonal C D n →ₗ[ℤ] Homology (ordinaryTotal C D) n :=
  (homologyMap (inclusion C D) n).toAddMonoidHom.toIntLinearMap.comp
    (cycleEquiv C hC D n).toLinearMap

def bDiagonal (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    Homology (ordinaryTotal C D) (n+1) →ₗ[ℤ] BoundaryDiagonal C D n :=
  (boundaryEquiv C hC D n).symm.toLinearMap.comp
    (homologyMap (projection C D) (n+1)).toAddMonoidHom.toIntLinearMap

theorem exact_j_a (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    Function.Exact (jDiagonal C D n) (aDiagonal C hC D n) := by
  obtain ⟨δ, ⟨_,hs,hδ⟩, _⟩ := P103.Ch11.KunnethTotalConnector.total_connector R C hC D n
  have hc (t : BoundaryDiagonal C D n) :
      δ (boundaryEquiv C hC D n t) = cycleEquiv C hC D n (jDiagonal C D n t) :=
    LinearMap.congr_fun (connector_diagonal C hC D n δ hδ) t
  intro z
  constructor
  · intro hz
    obtain ⟨t,ht⟩ := (hs.2.2 (cycleEquiv C hC D n z)).mp hz
    obtain ⟨t,rfl⟩ := (boundaryEquiv C hC D n).surjective t
    exact ⟨t, (cycleEquiv C hC D n).injective ((hc t).symm.trans ht)⟩
  · rintro ⟨t,rfl⟩
    change homologyMap (inclusion C D) n (cycleEquiv C hC D n (jDiagonal C D n t)) = 0
    exact (congrArg (homologyMap (inclusion C D) n) (hc t).symm).trans
      (hs.2.2.apply_apply_eq_zero _)

theorem fiveTerm (C : RightComplex.{u,v} R) (hC : FlatTermsAndBoundaries.{u,v,w} C)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    Function.Exact (jDiagonal C D (n+1)) (aDiagonal C hC D (n+1)) ∧
    Function.Exact (aDiagonal C hC D (n+1)) (bDiagonal C hC D n) ∧
    Function.Exact (bDiagonal C hC D n) (jDiagonal C D n) := by
  obtain ⟨δ, ⟨_,hs,hδ⟩, _⟩ := P103.Ch11.KunnethTotalConnector.total_connector R C hC D n
  have hc (t : BoundaryDiagonal C D n) :
      δ (boundaryEquiv C hC D n t) = cycleEquiv C hC D n (jDiagonal C D n t) :=
    LinearMap.congr_fun (connector_diagonal C hC D n δ hδ) t
  let eL := boundaryEquiv C hC D n
  let eZ := cycleEquiv C hC D (n+1)
  refine ⟨exact_j_a C hC D (n+1), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx' : homologyMap (projection C D) (n+1) x = 0 := by
        apply eL.symm.injective
        exact hx.trans (map_zero eL.symm).symm
      obtain ⟨z,hz⟩ := (hs.1 x).mp hx'
      obtain ⟨z,rfl⟩ := eZ.surjective z
      exact ⟨z,hz⟩
    · rintro ⟨z,rfl⟩
      change eL.symm (homologyMap (projection C D) (n+1) (homologyMap (inclusion C D) (n+1) (eZ z))) = 0
      rw [hs.1.apply_apply_eq_zero, map_zero]
  · intro t
    constructor
    · intro ht
      have ht' : δ (eL t) = 0 := by
        change δ (boundaryEquiv C hC D n t) = 0
        rw [hc]
        change cycleEquiv C hC D n (jDiagonal C D n t) = 0
        rw [ht, map_zero]
      obtain ⟨x,hx⟩ := (hs.2.1 (eL t)).mp ht'
      refine ⟨x, ?_⟩
      change eL.symm (homologyMap (projection C D) (n+1) x) = t
      exact (congrArg eL.symm hx).trans (eL.symm_apply_apply t)
    · rintro ⟨x,rfl⟩
      apply (cycleEquiv C hC D n).injective
      change cycleEquiv C hC D n (jDiagonal C D n
        (eL.symm (homologyMap (projection C D) (n+1) x))) = cycleEquiv C hC D n 0
      exact (hc _).symm.trans ((congrArg δ (eL.apply_symm_apply _)).trans
        ((hs.2.1.apply_apply_eq_zero _).trans (map_zero (cycleEquiv C hC D n)).symm))

theorem diagonal_rightExact (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    Function.Exact (jDiagonal C D n) (qDiagonal C D n) ∧ Function.Surjective (qDiagonal C D n) := by
  have he (i : P103.Specs.Ch11.KunnethSequence.Diagonal n) :=
    P103.Ch11.UniversalCoefficientsHomology.boundary_cycle_homology_shortExact C i.val.1
  have hq (i : P103.Specs.Ch11.KunnethSequence.Diagonal n) :
      Function.Exact (jTensor C (ModuleCat.of R (Homology D i.val.2)) i.val.1)
        (tensorMap (homologyClass C i.val.1) (LinearMap.id : Homology D i.val.2 →ₗ[R] _)) ∧
      Function.Surjective (tensorMap (homologyClass C i.val.1) (LinearMap.id : Homology D i.val.2 →ₗ[R] _)) :=
    P103.HomTensorExactness.tensor_first_rightExact _ _ (he i).2.1 (he i).2.2
      (jTensor C (ModuleCat.of R (Homology D i.val.2)) i.val.1).toAddMonoidHom (by intros; rfl)
      (tensorMap (homologyClass C i.val.1) (LinearMap.id : Homology D i.val.2 →ₗ[R] _)).toAddMonoidHom (by intros; rfl)
  exact ⟨exact_lmap _ _ (fun i => (hq i).1), (DirectSum.lmap_surjective _).mpr (fun i => (hq i).2)⟩

end Columns

section Transport
open Function
universe v' w' x x'
variable {K : Type u} [Ring K]
variable {A : Type v} {A' : Type v'} {B : Type w} {B' : Type w'}
  {C : Type x} {C' : Type x'}
  [AddCommMonoid A] [AddCommMonoid A'] [AddCommMonoid B] [AddCommMonoid B']
  [AddCommMonoid C] [AddCommMonoid C']
  [Module K A] [Module K A'] [Module K B] [Module K B'] [Module K C] [Module K C']

/-- Transport a short exact sequence along three specified linear equivalences. -/
theorem shortExact_transport (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (eA : A' ≃ₗ[K] A) (eB : B ≃ₗ[K] B') (eC : C ≃ₗ[K] C')
    (hi : Injective f) (he : Exact f g) (hs : Surjective g) :
    Injective (eB.toLinearMap.comp (f.comp eA.toLinearMap)) ∧
    Exact (eB.toLinearMap.comp (f.comp eA.toLinearMap))
      (eC.toLinearMap.comp (g.comp eB.symm.toLinearMap)) ∧
    Surjective (eC.toLinearMap.comp (g.comp eB.symm.toLinearMap)) := by
  refine ⟨eB.injective.comp (hi.comp eA.injective), ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hy' : g (eB.symm y) = 0 := eC.injective (hy.trans (map_zero eC).symm)
      obtain ⟨a, ha⟩ := (he (eB.symm y)).mp hy'
      refine ⟨eA.symm a, ?_⟩
      change eB (f (eA (eA.symm a))) = y
      rw [eA.apply_symm_apply, ha, eB.apply_symm_apply]
    · rintro ⟨a, rfl⟩
      change eC (g (eB.symm (eB (f (eA a))))) = 0
      rw [eB.symm_apply_apply, he.apply_apply_eq_zero, map_zero]
  · intro c
    obtain ⟨b, hb⟩ := hs (eC.symm c)
    refine ⟨eB b, ?_⟩
    change eC (g (eB.symm (eB b))) = c
    rw [eB.symm_apply_apply, hb, eC.apply_symm_apply]

end Transport

open P103.Specs.Ch11.UniversalCoefficientsHomology

private def unshiftBoundaryDiagonal (C : RightComplex.{u,v} R)
    (D : LeftComplex.{u,w} R) (n : ℕ) :
    P103.Specs.Ch11.KunnethFlatColumns.DiagonalTensor (shiftedBoundaryTerms C) D n →ₗ[ℤ]
      ⨁ i : TailDiagonal n, Tensor R (boundaries C i.val.1) (Homology D i.val.2) :=
  DirectSum.toModule ℤ _ _ (fun i : Diagonal n => match i with
    | ⟨(0,q),h⟩ => 0
    | ⟨(p+1,q),h⟩ => DirectSum.lof ℤ _
      (fun j : TailDiagonal n => Tensor R (boundaries C j.val.1) (Homology D j.val.2))
      (⟨(p,q),by omega⟩ : TailDiagonal n))

private theorem torBoundaryMap_injective (C : RightComplex.{u,v} R)
    (D : LeftComplex.{u,w} R) (P : HomologyModels C) (n : ℕ)
    (e : ∀ i : TailDiagonal n, TorTerm C D P i.val ≃ₗ[ℤ] ComponentKernel C D i.val) :
    Function.Injective (torBoundaryMap C D P n e) := by
  let k : ∀ i : TailDiagonal n, TorTerm C D P i.val →ₗ[ℤ]
      Tensor R (boundaries C i.val.1) (Homology D i.val.2) :=
    fun i => (ComponentKernel C D i.val).subtype.comp (e i).toLinearMap
  have hk : (unshiftBoundaryDiagonal C D n).comp (torBoundaryMap C D P n e) =
      DirectSum.lmap k := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p,q⟩,h⟩
    apply LinearMap.ext
    intro x
    simp [unshiftBoundaryDiagonal, torBoundaryMap, k]
  intro x y hxy
  apply (DirectSum.lmap_injective k).mpr
    (fun i => Subtype.val_injective.comp (e i).injective)
  rw [← hk]
  exact congrArg (unshiftBoundaryDiagonal C D n) hxy

set_option maxHeartbeats 4000000 in
private theorem torBoundaryMap_natural
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D') (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} R 1) (n : ℕ)
    (S : NormalizedDegreeSequence C D P n) (S' : NormalizedDegreeSequence C' D' P' n) :
    (P103.Specs.Ch11.KunnethFlatColumns.diagonalMap
      (fun p => (P103.Specs.Ch11.KunnethTotalConnector.shiftedBoundaryComplexMap f).f p)
      g n).comp (torBoundaryMap C D P n S.kernelIso) =
    (torBoundaryMap C' D' P' n S'.kernelIso).comp (torDiagonalMap f g P P' T n) := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  obtain ⟨e,he,heq⟩ := S.kernelIso_canonical i
  obtain ⟨e',he',heq'⟩ := S'.kernelIso_canonical i
  have h := P103.Ch11.UniversalCoefficientsHomology.torKernelIdentification_natural
    f (ModuleCat.of R (Homology D i.val.2)) (ModuleCat.of R (Homology D' i.val.2))
    (ModuleCat.ofHom (homologyMap g i.val.2)) i.val.1 (P i.val.1) (P' i.val.1)
    T e e' he he' x
  rw [← heq x, ← heq' _] at h
  simp only [LinearMap.comp_apply, torBoundaryMap, DirectSum.toModule_lof,
    torDiagonalMap, DirectSum.lmap_lof,
    P103.Specs.Ch11.KunnethFlatColumns.diagonalMap]
  apply congrArg (DirectSum.lof ℤ _ _
    (⟨(i.val.1+1,i.val.2),by have := i.property; omega⟩ : Diagonal n))
  exact h.symm

-- The canonical normalization determines the natural right arrow.
theorem normalized_natural : normalized_naturalType.{u,v,w} := by
  intro R _ C C' D D' f g P P' T n S S'
  refine ⟨alpha_natural R C C' D D' f g n S.α S'.α S.α_formula S'.α_formula, ?_⟩
  apply LinearMap.ext
  intro x
  apply torBoundaryMap_injective C' D' P' n S'.kernelIso
  apply S'.boundaryEquiv.injective
  change S'.boundaryEquiv (torBoundaryMap C' D' P' n S'.kernelIso
      (torDiagonalMap f g P P' T n (S.β x))) =
    S'.boundaryEquiv (torBoundaryMap C' D' P' n S'.kernelIso
      (S'.β (homologyMap (ordinaryTotalMap f g) n x)))
  have ht := LinearMap.congr_fun (torBoundaryMap_natural f g P P' T n S S') (S.β x)
  dsimp only [LinearMap.comp_apply] at ht
  have hn := P103.Ch11.KunnethFlatColumns.diagonal_natural R
    (shiftedBoundaryTerms C) (shiftedBoundaryTerms C') D D'
    (fun p => (P103.Specs.Ch11.KunnethTotalConnector.shiftedBoundaryComplexMap f).f p)
    g n S.boundaryEquiv S'.boundaryEquiv S.boundaryEquiv_formula S'.boundaryEquiv_formula
    (torBoundaryMap C D P n S.kernelIso (S.β x))
  calc
    S'.boundaryEquiv (torBoundaryMap C' D' P' n S'.kernelIso
      (torDiagonalMap f g P P' T n (S.β x))) =
        S'.boundaryEquiv (P103.Specs.Ch11.KunnethFlatColumns.diagonalMap
          (fun p => (P103.Specs.Ch11.KunnethTotalConnector.shiftedBoundaryComplexMap f).f p)
          g n (torBoundaryMap C D P n S.kernelIso (S.β x))) :=
      congrArg S'.boundaryEquiv ht.symm
    _ = homologyMap (ordinaryTotalMap
      (P103.Specs.Ch11.KunnethTotalConnector.shiftedBoundaryComplexMap f) g) n
      (S.boundaryEquiv (torBoundaryMap C D P n S.kernelIso (S.β x))) := hn.symm
    _ = homologyMap (ordinaryTotalMap
      (P103.Specs.Ch11.KunnethTotalConnector.shiftedBoundaryComplexMap f) g) n
      (homologyMap (P103.Specs.Ch11.KunnethTotalConnector.projection C D) n x) :=
        congrArg _ (S.β_formula x)
    _ = homologyMap (P103.Specs.Ch11.KunnethTotalConnector.projection C' D') n
      (homologyMap (ordinaryTotalMap f g) n x) :=
        DFunLike.congr_fun (P103.Ch11.KunnethTotalConnector.homology_squares f g n).2 x
    _ = S'.boundaryEquiv (torBoundaryMap C' D' P' n S'.kernelIso
      (S'.β (homologyMap (ordinaryTotalMap f g) n x))) := (S'.β_formula _).symm


open P103.Specs.Ch11.KunnethFlatColumns
open P103.Specs.Ch11.KunnethTotalConnector

/-- The cycle representative formula follows from the quotient factorization. -/
theorem alphaFormula_of_factor (C : RightComplex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (D : LeftComplex.{u,w} R) (n : ℕ)
    (α : TensorDiagonal C D n →ₗ[ℤ] Homology (ordinaryTotal C D) n)
    (hα : ∀ v, α (qDiagonal C D n v) = Columns.aDiagonal C hC D n v) :
    AlphaFormula C D n α := by
  intro i c x z hz
  obtain ⟨w, hw, he⟩ := Columns.cycleEquiv_formula C hC D n
    i.val.1 i.val.2 i.property c x
  let v : CycleDiagonal C D n := DirectSum.lof ℤ _ _ i
    (tmul R c (homologyClass D i.val.2 x))
  have hv : qDiagonal C D n v = DirectSum.lof ℤ _ _ i
      (tmul R (homologyClass C i.val.1 c) (homologyClass D i.val.2 x)) := by
    simp [v, qDiagonal, tensorMap_tmul]
  have hwz : cyclesMap (inclusion C D) n w = z := by
    apply Subtype.ext
    change ((inclusion C D).f n).hom w.val = z.val
    rw [hw, hz]
    have hmap := P103.Ch11.TorBalance.ordinaryTotalMap_inclusion
      (cycleInclusion C) (𝟙 D) i.val.1 i.val.2 n i.property c x.val
    change ((inclusion C D).f n).hom
      (ordinaryInclusion (cycleComplex C) D i.val.1 i.val.2 n i.property (tmul R c x.val)) =
      ordinaryInclusion C D i.val.1 i.val.2 n i.property (tmul R c.val x.val) at hmap
    exact hmap
  rw [← hv, hα]
  change homologyMap (inclusion C D) n (Columns.cycleEquiv C hC D n v) = _
  change Columns.cycleEquiv C hC D n v = _ at he
  rw [he]
  erw [P103.Ch10.Complexes.homologyMap_apply, hwz]
  rfl

namespace Columns
def tailDiagonalEquiv (n : ℕ) : TailDiagonal (n+1) ≃ P103.Specs.Ch11.KunnethSequence.Diagonal n where
  toFun i := ⟨i.val, by have := i.property; omega⟩
  invFun i := ⟨i.val, by have := i.property; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex the positive tail and identify each Tor component with its kernel. -/
def tailKernelEquiv (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ)
    (e : ∀ i : TailDiagonal (n+1), TorTerm C D P i.val ≃ₗ[ℤ] ComponentKernel C D i.val) :
    TorDiagonal C D P (n+1) ≃ₗ[ℤ]
      (⨁ i : P103.Specs.Ch11.KunnethSequence.Diagonal n, ComponentKernel C D i.val) :=
  (DirectSum.congrLinearEquiv e).trans (DirectSum.lequivCongrLeft ℤ (tailDiagonalEquiv n))

theorem tailKernelEquiv_lof (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ)
    (e : ∀ i : TailDiagonal (n+1), TorTerm C D P i.val ≃ₗ[ℤ] ComponentKernel C D i.val)
    (i : TailDiagonal (n+1)) (x : TorTerm C D P i.val) :
    tailKernelEquiv C D P n e (DirectSum.lof ℤ _ _ i x) =
      DirectSum.lof ℤ _ _ (tailDiagonalEquiv n i) (e i x) := by
  classical
  change (DirectSum.lequivCongrLeft ℤ (tailDiagonalEquiv n))
    ((DirectSum.lmap (fun i => (e i).toLinearMap)) (DirectSum.lof ℤ _ _ i x)) = _
  exact (congrArg (DirectSum.lequivCongrLeft ℤ (tailDiagonalEquiv n))
    (DirectSum.lmap_lof (fun i => (e i).toLinearMap) i x)).trans
      (DirectSum.lequivCongrLeft_lof ℤ
        (M := fun j : TailDiagonal (n+1) => ComponentKernel C D j.val)
        (e := tailDiagonalEquiv n)
        (i := i) (k := tailDiagonalEquiv n i) rfl (e i x) (e i x) rfl)

/-- Kernels commute with the finite diagonal direct sum. -/
def torKernelEquiv (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ)
    (e : ∀ i : TailDiagonal (n+1), TorTerm C D P i.val ≃ₗ[ℤ] ComponentKernel C D i.val) :
    TorDiagonal C D P (n+1) ≃ₗ[ℤ] LinearMap.ker (jDiagonal C D n) :=
  (tailKernelEquiv C D P n e).trans
    (directSumKernelEquiv (fun i : P103.Specs.Ch11.KunnethSequence.Diagonal n =>
      jTensor C (ModuleCat.of R (Homology D i.val.2)) i.val.1))

/-- The normalized Tor kernel inclusion is exactly the shifted insertion. -/
theorem torKernelEquiv_boundary (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ)
    (e : ∀ i : TailDiagonal (n+1), TorTerm C D P i.val ≃ₗ[ℤ] ComponentKernel C D i.val)
    (x : TorDiagonal C D P (n+1)) :
    boundaryShift C D n (torKernelEquiv C D P n e x).val =
      torBoundaryMap C D P (n+1) e x := by
  have hh : (boundaryShift C D n).comp
      ((LinearMap.ker (jDiagonal C D n)).subtype.comp (torKernelEquiv C D P n e).toLinearMap) =
      torBoundaryMap C D P (n+1) e := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change boundaryShift C D n
      (directSumKernelEquiv (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n =>
        jTensor C (ModuleCat.of R (Homology D j.val.2)) j.val.1)
          (tailKernelEquiv C D P n e (DirectSum.lof ℤ _ _ i x))).val = _
    calc
      _ = boundaryShift C D n
          (directSumKernelEquiv (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n =>
            jTensor C (ModuleCat.of R (Homology D j.val.2)) j.val.1)
              (DirectSum.lof ℤ _ _ (tailDiagonalEquiv n i) (e i x))).val :=
        congrArg (fun t => boundaryShift C D n
          (directSumKernelEquiv (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n =>
            jTensor C (ModuleCat.of R (Homology D j.val.2)) j.val.1) t).val)
          (tailKernelEquiv_lof C D P n e i x)
      _ = _ := by
        change boundaryShift C D n (DirectSum.lmap
          (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n =>
            (ComponentKernel C D j.val).subtype)
            (DirectSum.lof ℤ _ _ (tailDiagonalEquiv n i) (e i x))) = _
        simp only [DirectSum.lmap_lof, boundaryShift, DirectSum.toModule_lof,
          torBoundaryMap, LinearMap.comp_apply]
        rfl
  exact LinearMap.congr_fun hh x
end Columns

/-- Assemble the positive sequence from the cycle quotient factorization. -/
theorem positiveSequence_of_factor (C : RightComplex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ)
    (α : TensorDiagonal C D (n+1) →ₗ[ℤ] Homology (ordinaryTotal C D) (n+1))
    (hα : Function.Injective α)
    (hαq : ∀ v, α (qDiagonal C D (n+1) v) = Columns.aDiagonal C hC D (n+1) v) :
    Nonempty (NormalizedDegreeSequence C D P (n+1)) := by
  classical
  let ee (i : TailDiagonal (n+1)) :=
    P103.Ch11.UniversalCoefficientsHomology.torKernelIdentification C hC
      (ModuleCat.of R (Homology D i.val.2)) i.val.1 (P i.val.1)
  let e : ∀ i : TailDiagonal (n+1), TorTerm C D P i.val ≃ₗ[ℤ] ComponentKernel C D i.val :=
    fun i => (ee i).choose
  have he (i : TailDiagonal (n+1)) :
      TorKernelIdentification C (ModuleCat.of R (Homology D i.val.2)) i.val.1 (P i.val.1) (e i) :=
    (ee i).choose_spec
  let eK : TorDiagonal C D P (n+1) ≃ₗ[ℤ] LinearMap.ker (jDiagonal C D n) :=
    Columns.torKernelEquiv C D P n e
  have hq := Columns.diagonal_rightExact C D (n+1)
  have hs := Columns.fiveTerm C hC D n
  let bk : Homology (ordinaryTotal C D) (n+1) →ₗ[ℤ] LinearMap.ker (jDiagonal C D n) :=
    (Columns.bDiagonal C hC D n).codRestrict (LinearMap.ker (jDiagonal C D n))
      (fun x => (hs.2.2 (Columns.bDiagonal C hC D n x)).mpr ⟨x, rfl⟩)
  let β : Homology (ordinaryTotal C D) (n+1) →ₗ[ℤ] TorDiagonal C D P (n+1) :=
    eK.symm.toLinearMap.comp bk
  have hβ (x) : (eK (β x)).val = Columns.bDiagonal C hC D n x := by
    change (eK (eK.symm (bk x))).val = _
    exact congrArg Subtype.val (eK.apply_symm_apply (bk x))
  have hz (x) : β x = 0 ↔ Columns.bDiagonal C hC D n x = 0 := by
    constructor
    · intro hx
      exact (hβ x).symm.trans ((congrArg (fun t => (eK t).val) hx).trans
        (congrArg Subtype.val (map_zero eK)))
    · intro hx
      apply eK.injective
      apply Subtype.ext
      exact (hβ x).trans (hx.trans (congrArg Subtype.val (map_zero eK)).symm)
  have hαβ : Function.Exact α β := by
    intro x
    rw [hz]
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := (hs.2.1 x).mp hx
      exact ⟨qDiagonal C D (n+1) v, (hαq v).trans hv⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨v, rfl⟩ := hq.2 y
      exact (congrArg (Columns.bDiagonal C hC D n) (hαq v)).trans
        (hs.2.1.apply_apply_eq_zero v)
  have sβ : Function.Surjective β := by
    intro y
    obtain ⟨x, hx⟩ := (hs.2.2 (eK y).val).mp (eK y).property
    refine ⟨x, eK.injective (Subtype.ext ?_)⟩
    exact (hβ x).trans hx
  refine ⟨{
    α := α
    β := β
    injective_α := hα
    exact := hαβ
    surjective_β := sβ
    α_formula := alphaFormula_of_factor C hC D (n+1) α hαq
    boundaryEquiv := Columns.shiftedEquiv C hC D (n+1)
    boundaryEquiv_formula := Columns.shiftedEquiv_formula C hC D (n+1)
    kernelIso := e
    kernelIso_canonical := ?_
    β_formula := ?_ }⟩
  · intro i
    exact ⟨e i, he i, fun _ => rfl⟩
  · intro x
    have hh := congrArg (fun t => Columns.shiftedEquiv C hC D (n+1)
      (Columns.boundaryShift C D n t)) (hβ x)
    exact (congrArg (Columns.shiftedEquiv C hC D (n+1))
      (Columns.torKernelEquiv_boundary C D P n e (β x)).symm).trans
        (hh.trans ((Columns.boundaryEquiv C hC D n).apply_symm_apply _))

/-- The zero-degree sequence has its actual empty Tor diagonal. -/
theorem zeroSequence_of_factor (C : RightComplex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C)
    (α : TensorDiagonal C D 0 →ₗ[ℤ] Homology (ordinaryTotal C D) 0)
    (hα : Function.Injective α)
    (hαq : ∀ v, α (qDiagonal C D 0 v) = Columns.aDiagonal C hC D 0 v) :
    Nonempty (NormalizedDegreeSequence C D P 0) := by
  classical
  letI : IsEmpty (TailDiagonal 0) := ⟨by rintro ⟨⟨p,q⟩,h⟩; omega⟩
  let a := Columns.aDiagonal C hC D 0
  have hs := P103.Ch11.KunnethTotalConnector.total_zero R C hC D
  have sa : Function.Surjective a := hs.2.2.comp (Columns.cycleEquiv C hC D 0).surjective
  have sα : Function.Surjective α := by
    intro x
    obtain ⟨v, rfl⟩ := sa x
    exact ⟨qDiagonal C D 0 v, hαq v⟩
  refine ⟨{
    α := α
    β := 0
    injective_α := hα
    exact := ?_
    surjective_β := ?_
    α_formula := alphaFormula_of_factor C hC D 0 α hαq
    boundaryEquiv := Columns.shiftedEquiv C hC D 0
    boundaryEquiv_formula := Columns.shiftedEquiv_formula C hC D 0
    kernelIso := fun i => isEmptyElim i
    kernelIso_canonical := fun i => isEmptyElim i
    β_formula := ?_ }⟩
  · intro x
    exact ⟨fun _ => sα x, fun _ => rfl⟩
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · intro x
    haveI := hs.1
    exact Subsingleton.elim _ _



open Function
noncomputable section
universe kf af bf cf df
variable {K : Type kf} [Ring K]
variable {U : Type af} {V : Type bf} {Q : Type cf} {W : Type df}
  [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid Q] [AddCommMonoid W]
  [Module K U] [Module K V] [Module K Q] [Module K W]

private theorem sameFiber_of_kernel (q : V →ₗ[K] Q) (a : V →ₗ[K] W)
    (hk : ∀ v, q v = 0 → a v = 0) (v w : V) (h : q v = q w) : a v = a w := by
  have hz : q (v + (-1 : K) • w) = 0 := by
    rw [map_add, map_smul, h]
    calc
      q w + (-1 : K) • q w = (1 + (-1 : K)) • q w := by rw [add_smul, one_smul]
      _ = 0 := by rw [add_neg_cancel, zero_smul]
  have ha : a v + (-1 : K) • a w = 0 := by
    simpa only [map_add, map_smul] using hk _ hz
  have hinv : (-1 : K) • a w + a w = 0 := by
    calc
      (-1 : K) • a w + a w = ((-1 : K) + 1) • a w := by rw [add_smul, one_smul]
      _ = 0 := by rw [neg_add_cancel, zero_smul]
  calc
    a v = (a v + (-1 : K) • a w) + a w := by rw [add_assoc, hinv, add_zero]
    _ = a w := by rw [ha, zero_add]

/-- The same exact kernel and a surjective presentation give an injective factor. -/
theorem factor_of_exact (j : U →ₗ[K] V) (q : V →ₗ[K] Q) (a : V →ₗ[K] W)
    (hq : Exact j q) (sq : Surjective q) (ha : Exact j a) :
    ∃ α : Q →ₗ[K] W, Injective α ∧ ∀ v, α (q v) = a v := by
  classical
  have hk (v) (h : q v = 0) : a v = 0 := by
    obtain ⟨u, rfl⟩ := (hq v).mp h
    exact ha.apply_apply_eq_zero _
  have hk' (v) (h : a v = 0) : q v = 0 := by
    obtain ⟨u, rfl⟩ := (ha v).mp h
    exact hq.apply_apply_eq_zero _
  let lift (x : Q) : V := (sq x).choose
  have hl (x : Q) : q (lift x) = x := (sq x).choose_spec
  let α : Q →ₗ[K] W :=
    { toFun := fun x => a (lift x)
      map_add' := fun x y => by
        exact (sameFiber_of_kernel q a hk _ _
          ((hl (x+y)).trans (by rw [map_add, hl, hl]))).trans (map_add a _ _)
      map_smul' := fun r x => by
        exact (sameFiber_of_kernel q a hk _ _
          ((hl (r • x)).trans (by rw [map_smul, hl]; rfl))).trans (map_smul a _ _) }
  have hα (v : V) : α (q v) = a v :=
    sameFiber_of_kernel q a hk _ _ (hl (q v))
  refine ⟨α, ?_, hα⟩
  intro x y hxy
  obtain ⟨v, rfl⟩ := sq x
  obtain ⟨w, rfl⟩ := sq y
  rw [hα, hα] at hxy
  exact sameFiber_of_kernel a q hk' v w hxy

end

/-- The natural Künneth short exact sequence with its canonical Tor kernel map. -/
theorem right_sequence : right_sequenceType.{u,v,w} := by
  intro R _ C hC D P n
  have hq := Columns.diagonal_rightExact C D n
  obtain ⟨α, hi, hfac⟩ := factor_of_exact
    (jDiagonal C D n) (qDiagonal C D n) (Columns.aDiagonal C hC D n)
    hq.1 hq.2 (Columns.exact_j_a C hC D n)
  cases n with
  | zero => exact zeroSequence_of_factor C hC D P α hi hfac
  | succ n => exact positiveSequence_of_factor C hC D P n α hi hfac


section OppositeOrientation
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch02.FlatnessTests
open P103.Specs.Ch11.KunnethOppositeInterchange
open P103.Specs.Ch11.KunnethSequence
universe reindexK reindexI reindexJ reindexA reindexB

theorem directSum_reindex_congr_lof
    {K : Type reindexK} [Ring K] {I : Type reindexI} {J : Type reindexJ} [DecidableEq I] [DecidableEq J]
  {A : I → Type reindexA} {B : J → Type reindexB}
  [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (B j)]
  [∀ i, Module K (A i)] [∀ j, Module K (B j)]
    (e : I ≃ J)
    (f : ∀ j, A (e.symm j) ≃ₗ[K] B j)
    (i : I) (j : J) (h : i = e.symm j) (x : A i) (y : A (e.symm j))
    (hxy : cast (congrArg A h) x = y) :
    ((DirectSum.lequivCongrLeft K e).trans (DirectSum.congrLinearEquiv f))
      (DirectSum.lof K I A i x) = DirectSum.lof K J B j (f j y) := by
  change (DirectSum.congrLinearEquiv f)
    ((DirectSum.lequivCongrLeft K e) (DirectSum.lof K I A i x)) = _
  rw [DirectSum.lequivCongrLeft_lof K h x y hxy]
  change (DirectSum.lmap (fun j => (f j).toLinearMap))
    (DirectSum.lof K J (fun j => A (e.symm j)) j y) = _
  simp only [DirectSum.lmap_lof]
  rfl


universe naturalK naturalI naturalJ naturalA naturalA' naturalB naturalB'

theorem directSum_reindex_congr_natural
    {K : Type naturalK} [Ring K]
    {I : Type naturalI} {J : Type naturalJ} [DecidableEq I] [DecidableEq J]
    {A : I → Type naturalA} {A' : I → Type naturalA'}
    {B : J → Type naturalB} {B' : J → Type naturalB'}
    [∀ i, AddCommMonoid (A i)] [∀ i, AddCommMonoid (A' i)]
    [∀ j, AddCommMonoid (B j)] [∀ j, AddCommMonoid (B' j)]
    [∀ i, Module K (A i)] [∀ i, Module K (A' i)]
    [∀ j, Module K (B j)] [∀ j, Module K (B' j)]
    (e : I ≃ J) (E : ∀ j, A (e.symm j) ≃ₗ[K] B j)
    (E' : ∀ j, A' (e.symm j) ≃ₗ[K] B' j)
    (a : ∀ i, A i →ₗ[K] A' i) (b : ∀ j, B j →ₗ[K] B' j)
    (h : ∀ j x, E' j (a (e.symm j) x) = b j (E j x)) :
    ((DirectSum.lequivCongrLeft K e).trans (DirectSum.congrLinearEquiv E')).toLinearMap.comp
      (DirectSum.lmap a) =
    (DirectSum.lmap b).comp
      ((DirectSum.lequivCongrLeft K e).trans (DirectSum.congrLinearEquiv E)).toLinearMap := by
  apply DirectSum.linearMap_ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  apply LinearMap.ext
  intro x
  change ((DirectSum.lequivCongrLeft K e).trans (DirectSum.congrLinearEquiv E'))
      (DirectSum.lmap a (DirectSum.lof K I A (e.symm j) x)) =
    DirectSum.lmap b
      (((DirectSum.lequivCongrLeft K e).trans (DirectSum.congrLinearEquiv E))
        (DirectSum.lof K I A (e.symm j) x))
  rw [DirectSum.lmap_lof,
    directSum_reindex_congr_lof e E' (e.symm j) j rfl _ _ rfl,
    directSum_reindex_congr_lof e E (e.symm j) j rfl _ _ rfl,
    DirectSum.lmap_lof]
  exact congrArg (DirectSum.lof K J B' j) (h j x)


/-- Swapping the two indices of a homology diagonal. -/
def diagonalSwap (n : ℕ) : P103.Specs.Ch11.KunnethSequence.Diagonal n ≃ P103.Specs.Ch11.KunnethSequence.Diagonal n where
  toFun i := ⟨(i.val.2,i.val.1), by have := i.property; omega⟩
  invFun i := ⟨(i.val.2,i.val.1), by have := i.property; omega⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

/-- Swapping the two indices of a Tor diagonal. -/
def tailDiagonalSwap (n : ℕ) : TailDiagonal n ≃ TailDiagonal n where
  toFun i := ⟨(i.val.2,i.val.1), by have := i.property; omega⟩
  invFun i := ⟨(i.val.2,i.val.1), by have := i.property; omega⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

/-- Tensor transport along two actual module isomorphisms. -/
def balancedTensorCongr {A A' B B' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [Module R B] [Module R B']
    (e : A ≃ₗ[Rᵐᵒᵖ] A') (f : B ≃ₗ[R] B') :
    Tensor R A B ≃ₗ[ℤ] Tensor R A' B' :=
  LinearEquiv.ofLinearMap (tensorMap e.toLinearMap f.toLinearMap)
    (tensorMap e.symm.toLinearMap f.symm.toLinearMap)
    (by
      apply tensor_hom_ext; intro a b
      simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply]
      change tmul R (e (e.symm a)) (f (f.symm b)) = tmul R a b
      rw [e.apply_symm_apply, f.apply_symm_apply])
    (by
      apply tensor_hom_ext; intro a b
      simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply]
      change tmul R (e.symm (e a)) (f.symm (f b)) = tmul R a b
      rw [e.symm_apply_apply, f.symm_apply_apply])

/-- The tensor flip carries exactly the Koszul sign used on the total complex. -/
def signedHomologyTensorFlip (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (p q : ℕ) :
    Tensor R (Homology C p) (Homology D q) ≃ₗ[ℤ]
      Tensor Rᵐᵒᵖ (Homology (doubleOppositeComplex D) q) (Homology C p) := by
  letI := doubleOppositeModule R (Homology D q)
  exact ((tensorFlip (Homology C p) (Homology D q)).trans
    (balancedTensorCongr (homologyScalarEquiv (R := R) D q).symm
      (LinearEquiv.refl Rᵐᵒᵖ (Homology C p)))).trans
    (LinearEquiv.smulOfUnit (((p : ℤ) * (q : ℤ)).negOnePow))

/-- Signed interchange on the source's direct sum of tensor homology groups. -/
def tensorDiagonalFlip (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    TensorDiagonal C D n ≃ₗ[ℤ] TensorDiagonal (doubleOppositeComplex D) C n :=
  (DirectSum.lequivCongrLeft ℤ (diagonalSwap n)).trans
    (DirectSum.congrLinearEquiv (fun i : P103.Specs.Ch11.KunnethSequence.Diagonal n =>
      signedHomologyTensorFlip C D i.val.2 i.val.1))

@[simp] theorem tensorDiagonalFlip_lof
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ)
    (i : P103.Specs.Ch11.KunnethSequence.Diagonal n) (a : Homology C i.val.1) (b : Homology D i.val.2) :
    tensorDiagonalFlip C D n
      (DirectSum.lof ℤ _ _ i (tmul R a b)) =
    ((i.val.1 : ℤ) * (i.val.2 : ℤ)).negOnePow •
      (DirectSum.lof ℤ _ _ ((diagonalSwap n) i) (tmul Rᵐᵒᵖ ((homologyScalarEquiv D i.val.2).symm b) a)) := by
  change (DirectSum.congrLinearEquiv _)
    ((DirectSum.lequivCongrLeft ℤ (diagonalSwap n))
      (DirectSum.lof ℤ (P103.Specs.Ch11.KunnethSequence.Diagonal n) (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n => TensorTerm C D j.val)
        i (tmul R a b))) = _
  erw [DirectSum.lequivCongrLeft_lof (k := (diagonalSwap n) i) ℤ
    (by apply Subtype.ext; rfl) _ _ rfl]
  change (DirectSum.lmap (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n =>
      (signedHomologyTensorFlip C D j.val.2 j.val.1).toLinearMap))
    (DirectSum.lof ℤ (P103.Specs.Ch11.KunnethSequence.Diagonal n)
      (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n => TensorTerm C D ((diagonalSwap n).symm j).val)
      ((diagonalSwap n) i) (tmul R a b)) = _
  dsimp only [diagonalSwap, tailDiagonalSwap] at *
  erw [DirectSum.lmap_lof]
  change DirectSum.lof ℤ (P103.Specs.Ch11.KunnethSequence.Diagonal n)
    (fun j : P103.Specs.Ch11.KunnethSequence.Diagonal n => TensorTerm (doubleOppositeComplex D) C j.val) ((diagonalSwap n) i)
    (((i.val.1 : ℤ) * (i.val.2 : ℤ)).negOnePow •
      (tmul Rᵐᵒᵖ ((homologyScalarEquiv D i.val.2).symm b) a)) = _
  exact map_zsmul_unit _ _ _

/-- A fixed family of projective models for the homology of the opposite complex. -/
def oppositeHomologyModels (D : LeftComplex.{u,w} R) :
    HomologyModels (doubleOppositeComplex D) := fun q =>
  P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ (Homology (doubleOppositeComplex D) q))

/-- Change only the augmentation target along a specified module isomorphism. -/
def resolutionAlongEquiv {S : Type u} [Ring S] {A B : Type w}
    [AddCommGroup A] [AddCommGroup B] [Module S A] [Module S B]
    (P : LeftResolution S A) (e : A ≃ₗ[S] B) : LeftResolution S B where
  complex := P.complex
  ε := e.toLinearMap.comp P.ε
  surjective := e.surjective.comp P.surjective
  exact_zero := P.exact_zero.trans (by
    ext x
    change P.ε x = 0 ↔ e (P.ε x) = 0
    constructor
    · intro h; rw [h,map_zero]
    · intro h; exact e.injective (h.trans (map_zero e).symm))
  exact_succ := P.exact_succ

/-- Comparison lifts commute with changing the augmentation target. -/
theorem resolutionAlongEquiv_lift {S : Type u} [Ring S] {A A' B B' : Type w}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [Module S A] [Module S A'] [Module S B] [Module S B']
    (P : LeftResolution S A) (P' : LeftResolution S A')
    (e : A ≃ₗ[S] B) (e' : A' ≃ₗ[S] B')
    (f : A →ₗ[S] A') (g : B →ₗ[S] B') (m : P.complex ⟶ P'.complex)
    (hm : ChainLift P P' f m)
    (he : ∀ x, e' (f x) = g (e x)) :
    ChainLift (resolutionAlongEquiv P e) (resolutionAlongEquiv P' e') g m := by
  apply LinearMap.ext
  intro x
  change e' (P'.ε ((m.f 0).hom x)) = g (e (P.ε x))
  have hmx := LinearMap.congr_fun hm x
  change P'.ε ((m.f 0).hom x) = f (P.ε x) at hmx
  rw [hmx]
  exact he (P.ε x)

/-- The given opposite model, augmented to the explicitly transported homology module. -/
def oppositeCoefficientResolution (D : LeftComplex.{u,w} R)
    (Q : HomologyModels (doubleOppositeComplex D)) (q : ℕ) :
    letI := doubleOppositeModule R (Homology D q)
    LeftResolution Rᵐᵒᵖᵐᵒᵖ (Homology D q) := by
  letI := doubleOppositeModule R (Homology D q)
  exact resolutionAlongEquiv (Q q).val (homologyScalarEquiv (R := R) D q)

/-- The opposite-ring Tor identification on every actual component and model. -/
def torComponentUnflip (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (Q : HomologyModels (doubleOppositeComplex D))
    (p q : ℕ) :
    TorTerm (doubleOppositeComplex D) C Q (q,p) ≃ₗ[ℤ] TorTerm C D P (p,q) := by
  letI := doubleOppositeModule R (Homology D q)
  exact ((P103.Ch11.KunnethOppositeInterchange.allModelTorTransport R).equiv
    (ModuleCat.of Rᵐᵒᵖ (Homology C p)) (ModuleCat.of R (Homology D q))
    (P p).val (P p).property (oppositeCoefficientResolution (R := R) D Q q) (Q q).property 1).toAddEquiv.toIntLinearEquiv

/-- Koszul-normalized interchange on each actual Tor component. -/
def signedTorComponentUnflip (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (Q : HomologyModels (doubleOppositeComplex D))
    (p q : ℕ) :
    TorTerm (doubleOppositeComplex D) C Q (q,p) ≃ₗ[ℤ] TorTerm C D P (p,q) :=
  (torComponentUnflip C D P Q p q).trans
    (LinearEquiv.smulOfUnit (((p : ℤ) * (q : ℤ)).negOnePow))

/-- Signed opposite-ring Tor interchange, retaining the original right-left formula. -/
def torDiagonalUnflip (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (Q : HomologyModels (doubleOppositeComplex D)) (n : ℕ) :
    TorDiagonal (doubleOppositeComplex D) C Q n ≃ₗ[ℤ] TorDiagonal C D P n :=
  (DirectSum.lequivCongrLeft ℤ (tailDiagonalSwap n)).trans
    (DirectSum.congrLinearEquiv (fun i : TailDiagonal n =>
      signedTorComponentUnflip C D P Q i.val.1 i.val.2))

/-- Homology of the actual signed chain isomorphism. -/
def totalHomologyFlip (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    Homology (ordinaryTotal C D) n ≃ₗ[ℤ]
      Homology (ordinaryTotal (doubleOppositeComplex D) C) n :=
  ((quotientHomology (ComplexShape.down ℕ) n).mapIso
    (P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip C D)).toLinearEquiv.toAddEquiv.toIntLinearEquiv

/-- Flatness of the second factor is precisely first-factor flatness after transport. -/
theorem leftFlat_opposite (D : LeftComplex.{u,w} R)
    (hD : LeftFlatTermsAndBoundaries.{u,v,w} D) :
    FlatTermsAndBoundaries.{u,w,v} (doubleOppositeComplex D) := by
  constructor
  · intro q
    exact (P103.Ch11.KunnethOppositeInterchange.complex_transport D q).2.2.1.mp (hD.1 q)
  · intro q
    exact (P103.Ch11.KunnethOppositeInterchange.complex_transport D q).2.2.2.2.mp (hD.2 q)


@[simp] theorem torDiagonalUnflip_lof
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (Q : HomologyModels (doubleOppositeComplex D)) (n : ℕ)
    (i : TailDiagonal n) (a : TorTerm (doubleOppositeComplex D) C Q i.val) :
    torDiagonalUnflip C D P Q n (DirectSum.lof ℤ _ _ i a) =
      DirectSum.lof ℤ _ _ ((tailDiagonalSwap n) i)
        (signedTorComponentUnflip C D P Q i.val.2 i.val.1 a) := by
  exact directSum_reindex_congr_lof
    (A := fun j : TailDiagonal n => TorTerm (doubleOppositeComplex D) C Q j.val)
    (B := fun j : TailDiagonal n => TorTerm C D P j.val)
    (tailDiagonalSwap n) (fun j => signedTorComponentUnflip C D P Q j.val.1 j.val.2)
    i ((tailDiagonalSwap n) i) (by apply Subtype.ext; rfl) a a rfl

/-- Naturality of opposite Tor transport with abstract module objects and scalar identifications. -/
theorem torTransportAlongEquiv_natural
    (J : AllModelTorTransport.{u,v,w} R)
    (A A' : ModuleCat.{v} Rᵐᵒᵖ) (B B' : ModuleCat.{w} R)
    (V V' : ModuleCat.{w} Rᵐᵒᵖᵐᵒᵖ)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (P' : ProjectiveChoice Rᵐᵒᵖ A')
    (Q : ProjectiveChoice Rᵐᵒᵖᵐᵒᵖ V) (Q' : ProjectiveChoice Rᵐᵒᵖᵐᵒᵖ V')
    (e : letI := doubleOppositeModule R B; V ≃ₗ[Rᵐᵒᵖᵐᵒᵖ] B)
    (e' : letI := doubleOppositeModule R B'; V' ≃ₗ[Rᵐᵒᵖᵐᵒᵖ] B')
    (f : A ⟶ A') (g : B ⟶ B') (h : V ⟶ V')
    (he : ∀ x, e' (h.hom x) = g.hom (e x))
    (T : TorMaps.{u,v,w} R 1) (U : TorMaps.{u,w,v} Rᵐᵒᵖ 1) :
    letI := doubleOppositeModule R B
    letI := doubleOppositeModule R B'
    let E := J.equiv A B P.val P.property (resolutionAlongEquiv Q.val e) Q.property 1
    let E' := J.equiv A' B' P'.val P'.property (resolutionAlongEquiv Q'.val e') Q'.property 1
    ∀ x : TorWith Q.val A 1, E' (U.map Q Q' h f x) = T.map P P' f g (E x) := by
  letI := doubleOppositeModule R B
  letI := doubleOppositeModule R B'
  dsimp only
  let l := P103.Ch10.Comparison.chainMap P.val P'.val P.property f.hom
  let m := P103.Ch10.Comparison.chainMap Q.val Q'.val Q.property h.hom
  have hl := P103.Ch10.Comparison.chainMap_lifts P.val P'.val P.property f.hom
  have hm := P103.Ch10.Comparison.chainMap_lifts Q.val Q'.val Q.property h.hom
  have hm' := resolutionAlongEquiv_lift Q.val Q'.val e e' h.hom
    (doubleOppositeLinear (R := R) g.hom) m hm he
  have hnat := J.naturality A A' B B' P.val P'.val P.property P'.property
    (resolutionAlongEquiv Q.val e) (resolutionAlongEquiv Q'.val e') Q.property Q'.property
    f g l m hl hm' 1
  have hT := T.formula P P' f g l hl
  have hU := U.formula Q Q' h f m hm
  intro x
  exact (congrArg (J.equiv A' B' P'.val P'.property (resolutionAlongEquiv Q'.val e') Q'.property 1)
    (DFunLike.congr_fun hU x)).trans
      ((DFunLike.congr_fun hnat x).trans
        (DFunLike.congr_fun hT
          (J.equiv A B P.val P.property (resolutionAlongEquiv Q.val e) Q.property 1 x)).symm)

/-- Canonical opposite Tor transport is natural for every Tor map construction. -/
theorem torComponentUnflip_natural
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D')
    (P : HomologyModels C) (P' : HomologyModels C')
    (Q : HomologyModels (doubleOppositeComplex D))
    (Q' : HomologyModels (doubleOppositeComplex D'))
    (T : TorMaps.{u,v,w} R 1) (U : TorMaps.{u,w,v} Rᵐᵒᵖ 1) (p q : ℕ)
    (x : TorTerm (doubleOppositeComplex D) C Q (q,p)) :
    torComponentUnflip C' D' P' Q' p q
      (U.map (Q q) (Q' q)
        (ModuleCat.ofHom (homologyMap (doubleOppositeMap g) q))
        (ModuleCat.ofHom (homologyMap f p)) x) =
      T.map (P p) (P' p) (ModuleCat.ofHom (homologyMap f p))
        (ModuleCat.ofHom (homologyMap g q))
          (torComponentUnflip C D P Q p q x) := by
  exact torTransportAlongEquiv_natural
    (P103.Ch11.KunnethOppositeInterchange.allModelTorTransport R)
    (ModuleCat.of Rᵐᵒᵖ (Homology C p)) (ModuleCat.of Rᵐᵒᵖ (Homology C' p))
    (ModuleCat.of R (Homology D q)) (ModuleCat.of R (Homology D' q))
    (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ (Homology (doubleOppositeComplex D) q))
    (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ (Homology (doubleOppositeComplex D') q))
    (P p) (P' p) (Q q) (Q' q)
    (homologyScalarEquiv D q) (homologyScalarEquiv D' q)
    (ModuleCat.ofHom (homologyMap f p)) (ModuleCat.ofHom (homologyMap g q))
    (ModuleCat.ofHom (homologyMap (doubleOppositeMap g) q))
    (fun x => P103.Ch11.KunnethOppositeInterchange.homology_scalar_natural g q x)
    T U x


/-- The original Tor diagonal square, including changes of either projective model. -/
theorem torDiagonalUnflip_natural
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D')
    (P : HomologyModels C) (P' : HomologyModels C')
    (Q : HomologyModels (doubleOppositeComplex D))
    (Q' : HomologyModels (doubleOppositeComplex D'))
    (T : TorMaps.{u,v,w} R 1) (U : TorMaps.{u,w,v} Rᵐᵒᵖ 1) (n : ℕ) :
    (torDiagonalUnflip C' D' P' Q' n).toLinearMap.comp
      (torDiagonalMap (doubleOppositeMap g) f Q Q' U n) =
    (torDiagonalMap f g P P' T n).comp (torDiagonalUnflip C D P Q n).toLinearMap := by
  exact directSum_reindex_congr_natural
    (A := fun j : TailDiagonal n => TorTerm (doubleOppositeComplex D) C Q j.val)
    (A' := fun j : TailDiagonal n => TorTerm (doubleOppositeComplex D') C' Q' j.val)
    (B := fun j : TailDiagonal n => TorTerm C D P j.val)
    (B' := fun j : TailDiagonal n => TorTerm C' D' P' j.val)
    (tailDiagonalSwap n)
    (fun j => signedTorComponentUnflip C D P Q j.val.1 j.val.2)
    (fun j => signedTorComponentUnflip C' D' P' Q' j.val.1 j.val.2)
    (fun j => (U.map (Q j.val.1) (Q' j.val.1)
      (ModuleCat.ofHom (homologyMap (doubleOppositeMap g) j.val.1))
      (ModuleCat.ofHom (homologyMap f j.val.2))).toAddMonoidHom.toIntLinearMap)
    (fun j => (T.map (P j.val.1) (P' j.val.1)
      (ModuleCat.ofHom (homologyMap f j.val.1))
      (ModuleCat.ofHom (homologyMap g j.val.2))).toAddMonoidHom.toIntLinearMap)
    (fun j x => by
      exact (congrArg (fun z => (((j.val.1 : ℤ) * (j.val.2 : ℤ)).negOnePow • z))
        (torComponentUnflip_natural f g P P' Q Q' T U j.val.1 j.val.2 x)).trans
          (map_zsmul_unit _ _ _).symm)

/-- Naturality on the actual signed total homology is simultaneous in both factors. -/
theorem totalHomologyFlip_natural
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    (totalHomologyFlip C' D' n).toLinearMap.comp
      (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap =
    (homologyMap (ordinaryTotalMap (doubleOppositeMap g) f) n).toAddMonoidHom.toIntLinearMap.comp
      (totalHomologyFlip C D n).toLinearMap :=
by
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun
    (P103.Ch11.TorBalance.homologyMap_square _ _ _ _
      (P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip_natural f g) n) x


/-- Scalar transport preserves the actual quotient representative class. -/
theorem oppositeHomologyClass (D : LeftComplex.{u,w} R) (q : ℕ) (x : cycles D q) :
    (homologyScalarEquiv (R := R) D q).symm (homologyClass D q x) =
      homologyClass (doubleOppositeComplex D) q (⟨x.val,x.property⟩ : cycles (doubleOppositeComplex D) q) := rfl

/-- Transport of the prescribed elementary class formula across signed interchange. -/
theorem left_alpha_formula
    (hpure : pure_tensor_cycleType.{u,w,v})
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (Q : HomologyModels (doubleOppositeComplex D)) (n : ℕ)
    (S : NormalizedDegreeSequence (doubleOppositeComplex D) C Q n) :
    AlphaFormula C D n
      ((totalHomologyFlip C D n).symm.toLinearMap.comp
        (S.α.comp (tensorDiagonalFlip C D n).toLinearMap)) := by
  intro i c x z hz
  apply (totalHomologyFlip C D n).injective
  change (totalHomologyFlip C D n)
      ((totalHomologyFlip C D n).symm
        (S.α ((tensorDiagonalFlip C D n) _))) = _
  rw [LinearEquiv.apply_symm_apply, tensorDiagonalFlip_lof, map_zsmul_unit]
  let x' : cycles (doubleOppositeComplex D) i.val.2 := ⟨x.val,x.property⟩
  let z' : cycles (ordinaryTotal (doubleOppositeComplex D) C) n :=
    ⟨ordinaryInclusion (doubleOppositeComplex D) C i.val.2 i.val.1 n
      (by have := i.property; omega) (tmul Rᵐᵒᵖ x'.val c.val),
      hpure Rᵐᵒᵖ (doubleOppositeComplex D) C i.val.2 i.val.1 n
        (by have := i.property; omega) x' c⟩
  erw [oppositeHomologyClass, S.α_formula ((diagonalSwap n) i) x' c z' rfl]
  change ((i.val.1 : ℤ) * (i.val.2 : ℤ)).negOnePow •
      homologyClass (ordinaryTotal (doubleOppositeComplex D) C) n z' =
    homologyClass (ordinaryTotal (doubleOppositeComplex D) C) n
      (cyclesMap (P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip C D).hom n z)
  rw [← map_zsmul_unit]
  congr 1
  apply Subtype.ext
  change ((i.val.1 : ℤ) * (i.val.2 : ℤ)).negOnePow •
      ordinaryInclusion (doubleOppositeComplex D) C i.val.2 i.val.1 n
        (by have := i.property; omega) (tmul Rᵐᵒᵖ x.val c.val) =
    (((P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip C D).hom.f n).hom z.val)
  rw [hz, P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip_formula]

/-- Explicit second-factor sequence, with signed tensor and Tor comparisons. -/
def leftTransportedSequence
    (hpure : pure_tensor_cycleType.{u,w,v})
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (Q : HomologyModels (doubleOppositeComplex D)) (n : ℕ)
    (S : NormalizedDegreeSequence (doubleOppositeComplex D) C Q n) :
    DegreeSequence C D P n := by
  let ht := shortExact_transport S.α S.β
    (tensorDiagonalFlip C D n) (totalHomologyFlip C D n).symm
    (torDiagonalUnflip C D P Q n) S.injective_α S.exact S.surjective_β
  exact
    { α := (totalHomologyFlip C D n).symm.toLinearMap.comp
        (S.α.comp (tensorDiagonalFlip C D n).toLinearMap)
      β := (torDiagonalUnflip C D P Q n).toLinearMap.comp
        (S.β.comp (totalHomologyFlip C D n).toLinearMap)
      injective_α := ht.1
      exact := ht.2.1
      surjective_β := ht.2.2
      α_formula := left_alpha_formula hpure C D Q n S }


/-- The diagonal equivalence has precisely the frozen tensor-interchange map. -/
theorem tensorDiagonalFlip_eq_signedTensorInterchange
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    (tensorDiagonalFlip C D n).toLinearMap = signedTensorInterchange C D n := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro t
  induction t using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      change tensorDiagonalFlip C D n (DirectSum.lof ℤ _ _ i (tmul R a b)) = _
      rw [tensorDiagonalFlip_lof]
      simp only [signedTensorInterchange, DirectSum.toModule_lof, LinearMap.comp_apply,
        LinearMap.smul_apply]
      rw [map_zsmul_unit]
      congr 1
    | add x y hx hy =>
      change tensorDiagonalFlip C D n (DirectSum.lof ℤ _ _ i
        ((relations R (Homology C i.val.1) (Homology D i.val.2)).mkQ (x+y))) =
        signedTensorInterchange C D n (DirectSum.lof ℤ _ _ i
          ((relations R (Homology C i.val.1) (Homology D i.val.2)).mkQ (x+y)))
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy


/-- The transported augmentation target is definitionally the shared homology quotient. -/
theorem torComponentUnflip_eq_interchange
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (Q : HomologyModels (doubleOppositeComplex D)) (p q : ℕ) :
    torComponentUnflip C D P Q p q =
      torInterchangeComponent C D P Q
        (P103.Ch11.KunnethOppositeInterchange.allModelTorTransport R) p q := by
  rfl

/-- The component formula retains both the index exchange and the Koszul sign. -/
theorem torDiagonalUnflip_apply
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (Q : HomologyModels (doubleOppositeComplex D)) (n : ℕ)
    (x : TorDiagonal (doubleOppositeComplex D) C Q n) (i : TailDiagonal n) :
    (torDiagonalUnflip C D P Q n x) i =
      ((i.val.1 : ℤ) * (i.val.2 : ℤ)).negOnePow •
        torInterchangeComponent C D P Q
          (P103.Ch11.KunnethOppositeInterchange.allModelTorTransport R) i.val.1 i.val.2
          (x (⟨(i.val.2,i.val.1),by have := i.property; omega⟩ : TailDiagonal n)) := by
  change signedTorComponentUnflip C D P Q i.val.1 i.val.2
    ((DirectSum.lequivCongrLeft ℤ (tailDiagonalSwap n)) x i) = _
  rw [DirectSum.lequivCongrLeft_apply]
  change ((i.val.1 : ℤ) * (i.val.2 : ℤ)).negOnePow •
      torComponentUnflip C D P Q i.val.1 i.val.2 _ = _
  rw [torComponentUnflip_eq_interchange]
  rfl

/-- Both arrows are the specified transport of the normalized opposite-ring sequence. -/
theorem leftTransportedSequence_normalization
    (hpure : pure_tensor_cycleType.{u,w,v})
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (Q : HomologyModels (doubleOppositeComplex D)) (n : ℕ)
    (S : NormalizedDegreeSequence (doubleOppositeComplex D) C Q n) :
    LeftNormalization C D P n (leftTransportedSequence hpure C D P Q n S) := by
  let I : SignedInterchange.{u,v,w} R :=
    { iso := P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip
      formula := P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip_formula
      naturality := P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip_natural
      homology_naturality := fun f g n =>
        P103.Ch11.TorBalance.homologyMap_square _ _ _ _
          (P103.Ch11.KunnethOppositeInterchange.ordinarySignedFlip_natural f g) n }
  refine ⟨I, P103.Ch11.KunnethOppositeInterchange.allModelTorTransport R, Q, S, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change totalHomologyFlip C D n
      ((totalHomologyFlip C D n).symm (S.α (tensorDiagonalFlip C D n x))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg S.α (DFunLike.congr_fun
      (tensorDiagonalFlip_eq_signedTensorInterchange C D n) x)
  · intro x i
    change (torDiagonalUnflip C D P Q n (S.β (totalHomologyFlip C D n x))) i = _
    exact torDiagonalUnflip_apply C D P Q n _ i

/-- The first-factor theorem gives every second-factor sequence over the opposite ring. -/
theorem left_sequence_from_right
    (hr : right_sequenceType.{u,w,v}) (hpure : pure_tensor_cycleType.{u,w,v}) :
    left_sequenceType.{u,v,w} := by
  intro R _ C D hD P n
  let Q := oppositeHomologyModels D
  obtain ⟨S⟩ := hr Rᵐᵒᵖ (doubleOppositeComplex D) (leftFlat_opposite D hD) C Q n
  exact ⟨leftTransportedSequence hpure C D P Q n S⟩

/-- Naturality survives the three opposite-ring comparison isomorphisms. -/
theorem leftTransportedSequence_natural
    (hpure : pure_tensor_cycleType.{u,w,v})
    (hn : normalized_naturalType.{u,w,v})
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D')
    (P : HomologyModels C) (P' : HomologyModels C')
    (Q : HomologyModels (doubleOppositeComplex D))
    (Q' : HomologyModels (doubleOppositeComplex D'))
    (T : TorMaps.{u,v,w} R 1) (U : TorMaps.{u,w,v} Rᵐᵒᵖ 1) (n : ℕ)
    (S : NormalizedDegreeSequence (doubleOppositeComplex D) C Q n)
    (S' : NormalizedDegreeSequence (doubleOppositeComplex D') C' Q' n) :
    ((homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap).comp
        (leftTransportedSequence hpure C D P Q n S).α =
      (leftTransportedSequence hpure C' D' P' Q' n S').α.comp
        (tensorDiagonalMap f g n) ∧
    (torDiagonalMap f g P P' T n).comp (leftTransportedSequence hpure C D P Q n S).β =
      (leftTransportedSequence hpure C' D' P' Q' n S').β.comp
        (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap := by
  refine ⟨alpha_natural R C C' D D' f g n _ _
    (leftTransportedSequence hpure C D P Q n S).α_formula
    (leftTransportedSequence hpure C' D' P' Q' n S').α_formula, ?_⟩
  apply LinearMap.ext
  intro x
  have ht := DFunLike.congr_fun
    (torDiagonalUnflip_natural f g P P' Q Q' T U n) (S.β (totalHomologyFlip C D n x))
  have hs := DFunLike.congr_fun
    (hn Rᵐᵒᵖ (doubleOppositeComplex D) (doubleOppositeComplex D') C C'
      (doubleOppositeMap g) f Q Q' U n S S').2 (totalHomologyFlip C D n x)
  have hm := DFunLike.congr_fun (totalHomologyFlip_natural f g n) x
  dsimp only [LinearMap.comp_apply] at ht hs hm
  change torDiagonalMap f g P P' T n
      (torDiagonalUnflip C D P Q n (S.β (totalHomologyFlip C D n x))) =
    torDiagonalUnflip C' D' P' Q' n
      (S'.β (totalHomologyFlip C' D' n (homologyMap (ordinaryTotalMap f g) n x)))
  calc
    torDiagonalMap f g P P' T n
        (torDiagonalUnflip C D P Q n (S.β (totalHomologyFlip C D n x))) =
      torDiagonalUnflip C' D' P' Q' n
        (torDiagonalMap (doubleOppositeMap g) f Q Q' U n
          (S.β (totalHomologyFlip C D n x))) := ht.symm
    _ = torDiagonalUnflip C' D' P' Q' n
      (S'.β (homologyMap (ordinaryTotalMap (doubleOppositeMap g) f) n
        (totalHomologyFlip C D n x))) := congrArg (torDiagonalUnflip C' D' P' Q' n) hs
    _ = torDiagonalUnflip C' D' P' Q' n
      (S'.β (totalHomologyFlip C' D' n (homologyMap (ordinaryTotalMap f g) n x))) :=
        congrArg (fun y => torDiagonalUnflip C' D' P' Q' n (S'.β y)) hm.symm

/-- A single simultaneous natural family under exactly the second-factor hypotheses. -/
theorem left_natural_sequence_from_right
    (hr : right_sequenceType.{u,w,v}) (hpure : pure_tensor_cycleType.{u,w,v})
    (hn : normalized_naturalType.{u,w,v}) : left_natural_sequenceType.{u,v,w} := by
  classical
  intro R _
  let Q (D : LeftComplex.{u,w} R) := oppositeHomologyModels D
  let S (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
      (hD : LeftFlatTermsAndBoundaries.{u,v,w} D) (n : ℕ) :
      NormalizedDegreeSequence (doubleOppositeComplex D) C (Q D) n :=
    Classical.choice (hr Rᵐᵒᵖ (doubleOppositeComplex D) (leftFlat_opposite D hD) C (Q D) n)
  refine ⟨{ sequence := fun C D hD P n => leftTransportedSequence hpure C D P (Q D) n (S C D hD n)
            normalization := fun C D hD P n =>
              leftTransportedSequence_normalization hpure C D P (Q D) n (S C D hD n)
            naturality := ?_ }⟩
  intro C C' D D' hD hD' f g P P' T n
  obtain ⟨U⟩ := P103.Ch11.ExtTorDefinitions.tor_bifunctorial Rᵐᵒᵖ 1
  exact leftTransportedSequence_natural hpure hn f g P P' (Q D) (Q D') T U n
    (S C D hD n) (S C' D' hD' n)


/-- Second-factor flatness gives the same arbitrary-ring right-left Künneth sequence. -/
theorem left_sequence : left_sequenceType.{u,v,w} :=
  left_sequence_from_right right_sequence pure_tensor_cycle

/-- The second-factor sequences form one simultaneous natural family. -/
theorem left_natural_sequence : left_natural_sequenceType.{u,v,w} :=
  left_natural_sequence_from_right right_sequence pure_tensor_cycle normalized_natural


end OppositeOrientation


/-- Naturality under the genuine coefficient scalar map is scalar compatibility. -/
theorem scalarCompatibility_of_natural {K : Type u} [CommRing K]
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K) (P : HomologyModels C)
    (T : TorMaps.{u,v,w} K 1) (n : ℕ) (S : DegreeSequence C D P n)
    (hn : ∀ g : D ⟶ D,
      ((homologyMap (ordinaryTotalMap (𝟙 C) g) n).toAddMonoidHom.toIntLinearMap).comp S.α =
        S.α.comp (tensorDiagonalMap (𝟙 C) g n) ∧
      (torDiagonalMap (𝟙 C) g P P T n).comp S.β =
        S.β.comp (homologyMap (ordinaryTotalMap (𝟙 C) g) n).toAddMonoidHom.toIntLinearMap) :
    ScalarCompatibility C D P T n S := by
  classical
  intro r
  let σ := P103.Ch11.TorBalance.scalarChainMap D r
  have hσ (q : ℕ) (x : D.X q) : (σ.f q).hom x = r • x := rfl
  have hH (q : ℕ) : homologyMap σ q =
      (scalarMap (ModuleCat.of K (Homology D q)) r).hom := by
    apply LinearMap.ext
    intro x
    obtain ⟨z,rfl⟩ := (cycleBoundaries D q).mkQ_surjective x
    change homologyClass D q (cyclesMap σ q z) = r • homologyClass D q z
    rw [← map_smul]
    apply congrArg (homologyClass D q)
    apply Subtype.ext
    exact hσ q z.val
  have ht : tensorDiagonalMap (𝟙 C) σ n = tensorScalarDiagonal C D n r := by
    unfold tensorDiagonalMap tensorScalarDiagonal
    apply congrArg DirectSum.lmap
    funext i
    exact congrArg₂ tensorMap (P103.Ch10.Complexes.homologyMap_id C i.val.1) (hH i.val.2)
  refine ⟨σ, hσ, ?_, ?_, ?_, ?_, ?_⟩
  · intro q x
    exact DFunLike.congr_fun (hH q) x
  · intro p q h c x
    have h := P103.Ch11.TorBalance.ordinaryTotalMap_inclusion (𝟙 C) σ p q n h c x
    exact h
  · intro i a b
    simp only [tensorScalarDiagonal, DirectSum.lmap_lof, tensorMap_tmul]
    rfl
  · exact (hn σ).1.trans (congrArg (fun m => S.α.comp m) ht)
  · intro x i
    have h := congrArg (fun t : TorDiagonal C D P n => t i)
      (DFunLike.congr_fun (hn σ).2 x)
    change (S.β (homologyMap (ordinaryTotalMap (𝟙 C) σ) n x)) i =
      T.map (P i.val.1) (P i.val.1) (𝟙 _) (scalarMap (ModuleCat.of K (Homology D i.val.2)) r)
        ((S.β x) i)
    change T.map (P i.val.1) (P i.val.1)
        (ModuleCat.ofHom (homologyMap (𝟙 C) i.val.1))
        (ModuleCat.ofHom (homologyMap σ i.val.2)) ((S.β x) i) =
      (S.β (homologyMap (ordinaryTotalMap (𝟙 C) σ) n x)) i at h
    have hf : ModuleCat.ofHom (homologyMap (𝟙 C) i.val.1) = 𝟙 (ModuleCat.of Kᵐᵒᵖ (Homology C i.val.1)) := by
      apply ModuleCat.hom_ext
      exact P103.Ch10.Complexes.homologyMap_id C i.val.1
    have hg : ModuleCat.ofHom (homologyMap σ i.val.2) =
        scalarMap (ModuleCat.of K (Homology D i.val.2)) r := by
      apply ModuleCat.hom_ext
      exact hH i.val.2
    rw [hf,hg] at h
    exact h.symm


/-- The two natural families respect the actual coefficient scalar actions. -/
theorem scalar_compatibility : P103.Specs.Ch11.KunnethSequence.scalar_compatibilityType.{u,v,w} := by
  intro K _
  constructor
  · intro C D P T n S
    apply scalarCompatibility_of_natural C D P T n S.toDegreeSequence
    intro g
    exact normalized_natural K C C D D (𝟙 C) g P P T n S S
  · intro L C D hD P T n
    apply scalarCompatibility_of_natural C D P T n (L.sequence C D hD P n)
    intro g
    exact L.naturality C C D D hD hD (𝟙 C) g P P T n

end
end P103.Ch11.KunnethSequence
