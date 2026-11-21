import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethTotalConnector
import MathGenome.Internal.AlgebraCore.P103.Ch11.KunnethFlatColumns
import MathGenome.Internal.AlgebraCore.P103.Ch11.UniversalCoefficientsHomology

namespace P103.Ch11.KunnethTotalConnector
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.KunnethFlatColumns
open P103.Specs.Ch11.KunnethTotalConnector
open P103.Ch11.FlatResolutions P103.Ch11.KunnethFlatColumns
noncomputable section
universe u v w
variable {R : Type u} [Ring R]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The summand formula extended from pure tensors to all tensors. -/
theorem totalMap_inclusion
    {C C' : Complex.{u,v} R} {D D' : ChainComplex (ModuleCat.{w} R) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (p q n : ℕ) (h : p+q=n)
    (z : Tensor R (C.X p) (D.X q)) :
    ((ordinaryTotalMap f g).f n).hom (ordinaryInclusion C D p q n h z) =
      ordinaryInclusion C' D' p q n h (tensorMap (f.f p).hom (g.f q).hom z) := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht a b => exact P103.Ch11.TorBalance.ordinaryTotalMap_inclusion f g p q n h a b
  | ha a b ha hb => simp only [map_add, ha, hb]

/-- Total maps act componentwise on the finite ordinary diagonal. -/
theorem projection_totalMap
    {C C' : Complex.{u,v} R} {D D' : ChainComplex (ModuleCat.{w} R) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (p q n : ℕ) (h : p+q=n)
    (z : (ordinaryTotal C D).X n) :
    ordinaryProjection C' D' p q n h (((ordinaryTotalMap f g).f n).hom z) =
      tensorMap (f.f p).hom (g.f q).hom (ordinaryProjection C D p q n h z) := by
  classical
  conv_lhs => rw [← ordinary_reconstruction C D n z]
  conv_rhs => rw [← ordinary_reconstruction C D n z]
  simp only [map_sum, totalMap_inclusion]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hip : i.val.1=p
  · have hiq : i.val.2=q := by have := i.property; omega
    rcases i with ⟨⟨k,l⟩,hi⟩
    dsimp at hip hiq
    subst k
    subst l
    rw [ordinaryProjection_inclusion, ordinaryProjection_inclusion]
  · rw [ordinaryProjection_inclusion_ne _ _ i.val.1 i.val.2 p q n i.property h (Or.inl hip),
      ordinaryProjection_inclusion_ne _ _ i.val.1 i.val.2 p q n i.property h (Or.inl hip), map_zero]

/-- Componentwise tensor short exactness survives the actual coproduct total. -/
theorem total_degreewise_exact : total_degreewise_exactType.{u,v,w} := by
  intro R _ C hC D n
  classical
  have hs (p q : ℕ) :
      Function.Injective (tensorMap (cycles C p).subtype (LinearMap.id : D.X q →ₗ[R] D.X q)) ∧
      Function.Exact (tensorMap (cycles C p).subtype (LinearMap.id : D.X q →ₗ[R] D.X q))
        (tensorMap (boundaryProjectionTerm C p) (LinearMap.id : D.X q →ₗ[R] D.X q)) ∧
      Function.Surjective (tensorMap (boundaryProjectionTerm C p)
        (LinearMap.id : D.X q →ₗ[R] D.X q)) :=
    P103.Ch11.UniversalCoefficientsHomology.tensor_degreewise_exact R C hC (D.X q) p
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply ordinary_ext (cycleComplex C) D n
    intro p q h
    apply (hs p q).1
    have H := congrArg (ordinaryProjection C D p q n h) hab
    simpa only [inclusion, projection_totalMap, cycleInclusion,
      HomologicalComplex.id_f, ModuleCat.hom_id, ModuleCat.hom_ofHom] using H
  · intro z
    constructor
    · intro hz
      have hz' (i : Diagonal n) :
          tensorMap (boundaryProjectionTerm C i.val.1) (LinearMap.id : D.X i.val.2 →ₗ[R] D.X i.val.2)
            (ordinaryProjection C D i.val.1 i.val.2 n i.property z) = 0 := by
        have H := congrArg (ordinaryProjection (shiftedBoundaryComplex C) D
          i.val.1 i.val.2 n i.property) hz
        dsimp only [projection] at H
        rw [projection_totalMap, map_zero] at H
        simpa only [HomologicalComplex.id_f, ModuleCat.hom_id,
          boundaryProjection, ModuleCat.hom_ofHom] using H
      choose a ha using fun i : Diagonal n => (hs i.val.1 i.val.2).2.1 _ |>.mp (hz' i)
      refine ⟨∑ i : Diagonal n,
        ordinaryInclusion (cycleComplex C) D i.val.1 i.val.2 n i.property (a i), ?_⟩
      rw [map_sum]
      calc
        _ = ∑ i : Diagonal n, ordinaryInclusion C D i.val.1 i.val.2 n i.property
            (ordinaryProjection C D i.val.1 i.val.2 n i.property z) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [inclusion, totalMap_inclusion]
          simp only [cycleInclusion, HomologicalComplex.id_f, ModuleCat.hom_id,
            ModuleCat.hom_ofHom, ha i]
        _ = z := ordinary_reconstruction C D n z
    · rintro ⟨a,rfl⟩
      apply ordinary_ext (shiftedBoundaryComplex C) D n
      intro p q h
      rw [projection, projection_totalMap, inclusion, projection_totalMap, map_zero]
      exact (hs p q).2.1.apply_apply_eq_zero _
  · intro z
    choose a ha using fun i : Diagonal n => (hs i.val.1 i.val.2).2.2
      (ordinaryProjection (shiftedBoundaryComplex C) D i.val.1 i.val.2 n i.property z)
    refine ⟨∑ i : Diagonal n, ordinaryInclusion C D i.val.1 i.val.2 n i.property (a i), ?_⟩
    rw [map_sum]
    calc
      _ = ∑ i : Diagonal n,
          ordinaryInclusion (shiftedBoundaryComplex C) D i.val.1 i.val.2 n i.property
            (ordinaryProjection (shiftedBoundaryComplex C) D i.val.1 i.val.2 n i.property z) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [projection, totalMap_inclusion]
        simp only [boundaryProjection, HomologicalComplex.id_f, ModuleCat.hom_id,
          ModuleCat.hom_ofHom, ha i]
      _ = z := ordinary_reconstruction (shiftedBoundaryComplex C) D n z

/-- A cycle in D makes the vertical part of this lifted differential vanish.
Only the positive horizontal differential remains. -/
theorem lifted_tensor_d (C : Complex.{u,v} R)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (c : C.X (p+1)) (x : cycles D q) :
    ((ordinaryTotal C D).d (n+1) n).hom
      (ordinaryInclusion C D (p+1) q (n+1) (by omega) (tmul R c x.val)) =
    ordinaryInclusion C D p q n h (tmul R ((C.d (p+1) p).hom c) x.val) := by
  apply ordinary_ext C D n
  intro k l hkl
  have H := LinearMap.congr_fun (ordinaryProjection_d C D k l n hkl)
    (ordinaryInclusion C D (p+1) q (n+1) (by omega) (tmul R c x.val))
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at H
  rw [H]
  have hv : tensorMap (LinearMap.id : C.X k →ₗ[Rᵐᵒᵖ] C.X k) (D.d (l+1) l).hom
      (ordinaryProjection C D k (l+1) (n+1) (by omega)
        (ordinaryInclusion C D (p+1) q (n+1) (by omega) (tmul R c x.val))) = 0 := by
    by_cases hk : k=p+1
    · subst k
      by_cases hq : q=l+1
      · subst q
        rw [ordinaryProjection_inclusion]
        change tmul R c ((D.d (l+1) l).hom x.val) = 0
        have hx := x.property
        change (D.d (l+1) ((ComplexShape.down ℕ).next (l+1))).hom x.val = 0 at hx
        rw [ChainComplex.next_nat_succ] at hx
        rw [hx, tmul_zero]
      · rw [ordinaryProjection_inclusion_ne C D (p+1) q (p+1) (l+1) (n+1)
          (by omega) (by omega) (Or.inr hq), map_zero]
    · rw [ordinaryProjection_inclusion_ne C D (p+1) q k (l+1) (n+1)
        (by omega) (by omega) (Or.inl (Ne.symm hk)), map_zero]
  rw [hv, smul_zero, add_zero]
  by_cases hk : k=p
  · subst k
    have hl : l=q := by omega
    subst l
    rw [ordinaryProjection_inclusion, ordinaryProjection_inclusion]
    rfl
  · rw [ordinaryProjection_inclusion_ne C D (p+1) q (k+1) l (n+1)
      (by omega) (by omega) (Or.inl (by omega)), map_zero,
      ordinaryProjection_inclusion_ne C D p q k l n h hkl (Or.inl (Ne.symm hk))]

/-- Every connector with the full representative formula has the prescribed
positive normalization in all flat-column coordinates. -/
theorem connector_formula (C : Complex.{u,v} R)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ)
    (δ : Homology (ordinaryTotal (shiftedBoundaryComplex C) D) (n+1) →ₗ[ℤ]
      Homology (ordinaryTotal (cycleComplex C) D) n)
    (hδ : TotalConnecting C D n δ) : ConnectorFormula C D n δ := by
  intro eZ eL heZ heL p q h b x
  obtain ⟨x,rfl⟩ := (cycleBoundaries D q).mkQ_surjective x
  obtain ⟨c,hc⟩ := (P103.Ch11.UniversalCoefficientsHomology.cycle_boundary_shortExact C (p+1)).2.2 b
  obtain ⟨zL,hzL,heL⟩ := heL (p+1) q (by omega) b x
  obtain ⟨zZ,hzZ,heZ⟩ := heZ p q h (boundaryToCycles C p b) x
  erw [heL, heZ]
  apply hδ zL (ordinaryInclusion C D (p+1) q (n+1) (by omega) (tmul R c x.val)) zZ
  · rw [hzL]
    rw [projection, P103.Ch11.TorBalance.ordinaryTotalMap_inclusion]
    simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply,
      boundaryProjection, ModuleCat.hom_ofHom]
    exact congrArg (fun t => ordinaryInclusion (shiftedBoundaryComplex C) D (p+1) q
      (n+1) (by omega) (tmul R t x.val)) hc
  · rw [hzZ]
    rw [inclusion, P103.Ch11.TorBalance.ordinaryTotalMap_inclusion, lifted_tensor_d]
    have hc' : (C.d (p+1) p).hom c = b.val := congrArg Subtype.val hc
    rw [hc']
    rfl

/-- The actual long exact sequence, including independence and uniqueness of
the connector and its normalized component formula. -/
theorem total_connector : total_connectorType.{u,v,w} := by
  intro R _ C hC D n
  obtain ⟨δ,hδ,hunique⟩ := P103.Ch10.HomologySequence.sequence
    (inclusion C D) (projection C D) (total_degreewise_exact R C hC D) (n+1) n (by rfl)
  let δ' := δ.toAddMonoidHom.toIntLinearMap
  have hc : TotalConnecting C D n δ' := hδ.1
  refine ⟨δ', ⟨hc, hδ.2, connector_formula C D n δ' hc⟩, ?_⟩
  intro ε hε
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Quotient.exists_rep z
  obtain ⟨b,a,hb,ha⟩ := P103.Ch10.HomologySequence.lifts
    (inclusion C D) (projection C D) (total_degreewise_exact R C hC D) (by rfl) z
  exact (hε.1 z b a hb ha).trans (hδ.1 z b a hb ha).symm

/-- Only (0,0) occurs in degree zero, and L₀ is the zero module. -/
theorem shifted_total_zero (C : Complex.{u,v} R)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    Subsingleton ((ordinaryTotal (shiftedBoundaryComplex C) D).X 0) := by
  refine ⟨fun a b => ?_⟩
  apply ordinary_ext (shiftedBoundaryComplex C) D 0
  intro p q h
  have hp : p=0 := by omega
  have hq : q=0 := by omega
  subst p
  subst q
  exact Subsingleton.elim _ _

/-- Endpoint exactness is proved directly in degree zero, where every
chain is a cycle. There is no use of degree -1 of a natural complex. -/
theorem total_zero : total_zeroType.{u,v,w} := by
  intro R _ C hC D
  have hterm := shifted_total_zero C D
  have hzero : Subsingleton (Homology (ordinaryTotal (shiftedBoundaryComplex C) D) 0) := by
    let inst : Subsingleton ((ordinaryTotal (shiftedBoundaryComplex C) D).X 0) := hterm
    exact inferInstance
  have he : Function.Exact (homologyMap (inclusion C D) 0) (homologyMap (projection C D) 0) := by
    intro z
    constructor
    · intro _
      obtain ⟨z,rfl⟩ := Quotient.exists_rep z
      have hpz : ((projection C D).f 0).hom z.val = 0 := hterm.elim _ _
      obtain ⟨a,ha⟩ := ((total_degreewise_exact R C hC D 0).2.1 z.val).mp hpz
      have haz : a ∈ cycles (ordinaryTotal (cycleComplex C) D) 0 := by
        change ((ordinaryTotal (cycleComplex C) D).d 0 ((ComplexShape.down ℕ).next 0)).hom a = 0
        rw [ChainComplex.next_nat_zero,
          (ordinaryTotal (cycleComplex C) D).shape 0 0 (by simp [ComplexShape.down])]
        rfl
      refine ⟨homologyClass _ 0 ⟨a,haz⟩, ?_⟩
      change homologyClass _ 0 (cyclesMap (inclusion C D) 0 ⟨a,haz⟩) = homologyClass _ 0 z
      exact congrArg (homologyClass _ 0) (Subtype.ext ha)
    · intro _
      exact hzero.elim _ _
  refine ⟨hzero, he, ?_⟩
  intro z
  exact (he z).mp (hzero.elim _ _)

/-- The two actual totalized short exact sequences form a commuting diagram. -/
theorem total_squares {C C' : Complex.{u,v} R}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (f : C ⟶ C') (g : D ⟶ D') :
    inclusion C D ≫ ordinaryTotalMap f g =
      ordinaryTotalMap (cycleComplexMap f) g ≫ inclusion C' D' ∧
    projection C D ≫ ordinaryTotalMap (shiftedBoundaryComplexMap f) g =
      ordinaryTotalMap f g ≫ projection C' D' := by
  constructor
  · apply HomologicalComplex.Hom.ext
    funext n
    apply P103.Ch11.TorBalance.ordinaryTotal_hom_ext (cycleComplex C) D n
    intro p q h a b
    change ((ordinaryTotalMap f g).f n).hom
      (((inclusion C D).f n).hom (ordinaryInclusion (cycleComplex C) D p q n h (tmul R a b))) =
      ((inclusion C' D').f n).hom
        (((ordinaryTotalMap (cycleComplexMap f) g).f n).hom
          (ordinaryInclusion (cycleComplex C) D p q n h (tmul R a b)))
    rw [inclusion, totalMap_inclusion]
    change ((ordinaryTotalMap f g).f n).hom
      (ordinaryInclusion C D p q n h (tensorMap (cycles C p).subtype LinearMap.id (tmul R a b))) = _
    rw [totalMap_inclusion, totalMap_inclusion, totalMap_inclusion]
    rfl
  · apply HomologicalComplex.Hom.ext
    funext n
    apply P103.Ch11.TorBalance.ordinaryTotal_hom_ext C D n
    intro p q h a b
    change ((ordinaryTotalMap (shiftedBoundaryComplexMap f) g).f n).hom
      (((projection C D).f n).hom (ordinaryInclusion C D p q n h (tmul R a b))) =
      ((projection C' D').f n).hom
        (((ordinaryTotalMap f g).f n).hom (ordinaryInclusion C D p q n h (tmul R a b)))
    rw [projection, totalMap_inclusion]
    change ((ordinaryTotalMap (shiftedBoundaryComplexMap f) g).f n).hom
      (ordinaryInclusion (shiftedBoundaryComplex C) D p q n h
        (tensorMap (boundaryProjectionTerm C p) LinearMap.id (tmul R a b))) = _
    rw [totalMap_inclusion, totalMap_inclusion, totalMap_inclusion]
    apply congrArg (ordinaryInclusion (shiftedBoundaryComplex C') D' p q n h)
    apply congrArg (fun a => tmul R a ((g.f q).hom b))
    cases p with
    | zero => rfl
    | succ p =>
      apply Subtype.ext
      exact (P103.Ch10.HomologySequence.comm_apply f (p+1) p a).symm

/-- Naturality of the two nonconnecting arrows holds without flatness. -/
theorem homology_squares {C C' : Complex.{u,v} R}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    (homologyMap (ordinaryTotalMap f g) n).comp (homologyMap (inclusion C D) n) =
      (homologyMap (inclusion C' D') n).comp
        (homologyMap (ordinaryTotalMap (cycleComplexMap f) g) n) ∧
    (homologyMap (ordinaryTotalMap (shiftedBoundaryComplexMap f) g) n).comp
        (homologyMap (projection C D) n) =
      (homologyMap (projection C' D') n).comp (homologyMap (ordinaryTotalMap f g) n) := by
  constructor
  · simpa only [P103.Ch10.Complexes.homologyMap_comp] using
      congrArg (fun k => homologyMap k n) (total_squares f g).1
  · simpa only [P103.Ch10.Complexes.homologyMap_comp] using
      congrArg (fun k => homologyMap k n) (total_squares f g).2

/-- Naturality of all five squares, with simultaneous maps of both complexes. -/
theorem total_natural : total_naturalType.{u,v,w} := by
  intro R _ C C' D D' hC _ f g n δ ε hδ hε
  refine ⟨(homology_squares f g (n+1)).1, (homology_squares f g (n+1)).2,
    ?_, (homology_squares f g n).1, (homology_squares f g n).2⟩
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Quotient.exists_rep z
  obtain ⟨b,a,hb,ha⟩ := P103.Ch10.HomologySequence.lifts
    (inclusion C D) (projection C D) (total_degreewise_exact R C hC D) (by rfl) z
  change homologyMap (ordinaryTotalMap (cycleComplexMap f) g) n
      (δ (homologyClass _ (n+1) z)) =
    ε (homologyClass _ (n+1)
      (cyclesMap (ordinaryTotalMap (shiftedBoundaryComplexMap f) g) (n+1) z))
  rw [hδ z b a hb ha]
  change homologyClass _ n (cyclesMap (ordinaryTotalMap (cycleComplexMap f) g) n a) = _
  symm
  apply hε _ (((ordinaryTotalMap f g).f (n+1)).hom b) _
  · have H := congrArg (fun k => (k.f (n+1)).hom b) (total_squares f g).2
    change ((ordinaryTotalMap (shiftedBoundaryComplexMap f) g).f (n+1)).hom
      (((projection C D).f (n+1)).hom b) =
      ((projection C' D').f (n+1)).hom (((ordinaryTotalMap f g).f (n+1)).hom b) at H
    change ((projection C' D').f (n+1)).hom _ =
      ((ordinaryTotalMap (shiftedBoundaryComplexMap f) g).f (n+1)).hom z.val
    rw [← H, hb]
  · have H := congrArg (fun k => (k.f n).hom a.val) (total_squares f g).1
    change ((ordinaryTotalMap f g).f n).hom (((inclusion C D).f n).hom a.val) =
      ((inclusion C' D').f n).hom (((ordinaryTotalMap (cycleComplexMap f) g).f n).hom a.val) at H
    change ((inclusion C' D').f n).hom
        (((ordinaryTotalMap (cycleComplexMap f) g).f n).hom a.val) =
      ((ordinaryTotal C' D').d (n+1) n).hom (((ordinaryTotalMap f g).f (n+1)).hom b)
    rw [← H, ha]
    exact (P103.Ch10.HomologySequence.comm_apply (ordinaryTotalMap f g) (n+1) n b).symm

theorem total_zero_natural : total_zero_naturalType.{u,v,w} := by
  intro R _ C C' D D' f g
  exact homology_squares f g 0

end
end P103.Ch11.KunnethTotalConnector
