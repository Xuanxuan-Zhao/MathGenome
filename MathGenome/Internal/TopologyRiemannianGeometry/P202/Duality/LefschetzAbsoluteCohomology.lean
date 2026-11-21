import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.LefschetzAbsoluteCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.LefschetzRelativeCohomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u v
namespace P202.LefschetzAbsoluteCohomology
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass P202Specs.ChainLES
open P202Specs.LefschetzAbsoluteCohomology

variable (R : Type u) [CommRing R]

/-- The ordinary front/back cap has the same differential identity as the
two pair operations. No topological assumption is used. -/
def ordinarySystem (X : TopCat.{v}) :
    P202.CapProducts.CapSystem (ordinaryCochains R R X)
      (ordinaryComplex R R X) (ordinaryComplex R R X) where
  op p q k h := (LinearMap.llcomp R _ _ _ (P202Specs.CapProducts.castOrdinary R h)).comp
    ((P202Specs.CapProducts.cap R X p q).comp (ordinaryCochainsEquiv R R X p).toLinearMap)
  boundary := by
    intro p q n k hn hk a z
    simpa only [LinearMap.comp_apply, LinearMap.llcomp_apply, LinearEquiv.coe_coe,
      P202.CupProduct.ordinaryCochainsEquiv_d] using
      P202.CapProducts.cap_boundary_degrees R X p q n k hn hk
        (ordinaryCochainsEquiv R R X p a) z
  negative := ((P202.CohomologyPairs.negative R R).1 X (-1) (by omega)).1

/-- Construction of ordinary cap on the actual homology quotients. -/
def ordinaryProductsData : OrdinaryProducts.{u,v} R where
  op X := (ordinarySystem R X).homologyOp
  represents := by
    intro X p q a z
    refine ⟨(ordinarySystem R X).cycleOp p q a z, ?_, ?_⟩
    · exact (ordinarySystem R X).cycleOp_i p q a z
    · exact (ordinarySystem R X).homologyOp_rep p q a z

theorem ordinaryProducts : Expected.ordinaryProducts.{u,v} :=
  fun R _ => ⟨ordinaryProductsData R⟩

lemma homologyMap_rep {shape : ComplexShape ℤ}
    {C D : HomologicalComplex (ModuleCat.{max u v} R) shape}
    (f : C ⟶ D) (i : ℤ) (z : C.cycles i) :
    homologyMap f i (C.homologyπ i z) = D.homologyπ i (cyclesMap f i z) := by
  exact congrArg (fun h => h z) (homologyπ_naturality f i)

lemma cyclesMap_rep {shape : ComplexShape ℤ}
    {C D : HomologicalComplex (ModuleCat.{max u v} R) shape}
    (f : C ⟶ D) (i : ℤ) (z : C.cycles i) :
    D.iCycles i (cyclesMap f i z) = f.f i (C.iCycles i z) := by
  exact congrArg (fun h => h z) (cyclesMap_i f i)

/-- The representative law uniquely determines the absolute pair cap. -/
lemma absoluteCap_eq (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p : ℕ) (q : ℤ)
    (a : ordinaryCohomology R R P.space (p : ℤ)) (z : relativeHomology R R P q) :
    c.absolute P p q (a ⊗ₜ[R] z) =
      (P202.CapProducts.absoluteSystem R P).homologyOp p q a z := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryCochains R R P.space).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinary R R P).homologyπ q)).mp inferInstance z
  obtain ⟨v, hv⟩ := P202.CapProducts.projection_surjective R P q ((ordinary R R P).iCycles q z)
  obtain ⟨w, hw, hc⟩ := c.absolute_represents P p q a z v hv
  obtain ⟨w', hw', hc'⟩ := (P202.CapProducts.pairProductsData R).absolute_represents P p q a z v hv
  have he : w = w' := (P202.CapProducts.cycles_injective _ _) (hw.trans hw'.symm)
  exact hc.trans (he ▸ hc'.symm)

/-- The representative law likewise uniquely determines ordinary cap. -/
lemma ordinaryCap_eq (c : OrdinaryProducts.{u,v} R) (X : TopCat.{v}) (p : ℕ) (q : ℤ)
    (a : ordinaryCohomology R R X (p : ℤ)) (z : homology R R X q) :
    c.op X p q a z = (ordinarySystem R X).homologyOp p q a z := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryCochains R R X).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryComplex R R X).homologyπ q)).mp inferInstance z
  obtain ⟨w, hw, hc⟩ := c.represents X p q a z
  obtain ⟨w', hw', hc'⟩ := (ordinaryProductsData R).represents X p q a z
  have he : w = w' := (P202.CapProducts.cycles_injective _ _) (hw.trans hw'.symm)
  exact hc.trans (he ▸ hc'.symm)

@[simp] lemma absoluteCap_nat (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p : ℕ) (q : ℤ) (z : relativeHomology R R P q) :
    absoluteCap R c P (p : ℤ) q z = absoluteCapNat R c P p q z := by
  simp [absoluteCap]

@[simp] lemma relativeCap_nat (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p : ℕ) (q : ℤ) (z : relativeHomology R R P q) :
    relativeCap R c P (p : ℤ) q z = relativeCapNat R c P p q z := by
  simp [relativeCap]

@[simp] lemma ordinaryCap_nat (c : OrdinaryProducts.{u,v} R)
    (X : TopCat.{v}) (p : ℕ) (q : ℤ) (z : homology R R X q) :
    ordinaryCap R c X (p : ℤ) q z = (c.op X p q).flip z := by
  simp [ordinaryCap]

/-- The quotient square commutes on representatives before passing to
homology. Its proof does not use a cap isomorphism. -/
theorem quotient_nat (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p : ℕ) (q : ℤ) (z : relativeHomology R R P q)
    (a : relativeCohomology R R P (p : ℤ)) :
    absoluteCapNat R c P p q z (homologyMap (relativeToAbsolute R R P) (p : ℤ) a) =
      homologyMap (projection (ordinaryFunctor R R) P) (q-p)
        (relativeCapNat R c P p q z a) := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relativeCochains R R P).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinary R R P).homologyπ q)).mp inferInstance z
  obtain ⟨v, hv⟩ := P202.CapProducts.projection_surjective R P q ((ordinary R R P).iCycles q z)
  rw [homologyMap_rep]
  obtain ⟨w, hw, hc⟩ := c.absolute_represents P p q
    (cyclesMap (relativeToAbsolute R R P) (p : ℤ) a) z v hv
  obtain ⟨w', hw', hc'⟩ := c.relative_represents P p q a z v hv
  change c.absolute P p q (_ ⊗ₜ[R] _) = homologyMap (projection (ordinaryFunctor R R) P) (q-p) (c.relative P p q (_ ⊗ₜ[R] _))
  rw [hc, hc']
  erw [homologyMap_rep]
  congr 1
  apply P202.CapProducts.cycles_injective
  rw [cyclesMap_rep, hw]
  erw [hw']
  change (projection (ordinaryFunctor R R) P).f (q-p)
      (P202Specs.CapProducts.cap R P.space p q
        (ordinaryCochainsEquiv R R P.space p
          ((ordinaryCochains R R P.space).iCycles (p : ℤ)
            (cyclesMap (relativeToAbsolute R R P) (p : ℤ) a))) v) = _
  rw [cyclesMap_rep]

/-- The quotient square in all integer degrees. -/
theorem quotient (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p q : ℤ) (z : relativeHomology R R P q)
    (a : relativeCohomology R R P p) :
    absoluteCap R c P p q z (homologyMap (relativeToAbsolute R R P) p a) =
      homologyMap (projection (ordinaryFunctor R R) P) (q-p)
        (relativeCap R c P p q z a) := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [absoluteCap_nat, relativeCap_nat]
    exact quotient_nat R c P p q z a
  · simp [absoluteCap, relativeCap, hp]

/-- Evaluation of the positive snake connecting map on any chosen lift and
any cycle representing its boundary. It applies to chains and cochains. -/
lemma connecting_rep {shape : ComplexShape ℤ}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{max u v} R) shape))
    (h : DegreewiseShortExact S) (i j : ℤ) (hij : shape.Rel i j)
    (z : S.X₃.cycles i) (c : S.X₂.X i) (hc : S.g.f i c = S.X₃.iCycles i z)
    (x : S.X₁.cycles j)
    (hx : S.f.f j (S.X₁.iCycles j x) = S.X₂.d i j c) :
    connecting h i j hij (S.X₃.homologyπ i z) = S.X₁.homologyπ j x := by
  have hz : S.X₃.d i j (S.X₃.iCycles i z) = 0 :=
    congrArg (fun f => f z) (S.X₃.iCycles_d i j)
  have hs := HomologicalComplex.shortExact_of_degreewise_shortExact S h
  have H := hs.δ_apply i j hij (S.X₃.iCycles i z) hz c hc
    (S.X₁.iCycles j x) hx (shape.next j) rfl
  have he₁ : S.X₃.cyclesMk (S.X₃.iCycles i z) j (shape.next_eq' hij) hz = z := by
    apply (ModuleCat.mono_iff_injective (S.X₃.iCycles i)).mp inferInstance
    exact S.X₃.i_cyclesMk _ _ _ _
  have he₂ : S.X₁.cyclesMk (S.X₁.iCycles j x) (shape.next j) rfl
      (hs.d_eq_zero_of_f_eq_d_apply i j c (S.X₁.iCycles j x) hx _) = x := by
    apply (ModuleCat.mono_iff_injective (S.X₁.iCycles j)).mp inferInstance
    exact S.X₁.i_cyclesMk _ _ _ _
  change connecting h i j hij (S.X₃.homologyπ i _) = S.X₁.homologyπ j _ at H
  simpa only [he₁, he₂] using H

/-- Index transport for the categorical cycles, with no change to a chain. -/
def cycleCast (K : ChainComplex (ModuleCat.{max u v} R) ℤ)
    {i j : ℤ} (h : i=j) : K.cycles i →ₗ[R] K.cycles j := h ▸ LinearMap.id

lemma cycleCast_i (K : ChainComplex (ModuleCat.{max u v} R) ℤ)
    {i j : ℤ} (h : i=j) (z : K.cycles i) :
    K.iCycles j (cycleCast R K h z) =
      P202.CapProducts.complexCast R K h (K.iCycles i z) := by
  subst j
  rfl

lemma cycleCast_class (K : ChainComplex (ModuleCat.{max u v} R) ℤ)
    {i j : ℤ} (h : i=j) (z : K.cycles i) :
    K.homologyπ j (cycleCast R K h z) =
      degreeCast R (fun j => K.homology j) h (K.homologyπ i z) := by
  subst j
  rfl

/-- The homological connecting square with the exact front/back sign. -/
theorem boundary_nat (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (b : OrdinaryProducts.{u,v} R) (P : Pair.{v}) (p : ℕ) (q : ℤ)
    (z : relativeHomology R R P q)
    (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) P))
    (a : ordinaryCohomology R R P.space (p : ℤ)) :
    connecting hH (q-p) (q-p-1) (by simp)
      (absoluteCapNat R c P p q z a) =
      (-1 : ℤ)^p • degreeCast R (homology R R P.sub)
        (by omega : (q-1)-(p : ℤ)=q-p-1)
        (b.op P.sub p (q-1) (homologyMap (restriction R R P) (p : ℤ) a)
          (connecting hH q (q-1) (by simp) z)) := by
  let C := ordinaryCochains R R P.space
  let K := ordinaryComplex R R P.space
  let L := ordinaryComplex R R P.sub
  let Q := ordinary R R P
  let i := inclusion (ordinaryFunctor R R) P
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ q)).mp inferInstance z
  have hz : Q.d q (q-1) (Q.iCycles q z) = 0 :=
    P202.CapProducts.chain_cycle_closed Q q z
  obtain ⟨v, hv, x, ⟨hx, hxc⟩, _⟩ := P202.ChainLES.lifts_exist _ hH q (q-1) (by simp) _ hz
  let x' := P202.CapProducts.chainCycle L (q-1) x (hxc _)
  have hx' : i.f (q-1) (L.iCycles (q-1) x') = K.d q (q-1) v := by
    change i.f (q-1) x = K.d q (q-1) v at hx
    simpa only [x', P202.CapProducts.chainCycle_i] using hx
  have hδ : connecting hH q (q-1) (by simp) (Q.homologyπ q z) =
      L.homologyπ (q-1) x' := connecting_rep R _ hH q (q-1) (by simp) z v hv x' hx'
  obtain ⟨w, hw, hc⟩ := c.absolute_represents P p q a z v hv
  obtain ⟨w', hw', hc'⟩ := b.represents P.sub p (q-1)
    (cyclesMap (restriction R R P) (p : ℤ) a) x'
  let w'' := cycleCast R L (by omega : (q-1)-(p : ℤ)=q-p-1) w'
  have hval : P202Specs.CupProduct.cocycleValue R P.sub p
      (cyclesMap (restriction R R P) (p : ℤ) a) =
      P202Specs.CupProduct.pullback R P.inclusion p
        (P202Specs.CupProduct.cocycleValue R P.space p a) := by
    change ordinaryCochainsEquiv R R P.sub p
      ((ordinaryCochains R R P.sub).iCycles (p : ℤ)
        (cyclesMap (restriction R R P) (p : ℤ) a)) = _
    rw [cyclesMap_rep]
    exact P202.CupProduct.ordinaryCochainsEquiv_pullback R P.inclusion p _
  have hboundary : i.f (q-p-1) (L.iCycles (q-p-1) ((-1 : ℤ)^p • w'')) =
      K.d (q-p) (q-p-1)
        (P202Specs.CapProducts.cap R P.space p q
          (P202Specs.CupProduct.cocycleValue R P.space p a) v) := by
    rw [P202.CapProducts.ordinaryBoundary, P202.CupProduct.cocycleValue_delta,
      map_zero, LinearMap.zero_apply, map_zero, sub_zero]
    rw [← hx']
    erw [← P202.CapProducts.ordinaryNatural R P.inclusion]
    rw [P202.CapProducts.castOrdinary_map R P.inclusion]
    change i.f (q-p-1) (L.iCycles (q-p-1) ((-1 : ℤ)^p • w'')) =
      (-1 : ℤ)^p • i.f (q-p-1)
        (P202Specs.CapProducts.castOrdinary R (by omega : (q-1)-(p : ℤ)=q-p-1)
          (P202Specs.CapProducts.cap R P.sub p (q-1) _ (L.iCycles (q-1) x')))
    rw [map_zsmul, map_zsmul]
    congr 2
    rw [cycleCast_i]
    erw [P202.CapProducts.complexCast_ordinary]
    rw [hw', hval]
  have hδcap := connecting_rep R _ hH (q-p) (q-p-1) (by simp) w
    (P202Specs.CapProducts.cap R P.space p q
      (P202Specs.CupProduct.cocycleValue R P.space p a) v)
    hw.symm ((-1 : ℤ)^p • w'') hboundary
  change connecting hH (q-p) (q-p-1) (by simp) (Q.homologyπ (q-p) w) =
    L.homologyπ (q-p-1) ((-1 : ℤ)^p • w'') at hδcap
  change connecting hH (q-p) (q-p-1) (by simp)
    (c.absolute P p q (_ ⊗ₜ[R] _)) = _
  rw [hc, hδcap, map_zsmul, cycleCast_class, hδ, homologyMap_rep, hc']

/-- The cohomological connecting square is positive. The cap boundary
identity supplies an explicit primitive for the difference. -/
theorem connecting_nat (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (b : OrdinaryProducts.{u,v} R) (P : Pair.{v}) (p : ℕ) (q : ℤ)
    (z : relativeHomology R R P q)
    (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) P))
    (hC : DegreewiseShortExact (cochainSequence R R P))
    (a : ordinaryCohomology R R P.sub (p : ℤ)) :
    degreeCast R (homology R R P.space)
      (by push_cast; omega : q-((p+1 : ℕ) : ℤ)=(q-1)-p)
      (relativeCapNat R c P (p+1) q z
        (connecting hC (p : ℤ) ((p+1 : ℕ) : ℤ) (by simp) a)) =
      homologyMap (inclusion (ordinaryFunctor R R) P) ((q-1)-p)
        (b.op P.sub p (q-1) a (connecting hH q (q-1) (by simp) z)) := by
  let C := ordinaryCochains R R P.space
  let C' := ordinaryCochains R R P.sub
  let D := relativeCochains R R P
  let K := ordinaryComplex R R P.space
  let L := ordinaryComplex R R P.sub
  let Q := ordinary R R P
  let i : L ⟶ K := inclusion (ordinaryFunctor R R) P
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (C'.homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ q)).mp inferInstance z
  have ha : C'.d (p : ℤ) ((p+1 : ℕ) : ℤ) (C'.iCycles (p : ℤ) a) = 0 :=
    P202.CapProducts.cochain_cycle_closed C' p a
  obtain ⟨aM, haM, da, ⟨hda, hdac⟩, _⟩ :=
    P202.ChainLES.lifts_exist _ hC (p : ℤ) ((p+1 : ℕ) : ℤ) (by simp) _ ha
  let da' := D.cyclesMk da _ rfl (hdac _)
  have hda' : (relativeToAbsolute R R P).f ((p+1 : ℕ) : ℤ)
      (D.iCycles ((p+1 : ℕ) : ℤ) da') = C.d (p : ℤ) ((p+1 : ℕ) : ℤ) aM := by
    change (relativeToAbsolute R R P).f ((p+1 : ℕ) : ℤ) da = C.d (p : ℤ) ((p+1 : ℕ) : ℤ) aM at hda
    have he : D.iCycles ((p+1 : ℕ) : ℤ) da' = da := D.i_cyclesMk _ _ _ _
    rw [he]
    exact hda
  have hδa : connecting hC (p : ℤ) ((p+1 : ℕ) : ℤ) (by simp)
      (C'.homologyπ (p : ℤ) a) = D.homologyπ ((p+1 : ℕ) : ℤ) da' :=
    connecting_rep R _ hC _ _ (by simp) a aM haM da' hda'
  have hz : Q.d q (q-1) (Q.iCycles q z) = 0 :=
    P202.CapProducts.chain_cycle_closed Q q z
  obtain ⟨v, hv, x, ⟨hx, hxc⟩, _⟩ :=
    P202.ChainLES.lifts_exist _ hH q (q-1) (by simp) _ hz
  let x' := P202.CapProducts.chainCycle L (q-1) x (hxc _)
  have hx' : i.f (q-1) (L.iCycles (q-1) x') = K.d q (q-1) v := by
    change i.f (q-1) x = K.d q (q-1) v at hx
    simpa only [x', P202.CapProducts.chainCycle_i] using hx
  have hδz : connecting hH q (q-1) (by simp) (Q.homologyπ q z) =
      L.homologyπ (q-1) x' := connecting_rep R _ hH _ _ (by simp) z v hv x' hx'
  obtain ⟨w, hw, hc⟩ := c.relative_represents P (p+1) q da' z v hv
  obtain ⟨w', hw', hc'⟩ := b.represents P.sub p (q-1) a x'
  let j : ℤ := (q-1)-p
  let wμ := cycleCast R K (by dsimp [j]; push_cast; omega : q-((p+1 : ℕ) : ℤ)=j) w
  let wB := cyclesMap i j w'
  have hval : P202.CapProducts.relativeValue R P (p+1)
      (D.iCycles ((p+1 : ℕ) : ℤ) da') =
      P202Specs.CupProduct.delta R P.space p (ordinaryCochainsEquiv R R P.space p aM) := by
    change ordinaryCochainsEquiv R R P.space (p+1)
      ((relativeToAbsolute R R P).f ((p+1 : ℕ) : ℤ) (D.iCycles ((p+1 : ℕ) : ℤ) da')) = _
    rw [hda', P202.CupProduct.ordinaryCochainsEquiv_d]
  have hvalB : P202Specs.CupProduct.cocycleValue R P.sub p a =
      P202Specs.CupProduct.pullback R P.inclusion p
        (ordinaryCochainsEquiv R R P.space p aM) := by
    rw [← P202.CupProduct.ordinaryCochainsEquiv_pullback]
    exact congrArg (ordinaryCochainsEquiv R R P.sub p) haM.symm
  have hboundary : K.d (j+1) j
      (P202.CapProducts.complexCast R K (by dsimp [j]; omega : q-(p : ℤ)=j+1)
        ((-1 : ℤ)^p • P202Specs.CapProducts.cap R P.space p q
          (ordinaryCochainsEquiv R R P.space p aM) v)) =
      K.iCycles j (wB-wμ) := by
    rw [← P202.CapProducts.complexCast_d R K
      (by dsimp [j]; omega : q-(p : ℤ)=j+1) (by dsimp [j]; omega : q-p-1=j)]
    rw [map_zsmul, P202.CapProducts.ordinaryBoundary, smul_smul, ← mul_pow]
    norm_num
    simp only [map_sub]
    rw [cyclesMap_rep, cycleCast_i]
    erw [hw, hw', hvalB]
    change P202.CapProducts.complexCast R K _
      (P202Specs.CapProducts.castOrdinary R _
        (P202Specs.CapProducts.cap R P.space p (q-1)
          (ordinaryCochainsEquiv R R P.space p aM) (K.d q (q-1) v))) - _ = _
    rw [← hx']
    erw [← P202.CapProducts.ordinaryNatural R P.inclusion]
    dsimp only [K, L, i]
    simp only [P202.CapProducts.complexCast_ordinary,
      P202.CapProducts.castOrdinary_comp, P202.CapProducts.castOrdinary_map]
    rw [← hval]
    rfl
  have he : K.homologyπ j wB = K.homologyπ j wμ := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (P202.CapProducts.chain_class_zero_iff K j _).mpr ⟨_, hboundary⟩
  change degreeCast R (homology R R P.space) _
    (c.relative P (p+1) q (_ ⊗ₜ[R] _)) = _
  rw [hδa, hc, hδz, hc']
  erw [homologyMap_rep]
  exact (cycleCast_class R K _ w).symm.trans he.symm


/-- The signed boundary square, including zero negative-cohomology terms. -/
theorem boundary_square (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (b : OrdinaryProducts.{u,v} R) (P : Pair.{v}) (p q : ℤ)
    (z : relativeHomology R R P q)
    (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) P))
    (a : ordinaryCohomology R R P.space p) :
    connecting hH (q-p) (q-p-1) (by simp) (absoluteCap R c P p q z a) =
      (-1 : ℤ)^p.natAbs • degreeCast R (homology R R P.sub)
        (by omega : (q-1)-p=q-p-1)
        (ordinaryCap R b P.sub p (q-1) (connecting hH q (q-1) (by simp) z)
          (homologyMap (restriction R R P) p a)) := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    simpa only [absoluteCap_nat, ordinaryCap_nat, Int.natAbs_natCast,
      LinearMap.flip_apply] using boundary_nat R c b P p q z hH a
  · simp [absoluteCap, ordinaryCap, hp]
    exact map_zero _

/-- The positive connecting square in all integer cohomological degrees. -/
theorem connecting_square (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (b : OrdinaryProducts.{u,v} R) (P : Pair.{v}) (p q : ℤ)
    (z : relativeHomology R R P q)
    (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) P))
    (hC : DegreewiseShortExact (cochainSequence R R P))
    (a : ordinaryCohomology R R P.sub p) :
    degreeCast R (homology R R P.space) (by omega : q-(p+1)=(q-1)-p)
      (relativeCap R c P (p+1) q z (connecting hC p (p+1) (by simp) a)) =
      homologyMap (inclusion (ordinaryFunctor R R) P) ((q-1)-p)
        (ordinaryCap R b P.sub p (q-1) (connecting hH q (q-1) (by simp) z) a) := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    change degreeCast R (homology R R P.space)
      (by push_cast; omega : q-((p+1 : ℕ) : ℤ)=(q-1)-p)
      (relativeCap R c P ((p+1 : ℕ) : ℤ) q z
        (connecting hC (p : ℤ) ((p+1 : ℕ) : ℤ) (by simp) a)) = _
    rw [relativeCap_nat, ordinaryCap_nat]
    exact connecting_nat R c b P p q z hH hC a
  · haveI := ModuleCat.subsingleton_of_isZero
      (((P202.CohomologyPairs.negative R R).1 P.sub p (by omega)).2)
    have ha : a = 0 := Subsingleton.elim _ _
    simp [ha]

/-- All three kinds of arrows of the actual two long exact sequences are
compatible with cap, before applying any duality theorem. -/
theorem diagram : Expected.diagram.{u,v} := by
  intro R _ c b P q z hH hC
  exact ⟨fun p a => quotient R c P p q z a,
    fun p a => boundary_square R c b P p q z hH a,
    fun p a => connecting_square R c b P p q z hH hC a⟩


/-- Quotienting by the chains of the empty subspace is an isomorphism. -/
lemma projection_isIso_empty (P : Pair.{v}) [IsEmpty P.sub] :
    IsIso (projection (ordinaryFunctor R R) P) := by
  haveI : ∀ j : ℤ, IsIso ((projection (ordinaryFunctor R R) P).f j) := by
    intro j
    exact ((P202.RelativeSingularChains.ordinary_short_exact R R P j).isIso_g_iff).mpr
      (P202.SingularDegreeZero.emptyOrdinaryX R R P.sub j)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- When the boundary is empty, the quotient square and the first cap
isomorphism already give the second cap isomorphism. -/
theorem empty_boundary_duality
    (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold n .halfSpace M)
    (collar : Collar (manifoldBoundary A))
    (AI : Manifold n (Interior (manifoldBoundary A))) (o : Orientation R AI)
    (hM : IsCompact (Set.univ : Set M)) (hB : manifoldBoundary A = ∅) (p : ℤ) :
    Function.Bijective (absoluteCap R c (boundaryPair M (manifoldBoundary A)) p (n : ℤ)
      (fundamentalClass R (manifoldBoundary A) n o.val)) := by
  let B := manifoldBoundary A
  let P := boundaryPair M B
  let μ := fundamentalClass R B n o.val
  letI : IsEmpty P.sub := ⟨fun x => by
    have hx : x.val ∈ manifoldBoundary A := x.property
    rw [hB] at hx
    exact hx⟩
  haveI := projection_isIso_empty R P
  haveI : IsIso (relativeToAbsolute R R P) := by
    change IsIso ((dualComplexFunctor R R (ComplexShape.down ℤ)).map
      (projection (ordinaryFunctor R R) P).op)
    infer_instance
  have hC := (asIso (homologyMap (relativeToAbsolute R R P) p)).toLinearEquiv.bijective
  have hH := (asIso (homologyMap (projection (ordinaryFunctor R R) P) ((n : ℤ)-p))).toLinearEquiv.bijective
  have hrel := (P202.LefschetzRelativeCohomology.duality R c (P202.CompactSupport.dualityData R)
    n M A collar AI o hM).1 p
  change Function.Bijective (relativeCap R c P p (n : ℤ) μ) at hrel
  apply (Function.Bijective.of_comp_iff (absoluteCap R c P p (n : ℤ) μ) hC).mp
  have he : (fun a => absoluteCap R c P p (n : ℤ) μ
      (homologyMap (relativeToAbsolute R R P) p a)) =
      (fun a => homologyMap (projection (ordinaryFunctor R R) P) ((n : ℤ)-p)
        (relativeCap R c P p (n : ℤ) μ a)) := funext (quotient R c P p (n : ℤ) μ)
  change Function.Bijective (fun a => absoluteCap R c P p (n : ℤ) μ
    (homologyMap (relativeToAbsolute R R P) p a))
  rw [he]
  exact hH.comp hrel

/-- The all-degree assertion in particular includes dimension zero. The
empty intrinsic boundary here is proved from the half-space atlas. -/
theorem zero_dimension_duality
    (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold 0 .halfSpace M)
    (collar : Collar (manifoldBoundary A))
    (AI : Manifold 0 (Interior (manifoldBoundary A))) (o : Orientation R AI)
    (hM : IsCompact (Set.univ : Set M)) (p : ℤ) :
    Function.Bijective (absoluteCap R c (boundaryPair M (manifoldBoundary A)) p 0
      (fundamentalClass R (manifoldBoundary A) 0 o.val)) :=
  empty_boundary_duality R c 0 M A collar AI o hM
    (P202.RelativeFundamentalClass.manifoldBoundary_zero A) p

/-- Negative cohomology gives the asserted isomorphism onto the already
proved above-dimension zero relative homology group. -/
theorem negative_duality
    (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold n .halfSpace M)
    (collar : Collar (manifoldBoundary A))
    (AI : Manifold n (Interior (manifoldBoundary A))) (o : Orientation R AI)
    (hM : IsCompact (Set.univ : Set M)) (p : ℤ) (hp : p < 0) :
    Function.Bijective (absoluteCap R c (boundaryPair M (manifoldBoundary A)) p (n : ℤ)
      (fundamentalClass R (manifoldBoundary A) n o.val)) := by
  haveI : Subsingleton (ordinaryCohomology R R (boundaryPair M (manifoldBoundary A)).space p) :=
    ModuleCat.subsingleton_of_isZero
      (((P202.CohomologyPairs.negative R R).1 (boundaryPair M (manifoldBoundary A)).space p hp).2)
  haveI := ModuleCat.subsingleton_of_isZero
    ((P202.LefschetzRelativeCohomology.aboveDimension R n M A collar AI o hM
      ((n : ℤ)-p) (by omega)).2)
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩

/-- On a compact boundaryless manifold, the ordinary cap with *any* class
having the prescribed local orientation values is bijective. This identifies
the actual representative formula with compact-support Poincaré duality. -/
theorem compact_cap_bijective (b : OrdinaryProducts.{u,v} R)
    (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A)
    (hM : IsCompact (Set.univ : Set M))
    (μ : homology R R (TopCat.of M) (n : ℤ))
    (hμ : P202Specs.CompactOrientation.HasLocalValues R o.val Set.univ
      (P202Specs.CompactOrientation.absoluteToSupported R M n μ)) (p : ℤ) :
    Function.Bijective (ordinaryCap R b (TopCat.of M) p (n : ℤ) μ) := by
  let d := P202.CompactSupport.dualityData R
  obtain ⟨hf, μ₀, hμ₀, hrep⟩ :=
    P202.PoincareDuality.compactIdentification R d n M A o hM
  have heμ : μ = μ₀ :=
    (P202.CompactOrientation.ordinaryFundamentalClass R n M A o hM).2.unique hμ hμ₀
  subst μ₀
  let e (p : ℤ) := LinearEquiv.ofBijective
    (P202Specs.PoincareDuality.forgetSupport R M p) (hf p)
  have hnat (p : ℕ) (a : ordinaryCohomology R R (TopCat.of M) (p : ℤ)) :
      ordinaryCap R b (TopCat.of M) (p : ℤ) (n : ℤ) μ a =
        d.D n M A o (p : ℤ) ((e (p : ℤ)).symm a) := by
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((ordinaryCochains R R (TopCat.of M)).homologyπ (p : ℤ))).mp inferInstance a
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
      ((ordinaryComplex R R (TopCat.of M)).homologyπ (n : ℤ))).mp inferInstance μ
    obtain ⟨w, hw, hD⟩ := hrep p a z hz
    obtain ⟨w', hw', hb⟩ := b.represents (TopCat.of M) p (n : ℤ) a z
    have hew : w = w' := P202.CapProducts.cycles_injective _ _ (hw.trans hw'.symm)
    rw [hz] at hb
    rw [ordinaryCap_nat]
    change b.op (TopCat.of M) p (n : ℤ) _ μ = _
    exact hb.trans (hew ▸ hD.symm)
  have hall (p : ℤ) (a : ordinaryCohomology R R (TopCat.of M) p) :
      ordinaryCap R b (TopCat.of M) p (n : ℤ) μ a =
        d.D n M A o p ((e p).symm a) := by
    by_cases hp : 0 ≤ p
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      exact hnat p a
    · rw [d.negative n M A o p (by omega)]
      simp [ordinaryCap, hp]
  have he : ordinaryCap R b (TopCat.of M) p (n : ℤ) μ =
      (d.D n M A o p).comp (e p).symm.toLinearMap := LinearMap.ext (hall p)
  rw [he]
  exact (P202.PoincareDuality.duality R d n M A o p).comp (e p).symm.bijective

theorem aboveDimension : Expected.aboveDimension.{u,v} :=
  P202.LefschetzRelativeCohomology.aboveDimension

lemma degreeCast_comp (H : ℤ → ModuleCat.{max u v} R)
    {i j k : ℤ} (h : i=j) (h' : j=k) (a : H i) :
    degreeCast R H h' (degreeCast R H h a) = degreeCast R H (h.trans h') a := by
  subst j; subst k; rfl

@[simp] lemma degreeCast_self (H : ℤ → ModuleCat.{max u v} R)
    (i : ℤ) (h : i=i) (a : H i) : degreeCast R H h a = a := by rfl

lemma degreeCast_bijective (H : ℤ → ModuleCat.{max u v} R)
    {i j : ℤ} (h : i=j) : Function.Bijective (degreeCast R H h) := by
  subst j
  exact Function.bijective_id

lemma degreeCast_homologyMap {K L : ChainComplex (ModuleCat.{max u v} R) ℤ}
    (f : K ⟶ L) {i j : ℤ} (h : i=j) (a : K.homology i) :
    degreeCast R (fun j => L.homology j) h (homologyMap f i a) =
      homologyMap f j (degreeCast R (fun j => K.homology j) h a) := by
  subst j; rfl

lemma degreeCast_connecting
    (S : ShortComplex (ChainComplex (ModuleCat.{max u v} R) ℤ))
    (hS : DegreewiseShortExact S) (i j k : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) (hik : (ComplexShape.down ℤ).Rel i k)
    (h : j=k) (a : S.X₃.homology i) :
    degreeCast R (fun j => S.X₁.homology j) h (connecting hS i j hij a) =
      connecting hS i k hik a := by
  subst k; rfl

lemma connecting_square_degrees
    (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (b : OrdinaryProducts.{u,v} R) (P : Pair.{v}) (p r q : ℤ) (hr : p+1=r)
    (z : relativeHomology R R P q)
    (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) P))
    (hC : DegreewiseShortExact (cochainSequence R R P))
    (a : ordinaryCohomology R R P.sub p) :
    degreeCast R (homology R R P.space) (by omega : q-r=(q-1)-p)
      (relativeCap R c P r q z (connecting hC p r (by change p+1=r; exact hr) a)) =
      homologyMap (inclusion (ordinaryFunctor R R) P) ((q-1)-p)
        (ordinaryCap R b P.sub p (q-1) (connecting hH q (q-1) (by simp) z) a) := by
  subst r
  exact connecting_square R c b P p q z hH hC a

/-- The signed diagram proves the middle cap isomorphism from the first
cap map and ordinary duality for its boundary class. -/
theorem bijective_of_pair_diagram
    (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (b : OrdinaryProducts.{u,v} R) (P : Pair.{v}) (q : ℤ)
    (z : relativeHomology R R P q)
    (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) P))
    (hC : DegreewiseShortExact (cochainSequence R R P))
    (hrel : ∀ p : ℤ, Function.Bijective (relativeCap R c P p q z))
    (hb : ∀ p : ℤ, Function.Bijective
      (ordinaryCap R b P.sub p (q-1) (connecting hH q (q-1) (by simp) z)))
    (p : ℤ) : Function.Bijective (absoluteCap R c P p q z) := by
  let D := diagram R c b P q z hH hC
  let h₁ : (q-1)-(p-1)=q-p := by omega
  let h₅ : q-(p+1)=(q-1)-p := by omega
  apply P202.PoincareDuality.signed_five_lemma R
    (connecting hC (p-1) p (by simp))
    (homologyMap (relativeToAbsolute R R P) p)
    (homologyMap (restriction R R P) p)
    (connecting hC p (p+1) (by simp))
    (homologyMap (inclusion (ordinaryFunctor R R) P) (q-p))
    (homologyMap (projection (ordinaryFunctor R R) P) (q-p))
    (connecting hH (q-p) ((q-1)-p) (by change (q-1)-p+1=q-p; omega))
    (homologyMap (inclusion (ordinaryFunctor R R) P) ((q-1)-p))
    (ModuleCat.ofHom ((degreeCast R (homology R R P.sub) h₁).comp
      (ordinaryCap R b P.sub (p-1) (q-1) (connecting hH q (q-1) (by simp) z))))
    (ModuleCat.ofHom (relativeCap R c P p q z))
    (ModuleCat.ofHom (absoluteCap R c P p q z))
    (ModuleCat.ofHom (ordinaryCap R b P.sub p (q-1) (connecting hH q (q-1) (by simp) z)))
    (ModuleCat.ofHom ((degreeCast R (homology R R P.space) h₅).comp
      (relativeCap R c P (p+1) q z))) ((-1 : ℤˣ)^p.natAbs)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have H := connecting_square_degrees R c b P (p-1) p q (by omega) z hH hC a
    have H' := congrArg (degreeCast R (homology R R P.space) h₁) H
    rw [degreeCast_comp, degreeCast_self] at H'
    erw [degreeCast_homologyMap] at H'
    exact H'
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact D.quotient p
  · intro a
    have H := D.boundary p a
    have H' := congrArg (degreeCast R (homology R R P.sub)
      (by omega : q-p-1=(q-1)-p)) H
    rw [map_zsmul, degreeCast_comp, degreeCast_self] at H'
    have he := degreeCast_connecting R _ hH (q-p) (q-p-1) ((q-1)-p)
      (by simp) (by change (q-1)-p+1=q-p; omega) (by omega) (absoluteCap R c P p q z a)
    change degreeCast R (homology R R P.sub) _
      (connecting hH (q-p) (q-p-1) _ (absoluteCap R c P p q z a)) = _ at he
    rw [he] at H' 
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    change connecting hH (q-p) ((q-1)-p) _ (absoluteCap R c P p q z a) =
      (-1 : ℤ)^p.natAbs • ordinaryCap R b P.sub p (q-1)
        (connecting hH q (q-1) _ z) (homologyMap (restriction R R P) p a)
    exact H' 
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact D.connecting p
  · exact P202.PoincareDuality.exact_functions R _
      ((P202.ChainLES.exactness _ hC).2 (p-1) p (by simp)) 2 (by omega)
  · exact P202.PoincareDuality.exact_functions R _
      ((P202.ChainLES.exactness _ hC).1 p) 0 (by omega)
  · exact P202.PoincareDuality.exact_functions R _
      ((P202.ChainLES.exactness _ hC).2 p (p+1) (by simp)) 1 (by omega)
  · exact P202.PoincareDuality.exact_functions R _
      ((P202.ChainLES.exactness _ hH).1 (q-p)) 0 (by omega)
  · exact P202.PoincareDuality.exact_functions R _
      ((P202.ChainLES.exactness _ hH).2 (q-p) ((q-1)-p)
        (by change (q-1)-p+1=q-p; omega)) 1 (by omega)
  · exact P202.PoincareDuality.exact_functions R _
      ((P202.ChainLES.exactness _ hH).2 (q-p) ((q-1)-p)
        (by change (q-1)-p+1=q-p; omega)) 2 (by omega)
  · exact ((degreeCast_bijective R _ h₁).comp (hb (p-1))).2
  · exact hrel p
  · exact hb p
  · exact ((degreeCast_bijective R _ h₅).comp (hrel (p+1))).1


lemma degreeCast_eqToHom (H : ℤ → ModuleCat.{max u v} R)
    {i j : ℤ} (h : i=j) (a : H i) :
    degreeCast R H h a = (eqToHom (congrArg H h)) a := by
  subst j; rfl

lemma ordinaryCap_degreeCast (b : OrdinaryProducts.{u,v} R) (X : TopCat.{v})
    (p : ℤ) {q q' : ℤ} (h : q=q') (z : homology R R X q)
    (a : ordinaryCohomology R R X p) :
    degreeCast R (homology R R X) (congrArg (fun q => q-p) h)
      (ordinaryCap R b X p q z a) =
        ordinaryCap R b X p q' (degreeCast R (homology R R X) h z) a := by
  subst q'; rfl

/-- The complete second Poincaré–Lefschetz isomorphism, with the original
relative fundamental class and with no pre-assumed second cap isomorphism. -/
theorem duality : Expected.duality.{u,v} := by
  intro R _ c n M _ A
  dsimp only
  intro collar AI o hM p
  cases n with
  | zero => exact zero_dimension_duality R c M A collar AI o hM p
  | succ k =>
    letI : T2Space M := A.hausdorff
    letI : CompactSpace M := isCompact_univ_iff.mp hM
    let B := manifoldBoundary A
    let P := boundaryPair M B
    let μ := fundamentalClass R B (k+1) o.val
    let hH := P202.RelativeSingularChains.ordinary_short_exact R R P
    let hC := P202.CohomologyPairs.short_exact R R P
    let b := ordinaryProductsData R
    have hB : IsClosed B := P202.RelativeFundamentalClass.Geometry.manifoldBoundary_isClosed A
    have hCompactB : IsCompact (Set.univ : Set B) := by
      letI : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
      exact isCompact_univ
    obtain ⟨AB⟩ := (P202.RelativeFundamentalClass.boundaryGeometry).2.1 k M A
    have hboundary := P202.RelativeFundamentalClass.intrinsicBoundary R k M A collar AI AB o hM
    obtain ⟨oB, hoB⟩ := hboundary.1.exists
    have hμB := (hboundary.2 oB hoB hH).2
    have hvalues := (hboundary.2 oB hoB hH).1
    let e : ((k+1 : ℕ) : ℤ)-1=(k : ℤ) := by omega
    have hδμ : degreeCast R (homology R R (TopCat.of B)) e
        (connecting hH ((k+1 : ℕ) : ℤ) (((k+1 : ℕ) : ℤ)-1) (by simp) μ) =
        boundaryClass R B k oB.val := by
      rw [degreeCast_eqToHom]
      exact hμB
    apply bijective_of_pair_diagram R c b P ((k+1 : ℕ) : ℤ) μ hH hC
    · intro r
      exact (P202.LefschetzRelativeCohomology.duality R c (P202.CompactSupport.dualityData R)
        (k+1) M A collar AI o hM).1 r
    · intro r
      let f := ordinaryCap R b P.sub r (((k+1 : ℕ) : ℤ)-1)
        (connecting hH ((k+1 : ℕ) : ℤ) (((k+1 : ℕ) : ℤ)-1) (by simp) μ)
      let g := degreeCast R (homology R R P.sub) (congrArg (fun q : ℤ => q-r) e)
      have he : g.comp f = ordinaryCap R b P.sub r (k : ℤ) (boundaryClass R B k oB.val) := by
        apply LinearMap.ext
        intro a
        change degreeCast R (homology R R P.sub) _
          (ordinaryCap R b P.sub r _ _ a) = _
        rw [ordinaryCap_degreeCast R b P.sub r e]
        exact congrArg (fun z : homology R R P.sub (k : ℤ) =>
          ordinaryCap R b P.sub r (k : ℤ) z a) hδμ
      apply (Function.Bijective.of_comp_iff' (degreeCast_bijective R _ _) f).mp
      change Function.Bijective (g.comp f)
      rw [he]
      exact compact_cap_bijective R b k B AB oB hCompactB (boundaryClass R B k oB.val) hvalues r

/-- Specialization of the signed diagram to μ and the induced μ_B. -/
theorem comparison : Expected.comparison.{u,v} := by
  intro R _ c b q M _ A
  dsimp only
  intro collar AI AB o oB hoB hM hH hC
  refine ⟨diagram R c b _ _ _ hH hC, ?_⟩
  rw [degreeCast_eqToHom]
  exact ((P202.RelativeFundamentalClass.intrinsicBoundary R q M A collar AI AB o hM).2
    oB hoB hH).2

end P202.LefschetzAbsoluteCohomology

