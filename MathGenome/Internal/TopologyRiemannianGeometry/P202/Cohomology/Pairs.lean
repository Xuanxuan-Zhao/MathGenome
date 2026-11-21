import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open scoped Simplicial
namespace P202.CohomologyPairs
open P202Specs.CohomologyPairs P202Specs.SingularChains
  P202Specs.RelativeSingularChains P202Specs.ChainLES
universe u v w t
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

theorem coboundary : Expected.coboundary.{u,v,w} R A := by
  intro X i j a c
  rfl
theorem relative_coboundary : Expected.relativeCoboundary.{u,v,w} R A := by
  intro P i j a c
  rfl

/-- Restrict chain coordinates along the injective simplex inclusion. Its dual
extends an arbitrary cochain by zero, including for empty subspaces. -/
def chainRetraction (P : Pair.{w}) (q : ℕ) : Chains R P.space q →ₗ[R] Chains R P.sub q :=
  Finsupp.lcomapDomain ((TopCat.toSSet.map P.inclusion).app (op ⦋q⦌))
    (P202.RelativeSingularChains.simplex_injective P q)

lemma chainRetraction_inclusion (P : Pair.{w}) (q : ℕ) (c : Chains R P.sub q) :
    chainRetraction R P q ((chainMap R R P.inclusion).f q c) = c :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ _ c

/-- The splitting is only degreewise; it is not asserted to commute with d. -/
lemma ordinary_inclusion_split (P : Pair.{w}) (q : ℤ) :
    ∃ r : (ordinaryComplex R R P.space).X q ⟶ (ordinaryComplex R R P.sub).X q,
      (inclusion (ordinaryFunctor R R) P).f q ≫ r = 𝟙 _ := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    refine ⟨(ordinaryNonnegativeIso R R P.space n).hom ≫
      ModuleCat.ofHom (chainRetraction R P n) ≫ (ordinaryNonnegativeIso R R P.sub n).inv, ?_⟩
    rw [← Category.assoc, ← Category.assoc, ordinary_inclusion_degree]
    simp only [Category.assoc]
    have h : (inclusion (chainFunctor R R) P).f n ≫
        ModuleCat.ofHom (chainRetraction R P n) = 𝟙 _ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact chainRetraction_inclusion R P n c
    rw [← Category.assoc ((inclusion (chainFunctor R R) P).f n), h]
    simp
  · refine ⟨0, ?_⟩
    exact (P202.SingularChains.ordinary_negative_chains R R P.sub q (by omega)).eq_of_src _ _

theorem restriction_surjective : Expected.restrictionSurjective.{u,v,w} R A := by
  intro P q a
  change (ordinaryComplex R R P.sub).X q →ₗ[R] A at a
  obtain ⟨r, hr⟩ := ordinary_inclusion_split R P q
  refine ⟨a.comp r.hom, ?_⟩
  apply LinearMap.ext
  intro c
  change a (r ((inclusion (ordinaryFunctor R R) P).f q c)) = a c
  exact congrArg a (congrArg (fun f : (ordinaryComplex R R P.sub).X q ⟶ _ => f c) hr)

/-- Duality is left exact for every coefficient module. Right exactness here
uses the actual splitting on simplex coordinates. -/
lemma dual_shortExact (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact)
    (hsplit : ∃ r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 _) :
    (ShortComplex.mk ((dualFunctor R A).map S.g.op) ((dualFunctor R A).map S.f.op)
      (by rw [← Functor.map_comp, ← op_comp, S.zero, op_zero, Functor.map_zero])).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro a ha
    have hker : S.g.hom.ker ≤ a.ker := by
      intro c hc
      obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS.exact c hc
      change a c = 0
      rw [← hb]
      exact congrArg (fun f : S.X₁ →ₗ[R] A => f b) ha
    refine ⟨S.g.hom.liftOfSurjective hS.moduleCat_surjective_g ⟨a, hker⟩, ?_⟩
    ext c
    exact LinearMap.equivOfSurjective_apply hS.moduleCat_surjective_g hker
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro a b hab
    ext c
    obtain ⟨x, rfl⟩ := hS.moduleCat_surjective_g c
    exact congrArg (fun f : S.X₂ →ₗ[R] A => f x) hab
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro a
    obtain ⟨r, hr⟩ := hsplit
    refine ⟨a.comp r.hom, ?_⟩
    ext c
    change a (r (S.f c)) = a c
    exact congrArg a (congrArg (fun f : S.X₁ ⟶ S.X₁ => f c) hr)

theorem short_exact : Expected.shortExact.{u,v,w} R A := by
  intro P q
  exact dual_shortExact R A
    ((sequence (ordinaryFunctor R R) P).map (HomologicalComplex.eval _ _ q))
    (P202.RelativeSingularChains.sequence_shortExact (ordinaryFunctor R R) P q)
    (ordinary_inclusion_split R P q)

/-- The cochain sequence gives the long exact sequence in the increasing
cohomological direction; the inherited lift formula has positive sign. -/
theorem long_exact : Expected.longExact.{u,v,w} R A := by
  let h := short_exact R A
  refine ⟨h, ?_, ?_⟩
  · intro P
    exact ⟨(P202.ChainLES.exactness _ (h P)).1,
      fun q => (P202.ChainLES.exactness _ (h P)).2 q (q+1) (by simp),
      P202.ChainLES.module_lift _ (h P)⟩
  · intro P Q f
    have hn := P202.ChainLES.naturality (cochainSequenceMap R A f) (h Q) (h P)
    exact ⟨hn.1, hn.2.1, fun q => hn.2.2 q (q+1) (by simp)⟩

theorem pullback : Expected.pullback.{u,v,w} R A := by
  constructor
  · intro X Y f q a c; rfl
  · intro P Q f q a c; rfl

theorem functoriality : Expected.functoriality.{u,v,w} R A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X q; exact (ordinaryCohomologyFunctor R A q).map_id (op X)
  · intro X Y Z f g q; exact (ordinaryCohomologyFunctor R A q).map_comp g.op f.op
  · intro P q; exact (relativeCohomologyFunctor R A q).map_id (op P)
  · intro P Q T f g q; exact (relativeCohomologyFunctor R A q).map_comp g.op f.op

theorem homotopy_invariant : Expected.homotopyInvariant.{u,v,w} R A := by
  constructor
  · intro X Y f g H q
    obtain ⟨h⟩ := P202.PrismHomotopy.ordinary R R H
    exact (((dualFunctor R A).mapHomotopy h.op).homologyMap_eq q).symm
  · intro P Q f g H q
    obtain ⟨a, b, h, k, _⟩ := P202.PrismHomotopy.relative R R H
    exact (((dualFunctor R A).mapHomotopy h.op).homologyMap_eq q).symm

lemma dual_isZero (V : ModuleCat.{t} R) (hV : IsZero V) :
    IsZero (ModuleCat.of R (V →ₗ[R] A)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have := ModuleCat.subsingleton_of_isZero hV
  refine ⟨fun f g => ?_⟩
  apply LinearMap.ext
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  simp only [hx, map_zero]

theorem negative : Expected.negative.{u,v,w} R A := by
  constructor
  · intro X q hq
    have h : IsZero ((ordinaryCochains R A X).X q) :=
      dual_isZero R A _ (P202.SingularChains.ordinary_negative_chains R R X q hq)
    exact ⟨h, ((ordinaryCochains R A X).sc q).isZero_homology_of_isZero_X₂ h⟩
  · intro P q hq
    have h : IsZero ((relativeCochains R A P).X q) :=
      dual_isZero R A _ (P202.RelativeSingularChains.ordinary_negative R R P q hq).1
    exact ⟨h, ((relativeCochains R A P).sc q).isZero_homology_of_isZero_X₂ h⟩

/-- Universal property of the quotient, retaining the evaluation formula. -/
theorem quotient_vanishing : Expected.quotientVanishing.{u,v,w} R A := by
  intro P q
  let f := ((chainMap R R P.inclusion).f q).hom
  let p := f.range
  let j : quotientCochains R A P q →ₗ[R] vanishingCochains R A P q :=
    { toFun := fun a => ⟨a.comp p.mkQ, by
        apply LinearMap.ext
        intro c
        change a (p.mkQ (f c)) = 0
        have h : p.mkQ (f c) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨c, rfl⟩
        rw [h, map_zero]⟩
      map_add' := by intro a b; rfl
      map_smul' := by intro r a; rfl }
  have hinj : Function.Injective j := by
    intro a b hab
    apply LinearMap.ext
    intro c
    obtain ⟨x, rfl⟩ := p.mkQ_surjective c
    exact congrArg (fun z : vanishingCochains R A P q => z.val x) hab
  have hsurj : Function.Surjective j := by
    intro b
    have hb : p ≤ b.val.ker := by
      rintro x ⟨c, rfl⟩
      exact congrArg (fun z : Chains R P.sub q →ₗ[R] A => z c) b.property
    refine ⟨p.liftQ b.val hb, ?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl
  exact ⟨LinearEquiv.ofBijective j ⟨hinj, hsurj⟩, fun _ _ => rfl⟩

theorem vanishing_on_simplices : Expected.vanishingOnSimplices.{u,v,w} R A := by
  intro P q a
  constructor
  · intro ha s hs
    obtain ⟨t, rfl⟩ := (P202.RelativeSingularChains.simplex_image P q s).mpr hs
    have h := congrArg (fun z : Chains R P.sub q →ₗ[R] A => z (Finsupp.single t 1)) ha
    change a (((chainMap R R P.inclusion).f q).hom (Finsupp.single t 1)) = 0 at h
    rw [P202.SingularChains.chainMap_single] at h
    exact h
  · intro h
    apply Finsupp.lhom_ext
    intro t r
    change a (((chainMap R R P.inclusion).f q).hom (Finsupp.single t r)) = 0
    rw [P202.SingularChains.chainMap_single]
    rw [← Finsupp.smul_single_one, map_smul,
      h _ ((P202.RelativeSingularChains.simplex_image P q _).mp ⟨t, rfl⟩), smul_zero]

theorem natural_coboundary : Expected.naturalCoboundary.{u,v,w} R A := by
  intro X q a c
  change a ((ordinaryNonnegativeIso R R X q).hom
    ((ordinaryComplex R R X).d ((q+1 : ℕ) : ℤ) (q : ℤ)
      ((ordinaryNonnegativeIso R R X (q+1)).inv c))) = a (boundary R R X q c)
  exact congrArg a (congrArg (fun f : (complex R R X).X (q+1) ⟶ (complex R R X).X q => f c)
    (P202.SingularChains.ordinary_boundary R R X q))

lemma chainQuotientEquiv_projection (P : Pair.{w}) (q : ℕ) (c : Chains R P.space q) :
    chainQuotientEquiv R R P q ((projection (chainFunctor R R) P).f q c) =
      Submodule.Quotient.mk c := by
  have h := congrArg (fun f => f c)
    (PreservesCokernel.π_iso_hom (HomologicalComplex.eval (ModuleCat R) _ q)
      (inclusion (chainFunctor R R) P))
  change ((degreeQuotientIso (chainFunctor R R) P q).hom)
    ((projection (chainFunctor R R) P).f q c) =
      cokernel.π ((inclusion (chainFunctor R R) P).f q) c at h
  change (ModuleCat.cokernelIsoRangeQuotient _).hom
    ((degreeQuotientIso (chainFunctor R R) P q).hom
      ((projection (chainFunctor R R) P).f q c)) = _
  rw [h]
  exact congrArg (fun f : (complex R R P.space).X q ⟶ _ => f c)
    (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom ((inclusion (chainFunctor R R) P).f q))

theorem quotient_identification : Expected.quotientIdentification.{u,v,w} R A := by
  intro P q a c
  change (ordinary R R P).X (q : ℤ) →ₗ[R] A at a
  let e := (ordinaryDegreeIso R R P q).toLinearEquiv.trans (chainQuotientEquiv R R P q)
  have h : e ((projection (ordinaryFunctor R R) P).f (q : ℤ)
      ((ordinaryNonnegativeIso R R P.space q).inv c)) = Submodule.Quotient.mk c := by
    have h' := congrArg (fun f : (ordinaryComplex R R P.space).X (q : ℤ) ⟶ _ =>
      f ((ordinaryNonnegativeIso R R P.space q).inv c))
      (P202.RelativeSingularChains.ordinary_degree R R P q)
    simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply] at h'
    change chainQuotientEquiv R R P q
      ((ordinaryDegreeIso R R P q).hom
        ((projection (ordinaryFunctor R R) P).f (q : ℤ)
          ((ordinaryNonnegativeIso R R P.space q).inv c))) = _
    exact (congrArg (chainQuotientEquiv R R P q) h').trans
      (chainQuotientEquiv_projection R P q c)
  change a (e.symm (Submodule.Quotient.mk c)) =
    a ((projection (ordinaryFunctor R R) P).f (q : ℤ)
      ((ordinaryNonnegativeIso R R P.space q).inv c))
  exact congrArg a (e.symm_apply_eq.mpr h.symm)

/-! Public construction interfaces. -/

def ordinaryCochainFunctor : P202Specs.CohomologyPairs.ordinaryCochainFunctor_type.{u,v,w} :=
  P202Specs.CohomologyPairs.ordinaryCochainFunctor_value

def relativeCochainFunctor : P202Specs.CohomologyPairs.relativeCochainFunctor_type.{u,v,w} :=
  P202Specs.CohomologyPairs.relativeCochainFunctor_value

def ordinaryCohomologyFunctor : P202Specs.CohomologyPairs.ordinaryCohomologyFunctor_type.{u,v,w} :=
  P202Specs.CohomologyPairs.ordinaryCohomologyFunctor_value

def relativeCohomologyFunctor : P202Specs.CohomologyPairs.relativeCohomologyFunctor_type.{u,v,w} :=
  P202Specs.CohomologyPairs.relativeCohomologyFunctor_value

def ordinaryCochainsEquiv : P202Specs.CohomologyPairs.ordinaryCochainsEquiv_type.{u,v,w} :=
  P202Specs.CohomologyPairs.ordinaryCochainsEquiv_value

def quotientCochainsEquiv : P202Specs.CohomologyPairs.quotientCochainsEquiv_type.{u,v,w} :=
  P202Specs.CohomologyPairs.quotientCochainsEquiv_value

def cohomologyQuotientEquiv : P202Specs.CohomologyPairs.cohomologyQuotientEquiv_type.{u,t} :=
  P202Specs.CohomologyPairs.cohomologyQuotientEquiv_value

def cochainSequence : P202Specs.CohomologyPairs.cochainSequence_type.{u,v,w} :=
  P202Specs.CohomologyPairs.cochainSequence_value

def abelianOrdinaryCochainFunctor : P202Specs.CohomologyPairs.abelianOrdinaryCochainFunctor_type.{v,w} :=
  P202Specs.CohomologyPairs.abelianOrdinaryCochainFunctor_value

def abelianRelativeCochainFunctor : P202Specs.CohomologyPairs.abelianRelativeCochainFunctor_type.{v,w} :=
  P202Specs.CohomologyPairs.abelianRelativeCochainFunctor_value

end P202.CohomologyPairs
