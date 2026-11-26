import Specs.LinearAlgebraicGroups.Arithmetic.TorusFibreKummerRealization
import LinearAlgebraicGroups.Arithmetic.KummerObstructions
import Mathlib.RingTheory.Noetherian.Orzech

noncomputable section

universe u

namespace LinearAlgebraicGroups.Arithmetic.TorusFibreKummerRealization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
open Algebra.TensorProduct

open Specs.TorusFibreKummerRealization
open Specs.CentralCover Specs.CentralCoverSpreading Specs.IntegralCentralQuotient
open LinearAlgebraicGroups.Arithmetic.Kummer
open LinearAlgebraicGroups.Arithmetic.CentralCover
  (coordinateHom spectrum_coordinateHom spectrumOfHopfHom_injective property_of_groupIso
    hopfSpectrumIsoOfBialgEquiv fullKernel_of_spectrumPullback)

open private spectrumOfHopfHom_comp torus_degreePart_comm
  degreePart degreePart_eq degreePart_degree
  from LinearAlgebraicGroups.Classification.IntegralCentralQuotient
open private cover_invariants coordinateCharacter_pow fibreElement_scalar
  from LinearAlgebraicGroups.Arithmetic.KummerObstructions

variable {R : Type u} [CommRing R] {I : Type} (n : I → ℕ)

private abbrev reduction (R : Type u) [CommRing R] {I : Type} (n : I → ℕ) :
    TorusCoordinates R I →ₐc[R] KernelCoordinates R n :=
  MonoidAlgebra.mapDomainBialgHom R (reduceCharacters n)

private theorem reduction_surjective : Function.Surjective (reduction R n) := by
  have h : Function.Surjective (reduceCharacters.{u} n) := by
    intro x
    choose l hl using fun i => ZMod.intCast_surjective (x.down i).toAdd
    refine ⟨⟨Multiplicative.ofAdd l⟩, ULift.ext (funext fun i => ?_)⟩
    exact congrArg Multiplicative.ofAdd (hl i)
  intro x
  obtain ⟨p, hp⟩ := Finsupp.mapDomain_surjective h x.coeff
  exact ⟨MonoidAlgebra.ofCoeff p, MonoidAlgebra.coeff_injective hp⟩

private theorem reduction_power (x : TorusCoordinates R I) :
    reduction R n (powerPullback R n x) =
      algebraMap R (KernelCoordinates R n) (Bialgebra.counitAlgHom R _ x) := by
  have h (z : ULift.{u} (Multiplicative (I → ℤ))) :
      reduceCharacters n (powerCharacters n z) = 1 := by
    apply ULift.ext
    funext i
    change Multiplicative.ofAdd (((n i : ℤ) * z.down.toAdd i : ℤ) : ZMod (n i)) = 1
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, ofAdd_zero]
  let l := (reduction R n).toAlgHom.comp (powerPullback R n).toAlgHom
  let r := (Algebra.ofId R (KernelCoordinates R n)).comp (Bialgebra.counitAlgHom R (TorusCoordinates R I))
  have he : l = r := by
    apply AlgHom.toLinearMap_injective
    apply (MonoidAlgebra.basis _ R).ext
    intro z
    change reduction R n (powerPullback R n (MonoidAlgebra.of R _ z)) =
      algebraMap R (KernelCoordinates R n) (Coalgebra.counit (R := R) (MonoidAlgebra.of R _ z))
    rw [(MonoidAlgebra.isGroupLikeElem_of (R := R) z).counit_eq_one, map_one,
      MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainBialgHom_single,
      MonoidAlgebra.mapDomainBialgHom_single, h, ← MonoidAlgebra.of_apply, map_one]
  exact DFunLike.congr_fun he x

private theorem power_injective (hn : ∀ i, 0 < n i) :
    Function.Injective (powerPullback R n) := by
  apply MonoidAlgebra.mapDomain_injective
  intro x y h
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  funext i
  have hi : (n i : ℤ) * x.down.toAdd i = (n i : ℤ) * y.down.toAdd i :=
    congrArg (fun z : ULift.{u} (Multiplicative (I → ℤ)) => z.down.toAdd i) h
  exact mul_left_cancel₀ (by exact_mod_cast (hn i).ne') hi

private theorem reduce_torusCharacter (i : I) :
    reduceCharacters.{u} n (torusCharacter i) = coordinateCharacter n i := by
  classical
  apply ULift.ext
  funext j
  change Multiplicative.ofAdd ((Pi.single (M := fun _ : I => ℤ) i (1 : ℤ) j : ℤ) : ZMod (n j)) =
    Pi.mulSingle (M := fun j => Characters (n j)) i (Multiplicative.ofAdd (1 : ZMod (n i))) j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h]

private theorem power_torusCharacter (i : I) :
    powerCharacters.{u} n (torusCharacter i) = torusCharacter i ^ n i := by
  classical
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  funext j
  change (n j : ℤ) * Pi.single (M := fun _ : I => ℤ) i (1 : ℤ) j = (n i : ℤ) * Pi.single (M := fun _ : I => ℤ) i (1 : ℤ) j
  by_cases h : j = i
  · subst j
    rfl
  · simp [Pi.single_eq_of_ne h]

section CoordinateKernel

variable {B A : Type u} [CommRing B] [CommRing A] [HopfAlgebra R B] [HopfAlgebra R A]
  (q₀ : B →ₐc[R] A) (π₀ : A →ₐc[R] KernelCoordinates R n)
  (t : A →ₐc[R] TorusCoordinates R I) (s : B →ₐc[R] TorusCoordinates R I)

private theorem kernel_coordinate_equiv [Finite I] (hn : ∀ i, 0 < n i)
    (hfull : IsFullKernel q₀ π₀) (ht : Function.Surjective t)
    (hsquare : t.comp q₀ = (powerPullback R n).comp s) :
    ∃ e : KernelCoordinates R n ≃ₐc[R] KernelCoordinates R n,
      e.toBialgHom.comp π₀ = (reduction R n).comp t := by
  let f := (reduction R n).comp t
  have hf (b : B) : f (q₀ b) =
      algebraMap R (KernelCoordinates R n) (Bialgebra.counitAlgHom R B b) := by
    change reduction R n (t (q₀ b)) = _
    rw [show t (q₀ b) = powerPullback R n (s b) from DFunLike.congr_fun hsquare b,
      reduction_power]
    exact congrArg (algebraMap R (KernelCoordinates R n))
      (DFunLike.congr_fun s.counitAlgHom_comp b)
  obtain ⟨g, hg, _⟩ :=
    ((CentralCoverSpreading.isFullKernel_iff_affine_points q₀ π₀).mp hfull).2.2
      (KernelCoordinates R n) f.toAlgHom hf
  have hgf (x : A) : g (π₀ x) = f x := DFunLike.congr_fun hg x
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := ((reduction_surjective (R := R) n).comp ht) y
    exact ⟨π₀ x, (hgf x).trans hx⟩
  -- The split kernel and the standard torus kernel have the same finite free coordinate module.
  let K := KernelCoordinates R n
  let (i : I) : NeZero (n i) := ⟨(hn i).ne'⟩
  let : Finite (ULift.{u} (∀ i, Characters (n i))) := inferInstance
  let : Module.Finite R K := Module.Finite.of_basis (MonoidAlgebra.basis _ R)
  have hinj : Function.Injective g :=
    OrzechProperty.injective_of_surjective_endomorphism g.toLinearMap hsurj
  let gb : K →ₐc[R] K := BialgHom.ofAlgHom g (by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hfull.1 y
    change Bialgebra.counitAlgHom R K (g (π₀ x)) =
      Bialgebra.counitAlgHom R K (π₀ x)
    rw [hgf]
    exact (DFunLike.congr_fun f.counitAlgHom_comp x).trans
      (DFunLike.congr_fun π₀.counitAlgHom_comp x).symm) (by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hfull.1 y
    change Algebra.TensorProduct.map g g (Bialgebra.comulAlgHom R K (π₀ x)) =
      Bialgebra.comulAlgHom R K (g (π₀ x))
    have hπco : Bialgebra.comulAlgHom R K (π₀ x) =
        Algebra.TensorProduct.map π₀.toAlgHom π₀.toAlgHom (Bialgebra.comulAlgHom R A x) :=
      (DFunLike.congr_fun π₀.map_comp_comulAlgHom x).symm
    rw [hπco, hgf]
    change ((Algebra.TensorProduct.map g g).comp
      (Algebra.TensorProduct.map π₀.toAlgHom π₀.toAlgHom)) (Bialgebra.comulAlgHom R A x) = _
    rw [← Algebra.TensorProduct.map_comp, hg]
    exact DFunLike.congr_fun f.map_comp_comulAlgHom x)
  refine ⟨BialgEquiv.ofBijective gb ⟨hinj, hsurj⟩, ?_⟩
  apply DFunLike.ext
  exact hgf

end CoordinateKernel

section Realization

variable {B A V : Type u} [CommRing B] [CommRing A] [HopfAlgebra R B] [HopfAlgebra R A]
  [CommRing V] [Algebra R V]

private def torusEvaluation [Fintype I] (a : I → Vˣ) :
    TorusCoordinates R I →ₐ[R] V :=
  (MonoidAlgebra.lift R V _)
    ((Units.coeHom V).comp
      { toFun := fun c => ∏ i, a i ^ c.down.toAdd i
        map_one' := by change (∏ i, a i ^ (0 : ℤ)) = 1; simp
        map_mul' := fun c d => by
          change (∏ i, a i ^ (c.down.toAdd i + d.down.toAdd i)) = _
          simp only [zpow_add, Finset.prod_mul_distrib] })

private theorem torusEvaluation_apply [Fintype I] (a : I → Vˣ) (i : I) :
    torusEvaluation (R := R) a (MonoidAlgebra.of R _ (torusCharacter i)) = (a i : V) := by
  classical
  rw [torusEvaluation, MonoidAlgebra.lift_of]
  change ↑(∏ j, a j ^ Pi.single (M := fun _ : I => ℤ) i (1 : ℤ) j) = (a i : V)
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem class_at_torusPoint [Finite I] (hn : ∀ i, 0 < n i)
    (q₀ : B →ₐc[R] A) (π : A →ₐc[R] KernelCoordinates R n)
    (t : A →ₐc[R] TorusCoordinates R I) (s : B →ₐc[R] TorusCoordinates R I)
    (ht : Function.Surjective t) (hsquare : t.comp q₀ = (powerPullback R n).comp s)
    (hπ : π = (reduction R n).comp t) (htorsor : IsRightTorsor q₀ π)
    (ev : TorusCoordinates R I →ₐ[R] V) (i : I) (a : Vˣ)
    (heval : ev (MonoidAlgebra.of R _ (torusCharacter i)) = (a : V)) :
    letI : Algebra B A := q₀.toAlgHom.toAlgebra
    PullbackHasClass n π (ev.comp s.toAlgHom) i (classOf (n i) a) := by
  classical
  let : Algebra B A := q₀.toAlgHom.toAlgebra
  let p := ev.comp s.toAlgHom
  let : Algebra B V := p.toAlgebra
  let (j : I) : NeZero (n j) := ⟨(hn j).ne'⟩
  let : Fintype (ULift.{u} (∀ j, Characters (n j))) := Fintype.ofFinite _
  let m := coordinateCharacter n i
  let z := torusCharacter.{u} i
  let χ := MonoidAlgebra.of R (ULift.{u} (Multiplicative (I → ℤ)))
  let ψ := reduction R n
  have hz : rightCoaction ψ (χ z) = χ z ⊗ₜ[R] MonoidAlgebra.of R _ m := by
    change (Algebra.TensorProduct.map (AlgHom.id R (TorusCoordinates R I)) ψ.toAlgHom)
      (Coalgebra.comul (R := R) (χ z)) = _
    rw [(MonoidAlgebra.isGroupLikeElem_of (R := R) z).comul_eq_tmul_self,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change χ z ⊗ₜ[R] ψ (MonoidAlgebra.single z 1) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single, reduce_torusCharacter]
    rfl
  -- Project a lift of the torus monomial to its character degree in the full cover.
  obtain ⟨b₀, hb₀⟩ := ht (χ z)
  let b := degreePart π m b₀
  have hb : rightCoaction π b = b ⊗ₜ[R] MonoidAlgebra.of R _ m :=
    degreePart_degree π m b₀
  have htb : t b = χ z := by
    change t (degreePart π m b₀) = χ z
    rw [hπ, torus_degreePart_comm, hb₀, degreePart_eq ψ _ _ _ hz, ite_eq_left rfl]
  have hpow : rightCoaction π (b ^ n i) = (b ^ n i) ⊗ₜ[R] (1 : KernelCoordinates R n) := by
    let χK := MonoidAlgebra.of R (ULift.{u} (∀ j, Characters (n j)))
    have hm : m ^ n i = 1 := coordinateCharacter_pow n i
    rw [map_pow, hb, tmul_pow, ← map_pow χK, hm, map_one]
  -- The torsor descends the power, and restriction to the torus identifies it.
  obtain ⟨r, hr⟩ := ((cover_invariants q₀ π htorsor).2 _).mp hpow
  have hsr : s r = χ z := by
    apply power_injective n hn
    calc
      powerPullback R n (s r) = t (q₀ r) := (DFunLike.congr_fun hsquare r).symm
      _ = (χ z) ^ n i := by rw [hr, map_pow, htb]
      _ = powerPullback R n (χ z) := by
        rw [← map_pow χ, ← power_torusCharacter n i]
        exact (MonoidAlgebra.mapDomainBialgHom_single ..).symm
  have hroot : ((1 : V) ⊗ₜ[B] b) ^ n i = algebraMap V (V ⊗[B] A) (a : V) := by
    change (includeRight (R := B) (A := V) (B := A) b) ^ n i = _
    rw [← map_pow, ← hr]
    calc
      includeRight (q₀ r) = algebraMap V (V ⊗[B] A) (p r) :=
        fibreElement_scalar q₀.toAlgHom p r
      _ = _ := by change algebraMap V (V ⊗[B] A) (ev (s r)) = _; rw [hsr, heval]
  exact ⟨b, a, hb, (isUnit_pow_iff (hn i).ne').mp (hroot ▸ a.isUnit.map _), hroot, rfl⟩

end Realization


private theorem coordinate_surjective {B A : Type u} [CommRing B] [CommRing A]
    [HopfAlgebra R B] [HopfAlgebra R A] (f : B →ₐc[R] A)
    (h : IsClosedImmersion (spectrumOfHopfHom f).hom.hom.left) :
    Function.Surjective f := by
  let φ := CommRingCat.ofHom f.toAlgHom.toRingHom
  have : IsClosedImmersion (Spec.map φ) := h
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2
  have hφ : (Scheme.ΓSpecIso _).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso _).hom = φ := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  change Function.Surjective φ
  rw [← hφ]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
    (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2)

section IntegralModel

variable {E : Type u} [Field E] [Algebra R E]
  {G H : AffineAlgebraicGroup E} {q : H.val ⟶ G.val} {N : ClosedSubgroup H.val}
  {T : SplitCoverData G H q N} {m : ℕ} {j : MatrixEmbedding G m}
  (M : IntegralModel (R := R) T j)

set_option backward.isDefEq.respectTransparency false in
private theorem markedTorusCoordinates {B A : Type u} [CommRing B] [CommRing A]
    [HopfAlgebra R B] [HopfAlgebra R A]
    (eG : HopfSpectrum R B ≅ M.target.val) (eH : HopfSpectrum R A ≅ M.source.val)
    (q₀ : B →ₐc[R] A) (hq : spectrumOfHopfHom q₀ ≫ eG.hom = eH.hom ≫ M.map) :
    ∃ (t : A →ₐc[R] TorusCoordinates R T.indices) (s : B →ₐc[R] TorusCoordinates R T.indices),
      spectrumOfHopfHom t ≫ eH.hom = M.splitSourceTorus.inv ≫ M.sourceTorusInclusion ∧
      spectrumOfHopfHom s ≫ eG.hom = M.splitTargetTorus.inv ≫ M.targetTorusInclusion ∧
      Function.Surjective t ∧ t.comp q₀ = (powerPullback R T.exponents).comp s := by
  let eT := M.splitSourceTorus
  let eS := M.splitTargetTorus
  let t := coordinateHom (eT.inv ≫ M.sourceTorusInclusion ≫ eH.inv)
  let s := coordinateHom (eS.inv ≫ M.targetTorusInclusion ≫ eG.inv)
  have ht : spectrumOfHopfHom t ≫ eH.hom = eT.inv ≫ M.sourceTorusInclusion := by
    rw [show spectrumOfHopfHom t = _ from spectrum_coordinateHom _]
    simp
  have hs : spectrumOfHopfHom s ≫ eG.hom = eS.inv ≫ M.targetTorusInclusion := by
    rw [show spectrumOfHopfHom s = _ from spectrum_coordinateHom _]
    simp
  have hp : integralPowerMap R T.exponents ≫ eS.inv = eT.inv ≫ M.torusMap := by
    rw [← cancel_epi eT.hom, ← cancel_mono eS.hom]
    simpa using M.splitTorusMap.symm
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · exact coordinate_surjective t
        (property_of_groupIso eT.symm eH ht @IsClosedImmersion M.sourceTorusClosed)
  · apply spectrumOfHopfHom_injective
    change spectrumOfHopfHom (t.comp q₀) =
      spectrumOfHopfHom ((powerPullback R T.exponents).comp s)
    rw [spectrumOfHopfHom_comp, spectrumOfHopfHom_comp]
    change spectrumOfHopfHom t ≫ spectrumOfHopfHom q₀ =
      integralPowerMap R T.exponents ≫ spectrumOfHopfHom s
    rw [← cancel_mono eG.hom, Category.assoc, Category.assoc, hs, hq,
      ← Category.assoc (spectrumOfHopfHom t), ← Category.assoc (integralPowerMap R T.exponents),
      ht, hp, Category.assoc, Category.assoc, M.torusCompatibility]

set_option backward.isDefEq.respectTransparency false in
private theorem compatibleKernel :
    ∃ eZ : M.kernel.val ≅ integralRootsOfUnityProduct R T.exponents,
      eZ.inv ≫ M.kernelInclusion =
        kernelIntoTorus R T.exponents ≫ M.splitSourceTorus.inv ≫ M.sourceTorusInclusion := by
  let := T.finiteIndices
  obtain ⟨B, ⟨eG⟩⟩ := essImage_hopfSpec.mpr M.target.property.1
  obtain ⟨A, ⟨eH⟩⟩ := essImage_hopfSpec.mpr M.source.property.1
  let q₀ := coordinateHom (eH.hom ≫ M.map ≫ eG.inv)
  let e₀ := M.splitKernel
  let π₀ := coordinateHom (e₀.inv ≫ M.kernelInclusion ≫ eH.inv)
  have hq : spectrumOfHopfHom q₀ ≫ eG.hom = eH.hom ≫ M.map := by
    rw [show spectrumOfHopfHom q₀ = _ from spectrum_coordinateHom _]
    simp
  have hj : spectrumOfHopfHom π₀ ≫ eH.hom = e₀.inv ≫ M.kernelInclusion := by
    rw [show spectrumOfHopfHom π₀ = _ from spectrum_coordinateHom _]
    simp
  let F := Grp.forget (OverBase R)
  have hpb : IsPullback (spectrumOfHopfHom π₀).hom.hom (toUnit _)
      (spectrumOfHopfHom q₀).hom.hom η[(HopfSpectrum R B.unop).X] := by
    refine M.torsor.kernel.of_iso' (F.mapIso e₀.symm) (F.mapIso eH) (Iso.refl _)
      (F.mapIso eG) ?_ (toUnit_unique _ _) ?_ ?_
    · exact (congrArg F.map hj).symm
    · exact (congrArg F.map hq).symm
    · change (𝟙 _) ≫ η[M.target.val.X] = η[(HopfSpectrum R B.unop).X] ≫ eG.hom.hom.hom
      rw [Category.id_comp, IsMonHom.one_hom]
  have hjc : Function.Surjective π₀ :=
    coordinate_surjective π₀
        (property_of_groupIso e₀.symm eH hj @IsClosedImmersion M.torsor.closed)
  obtain ⟨t, s, ht, _, htc, hsq⟩ := markedTorusCoordinates M eG eH q₀ hq
  obtain ⟨e, he⟩ := kernel_coordinate_equiv T.exponents q₀ π₀ t s T.positiveExponents
    (fullKernel_of_spectrumPullback q₀ π₀ hjc hpb) htc hsq
  let E := hopfSpectrumIsoOfBialgEquiv e
  refine ⟨e₀ ≪≫ E.symm, ?_⟩
  have hE : E.hom = spectrumOfHopfHom e.toBialgHom := rfl
  change E.hom ≫ e₀.inv ≫ M.kernelInclusion =
    kernelIntoTorus R T.exponents ≫ M.splitSourceTorus.inv ≫ M.sourceTorusInclusion
  rw [hE, ← hj, ← ht, ← Category.assoc (spectrumOfHopfHom e.toBialgHom),
    ← spectrumOfHopfHom_comp]
  change spectrumOfHopfHom (e.toBialgHom.comp π₀) ≫ eH.hom =
    kernelIntoTorus R T.exponents ≫ spectrumOfHopfHom t ≫ eH.hom
  rw [he, spectrumOfHopfHom_comp, Category.assoc]

end IntegralModel

set_option backward.isDefEq.respectTransparency false in
/-- The marked integral torus realizes every tuple of unit Kummer classes
for the same kernel coordinates and Hopf presentation used by the cover. -/
theorem torusFibreKummerRealization : Specs.TorusFibreKummerRealization.Statement.{u} := by
  intro R E _ _ _ _ _ G H q N T m j M
  let := T.finiteIndices
  obtain ⟨eZ, hZ⟩ := compatibleKernel M
  refine ⟨eZ, hZ, ?_⟩
  intro B A _ _ _ _ eG eH q₀ π hq hπ htor
  obtain ⟨t, s, ht, hs, htc, hsq⟩ := markedTorusCoordinates M eG eH q₀ hq
  have hπ' : π = (reduction R T.exponents).comp t := by
    apply spectrumOfHopfHom_injective
    change spectrumOfHopfHom π = spectrumOfHopfHom ((reduction R T.exponents).comp t)
    rw [spectrumOfHopfHom_comp, ← cancel_mono eH.hom, Category.assoc, ht, hπ, hZ]
  refine ⟨s, hs, ?_⟩
  intro V _ _ _ a
  let ev := torusEvaluation (R := R) a
  refine ⟨ev, ev.comp s.toAlgHom, torusEvaluation_apply a, rfl, fun i => ?_⟩
  exact class_at_torusPoint T.exponents T.positiveExponents q₀ π t s htc hsq hπ' htor ev i (a i)
    (torusEvaluation_apply a i)

end LinearAlgebraicGroups.Arithmetic.TorusFibreKummerRealization
