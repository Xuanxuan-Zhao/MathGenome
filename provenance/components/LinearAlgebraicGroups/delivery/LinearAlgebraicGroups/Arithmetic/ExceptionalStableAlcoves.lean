import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
import LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricReduction
import LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricDescent
import LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives
import LinearAlgebraicGroups.Arithmetic.ExceptionalSplitIwahoriDescent
import LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalStableAlcoves
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
attribute [local instance] integerAlgebra

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

private theorem change_cocycle {Γ G : Type*} [Group Γ] [Group G]
    (ρ : Γ →* MulAut G) (a : Γ → G) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (g : G) (σ τ : Γ) :
    g⁻¹ * a (σ * τ) * ρ (σ * τ) g =
      (g⁻¹ * a σ * ρ σ g) * ρ σ (g⁻¹ * a τ * ρ τ g) := by
  rw [ha, map_mul ρ]
  simp only [MulAut.mul_apply, map_mul, map_inv]
  group

section FixedFace

universe u v

variable {K G W V : Type u} {J : Type v} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} [Group G] [Group W]
  {j : G →* FieldPoints M K} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := W) A p}
  {B : Building C} {Q : C.TypeQuotient}

private theorem lift_one_iwahori (B : Building C) : (C.lift 1 : G) ∈ C.I := by
  have hk : C.lift 1 ∈ C.affine.ker := by simp [C.lift_label]
  have hk' : (C.lift 1 : G) ∈ C.affine.ker.map C.N.subtype := ⟨C.lift 1, hk, rfl⟩
  have ht := (congrArg (fun H : Subgroup G => (C.lift 1 : G) ∈ H) C.kernel).mp hk'
  have hm := (congrArg (fun H : Subgroup G => (C.lift 1 : G) ∈ H)
    B.iwahori_inter_normalizer).mpr ht
  exact hm.1

private theorem standard_chart_place (t : Weights (A.SimpleWall p)) :
    B.realization.chart 1 (simplexPoint B.realization.coordinates B.realization.vertex t) =
      B.realization.place 1 t := by
  have h := B.realization.chart_place 1 1 t
  have hr (x) :
      realAffine B.realization.coordinates B.realization.coordinates
        ((1 : A.affineWeylGroup).val) x = x := by
    simp [realAffine, Specs.ExceptionalRealAlcove.realAffine, AffineEquiv.one_def]
  rw [hr, one_mul] at h
  rw [h]
  apply (B.realization.place_eq _ _ _ _).2
  have hi : (C.lift 1 : G) ∈ parahoric C (cotype t) :=
    Subgroup.subset_closure (Or.inl (lift_one_iwahori B))
  exact ⟨rfl, by simpa using (parahoric C (cotype t)).inv_mem hi⟩

private theorem fixed_standard_face {Γ : Type u} [Group Γ] [Finite Γ]
    (ad : AdjointAction B Q) (had : AdjointCoefficientActions ad)
    (ρ : Γ →* MulAut G) (e : Γ → V ≃ᵃ[ℚ] V)
    (he : ∀ σ, AutomorphismComparison C (ρ σ) (e σ))
    (a : Γ → G) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    Nonempty (FixedStandardFace ad ρ e a) := by
  obtain ⟨coef, hcomm, htwisted⟩ := had Γ ρ e he
  obtain ⟨twist, _, htwist, _, _, ⟨z, hz⟩, hface⟩ := htwisted a ha
  obtain ⟨g, T, t, _, ht, hb, hmove, hfixed⟩ := hface z hz
  obtain ⟨x, hx⟩ := B.realization.barycenter_rational T t hb
  refine ⟨⟨coef, hcomm, g, t, x, ht.symm ▸ hb, hx, ?_, change_cocycle ρ a ha g, ?_⟩⟩
  · rw [hx, standard_chart_place]
  · intro σ
    let y := B.realization.place 1 t
    have hgy : ad.action (g : G) y = B.realization.place g t := by
      rw [ad.restrict, hmove]
    have hfix := (hfixed σ).2
    rw [htwist, ← hgy, hcomm] at hfix
    change ad.action ((g : G)⁻¹ * a σ * ρ σ g) (coef.action σ y) = y
    rw [map_mul, map_mul, IsometryEquiv.mul_apply, IsometryEquiv.mul_apply, hfix,
      ← IsometryEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

end FixedFace

private theorem integral_tmul {Y : Type*} [AddCommGroup Y] (a : ℤ) (y : Y) :
    (a : ℚ) ⊗ₜ[ℤ] y = (1 : ℚ) ⊗ₜ[ℤ] (a • y) := by
  rw [← TensorProduct.smul_tmul]
  simp

private theorem tensor_scale_integral {Y : Type*} [AddCommGroup Y] (r : ℚ) (y : Y) :
    (r.den : ℚ) • (r ⊗ₜ[ℤ] y) = (1 : ℚ) ⊗ₜ[ℤ] (r.num • y) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, Rat.mul_den_eq_num, integral_tmul]

/-- Clear a positive denominator in the rational cocharacter apartment. -/
theorem integralScalingDenominator.{u} :
    IntegralScalingDenominator.{u} := by
  unfold IntegralScalingDenominator
  intro Y _ x
  induction x using TensorProduct.inductionOn with
  | tmul r y => exact ⟨r.den, r.num • y, r.den_pos, tensor_scale_integral r y⟩
  | add x z hx hz =>
    obtain ⟨d, y, hd, hy⟩ := hx
    obtain ⟨e, w, he, hw⟩ := hz
    refine ⟨d * e, (e : ℤ) • y + (d : ℤ) • w, Nat.mul_pos hd he, ?_⟩
    rw [Nat.cast_mul, smul_add]
    have hz' : ((d : ℚ) * (e : ℚ)) • z = (d : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] w) := by
      rw [mul_smul, hw]
    -- Use the opposite factor first on the term with denominator d.
    have hx' : ((d : ℚ) * (e : ℚ)) • x = (e : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] y) := by
      rw [mul_comm, mul_smul, hy]
    rw [hx', hz', TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, TensorProduct.tmul_add]
    exact congrArg₂ (· + ·)
      (by simpa only [Int.cast_natCast] using integral_tmul (e : ℤ) y)
      (by simpa only [Int.cast_natCast] using integral_tmul (d : ℤ) w)

section StableAlcove

open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalSplitParahoricDescent (FaceReduction uniformizerPolynomial)
open scoped WithZero Polynomial
open private uniformizer_polynomial_irreducible
  from LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricReduction

private theorem exists_normalized_uniformizer (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ π : Fˣ, normalizedValuation F (π : F) = WithZero.exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hv : normalizedValuation F x = WithZero.exp (-1 : ℤ) := by
    change e (ValuativeRel.valuation F x) = _
    exact (congrArg e hx).trans (e.apply_symm_apply _)
  have hx₀ : x ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (by simpa only [map_zero] using hv.symm)
  exact ⟨Units.mk0 x hx₀, hv⟩

private theorem adjoinUniformizerRoot {F K L : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {d : ℕ} (hd : 0 < d)
    (π : Fˣ) (hπ : normalizedValuation K (algebraMap F K (π : F)) = WithZero.exp (-1 : ℤ))
    (ξ : Lˣ) (hξ : (ξ : L) ^ d = algebraMap K L (algebraMap F K (π : F)))
    (hgen : Algebra.adjoin K ({(ξ : L)} : Set L) = ⊤) :
    ∃ r : AdjoinRoot (uniformizerPolynomial (K := K) d π) ≃ₐ[K] L,
      r (AdjoinRoot.root (uniformizerPolynomial (K := K) d π)) = ξ := by
  let f := uniformizerPolynomial (K := K) d π
  letI : Fact (Irreducible f) := ⟨uniformizer_polynomial_irreducible hd.ne' hπ⟩
  have hroot : f.eval₂ (Algebra.ofId K L) (ξ : L) = 0 := by
    simp [f, uniformizerPolynomial, hξ]
  let m := AdjoinRoot.liftAlgHom f (Algebra.ofId K L) (ξ : L) hroot
  have hm : m (AdjoinRoot.root f) = ξ := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hsurj : Function.Surjective m := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← hgen]
    exact Algebra.adjoin_le fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨AdjoinRoot.root f, hm⟩
  exact ⟨AlgEquiv.ofBijective m ⟨m.injective, hsurj⟩, hm⟩

open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {B : SplitBuildingLevel Y}
  {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')} {x : ℚ ⊗[ℤ] E.Y}
  {d : ℕ} {y : E.Y} {π : Kˣ}
  {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  {ξ : Lˣ}

set_option backward.isDefEq.respectTransparency false in
private def descentReduction
    (R : Specs.ExceptionalSplitParahoricReduction.FaceReduction B t x d y π L ξ) :
    FaceReduction B t x d y π L ξ where
  toFaceReduction := {
    component_eq := by
      have hp : (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of (residue L))))) =
          IsLocalRing.closedPoint (residue L) := Subsingleton.elim _ _
      simpa only [hp] using R.component_eq
    integral := R.integral
    scale := R.scale
    muGroup := R.muGroup
    unitPoints := R.unitPoints
    μImage := R.μImage
    μImage_cocharacter := R.μImage_cocharacter
    centralizer := R.centralizer
    centralizes := R.centralizes
    centralizer_smooth := R.centralizer_smooth
    identityComponent := R.identityComponent
    component_open := R.component_open
    group_is_affine := R.group_is_affine
    group_lft := R.group_lft
    group_qc := R.group_qc
    reductive := R.reductive
    torus := R.torus
    torusComparison := R.torusComparison
    torus_marked := R.torus_marked
    torus_split := R.torus_split
    torus_maximal := R.torus_maximal
    ambientMarking := R.ambientMarking
    root_characters := R.root_characters
    roots := R.roots
    borel := R.borel
    borel_is_borel := R.borel_is_borel
    borel_torus := R.borel_torus
    borel_roots := R.borel_roots
    reduction := R.reduction
    reduction_eq := R.reduction_eq
  }
  parameter := R.parameter
  same_residue := R.same_residue
  reduction_surjective := R.reduction_surjective
  preimage_borel := R.preimage_borel
  flags := R.flags
  incident := R.incident
  incident_eq := R.incident_eq

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The scaled residue flags yield a stable chamber of the original marked building. -/
theorem stableIncidentAlcoves : StableIncidentAlcoves.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ hunram D E M M' c p p' e Y B C l ω ρ h
    hmarked hauto a ha
  obtain ⟨face⟩ := fixed_standard_face B.adjoint B.coefficients ρ h hauto a ha
  obtain ⟨d, y, hd, hy⟩ := integralScalingDenominator face.x
  obtain ⟨π, hπ⟩ := exists_normalized_uniformizer F
  let πK := Units.map (algebraMap F K).toMonoidHom π
  have hπK : normalizedValuation K (πK : K) = WithZero.exp (-1 : ℤ) :=
    (hunram (π : F)).trans hπ
  obtain ⟨L, fL, aL, finL, vL, topL, locL, extL, ξ, hξ, hres, hgen, _, hram, _⟩ :=
    ExceptionalSplitParahoricReduction.exists_uniformizer_root_same_residue d hd πK hπK
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : ValuativeExtension F L := ⟨fun z z' => by
    rw [IsScalarTower.algebraMap_apply F K L, IsScalarTower.algebraMap_apply F K L,
      ValuativeExtension.vle_iff_vle (A := K), ValuativeExtension.vle_iff_vle (A := F)]⟩
  obtain ⟨r, hr⟩ := adjoinUniformizerRoot hd π hπK ξ hξ hgen
  obtain ⟨R₀⟩ := ExceptionalSplitParahoricReduction.splitFaceResidueAtRoot K B face.weights face.x
    face.rational_eq d y hd hy πK hπK L ξ hξ hres
  let R := descentReduction R₀
  let b := changeCoordinates ρ a (face.mover : FieldPoints M' K)
  obtain ⟨S, ⟨flag⟩, hflag⟩ := ExceptionalSplitParahoricDescent.splitParahoricResidueDescent
    hunram B ρ h C l ω hmarked hauto face.coefficient face.equivariant b face.cocycle
    face.weights face.x d y π ξ face.barycenter hd hy hπ face.rational_eq face.fixed r hr R
  obtain ⟨q, g, hq, hg, hfix⟩ := hflag flag
  exact ⟨{ face := face
           denominator := d
           cocharacter := y
           denominator_pos := hd
           scaling_eq := hy
           uniformizer := π
           uniformizer_value := hπ
           extension := L
           root := ξ
           rootAlgebra := r
           root_eq := hr
           ramification := hram
           reduction := R
           descended := S
           flag := flag
           incident := q
           chamber := g
           flag_eq := hq
           chamber_eq := hg
           fixed := hfix }⟩

end StableAlcove

section NormalForm

open Specs.AutomorphismSequence (AdjointQuotient)
open Specs.ExceptionalStableAlcoveRepresentatives (IsArithmeticFrobenius)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRingHom)
open Specs.ExceptionalMarkedRootDescent (markedFibrePoint markedWeylWord integralTestAlgebra)
open Specs.IntegralSemisimpleModel (cocharacter torusPoint)
open Specs.SplitIwahoriSchemeOperators (IsCoefficientAction IsMarkedRepresentative)
open ExceptionalStableAlcoveRepresentatives
  (stableAlcoveStabilizer outerAlcoveTypeCorrection innerLengthZeroRepresentatives
    innerAlcoveRepresentativeCocycle)
open ExceptionalSplitIwahoriDescent (splitIwahoriCocycleNeutralization)
open private markedTorusHom markedTorusHom_apply base_change_torus base_change_word
  cocharacterAction torus_word_power torusCocharacterHom
  from LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives
open private cocharacter_natural from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open scoped Pointwise WithZero

private theorem changeCoordinates_mul {Γ H : Type*} [Group Γ] [Group H]
    (ρ : Γ →* MulAut H) (a : Γ → H) (g k : H) (σ : Γ) :
    changeCoordinates ρ (changeCoordinates ρ a g) k σ = changeCoordinates ρ a (g * k) σ := by
  simp only [changeCoordinates, mul_inv_rev, map_mul]
  group

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  {G : Specs.AffineAlgebraicGroup F} {D : BasedRootDatum.{u}} {n : ℕ}
  {M : MarkedExceptionalCover D n} {Q : AdjointQuotient G}

set_option backward.isDefEq.respectTransparency false in
private theorem coefficient_of_trivial_diagram (L : MarkedUnramifiedLevel (K := K) M Q)
    (h : L.diagram = 1) (σ : Gal(K/F)) (g : FieldPoints M.adModel K) :
    L.coefficient σ g = scalarPoints M.adModel σ.toRingHom g := by
  obtain ⟨e, he⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison L.marking
  let R := CommAlgCat.of F K
  obtain ⟨v, hv⟩ := (e.app R).groupIsoToMulEquiv.surjective g
  change e.hom.app R v = g at hv
  rw [he] at hv
  rw [← hv, L.markedCoefficient.1, h]
  let f : R ⟶ R := CommAlgCat.ofHom σ.toAlgHom
  change pinnedCoefficientPoint L.marking (L.pinned ((1 : Gal(K/F) →*
    Aut L.marking.realization.attached.toBased) σ)) σ v = _
  simp only [MonoidHom.one_apply, map_one]
  change markedFibrePoint L.marking R (mapPoints f v) =
    scalarPoints M.adModel σ.toRingHom (markedFibrePoint L.marking R v)
  rw [← he, ← he]
  exact ConcreteCategory.congr_hom (e.hom.naturality f) v

private theorem scalar_marked_word (M' : Model D) (π : Fˣ) (y : D.Y) (word : List D.I) :
    scalarPoints M' (algebraMap F K)
        (markedTorusHom M' (integralRing F) (cocharacter D y (integralRing F) π) *
          markedWeylWord M'.toIntegralMarking (integralRing F) word) =
      markedTorusHom M' (integralRing K)
          (cocharacter D y (integralRing K) (Units.map (algebraMap F K).toMonoidHom π)) *
        markedWeylWord M'.toIntegralMarking (integralRing K) word := by
  let f := integralRingMap (algebraMap F K)
  rw [map_mul]
  change changeRingHom M'.group f (markedTorusHom M' (integralRing F) _) *
    changeRingHom M'.group f (markedWeylWord M'.toIntegralMarking (integralRing F) word) = _
  rw [base_change_torus, cocharacter_natural, base_change_word]
  rfl

private theorem marked_word_pow (M' : Model D) (π : Kˣ) (y : D.Y) (word : List D.I) (m : ℕ) :
    ∃ (y' : D.Y) (word' : List D.I),
      (markedTorusHom M' (integralRing K) (cocharacter D y (integralRing K) π) *
        markedWeylWord M'.toIntegralMarking (integralRing K) word) ^ m =
        markedTorusHom M' (integralRing K) (cocharacter D y' (integralRing K) π) *
          markedWeylWord M'.toIntegralMarking (integralRing K) word' := by
  let R := integralRing K
  let w := cocharacterAction D (word.map (RootPairing.weylGroup.ofIdx D.datum)).prod
  have hp (m : ℕ) : ∃ word' : List D.I,
      markedWeylWord M'.toIntegralMarking R word ^ m = markedWeylWord M'.toIntegralMarking R word' := by
    induction m with
    | zero => exact ⟨[], rfl⟩
    | succ m ih =>
      obtain ⟨word', hword'⟩ := ih
      refine ⟨word' ++ word, ?_⟩
      rw [pow_succ, hword']
      simp only [markedWeylWord, List.map_append, List.prod_append]
  obtain ⟨word', hw⟩ := hp m
  refine ⟨∑ j ∈ Finset.range m, (w ^ j) y, word', ?_⟩
  have h := torus_word_power M' R word π y m
  change (_ * _) ^ m = markedTorusHom M' R (cocharacter D _ R π) *
    markedWeylWord M'.toIntegralMarking R word ^ m at h
  exact h.trans (congrArg (_ * ·) hw)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem alcoveNormalFormAtLevel (L : MarkedUnramifiedLevel (K := K) M Q)
    (hunram : IsUnramifiedLocalExtension F K) (φ : Gal(K/F)) (hφ : IsArithmeticFrobenius φ)
    (hn : n = 6 ∨ n = 7 ∨ n = 8) (hbranch : n = 6 ∨ L.diagram = 1)
    (hdegree : 12 ∣ Nat.card Gal(K/F))
    (a : Gal(K/F) → FieldPoints M.adModel K)
    (ha : ∀ σ τ, a (σ * τ) = a σ * L.coefficient σ (a τ)) :
    Nonempty (AlcoveNormalForm L a) := by
  obtain ⟨S⟩ := stableIncidentAlcoves hunram L.building L.marking L.pinned L.diagram L.coefficient
    L.affineAction L.markedCoefficient L.affine_comparison a ha
  let b := changeCoordinates L.coefficient a (S.mover : FieldPoints M.adModel K)
  have hb (σ τ) : b (σ * τ) = b σ * L.coefficient σ (b τ) :=
    change_cocycle L.coefficient a ha S.mover σ τ
  have hb_eq (σ) : b σ = changeCoordinates L.coefficient
      (changeCoordinates L.coefficient a (S.face.mover : FieldPoints M.adModel K)) S.chamber σ :=
    (changeCoordinates_mul _ _ _ _ _).symm
  obtain ⟨_, hst⟩ := stableAlcoveStabilizer L.building L.affine_comparison S.face.coefficient
    (changeCoordinates L.coefficient a (S.face.mover : FieldPoints M.adModel K))
    S.chamber S.face.cocycle S.fixed
  have hstab (σ) :
      L.building.adjoint.action (b σ) ''
          (S.face.coefficient.action σ '' L.building.ad.realization.closedFace 1 ∅) =
            L.building.ad.realization.closedFace 1 ∅ ∧
      b σ ∈ L.level.ad.I ⊔ lengthZeroNormalizer L.level.ad ∧
      (typeChange L.level.typeQuotient (b σ) = 1 ↔ b σ ∈ L.level.ad.I) := by
    rw [hb_eq]
    exact hst σ
  by_cases hi : L.diagram = 1
  · have hscalar := coefficient_of_trivial_diagram L hi
    have htype (σ) : TypeQuotientTransport L.level.typeQuotient L.level.typeQuotient
        (L.coefficient σ).toMonoidHom (MonoidHom.id _) := by
      have hσ : L.diagram σ = 1 := by simp [hi]
      have hId : (L.typeAction σ).toMonoidHom = MonoidHom.id _ := by
        rw [(L.type_action_eq σ).1 hσ]
        rfl
      rw [← hId]
      exact L.type_comparison σ
    obtain ⟨π, hπ⟩ := exists_normalized_uniformizer F
    obtain ⟨y, word, t₀, hword, heval, _, hclass, htmem, htfin, hpow, ht1⟩ :=
      innerLengthZeroRepresentatives L.base L.baseBuilding n M.adNumbering hn M.adNumbering_eq
        M.rootSpan π hπ (typeChange L.level.typeQuotient (b φ))
    let t : lengthZeroNormalizer L.base.ad := ⟨t₀, htmem⟩
    have htord : orderOf (t : FieldPoints M.adModel F) ∣ Nat.card Gal(K/F) := by
      apply dvd_trans (orderOf_dvd_of_pow_eq_one hpow)
      refine dvd_trans ?_ hdegree
      rw [L.type_order]
      rcases hn with h | h | h <;> rw [h] <;> decide
    obtain ⟨r, hgen, hrmem, hrc, hrtype, hdiff, _, _⟩ :=
      innerAlcoveRepresentativeCocycle hunram L.base L.level L.building L.scalar L.scalar_types
        φ hφ L.coefficient hscalar htype b hb (fun σ => (hstab σ).2.1) t hclass htord
    have hmark (σ : Gal(K/F)) : IsMarkedRepresentative L.level (r σ) := by
      have hs : σ ∈ Subgroup.zpowers φ := hφ.1 ▸ Subgroup.mem_top _
      obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr hs
      rw [← hm, map_pow, hgen]
      let πK := Units.map (algebraMap F K).toMonoidHom π
      have hπK : normalizedValuation K (πK : K) = WithZero.exp (-1 : ℤ) :=
        (hunram (π : F)).trans hπ
      have ht' : scalarPoints M.adModel (algebraMap F K) t =
          markedTorusHom M.adModel (integralRing K) (cocharacter M.adDatum y (integralRing K) πK) *
            markedWeylWord M.adModel.toIntegralMarking (integralRing K) word := by
        change scalarPoints M.adModel (algebraMap F K) (t₀ : FieldPoints M.adModel F) = _
        rw [heval]
        exact scalar_marked_word M.adModel π y word
      refine ⟨by rw [← hgen, ← map_pow]; exact hrmem (φ ^ m), πK, ?_⟩
      rw [ht']
      obtain ⟨y', word', hpow'⟩ := marked_word_pow M.adModel πK y word m
      exact ⟨y', word', hπK, hpow'⟩
    obtain ⟨k, hk⟩ := splitIwahoriCocycleNeutralization hunram L.level L.coefficient r b
      hrc (.inr ⟨hscalar, hmark⟩) hb hdiff
    refine ⟨{
               stable := S
               stabilized := hstab
               frobenius := φ
               arithmetic := hφ
               correction := k
               representative := r
               representative_cocycle := hrc
               representative_mem := hrmem
               correction_eq := fun σ => (hk σ).symm.trans (changeCoordinates_mul _ _ _ _ _)
               outer_correction := fun ho => (ho hi).elim
               inner_correction := fun _ => ⟨k.property, π, y, word, t, hπ, hword, heval,
                 htfin, htord, hrtype, fun h => ht1 (hclass.symm.trans h), hgen⟩ }⟩
  · have hn6 := hbranch.resolve_right hi
    subst n
    have hnφ : L.diagram φ ≠ 1 := by
      intro h
      apply hi
      ext σ
      have hm : σ ∈ Subgroup.zpowers φ := hφ.1 ▸ Subgroup.mem_top _
      obtain ⟨m, rfl⟩ := hm
      simp [map_zpow, h]
    obtain ⟨δ, _, hδc, hδ⟩ :=
      outerAlcoveTypeCorrection L.building M.adNumbering M.adNumbering_eq M.rootSpan
        φ hφ.1 L.coefficient L.affineAction L.typeAction
        (fun σ => ⟨L.affine_comparison σ, L.type_comparison σ⟩)
        ((L.type_action_eq φ).2 hnφ) b hb (fun σ => (hstab σ).2.1)
    let b' := changeCoordinates L.coefficient b (δ : FieldPoints M.adModel K)
    have hcoef : IsCoefficientAction L.coefficient :=
      .inr ⟨L.marking, L.pinned.toMonoidHom.comp L.diagram, L.markedCoefficient.1⟩
    obtain ⟨k, hk⟩ := splitIwahoriCocycleNeutralization hunram L.level L.coefficient 1 b'
      (by simp) (.inl ⟨hcoef, rfl⟩) hδc
      (fun σ => by simpa only [Pi.one_apply, inv_one, mul_one] using
        (show b' σ ∈ L.level.ad.I from hδ σ))
    refine ⟨{
               stable := S
               stabilized := hstab
               frobenius := φ
               arithmetic := hφ
               correction := (δ : FieldPoints M.adModel K) * k
               representative := 1
               representative_cocycle := by simp
               representative_mem := fun _ => Subgroup.one_mem _
               correction_eq := ?_
               outer_correction := fun _ => ⟨δ, k, rfl, ?_, fun _ => rfl⟩
               inner_correction := fun h => (hi h).elim }⟩
    · intro σ
      exact (hk σ).symm.trans ((changeCoordinates_mul _ _ _ _ _).trans
        (changeCoordinates_mul _ _ _ _ _))
    · intro σ
      rw [← changeCoordinates_mul]
      exact hδ σ

end NormalForm

section FieldSupport

open Opposite
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation normalizedValueGroupMap ramificationIndex)
open Specs.ExceptionalStableAlcoveRepresentatives (IsArithmeticFrobenius)
open MaximalUnramifiedBrauer (IsUnramified)
open Specs.ExceptionalUnramifiedCocycleSupport (HasUnramifiedSupport)
open Descent.NonabelianCohomology (pointAction pointMap restriction)
open ExceptionalUnramifiedCocycleSupport (arithmeticFrobenius unramifiedEnlargement)
open private normalizedValueGroupMap_apply normalizedValueGroupMap_exp normalizedValuation_algebraMap_exp
  from LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open scoped WithZero

local notation "CohPoints" => Descent.NonabelianCohomology.Points

private theorem pointMap_comp_apply {F K L E : Type u} [Field F] [Field K] [Field L] [Field E]
    [Algebra F K] [Algebra F L] [Algebra F E]
    (H : Specs.GroupScheme F) (i : K →ₐ[F] L) (j : L →ₐ[F] E) (x : CohPoints F K H.X) :
    pointMap F L H.X j (pointMap F K H.X i x) = pointMap F K H.X (j.comp i) x := by
  change (testSpec F).map (CommAlgCat.ofHom j).op ≫
      (testSpec F).map (CommAlgCat.ofHom i).op ≫ x =
    (testSpec F).map (CommAlgCat.ofHom (j.comp i)).op ≫ x
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

private theorem pointMap_equivariant {F K L : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] (H : Specs.GroupScheme F)
    (i : K →ₐ[F] L) (σ : Gal(K/F)) (τ : Gal(L/F))
    (h : ∀ z, i (σ z) = τ (i z)) (x : CohPoints F K H.X) :
    pointMap F K H.X i (pointAction F K H.X σ x) =
      pointAction F L H.X τ (pointMap F K H.X i x) := by
  change pointMap F K H.X i (pointMap F K H.X σ.toAlgHom x) =
    pointMap F L H.X τ.toAlgHom (pointMap F K H.X i x)
  rw [pointMap_comp_apply, pointMap_comp_apply]
  have he : i.comp σ.toAlgHom = τ.toAlgHom.comp i := AlgHom.ext h
  rw [he]

private theorem normalized_unramified {F K : Type u} [Field F] [Field K] [Algebra F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    (h : Function.Surjective (fun x : F => ValuativeRel.valuation K (algebraMap F K x))) :
    IsUnramifiedLocalExtension F K := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨x, hx⟩ := h (e.symm (WithZero.exp (1 : ℤ)))
  have hxv : normalizedValuation K (algebraMap F K x) = WithZero.exp (1 : ℤ) := by
    change e (ValuativeRel.valuation K (algebraMap F K x)) = _
    exact (congrArg e hx).trans (e.apply_symm_apply _)
  have hx₀ : x ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (by simpa only [map_zero] using hxv.symm)
  have hpos : 0 < ramificationIndex F K := by
    have hm : StrictMono (normalizedValueGroupMap F K) :=
      e.strictMono.comp (ValuativeExtension.mapValueGroupWithZero_strictMono.comp
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).symm.strictMono)
    have ht := hm (WithZero.exp_lt_exp.mpr (show (0 : ℤ) < 1 by decide))
    rw [normalizedValueGroupMap_exp, normalizedValueGroupMap_exp, mul_zero, mul_one,
      WithZero.exp_lt_exp] at ht
    exact ht
  rw [normalizedValuation_algebraMap_exp F K hx₀] at hxv
  have he : ramificationIndex F K = 1 :=
    Int.eq_one_of_dvd_one hpos.le ⟨_, (WithZero.exp_injective hxv).symm⟩
  intro z
  by_cases hz : z = 0
  · simp [hz]
  rw [normalizedValuation_algebraMap_exp F K hz, he, one_mul, WithZero.exp_log]
  exact (map_ne_zero (normalizedValuation F)).mpr hz

set_option backward.isDefEq.respectTransparency false in
private theorem frobenius_of_unramified {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    (h : Function.Surjective (fun x : F => ValuativeRel.valuation K (algebraMap F K x))) :
    ∃ φ : Gal(K/F), IsArithmeticFrobenius φ := by
  obtain ⟨φ, hres, _, _, hgen⟩ := arithmeticFrobenius (F := F) (L := K) h
  refine ⟨φ, top_unique ?_, ?_⟩
  · intro σ _
    obtain ⟨j, rfl⟩ := hgen.surjective σ
    exact ⟨(j.val : ℤ), zpow_natCast _ _⟩
  · intro z z' hz
    obtain ⟨y, hy, hpow⟩ := hres z
    have he : y = z' := Subtype.ext (hy.trans hz.symm)
    rw [he] at hpow
    exact hpow

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem enlargeCocycleSupport {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {H : Specs.GroupScheme F}
    {K₀ : FiniteGaloisIntermediateField F (SeparableClosure F)}
    {b : Gal(SeparableClosure F/F) → CohPoints F (SeparableClosure F) H.X}
    (hb : HasUnramifiedSupport (G := H) K₀ b) :
    ∃ (K : FiniteGaloisIntermediateField F (SeparableClosure F))
      (_ : ValuativeRel K) (_ : TopologicalSpace K) (_ : IsNonarchimedeanLocalField K)
      (_ : ValuativeExtension F K),
      K₀ ≤ K ∧ IsUnramifiedLocalExtension F K ∧ 12 ∣ Nat.card Gal(K/F) ∧
      (∃ φ : Gal(K/F), IsArithmeticFrobenius φ) ∧
      ∃ aK : Gal(K/F) → CohPoints F K H.X,
        (∀ σ τ, aK (σ * τ) = aK σ * pointAction F K H.X σ (aK τ)) ∧
        ∀ σ, pointMap F K H.X K.toIntermediateField.val (aK (restriction K σ)) = b σ := by
  obtain ⟨J, aJ, h₀J, hJ, hJc, hJb⟩ := hb
  obtain ⟨K, hJK, hK, hdegree, r, _, hr, hrabs⟩ := unramifiedEnlargement J hJ 12 (by decide)
  obtain ⟨_, _, vK, topK, locK, extK, hs⟩ := hK
  let i := IntermediateField.inclusion hJK
  letI : Algebra J K := i.toAlgebra
  letI : IsScalarTower F J K := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  letI : Module.Free J K := Module.Free.of_divisionRing _ _
  have hd : 12 ∣ Nat.card Gal(K/F) := by
    rw [IsGalois.card_aut_eq_finrank F K, ← Module.finrank_mul_finrank F J K]
    exact dvd_mul_of_dvd_right hdegree _
  let aK σ := pointMap F J H.X i (aJ (r σ))
  refine ⟨K, vK, topK, locK, extK, h₀J.trans hJK, normalized_unramified hs, hd,
    frobenius_of_unramified hs, aK, ?_, ?_⟩
  · intro σ τ
    dsimp only [aK]
    rw [map_mul r, hJc, map_mul, pointMap_equivariant H i (r σ) σ (hr σ)]
  · intro σ
    dsimp only [aK]
    rw [pointMap_comp_apply, hrabs]
    exact hJb σ

end FieldSupport

section MarkedCover

open Specs.Pinning (BasedIso)
open Specs.ExceptionalAffineRootSystems (exceptionalCartan)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open ExceptionalIwahoriImageComparison (markedCentralCoverExists)
open private cover_simple from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private derivedDatum derivedDatum_coroots_span restrictToCorootLattice
  from LinearAlgebraicGroups.Classification.IntegralRealization

private noncomputable def dualDatum (D : BasedRootDatum.{u}) : BasedRootDatum.{u} := by
  letI := D.finiteRoots
  letI := D.freeX
  letI := D.freeY
  letI := D.reduced
  exact {
    I := D.I
    X := D.Y
    Y := D.X
    finiteRoots := D.finiteRoots
    freeX := D.freeY
    freeY := D.freeX
    finiteX := D.finiteY
    finiteY := D.finiteX
    datum := D.datum.flip
    reduced := inferInstance
    base := D.base.flip }

private noncomputable abbrev adjointDatum (D : BasedRootDatum.{u}) : BasedRootDatum.{u} :=
  dualDatum (derivedDatum (dualDatum D))

private noncomputable abbrev adjointCocharacterMap (D : BasedRootDatum.{u}) :
    D.Y →ₗ[ℤ] (adjointDatum D).Y :=
  restrictToCorootLattice (dualDatum D)

private theorem adjointCocharacterMap_coroot (D : BasedRootDatum.{u}) (i : D.I) :
    adjointCocharacterMap D (D.datum.coroot i) = (adjointDatum D).datum.coroot i := rfl

private theorem adjointCocharacterMap_pairing (D : BasedRootDatum.{u}) (i : D.I) (y : D.Y) :
    (adjointDatum D).datum.toLinearMap ((adjointDatum D).datum.root i) (adjointCocharacterMap D y) =
      D.datum.toLinearMap (D.datum.root i) y := rfl

private theorem cocharacter_zero_of_root_evaluations (D : BasedRootDatum.{u})
    (hD : D.datum.corootSpan ℤ = ⊤) (y : D.Y) (h : ∀ i, D.datum.root' i y = 0) : y = 0 := by
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  apply D.datum.flip.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero
  · change y ∈ D.datum.corootSpan ℤ
    rw [hD]
    exact Submodule.mem_top
  · rw [RootPairing.rootForm_apply_apply]
    simp only [show ∀ i, D.datum.flip.coroot' i y = D.datum.root' i y from fun _ => rfl,
      h, zero_mul, Finset.sum_const_zero]

private theorem cocharacter_range {D E : BasedRootDatum.{u}}
    (f : D.Y →ₗ[ℤ] E.Y) (e : D.I ≃ E.I)
    (hD : D.datum.corootSpan ℤ = ⊤) (h : ∀ i, f (D.datum.coroot i) = E.datum.coroot (e i)) :
    f.range = E.datum.corootSpan ℤ := by
  rw [← Submodule.map_top, ← hD]
  change (Submodule.span ℤ (Set.range D.datum.coroot)).map f =
    Submodule.span ℤ (Set.range E.datum.coroot)
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, (h i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp [h]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem markedCoverDatumIso {D C : BasedRootDatum.{u}}
    {M : Model C} {M' : Model (adjointDatum D)}
    (c : MarkedCentralCover M M') (hD : D.datum.corootSpan ℤ = ⊤)
    (hC : C.datum.corootSpan ℤ = ⊤) :
    ∃ e : BasedIso D C, e.val.indexEquiv = c.rootEquiv.symm := by
  let E := adjointDatum D
  let f : D.Y →ₗ[ℤ] E.Y := adjointCocharacterMap D
  let g : C.Y →ₗ[ℤ] E.Y := c.pushCocharacter
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hz := LinearMap.mem_ker.mp hy
    apply cocharacter_zero_of_root_evaluations D hD y
    intro i
    change D.datum.toLinearMap (D.datum.root i) y = 0
    rw [← adjointCocharacterMap_pairing D i y]
    change E.datum.toLinearMap (E.datum.root i) (f y) = 0
    rw [hz, map_zero]
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hz := LinearMap.mem_ker.mp hy
    apply cocharacter_zero_of_root_evaluations C hC y
    intro i
    change C.datum.toLinearMap (C.datum.root i) y = 0
    rw [← c.roots i, c.pairing]
    change E.datum.toLinearMap _ (g y) = 0
    rw [hz, map_zero]
  have hrange : f.range = g.range :=
    (cocharacter_range f (.refl _) hD (adjointCocharacterMap_coroot D)).trans
      (cocharacter_range g c.rootEquiv hC c.coroots).symm
  let ey := (LinearEquiv.ofInjective f hf).trans
    ((LinearEquiv.ofEq _ _ hrange).trans (LinearEquiv.ofInjective g hg).symm)
  have hey (y : D.Y) : g (ey y) = f y := by
    have h := (LinearEquiv.ofInjective g hg).apply_symm_apply
      (LinearEquiv.ofEq _ _ hrange (LinearEquiv.ofInjective f hf y))
    exact congrArg Subtype.val h
  have hey_coroot (i : C.I) : ey.symm (C.datum.coroot i) = D.datum.coroot (c.rootEquiv i) := by
    apply ey.injective
    rw [ey.apply_symm_apply]
    apply hg
    rw [hey, c.coroots]
    exact (adjointCocharacterMap_coroot D _).symm
  let ex := D.datum.toPerfPair.trans (ey.symm.dualMap.trans C.datum.toPerfPair.symm)
  have hex (x : D.X) (y : C.Y) :
      C.datum.toLinearMap (ex x) y = D.datum.toLinearMap x (ey.symm y) := by
    change C.datum.toPerfPair (C.datum.toPerfPair.symm _) y = _
    rw [C.datum.toPerfPair.apply_symm_apply]
    rfl
  let τ : D.datum.Equiv C.datum := {
    weightMap := ex
    coweightMap := ey.symm
    indexEquiv := c.rootEquiv.symm
    weight_coweight_transpose := by ext y x; exact hex x y
    root_weightMap := by
      funext i
      apply C.datum.toPerfPair.injective
      ext y
      change C.datum.toLinearMap (ex (D.datum.root i)) y =
        C.datum.toLinearMap (C.datum.root (c.rootEquiv.symm i)) y
      rw [hex, ← adjointCocharacterMap_pairing, ← c.roots, c.pairing,
        c.rootEquiv.apply_symm_apply]
      have he := hey (ey.symm y)
      rw [ey.apply_symm_apply] at he
      rw [← he]
    coroot_coweightMap := funext hey_coroot
    bijective_weightMap := ex.bijective
    bijective_coweightMap := ey.symm.bijective }
  refine ⟨⟨τ, ?_⟩, rfl⟩
  ext i
  change i ∈ c.rootEquiv.symm '' (D.base.support : Set D.I) ↔ i ∈ C.base.support
  rw [Set.mem_image_equiv]
  exact (cover_simple c i).symm

private theorem exceptionalCartan_eq (n : ℕ) (h : n = 6 ∨ n = 7 ∨ n = 8) :
    exceptionalCartan n = CartanMatrix.E n := by
  rcases h with rfl | rfl | rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;> decide

set_option backward.isDefEq.respectTransparency false in
private theorem markedExceptionalCoverExists (D : BasedRootDatum.{u}) (n : ℕ)
    (b : Fin n ≃ D.base.support) (hD : D.datum.corootSpan ℤ = ⊤)
    (hb : ∀ i j, D.datum.pairing (b i) (b j) = exceptionalCartan n i j) :
    Nonempty (MarkedExceptionalCover D n) := by
  classical
  let E := adjointDatum D
  have hE : E.datum.rootSpan ℤ = ⊤ := derivedDatum_coroots_span (dualDatum D)
  obtain ⟨C, MC, ME, hC, ⟨c⟩⟩ := markedCentralCoverExists E hE
  obtain ⟨e, he⟩ := markedCoverDatumIso c hD hC
  let bC := b.trans ((e.val.indexEquiv.image _).trans (Set.equivOfEq e.property))
  let bE : Fin n ≃ E.base.support := b
  letI := D.freeX
  let hrankC : Module.finrank ℤ C.Y = n := by
    let B := C.base.flip.toWeightBasisInt.map (LinearEquiv.ofTop _ hC)
    rw [Module.finrank_eq_nat_card_basis B]
    change Nat.card C.base.support = n
    exact (Nat.card_congr bC.symm).trans (Nat.card_fin n)
  let hrankE : Module.finrank ℤ E.Y = n := by
    change Module.finrank ℤ (Module.Dual ℤ (D.datum.rootSpan ℤ)) = n
    rw [← D.base.toWeightBasisInt.toDualEquiv.finrank_eq,
      Module.finrank_eq_nat_card_basis D.base.toWeightBasisInt]
    exact (Nat.card_congr b.symm).trans (Nat.card_fin n)
  have hc (i : Fin n) : c.rootEquiv (bC i).val = (bE i).val := by
    change c.rootEquiv (e.val.indexEquiv (b i).val) = (b i).val
    rw [he]
    exact c.rootEquiv.apply_symm_apply ((b i).val : E.I)
  refine ⟨⟨C, E, MC, ME, c, e, bC, bE, ⟨hrankC, ?_⟩, ⟨hrankE, ?_⟩, hc, hC, hE⟩⟩
  · intro i j
    exact e.val.toHom.pairing.trans (hb i j)
  · intro i j
    exact hb i j

end MarkedCover

section AbsoluteNormalForm

open _root_.LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence restrictIso)
open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction pinnedSection
  basedAutTopology fieldGalTopology)
open Specs.ExceptionalFormsOverUnramifiedFields (IsExceptionalReference HasTypeE)
open Specs.ExceptionalTwistedTraceComparison (Twist PointCocycle)
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Specs.GeometricRadicals (IsSemisimple IsSplitReductive)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.RelativeFormComparison (fieldMap fieldTest transportedAut)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Specs.ExceptionalAffineRootSystems (alcoveStabilizer)
open Descent.NonabelianCohomology (Cocycle pointAction pointMap restriction)
open MaximalUnramifiedBrauer (IsUnramified)
open ExceptionalUnramifiedCocycleSupport (exceptionalCocycleSupport neutralTwist)
open ExceptionalStableAlcoveRepresentatives (cocycle_trivial_of_generator)
open private simpleRootEquiv iso_of_fixed_trivialization
  from LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport
open private latticeCriterion_pair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private pushKBorel maximalTransport from LinearAlgebraicGroups.Classification.PinnedEquivalence

attribute [local instance] basedAutTopology fieldGalTopology

local notation "CohPoints" => Descent.NonabelianCohomology.Points

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

set_option backward.isDefEq.respectTransparency false in
private theorem pinned_trivialization_fixed
    {A : RootGroups.AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G} {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) D.toBased)}
    (V : PinnedRepresentative (S := SeparableClosure F) E ω)
    (σ : Gal(SeparableClosure F/F)) (h : ω σ = 1) :
    restrictIso (fieldMap F (SeparableClosure F) σ) V.trivialization = V.trivialization := by
  have ht := V.transport_eq σ
  rw [h, map_one] at ht
  change Aut.of (restrictIso (fieldMap F (SeparableClosure F) σ) V.trivialization ≪≫
    V.trivialization.symm) = 1 at ht
  have hj := congrArg Aut.asIso ht
  change restrictIso (fieldMap F (SeparableClosure F) σ) V.trivialization ≪≫
    V.trivialization.symm = Iso.refl _ at hj
  have hc := congrArg (fun i => i ≪≫ V.trivialization) hj
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans] using hc

set_option backward.isDefEq.respectTransparency false in
private theorem twist_isQuasiSplit_of_iso
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := SeparableClosure F) Q.quotient.val} (T : Twist a)
    (i : G.val ≅ T.group.val) (B : ClosedSubgroup G.val) (hB : GeometricBorelConjugacy.IsKBorel B) :
    IsQuasiSplit T.group :=
  ⟨T.reductive, transportSubgroup i B, pushKBorel i hB⟩

private theorem twist_isSplit_of_iso
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := SeparableClosure F) Q.quotient.val} (T : Twist a)
    (P : Pinning.SplitBorelPair F) (i : P.G.val ≅ T.group.val) : IsSplitReductive T.group :=
  ⟨T.reductive, transportSubgroup i P.T, P.split, maximalTransport i P.T P.maximal⟩

variable {K : FiniteGaloisIntermediateField F (SeparableClosure F)}
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    {D : BasedRootDatum.{u}} {n : ℕ} {M : MarkedExceptionalCover D n}
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}

set_option backward.isDefEq.respectTransparency false in
private theorem representative_trivial_of_type
    {L : MarkedUnramifiedLevel (K := K) M Q}
    {a : Gal(K/F) → FieldPoints M.adModel K} (N : AlcoveNormalForm L a)
    (hi : L.diagram = 1)
    (htype : n = 8 ∨ ∀ σ, typeChange L.level.typeQuotient (N.representative σ) = 1) :
    ∀ σ, N.representative σ = 1 := by
  have hφ : typeChange L.level.typeQuotient (N.representative N.frobenius) = 1 := by
    rcases htype with h8 | ht
    · have hone := L.type_order.trans (show (if n = 6 then 3 else if n = 7 then 2 else 1) = 1 by
        rw [h8]; decide)
      exact (Nat.card_eq_one_iff_unique.mp hone).1.elim _ _
    · exact ht _
  obtain ⟨_, π, y, word, t, _, _, _, _, _, _, ht, hrep⟩ := N.inner_correction hi
  apply cocycle_trivial_of_generator L.coefficient N.representative N.representative_cocycle
    N.frobenius N.arithmetic.1
  have hclass : typeChange L.base.typeQuotient t = 1 :=
    (L.scalar_types.1 (t : FieldPoints M.adModel F)).symm.trans (hrep ▸ hφ)
  rw [hrep, ht hclass, map_one]

set_option maxHeartbeats 1100000 in
set_option backward.isDefEq.respectTransparency false in
private theorem inflateNormalForm
    {L : MarkedUnramifiedLevel (K := K) M Q}
    (a : PointCocycle (S := SeparableClosure F) Q.quotient.val)
    (aK : Gal(K/F) → CohPoints F K Q.quotient.val.X)
    (N : AlcoveNormalForm L (fun σ => L.adjointPoint (aK σ)))
    (b : CohPoints F (SeparableClosure F) Q.quotient.val.X)
    (hb : ∀ σ, pointMap F K Q.quotient.val.X K.toIntermediateField.val (aK (restriction K σ)) =
      changeCoordinates (pointAction F (SeparableClosure F) Q.quotient.val.X) a.val b σ) :
    ∃ b' : CohPoints F (SeparableClosure F) Q.quotient.val.X,
      ∀ σ, pointMap F K Q.quotient.val.X K.toIntermediateField.val
        (L.adjointPoint.symm (N.representative (restriction K σ))) =
          changeCoordinates (pointAction F (SeparableClosure F) Q.quotient.val.X) a.val b' σ := by
  let J := Q.quotient.val
  let p := pointMap F K J.X K.toIntermediateField.val
  let t : FieldPoints M.adModel K := (N.stable.mover : FieldPoints M.adModel K) * N.correction
  let z := L.adjointPoint.symm t
  let ρ := pointAction F (SeparableClosure F) J.X
  refine ⟨b * p z, fun σ => ?_⟩
  have heq : L.adjointPoint z = t := L.adjointPoint.apply_symm_apply _
  have hσ : ∀ x : K, K.toIntermediateField.val (restriction K σ x) =
      σ (K.toIntermediateField.val x) := AlgEquiv.restrictNormalHom_apply K.toIntermediateField σ
  have h (τ : Gal(K/F)) :
      L.adjointPoint.symm (N.representative τ) =
        changeCoordinates (pointAction F K J.X) aK z τ := by
    rw [N.correction_eq τ]
    change L.adjointPoint.symm (changeCoordinates L.coefficient
      (fun σ' => L.adjointPoint (aK σ')) t τ) = _
    rw [← heq, changeCoordinates, changeCoordinates, ← L.coefficient_eq, ← map_inv, ← map_mul,
      ← map_mul, L.adjointPoint.symm_apply_apply]
  rw [h]
  change p (changeCoordinates (pointAction F K J.X) aK z (restriction K σ)) =
    changeCoordinates ρ a.val (b * p z) σ
  rw [changeCoordinates, map_mul, map_mul, map_inv,
    pointMap_equivariant J K.toIntermediateField.val (restriction K σ) σ hσ, hb σ,
    ← changeCoordinates_mul]
  rfl

/-- The marked comparison at a fixed unramified level, after the given
diagram cocycle has factored through that level. -/
private def UnramifiedMarkedLevels : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {A : RootGroups.AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G} {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) D.toBased)}
    (V : PinnedRepresentative (S := SeparableClosure F) E ω)
    (n : ℕ) (_hn : n = 6 ∨ n = 7 ∨ n = 8) (_hbranch : n = 6 ∨ ∀ σ, ω σ = 1)
    (M : MarkedExceptionalCover D.toBased n) (Q₀ : AdjointQuotient V.model.val)
    (K : FiniteGaloisIntermediateField F (SeparableClosure F))
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ ωK : Gal(K/F) →* Aut D.toBased, (∀ σ, ωK (restriction K σ) = ω σ) →
    ∃ L : MarkedUnramifiedLevel (K := K) M Q₀,
      IsReferenceMarking V K L ∧
      (L.diagram = 1 ↔ ∀ σ, ω σ = 1) ∧
      (∀ (σ : Gal(SeparableClosure F/F)) (α : D.toBased.I),
        (markedDiagramEquiv L.marking.realization (L.diagram (restriction K σ))).asIso.hom.val.indexEquiv
          (M.cover.rootEquiv (M.datum.val.indexEquiv α)) =
        M.cover.rootEquiv (M.datum.val.indexEquiv ((ω σ).asIso.hom.val.indexEquiv α)))

set_option maxHeartbeats 2400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exceptionalAlcoveNormalForm_of_markedLevels (mark : UnramifiedMarkedLevels.{u}) :
    ExceptionalAlcoveNormalForm.{u} := by
  intro F _ _ _ _ S A P D l Q E ω V n hn htype hss hsc hbranch K₀ hK₀ ⟨ω₀, hω₀⟩ Q₀ a
  have href : IsExceptionalReference D := ⟨hss, hsc, by
    rcases hn with rfl | rfl | rfl
    · exact .inl htype
    · exact .inr (.inl htype)
    · exact .inr (.inr htype)⟩
  obtain ⟨b, hb⟩ := exceptionalCocycleSupport V href Q₀ K₀ hK₀ ⟨ω₀, hω₀⟩ a
  obtain ⟨K, vK, topK, locK, extK, h₀K, hKu, hd, ⟨φ, hφ⟩, aK, haK, haKS⟩ :=
    enlargeCocycleSupport hb
  have hD : D.toBased.datum.corootSpan ℤ = ⊤ :=
    (latticeCriterion_pair Classification.IntegralRealization.integralRealization P.pair D hss).mp hsc
  obtain ⟨b₀, b₀eq⟩ := htype
  let bD := b₀.trans (simpleRootEquiv D)
  obtain ⟨M⟩ := markedExceptionalCoverExists D.toBased n bD hD
    (fun i j => (b₀eq i j).trans (congrFun
      (congrFun (exceptionalCartan_eq n hn).symm i) j))
  letI : Algebra K₀ K := (IntermediateField.inclusion h₀K).toAlgebra
  letI : IsScalarTower F K₀ K :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion h₀K).comp_algebraMap.symm
  let ωK := ω₀.comp (AlgEquiv.restrictNormalHom K₀ : Gal(K/F) →* Gal(K₀/F))
  have hωK (σ : Gal(S/F)) : ωK (restriction K σ) = ω σ := by
    rw [← hω₀ σ]
    apply congrArg ω₀
    apply AlgEquiv.ext
    intro x
    apply K₀.toIntermediateField.val.injective
    let i := IntermediateField.inclusion h₀K
    change K.toIntermediateField.val (i ((AlgEquiv.restrictNormalHom K₀ (restriction K σ)) x)) =
      K₀.toIntermediateField.val (restriction K₀ σ x)
    rw [show i ((AlgEquiv.restrictNormalHom K₀ (restriction K σ)) x) = restriction K σ (i x) from
      AlgEquiv.restrictNormal_commutes (restriction K σ) K₀ x]
    exact (AlgEquiv.restrictNormalHom_apply K.toIntermediateField σ (i x)).trans
      (AlgEquiv.restrictNormalHom_apply K₀.toIntermediateField σ x).symm
  obtain ⟨L, hL, hLinner, hLdiagram⟩ := mark V n hn hbranch M Q₀ K hKu ωK hωK
  have hbranch' := hbranch.imp_right hLinner.mpr
  let aL σ := L.adjointPoint (aK σ)
  have haL (σ τ) : aL (σ * τ) = aL σ * L.coefficient σ (aL τ) := by
    dsimp only [aL]
    rw [haK, map_mul, L.coefficient_eq]
  obtain ⟨N⟩ := alcoveNormalFormAtLevel L hKu φ hφ hn hbranch' hd aL haL
  obtain ⟨b', hb'⟩ := inflateNormalForm a aK N b haKS
  refine ⟨K, vK, topK, locK, extK, h₀K, hKu, M, L, aK, N, hL, hLinner,
    hLdiagram, haK, ⟨b, haKS⟩, ⟨b', hb'⟩, ?_⟩
  have neutral (hr : ∀ σ, N.representative σ = 1) (T : Twist a) :
      Nonempty (V.model.val.val ≅ T.group.val) :=
    neutralTwist a T ⟨b', fun σ => by
      have h := hb' σ
      rw [hr, map_one, map_one] at h
      exact h⟩
  intro T
  constructor
  · intro ho
    obtain ⟨δ, k, _, _, hr⟩ := N.outer_correction (ho ∘ hLinner.mp)
    obtain ⟨i⟩ := neutral hr T
    exact ⟨⟨i.symm⟩, twist_isQuasiSplit_of_iso T i V.B V.borel⟩
  · intro hi ht
    have hr := representative_trivial_of_type N (hLinner.mpr hi) ht
    obtain ⟨i⟩ := neutral hr T
    obtain ⟨j⟩ := iso_of_fixed_trivialization P.pair.G V.model.val V.trivialization
      (fun σ => pinned_trivialization_fixed V σ (hi σ))
    exact ⟨⟨i.symm⟩, twist_isSplit_of_iso T P.pair (j ≪≫ i)⟩

end AbsoluteNormalForm

section ReferenceDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.RelativeFormComparison (fieldTest fieldMap IsInduced IsInducedByHopf)
open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.AdjointCocharacters (coordinateHopf coordinateHopfIso)
open Descent.Forms (spectrumIso)
open private descend_standard_iso standard extendedHom_comp extendedHom_id
  from LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso extendedSpecIso_natural extendedSpecIso_hom_fst
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private groundIso schemeIsoEquiv_ground schemeIsoEquiv_apply
  from LinearAlgebraicGroups.Descent.RelativeFormComparison

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem fixedRelativeIsoDescends {k S : Type u} [Field k] [Field S] [Algebra k S]
    [IsGalois k S] (G H : AffineAlgebraicGroup k)
    (j : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S))
    (hj : ∀ σ, restrictIso (fieldMap k S σ) j = j) :
    ∃ i : G.val ≅ H.val, groundIso (S := S) i = j := by
  let A := Specs.AdjointCocharacters.coordinateHopf G
  let B := Specs.AdjointCocharacters.coordinateHopf H
  let g := coordinateHopfIso G
  let h := coordinateHopfIso H
  let t := extendedGroupIso (k := k) S
  let F := groupBaseChange k S
  obtain ⟨e, he, hequiv⟩ := Descent.RelativeFormComparison.hopfIsomorphismComparison
    t (extendedSpecIso_hom_fst S) g h
  obtain ⟨q, hq⟩ := e.surjective j
  have hact : (standard S A).Equivariant (standard S B) q.hom := by
    intro σ x
    exact ((hequiv σ q q).mpr (by rw [hq, hj])) x
  obtain ⟨p, hp⟩ := descend_standard_iso q hact
  have hp_inv : extendedHopfMap S p.inv = q.inv := by
    apply (cancel_mono q.hom).mp
    rw [q.inv_hom_id, ← hp, ← extendedHom_comp, p.inv_hom_id, extendedHom_id]
  have hnat : (spectrumIso q).hom ≫ (t B).hom = (t A).hom ≫ F.map (spectrumIso p).hom := by
    apply Grp.hom_ext
    change (specGroupMap q.inv).hom.hom ≫ _ = _ ≫ (baseChange k S).map (specGroupMap p.inv).hom.hom
    rw [← hp_inv]
    exact extendedSpecIso_natural S p.inv
  let i := g.symm ≪≫ spectrumIso p ≪≫ h
  have hi : (t A ≪≫ F.mapIso g).symm ≪≫ spectrumIso q ≪≫ t B ≪≫ F.mapIso h = F.mapIso i := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Category.assoc]
    rw [reassoc_of% hnat, Iso.inv_hom_id_assoc]
    simp [i, Functor.map_comp]
  have hj' := (he q j).mpr hq
  change IsInduced k S _ j at hj'
  rw [hi] at hj'
  have hGround := schemeIsoEquiv_ground (S := S) i
  refine ⟨i, ?_⟩
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  apply Over.OverMorphism.ext
  rw [← hGround]
  exact (schemeIsoEquiv_apply (F.mapIso i) U.unop x).trans (hj' U.unop x).symm

private theorem additiveLine_eq {k : Type u} [Field k] (A B : RootGroups.AdditiveLine k) : A = B := by
  rcases A with ⟨a, hd, he, hs⟩
  rcases B with ⟨b, hd', he', hs'⟩
  have hd₀ : a.delta = b.delta := Polynomial.algHom_ext (hd.trans hd'.symm)
  have he₀ : a.epsilon = b.epsilon := Polynomial.algHom_ext (he.trans he'.symm)
  have hs₀ : a.inverse = b.inverse := Polynomial.algHom_ext (hs.trans hs'.symm)
  cases a
  cases b
  dsimp at hd₀ he₀ hs₀
  subst_vars
  rfl

open Specs.Pinning (PinnedGroup AttachedDatum PinnedIso BasedIso transportCharacter pinGraph)
open Specs.RationalRealization (Realization)
open Specs.IntegralSemisimpleModel (fibre splitTorus forgetFibrePoint)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence
open Classification.Pinning (inducedBasedIso)

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem groundReferenceMarking {F : Type u} [Field F]
    {B : BasedRootDatum.{u}} {M : Model B} (C : MarkedFibre M F)
    {P : PinnedGroup C.line} {D : AttachedDatum P.pair}
    (d : BasedIso D.toBased B) :
    let R : Realization B C.line := ⟨P, D, inv (show D.toBased ⟶ B from d)⟩
    ∃ p : PinnedIso C.realization.pinned P,
      inducedBasedIso p C.realization.attached D =
        Groupoid.inv (show B ⟶ C.realization.attached.toBased from C.realization.datumIso) ≫
          (show B ⟶ D.toBased from R.datumIso) ∧
      let j := C.groupIso ≪≫ p.group
      let s := C.torusIso ≪≫ p.torus
      (fibre F).map M.torus ≫ j.hom = s.hom ≫ P.pair.T.inclusion ∧
      (∀ (α : B.base.support) (U : TestAlgebra F) (z : U),
        forgetFibrePoint M.group U (RootGroups.rootPoint (R.rootMap α ≫ j.inv) U z) =
          M.line.point (integralRing U) z ≫ (M.root α.val).hom.hom) := by
  let R : Realization B C.line := ⟨P, D, inv (show D.toBased ⟶ B from d)⟩
  let e : BasedIso C.realization.attached.toBased D.toBased :=
    Groupoid.inv (show B ⟶ C.realization.attached.toBased from C.realization.datumIso) ≫
      (show B ⟶ D.toBased from R.datumIso)
  obtain ⟨p, hp⟩ := pinnedLift C.realization.pinned P C.realization.attached D e
  let j := C.groupIso ≪≫ p.group
  let s := C.torusIso ≪≫ p.torus
  refine ⟨p, hp, ?_, ?_⟩
  · change (fibre F).map M.torus ≫ (C.groupIso.hom ≫ p.group.hom) =
      (C.torusIso.hom ≫ p.torus.hom) ≫ P.pair.T.inclusion
    rw [← Category.assoc, C.torus_comm, Category.assoc, p.torus_comm, ← Category.assoc]
  · intro α U z
    let α₀ := C.realization.simpleRoot α
    have hlabel : transportCharacter p.torus α₀.val.val = (R.simpleRoot α).val.val := by
      have h₀ : transportCharacter p.torus α₀.val.val =
          ((inducedBasedIso p C.realization.attached D).val.indexEquiv α₀.val).val := rfl
      rw [h₀, hp]
      have hα : (e.val.indexEquiv α₀.val) = (R.simpleRoot α).val := by
        dsimp only [e, α₀, Realization.simpleRoot]
        change (R.datumIso.val.indexEquiv
          (C.realization.datumIso.val.indexEquiv.symm (C.realization.datumIso.val.indexEquiv α.val))) =
            R.datumIso.val.indexEquiv α.val
        rw [Equiv.symm_apply_apply]
      exact congrArg Subtype.val hα
    have hg : (transportCharacter p.torus α₀.val.val,
        C.realization.rootMap α ≫ p.group.hom) ∈ pinGraph P := by
      rw [← p.pin_comm]
      exact ⟨_, ⟨α₀, rfl⟩, rfl⟩
    obtain ⟨β, hβ⟩ := hg
    have hβlabel : β = R.simpleRoot α := by
      exact Subtype.ext (Subtype.ext ((congrArg Prod.fst hβ).trans hlabel))
    subst β
    have hmap : R.rootMap α = C.realization.rootMap α ≫ p.group.hom := congrArg Prod.snd hβ
    have hcomp : R.rootMap α ≫ j.inv = C.realization.rootMap α ≫ C.groupIso.inv := by
      simp [hmap, j, Category.assoc]
    change forgetFibrePoint M.group U (RootGroups.rootPoint (R.rootMap α ≫ j.inv) U z) = _
    rw [hcomp]
    have hx := C.root_eval α.val U z
    have hs := C.simple_eq α
    rw [hs] at hx
    unfold Realization.rootMap
    rw [Category.assoc]
    exact hx

end ReferenceDescent

section RelativeLevelComparison

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.Limits Opposite
open Specs.RelativeFormComparison (fieldTest fieldMap IsInduced)
open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private groundIso schemeIsoEquiv schemeIsoEquiv_apply schemeIsoEquiv_trans
  schemeIsoEquiv_ground from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private rebaseRelativeIso rebaseRelativeIso_fixed relativeBaseChange forgetFieldSlice
  forgetFieldPoints fieldTestIso from LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport
open private relativeSectionEquiv from LinearAlgebraicGroups.Descent.AutomorphismSequence

variable {F K S : Type u} [Field F] [Field K] [Field S]
  [Algebra F K] [Algebra K S] [Algebra F S] [IsScalarTower F K S]

private noncomputable abbrev coefficientInclusion : fieldTest F S ⟶ fieldTest F K :=
  (testSpec F).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom F K S)).op

private theorem fieldSpecTower : fieldSpecMap K S ≫ fieldSpecMap F K = fieldSpecMap F S := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (IsScalarTower.algebraMap_apply F K S x).symm

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem relativeIsoAtLevel [IsGalois K S]
    (G H : AffineAlgebraicGroup F)
    (j : relativePoints G.val (fieldTest F S) ≅ relativePoints H.val (fieldTest F S))
    (hj : ∀ σ : Gal(S/K), restrictIso (fieldMap F S (σ.restrictScalars F)) j = j) :
    ∃ i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val,
      restrictIso (coefficientInclusion (F := F) (K := K) (S := S))
        (schemeIsoEquiv K G.val H.val i) = j := by
  obtain ⟨i, hi⟩ := fixedRelativeIsoDescends (baseChangedAlgebraicGroup K G)
    (baseChangedAlgebraicGroup K H) (rebaseRelativeIso (K := K) j)
    (fun σ => rebaseRelativeIso_fixed j σ (hj σ))
  refine ⟨i, ?_⟩
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  let U' := U.unop
  let X : SchemeOver K := Over.mk (U'.hom.left ≫ fieldSpecMap K S)
  let v : X ⟶ fieldTest K S :=
    Over.homMk (show X.left ⟶ (fieldTest K S).left from U'.hom.left) (by rfl)
  let V : Over (fieldTest K S) := Over.mk v
  let W := (forgetFieldSlice (F := F) (K := K) (S := S)).obj V
  have hw : W.hom.left = U'.hom.left := Category.comp_id _
  let a₀ : W.left ⟶ U'.left := Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ U'.left.hom = (U'.hom.left ≫ fieldSpecMap K S) ≫ fieldSpecMap F K
    rw [Category.id_comp, Category.assoc, fieldSpecTower]
    exact (Over.w U'.hom).symm)
  let a : W ⟶ U' := Over.homMk a₀ (by
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ U'.hom.left = W.hom.left
    rw [Category.id_comp, hw])
  let T := (Over.map (coefficientInclusion (F := F) (K := K) (S := S))).obj U'
  let p : X ⟶ ((groupBaseChange F K).obj G.val).X :=
    (relativeSectionEquiv T G.val.X).symm x
  let g := forgetFieldPoints (F := F) (K := K) G.val X
  let h := forgetFieldPoints (F := F) (K := K) H.val X
  have hpr : g p = a₀ ≫ x := by
    apply Over.OverMorphism.ext
    change (pullback.lift x.left T.hom.left _) ≫ pullback.fst G.val.X.hom (fieldSpecMap F K) =
      𝟙 _ ≫ x.left
    rw [pullback.lift_fst, Category.id_comp]
  have he : h (p ≫ i.hom.hom.hom) = (j.hom.app (op W)).hom (g p) := by
    have hv := congrArg (fun e : relativePoints ((groupBaseChange F K).obj G.val) (fieldTest K S) ≅
        relativePoints ((groupBaseChange F K).obj H.val) (fieldTest K S) =>
      (e.hom.app (op V)).hom p) hi
    change p ≫ i.hom.hom.hom = h.symm ((j.hom.app (op W)).hom (g p)) at hv
    rw [hv, MulEquiv.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom (j.hom.naturality a.op) x
  change (j.hom.app (op W)).hom (a₀ ≫ x) = a₀ ≫ (j.hom.app U).hom x at hn
  have ha : ((schemeIsoEquiv K G.val H.val i).hom.app (op T)).hom x =
      (j.hom.app U).hom x := by
    apply Over.OverMorphism.ext
    rw [schemeIsoEquiv_apply (S := K) i T x]
    change (h (p ≫ i.hom.hom.hom)).left = _
    rw [he, hpr, hn]
    exact Category.id_comp _
  exact ha

end RelativeLevelComparison

section CentralQuotient

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open Specs.AutomorphismSequence (AdjointQuotient)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.IntegralSemisimpleModel (fibre)
open Specs.SchemeCentre (rootLattice)
open Specs.DiagonalizableGroups (groupAlgebra diagonalClosedInclusion)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (absoluteRoots)
open Specs.Pinning (SplitBorelPair AttachedDatum)
open Specs.Fppf (IsFppf)
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers

private theorem epi_of_flat_surjective_over {k : Type u} [Field k] {X Y : SchemeOver k}
    (f : X ⟶ Y) (hf : Flat f.left) (hs : Surjective f.left) : Epi f := by
  letI := hf
  letI := hs
  letI : Epi f.left := Flat.epi_of_flat_of_surjective f.left
  exact Over.epi_of_epi_left _

private theorem pullback_fst_epi {k : Type u} [Field k] {X Y U : SchemeOver k}
    (g : U ⟶ Y) (f : X ⟶ Y) (hf : Flat f.left) (hs : Surjective f.left) :
    Epi (pullback.fst g f) := by
  have hp := (IsPullback.of_hasPullback g f).map (Over.forget (Spec (CommRingCat.of k)))
  exact epi_of_flat_surjective_over _
    (MorphismProperty.of_isPullback (P := @Flat) hp.flip hf)
    (MorphismProperty.of_isPullback (P := @Surjective) hp.flip hs)

set_option backward.isDefEq.respectTransparency false in
private theorem centralizes_of_flat_surjective {k : Type u} [Field k] {G H : GroupScheme k}
    (f : G ⟶ H) (hf : Flat f.hom.hom.left) (hs : Surjective f.hom.hom.left)
    {U : SchemeOver k} {x : U ⟶ G.X} (hx : Centralizes (𝟙 G) x) :
    Centralizes (𝟙 H) (x ≫ f.hom.hom) := by
  rw [centralizes_iff] at hx ⊢
  intro V a y
  let q := f.hom.hom
  let P := pullback y q
  let p : P ⟶ V := pullback.fst y q
  let z : P ⟶ G.X := pullback.snd y q
  letI : Epi p := pullback_fst_epi y q hf hs
  have hy : z ≫ q = p ≫ y := (pullback.condition (f := y) (g := q)).symm
  have hc := (hx P (p ≫ a) z).map (IsMonHom.monoidHom q P)
  change Commute (((p ≫ a) ≫ x) ≫ q) ((z ≫ 𝟙 _) ≫ q) at hc
  simp only [Category.comp_id, Category.assoc, hy] at hc
  change Commute (a ≫ x ≫ q) (y ≫ 𝟙 _)
  rw [Category.comp_id]
  apply (cancel_epi p).mp
  simpa only [MonObj.comp_mul, Category.assoc] using hc.eq

private theorem fullRootLattice {k : Type u} [Field k] {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M k) (hD : D.datum.rootSpan ℤ = ⊤) :
    rootLattice C.realization.pinned.pair.T = ⊤ := by
  let E := C.realization.attached
  letI := E.comm
  let e := C.realization.datumIso.val
  have hm : Set.range E.datum.rootDatum.root = e.weightEquiv '' (Set.range D.datum.root) := by
    rw [← Set.range_comp]
    change _ = Set.range (e.weightMap ∘ D.datum.root)
    rw [e.root_weightMap, Set.range_comp, Set.range_eq_univ.mpr e.indexEquiv.surjective,
      Set.image_univ]
    rfl
  have hE : E.datum.rootDatum.rootSpan ℤ = ⊤ := by
    have hh := congrArg (Submodule.map e.weightEquiv.toLinearMap) hD
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr e.weightEquiv.surjective] at hh
    change Submodule.map e.weightEquiv.toLinearMap (Submodule.span ℤ (Set.range D.datum.root)) =
      ⊤ at hh
    rw [Submodule.map_span] at hh
    change Submodule.span ℤ (Set.range E.datum.rootDatum.root) = ⊤
    rw [hm]
    exact hh
  have hr : Set.range E.datum.rootDatum.root =
      Additive.toMul ⁻¹' absoluteRoots C.realization.pinned.pair.T := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [E.datum.root_eq]
      exact i.property
    · intro hx
      exact ⟨⟨Additive.toMul x, hx⟩, E.datum.root_eq _⟩
  have hsub : (rootLattice C.realization.pinned.pair.T).toAddSubgroup.toIntSubmodule =
      E.datum.rootDatum.rootSpan ℤ := by
    apply Submodule.toAddSubgroup_injective
    change (rootLattice C.realization.pinned.pair.T).toAddSubgroup = _
    rw [Submodule.span_int_eq_addSubgroupClosure, rootLattice,
      Subgroup.toAddSubgroup_closure, hr]
  apply top_unique
  intro χ _
  change Additive.ofMul χ ∈
    (rootLattice C.realization.pinned.pair.T).toAddSubgroup.toIntSubmodule
  rw [hsub, hE]
  exact Submodule.mem_top

set_option backward.isDefEq.respectTransparency false in
private theorem trivialCentre_of_fullRootLattice {k : Type u} [Field k]
    (P : SplitBorelPair k) (hP : rootLattice P.T = ⊤)
    {U : SchemeOver k} (x : U ⟶ P.G.val.X) (hx : Centralizes (𝟙 P.G.val) x) : x = 1 := by
  obtain ⟨_, e, _, h, hc, _⟩ :=
    RootData.SchemeCentre.schemeCentre P.G P.reductive P.T P.split P.maximal
  let A := groupAlgebra k (Character P.T.group ⧸ rootLattice P.T)
  let Z : ClosedSubgroup P.G.val :=
    ⟨specGroup A, diagonalClosedInclusion k (rootLattice P.T) ≫ e.hom ≫ P.T.inclusion, h⟩
  obtain ⟨z, hz⟩ := (hc U x).mp hx
  letI : Subsingleton (Character P.T.group ⧸ rootLattice P.T) := by
    rw [hP]
    exact QuotientGroup.subsingleton_quotient_top
  let q := MonoidAlgebra.uniqueAlgEquiv k (A := k)
    (Character P.T.group ⧸ rootLattice P.T)
  let j : Z.group.X ≅ (testSpec k).obj (op (CommAlgCat.of k k)) :=
    (testSpec k).mapIso (CommAlgCat.isoMk q).symm.op
  let j₀ : (testSpec k).obj (op (CommAlgCat.of k k)) ≅ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ 𝟙 _ = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  have ht : IsTerminal Z.group.X := Over.mkIdTerminal.ofIso (j ≪≫ j₀).symm
  have hz₀ : z = 1 := ht.hom_ext _ _
  rw [← hz, hz₀]
  exact MonObj.one_comp _

set_option backward.isDefEq.respectTransparency false in
private theorem markedAdjointQuotient {k : Type u} [Field k]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (C : MarkedFibre M k) (C' : MarkedFibre M' k)
    (hE : E.datum.rootSpan ℤ = ⊤) :
    ∃ (Q : AdjointQuotient C.realization.pinned.pair.G)
      (j : Q.quotient.val ≅ C'.realization.pinned.pair.G.val),
        Q.projection ≫ j.hom = C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom := by
  let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
  obtain ⟨⟨hfin, hflat, hsurj, _⟩, _, Z, hZ, _, hz⟩ := c.fibre k C C'
  have hcentre : RepresentsSubgroup Z (fun _ x => Centralizes (𝟙 _) x) := by
    intro U x
    constructor
    · intro hx
      have h := trivialCentre_of_fullRootLattice C'.realization.pinned.pair
        (fullRootLattice C' hE) (x ≫ f.hom.hom)
        (centralizes_of_flat_surjective f hflat hsurj hx)
      refine ⟨hZ.lift x (toUnit U) ?_, hZ.lift_fst _ _ _⟩
      exact h
    · rintro ⟨z, rfl⟩
      rw [centralizes_iff] at hz ⊢
      intro V a g
      simpa only [Category.assoc] using hz V (a ≫ z) g
  letI := hfin
  letI : LocallyOfFiniteType C'.realization.pinned.pair.G.val.X.hom :=
    C'.realization.pinned.pair.G.property.2.1
  letI : IsLocallyNoetherian C'.realization.pinned.pair.G.val.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian C'.realization.pinned.pair.G.val.X.hom
  exact ⟨⟨Z, hcentre, C'.realization.pinned.pair.G, f, ⟨hflat, hsurj, inferInstance⟩, hZ⟩,
    Iso.refl _, Category.comp_id _⟩

end CentralQuotient

section DiagramComparison

open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (BasedIso PinnedIso PinnedGroup AttachedDatum transportCharacter)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutation)
open Specs.RationalRealization (Realization)
open private cover_simple linearMap_ext_cover
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private basedIso_ext_weight from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private pinnedLift_character from LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

variable {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}

private theorem character_range (c : MarkedCentralCover M M') (hE : E.datum.rootSpan ℤ = ⊤) :
    c.pullCharacter.range = D.datum.rootSpan ℤ := by
  rw [← Submodule.map_top, ← hE]
  change Submodule.map c.pullCharacter (Submodule.span ℤ (Set.range E.datum.root)) =
    Submodule.span ℤ (Set.range D.datum.root)
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨c.rootEquiv.symm i, by rw [← c.roots, Equiv.apply_symm_apply]; rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨c.rootEquiv i, c.roots i⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_adjointBasedIso (c : MarkedCentralCover M M') (hE : E.datum.rootSpan ℤ = ⊤)
    (τ : BasedIso D D) :
    ∃ s : BasedIso E E,
      (∀ x, c.pullCharacter (s.val.weightEquiv x) = τ.val.weightEquiv (c.pullCharacter x)) ∧
      (∀ i, s.val.indexEquiv (c.rootEquiv i) = c.rootEquiv (τ.val.indexEquiv i)) := by
  let t := τ.val
  let R := c.pullCharacter.range
  have hR : R.map t.weightEquiv.toLinearMap = R := by
    dsimp only [R]
    rw [character_range c hE]
    change (Submodule.span ℤ (Set.range D.datum.root)).map t.weightMap =
      Submodule.span ℤ (Set.range D.datum.root)
    rw [Submodule.map_span, ← Set.range_comp, t.root_weightMap, Set.range_comp,
      Set.range_eq_univ.mpr t.indexEquiv.surjective, Set.image_univ]
  let j := LinearEquiv.ofInjective c.pullCharacter c.characterInjective
  let f := (j.trans (t.weightEquiv.ofSubmodules R R hR)).trans j.symm
  have hf (x : E.X) : c.pullCharacter (f x) = t.weightEquiv (c.pullCharacter x) := by
    exact congrArg Subtype.val (j.apply_symm_apply (t.weightEquiv.ofSubmodules R R hR (j x)))
  let v := c.rootEquiv.symm.trans (t.indexEquiv.trans c.rootEquiv)
  have hv (i : D.I) : v (c.rootEquiv i) = c.rootEquiv (t.indexEquiv i) := by
    simp [v]
  let g := E.datum.flip.toPerfPair.trans (f.dualMap.trans E.datum.flip.toPerfPair.symm)
  have hg (x : E.X) (y : E.Y) : E.datum.toLinearMap x (g y) = E.datum.toLinearMap (f x) y := by
    change (E.datum.flip.toPerfPair
      (E.datum.flip.toPerfPair.symm (f.dualMap (E.datum.flip.toPerfPair y)))) x = _
    rw [E.datum.flip.toPerfPair.apply_symm_apply]
    rfl
  let s : E.datum.Equiv E.datum :=
    { weightMap := f
      coweightMap := g
      indexEquiv := v
      weight_coweight_transpose := by ext y x; exact (hg x y).symm
      root_weightMap := by
        funext i
        obtain ⟨j, rfl⟩ := c.rootEquiv.surjective i
        change f (E.datum.root (c.rootEquiv j)) = E.datum.root (v (c.rootEquiv j))
        apply c.characterInjective
        rw [hf, hv, c.roots, c.roots]
        exact t.toHom.root_weightMap_apply _ _ _
      coroot_coweightMap := by
        funext i
        obtain ⟨i, rfl⟩ := v.surjective i
        change g (E.datum.coroot (v i)) = E.datum.coroot (v.symm (v i))
        rw [Equiv.symm_apply_apply]
        obtain ⟨j, rfl⟩ := c.rootEquiv.surjective i
        change g (E.datum.coroot (v (c.rootEquiv j))) = E.datum.coroot (c.rootEquiv j)
        apply E.datum.flip.toPerfPair.injective
        ext x
        change E.datum.toLinearMap x (g (E.datum.coroot (v (c.rootEquiv j)))) =
          E.datum.toLinearMap x (E.datum.coroot (c.rootEquiv j))
        rw [hg, hv, ← c.coroots, ← c.coroots, ← c.pairing, ← c.pairing, hf,
          t.toLinearMap_weightEquiv]
        have ht := t.toHom.coroot_coweightMap_apply D.datum D.datum (t.indexEquiv j)
        change t.coweightEquiv (D.datum.coroot (t.indexEquiv j)) =
          D.datum.coroot (t.indexEquiv.symm (t.indexEquiv j)) at ht
        rw [ht, Equiv.symm_apply_apply]
      bijective_weightMap := f.bijective
      bijective_coweightMap := g.bijective }
  refine ⟨⟨s, ?_⟩, hf, hv⟩
  have hbase (i : E.I) : i ∈ E.base.support ↔ c.rootEquiv.symm i ∈ D.base.support := by
    rw [cover_simple c, Equiv.apply_symm_apply]
  ext i
  change i ∈ v '' (E.base.support : Set E.I) ↔ i ∈ E.base.support
  rw [Set.mem_image_equiv]
  change v.symm i ∈ E.base.support ↔ i ∈ E.base.support
  rw [hbase, hbase]
  have hi : c.rootEquiv.symm (v.symm i) = t.indexEquiv.symm (c.rootEquiv.symm i) := by simp [v]
  rw [hi]
  change t.indexEquiv.symm (c.rootEquiv.symm i) ∈ (D.base.support : Set D.I) ↔
    c.rootEquiv.symm i ∈ (D.base.support : Set D.I)
  rw [← Set.mem_image_equiv, τ.property]

private noncomputable def adjointBasedIso (c : MarkedCentralCover M M')
    (hE : E.datum.rootSpan ℤ = ⊤) (τ : BasedIso D D) : BasedIso E E :=
  (exists_adjointBasedIso c hE τ).choose

private theorem adjointBasedIso_weight (c : MarkedCentralCover M M')
    (hE : E.datum.rootSpan ℤ = ⊤) (τ : BasedIso D D) (x : E.X) :
    c.pullCharacter ((adjointBasedIso c hE τ).val.weightEquiv x) =
      τ.val.weightEquiv (c.pullCharacter x) :=
  (exists_adjointBasedIso c hE τ).choose_spec.1 x

private theorem adjointBasedIso_index (c : MarkedCentralCover M M')
    (hE : E.datum.rootSpan ℤ = ⊤) (τ : BasedIso D D) (i : D.I) :
    (adjointBasedIso c hE τ).val.indexEquiv (c.rootEquiv i) = c.rootEquiv (τ.val.indexEquiv i) :=
  (exists_adjointBasedIso c hE τ).choose_spec.2 i

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adjointDiagram (c : MarkedCentralCover M M')
    (hE : E.datum.rootSpan ℤ = ⊤) : Aut D →* Aut E where
  toFun a := Aut.of ((Groupoid.isoEquivHom E E).symm (adjointBasedIso c hE a.asIso.hom))
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change adjointBasedIso c hE (𝟙 D) = (𝟙 E : E ⟶ E)
    apply basedIso_ext_weight
    intro x
    apply c.characterInjective
    exact adjointBasedIso_weight c hE (𝟙 D) x
  map_mul' a b := by
    apply Aut.ext
    apply Iso.ext
    change adjointBasedIso c hE (b.asIso.hom ≫ a.asIso.hom) =
      (adjointBasedIso c hE b.asIso.hom ≫ adjointBasedIso c hE a.asIso.hom : E ⟶ E)
    apply basedIso_ext_weight
    intro x
    apply c.characterInjective
    change c.pullCharacter ((adjointBasedIso c hE (b.asIso.hom ≫ a.asIso.hom)).val.weightEquiv x) =
      c.pullCharacter ((adjointBasedIso c hE a.asIso.hom).val.weightEquiv
        ((adjointBasedIso c hE b.asIso.hom).val.weightEquiv x))
    rw [adjointBasedIso_weight, adjointBasedIso_weight, adjointBasedIso_weight]
    rfl

private theorem adjointDiagram_injective (c : MarkedCentralCover M M')
    (hE : E.datum.rootSpan ℤ = ⊤) : Function.Injective (adjointDiagram c hE) := by
  intro a b hab
  have he : adjointBasedIso c hE a.asIso.hom = adjointBasedIso c hE b.asIso.hom :=
    congrArg (fun a : Aut E => a.asIso.hom) hab
  have hw := linearMap_ext_cover c a.asIso.hom.val.weightMap b.asIso.hom.val.weightMap (fun x =>
    (adjointBasedIso_weight c hE a.asIso.hom x).symm.trans
      ((congrArg (fun j : BasedIso E E => c.pullCharacter (j.val.weightEquiv x)) he).trans
        (adjointBasedIso_weight c hE b.asIso.hom x)))
  apply Aut.ext
  apply Iso.ext
  exact basedIso_ext_weight _ _ (fun x => LinearMap.congr_fun hw x)

set_option backward.isDefEq.respectTransparency false in
private theorem basedAutOfIso_index {D E : BasedRootDatum.{u}} (j : D ≅ E) (a : Aut D) (x : D.I) :
    (Aut.autMulEquivOfIso j a).asIso.hom.val.indexEquiv (j.hom.val.indexEquiv x) =
      j.hom.val.indexEquiv (a.asIso.hom.val.indexEquiv x) := by
  have h := congrArg (fun f : D ⟶ D => f.val.indexEquiv x) j.hom_inv_id
  change j.inv.val.indexEquiv (j.hom.val.indexEquiv x) = x at h
  change j.hom.val.indexEquiv (a.asIso.hom.val.indexEquiv
    (j.inv.val.indexEquiv (j.hom.val.indexEquiv x))) = _
  rw [h]

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedLift_comm {k : Type u} [Field k] {A : RootGroups.AdditiveLine k}
    {P P' : PinnedGroup A} {D : AttachedDatum P.pair} {D' : AttachedDatum P'.pair}
    {l : Aut D.toBased ≃* Aut P} {l' : Aut D'.toBased ≃* Aut P'}
    {Q : AdjointQuotient P.pair.G} {Q' : AdjointQuotient P'.pair.G}
    (h : SplitSequence P D l Q) (h' : SplitSequence P' D' l' Q')
    (p : PinnedIso P P') (a : Aut D'.toBased) :
    let e := (Groupoid.isoEquivHom D.toBased D'.toBased).symm
      (Classification.Pinning.inducedBasedIso p D D')
    let b := (Aut.autMulEquivOfIso e.symm) a
    (l b).asIso.hom.group.hom ≫ p.group.hom = p.group.hom ≫ (l' a).asIso.hom.group.hom := by
  intro e b
  let s := (l b).asIso.hom
  let s' := (l' a).asIso.hom
  have hp : s.trans p = p.trans s' := by
    apply Classification.PinnedUniqueness.pinnedIsoUniqueness
    intro χ
    change transportCharacter (s.torus ≪≫ p.torus) χ =
      transportCharacter (p.torus ≪≫ s'.torus) χ
    simp only [transportCharacter, Iso.trans_inv, Category.assoc]
    change transportCharacter p.torus (transportCharacter s.torus χ) =
      transportCharacter s'.torus (transportCharacter p.torus χ)
    change transportCharacter p.torus (transportCharacter (l b).asIso.hom.torus χ) =
      transportCharacter (l' a).asIso.hom.torus (transportCharacter p.torus χ)
    rw [pinnedLift_character h, pinnedLift_character h']
    change Additive.toMul (e.hom.val.weightEquiv (b.asIso.hom.val.weightEquiv (Additive.ofMul χ))) =
      Additive.toMul (a.asIso.hom.val.weightEquiv (e.hom.val.weightEquiv (Additive.ofMul χ)))
    change Additive.toMul (e.hom.val.weightEquiv (e.hom.val.weightEquiv.symm
      (a.asIso.hom.val.weightEquiv (e.hom.val.weightEquiv (Additive.ofMul χ))))) = _
    rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun p : PinnedIso P P' => p.group.hom) hp

end DiagramComparison

section RelativeActions

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.Limits Opposite
open Specs.RelativeFormComparison (fieldTest fieldMap)
open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.SteinbergPinnedDescent (comparisonOnPoints)
open Specs.AdjointRepresentation (GroupPoints)
open private groundIso schemeIsoEquiv schemeIsoEquiv_apply
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private relativeSectionEquiv relativeSection_natural relativeTest
  from LinearAlgebraicGroups.Descent.AutomorphismSequence
open Descent.NonabelianCohomology (pointAction)

variable {F : Type u} [Field F] {G H : GroupScheme F} {S : SchemeOver F}

private theorem relativeIso_naturality (i : relativePoints G S ≅ relativePoints H S)
    {U V : Over S} (f : V ⟶ U) (x : U.left ⟶ G.X) :
    (i.hom.app (op V)).hom (f.left ≫ x) = f.left ≫ (i.hom.app (op U)).hom x :=
  ConcreteCategory.congr_hom (i.hom.naturality f.op) x

set_option backward.isDefEq.respectTransparency false in
private theorem restrictRelativeIso_injective {S' : SchemeOver F} (e : S' ⟶ S)
    (he : Flat e.left) (hs : Surjective e.left)
    {i j : relativePoints G S ≅ relativePoints H S}
    (hij : restrictIso e i = restrictIso e j) : i = j := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  let V : Over S' := Over.mk (pullback.snd U.unop.hom e)
  let V' := (Over.map e).obj V
  let f : V' ⟶ U.unop := Over.homMk (pullback.fst U.unop.hom e) pullback.condition
  letI : Epi f.left := pullback_fst_epi U.unop.hom e he hs
  apply (cancel_epi f.left).mp
  rw [← relativeIso_naturality i f, ← relativeIso_naturality j f]
  exact congrArg (fun t : relativePoints G S' ≅ relativePoints H S' =>
    (t.hom.app (op V)).hom (f.left ≫ x)) hij

set_option backward.isDefEq.respectTransparency false in
private theorem relativeIso_eval {K : Type u} [Field K] [Algebra F K]
    (i : (groupBaseChange F K).obj G ≅ (groupBaseChange F K).obj H)
    (U : Over (fieldTest F K)) (x : relativeTest U ⟶ ((groupBaseChange F K).obj G).X) :
    ((schemeIsoEquiv K G H i).hom.app (op U)).hom (relativeSectionEquiv U G.X x) =
      relativeSectionEquiv U H.X (x ≫ i.hom.hom.hom) := by
  apply Over.OverMorphism.ext
  have h := schemeIsoEquiv_apply (S := K) i U (relativeSectionEquiv U G.X x)
  change _ = (relativeSectionEquiv U H.X
    ((relativeSectionEquiv U G.X).symm (relativeSectionEquiv U G.X x) ≫ i.hom.hom.hom)).left at h
  simpa only [Equiv.symm_apply_apply] using h

set_option backward.isDefEq.respectTransparency false in
private theorem relativeCentralSquare {K : Type u} [Field K] [Algebra F K]
    {G' H' : GroupScheme F} (p : G ⟶ G') (f : H ⟶ H')
    (i : (groupBaseChange F K).obj G ≅ (groupBaseChange F K).obj H)
    (j : (groupBaseChange F K).obj G' ≅ (groupBaseChange F K).obj H')
    (h : (groupBaseChange F K).map p ≫ j.hom = i.hom ≫ (groupBaseChange F K).map f) :
    ∀ (U : Over (fieldTest F K)) (x : U.left ⟶ G.X),
      ((schemeIsoEquiv K G' H' j).hom.app (op U)).hom (x ≫ p.hom.hom) =
        ((schemeIsoEquiv K G H i).hom.app (op U)).hom x ≫ f.hom.hom := by
  intro U x
  let y := (relativeSectionEquiv U G.X).symm x
  have hy : relativeSectionEquiv U G.X y = x := (relativeSectionEquiv U G.X).apply_symm_apply x
  rw [← hy, ← relativeSection_natural U p.hom.hom y, relativeIso_eval, relativeIso_eval,
    ← relativeSection_natural U f.hom.hom]
  apply congrArg (relativeSectionEquiv U H'.X)
  simp only [Category.assoc]
  exact congrArg (fun a : (groupBaseChange F K).obj G ⟶ (groupBaseChange F K).obj H' =>
    y ≫ a.hom.hom) h

set_option backward.isDefEq.respectTransparency false in
private theorem relativeIso_ext_of_cover {G' : GroupScheme F}
    (p : G' ⟶ G) (hp : Flat p.hom.hom.left) (hp' : Surjective p.hom.hom.left)
    {i j : relativePoints G S ≅ relativePoints H S}
    (h : ∀ (U : Over S) (x : U.left ⟶ G'.X),
      (i.hom.app (op U)).hom (x ≫ p.hom.hom) = (j.hom.app (op U)).hom (x ≫ p.hom.hom)) :
    i = j := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro y
  let q := p.hom.hom
  let v := pullback.fst y q
  let x := pullback.snd y q
  let V : Over S := Over.mk (v ≫ U.unop.hom)
  let f : V ⟶ U.unop := Over.homMk v rfl
  letI : Epi f.left := pullback_fst_epi y q hp hp'
  have he : f.left ≫ y = x ≫ p.hom.hom := pullback.condition
  apply (cancel_epi f.left).mp
  rw [← relativeIso_naturality i f, ← relativeIso_naturality j f, he]
  exact h V x

set_option backward.isDefEq.respectTransparency false in
private theorem adjointRelativeAction {K : Type u} [Field K] [Algebra F K] {G' H' : GroupScheme F}
    (p : G ⟶ G') (f : H ⟶ H') (hp : Flat p.hom.hom.left) (hp' : Surjective p.hom.hom.left)
    (i : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K))
    (j : relativePoints G' (fieldTest F K) ≅ relativePoints H' (fieldTest F K))
    (hi : ∀ (U : Over (fieldTest F K)) (x : U.left ⟶ G.X),
      (j.hom.app (op U)).hom (x ≫ p.hom.hom) = (i.hom.app (op U)).hom x ≫ f.hom.hom)
    (e : fieldTest F K ⟶ fieldTest F K) (s : H ≅ H) (t : H' ≅ H')
    (hs : f ≫ t.hom = s.hom ≫ f)
    (h : restrictIso e i = i ≪≫ groundIso s.symm) :
    restrictIso e j = j ≪≫ groundIso t.symm := by
  have hinv : s.inv ≫ f = f ≫ t.inv := by
    apply (cancel_mono t.hom).mp
    rw [Category.assoc, hs, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply relativeIso_ext_of_cover p hp hp'
  intro U x
  let V := (Over.map e).obj U
  have he := congrArg (fun r : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K) =>
    (r.hom.app (op U)).hom x) h
  change (i.hom.app (op V)).hom x = (i.hom.app (op U)).hom x ≫ s.inv.hom.hom at he
  change (j.hom.app (op V)).hom (x ≫ p.hom.hom) =
    (j.hom.app (op U)).hom (x ≫ p.hom.hom) ≫ t.inv.hom.hom
  rw [hi V, hi U, he, Category.assoc, Category.assoc]
  exact congrArg (fun a : H ⟶ H' => (i.hom.app (op U)).hom x ≫ a.hom.hom) hinv

set_option backward.isDefEq.respectTransparency false in
private theorem twistedEvaluation {K : Type u} [Field K] [Algebra F K]
    (i : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K))
    (σ : Gal(K/F)) (s : H ≅ H)
    (h : restrictIso (fieldMap F K σ) i = i ≪≫ groundIso s.symm)
    (x : GroupPoints G (CommAlgCat.of F K)) :
    comparisonOnPoints i (pointAction F K G.X σ x) =
      pointAction F K H.X σ (comparisonOnPoints i x) ≫ s.hom.hom.hom := by
  let U : Over (fieldTest F K) := Over.mk (𝟙 _)
  let V := (Over.map (fieldMap F K σ)).obj U
  let a : V ⟶ U := Over.homMk V.hom (Category.comp_id _)
  have ha := relativeIso_naturality i a x
  let y := pointAction F K G.X σ x
  have he := congrArg (fun r : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K) =>
    (r.hom.app (op U)).hom y) h
  change (i.hom.app (op V)).hom y = comparisonOnPoints i y ≫ s.inv.hom.hom at he
  have hn : a.left = fieldMap F K σ := Category.id_comp _
  change (i.hom.app (op V)).hom (a.left ≫ x) = a.left ≫ comparisonOnPoints i x at ha
  rw [hn] at ha
  change (i.hom.app (op V)).hom y =
    pointAction F K H.X σ (comparisonOnPoints i x) at ha
  apply (cancel_mono s.inv.hom.hom).mp
  have hz := congrArg (Grp.forget (SchemeOver F)).map s.hom_inv_id
  change s.hom.hom.hom ≫ s.inv.hom.hom = 𝟙 H.X at hz
  rw [← he, ha, Category.assoc, hz, Category.comp_id]

end RelativeActions

section PinnedLevelDescent

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.Limits Opposite
open Specs.RelativeFormComparison (fieldTest fieldMap transportedAut)
open Specs.AutomorphismSequence (relativePoints restrictIso scalarAut forgetPinning AdjointQuotient SplitSequence)
open Specs.Pinning (PinnedGroup AttachedDatum)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction pinnedSection
  basedAutTopology fieldGalTopology)
open Specs.SteinbergPinnedDescent (comparisonOnPoints)
open Specs.AdjointRepresentation (GroupPoints)
open Descent.NonabelianCohomology (Cocycle restriction pointMap)
open private groundIso schemeIsoEquiv schemeIsoEquiv_apply
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
attribute [local instance] basedAutTopology fieldGalTopology

variable {F : Type u} [Field F] {G H : GroupScheme F}

private theorem restrictRelativeIso_comp {T U V : SchemeOver F} (f : T ⟶ U) (g : U ⟶ V)
    (i : relativePoints G V ≅ relativePoints H V) :
    restrictIso f (restrictIso g i) = restrictIso (f ≫ g) i := by
  apply Iso.ext
  apply NatTrans.ext
  funext W
  apply GrpCat.ext
  intro x
  change W.unop.left ⟶ G.X at x
  let X := (Over.map g).obj ((Over.map f).obj W.unop)
  let Y := (Over.map (f ≫ g)).obj W.unop
  let a : X ⟶ Y := Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ (W.unop.hom ≫ f ≫ g) = (W.unop.hom ≫ f) ≫ g
    rw [Category.id_comp, Category.assoc])
  have h := relativeIso_naturality i a x
  change (i.hom.app (op X)).hom (𝟙 W.unop.left ≫ x) =
    𝟙 W.unop.left ≫ (i.hom.app (op Y)).hom x at h
  have hx : (𝟙 W.unop.left) ≫ x = x := Category.id_comp x
  have hy : (𝟙 W.unop.left) ≫ (i.hom.app (op Y)).hom x = (i.hom.app (op Y)).hom x :=
    Category.id_comp (show W.unop.left ⟶ H.X from (i.hom.app (op Y)).hom x)
  exact (congrArg (i.hom.app (op X)).hom hx).symm.trans (h.trans hy)

private theorem restrictRelativeIso_trans {T U : SchemeOver F} {J : GroupScheme F}
    (f : T ⟶ U) (i : relativePoints G U ≅ relativePoints H U)
    (j : relativePoints H U ≅ relativePoints J U) :
    restrictIso f (i ≪≫ j) = restrictIso f i ≪≫ restrictIso f j := by
  apply Iso.ext
  rfl

private theorem restrictRelativeIso_inverse {T : SchemeOver F} (f : T ⟶ T)
    (i : relativePoints G T ≅ relativePoints H T) (s : relativePoints G T ≅ relativePoints G T)
    (h : restrictIso f i ≪≫ i.symm = s) :
    restrictIso f i.symm = i.symm ≪≫ s.symm := by
  have h' : restrictIso f i = s ≪≫ i := calc
    restrictIso f i = (restrictIso f i ≪≫ i.symm) ≪≫ i := by
      rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    _ = s ≪≫ i := congrArg (fun j => j ≪≫ i) h
  apply Iso.ext
  exact congrArg Iso.inv h'

set_option backward.isDefEq.respectTransparency false in
private theorem restrictPinnedTrivialization
    {A : RootGroups.AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G} {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) D.toBased)}
    (V : PinnedRepresentative (S := SeparableClosure F) E ω)
    (σ : Gal(SeparableClosure F/F)) :
    restrictIso (fieldMap F (SeparableClosure F) σ) V.trivialization.symm =
      V.trivialization.symm ≪≫ groundIso (l (ω σ)).asIso.hom.group.symm := by
  let S := SeparableClosure F
  let T := fieldTest F S
  let G := P.pair.G.val
  let H := V.model.val.val
  let i : relativePoints G T ≅ relativePoints H T := V.trivialization
  let s : G ≅ G := (l (ω σ)).asIso.hom.group
  let f := Functor.mapAut P (forgetPinning (A := A)) (l (ω σ))
  have hsection : pinnedSection E (ω σ) = scalarAut f T :=
    E.sectionOnConstants _ _
  have h : transportedAut F S i σ = scalarAut f T := (V.transport_eq σ).trans hsection
  have hi : restrictIso (fieldMap F S σ) i ≪≫ i.symm = (scalarAut f T).asIso :=
    congrArg (fun a : Aut (relativePoints G T) => a.asIso) h
  have hg : (scalarAut f T).asIso = groundIso s := by
    apply Iso.ext
    rfl
  exact restrictRelativeIso_inverse (fieldMap F S σ) i (groundIso s) (hi.trans hg)

variable (K : FiniteGaloisIntermediateField F (SeparableClosure F))

private theorem coefficientInclusion_comm (σ : Gal(SeparableClosure F/F)) :
    coefficientInclusion (F := F) (K := K) (S := SeparableClosure F) ≫
        fieldMap F K (restriction K σ) =
      fieldMap F (SeparableClosure F) σ ≫ coefficientInclusion (F := F) (K := K) := by
  apply Over.OverMorphism.ext
  change fieldSpecMap K (SeparableClosure F) ≫ Spec.map (CommRingCat.ofHom (restriction K σ).toRingHom) =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ fieldSpecMap K (SeparableClosure F)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change algebraMap K (SeparableClosure F) (restriction K σ x) =
    σ (algebraMap K (SeparableClosure F) x)
  exact AlgEquiv.restrictNormalHom_apply K.toIntermediateField σ x

set_option maxHeartbeats 1300000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pinnedLevelIso
    {A : RootGroups.AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G} {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) D.toBased)}
    (V : PinnedRepresentative (S := SeparableClosure F) E ω)
    (ωK : Gal(K/F) →* Aut D.toBased) (hω : ∀ σ, ωK (restriction K σ) = ω σ) :
    ∃ i : (groupBaseChange F K).obj V.model.val.val ≅ (groupBaseChange F K).obj P.pair.G.val,
      let r := schemeIsoEquiv K V.model.val.val P.pair.G.val i
      restrictIso (coefficientInclusion (F := F) (K := K) (S := SeparableClosure F)) r =
        V.trivialization.symm ∧
      ∀ σ : Gal(K/F), restrictIso (fieldMap F K σ) r =
        r ≪≫ groundIso (l (ωK σ)).asIso.hom.group.symm := by
  let S := SeparableClosure F
  have hfix (τ : Gal(S/K)) : ω (τ.restrictScalars F) = 1 := by
    rw [← hω]
    have h : restriction K (τ.restrictScalars F) = 1 := by
      apply AlgEquiv.ext
      intro x
      apply K.toIntermediateField.val.injective
      exact (AlgEquiv.restrictNormalHom_apply K.toIntermediateField (τ.restrictScalars F) x).trans
        (τ.commutes x)
    rw [h, map_one]
  obtain ⟨i, hi⟩ := relativeIsoAtLevel V.model.val P.pair.G V.trivialization.symm (fun τ => by
    rw [restrictPinnedTrivialization V, hfix, map_one]
    exact Iso.trans_refl _)
  refine ⟨i, hi, ?_⟩
  intro σ
  obtain ⟨τ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S :
    Function.Surjective (restriction K)) σ
  let e := coefficientInclusion (F := F) (K := K) (S := S)
  have hflat : Flat e.left := inferInstanceAs (Flat (fieldSpecMap K S))
  have hsurj : Surjective e.left := by
    change Surjective (fieldSpecMap K S)
    exact ⟨fun y => ⟨IsLocalRing.closedPoint S, Subsingleton.elim _ _⟩⟩
  apply restrictRelativeIso_injective e hflat hsurj
  rw [restrictRelativeIso_comp, coefficientInclusion_comm, ← restrictRelativeIso_comp, hi,
    restrictPinnedTrivialization V, restrictRelativeIso_trans, hi, hω]
  apply Iso.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem relativeIso_baseChangePoint {K : Type u} [Field K] [Algebra F K]
    (i : (groupBaseChange F K).obj G ≅ (groupBaseChange F K).obj H)
    (x : GroupPoints ((groupBaseChange F K).obj G) (CommAlgCat.of K K)) :
    comparisonOnPoints (schemeIsoEquiv K G H i)
      (baseChangePoint F K G.X (CommAlgCat.of K K) x) =
        baseChangePoint F K H.X (CommAlgCat.of K K) (x ≫ i.hom.hom.hom) := by
  let U : Over (fieldTest F K) := Over.mk (𝟙 _)
  let k := Spec (CommRingCat.of K)
  let f := fieldSpecMap F K
  let x₀ : U.left ⟶ G.X := baseChangePoint F K G.X (CommAlgCat.of K K) x
  have ht : (fieldTest K K).hom = 𝟙 k := by
    change Spec.map (𝟙 (CommRingCat.of K)) = _
    exact Spec.map_id _
  have hx : x.left ≫ pullback.snd G.X.hom f = 𝟙 k := (Over.w x).trans ht
  have hc : x₀.left ≫ G.X.hom = (𝟙 k) ≫ f := by
    change (x.left ≫ pullback.fst G.X.hom f) ≫ G.X.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
  have hl : pullback.lift x₀.left (𝟙 k) hc = x.left := by
    apply pullback.hom_ext
    · exact pullback.lift_fst ..
    · rw [pullback.lift_snd, hx]
  have h := schemeIsoEquiv_apply (S := K) i U x₀
  apply Over.OverMorphism.ext
  change (((schemeIsoEquiv K G H i).hom.app (op U)).hom x₀).left =
    (x.left ≫ i.hom.hom.hom.left) ≫ pullback.fst H.X.hom f
  change _ = pullback.lift x₀.left (𝟙 k) hc ≫ i.hom.hom.hom.left ≫ pullback.fst H.X.hom f at h
  rw [hl] at h
  exact h.trans (Category.assoc _ _ _).symm

private theorem comparisonOnPoints_restrict {K S : Type u} [Field K] [Field S]
    [Algebra F K] [Algebra K S] [Algebra F S] [IsScalarTower F K S]
    (r : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K))
    (j : relativePoints G (fieldTest F S) ≅ relativePoints H (fieldTest F S))
    (hr : restrictIso (coefficientInclusion (F := F) (K := K) (S := S)) r = j)
    (x : GroupPoints G (CommAlgCat.of F K)) :
    pointMap F K H.X (IsScalarTower.toAlgHom F K S) (comparisonOnPoints r x) =
      comparisonOnPoints j (pointMap F K G.X (IsScalarTower.toAlgHom F K S) x) := by
  let U : Over (fieldTest F K) := Over.mk (𝟙 _)
  let W : Over (fieldTest F S) := Over.mk (𝟙 _)
  let e := coefficientInclusion (F := F) (K := K) (S := S)
  let V := (Over.map e).obj W
  let f : V ⟶ U := Over.homMk V.hom (Category.comp_id _)
  have h := relativeIso_naturality r f x
  have hf : f.left = e := Category.id_comp _
  rw [hf] at h
  have h' := congrArg (fun t : relativePoints G (fieldTest F S) ≅ relativePoints H (fieldTest F S) =>
    (t.hom.app (op W)).hom (e ≫ x)) hr
  exact h.symm.trans h'

end PinnedLevelDescent

section MarkedFibreTower

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open Specs.IntegralSemisimpleModel (fibre forgetFibrePoint)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.SteinbergPinnedDescent (comparisonOnPoints)
open Specs.RelativeFormComparison (fieldTest)
open Specs.AutomorphismSequence (AdjointQuotient relativePoints restrictIso)
open Descent.NonabelianCohomology (pointMap)
open private markedFibrePoint_natural from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private fibrePointEquiv forgetFibrePointEquiv from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private forgetFibrePoint_comp forgetFibrePoint_natural from
  LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private schemeIsoEquiv from LinearAlgebraicGroups.Descent.RelativeFormComparison

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}

set_option backward.isDefEq.respectTransparency false in
private theorem markedFibreAtLevel (C : MarkedFibre M F) (Ck : MarkedFibre M K) :
    ∃ j : (fibre K).obj M.group ≅ (groupBaseChange F K).obj C.realization.pinned.pair.G.val,
      ∀ (R : TestAlgebra K) (x : GroupPoints ((fibre K).obj M.group) R),
        markedFibrePoint C ((restrictTestAlgebra F K).obj R)
          (baseChangePoint F K C.realization.pinned.pair.G.val.X R (x ≫ j.hom.hom.hom)) =
            forgetFibrePoint M.group R x := by
  obtain ⟨j, hj⟩ := ExceptionalPinnedBaseChange.markedSplitGroupComparison C Ck
  refine ⟨Ck.groupIso ≪≫ j, ?_⟩
  intro R x
  change markedFibrePoint C ((restrictTestAlgebra F K).obj R)
      (baseChangePoint F K C.realization.pinned.pair.G.val.X R
        (x ≫ (Ck.groupIso.hom.hom.hom ≫ j.hom.hom.hom))) = _
  rw [← Category.assoc, hj]
  unfold markedFibrePoint
  have he := congrArg (Grp.forget (SchemeOver K)).map Ck.groupIso.hom_inv_id
  change Ck.groupIso.hom.hom.hom ≫ Ck.groupIso.inv.hom.hom = 𝟙 _ at he
  rw [Category.assoc, he, Category.comp_id]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem markedFibreAtLevel_central (c : MarkedCentralCover M M')
    (C : MarkedFibre M F) (C' : MarkedFibre M' F) (Ck : MarkedFibre M K)
    (j : (fibre K).obj M.group ≅ (groupBaseChange F K).obj C.realization.pinned.pair.G.val)
    (j' : (fibre K).obj M'.group ≅ (groupBaseChange F K).obj C'.realization.pinned.pair.G.val)
    (hj : ∀ (R : TestAlgebra K) (x : GroupPoints ((fibre K).obj M.group) R),
      markedFibrePoint C ((restrictTestAlgebra F K).obj R)
        (baseChangePoint F K C.realization.pinned.pair.G.val.X R (x ≫ j.hom.hom.hom)) =
          forgetFibrePoint M.group R x)
    (hj' : ∀ (R : TestAlgebra K) (x : GroupPoints ((fibre K).obj M'.group) R),
      markedFibrePoint C' ((restrictTestAlgebra F K).obj R)
        (baseChangePoint F K C'.realization.pinned.pair.G.val.X R (x ≫ j'.hom.hom.hom)) =
          forgetFibrePoint M'.group R x) :
    let f := C.groupIso.inv ≫ (fibre F).map c.map ≫ C'.groupIso.hom
    j.hom ≫ (groupBaseChange F K).map f = (fibre K).map c.map ≫ j'.hom := by
  intro f
  let G := (fibre K).obj M.group
  let H := (groupBaseChange F K).obj C'.realization.pinned.pair.G.val
  have hG : IsAffine G.X.left := by
    let i := Grp.forget (SchemeOver K) ⋙ Over.forget _
    letI : IsAffine (i.obj Ck.realization.pinned.pair.G.val) := Ck.realization.pinned.pair.G.property.1
    let e := i.mapIso Ck.groupIso
    exact isAffine_of_isAffineHom e.hom
  apply (groupHomComparison K G H hG).injective
  change (groupPointsFunctor K).map _ = (groupPointsFunctor K).map _
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  let RK := (restrictTestAlgebra F K).obj R
  apply (baseChangePointGroupEquiv K C'.realization.pinned.pair.G.val R).injective
  apply (fibrePointEquiv C' RK).injective
  change markedFibrePoint C' RK
      (baseChangePoint F K _ R ((x ≫ j.hom.hom.hom) ≫ ((groupBaseChange F K).map f).hom.hom)) =
    markedFibrePoint C' RK
      (baseChangePoint F K _ R ((x ≫ ((fibre K).map c.map).hom.hom) ≫ j'.hom.hom.hom))
  let z := x ≫ j.hom.hom.hom
  change markedFibrePoint C' RK
    (baseChangePoint F K _ R (z ≫ (baseChange F K).map f.hom.hom)) = _
  rw [baseChangePointsSchemeNaturality, markedFibrePoint_natural, hj, hj']
  exact (forgetFibrePoint_comp c.map R x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem markedFibrePoint_extend {S : Type u} [Field S] [Algebra F S]
    (C : MarkedFibre M F) (f : K →ₐ[F] S) (x : GroupPoints C.realization.pinned.pair.G.val
      (CommAlgCat.of F K)) :
    scalarPoints M f.toRingHom (markedFibrePoint C (CommAlgCat.of F K) x) =
      markedFibrePoint C (CommAlgCat.of F S) (pointMap F K _ f x) := by
  let R := CommAlgCat.of F K
  let T := CommAlgCat.of F S
  let g := CommAlgCat.ofHom f
  let y := x ≫ C.groupIso.inv.hom.hom
  change scalarPoints M f.toRingHom (forgetFibrePoint M.group R y) =
    forgetFibrePoint M.group T ((mapPoints g x) ≫ C.groupIso.inv.hom.hom)
  have hy : (mapPoints g x) ≫ C.groupIso.inv.hom.hom = mapPoints g y := Category.assoc ..
  rw [hy, forgetFibrePoint_natural]
  rfl

open ExceptionalUnramifiedCocycleSupport (baseChangeAdjointQuotient)
open private quotientIsoOfKernel centralizesIso from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private projection_eq_one_iff from LinearAlgebraicGroups.Descent.AutomorphismSequence

set_option backward.isDefEq.respectTransparency false in
private theorem adjointIsoAtLevel {G H : AffineAlgebraicGroup F}
    (Q : AdjointQuotient G) (Q' : AdjointQuotient H)
    (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val) :
    ∃ j : (groupBaseChange F K).obj Q.quotient.val ≅ (groupBaseChange F K).obj Q'.quotient.val,
      (groupBaseChange F K).map Q.projection ≫ j.hom =
        i.hom ≫ (groupBaseChange F K).map Q'.projection := by
  let QK := baseChangeAdjointQuotient K Q
  let QK' := baseChangeAdjointQuotient K Q'
  refine quotientIsoOfKernel QK.projection QK'.projection i QK.fppf QK'.fppf ?_
  intro U x
  rw [projection_eq_one_iff QK, projection_eq_one_iff QK']
  exact (Descent.AutomorphismSequence.innerAut_eq_one_iff x).trans
    ((centralizesIso i x).trans (Descent.AutomorphismSequence.innerAut_eq_one_iff _).symm)

end MarkedFibreTower

section LevelCoefficients

open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (BasedIso)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutation)
open Specs.ExceptionalSplitParahoricDescent (MarkedCoefficientAction)
open Specs.ExceptionalAffineRootSystems (alcoveStabilizer diagramCocharacters exceptionalCartan e6Partner)
open Specs.SteinbergPinnedDescent (e6Involution)
open private markedDiagramCharacter from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private basedIso_ext_weight from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private markedCoefficientAction_apply from LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

set_option backward.isDefEq.respectTransparency false in
private theorem e6_simple_permutation {D : BasedRootDatum.{u}} (b : Fin 6 ≃ D.base.support)
    (hb : ExceptionalNumbering D 6 b) (τ : BasedIso D D) :
    (∀ i, τ.val.indexEquiv (b i) = b i) ∨
      (∀ i, τ.val.indexEquiv (b i) = b (e6Partner i)) := by
  let s := simplePermutation D τ
  let q := (b.trans s).trans b.symm
  have hq (i : Fin 6) : (b (q i)).val = τ.val.indexEquiv (b i).val :=
    congrArg Subtype.val (b.apply_symm_apply (s (b i)))
  have hE := exceptionalCartan_eq 6 (Or.inl rfl)
  have hpair (i j : Fin 6) : CartanMatrix.E 6 (q i) (q j) = CartanMatrix.E 6 i j := by
    rw [← hE, ← hb.2, ← hb.2, hq i, hq j]
    exact τ.val.toHom.pairing
  rcases (SteinbergPinnedDescent.e6Diagram.1 q hpair) with h | h
  · left
    intro i
    simpa only [h, Equiv.Perm.one_apply] using (hq i).symm
  · right
    intro i
    have hh (i : Fin 6) : e6Involution i = e6Partner i := by fin_cases i <;> decide
    simpa only [h, hh] using (hq i).symm

private theorem basedAut_eq_one_of_simple {D : BasedRootDatum.{u}} (hD : D.datum.rootSpan ℤ = ⊤)
    (a : Aut D) (ha : ∀ i ∈ D.base.support, a.asIso.hom.val.indexEquiv i = i) : a = 1 := by
  apply Aut.ext
  apply Iso.ext
  apply basedIso_ext_weight
  have hspan : Submodule.span ℤ (D.datum.root '' (D.base.support : Set D.I)) = ⊤ :=
    D.base.span_root_support.trans hD
  have he : a.asIso.hom.val.weightEquiv.toLinearMap = LinearMap.id :=
    LinearMap.ext_on hspan (by
      rintro _ ⟨i, hi, rfl⟩
      change a.asIso.hom.val.weightMap (D.datum.root i) = D.datum.root i
      rw [a.asIso.hom.val.toHom.root_weightMap_apply _ _, ha i hi])
  exact LinearMap.congr_fun he

set_option backward.isDefEq.respectTransparency false in
private theorem diagramAffine_one (D : BasedRootDatum.{u}) :
    (diagramCocharacters (K := ℚ) ((1 : Aut D).asIso.hom.val)).toAffineEquiv = 1 := by
  have h : ((1 : Aut D).asIso.hom.val).coweightEquiv = LinearEquiv.refl ℤ D.Y := by
    ext y
    rfl
  unfold diagramCocharacters
  rw [h]
  apply AffineEquiv.ext
  intro x
  change (LinearMap.id : D.Y →ₗ[ℤ] D.Y).baseChange ℚ x = (1 : _ ≃ᵃ[ℚ] _) x
  rw [LinearMap.baseChange_id]
  rfl

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem levelCoefficientComparison (Y : SplitLevel K c p p' e)
    {n : ℕ} (b : Fin n ≃ D.base.support) (b' : Fin n ≃ E.base.support)
    (hb' : ExceptionalNumbering E n b') (hE : E.datum.rootSpan ℤ = ⊤)
    (hbb : ∀ i, c.rootEquiv (b i).val = (b' i).val)
    (C : MarkedFibre M F) (C' : MarkedFibre M' F)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    {Q' : AdjointQuotient C'.realization.pinned.pair.G}
    (hs : SplitSequence C.realization.pinned C.realization.attached l Q)
    (hs' : SplitSequence C'.realization.pinned C'.realization.attached l' Q')
    (ω : Gal(K/F) →* Aut C.realization.attached.toBased)
    (ω' : Gal(K/F) →* Aut C'.realization.attached.toBased)
    (hbranch : n = 6 ∨ ω' = 1)
    (hcompat : ∀ σ i, c.rootEquiv ((markedDiagramEquiv C.realization (ω σ)).asIso.hom.val.indexEquiv i) =
      (markedDiagramEquiv C'.realization (ω' σ)).asIso.hom.val.indexEquiv (c.rootEquiv i))
    (hscalar : Y.Coefficients (F := F))
    (houter : ∀ h : n = 6, Y.OuterE6Coefficients (h ▸ b) (h ▸ b') C C'
        (l := l) (l' := l') (Q := Q) (Q' := Q')) :
    ∃ (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
      (h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y))
      (β : Gal(K/F) →* MulAut (alcoveStabilizer (ApartmentRoots.split E.datum ℚ)
        ((ApartmentRoots.split E.datum ℚ).alcove p'))),
      MarkedCoefficientAction C' l' ω' ρ h ∧
      (∀ σ, AutomorphismComparison Y.ad (ρ σ) (h σ)) ∧
      (∀ σ, TypeQuotientTransport Y.typeQuotient Y.typeQuotient (ρ σ).toMonoidHom
        (β σ).toMonoidHom) ∧
      ∀ σ, (ω' σ = 1 → β σ = 1) ∧ (ω' σ ≠ 1 → ∀ z, β σ z = z⁻¹) := by
  let τ (σ : Gal(K/F)) := (markedDiagramEquiv C.realization (ω σ)).asIso.hom
  let τ' (σ : Gal(K/F)) := (markedDiagramEquiv C'.realization (ω' σ)).asIso.hom
  have hpin σ := markedDiagramCharacter C' hs' (ω' σ)
  by_cases htriv : ω' = 1
  · have ht (σ : Gal(K/F)) : ω' σ = 1 := congrArg (fun a : Gal(K/F) →* _ => a σ) htriv
    obtain ⟨_, a', _, ha', h⟩ := hscalar
    refine ⟨a', fun _ => 1, 1, ⟨?_, ?_, hpin⟩, fun σ => (h σ).2.1,
      fun σ => (h σ).2.2, fun σ => ⟨fun _ => rfl, fun hc => (hc (ht σ)).elim⟩⟩
    · intro σ v
      rw [ha', ht, map_one]
      change (ExceptionalAffineBruhat.markedCoefficientAction M' σ)
        (markedFibrePoint C' (CommAlgCat.of F K) v) =
          markedFibrePoint C' (CommAlgCat.of F K)
            ((testSpec F).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ v ≫ 𝟙 _)
      rw [Category.comp_id]
      exact markedCoefficientAction_apply C' σ v
    · intro σ
      rw [ht, map_one, diagramAffine_one]
  have h6 : n = 6 := hbranch.resolve_right htriv
  subst n
  have hcase (σ : Gal(K/F)) :
      (∀ i, (τ σ).val.indexEquiv (b i) = b i ∧ (τ' σ).val.indexEquiv (b' i) = b' i) ∨
      (∀ i, (τ σ).val.indexEquiv (b i) = b (e6Partner i) ∧
        (τ' σ).val.indexEquiv (b' i) = b' (e6Partner i)) := by
    rcases e6_simple_permutation b' hb' (τ' σ) with hi | hi
    · left
      intro i
      refine ⟨c.rootEquiv.injective ?_, hi i⟩
      rw [hcompat, hbb, hi]
    · right
      intro i
      refine ⟨c.rootEquiv.injective ?_, hi i⟩
      rw [hcompat, hbb, hi, hbb]
  obtain ⟨_, a', β, _, ha', h⟩ := houter rfl hs hs' ω ω' hcase
  refine ⟨a', fun σ => (diagramCocharacters (τ' σ).val).toAffineEquiv, β, ⟨ha', fun _ => rfl, hpin⟩,
    fun σ => (h σ).2.1, fun σ => (h σ).2.2.1, ?_⟩
  intro σ
  constructor
  · intro hσ
    have he : (diagramCocharacters (K := ℚ) (τ' σ).val).toAffineEquiv = 1 := by
      dsimp only [τ']
      rw [hσ, map_one, diagramAffine_one]
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change (β σ z).val.val = z.val.val
    have hz := (h σ).2.2.2.1 z
    change (β σ z).val.val = (diagramCocharacters (K := ℚ) (τ' σ).val).toAffineEquiv * z.val.val *
      (diagramCocharacters (K := ℚ) (τ' σ).val).toAffineEquiv⁻¹ at hz
    simpa only [he, inv_one, one_mul, mul_one] using hz
  · intro hσ
    rcases hcase σ with hfix | hmove
    · have he : markedDiagramEquiv C'.realization (ω' σ) = 1 := by
        apply basedAut_eq_one_of_simple hE
        intro i hi
        obtain ⟨j, hj⟩ := b'.surjective ⟨i, hi⟩
        exact (congrArg (fun j : E.I => (τ' σ).val.indexEquiv j) (congrArg Subtype.val hj)).symm.trans
          ((hfix j).2.trans (congrArg Subtype.val hj))
      apply (hσ ((markedDiagramEquiv C'.realization).injective (he.trans
        (map_one (markedDiagramEquiv C'.realization)).symm))).elim
    · exact (h σ).2.2.2.2 (fun i => (hmove i).2)

end LevelCoefficients

section MarkedPointActions

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.RelativeFormComparison (fieldTest fieldMap)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.SteinbergPinnedDescent (comparisonOnPoints)
open Specs.IntegralSemisimpleModel (fibre forgetFibrePoint)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open Descent.NonabelianCohomology (pointAction pointMap)
open private groundIso schemeIsoEquiv restrict_ground from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private fibrePointEquiv from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

local notation "CohPoints" => Descent.NonabelianCohomology.Points

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {E : BasedRootDatum.{u}} {M : Model E} (C : MarkedFibre M F)
  {G : GroupScheme F}

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem markedAdjointPoints
    (j : (fibre K).obj M.group ≅ (groupBaseChange F K).obj C.realization.pinned.pair.G.val)
    (hj : ∀ (R : TestAlgebra K) (x : GroupPoints ((fibre K).obj M.group) R),
      markedFibrePoint C ((restrictTestAlgebra F K).obj R)
        (baseChangePoint F K C.realization.pinned.pair.G.val.X R (x ≫ j.hom.hom.hom)) =
          forgetFibrePoint M.group R x)
    (d : (groupBaseChange F K).obj G ≅ (groupBaseChange F K).obj C.realization.pinned.pair.G.val)
    (ρ : Gal(K/F) →* MulAut (FieldPoints M K))
    (σpin : Gal(K/F) → Aut C.realization.pinned)
    (hρ : ∀ σ v, ρ σ (markedFibrePoint C (CommAlgCat.of F K) v) =
      pinnedCoefficientPoint C (σpin σ) σ v)
    (h : ∀ σ, let i := schemeIsoEquiv K G C.realization.pinned.pair.G.val d
      restrictIso (fieldMap F K σ) i = i ≪≫ groundIso (σpin σ).asIso.hom.group.symm) :
    ∃ e : CohPoints F K G.X ≃* FieldPoints M K,
      (∀ (x : GroupPoints ((groupBaseChange F K).obj G) (CommAlgCat.of K K)),
        e (baseChangePoint F K G.X (CommAlgCat.of K K) x) =
          forgetFibrePoint M.group (CommAlgCat.of K K) (x ≫ (d ≪≫ j.symm).hom.hom.hom)) ∧
      ∀ σ x, e (pointAction F K G.X σ x) = ρ σ (e x) := by
  let H := C.realization.pinned.pair.G.val
  let i := schemeIsoEquiv K G H d
  let R := CommAlgCat.of K K
  let e := (comparisonOnPoints i).trans (fibrePointEquiv C (CommAlgCat.of F K))
  refine ⟨e, ?_, ?_⟩
  · intro x
    change markedFibrePoint C (CommAlgCat.of F K)
      (comparisonOnPoints i (baseChangePoint F K G.X R x)) = _
    rw [relativeIso_baseChangePoint d x]
    let y := x ≫ (d ≪≫ j.symm).hom.hom.hom
    have hy : y ≫ j.hom.hom.hom = x ≫ d.hom.hom.hom := by
      have he := congrArg (Grp.forget (SchemeOver K)).map j.inv_hom_id
      change j.inv.hom.hom ≫ j.hom.hom.hom = 𝟙 _ at he
      change (x ≫ d.hom.hom.hom ≫ j.inv.hom.hom) ≫ j.hom.hom.hom = _
      simp only [Category.assoc, he, Category.comp_id]
    exact (congrArg (fun u => markedFibrePoint C (CommAlgCat.of F K)
      (baseChangePoint F K H.X R u)) hy).symm.trans (hj R y)
  · intro σ x
    change markedFibrePoint C (CommAlgCat.of F K)
      (comparisonOnPoints i (pointAction F K G.X σ x)) =
        ρ σ (markedFibrePoint C (CommAlgCat.of F K) (comparisonOnPoints i x))
    rw [hρ, twistedEvaluation i σ _ (h σ)]
    rfl

set_option maxHeartbeats 1300000 in
set_option backward.isDefEq.respectTransparency false in
private theorem referencePointsAtLevel {H : GroupScheme F} {S : Type u} [Field S]
    [Algebra F S] [Algebra K S] [IsScalarTower F K S]
    (p : C.realization.pinned.pair.G.val ≅ H)
    (i : (groupBaseChange F K).obj G ≅ (groupBaseChange F K).obj H)
    (j : (fibre K).obj M.group ≅ (groupBaseChange F K).obj C.realization.pinned.pair.G.val)
    (hj : ∀ (R : TestAlgebra K) (x : GroupPoints ((fibre K).obj M.group) R),
      markedFibrePoint C ((restrictTestAlgebra F K).obj R)
        (baseChangePoint F K C.realization.pinned.pair.G.val.X R (x ≫ j.hom.hom.hom)) =
          forgetFibrePoint M.group R x)
    (r : relativePoints G (fieldTest F S) ≅ relativePoints H (fieldTest F S))
    (hr : restrictIso (coefficientInclusion (F := F) (K := K) (S := S))
      (schemeIsoEquiv K G H i) = r)
    (x : GroupPoints ((groupBaseChange F K).obj G) (CommAlgCat.of K K)) :
    let f := IsScalarTower.toAlgHom F K S
    let J := i ≪≫ (groupBaseChange F K).mapIso p.symm ≪≫ j.symm
    scalarPoints M f.toRingHom
      (forgetFibrePoint M.group (CommAlgCat.of K K) (x ≫ J.hom.hom.hom)) =
        forgetFibrePoint M.group (CommAlgCat.of F S)
          (comparisonOnPoints r (pointMap F K G.X f
            (baseChangePoint F K G.X (CommAlgCat.of K K) x)) ≫ (C.groupIso ≪≫ p).inv.hom.hom) := by
  intro f J
  let R := CommAlgCat.of K K
  let Y := C.realization.pinned.pair.G.val
  let b := groupBaseChange F K
  let y := x ≫ J.hom.hom.hom
  have he : y ≫ j.hom.hom.hom =
      (x ≫ i.hom.hom.hom) ≫ (b.map p.inv).hom.hom := by
    have h := congrArg (Grp.forget (SchemeOver K)).map j.inv_hom_id
    change j.inv.hom.hom ≫ j.hom.hom.hom = 𝟙 _ at h
    change (x ≫ (i.hom.hom.hom ≫ (b.map p.inv).hom.hom ≫ j.inv.hom.hom)) ≫ j.hom.hom.hom = _
    simp only [Category.assoc, h]
    have h₀ : (b.map p.inv).hom.hom ≫ 𝟙 ((b.obj Y).X) = (b.map p.inv).hom.hom :=
      Category.comp_id _
    rw [h₀]
  rw [← hj R y, he]
  change scalarPoints M f.toRingHom (markedFibrePoint C (CommAlgCat.of F K)
    (baseChangePoint F K Y.X R ((x ≫ i.hom.hom.hom) ≫ (baseChange F K).map p.inv.hom.hom))) = _
  rw [baseChangePointsSchemeNaturality, markedFibrePoint_extend]
  have hn : pointMap F K Y.X f
      (baseChangePoint F K H.X R (x ≫ i.hom.hom.hom) ≫ p.inv.hom.hom) =
    pointMap F K H.X f (baseChangePoint F K H.X R (x ≫ i.hom.hom.hom)) ≫ p.inv.hom.hom := by
    let u := (testSpec F).map (CommAlgCat.ofHom f).op
    let v := baseChangePoint F K H.X R (x ≫ i.hom.hom.hom)
    change u ≫ (v ≫ p.inv.hom.hom) = (u ≫ v) ≫ p.inv.hom.hom
    exact (Category.assoc _ _ _).symm
  rw [hn, ← relativeIso_baseChangePoint i x, comparisonOnPoints_restrict _ _ hr]
  change forgetFibrePoint M.group (CommAlgCat.of F S)
      ((_ ≫ p.inv.hom.hom) ≫ C.groupIso.inv.hom.hom) =
    forgetFibrePoint M.group (CommAlgCat.of F S) (_ ≫ (p.inv.hom.hom ≫ C.groupIso.inv.hom.hom))
  rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem transportGroundAction {H J : GroupScheme F}
    (r : relativePoints H (fieldTest F K) ≅ relativePoints J (fieldTest F K))
    (p : G ≅ J) (s : G ≅ G) (t : J ≅ J) (σ : Gal(K/F))
    (hp : s.hom ≫ p.hom = p.hom ≫ t.hom)
    (hr : restrictIso (fieldMap F K σ) r = r ≪≫ groundIso t.symm) :
    restrictIso (fieldMap F K σ) (r ≪≫ groundIso p.symm) =
      (r ≪≫ groundIso p.symm) ≪≫ groundIso s.symm := by
  rw [restrictRelativeIso_trans, restrict_ground, hr, Iso.trans_assoc, Iso.trans_assoc]
  apply congrArg (r ≪≫ ·)
  let Z := fieldTest F K
  let F₀ := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget Z).op
  change F₀.mapIso t.symm ≪≫ F₀.mapIso p.symm = F₀.mapIso p.symm ≪≫ F₀.mapIso s.symm
  have h₀ : s ≪≫ p = p ≪≫ t := Iso.ext hp
  have he : (p ≪≫ t).symm = (s ≪≫ p).symm :=
    congrArg (fun i : G ≅ J => i.symm) h₀.symm
  apply Iso.ext
  change F₀.map t.inv ≫ F₀.map p.inv = F₀.map p.inv ≫ F₀.map s.inv
  rw [← F₀.map_comp, ← F₀.map_comp]
  exact congrArg (F₀.map) (congrArg (fun i : J ≅ G => i.hom) he)

end MarkedPointActions

section UnramifiedLevelAssembly

open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (PinnedGroup AttachedDatum BasedIso)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence restrictIso)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction basedAutTopology fieldGalTopology)
open Specs.RelativeFormComparison (fieldTest fieldMap)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Specs.IntegralSemisimpleModel (fibre)
open Specs.SteinbergPinnedDescent (comparisonOnPoints)
open Specs.ExceptionalStableAlcoveRepresentatives
open ExceptionalStableAlcoveRepresentatives (markedAlcoveCoefficientComparison)
open Descent.NonabelianCohomology (Cocycle restriction)
open private splitSequenceForAttached from LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange
open private centralCover_diagramEquivariant
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private groundIso schemeIsoEquiv schemeIsoEquiv_trans schemeIsoEquiv_ground
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
attribute [local instance] basedAutTopology fieldGalTopology

private theorem conjugateAut_trans {D E H : BasedRootDatum.{u}}
    (i : D ≅ E) (j : E ≅ H) (a : Aut D) :
    Aut.autMulEquivOfIso j (Aut.autMulEquivOfIso i a) =
      Aut.autMulEquivOfIso (i ≪≫ j) a := by
  apply Aut.ext
  apply Iso.ext
  change j.inv ≫ (i.inv ≫ a.asIso.hom ≫ i.hom) ≫ j.hom =
    (j.inv ≫ i.inv) ≫ a.asIso.hom ≫ (i.hom ≫ j.hom)
  simp only [Category.assoc]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem unramifiedMarkedLevels : UnramifiedMarkedLevels.{u} := by
  intro F _ _ _ _ A P D l Q E ω V n hn hbranch M Q₀ K _ _ _ _ hu ωK hω
  obtain ⟨p, p', e, X, BX, he, hp, hlevels⟩ := markedAlcoveCoefficientComparison F
    M.cover n M.scNumbering M.adNumbering hn M.scNumbering_eq M.adNumbering_eq M.corootSpan M.rootSpan
  obtain ⟨Y, BY, hscalar, htypes, horder, hcoef, houter⟩ := hlevels K hu
  obtain ⟨⟨line, pC, jC, sC, zC, htC, hsC, hteC, hreC⟩⟩ :=
    ExceptionalMarkedRootDescent.markedFibreExists M.scModel F
  have hA : A = line := additiveLine_eq _ _
  subst A
  let C : MarkedFibre M.scModel F := ⟨line, pC, jC, sC, zC, htC, hsC, hteC, hreC⟩
  let C' := X.ad_fibre
  obtain ⟨j, hj, ht, hr⟩ := groundReferenceMarking C M.datum
  obtain ⟨l₁, Q₁, ⟨E₁⟩⟩ := splitSequenceForAttached C.realization.pinned C.realization.attached
  obtain ⟨l₂, Q₂, ⟨E₂⟩⟩ := splitSequenceForAttached C'.realization.pinned C'.realization.attached
  let jD := (Groupoid.isoEquivHom C.realization.attached.toBased D.toBased).symm
    (Classification.Pinning.inducedBasedIso j C.realization.attached D)
  let u := (Groupoid.isoEquivHom M.scDatum C.realization.attached.toBased).symm C.realization.datumIso
  let v := (Groupoid.isoEquivHom D.toBased M.scDatum).symm M.datum
  have hD : jD = u.symm ≪≫ v.symm := by
    apply Iso.ext
    change (Classification.Pinning.inducedBasedIso j C.realization.attached D) =
      Groupoid.inv (show M.scDatum ⟶ C.realization.attached.toBased from C.realization.datumIso) ≫
        Groupoid.inv (show D.toBased ⟶ M.scDatum from M.datum)
    rw [hj, Groupoid.inv_eq_inv (show D.toBased ⟶ M.scDatum from M.datum)]
  have hdsc : jD.symm ≪≫ u.symm = v := by
    rw [hD]
    change (v ≪≫ u) ≪≫ u.symm = v
    rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  let A₁ := Aut.autMulEquivOfIso jD.symm
  let A₂ := markedDiagramEquiv C.realization
  let A₃ := adjointDiagram M.cover M.rootSpan
  let A₄ := markedDiagramEquiv C'.realization
  let g := A₄.symm.toMonoidHom.comp (A₃.comp (A₂.toMonoidHom.comp A₁.toMonoidHom))
  let ω₁ := A₁.toMonoidHom.comp ωK
  let ω₂ := g.comp ωK
  have hcomp (σ : Gal(K/F)) : A₄ (ω₂ σ) = A₃ (A₂ (ω₁ σ)) :=
    A₄.apply_symm_apply _
  have hroot (σ : Gal(K/F)) (i : M.scDatum.I) :
      M.cover.rootEquiv ((A₂ (ω₁ σ)).asIso.hom.val.indexEquiv i) =
        (A₄ (ω₂ σ)).asIso.hom.val.indexEquiv (M.cover.rootEquiv i) := by
    rw [hcomp]
    exact (adjointBasedIso_index M.cover M.rootSpan (A₂ (ω₁ σ)).asIso.hom i).symm
  have hinj : Function.Injective g :=
    A₄.symm.injective.comp ((adjointDiagram_injective M.cover M.rootSpan).comp
      (A₂.injective.comp A₁.injective))
  have hinner : ω₂ = 1 ↔ ∀ σ, ω σ = 1 := by
    constructor
    · intro h σ
      have hg : g (ωK (restriction K σ)) = g 1 := by
        change ω₂ (restriction K σ) = g 1
        rw [h, map_one]
        rfl
      exact (hω σ).symm.trans (hinj hg)
    · intro h
      apply MonoidHom.ext
      intro σ
      obtain ⟨τ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective (SeparableClosure F) :
        Function.Surjective (restriction K)) σ
      change g (ωK (restriction K τ)) = 1
      rw [hω, h, map_one]
  have hlabel (σ : Gal(SeparableClosure F/F)) (i : D.toBased.I) :
      (A₄ (ω₂ (restriction K σ))).asIso.hom.val.indexEquiv
          (M.cover.rootEquiv (M.datum.val.indexEquiv i)) =
        M.cover.rootEquiv (M.datum.val.indexEquiv ((ω σ).asIso.hom.val.indexEquiv i)) := by
    rw [← hroot]
    have hs : A₂ (ω₁ (restriction K σ)) = Aut.autMulEquivOfIso v (ω σ) := by
      change Aut.autMulEquivOfIso u.symm
        (Aut.autMulEquivOfIso jD.symm (ωK (restriction K σ))) = _
      rw [conjugateAut_trans, hdsc, hω]
    rw [hs]
    exact congrArg M.cover.rootEquiv (basedAutOfIso_index v (ω σ) i)
  obtain ⟨ρ, a, β, hmarked, haff, htype, haction⟩ := levelCoefficientComparison Y
    M.scNumbering M.adNumbering M.adNumbering_eq M.rootSpan M.numbering_comm C C' E₁ E₂ ω₁ ω₂
    (hbranch.imp_right hinner.mpr) hroot hcoef (fun h => houter h C C' l₁ l₂ Q₁ Q₂)
  obtain ⟨i, hi, hia⟩ := pinnedLevelIso K V ωK hω
  let b := groupBaseChange F K
  let i₁ := i ≪≫ b.mapIso j.group.symm
  let G := V.model.val.val
  let H := C.realization.pinned.pair.G.val
  let H' := C'.realization.pinned.pair.G.val
  let q := C.groupIso.inv ≫ (fibre F).map M.cover.map ≫ C'.groupIso.hom
  obtain ⟨Qm, m, hm⟩ := markedAdjointQuotient M.cover C C' M.rootSpan
  obtain ⟨d₀, hd₀⟩ := adjointIsoAtLevel Q₀ Qm i₁
  let d := d₀ ≪≫ b.mapIso m
  have hd : b.map Q₀.projection ≫ d.hom = i₁.hom ≫ b.map q := by
    change b.map Q₀.projection ≫ (d₀.hom ≫ b.map m.hom) = _
    rw [← Category.assoc, hd₀, Category.assoc, ← Functor.map_comp, hm]
  have hi₁ (σ : Gal(K/F)) :
      let r := schemeIsoEquiv K G H i₁
      restrictIso (fieldMap F K σ) r = r ≪≫ groundIso (l₁ (ω₁ σ)).asIso.hom.group.symm := by
    dsimp only [i₁]
    rw [schemeIsoEquiv_trans, schemeIsoEquiv_ground]
    exact transportGroundAction _ j.group _ _ σ
      (pinnedLift_comm E₁ E j (ωK σ)) (hia σ)
  have hda (σ : Gal(K/F)) :
      let r := schemeIsoEquiv K Q₀.quotient.val H' d
      restrictIso (fieldMap F K σ) r = r ≪≫ groundIso (l₂ (ω₂ σ)).asIso.hom.group.symm := by
    apply adjointRelativeAction Q₀.projection q Q₀.fppf.1 Q₀.fppf.2.1 (schemeIsoEquiv K G H i₁)
      _ (relativeCentralSquare Q₀.projection q i₁ d hd)
    · exact centralCover_diagramEquivariant M.cover M.rootSpan C C' E₁ E₂ (ω₁ σ) (ω₂ σ) (hroot σ)
    · exact hi₁ σ
  obtain ⟨f, hf⟩ := markedFibreAtLevel C Y.sc_fibre
  obtain ⟨f', hf'⟩ := markedFibreAtLevel C' Y.ad_fibre
  let ref := i₁ ≪≫ f.symm
  let adj := d ≪≫ f'.symm
  have hproj : b.map Q₀.projection ≫ adj.hom = ref.hom ≫ (fibre K).map M.cover.map := by
    apply (cancel_mono f'.hom).mp
    change (b.map Q₀.projection ≫ (d.hom ≫ f'.inv)) ≫ f'.hom =
      ((i₁.hom ≫ f.inv) ≫ (fibre K).map M.cover.map) ≫ f'.hom
    rw [Category.assoc, Category.assoc, f'.inv_hom_id, Category.comp_id, hd]
    simp only [Category.assoc]
    rw [← markedFibreAtLevel_central M.cover C C' Y.sc_fibre f f' hf hf', Iso.inv_hom_id_assoc]
  obtain ⟨point, hpoint, hpeq⟩ := markedAdjointPoints C' f' hf' d ρ (fun σ => l₂ (ω₂ σ)) hmarked.1 hda
  let L : MarkedUnramifiedLevel (K := K) M Q₀ :=
    { p := p
      p' := p'
      apartments := e
      apartments_eq := he
      p_eq := hp
      base := X
      baseBuilding := BX
      level := Y
      building := BY
      scalar := hscalar
      scalar_types := htypes
      referenceIso := ref
      adjointIso := adj
      central_comm := hproj
      adjointPoint := point
      adjointPoint_eq := hpoint
      marking := C'
      pinned := l₂
      diagram := ω₂
      coefficient := ρ
      affineAction := a
      typeAction := β
      markedCoefficient := hmarked
      coefficient_eq := hpeq
      affine_comparison := haff
      type_comparison := htype
      type_action_eq := haction
      type_order := horder }
  refine ⟨L, ?_, hinner, hlabel⟩
  refine ⟨C.groupIso ≪≫ j.group, C.torusIso ≪≫ j.torus, ht, hr, ?_⟩
  intro x
  have hx := referencePointsAtLevel C j.group i f hf V.trivialization.symm hi x
  change scalarPoints M.scModel K.toIntermediateField.val.toRingHom
    (Specs.IntegralSemisimpleModel.forgetFibrePoint M.scModel.group (CommAlgCat.of K K)
      (x ≫ ((i ≪≫ b.mapIso j.group.symm) ≪≫ f.symm).hom.hom.hom)) = _
  rw [Iso.trans_assoc]
  exact hx

/-- The exceptional cocycle has its marked alcove normal form at a finite unramified level. -/
theorem exceptionalAlcoveNormalForm : ExceptionalAlcoveNormalForm.{u} :=
  exceptionalAlcoveNormalForm_of_markedLevels unramifiedMarkedLevels

end UnramifiedLevelAssembly

end LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
