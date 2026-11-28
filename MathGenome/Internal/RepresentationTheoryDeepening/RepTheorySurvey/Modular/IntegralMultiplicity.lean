import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.Projection
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.DecompositionMatrix
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.ModularProjectiveCovers
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.IntegralMultiplicity

/-! The multiplicity and lattice assertions in Brauer reciprocity. -/

namespace RepTheorySurvey.Modular

/-- Evaluation at an idempotent identifies maps from its principal left ideal with the image of
its action. -/
theorem principalLeftIdeal_evaluation : MR09ReciprocitySpec.evaluation := by
  intro F A M _ _ _ _ _ _ _ e he
  let P := principalLeftIdeal e
  let T : M →ₗ[F] M := Algebra.lsmul F F M e
  let gen : P := ⟨e, Ideal.mem_span_singleton_self e⟩
  have hgen : e • gen = gen := Subtype.ext he.eq
  let eval : (P →ₗ[A] M) →ₗ[F] LinearMap.range T :=
    { toFun := fun f => ⟨f gen, ⟨f gen, by
        change e • f gen = f gen
        rw [← f.map_smul, hgen]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective eval := by
    intro f g h
    have hfg : f gen = g gen := congrArg Subtype.val h
    ext x
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
    have hx : a • gen = x := Subtype.ext ha
    rw [← hx, f.map_smul, g.map_smul, hfg]
  have hsurj : Function.Surjective eval := by
    intro v
    obtain ⟨w, hw⟩ := v.property
    have hfixed : e • (v : M) = v := by
      change e • w = (v : M) at hw
      rw [← hw, ← mul_smul, he.eq]
    refine ⟨(LinearMap.toSpanSingleton A M (v : M)).comp P.subtype, Subtype.ext ?_⟩
    exact hfixed
  exact ⟨LinearEquiv.ofBijective eval ⟨hinj, hsurj⟩, fun _ => rfl⟩


open CompositionMultiplicity
open MR09ReciprocitySpec (actionImage latticeAction)
open private value_eq_factor_sum from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.CompositionMultiplicities
open private mul_generator_eq_self from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.ModularProjectiveCovers

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem finrank_of_shortExact {F U V W : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] (f : U →ₗ[F] V) (g : V →ₗ[F] W)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g) :
    Module.finrank F V = Module.finrank F U + Module.finrank F W := by
  have hr : Module.finrank F U = Module.finrank F (LinearMap.ker g) :=
    (LinearEquiv.ofInjective f hf).finrank_eq.trans (congrArg (fun p : Submodule F V => Module.finrank F p)
      (LinearMap.exact_iff.mp h).symm)
  rw [hr, ← (g.quotKerEquivOfSurjective hg).finrank_eq, add_comm]
  exact (Submodule.finrank_quotient_add_finrank (LinearMap.ker g)).symm

section Field

variable {F G : Type*} [Field F] [Group G]
local notation "A" => MonoidAlgebra F G
variable {M N P : Type*} [AddCommGroup M] [Module (MonoidAlgebra F G) M]
  [AddCommGroup N] [Module (MonoidAlgebra F G) N]
  [AddCommGroup P] [Module (MonoidAlgebra F G) P]

/-- A compatible scalar action computes the same image as the canonical restriction. -/
private noncomputable def actionImageEquiv [Module F M] [IsScalarTower F A M] (e : A) :
    actionImage F G M e ≃ₗ[F] LinearMap.range (Algebra.lsmul F F M e) := by
  let E : RestrictScalars F A M ≃ₗ[F] M :=
    { toAddEquiv := RestrictScalars.addEquiv F A M
      map_smul' := fun c x => (RestrictScalars.addEquiv_map_smul F A M c x).trans
        (IsScalarTower.algebraMap_smul A c (RestrictScalars.addEquiv F A M x)) }
  refine E.ofSubmodules _ _ ?_
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨E y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨RestrictScalars.lsmul F A M e (E.symm y), LinearMap.mem_range_self _ _, by
      change e • E (E.symm y) = e • y
      rw [E.apply_symm_apply]⟩

private noncomputable def actionImageMap (e : A) (f : M →ₗ[A] N) :
    actionImage F G M e →ₗ[F] actionImage F G N e := by
  letI : Module F M := Module.compHom M (algebraMap F A)
  letI : Module F N := Module.compHom N (algebraMap F A)
  letI : IsScalarTower F A M := IsScalarTower.of_compHom F A M
  letI : IsScalarTower F A N := IsScalarTower.of_compHom F A N
  exact (f.restrictScalars F).restrict (fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨f y, (f.map_smul e y).symm⟩)

private noncomputable def imageDimension (e : A) (M : Type*) [AddCommGroup M] [Module A M] :
    ℕ := Module.finrank F (actionImage F G M e)

private theorem imageDimension_exact [GroundFinite F G N]
    (e : A) (he : IsIdempotentElem e) (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g) :
    imageDimension e N = imageDimension e M + imageDimension e P := by
  letI : Module.Finite F (RestrictScalars F A N) := ‹GroundFinite F G N›
  apply finrank_of_shortExact (actionImageMap e f) (actionImageMap e g)
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · intro z
    obtain ⟨y, hy⟩ := z.property
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨⟨_, LinearMap.mem_range_self (RestrictScalars.lsmul F A N e) x⟩,
      Subtype.ext ((g.map_smul e x).trans hy)⟩
  · intro y
    constructor
    · intro hy
      have hgy : g y.val = 0 := congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := (h y.val).mp hgy
      have hfixed : e • (show N from y.val) = (show N from y.val) :=
        (LinearMap.IsIdempotentElem.mem_range_iff (he.map (RestrictScalars.lsmul F A N))).mp y.property
      exact ⟨⟨_, LinearMap.mem_range_self (RestrictScalars.lsmul F A M e) x⟩,
        Subtype.ext ((f.map_smul e x).trans (hx ▸ hfixed))⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext ((h (f x.val)).mpr ⟨x.val, rfl⟩)

private noncomputable def imageDimensionCharacter (e : A) (he : IsIdempotentElem e) :
    AdditiveCharacter F G ℕ :=
  AdditiveCharacter.ofExact (fun M _ _ _ => imageDimension e M)
    (fun f g hf hg h => imageDimension_exact e he f g hf hg h)

private theorem imageDimension_congr (e : A) (f : M ≃ₗ[A] N) :
    imageDimension e M = imageDimension e N := by
  apply LinearEquiv.finrank_eq (LinearEquiv.ofBijective (actionImageMap e f.toLinearMap) ?_)
  refine ⟨fun x y h => Subtype.ext (f.injective (congrArg Subtype.val h)), ?_⟩
  intro z
  obtain ⟨y, hy⟩ := z.property
  exact ⟨⟨_, LinearMap.mem_range_self (RestrictScalars.lsmul F A M e) (f.symm y)⟩,
    Subtype.ext ((f.map_smul e (f.symm y)).trans (by
      rw [f.apply_symm_apply]
      exact hy))⟩

end Field

theorem modular_idempotent_image_finrank : MR09ReciprocitySpec.modularImageMultiplicity := by
  classical
  intro F G _ _ _ r d split hd i e he q hr ho M _ _ _
  let A := MonoidAlgebra F G
  obtain ⟨s⟩ := exists_completeSeries (F := F) (G := G) M
  have hs := value_eq_factor_sum (imageDimensionCharacter e he) s
  change imageDimension e M = ∑ j : Fin s.1.length, imageDimension e (Factor s.1 j) at hs
  change imageDimension e M = multiplicity F G M (columnModule q i)
  rw [hs, multiplicity_eq_count s, factorCount, Spec.factorCount]
  refine Finset.sum_congr rfl fun j _ => ?_
  let U := Factor s.1 j
  obtain ⟨k, ⟨f⟩⟩ := column_exhaustive q hd (modularColumnMap_surjective split)
    (modularColumnMap_ker split).le (ModuleCat.of A U) (factor_simple s.1 j)
  change imageDimension e U = if Isomorphic (F := F) (G := G) U (columnModule q i) then 1 else 0
  have hi : Isomorphic (F := F) (G := G) U (columnModule q i) ↔ k = i := by
    constructor
    · rintro ⟨g⟩
      exact (modular_column_family hd split).eq_of_iso ⟨f.symm.trans g⟩
    · rintro rfl
      exact ⟨f⟩
  rw [hi, imageDimension_congr e f]
  have hRank := ((actionImageEquiv e (M := columnModule q k)).finrank_eq.trans
    (congrArg (fun T : Module.End F (columnModule q k) =>
      Module.finrank F (LinearMap.range T)) (column_lsmul q k e).symm)).trans
    (column_rank_one q e i hr ho k)
  by_cases h : k = i
  · rw [ite_eq_left h] at hRank ⊢
    exact hRank
  · rw [ite_eq_right h] at hRank ⊢
    exact hRank


section Ordinary

variable {F G : Type*} [Field F] [Group G]
local notation "A" => MonoidAlgebra F G
variable (V : Type*) [AddCommGroup V] [Module (MonoidAlgebra F G) V]
  [Module F V] [IsScalarTower F (MonoidAlgebra F G) V]
  [Module.Finite F V]

private noncomputable def homDimension (M : Type*) [AddCommGroup M] [Module A M] : ℕ :=
  Module.finrank F (M →ₗ[A] V)

private theorem homDimension_exact [IsSemisimpleRing A]
    {L M N : Type*} [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [GroundFinite F G M]
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g) :
    homDimension (F := F) (G := G) V M = homDimension (F := F) (G := G) V L + homDimension (F := F) (G := G) V N := by
  letI : Module F M := Module.compHom M (algebraMap F A)
  letI : IsScalarTower F A M := IsScalarTower.of_compHom F A M
  letI : Module.Finite F M := ‹GroundFinite F G M›
  letI : Module.Finite F (M →ₗ[A] V) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ (R := F) (S := A) (R₁ := F) (M := M) (N := V))
      (fun _ _ hfg => LinearMap.restrictScalars_injective F hfg)
  rw [add_comm]
  apply finrank_of_shortExact (LinearMap.lcomp F V g) (LinearMap.lcomp F V f)
  · exact LinearMap.lcomp_injective_of_surjective g hg
  · intro t
    exact IsSemisimpleModule.extension_property f hf t
  · intro t
    constructor
    · intro ht
      have hker : LinearMap.ker g ≤ LinearMap.ker t := by
        rw [LinearMap.exact_iff.mp h]
        rintro _ ⟨x, rfl⟩
        exact DFunLike.congr_fun ht x
      refine ⟨g.liftOfSurjective hg ⟨t, hker⟩, ?_⟩
      exact LinearMap.ext fun x => LinearMap.equivOfSurjective_apply hg hker
    · rintro ⟨u, rfl⟩
      ext x
      change u (g (f x)) = 0
      rw [(h (f x)).mpr ⟨x, rfl⟩, map_zero]

private noncomputable def homDimensionCharacter [IsSemisimpleRing A] :
    AdditiveCharacter F G ℕ :=
  AdditiveCharacter.ofExact (fun M _ _ _ => homDimension (F := F) (G := G) V M)
    (fun f g hf hg h => homDimension_exact (F := F) (G := G) V f g hf hg h)

omit [Module.Finite F V] in
private theorem homDimension_congr {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M ≃ₗ[A] N) :
    homDimension (F := F) (G := G) V M = homDimension (F := F) (G := G) V N := by
  let equiv : (M →ₗ[A] V) ≃ₗ[F] (N →ₗ[A] V) :=
    { LinearMap.lcomp F V f.symm.toLinearMap with
      invFun := LinearMap.lcomp F V f.toLinearMap
      left_inv := fun t => LinearMap.ext fun x => by simp
      right_inv := fun t => LinearMap.ext fun x => by simp }
  exact equiv.finrank_eq

open Classical in
omit [Module.Finite F V] in
private theorem homDimension_simple [IsSimpleModule A V] {M : Type*}
    [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    (hV : homDimension (F := F) (G := G) V V = 1) :
    homDimension (F := F) (G := G) V M = if Isomorphic (F := F) (G := G) M V then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨e⟩ := h
    exact (homDimension_congr (F := F) (G := G) V e).trans hV
  · have : Subsingleton (M →ₗ[A] V) := subsingleton_of_forall_eq 0 fun f => by
      by_contra hf
      exact h ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)⟩
    exact Module.finrank_zero_of_subsingleton

end Ordinary

theorem ordinary_idempotent_image_finrank : MR09ReciprocitySpec.ordinaryImageMultiplicity := by
  classical
  intro F G _ _ _ hsplit e he V _ _ hV
  let A := MonoidAlgebra F G
  letI : Module F V := Module.compHom V (algebraMap F A)
  letI : IsScalarTower F A V := IsScalarTower.of_compHom F A V
  letI : Module.Finite F V := groundFinite_of_simple (F := F) (G := G) (S := V)
  let P := principalLeftIdeal e
  letI : GroundFinite F G A := groundFinite_groupAlgebra
  letI : GroundFinite F G P := groundFinite_of_injective P.subtype P.subtype_injective
  obtain ⟨r, d, hd, ⟨split⟩⟩ := hsplit
  letI : IsSemisimpleRing A := split.symm.toRingEquiv.isSemisimpleRing
  have hOne : homDimension (F := F) (G := G) V V = 1 := by
    obtain ⟨i, ⟨s⟩⟩ := column_exhaustive split.toAlgHom hd split.surjective
      (by
        intro a ha
        have hz : split a = 0 := RingHom.mem_ker.mp ha
        rw [(map_eq_zero_iff split split.injective).mp hz]
        exact (Ring.jacobson A).zero_mem)
      (ModuleCat.of A V) hV
    let C := columnModule split.toAlgHom i
    let d : Module.End A C ≃ₗ[F] Module.End A V :=
      { s.symm.conjRingEquiv.toAddEquiv with
        map_smul' := by
          intro c t
          apply LinearMap.ext
          intro x
          change s.symm (c • t (s x)) = c • s.symm (t (s x))
          exact (s.symm.restrictScalars F).map_smul c (t (s x)) }
    let k : F ≃ₗ[F] Module.End A C := LinearEquiv.ofBijective
      (Algebra.linearMap F (Module.End A C)) (columnScalar_bijective _ hd split.surjective i)
    exact (k.trans d).finrank_eq.symm.trans (Module.finrank_self F)
  obtain ⟨s⟩ := exists_completeSeries (F := F) (G := G) P
  have hs := value_eq_factor_sum (homDimensionCharacter (F := F) (G := G) V) s
  change homDimension (F := F) (G := G) V P = ∑ j : Fin s.1.length, homDimension (F := F) (G := G) V (Factor s.1 j) at hs
  obtain ⟨eval, _⟩ := principalLeftIdeal_evaluation (F := F) (A := A) (M := V) e he
  change imageDimension e V = multiplicity F G P V
  rw [show imageDimension e V = homDimension (F := F) (G := G) V P from
      (actionImageEquiv e (M := V)).finrank_eq.trans eval.finrank_eq.symm,
    hs, multiplicity_eq_count s, factorCount, Spec.factorCount]
  refine Finset.sum_congr rfl fun j _ => ?_
  letI := factor_simple s.1 j
  exact homDimension_simple (F := F) (G := G) V hOne


section LatticeImage

open IsLocalRing MR09ReciprocitySpec

private noncomputable def reduceRangeEquiv {O X : Type*} [CommRing O] [IsLocalRing O]
    [AddCommGroup X] [Module O X] {T : X →ₗ[O] X} (hT : IsIdempotentElem T) :
    ResidueQuotient O (LinearMap.range T) ≃ₗ[ResidueField O] LinearMap.range (reduceMap T) := by
  let U := LinearMap.range T
  let inc := reduceMap U.subtype
  let proj := reduceMap T.rangeRestrict
  have hLeft : Function.LeftInverse proj inc := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
      (maximalIdeal O • (⊤ : Submodule O U)) q
    change reduce (T.rangeRestrict x.val) = reduce x
    exact congrArg reduce (Subtype.ext ((LinearMap.IsIdempotentElem.mem_range_iff hT).mp x.property))
  have hComp (q : ResidueQuotient O X) : inc (proj q) = reduceMap T q := by
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
      (maximalIdeal O • (⊤ : Submodule O X)) q
    rfl
  have hRange : LinearMap.range inc = LinearMap.range (reduceMap T) := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨inc x, (hComp _).symm.trans (congrArg inc (hLeft x))⟩
    · rintro ⟨x, rfl⟩
      exact ⟨proj x, hComp x⟩
  exact (LinearEquiv.ofInjective inc hLeft.injective).trans (LinearEquiv.ofEq _ _ hRange)

private noncomputable def equivActionRange {F X Y : Type*} [Field F]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (E : X ≃ₗ[F] Y) (T : X →ₗ[F] X) (S : Y →ₗ[F] Y)
    (h : ∀ x, E (T x) = S (E x)) : LinearMap.range T ≃ₗ[F] LinearMap.range S := by
  refine E.ofSubmodules _ _ ?_
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨E y, (h y).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨T (E.symm y), LinearMap.mem_range_self T _, by
      change E (T (E.symm y)) = S y
      rw [h, E.apply_symm_apply]⟩

variable {G : Type*} [Group G] {O K : Type*} [CommRing O] [Field K] [Algebra O K]
variable {V : Type*} [AddCommGroup V] [Module (MonoidAlgebra K G) V]
local notation "OG" => MonoidAlgebra O G
local notation "KG" => MonoidAlgebra K G
local notation "Vₖ" => RestrictScalars K KG V
local notation "k" => ResidueField O
local notation "kG" => MonoidAlgebra k G

attribute [local instance] RestrictScalars.moduleOrig

private theorem latticeAction_coe (L : NativeStableLattice O K G V) (a : OG) :
    letI : Module O Vₖ := Module.restrictScalars O K Vₖ
    letI : IsScalarTower O K Vₖ := IsScalarTower.restrictScalars O K Vₖ
    ∀ x : L.carrier, (latticeAction L a x : Vₖ) =
      RestrictScalars.lsmul K KG V (groupAlgebraToFractionField O K G a) x.val := by
  intro x
  letI : Module O Vₖ := Module.restrictScalars O K Vₖ
  letI : IsScalarTower O K Vₖ := IsScalarTower.restrictScalars O K Vₖ
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    have hm : groupAlgebraToFractionField O K G (MonoidAlgebra.of O G g) =
        MonoidAlgebra.of K G g := by
      simp [MonoidAlgebra.of_apply, groupAlgebraToFractionField]
    change ((integralLatticeAction O L).asAlgebraHom (MonoidAlgebra.of O G g) x : Vₖ) = _
    rw [Representation.asAlgebraHom_of, hm]
    change Representation.ofModule (G := G) V g x.val = _
    rw [← Representation.asAlgebraHom_of]
    exact Representation.ofModule_asAlgebraHom_apply_apply V _ _
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | smul c a ha =>
    have hm : groupAlgebraToFractionField O K G (c • a) =
        algebraMap O K c • groupAlgebraToFractionField O K G a := by
      simp [groupAlgebraToFractionField, Algebra.smul_def, MonoidAlgebra.coe_algebraMap]
    simp only [hm, map_smul, LinearMap.smul_apply, Submodule.coe_smul, ha]
    rfl

private theorem span_lattice_image [IsDomain O] [IsFractionRing O K]
    (L : NativeStableLattice O K G V) (a : OG) :
    letI : Module O Vₖ := Module.restrictScalars O K Vₖ
    letI : IsScalarTower O K Vₖ := IsScalarTower.restrictScalars O K Vₖ
    let J := (LinearMap.range (latticeAction L a)).map L.carrier.subtype
    Submodule.span K (J : Set Vₖ) =
      actionImage K G V (groupAlgebraToFractionField O K G a) := by
  intro J
  letI : Module O Vₖ := Module.restrictScalars O K Vₖ
  letI : IsScalarTower O K Vₖ := IsScalarTower.restrictScalars O K Vₖ
  let T := RestrictScalars.lsmul K KG V (groupAlgebraToFractionField O K G a)
  have hs : (J : Set Vₖ) = T '' (L.carrier : Set Vₖ) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x.val, x.property, (latticeAction_coe L a x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, LinearMap.mem_range_self (latticeAction L a) ⟨x, hx⟩,
        latticeAction_coe L a ⟨x, hx⟩⟩
  rw [hs, ← Submodule.map_span, L.spans, Submodule.map_top]

private noncomputable def residueLatticeImageEquiv [IsLocalRing O]
    (L : NativeStableLattice O K G V) (e : OG) (he : IsIdempotentElem e) :
    ResidueQuotient O (LinearMap.range (latticeAction L e)) ≃ₗ[k]
      actionImage k G (NativeStableLattice.reduction L) (groupAlgebraReduction O G e) := by
  letI : Module O Vₖ := Module.restrictScalars O K Vₖ
  letI : IsScalarTower O K Vₖ := IsScalarTower.restrictScalars O K Vₖ
  let ρ := residueRepresentation (integralLatticeAction O L)
  let T := RestrictScalars.lsmul k kG ρ.asModule (groupAlgebraReduction O G e)
  let E := MR04Spec.asModuleScalarEquiv ρ
  have h (x : RestrictScalars k kG ρ.asModule) :
      E (T x) = reduceMap (latticeAction L e) (E x) := by
    change ρ.asAlgebraHom (groupAlgebraReduction O G e) (E x) = _
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective
      (maximalIdeal O • (⊤ : Submodule O L.carrier)) (E x)
    change reduce y = E x at hy
    rw [← hy, reduceMap_reduce]
    exact residueRepresentation_algebra_reduce (integralLatticeAction O L) e y
  exact (reduceRangeEquiv (he.map (latticeAction L))).trans
    (equivActionRange E T (reduceMap (latticeAction L e)) h).symm

theorem stableLattice_idempotent_image : MR09ReciprocitySpec.stableLatticeImage := by
  intro G _ O _ _ _ K _ _ _ V _ _ L e he T U W
  let X := RestrictScalars K (MonoidAlgebra K G) V
  letI : Module O X := Module.restrictScalars O K X
  letI : IsScalarTower O K X := IsScalarTower.restrictScalars O K X
  letI := L.finite
  letI := L.free
  letI : Module.Finite O (LinearMap.range T) :=
    Module.Finite.of_surjective T.rangeRestrict T.surjective_rangeRestrict
  letI : Module.Free O (LinearMap.range T) :=
    (Module.free_iff_isTorsionFree (R := O) (M := LinearMap.range T)).mpr inferInstance
  let E := residueLatticeImageEquiv L e he
  refine ⟨inferInstance, inferInstance, LinearMap.IsIdempotentElem.isCompl (he.map (latticeAction L)), ⟨E⟩, ?_, ?_⟩
  · let J := (LinearMap.range T).map L.carrier.subtype
    have hJ : Submodule.span K (J : Set X) = U := span_lattice_image L e
    have h := finrank_fractionSpan (K := K) J
    rw [hJ] at h
    exact h.trans (Submodule.equivMapOfInjective L.carrier.subtype
      L.carrier.subtype_injective (LinearMap.range T)).finrank_eq.symm
  · exact E.finrank_eq.symm.trans (finrank_residueQuotient (LinearMap.range T))

end LatticeImage


section PrincipalIdeal

open IsLocalRing
open scoped Pointwise

private theorem mul_mem_principalLeftIdeal {A : Type*} [Ring A] (a e : A) :
    a * e ∈ principalLeftIdeal e :=
  Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩

private noncomputable def mapPrincipalIdealCoefficients {R S G : Type*} [CommRing R]
    [CommRing S] [Group G] (f : R →+* S) (e : MonoidAlgebra R G) :
    principalLeftIdeal e →ₛₗ[f] principalLeftIdeal (MonoidAlgebra.mapRingHom G f e) where
  toFun x := ⟨MonoidAlgebra.mapRingHom G f x, by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
    rw [← ha, map_mul]
    exact mul_mem_principalLeftIdeal _ _⟩
  map_add' x y := Subtype.ext (map_add (MonoidAlgebra.mapRingHom G f) x.val y.val)
  map_smul' c x := Subtype.ext (by
    change MonoidAlgebra.mapRingHom G f (c • x.val) =
      f c • MonoidAlgebra.mapRingHom G f x.val
    simp [Algebra.smul_def, MonoidAlgebra.coe_algebraMap])

variable {O K G : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [Group G] [Finite G] {p : ℕ}
local notation "OG" => MonoidAlgebra O G
local notation "KG" => MonoidAlgebra K G
local notation "k" => ResidueField O
local notation "kG" => MonoidAlgebra k G

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite G] in
private theorem fractionalCoefficients_injective [IsFractionRing O K] :
    Function.Injective (groupAlgebraToFractionField O K G) :=
  MonoidAlgebra.map_injective _ (IsFractionRing.injective O K)

omit [Finite G] in
private theorem principalIdealReduction_surjective (e : OG) :
    Function.Surjective (mapPrincipalIdealCoefficients (residue O) e) := by
  intro x
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
  obtain ⟨b, hb⟩ := groupAlgebraReduction_surjective O G a
  refine ⟨⟨b * e, mul_mem_principalLeftIdeal b e⟩, Subtype.ext ?_⟩
  change groupAlgebraReduction O G (b * e) = (x : kG)
  rw [map_mul, hb]
  exact ha

private theorem principalIdealReduction_ker (system : SplittingSystem G p O K)
    (e : OG) (he : IsIdempotentElem e) :
    LinearMap.ker (mapPrincipalIdealCoefficients (residue O) e) =
      maximalIdeal O • (⊤ : Submodule O (principalLeftIdeal e)) := by
  rw [system.maximalIdeal_eq_span, Submodule.ideal_span_singleton_smul]
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro hx
    have hx' : (x : OG) ∈ RingHom.ker (groupAlgebraReduction O G) :=
      RingHom.mem_ker.mpr (congrArg Subtype.val hx)
    rw [groupAlgebraReduction_kernel O G system] at hx'
    change (x : OG) ∈ Ideal.span {algebraMap O OG system.uniformizer} at hx'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hx'
    refine ⟨⟨b * e, mul_mem_principalLeftIdeal b e⟩, Submodule.mem_top, Subtype.ext ?_⟩
    change system.uniformizer • (b * e) = (x : OG)
    rw [Algebra.smul_def, ← mul_assoc, Algebra.commutes _ b, hb, mul_generator_eq_self he]
  · rintro ⟨b, _, rfl⟩
    rw [map_smulₛₗ]
    have hπ : residue O system.uniformizer = 0 := by
      rw [residue_eq_zero_iff, system.maximalIdeal_eq_span]
      exact Ideal.mem_span_singleton_self _
    rw [hπ, zero_smul]

private noncomputable def principalIdealResidueEquiv (system : SplittingSystem G p O K)
    (e : OG) (he : IsIdempotentElem e) :
    ResidueQuotient O (principalLeftIdeal e) ≃ₗ[k] principalLeftIdeal (groupAlgebraReduction O G e) := by
  let I := maximalIdeal O • (⊤ : Submodule O (principalLeftIdeal e))
  let f := mapPrincipalIdealCoefficients (residue O) e
  have hk : LinearMap.ker f = I := principalIdealReduction_ker system e he
  let q := I.liftQ f hk.ge
  let b : ResidueQuotient O (principalLeftIdeal e) →ₗ[k]
      principalLeftIdeal (groupAlgebraReduction O G e) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := residue_surjective c
        exact q.map_smulₛₗ r x }
  refine LinearEquiv.ofBijective b ⟨?_, ?_⟩
  · change Function.Injective q
    exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' I f hk.symm)
  · intro x
    obtain ⟨y, hy⟩ := principalIdealReduction_surjective e x
    exact ⟨reduce y, hy⟩

private noncomputable def reduceEquiv {O X Y : Type*} [CommRing O] [IsLocalRing O]
    [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (E : X ≃ₗ[O] Y) :
    ResidueQuotient O X ≃ₗ[ResidueField O] ResidueQuotient O Y :=
  { reduceMap E.toLinearMap with
    invFun := reduceMap E.symm.toLinearMap
    left_inv := fun z => by
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
        (maximalIdeal O • (⊤ : Submodule O X)) z
      change reduce (E.symm (E x)) = reduce x
      rw [E.symm_apply_apply]
    right_inv := fun z => by
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
        (maximalIdeal O • (⊤ : Submodule O Y)) z
      change reduce (E (E.symm y)) = reduce y
      rw [E.apply_symm_apply] }

end PrincipalIdeal

open IsLocalRing in
theorem exists_principalIdeal_stableLattice : MR09ReciprocitySpec.principalIdealLattice := by
  classical
  intro G _ _ p O _ _ _ K _ _ system e he P Pbar
  letI := system.fractionRing
  let OG := MonoidAlgebra O G
  let KG := MonoidAlgebra K G
  let P₀ := principalLeftIdeal e
  let X := RestrictScalars K (MonoidAlgebra K G) P
  letI : Module O X := Module.restrictScalars O K X
  letI : IsScalarTower O K X := IsScalarTower.restrictScalars O K X
  let frac := groupAlgebraToFractionField O K G
  let red := groupAlgebraReduction O G
  let f : P₀ →ₗ[O] X :=
    { toFun := mapPrincipalIdealCoefficients (algebraMap O K) e
      map_add' := (mapPrincipalIdealCoefficients (algebraMap O K) e).map_add
      map_smul' := fun c x => by
        apply Subtype.ext
        change frac (c • (x : OG)) =
          algebraMap K KG (algebraMap O K c) * frac (x : OG)
        simp [frac, KG, groupAlgebraToFractionField, Algebra.smul_def, MonoidAlgebra.coe_algebraMap] }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact fractionalCoefficients_injective (congrArg (fun z : X => (RestrictScalars.addEquiv K KG P z : KG)) h)
  let E := LinearEquiv.ofInjective f hf
  let J := LinearMap.range f
  have hJ : Module.Finite O J := by
    letI : Module.Finite O OG := Module.Finite.of_basis (MonoidAlgebra.basis G O)
    let R : OG →ₗ[OG] P₀ := (LinearMap.toSpanSingleton OG OG e).codRestrict P₀
      (fun a => mul_mem_principalLeftIdeal a e)
    letI : Module.Finite O P₀ := Module.Finite.of_surjective (R.restrictScalars O) (by
      intro x
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
      exact ⟨a, Subtype.ext ha⟩)
    exact Module.Finite.equiv E
  have hfree : Module.Free O J := by
    letI : FaithfulSMul O K :=
      (faithfulSMul_iff_algebraMap_injective O K).mpr (IsFractionRing.injective O K)
    letI : Module.IsTorsionFree O X := Module.IsTorsionFree.trans_faithfulSMul O K X
    exact (Module.free_iff_isTorsionFree (R := O) (M := J)).mpr inferInstance
  have hspan : Submodule.span K (J : Set X) = ⊤ := by
    let R : KG →ₗ[K] X :=
      { toFun := fun a => ⟨a * frac e, mul_mem_principalLeftIdeal a (frac e)⟩
        map_add' := fun a b => Subtype.ext (add_mul a b _)
        map_smul' := fun c a => Subtype.ext (by
          change (c • a) * frac e = algebraMap K KG c * (a * frac e)
          rw [Algebra.smul_def, mul_assoc]) }
    have hR : Function.Surjective R := by
      intro x
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
      exact ⟨a, Subtype.ext ha⟩
    apply top_unique
    rw [← LinearMap.range_eq_top.mpr hR, ← Submodule.map_top,
      ← (MonoidAlgebra.basis G K).span_eq, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨MonoidAlgebra.of O G g * e, mul_mem_principalLeftIdeal _ _⟩, Subtype.ext ?_⟩
    change frac (MonoidAlgebra.of O G g * e) = (MonoidAlgebra.basis G K g) * frac e
    rw [map_mul]
    congr 1
    simp [frac, groupAlgebraToFractionField, MonoidAlgebra.of_apply, MonoidAlgebra.basis_apply]
  let L : NativeStableLattice O K G P :=
    { carrier := J
      finite := hJ
      free := hfree
      spans := hspan
      stable := by
        intro g x hx
        obtain ⟨y, rfl⟩ := hx
        refine ⟨MonoidAlgebra.of O G g • y, Subtype.ext ?_⟩
        rw [← Representation.asAlgebraHom_of, Representation.ofModule_asAlgebraHom_apply_apply]
        change frac (MonoidAlgebra.of O G g * (y : OG)) = MonoidAlgebra.of K G g * frac (y : OG)
        rw [map_mul]
        congr 1
        simp [frac, groupAlgebraToFractionField, MonoidAlgebra.of_apply] }
  refine ⟨L, ?_, ?_⟩
  · intro x
    change (x : X) ∈ J ↔ _
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩
  let σ := integralLatticeAction O L
  let ρ := residueRepresentation σ
  let Ebar := principalIdealResidueEquiv system e he
  let Eb := (reduceEquiv E.symm).trans Ebar
  let iso := ρ.asModuleEquiv.toAddEquiv.trans Eb.toAddEquiv
  have hAct (a : OG) (y : L.carrier) : E.symm (σ.asAlgebraHom a y) = a • E.symm y := by
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    have hy : f (E.symm y) = (y : X) := congrArg Subtype.val (E.apply_symm_apply y)
    change (latticeAction L a y : X) = f (a • E.symm y)
    rw [latticeAction_coe, ← hy]
    apply Subtype.ext
    change frac a * frac (E.symm y : OG) = frac (a * (E.symm y : OG))
    exact (map_mul frac _ _).symm
  refine ⟨{ iso with map_smul' := ?_ }⟩
  intro a x
  obtain ⟨b, rfl⟩ := groupAlgebraReduction_surjective O G a
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective
    (maximalIdeal O • (⊤ : Submodule O L.carrier)) (ρ.asModuleEquiv x)
  change reduce y = ρ.asModuleEquiv x at hy
  change Ebar (reduceMap E.symm.toLinearMap (ρ.asModuleEquiv (red b • x))) =
    red b • Ebar (reduceMap E.symm.toLinearMap (ρ.asModuleEquiv x))
  have hred := residueRepresentation_algebra_reduce σ b y
  change ρ.asAlgebraHom (red b) (reduce y) = reduce (σ.asAlgebraHom b y) at hred
  rw [Representation.asModuleEquiv_map_smul, ← hy, hred]
  change mapPrincipalIdealCoefficients (residue O) e (E.symm (σ.asAlgebraHom b y)) =
    red b • mapPrincipalIdealCoefficients (residue O) e (E.symm y)
  rw [hAct]
  apply Subtype.ext
  exact map_mul red _ _

theorem brauer_reciprocity : MR09ReciprocitySpec.brauerReciprocity := by
  intro G _ _ p O _ _ _ K _ _ system r d split hd i e he q eBar hr ho V _ _ hV
  letI := system.fractionRing
  letI : GroundFinite K G V := groundFinite_of_simple
  letI : IsSimpleModule (MonoidAlgebra (IsLocalRing.ResidueField O) G) (columnModule q i) :=
    (modular_column_family hd split).simple i
  letI : Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V) := ‹GroundFinite K G V›
  obtain ⟨L⟩ := exists_nativeStableLattice system V
  letI : GroundFinite (IsLocalRing.ResidueField O) G (NativeStableLattice.reduction L) :=
    MR04Spec.nativeReductionFinite V L
  obtain ⟨_, _, _, _, hK, hk⟩ := stableLattice_idempotent_image L e he
  calc
    _ = Module.finrank K (actionImage K G V (MR01Spec.fractionMapValue O K G e)) :=
      (ordinary_idempotent_image_finrank system.ordinarySplit _
        (he.map (MR01Spec.fractionMapValue O K G)) V).symm
    _ = _ := hK
    _ = Module.finrank (IsLocalRing.ResidueField O)
          (actionImage (IsLocalRing.ResidueField O) G (NativeStableLattice.reduction L) eBar) := hk.symm
    _ = _ := modular_idempotent_image_finrank split hd i eBar
      (he.map (MR01Spec.reductionValue O G)) hr ho (NativeStableLattice.reduction L)
    _ = _ := (decompositionMultiplicity_eq_lattice system V (columnModule q i) L).symm

end RepTheorySurvey.Modular
