import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat.Algebra
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

theorem rawExact : rawExactType.{u,v,w} k G := by
  intro h
  refine ⟨?_, fun _ _ _ _ _ _ => rfl⟩
  intro S hS
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · intro z
    constructor
    · intro hz
      have hz' (g : Fin n → G) : S.g (z g) = 0 := congrFun hz g
      choose x hx using fun g => (ShortComplex.moduleCat_exact_iff S).mp hS.exact (z g) (hz' g)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      exact ShortComplex.moduleCat_zero_apply _ x
  · intro x y hxy
    exact funext fun g => hS.moduleCat_injective_f (congrFun hxy g)
  · intro z
    choose y hy using fun g : Fin n → G => hS.moduleCat_surjective_g (z g)
    exact ⟨y, funext hy⟩

theorem ambientExact : AmbientExact.{u,v,w} k G := by
  intro S hS
  exact GroupLowDegreesAndCoefficients.Large.cochainExact k G (hS.map_of_exact (lift k G))

theorem sequenceComparison : sequenceComparisonType.{u,v,w} k G := by
  intro h
  let e : lifted k G h ≅ ambientBar.{u,v,w} k G := (barIso k G).symm
  refine ⟨e, ⟨?_, ?_⟩, ?_⟩
  · intro M n f g
    have he := (ambientEvaluation k G M n).apply_symm_apply (ULift.up f)
    exact congrArg (fun x : ULift.{u} (TupleCochain k G M n) =>
      (ULift.up (x.down g) : (lift k G).obj M)) he
  · intro M n φ g
    rfl
  · intro S hS
    refine ⟨hS.map_of_exact (lift k G), ?_, ambientExact k G hS, S.mapNatIso e, rfl, rfl, rfl⟩
    exact ((rawExact k G h).1 hS).map_of_exact ((scalarLift.{u,v,w} k).mapHomologicalComplex (.up ℕ))

private lemma rawDifferential (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G)
    (n : ℕ) (z : TupleCochain k G M n) :
    ((complex k G h M).d n (n+1)).hom z = differential k G M n z := by
  simp only [complex, rawFunctor, rawComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]

private lemma cyclesMk_apply {r : Type u} [CommRing r]
    (K : CochainComplex (ModuleCat.{w} r) ℕ) (n : ℕ)
    (z : K.X n) (hz : (K.d n (n+1)).hom z = 0) :
    (K.iCycles n).hom (K.cyclesMk z (n+1) (by simp) hz) = z :=
  K.i_cyclesMk z (n+1) (by simp) hz

private theorem zeroIdentification_exists (h : SquareZero.{u,v,w} k G) :
    ∃ e : invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k ≅ rawCohomology k G h 0,
      zeroIdentification k G e := by
  obtain ⟨e, he⟩ := barDegreeZero k G h
  refine ⟨e, ?_⟩
  intro M m
  obtain ⟨z, hz, he'⟩ := he M m
  let K := rawComplex k G h M
  have hz' : differential k G M 0 (fun _ => m.val) = 0 := by
    have eq := congrArg (fun f : K.cycles 0 ⟶ K.X 1 => f.hom z)
      (K.iCycles_d 0 1)
    change (K.d 0 1).hom ((K.iCycles 0).hom z) = 0 at eq
    have hd := rawDifferential k G h M 0 ((K.iCycles 0).hom z)
    change (K.d 0 1).hom ((K.iCycles 0).hom z) = differential k G M 0 ((K.iCycles 0).hom z) at hd
    change (K.iCycles 0).hom z = _ at hz
    rw [eq, hz] at hd
    exact hd.symm
  refine ⟨hz', he'.trans ?_⟩
  apply congrArg (K.homologyπ 0).hom
  apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (K.iCycles 0))
  exact hz.trans (cyclesMk_apply K 0 _ _).symm

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

theorem longExact : longExactType.{u,v,w} k G := by
  constructor
  · intro h hex
    refine ⟨fun n => by change (rawCohomology k G h n).Additive; infer_instance,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro S T hS hT f n
      exact (HomologicalComplex.HomologySequence.δ_naturality
        ((raw k G h).mapShortComplex.map f) (hex hS) (hex hT) n (n+1) rfl).symm
    · intro S hS n
      exact ⟨(hex hS).δ_comp n (n+1) rfl, (hex hS).homology_exact₁ n (n+1) rfl⟩
    · intro S hS n
      exact ⟨_, (hex hS).homology_exact₂ n⟩
    · intro S hS n
      exact ⟨(hex hS).comp_δ n (n+1) rfl, (hex hS).homology_exact₃ n (n+1) rfl⟩
    · intro S hS
      obtain ⟨e, _⟩ := zeroIdentification_exists k G h
      have hm : Mono ((invariantsFunctor k G).map S.f) := by
        apply (ModuleCat.mono_iff_injective _).mpr
        intro m m' eq
        exact Subtype.ext (hS.moduleCat_injective_f (congrArg Subtype.val eq))
      let := hm
      have hc : Mono (e.inv.app S.X₁ ≫ (invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k).map S.f) := by
        change Mono (e.inv.app S.X₁ ≫ (rawInvariantLift.{u,v,w} k).map ((invariantsFunctor k G).map S.f))
        infer_instance
      rw [← e.inv.naturality S.f] at hc
      change Mono ((rawCohomology k G h 0).map S.f)
      exact mono_of_mono ((rawCohomology k G h 0).map S.f) (e.inv.app S.X₂)
  · let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
    let := GroupDerivedInvariants.leftExact.{u,v,w} k G
    have H : IsCohomological (rightSystem F) := UniversalDeltaFunctors.rightDelta _ _ F
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      let := H.additive n
      change ((lift k G) ⋙ (rightSystem F).value n).Additive
      infer_instance
    · intro S T hs ht f n
      exact H.naturality (hs.map_of_exact (lift k G)) (ht.map_of_exact (lift k G))
        ((lift k G).mapShortComplex.map f) n
    · intro S hs n
      exact H.exact₁ (hs.map_of_exact (lift k G)) n
    · intro S hs n
      exact H.exact₂ (hs.map_of_exact (lift k G)) n
    · intro S hs n
      exact H.exact₃ (hs.map_of_exact (lift k G)) n
    · intro S hs
      exact H.mono_zero (hs.map_of_exact (lift k G))

private lemma cocycleRepresentatives {r : Type u} [CommRing r]
    (K : CochainComplex (ModuleCat.{w} r) ℕ) (n : ℕ) (a : K.homology n) :
    ∃ (z : K.X n) (hz : (K.d n (n+1)).hom z = 0),
      (K.homologyπ n).hom (K.cyclesMk z (n+1) (by simp) hz) = a := by
  obtain ⟨s, hs⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance a
  have hd : (K.d n (n+1)).hom ((K.iCycles n).hom s) = 0 :=
    congrArg (fun f : K.cycles n ⟶ K.X (n+1) => f.hom s) (K.iCycles_d n (n+1))
  refine ⟨(K.iCycles n).hom s, hd, ?_⟩
  rw [← hs]
  apply congrArg (K.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (K.iCycles n))
  exact K.i_cyclesMk _ _ _ _

theorem liftedBoundary : liftedBoundaryType.{u,v,w} k G := by
  intro h hex S hS n
  let C := S.map (raw k G h)
  have hc : C.ShortExact := hex hS
  constructor
  · intro a
    obtain ⟨z, hz, ha⟩ := cocycleRepresentatives C.X₃ n a
    exact ⟨z, (rawDifferential k G h S.X₃ n z).symm.trans hz, ha⟩
  intro z hz
  have hz' : (C.X₃.d n (n+1)).hom z = 0 := (rawDifferential k G h S.X₃ n z).trans hz
  constructor
  · have h₀ := hc.map_of_exact (HomologicalComplex.eval (ModuleCat k) (.up ℕ) n)
    have h₁ := hc.map_of_exact (HomologicalComplex.eval (ModuleCat k) (.up ℕ) (n+1))
    obtain ⟨y, hy⟩ := h₀.moduleCat_surjective_g z
    have hy' : (C.g.f n).hom y = z := hy
    have hd : (C.g.f (n+1)).hom ((C.X₂.d n (n+1)).hom y) = 0 := by
      have he := congrArg (fun f => f.hom y) (C.g.comm n (n+1))
      change (C.X₃.d n (n+1)).hom ((C.g.f n).hom y) = _ at he
      rw [hy', hz'] at he
      exact he.symm
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp h₁.exact _ hd
    have he : (C.f.f (n+1)).hom x = differential k G S.X₂ n y :=
      hx.trans (rawDifferential k G h S.X₂ n y)
    exact ⟨y, x, congrFun hy', congrFun he⟩
  · intro y x hy hx
    have hy' : (C.g.f n).hom y = z := funext hy
    have hx' : (C.f.f (n+1)).hom x = (C.X₂.d n (n+1)).hom y :=
      (funext hx).trans (rawDifferential k G h S.X₂ n y).symm
    have hd : (C.X₁.d (n+1) (n+2)).hom x = 0 :=
      hc.d_eq_zero_of_f_eq_d_apply n (n+1) y x hx' (n+2)
    refine ⟨(rawDifferential k G h S.X₁ (n+1) x).symm.trans hd, ?_⟩
    exact hc.δ_apply n (n+1) rfl z hz' y hy' x hx' (n+2) (by simp)

private lemma differential_one (M : Coeff.{u,v,w} k G) (z : TupleCochain k G M 1)
    (g : Fin 2 → G) :
    differential k G M 1 z g =
      act k G M (g 0) (z (fun _ => g 1)) -
        z (fun _ => g 0 * g 1) + z (fun _ => g 0) := by
  have ht : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i
    fin_cases i
    rfl
  have hh : (fun i : Fin 1 => g i.castSucc) = fun _ => g 0 := by
    funext i
    fin_cases i
    rfl
  have hm : Fin.contractNth (0 : Fin 2) (· * ·) g = fun _ => g 0 * g 1 := by
    funext i
    fin_cases i
    exact Fin.contractNth_apply_of_eq _ _ _ _ rfl
  have hcast : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
  simp [differential_apply, act, ht, hh, hm, hcast, sub_eq_add_neg]

private lemma isCrossed_iff (M : Coeff.{u,v,w} k G) (z : TupleCochain k G M 1) :
    (fun g : G => z (fun _ => g)) ∈ crossed k G M ↔ differential k G M 1 z = 0 := by
  change (∀ g h : G, z (fun _ => g*h) = z (fun _ => g) + act k G M g (z (fun _ => h))) ↔ _
  constructor
  · intro hz
    funext g
    rw [differential_one, hz]
    change _ = (0 : M)
    abel
  · intro hz g h
    have he := congrFun hz ![g, h]
    rw [differential_one] at he
    change act k G M g (z (fun _ => h)) - z (fun _ => g*h) + z (fun _ => g) = 0 at he
    calc
      z (fun _ => g*h) = z (fun _ => g*h) +
          (act k G M g (z (fun _ => h)) - z (fun _ => g*h) + z (fun _ => g)) := by rw [he, add_zero]
      _ = _ := by abel

private def oneCyclesEquiv (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    (complex k G h M).cycles 1 ≃ₗ[k] crossed k G M := by
  let K := complex k G h M
  let E : TupleCochain k G M 1 ≃ₗ[k] (G → M) :=
    LinearEquiv.funCongrLeft k M (Equiv.funUnique (Fin 1) G).symm
  refine LinearEquiv.ofBijective
    ((E.toLinearMap.comp (K.iCycles 1).hom).codRestrict _ (fun z => ?_)) ⟨?_, ?_⟩
  · apply (isCrossed_iff k G M _).mpr
    rw [← rawDifferential k G h]
    exact congrArg (fun f : K.cycles 1 ⟶ K.X 2 => f.hom z) (K.iCycles_d 1 2)
  · intro z z' hzz
    apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (K.iCycles 1))
    exact E.injective (congrArg Subtype.val hzz)
  · intro f
    obtain ⟨z, hz⟩ := E.surjective f.val
    have hc : E z ∈ crossed k G M := hz.symm ▸ f.property
    have hd : differential k G M 1 z = 0 := (isCrossed_iff k G M z).mp hc
    have hd' : (K.d 1 2).hom z = 0 := (rawDifferential k G h M 1 z).trans hd
    refine ⟨K.cyclesMk z 2 (by simp) hd', Subtype.ext ?_⟩
    change E ((K.iCycles 1).hom (K.cyclesMk z 2 _ hd')) = f.val
    rw [cyclesMk_apply]
    exact hz

open private differential_zero_apply from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

private lemma oneCyclesEquiv_boundaries (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    (((complex k G h M).toCycles 0 1).hom.range).map (oneCyclesEquiv k G h M).toLinearMap =
      boundaries k G M := by
  let K := complex k G h M
  let E : TupleCochain k G M 0 ≃ₗ[k] M := LinearEquiv.funUnique (Fin 0 → G) k M
  rw [← LinearMap.range_comp]
  have he : (oneCyclesEquiv k G h M).toLinearMap.comp (K.toCycles 0 1).hom =
      (principal k G M).comp E.toLinearMap := by
    ext y g
    change ((K.iCycles 1).hom ((K.toCycles 0 1).hom y)) (fun _ => g) =
      act k G M g (E y) - E y
    have hi : (K.iCycles 1).hom ((K.toCycles 0 1).hom y) = (K.d 0 1).hom y :=
      congrArg (fun f : K.X 0 ⟶ K.X 1 => f.hom y) (K.toCycles_i 0 1)
    rw [hi]
    rw [show (K.d 0 1).hom y = differential k G M 0 y from rawDifferential k G h M 0 y]
    exact differential_zero_apply k G M y (fun _ => g)
  change LinearMap.range ((oneCyclesEquiv k G h M).toLinearMap.comp (K.toCycles 0 1).hom) = _
  rw [he, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range E)]

private def oneKernelQuotientIso (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    (rawCohomology k G h 1).obj M ≅
      ModuleCat.of k ((complex k G h M).cycles 1 ⧸ ((complex k G h M).toCycles 0 1).hom.range) :=
  ((complex k G h M).homologyIsCokernel (i := 0) (j := 1) (by simp)).coconePointUniqueUpToIso
    (ModuleCat.cokernelIsColimit ((complex k G h M).toCycles 0 1))

private def oneIso (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    (rawCohomology k G h 1).obj M ≅ ModuleCat.of k (quotient k G M) :=
  oneKernelQuotientIso k G h M ≪≫
    (Submodule.Quotient.equiv _ _ (oneCyclesEquiv k G h M)
      (oneCyclesEquiv_boundaries k G h M)).toModuleIso

private lemma oneIso_on_cycles (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G)
    (z : (complex k G h M).cycles 1) :
    (oneIso k G h M).hom (((complex k G h M).homologyπ 1).hom z) =
      (boundaries k G M).mkQ (oneCyclesEquiv k G h M z) := by
  let K := complex k G h M
  have hi := IsColimit.comp_coconePointUniqueUpToIso_hom
    (K.homologyIsCokernel (i := 0) (j := 1) (by simp))
    (ModuleCat.cokernelIsColimit (K.toCycles 0 1)) WalkingParallelPair.one
  have hz : (oneKernelQuotientIso k G h M).hom.hom ((K.homologyπ 1).hom z) =
      ((K.toCycles 0 1).hom.range).mkQ z := congrArg (fun f => f.hom z) hi
  change (Submodule.Quotient.equiv _ _ (oneCyclesEquiv k G h M)
    (oneCyclesEquiv_boundaries k G h M)) ((oneKernelQuotientIso k G h M).hom.hom
      ((K.homologyπ 1).hom z)) = _
  rw [hz]
  rfl

private lemma oneIdentification_holds (h : SquareZero.{u,v,w} k G) :
    oneIdentification k G (oneIso k G h) := by
  constructor
  · intro M N a
    let KM := complex k G h M
    let KN := complex k G h N
    let f := (raw k G h).map a
    apply (cancel_epi (KM.homologyπ 1)).mp
    change KM.homologyπ 1 ≫ HomologicalComplex.homologyMap f 1 ≫ (oneIso k G h N).hom =
      KM.homologyπ 1 ≫ (oneIso k G h M).hom ≫ quotientMap k G a
    rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (oneIso k G h N).hom ((KN.homologyπ 1).hom
      ((HomologicalComplex.cyclesMap f 1).hom z)) =
      (quotientMap k G a).hom ((oneIso k G h M).hom ((KM.homologyπ 1).hom z))
    rw [oneIso_on_cycles, oneIso_on_cycles]
    apply congrArg (boundaries k G N).mkQ
    apply Subtype.ext
    funext g
    have he := congrArg (fun b => b.hom z) (HomologicalComplex.cyclesMap_i f 1)
    exact congrFun he (fun _ => g)
  · intro M z hz
    let K := complex k G h M
    let s := K.cyclesMk z 2 (by simp) ((rawDifferential k G h M 1 z).trans hz)
    refine ⟨oneCyclesEquiv k G h M s, ?_, oneIso_on_cycles k G h M s⟩
    intro g
    change (K.iCycles 1).hom s (fun _ => g) = _
    exact congrFun (cyclesMk_apply K 1 z _) _


private theorem originalLowDegrees (h : SquareZero.{u,v,w} k G)
    (e : ∀ n, derived.{u,v,w} k G n ≅ rawCohomology k G h n ⋙ scalarLift.{u,v,w} k)
    (e₀ : invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k ≅ rawCohomology k G h 0)
    (e₁ : ∀ M : Coeff.{u,v,w} k G,
      (rawCohomology k G h 1).obj M ≅ ModuleCat.of k (quotient k G M))
    (he₁ : oneIdentification k G e₁) : OriginalLowDegrees k G e e₀ e₁ := by
  have hn (n : ℕ) {M N : Coeff.{u,v,w} k G} (b : M ⟶ N) (x : (derived k G n).obj M) :
      (((e n).hom.app N).hom (((derived k G n).map b).hom x)).down =
        ((rawCohomology k G h n).map b).hom (((e n).hom.app M).hom x).down :=
    congrArg (fun f => (f.hom x).down) ((e n).hom.naturality b)
  refine ⟨?_, ?_, ?_⟩
  · intro M N b x
    change ((e₀.inv.app N).hom (((e 0).hom.app N).hom (((derived k G 0).map b).hom x)).down).down =
      ((invariantsFunctor k G).map b).hom ((e₀.inv.app M).hom (((e 0).hom.app M).hom x).down).down
    rw [hn]
    exact congrArg (fun f => (f.hom (((e 0).hom.app M).hom x).down).down) (e₀.inv.naturality b)
  · intro M N b x
    change (e₁ N).hom.hom (((e 1).hom.app N).hom (((derived k G 1).map b).hom x)).down =
      (quotientMap k G b).hom ((e₁ M).hom.hom (((e 1).hom.app M).hom x).down)
    rw [hn]
    exact congrArg (fun f => f.hom (((e 1).hom.app M).hom x).down) (he₁.1 M N b)
  · intro M z hz
    obtain ⟨f, hf, hef⟩ := he₁.2 M z hz
    refine ⟨f, hf, ?_⟩
    let c := ULift.up (classOf k G h M 1 z hz)
    have hc : ((e 1).hom.app M).hom (((e 1).inv.app M).hom c) = c :=
      congrArg (fun f => f.hom c) ((e 1).inv_hom_id_app M)
    change (e₁ M).hom.hom (((e 1).hom.app M).hom (((e 1).inv.app M).hom c)).down = _
    rw [hc]
    exact hef

open private uliftHomology_class from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

private lemma scalarHomology_class (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G)
    (n : ℕ) (x : (complex k G h M).cycles n) (y : ((lifted k G h).obj M).cycles n)
    (he : (((lifted k G h).obj M).iCycles n).hom y = ULift.up (((complex k G h M).iCycles n).hom x)) :
    (((rawHomologyLiftIso.{u,v,w} k G n).hom.app M).hom
      ((((lifted k G h).obj M).homologyπ n).hom y)) =
      ULift.up (((complex k G h M).homologyπ n).hom x) :=
  uliftHomology_class ((complex k G h M).sc n) x y he

private lemma scalarLift_boundary (h : SquareZero.{u,v,w} k G) (hex : RawExact k G h)
    {S : ShortComplex (Coeff.{u,v,w} k G)} (hS : S.ShortExact) (n : ℕ)
    (hs : (S.map (lifted k G h)).ShortExact) :
    hs.δ n (n+1) rfl ≫ (rawHomologyLiftIso.{u,v,w} k G (n+1)).hom.app S.X₁ =
      (rawHomologyLiftIso.{u,v,w} k G n).hom.app S.X₃ ≫
        (scalarLift.{u,v,w} k).map (rawBoundary k G (hex hS) n) := by
  let T := S.map (lifted k G h)
  let hπ := T.X₃.homologyπ n
  apply (cancel_epi hπ).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let z : TupleCochain k G S.X₃ n := ((T.X₃.iCycles n).hom s).down
  have hzup : (T.X₃.d n (n+1)).hom (ULift.up z) = 0 :=
    congrArg (fun f : T.X₃.cycles n ⟶ T.X₃.X (n+1) => f.hom s) (T.X₃.iCycles_d n (n+1))
  have hz : differential k G S.X₃ n z = 0 := by
    have hd : ((complex k G h S.X₃).d n (n+1)).hom z = 0 := congrArg ULift.down hzup
    exact (rawDifferential k G h S.X₃ n z).symm.trans hd
  obtain ⟨⟨y, x, hy, hx⟩, hformula⟩ := (liftedBoundary k G h hex hS n).2 z hz
  obtain ⟨hxd, hr⟩ := hformula y x hy hx
  have hyup : (T.g.f n).hom (ULift.up y) = ULift.up z := congrArg ULift.up (funext hy)
  have hxup : (T.f.f (n+1)).hom (ULift.up x) = (T.X₂.d n (n+1)).hom (ULift.up y) :=
    congrArg ULift.up ((funext hx).trans (rawDifferential k G h S.X₂ n y).symm)
  have hxd' : ((complex k G h S.X₁).d (n+1) (n+2)).hom x = 0 :=
    (rawDifferential k G h S.X₁ (n+1) x).trans hxd
  have hxdup : (T.X₁.d (n+1) (n+2)).hom (ULift.up x) = 0 := congrArg ULift.up hxd'
  have hδ := hs.δ_apply n (n+1) rfl (ULift.up z) hzup (ULift.up y) hyup (ULift.up x) hxup
    (n+2) (by simp)
  let sx := (complex k G h S.X₁).cyclesMk x (n+2) (by simp) hxd'
  let su := T.X₁.cyclesMk (ULift.up x) (n+2) (by simp) hxdup
  let sz := (complex k G h S.X₃).cyclesMk z (n+1) (by simp) ((rawDifferential k G h S.X₃ n z).trans hz)
  have hzclass := scalarHomology_class k G h S.X₃ n sz s
    (congrArg ULift.up (cyclesMk_apply (complex k G h S.X₃) n z _).symm)
  have hxclass := scalarHomology_class k G h S.X₁ (n+1) sx su
    ((cyclesMk_apply T.X₁ (n+1) (ULift.up x) _).trans
      (congrArg ULift.up (cyclesMk_apply (complex k G h S.X₁) (n+1) x _).symm))
  have hs' : T.X₃.cyclesMk (ULift.up z) (n+1) (by simp) hzup = s :=
    (ModuleCat.mono_iff_injective (T.X₃.iCycles n)).mp inferInstance
      (cyclesMk_apply T.X₃ n (ULift.up z) hzup)
  change (hs.δ n (n+1) rfl).hom ((T.X₃.homologyπ n).hom
    (T.X₃.cyclesMk (ULift.up z) (n+1) (by simp) hzup)) = (T.X₁.homologyπ (n+1)).hom su at hδ
  rw [hs'] at hδ
  change ((rawHomologyLiftIso k G (n+1)).hom.app S.X₁).hom
      ((hs.δ n (n+1) rfl).hom (hπ.hom s)) =
    ((scalarLift.{u,v,w} k).map (rawBoundary k G (hex hS) n)).hom
      (((rawHomologyLiftIso k G n).hom.app S.X₃).hom (hπ.hom s))
  change ((rawHomologyLiftIso k G (n+1)).hom.app S.X₁).hom ((T.X₁.homologyπ (n+1)).hom su) = _ at hxclass
  change ((rawHomologyLiftIso k G n).hom.app S.X₃).hom ((T.X₃.homologyπ n).hom s) = _ at hzclass
  rw [show hπ = T.X₃.homologyπ n from rfl, hδ, hxclass, hzclass]
  exact congrArg ULift.up hr.symm


private lemma homologyMap_class {r : Type u} [CommRing r]
    {K L : CochainComplex (ModuleCat.{w} r) ℕ} (f : K ⟶ L) (n : ℕ) (x : K.cycles n) :
    (HomologicalComplex.homologyMap f n).hom ((K.homologyπ n).hom x) =
      (L.homologyπ n).hom ((HomologicalComplex.cyclesMap f n).hom x) :=
  congrArg (fun p => p.hom x) (HomologicalComplex.homologyπ_naturality f n)

/-- The HA-A01-Carrier comparison on the homogeneous bar complexes of
the lifted coefficients. -/
def normalizedAmbientIso (n : ℕ) : derived.{u,v,w} k G n ≅ ambientBarCohomology k G n :=
  Functor.isoWhiskerLeft (lift k G)
      ((GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,w} k G).iso n) ≪≫
    (Functor.associator _ _ _).symm

/-- The normalized comparison is transported along the pointwise cochain isomorphism. -/
private theorem derivedAgreementFor (h : SquareZero.{u,v,w} k G) (hex : RawExact k G h)
    (ae : AmbientExact.{u,v,w} k G) (b : lifted k G h ≅ ambientBar.{u,v,w} k G)
    (hb : Pointwise k G b) : DerivedAgreement k G hex ae b := by
  obtain ⟨e₀, he₀⟩ := zeroIdentification_exists k G h
  let a := normalizedAmbientIso.{u,v,w} k G
  let e (n : ℕ) : derived.{u,v,w} k G n ≅ rawCohomology k G h n ⋙ scalarLift.{u,v,w} k :=
    a n ≪≫ (Functor.isoWhiskerRight b.symm _ ≪≫ rawHomologyLiftIso k G n)
  refine ⟨a, e, e₀, oneIso k G h, he₀, oneIdentification_holds k G h,
    originalLowDegrees k G h e e₀ _ (oneIdentification_holds k G h), fun _ _ => rfl, ?_, ?_⟩
  · intro M m
    let I := lift.{u,v,w} k G
    let E := GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,w} k G
    let B := (ambientBar k G).obj M
    let K := complex k G h M
    let L := (lifted k G h).obj M
    let f : B ⟶ L := b.inv.app M
    let unit := Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.degreeZeroUnit.{u,v,w} k G
    let t : B.homology 0 := ((a 0).hom.app M).hom ((unit.app (I.obj M)).hom m)
    obtain ⟨z, hz, hcoord, hclass⟩ := E.degreeZero (I.obj M) m
    let y : B.cycles 0 := B.cyclesMk z 1 (by simp) hz
    have ht : t = (B.homologyπ 0).hom y := hclass
    have hvertex : Fin.partialProd (Fin.elim0 : Fin 0 → G) = fun _ => 1 := by
      funext g
      rw [Fin.eq_zero g, Fin.partialProd_zero]
    let m₀ : invariants k G M := ⟨m.val.down, fun g => congrArg ULift.down (m.property g)⟩
    obtain ⟨hx, he⟩ := he₀ M m₀
    let s : L.cycles 0 := (HomologicalComplex.cyclesMap f 0).hom y
    have hi : (L.iCycles 0).hom s = ULift.up (fun _ => m₀.val) := by
      have hs : (L.iCycles 0).hom s = (f.f 0).hom ((B.iCycles 0).hom y) :=
        congrArg (fun p => p.hom y) (HomologicalComplex.cyclesMap_i f 0)
      rw [hs, show (B.iCycles 0).hom y = z from cyclesMk_apply B 0 z hz]
      apply ULift.ext
      funext g
      obtain rfl : g = Fin.elim0 := Subsingleton.elim _ _
      have hpoint := hb.2 M 0 z Fin.elim0
      have hc : z.hom (GroupBar.Large.single.{u,v,w} k G (fun _ : Fin 1 => 1) 1) = m.val :=
        hcoord
      refine hpoint.trans ?_
      have hv := congrArg (fun v : Fin 1 → G =>
        (z.hom (GroupBar.Large.single.{u,v,w} k G v 1)).down) hvertex
      exact hv.trans (congrArg ULift.down hc)
    let x := K.cyclesMk (i := 0) (fun _ => m₀.val) 1 (by simp)
      ((rawDifferential k G h M 0 _).trans hx)
    have hix : (L.iCycles 0).hom s = ULift.up ((K.iCycles 0).hom x) :=
      hi.trans (congrArg ULift.up (cyclesMk_apply K 0 _ _).symm)
    change ((rawHomologyLiftIso k G 0).hom.app M).hom
      ((HomologicalComplex.homologyMap f 0).hom t) = ULift.up ((e₀.hom.app M).hom (ULift.up m₀))
    rw [ht, homologyMap_class, he]
    exact scalarHomology_class k G h M 0 x s hix
  · intro S hS n
    have ha : derivedBoundary k G hS n ≫ (a (n+1)).hom.app S.X₁ =
        (a n).hom.app S.X₃ ≫ (ae hS).δ n (n+1) rfl :=
      (GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,w} k G).boundary
        (hS.map_of_exact (lift k G)) n
    refine ⟨ha, ?_⟩
    have hs : (S.map (lifted k G h)).ShortExact :=
      (hex hS).map_of_exact ((scalarLift.{u,v,w} k).mapHomologicalComplex (.up ℕ))
    have hn := HomologicalComplex.HomologySequence.δ_naturality
      (S.mapNatTrans b.inv) (ae hS) hs n (n+1) rfl
    change (ae hS).δ n (n+1) rfl ≫ HomologicalComplex.homologyMap (b.inv.app S.X₁) (n+1) =
      HomologicalComplex.homologyMap (b.inv.app S.X₃) n ≫ hs.δ n (n+1) rfl at hn
    change derivedBoundary k G hS n ≫ (a (n+1)).hom.app S.X₁ ≫
        HomologicalComplex.homologyMap (b.inv.app S.X₁) (n+1) ≫
          (rawHomologyLiftIso k G (n+1)).hom.app S.X₁ =
      ((a n).hom.app S.X₃ ≫ HomologicalComplex.homologyMap (b.inv.app S.X₃) n ≫
        (rawHomologyLiftIso k G n).hom.app S.X₃) ≫
          (scalarLift.{u,v,w} k).map (rawBoundary k G (hex hS) n)
    rw [← Category.assoc (derivedBoundary k G hS n), ha, Category.assoc, ← Category.assoc ((ae hS).δ _ _ _),
      hn]
    simp only [Category.assoc, scalarLift_boundary k G h hex hS n hs]

theorem derivedAgreement : derivedAgreementType.{u,v,w} k G := by
  let h := squareZero.{u,v,w} k G
  have hex : RawExact k G h := (rawExact k G h).1
  have ae : AmbientExact.{u,v,w} k G := ambientExact k G
  obtain ⟨b, hb, hseq⟩ := sequenceComparison k G h
  exact ⟨h, hex, ae, b, hb, hseq, derivedAgreementFor k G h hex ae b hb⟩

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence.Mixed

open CategoryTheory
open scoped MonoidAlgebra ModuleCat.Algebra
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence.Mixed
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open GroupCochainComparison.LargeCoordinates (coordinatesEquiv)
open private differential_coordinates from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCochainComparison
open private uliftHomology_class from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

universe u v a b c a' b' c' s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]
variable {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G} {P : Coeff.{u,v,c} k G}
variable {hM : SquareZero.{u,v,a} k G} {hN : SquareZero.{u,v,b} k G}
  {hP : SquareZero.{u,v,c} k G}

private theorem pointwiseExact {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (h : ShortExact k G i p) : Mixed.rawExactType k G i p := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro x y eq
    exact funext fun g => h.injective (congrFun eq g)
  · intro y
    constructor
    · intro hy
      choose x hx using fun g => (h.exact (y g)).mp (congrFun hy g)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun g => h.exact.apply_apply_eq_zero (x g)
  · intro z
    choose y hy using fun g : Fin n → G => h.surjective (z g)
    exact ⟨y, funext hy⟩

private theorem representatives (M : Coeff.{u,v,a} k G) (hM : SquareZero.{u,v,a} k G) :
    HasRepresentatives k G M hM := by
  intro n x
  obtain ⟨z, hz, eq⟩ := cocycleRepresentatives (rawComplex k G hM M) n x
  exact ⟨z, (rawDifferential k G hM M n z).symm.trans hz, eq⟩

private theorem lifts_exist {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (h : ShortExact k G i p) (n : ℕ) (z : TupleCochain k G P n)
    (hz : differential k G P n z = 0) :
    ∃ y x, Lifts k G i p n z y x := by
  obtain ⟨y, hy⟩ := (pointwiseExact k G h n).2.2 z
  have hd : post k G p (n+1) (differential k G N n y) = 0 := by
    rw [← post_differential, hy, hz]
  obtain ⟨x, hx⟩ := ((pointwiseExact k G h (n+1)).2.1 _).mp hd
  exact ⟨y, x, congrFun hy, congrFun hx⟩

private lemma commonDifferential (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G)
    (n : ℕ) (z : (commonRaw.{u,v,a,s} k G hM M).X n) :
    ((commonRaw.{u,v,a,s} k G hM M).d n (n+1)).hom z =
      ULift.up (differential k G M n z.down) := by
  simp only [commonRaw, Functor.mapHomologicalComplex_obj_d, rawComplex, CochainComplex.of_d]
  rfl

private lemma liftCycle (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G)
    (n : ℕ) (z : TupleCochain k G M n) (hz : differential k G M n z = 0) :
    ((commonRaw.{u,v,a,s} k G hM M).d n (n+1)).hom (ULift.up z) = 0 :=
  (commonDifferential.{u,v,a,s} k G hM M n (ULift.up z)).trans (congrArg ULift.up hz)

private abbrev liftedCoeff (M : Coeff.{u,v,a} k G) :=
  commonCoeff.{u,v,a,max u v a s} k G M

private def liftTuples (M : Coeff.{u,v,a} k G) (n : ℕ) :
    ULift.{max u v a s} (TupleCochain k G M n) ≃ₗ[k]
      Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.coordinates.{u,v,max a s}
        k G (liftedCoeff.{u,v,a,s} k G M) n where
  toFun z g := ULift.up (z.down g)
  invFun z := ULift.up (fun g => (z g).down)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def termComparison (M : Coeff.{u,v,a} k G) (n : ℕ) :
    ULift.{max u v a s} (TupleCochain k G M n) ≃ₗ[k] (commonBar.{u,v,a,s} k G M).X n :=
  (liftTuples.{u,v,a,s} k G M n).trans
    (coordinatesEquiv.{u,v,max a s} k G (liftedCoeff.{u,v,a,s} k G M) n).symm

private lemma termComparison_coordinates (M : Coeff.{u,v,a} k G) (n : ℕ)
    (z : ULift.{max u v a s} (TupleCochain k G M n)) (g : Fin n → G) :
    ambientCoordinates.{u,v,a,s} k G M n (termComparison.{u,v,a,s} k G M n z) g =
      ULift.up (z.down g) := by
  let ev := coordinatesEquiv.{u,v,max a s} k G (liftedCoeff.{u,v,a,s} k G M) n
  change ev (ev.symm (liftTuples.{u,v,a,s} k G M n z)) g = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private def compareBar (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G) :
    BarComparison.{u,v,a,s} k G hM M := by
  let e : commonRaw.{u,v,a,s} k G hM M ≅ commonBar.{u,v,a,s} k G M :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => (termComparison.{u,v,a,s} k G M n).toModuleIso) (by
        intro i j hij
        obtain rfl : j = i + 1 := hij.symm
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change ULift.{max u v a s} (TupleCochain k G M i) at z
        symm
        apply (coordinatesEquiv.{u,v,max a s} k G (liftedCoeff.{u,v,a,s} k G M) (i+1)).injective
        funext g
        change ambientCoordinates.{u,v,a,s} k G M _ (termComparison.{u,v,a,s} k G M _
          (((commonRaw.{u,v,a,s} k G hM M).d i (i+1)).hom z)) g =
          coordinatesEquiv.{u,v,max a s} k G (liftedCoeff.{u,v,a,s} k G M) _ (((commonBar.{u,v,a,s} k G M).d i (i+1)).hom
            (termComparison.{u,v,a,s} k G M i z)) g
        rw [commonDifferential.{u,v,a,s}, termComparison_coordinates.{u,v,a,s},
          differential_coordinates]
        simp only [differential_apply]
        change _ = Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential
          k G (liftedCoeff.{u,v,a,s} k G M) i (ambientCoordinates.{u,v,a,s} k G M i (termComparison.{u,v,a,s} k G M i z)) g
        simp only [Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential,
          termComparison_coordinates]
        let up : M →ₗ[k] commonCoeff.{u,v,a,max u v a s} k G M :=
          ((down.{u,v,a,max u v a s} k G M).symm.restrictScalars k).toLinearMap
        change up (_ + _ + _) = _
        simp only [map_add, map_sum, map_smul]
        rfl)
  refine ⟨e, fun n z g => termComparison_coordinates.{u,v,a,s} k G M n _ g, ?_⟩
  intro n φ g
  have eq := termComparison_coordinates.{u,v,a,s} k G M n
    ((termComparison.{u,v,a,s} k G M n).symm φ) g
  rw [LinearEquiv.apply_symm_apply] at eq
  exact congrArg ULift.down eq.symm

private lemma liftedRaw_shortExact {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (h : ShortExact k G i p) :
    (commonRawSequence.{u,v,a,b,c,s} k G (hM := hM) (hN := hN) (hP := hP) h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hex := pointwiseExact k G h n
  exact ModuleCat.shortComplexOfConj_shortExact
    (eM := ULift.moduleEquiv.{u,max v a,max u v a b c s})
    (eN := ULift.moduleEquiv.{u,max v b,max u v a b c s})
    (eL := ULift.moduleEquiv.{u,max v c,max u v a b c s})
    (f := post k G i n) (g := post k G p n) hex.2.1 hex.1 hex.2.2

theorem sequenceComparison : Mixed.sequenceComparisonExpected.{u,v,a,b,c,s} := by
  intro k G _ _ M N P hM hN hP i p h
  let S := commonSequence.{u,v,a,b,c,s} k G h
  have hS : S.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact (down.{u,v,a,max u v a b c s} k G M)
      (down.{u,v,b,max u v a b c s} k G N) (down.{u,v,c,max u v a b c s} k G P)
      i p h.exact h.injective h.surjective
  let eM := compareBar.{u,v,a,max a b c s} k G hM M
  let eN := compareBar.{u,v,b,max a b c s} k G hN N
  let eP := compareBar.{u,v,c,max a b c s} k G hP P
  let B := S.map (ambient.{u,v,max a b c s} k G)
  let A := commonRawSequence.{u,v,a,b,c,s} k G (hM := hM) (hN := hN) (hP := hP) h
  let e : A ≅ B := ShortComplex.isoMk eM.iso eN.iso eP.iso (by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    symm
    apply (coordinatesEquiv.{u,v,max a b c s} k G _ n).injective
    funext g
    change ambientCoordinates.{u,v,b,max a b c s} k G N n ((eN.iso.hom.f n).hom (ULift.up (post k G i n φ.down))) g =
      S.f.hom (ambientCoordinates.{u,v,a,max a b c s} k G M n ((eM.iso.hom.f n).hom φ) g)
    rw [eN.forward, show φ = ULift.up φ.down from rfl, eM.forward]
    rfl) (by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    symm
    apply (coordinatesEquiv.{u,v,max a b c s} k G _ n).injective
    funext g
    change ambientCoordinates.{u,v,c,max a b c s} k G P n ((eP.iso.hom.f n).hom (ULift.up (post k G p n φ.down))) g =
      S.g.hom (ambientCoordinates.{u,v,b,max a b c s} k G N n ((eN.iso.hom.f n).hom φ) g)
    rw [eP.forward, show φ = ULift.up φ.down from rfl, eN.forward]
    rfl)
  exact ⟨hS, GroupCohomologyOriginalCoefficients.NormalizedBar.shortExact k G hS,
    liftedRaw_shortExact.{u,v,a,b,c,s} k G h, eM, eN, eP, e, rfl, rfl, rfl⟩

private abbrev cochainClass {r : Type u} [CommRing r]
    (K : CochainComplex (ModuleCat.{a} r) ℕ) (n : ℕ) (z : K.X n)
    (hz : (K.d n (n+1)).hom z = 0) : K.homology n :=
  (K.homologyπ n).hom (K.cyclesMk z (n+1) (by simp) hz)

private lemma map_cochainClass {r : Type u} [CommRing r]
    {K L : CochainComplex (ModuleCat.{a} r) ℕ} (f : K ⟶ L) (n : ℕ)
    (z : K.X n) (hz : (K.d n (n+1)).hom z = 0) (y : L.X n)
    (hy : (L.d n (n+1)).hom y = 0) (h : (f.f n).hom z = y) :
    (HomologicalComplex.homologyMap f n).hom (cochainClass K n z hz) =
      cochainClass L n y hy := by
  rw [cochainClass, homologyMap_class]
  apply congrArg (L.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  rw [cyclesMk_apply]
  change (HomologicalComplex.cyclesMap f n ≫ L.iCycles n).hom _ = y
  rw [HomologicalComplex.cyclesMap_i]
  change (f.f n).hom ((K.iCycles n).hom _) = y
  rw [cyclesMk_apply, h]

private def scalarEquiv (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G) (n : ℕ) :
    H k G (M := M) hM n ≃ₗ[k] (commonRaw.{u,v,a,s} k G hM M).homology n :=
  ULift.moduleEquiv.symm.trans
    (((rawComplex k G hM M).sc n).mapHomologyIso (toCommonScalars.{u,v,a,s} k)).symm.toLinearEquiv

private lemma scalarEquiv_class (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G)
    (n : ℕ) (z : TupleCochain k G M n) (hz : differential k G M n z = 0) :
    scalarEquiv.{u,v,a,s} k G hM M n (classOf k G hM M n z hz) =
      cochainClass (commonRaw.{u,v,a,s} k G hM M) n (ULift.up z) (liftCycle.{u,v,a,s} k G hM M n z hz) := by
  let K := rawComplex k G hM M
  let L := commonRaw.{u,v,a,s} k G hM M
  let hx : (K.d n (n+1)).hom z = 0 := (rawDifferential k G hM M n z).trans hz
  let hy : (L.d n (n+1)).hom (ULift.up z) = 0 := liftCycle.{u,v,a,s} k G hM M n z hz
  let x := K.cyclesMk z (n+1) (by simp) hx
  let y := L.cyclesMk (ULift.up z) (n+1) (by simp) hy
  have he : (L.iCycles n).hom y = ULift.up ((K.iCycles n).hom x) := by
    dsimp only [x, y]
    rw [cyclesMk_apply, cyclesMk_apply]
  let e := ((K.sc n).mapHomologyIso (toCommonScalars.{u,v,a,s} k)).toLinearEquiv
  change e.symm (ULift.up ((K.homologyπ n).hom x)) = (L.homologyπ n).hom y
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (uliftHomology_class.{u,max u v a s,max v a} (K.sc n) x y he).symm

open AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
  (barResolution originalBarCoordinates originalBarCoordinates_apply originalBarCoordinates_d)
open P103.Specs.Ch10.Complexes (cycles homologyClass)
open P103.Specs.Ch11.ExtTorDefinitions (homComplex)

/-- The coefficient-sequence comparison on original tuple classes agrees
with the projective comparison on the very same original bar cocycle. -/
theorem barHomology_projectiveClass (e : BarComparison.{u,v,a,s} k G hM M) (n : ℕ)
    (z : cycles (homComplex (barResolution k G).complex M) n) :
    let t := originalBarCoordinates k G M n z.val
    ∃ ht : differential k G M n t = 0,
      e.homology n (classOf k G hM M n t ht) =
        (GroupCohomologyOriginalCoefficients.MixedProjective.compareBar.{u,v,a,max a s} k G M
          (liftedCoeff.{u,v,a,s} k G M) (down.{u,v,a,max u v a s} k G M).symm).classes n
          (homologyClass _ n z) := by
  let t := originalBarCoordinates k G M n z.val
  have hz := z.property
  change ((homComplex (barResolution k G).complex M).d n ((ComplexShape.up ℕ).next n)).hom z.val = 0 at hz
  rw [CochainComplex.next] at hz
  change z.val.comp ((originalBar k G).d (n+1) n).hom = 0 at hz
  have ht : differential k G M n t = 0 := by
    dsimp only [t]
    rw [← originalBarCoordinates_d, hz, map_zero]
  refine ⟨ht, ?_⟩
  let C := commonBar.{u,v,a,s} k G M
  let J := GroupCohomologyOriginalCoefficients.MixedProjective.compareBar.{u,v,a,max a s} k G M
    (liftedCoeff.{u,v,a,s} k G M) (down.{u,v,a,max u v a s} k G M).symm
  obtain ⟨y, hy, hclass⟩ := J.class_formula n z
  have he : (e.iso.hom.f n).hom (ULift.up t) = (C.iCycles n).hom y := by
    rw [show (C.iCycles n).hom y = J.cochain.app n z.val from hy]
    apply (coordinatesEquiv.{u,v,max a s} k G (liftedCoeff.{u,v,a,s} k G M) n).injective
    funext g
    have hJ := J.coordinates n z.val g
    change ambientCoordinates.{u,v,a,s} k G M n (J.cochain.app n z.val) g =
      ULift.up ((show (originalBar k G).X n →ₗ[k[G]] M from z.val)
        (basisElement k G n (Fin.partialProd g))) at hJ
    exact (e.forward n t g).trans ((congrArg ULift.up
      (originalBarCoordinates_apply k G M n z.val g)).trans hJ.symm)
  let hdy : (C.d n (n+1)).hom ((C.iCycles n).hom y) = 0 :=
    congrArg (fun f : C.cycles n ⟶ C.X (n+1) => f.hom y) (C.iCycles_d n (n+1))
  change (HomologicalComplex.homologyMap e.iso.hom n).hom
      (scalarEquiv.{u,v,a,s} k G hM M n (classOf k G hM M n t ht)) =
    J.classes n (homologyClass _ n z)
  rw [scalarEquiv_class, hclass]
  refine (map_cochainClass _ _ _ _ _ hdy he).trans ?_
  apply congrArg (C.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
  exact cyclesMk_apply C n _ hdy

private def inducedMapAt (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G)
    (f : M →ₗ[k[G]] N) : InducedMap k G hM hN f where
  hom n := ((scalarEquiv.{u,v,b,max a s} k G hN N n).symm.toLinearMap.comp
    (HomologicalComplex.homologyMap (commonPost.{u,v,a,b,s} k G (hM := hM) (hN := hN) f) n).hom).comp
      (scalarEquiv.{u,v,a,max b s} k G hM M n).toLinearMap
  on_class n z hz := by
    apply (scalarEquiv.{u,v,b,max a s} k G hN N n).injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, scalarEquiv_class]
    exact map_cochainClass _ _ _ _ _ _ rfl

private theorem liftedInitial {r : Type u} [CommRing r]
    {K L : CochainComplex (ModuleCat.{a} r) ℕ} (f : K ⟶ L) [Mono (f.f 0)] :
    Function.Injective (HomologicalComplex.homologyMap f 0).hom := by
  have (C : CochainComplex (ModuleCat.{a} r) ℕ) : IsIso (C.homologyπ 0) :=
    HomologicalComplex.isIso_homologyπ _ 0 0 (by rw [GroupCochainComparison.ResolutionBridge.prev_up_nat])
      (C.shape 0 0 (by decide))
  have : Mono (HomologicalComplex.cyclesMap f 0) := mono_of_mono _ (L.iCycles 0)
  apply (ModuleCat.mono_iff_injective _).mp
  have eq : HomologicalComplex.homologyMap f 0 =
      inv (K.homologyπ 0) ≫ HomologicalComplex.cyclesMap f 0 ≫ L.homologyπ 0 := by
    rw [← HomologicalComplex.homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [eq]
  infer_instance

private theorem fromConjugateExact {r : Type u} [CommRing r]
    {X : ModuleCat.{a} r} {Y : ModuleCat.{b} r} {Z : ModuleCat.{c} r}
    {X' Y' Z' : ModuleCat.{s} r} (eX : X ≃ₗ[r] X') (eY : Y ≃ₗ[r] Y') (eZ : Z ≃ₗ[r] Z')
    (f : X' ⟶ Y') (g : Y' ⟶ Z') (h : Function.Exact f.hom g.hom) :
    Function.Exact ((eY.symm.toLinearMap.comp f.hom).comp eX.toLinearMap)
      ((eZ.symm.toLinearMap.comp g.hom).comp eY.toLinearMap) := by
  change Function.Exact (eY.symm.comp f.hom ∘ₗ eX.toLinearMap)
    (eZ.symm.comp (g.hom ∘ₗ eY.toLinearMap))
  rwa [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.postcomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact]

private def makeSequence {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (h : ShortExact k G i p) : Sequence k G hM hN hP i p := by
  let S := commonRawSequence.{u,v,a,b,c,0} k G (hM := hM) (hN := hN) (hP := hP) h
  let hS : S.ShortExact := liftedRaw_shortExact.{u,v,a,b,c,0} k G h
  let eM := scalarEquiv.{u,v,a,max a b c} k G hM M
  let eN := scalarEquiv.{u,v,b,max a b c} k G hN N
  let eP := scalarEquiv.{u,v,c,max a b c} k G hP P
  let δ (n : ℕ) := ((eM (n+1)).symm.toLinearMap.comp (hS.δ n (n+1) rfl).hom).comp (eP n).toLinearMap
  refine ⟨inducedMapAt.{u,v,a,b,c} k G hM hN i, inducedMapAt.{u,v,b,c,a} k G hN hP p, δ, ?_, ?_, ?_⟩
  · change Function.Injective (((eN 0).symm.toLinearMap.comp
      (HomologicalComplex.homologyMap S.f 0).hom).comp (eM 0).toLinearMap)
    have : Mono (S.f.f 0) := ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS 0).mono_f
    exact (eN 0).symm.injective.comp ((liftedInitial S.f).comp (eM 0).injective)
  · intro n
    exact ⟨fromConjugateExact (eM n) (eN n) (eP n) _ _
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₂ n)),
      fromConjugateExact (eN n) (eP n) (eM (n+1)) _ _
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₃ n (n+1) rfl)),
      fromConjugateExact (eP n) (eM (n+1)) (eN (n+1)) _ _
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₁ n (n+1) rfl))⟩
  · intro n z hz y x hxy
    have hy : (S.g.f n).hom (ULift.up y) = ULift.up z := congrArg ULift.up (funext hxy.1)
    have hx : (S.f.f (n+1)).hom (ULift.up x) = (S.X₂.d n (n+1)).hom (ULift.up y) :=
      (congrArg ULift.up (funext hxy.2)).trans (commonDifferential.{u,v,b,max a b c} k G hN N n (ULift.up y)).symm
    have hd := hS.d_eq_zero_of_f_eq_d_apply n (n+1) (ULift.up y) (ULift.up x) hx (n+2)
    have hd' : differential k G M (n+1) x = 0 := congrArg ULift.down
      ((commonDifferential.{u,v,a,max a b c} k G hM M (n+1) (ULift.up x)).symm.trans hd)
    refine ⟨hd', (eM (n+1)).injective ?_⟩
    change eM (n+1) ((eM (n+1)).symm ((hS.δ n (n+1) rfl).hom
      (eP n (classOf k G hP P n z hz)))) = eM (n+1) (classOf k G hM M (n+1) x hd')
    rw [LinearEquiv.apply_symm_apply]
    dsimp only [eP, eM]
    rw [scalarEquiv_class, scalarEquiv_class]
    exact hS.δ_apply n (n+1) rfl (ULift.up z) (liftCycle.{u,v,c,max a b c} k G hP P n z hz)
      (ULift.up y) hy (ULift.up x) hx (n+2) (by simp)

theorem longExact : Mixed.longExactExpected.{u,v,a,b,c} := by
  intro k G _ _ M N P hM hN hP
  refine ⟨representatives k G M hM, representatives k G N hN, representatives k G P hP, ?_⟩
  intro i p h
  exact ⟨pointwiseExact k G h, ⟨makeSequence k G h⟩, lifts_exist k G h⟩

private def lowDegreeIdentification (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G) :
    LowDegrees k G hM M := by
  let e := (zeroIdentification_exists k G hM).choose
  exact ⟨ULift.moduleEquiv.symm.trans (e.app M).toLinearEquiv,
    (oneIso k G hM M).toLinearEquiv, (zeroIdentification_exists k G hM).choose_spec M,
    (oneIdentification_holds k G hM).2 M⟩

theorem lowDegrees : Mixed.lowDegreesExpected.{u,v,a,b} := by
  intro k G _ _ M N hM hN
  let eM := lowDegreeIdentification k G hM M
  let eN := lowDegreeIdentification k G hN N
  refine ⟨eM, eN, fun f => ⟨inducedMapAt.{u,v,a,b,0} k G hM hN f, ?_, ?_⟩⟩
  · intro x
    obtain ⟨hx, eqx⟩ := eM.on_zero x
    obtain ⟨hy, eqy⟩ := eN.on_zero (invariantsPost k G f x)
    rw [eqx, eqy, InducedMap.on_class]
    rfl
  · intro x
    obtain ⟨z, hz, rfl⟩ := representatives k G M hM 1 x
    rw [InducedMap.on_class]
    obtain ⟨t, ht, eqt⟩ := eM.on_one z hz
    obtain ⟨t', ht', eqt'⟩ := eN.on_one (post k G f 1 z) (by rw [post_differential, hz, map_zero])
    rw [eqt, eqt']
    change (boundaries k G N).mkQ t' = (boundaries k G N).mkQ (crossedPost k G f t)
    apply congrArg (boundaries k G N).mkQ
    apply Subtype.ext
    funext g
    exact (ht' g).trans (congrArg f (ht g).symm)

theorem naturality : Mixed.naturalityExpected.{u,v,a,b,c,a',b',c'} := by
  intro k G _ _ M N P M' N' P' hM hN hP hM' hN' hP' i p i' p' α β γ h₁ h₂ h h' S T
  let A := inducedMapAt.{u,v,a,a',0} k G hM hM' α
  let B := inducedMapAt.{u,v,b,b',0} k G hN hN' β
  let C := inducedMapAt.{u,v,c,c',0} k G hP hP' γ
  refine ⟨A, B, C, fun n => ⟨?_, ?_, ?_⟩⟩
  · ext x
    obtain ⟨z, hz, rfl⟩ := representatives k G M hM n x
    simp only [LinearMap.comp_apply, InducedMap.on_class]
    congr 1
    exact funext fun g => DFunLike.congr_fun h₁ (z g)
  · ext x
    obtain ⟨z, hz, rfl⟩ := representatives k G N hN n x
    simp only [LinearMap.comp_apply, InducedMap.on_class]
    congr 1
    exact funext fun g => DFunLike.congr_fun h₂ (z g)
  · ext x
    obtain ⟨z, hz, rfl⟩ := representatives k G P hP n x
    obtain ⟨y, w, hl⟩ := lifts_exist k G h n z hz
    obtain ⟨hw, hδ⟩ := S.lift_boundary n z hz y w hl
    have hz' : differential k G P' n (post k G γ n z) = 0 := by
      rw [post_differential, hz, map_zero]
    have hl' : Lifts k G i' p' n (post k G γ n z) (post k G β n y) (post k G α (n+1) w) := by
      constructor
      · intro g
        exact (DFunLike.congr_fun h₂ (y g)).symm.trans (congrArg γ (hl.1 g))
      · intro g
        change i' (α (w g)) = differential k G N' n (post k G β n y) g
        rw [post_differential]
        exact (DFunLike.congr_fun h₁ (w g)).symm.trans (congrArg β (hl.2 g))
    obtain ⟨_, hδ'⟩ := T.lift_boundary n _ hz' _ _ hl'
    simp only [LinearMap.comp_apply, hδ, InducedMap.on_class]
    exact hδ'.symm

private lemma liftedMapAgreement (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G)
    {f : M →ₗ[k[G]] N} (F : InducedMap k G hM hN f) (n : ℕ) (x : H k G (M := M) hM n) :
    scalarEquiv.{u,v,b,max a s} k G hN N n (F.hom n x) =
      (HomologicalComplex.homologyMap (commonPost.{u,v,a,b,s} k G (hM := hM) (hN := hN) f) n).hom
        (scalarEquiv.{u,v,a,max b s} k G hM M n x) := by
  obtain ⟨z, hz, rfl⟩ := representatives k G M hM n x
  rw [F.on_class, scalarEquiv_class, scalarEquiv_class]
  exact (map_cochainClass (commonPost.{u,v,a,b,s} k G (hM := hM) (hN := hN) f)
    n (ULift.up z) _ (ULift.up (post k G f n z)) _ rfl).symm

private lemma liftedBoundaryAgreement {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (h : ShortExact k G i p) (T : Sequence k G hM hN hP i p)
    (hA : (commonRawSequence.{u,v,a,b,c,s} k G (hM := hM) (hN := hN) (hP := hP) h).ShortExact)
    (n : ℕ) (x : H k G (M := P) hP n) :
    scalarEquiv.{u,v,a,max a b c s} k G hM M (n+1) (T.boundary n x) =
      (hA.δ n (n+1) rfl).hom (scalarEquiv.{u,v,c,max a b c s} k G hP P n x) := by
  let A := commonRawSequence.{u,v,a,b,c,s} k G (hM := hM) (hN := hN) (hP := hP) h
  obtain ⟨z, hz, rfl⟩ := representatives k G P hP n x
  obtain ⟨y, w, hl⟩ := lifts_exist k G h n z hz
  obtain ⟨hw, hδ⟩ := T.lift_boundary n z hz y w hl
  rw [hδ, scalarEquiv_class, scalarEquiv_class]
  have hy : (A.g.f n).hom (ULift.up y) = ULift.up z := congrArg ULift.up (funext hl.1)
  have hx : (A.f.f (n+1)).hom (ULift.up w) = (A.X₂.d n (n+1)).hom (ULift.up y) :=
    (congrArg ULift.up (funext hl.2)).trans (commonDifferential.{u,v,b,max a b c s} k G hN N n (ULift.up y)).symm
  exact (hA.δ_apply n (n+1) rfl (ULift.up z) (liftCycle.{u,v,c,max a b c s} k G hP P n z hz)
    (ULift.up y) hy (ULift.up w) hx (n+2) (by simp)).symm

private lemma barSequenceAgreement {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (h : ShortExact k G i p) (T : Sequence k G hM hN hP i p)
    (B : Mixed.SequenceComparison.{u,v,a,b,c,s} k G hM hN hP h) :
    BarSequenceAgreement k G T B := by
  let A := commonRawSequence.{u,v,a,b,c,s} k G (hM := hM) (hN := hN) (hP := hP) h
  let S := commonSequence.{u,v,a,b,c,s} k G h
  let D := S.map (ambient.{u,v,max a b c s} k G)
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have eq := congrArg (fun f => HomologicalComplex.homologyMap f n) B.iso.hom.comm₁₂
    simp only [HomologicalComplex.homologyMap_comp, B.on_first, B.on_second] at eq
    change (HomologicalComplex.homologyMap B.second.iso.hom n).hom
      (scalarEquiv.{u,v,b,max a b c s} k G hN N n (T.inclusion.hom n x)) =
      (HomologicalComplex.homologyMap D.f n).hom ((HomologicalComplex.homologyMap B.first.iso.hom n).hom
        (scalarEquiv.{u,v,a,max a b c s} k G hM M n x))
    rw [liftedMapAgreement.{u,v,a,b,max a b c s} k G hM hN]
    exact congrArg (fun f => f.hom (scalarEquiv.{u,v,a,max a b c s} k G hM M n x)) eq.symm
  · intro x
    have eq := congrArg (fun f => HomologicalComplex.homologyMap f n) B.iso.hom.comm₂₃
    simp only [HomologicalComplex.homologyMap_comp, B.on_second, B.on_third] at eq
    change (HomologicalComplex.homologyMap B.third.iso.hom n).hom
      (scalarEquiv.{u,v,c,max a b c s} k G hP P n (T.projection.hom n x)) =
      (HomologicalComplex.homologyMap D.g n).hom ((HomologicalComplex.homologyMap B.second.iso.hom n).hom
        (scalarEquiv.{u,v,b,max a b c s} k G hN N n x))
    rw [liftedMapAgreement.{u,v,b,c,max a b c s} k G hN hP]
    exact congrArg (fun f => f.hom (scalarEquiv.{u,v,b,max a b c s} k G hN N n x)) eq.symm
  · intro x
    have eq := HomologicalComplex.HomologySequence.δ_naturality B.iso.hom B.raw_exact B.bar_exact n (n+1) rfl
    rw [B.on_first, B.on_third] at eq
    change (HomologicalComplex.homologyMap B.first.iso.hom (n+1)).hom
      (scalarEquiv.{u,v,a,max a b c s} k G hM M (n+1) (T.boundary n x)) =
      (B.bar_exact.δ n (n+1) rfl).hom ((HomologicalComplex.homologyMap B.third.iso.hom n).hom
        (scalarEquiv.{u,v,c,max a b c s} k G hP P n x))
    rw [liftedBoundaryAgreement.{u,v,a,b,c,s} k G h T B.raw_exact]
    exact congrArg (fun f => f.hom (scalarEquiv.{u,v,c,max a b c s} k G hP P n x)) eq

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution
  (Cohomology Resolution)
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport
  (commonCoefficient commonCoefficientIso)
open private nativeComparison nativeCommon_agreement barClasses_natural barPost from
  MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open private homMap_id from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open P103.Specs.Ch10.Complexes (cycleBoundaries)

universe r

/-- Identify the iterated lift used by the native comparison with the
single common lift used by the coefficient sequence. -/
def commonCoefficientComparison (M : Coeff.{u,v,a} k G) :
    commonCoefficient.{u,v,a,s} k G M ≅ liftedCoeff.{u,v,a,s} k G M :=
  ((commonCoefficientIso.{u,v,a,s} k G M).symm.trans
    (down.{u,v,a,max u v a s} k G M).symm).toModuleIso

/-- Applying the inverse of the normalized comparison to the original
cochain class recovers the prescribed native projective computation after
carrier transport. The representative comes from the same P103 bar quotient. -/
theorem normalizedProjectiveComputation
    (e : BarComparison.{u,v,a,s} k G hM M) (Q : Resolution.{u,v,r} k G)
    (n : ℕ) (x : Cohomology k G Q M n) :
    let A := GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,a} k G
    let C := GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,max a s} k G
    let T := GroupCohomologyOriginalCoefficients.NativeTransport.normalized.{u,v,a,s} k G
    let E := nativeComparison.{u,v,a,r} k G A
    ∃ (z : cycles (homComplex (barResolution k G).complex M) n)
      (hz : differential k G M n (originalBarCoordinates k G M n z.val) = 0),
      homologyClass _ n z = E.original.equiv Q M n x ∧
      ((C.iso n).inv.app (liftedCoeff.{u,v,a,s} k G M)).hom
        (e.homology n (classOf k G hM M n (originalBarCoordinates k G M n z.val) hz)) =
      (((derivedH.{u,v,max a s} k G n).map (commonCoefficientComparison.{u,v,a,s} k G M).hom).hom
        (T.onOriginal k G M n (E.value k G Q M n x))) := by
  dsimp only
  let A := GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,a} k G
  let C := GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,max a s} k G
  let T := GroupCohomologyOriginalCoefficients.NativeTransport.normalized.{u,v,a,s} k G
  let E := nativeComparison.{u,v,a,r} k G A
  let J := GroupCohomologyOriginalCoefficients.MixedProjective.compareBar.{u,v,a,max a s} k G M
    (commonCoefficient.{u,v,a,s} k G M) (commonCoefficientIso.{u,v,a,s} k G M)
  let J' := GroupCohomologyOriginalCoefficients.MixedProjective.compareBar.{u,v,a,max a s} k G M
    (liftedCoeff.{u,v,a,s} k G M) (down.{u,v,a,max u v a s} k G M).symm
  let f := (commonCoefficientComparison.{u,v,a,s} k G M).hom
  let v := T.onOriginal k G M n (E.value k G Q M n x)
  let y := E.original.equiv Q M n x
  obtain ⟨z, hz⟩ := (cycleBoundaries (homComplex (barResolution k G).complex M) n).mkQ_surjective y
  obtain ⟨hd, he⟩ := barHomology_projectiveClass k G e n z
  refine ⟨z, hd, hz, ?_⟩
  change ((C.iso n).inv.app (liftedCoeff.{u,v,a,s} k G M)).hom
    (e.homology n (classOf k G hM M n (originalBarCoordinates k G M n z.val) hd)) =
      ((derivedH.{u,v,max a s} k G n).map f).hom v
  have hclass : e.homology n (classOf k G hM M n (originalBarCoordinates k G M n z.val) hd) =
      J'.classes n y := he.trans (congrArg (J'.classes n) (show homologyClass _ n z = y from hz))
  rw [hclass]
  have hf := barClasses_natural k G J J' (LinearMap.id : M →ₗ[k[G]] M) f (fun _ => rfl) n y
  have hi : barPost k G (LinearMap.id : M →ₗ[k[G]] M) =
      TorBalance.LinearChainMap.id (homComplex (barResolution k G).complex M) :=
    homMap_id k G (TorBalance.AugmentedResolution.ofP103 (barResolution k G)
      (GroupCohomologyOriginalCoefficients.barResolution_isProjective k G)) M
  have hid : (barPost k G (LinearMap.id : M →ₗ[k[G]] M)).homologyMap n y = y :=
    (congrArg (fun g => g.homologyMap n y) hi).trans
      (LinearMap.congr_fun (TorBalance.LinearChainMap.homologyMap_id
        (K := homComplex (barResolution k G).complex M) n) y)
  have hc : ((C.iso n).hom.app (commonCoefficient.{u,v,a,s} k G M)).hom v = J.classes n y :=
    nativeCommon_agreement k G A C T M Q n x
  let η := ((C.iso n).app (liftedCoeff.{u,v,a,s} k G M)).toLinearEquiv
  apply η.injective
  change η (η.symm (J'.classes n y)) = η (((derivedH.{u,v,max a s} k G n).map f).hom v)
  calc
    _ = J'.classes n y := η.apply_symm_apply _
    _ = _ := (congrArg (J'.classes n) hid.symm).trans hf
    _ = _ := congrArg (fun w => ((ambientH.{u,v,max a s} k G n).map f).hom w) hc.symm
    _ = _ := (congrArg (fun g => g.hom v) ((C.iso n).hom.naturality f)).symm

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar (Comparison)

private theorem ambientAgreement (e : Comparison.{u,v,s} k G) :
    AmbientAgreement k G e.iso := by
  refine ⟨?_, fun S hS _ n => e.boundary hS n⟩
  intro B m
  obtain ⟨z, hz, hc, hclass⟩ := e.degreeZero B m
  refine ⟨z, hz, ?_, hclass⟩
  change z.hom (GroupBar.Large.single k G (Fin.partialProd Fin.elim0) 1) = _
  have eq : Fin.partialProd (Fin.elim0 : Fin 0 → G) = fun _ => 1 := by
    funext g
    rw [Fin.eq_zero g, Fin.partialProd_zero]
  rw [eq]
  exact hc

/-- The connecting maps agree through HA-A01-Carrier's normalized comparison
and the homology maps of the specified pointwise bar comparison. -/
theorem normalizedBoundary {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (h : ShortExact k G i p) (T : Sequence k G hM hN hP i p)
    (B : Mixed.SequenceComparison.{u,v,a,b,c,s} k G hM hN hP h) :
    let S := commonSequence.{u,v,a,b,c,s} k G h
    let E := GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,max a b c s} k G
    BarSequenceAgreement k G T B ∧
    ∀ n x, ((E.iso (n+1)).inv.app S.X₁).hom (B.first.homology (n+1) (T.boundary n x)) =
      (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightBoundary
        (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor k G)
        B.coefficient_exact n).hom (((E.iso n).inv.app S.X₃).hom (B.third.homology n x)) := by
  dsimp only
  let E := GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,max a b c s} k G
  have ht := barSequenceAgreement.{u,v,a,b,c,s} k G h T B
  refine ⟨ht, ?_⟩
  intro n x
  let S := commonSequence.{u,v,a,b,c,s} k G h
  let η₁ := ((E.iso (n+1)).app S.X₁).toLinearEquiv
  let η₃ := ((E.iso n).app S.X₃).toLinearEquiv
  have he := E.boundary B.coefficient_exact n
  change η₁.symm (B.first.homology (n+1) (T.boundary n x)) =
    (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightBoundary
      (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor k G)
      B.coefficient_exact n).hom (η₃.symm (B.third.homology n x))
  apply η₁.injective
  rw [LinearEquiv.apply_symm_apply, (ht n).2.2]
  have eq := congrArg (fun f => f.hom (η₃.symm (B.third.homology n x))) he
  change η₁ _ = (B.bar_exact.δ n (n+1) rfl).hom (η₃ (η₃.symm (B.third.homology n x))) at eq
  rw [LinearEquiv.apply_symm_apply] at eq
  exact eq.symm

theorem derivedAgreement : Mixed.derivedAgreementExpected.{u,v,a,b,c,s} := by
  intro k G _ _ hM hN hP
  let E := GroupCohomologyOriginalCoefficients.NormalizedBar.normalized.{u,v,max a b c s} k G
  exact ⟨E.iso, ambientAgreement.{u,v,max a b c s} k G E, normalizedBoundary.{u,v,a,b,c,s} k G⟩

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence.Mixed
