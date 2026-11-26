import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SquareZeroLiftDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftGraph
import Mathlib.LinearAlgebra.Isomorphisms

/-! The graph construction for lifting across a prescribed square-zero extension. -/

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLift.Presentation

open Algebra.Extension TrivSqZeroExt

universe u v w t n l m

variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
  (p : Presentation e B σ) {c : e.CoefficientMap (B := B) N}

private theorem reduce_surjective : Function.Surjective p.reduce :=
  Ideal.Quotient.mk_surjective (I := p.IP)

theorem conormalReduction_mk (q : p.Q) :
    p.conormalReduction (Cotangent.mk q) =
      Cotangent.mk (P := p.barExtension) ⟨p.reduce q, q.property⟩ := rfl

theorem conormalReduction_surjective : Function.Surjective p.conormalReduction := by
  intro x
  obtain ⟨z, rfl⟩ := Cotangent.mk_surjective (P := p.barExtension) x
  obtain ⟨q, hq⟩ := p.reduce_surjective z.val
  have h : q ∈ p.Q := by
    change p.barMap (p.reduce q) = 0
    rw [hq]
    exact z.property
  exact ⟨Cotangent.mk ⟨q, h⟩, (p.conormalReduction_mk _).trans
    (congrArg Cotangent.mk (Subtype.ext hq))⟩

private theorem map_Q : Ideal.map p.reduce p.Q = p.J := by
  ext z
  rw [Ideal.mem_map_iff_of_surjective _ p.reduce_surjective]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hz
    obtain ⟨q, rfl⟩ := p.reduce_surjective z
    exact ⟨q, hz, rfl⟩

theorem conormalReduction_ker : LinearMap.ker p.conormalReduction = p.K := by
  ext x
  change p.conormalReduction x = 0 ↔ x ∈ p.K
  constructor
  · obtain ⟨q, rfl⟩ := Cotangent.mk_surjective (P := p.extension) x
    rw [p.conormalReduction_mk, Cotangent.mk_eq_zero_iff]
    change p.reduce q.val ∈ (p.J ^ 2 : Ideal p.Bar) → _
    have hmap : Ideal.map p.reduce (p.Q ^ 2) = (p.J ^ 2 : Ideal p.Bar) :=
      (Ideal.map_pow p.reduce _ _).trans (congrArg (fun J : Ideal p.Bar => J ^ 2) p.map_Q)
    rw [← hmap, Ideal.mem_map_iff_of_surjective _ p.reduce_surjective]
    rintro ⟨r, hr, heq⟩
    have hi : q.val - r ∈ p.IP :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp heq.symm
    refine (p.mem_K _).mpr ⟨⟨q.val - r, hi⟩, ?_⟩
    change Cotangent.mk (P := p.extension) ⟨q.val - r, p.IP_le_Q hi⟩ = _
    apply (Cotangent.mk_eq_mk_iff_sub_mem _ _).2
    change q.val - r - q.val ∈ p.Q ^ 2
    rw [show q.val - r - q.val = -r by abel]
    exact Submodule.neg_mem _ hr
  · rintro hx
    obtain ⟨i, rfl⟩ := (p.mem_K _).mp hx
    change p.conormalReduction (Cotangent.mk ⟨i.val, p.IP_le_Q i.property⟩) = 0
    rw [p.conormalReduction_mk]
    have hi : p.reduce i.val = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr i.property
    let q : p.J := ⟨p.reduce i.val, p.IP_le_Q i.property⟩
    change Cotangent.mk q = 0
    have hq : q = 0 := Subtype.ext hi
    rw [hq, map_zero]

/-- Reduction gives the canonical isomorphism from the cokernel to the reduced conormal. -/
def conormalQuotientEquiv : (p.Conormal ⧸ p.K) ≃ₗ[B] p.BarConormal :=
  (Submodule.quotEquivOfEq _ _ p.conormalReduction_ker.symm).trans
    (p.conormalReduction.quotKerEquivOfSurjective p.conormalReduction_surjective)

theorem conormalQuotientEquiv_mk (x : p.Conormal) :
    p.conormalQuotientEquiv (p.K.mkQ x) = p.conormalReduction x := rfl

namespace ChosenLift

variable {p} (L : p.ChosenLift.{u,v,w,t,n,l} c)

private theorem ker_mul_eq_zero (x y : L.lift.ker) :
    (x.val * y.val : L.lift.Ring) = 0 := by
  have h := Ideal.mul_mem_mul x.property y.property
  simpa only [← pow_two, L.lift.squareZero, Ideal.mem_bot] using h

private def evaluateRelation :
    letI := p.targetModule N
    p.Q →ₗ[p.extension.Ring] N := by
  letI := p.targetModule N
  refine
    { toFun := fun q => L.lift.marking (L.evaluateKer q)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    rw [← map_add]
    exact congrArg L.lift.marking (Subtype.ext (L.evaluate.map_add x y))
  · intro r x
    change L.lift.marking (L.evaluateKer (r • x)) =
      p.ringHom r • L.lift.marking (L.evaluateKer x)
    rw [← L.map_evaluate r, ← map_smul, L.lift.map_smul]
    exact congrArg L.lift.marking (Subtype.ext (L.evaluate.map_mul r x))

private theorem evaluateRelation_mul (q r : p.Q) : L.evaluateRelation (q * r) = 0 := by
  have h : L.evaluateKer (q * r) = 0 := by
    apply Subtype.ext
    change L.evaluate ((q : p.extension.Ring) * r) = 0
    rw [map_mul]
    exact L.ker_mul_eq_zero (L.evaluateKer q) (L.evaluateKer r)
  change L.lift.marking (L.evaluateKer (q * r)) = 0
  rw [h, map_zero]

/-- Evaluation on the chosen generators gives the map on the conormal module. -/
def relationMap : p.Conormal →ₗ[B] N := by
  letI : Module p.extension.Ring N := p.targetModule N
  let f := Ideal.Cotangent.lift L.evaluateRelation L.evaluateRelation_mul
  refine
    { toFun := fun q => f q.val
      map_add' := fun q r => f.map_add q.val r.val
      map_smul' := ?_ }
  intro b q
  have hs : Function.Surjective p.ringHom := p.surjective
  obtain ⟨r, rfl⟩ := hs b
  have hq : p.ringHom r • q = r • q := algebraMap_smul p.extension.Ring r q
  change f ((p.ringHom r • q).val) = p.ringHom r • f q.val
  rw [hq, Cotangent.val_smul', map_smul]
  rfl

@[simp] theorem relationMap_mk (q : p.Q) :
    L.relationMap (Cotangent.mk q) = L.lift.marking (L.evaluateKer q) := rfl

/-- A lift with chosen generators satisfies the prescribed equation. -/
def toRelationMaps : p.RelationMaps c := by
  letI := p.targetModule N
  letI := p.targetTower (N := N)
  refine ⟨L.relationMap, fun x => ?_⟩
  let f := (L.relationMap.restrictScalars p.extension.Ring).comp p.toConormal
  change f x = _
  have h : f = p.prescribed c := p.prescribed_unique c _ (by
    intro i
    change L.relationMap (Cotangent.mk _) = c i
    rw [L.relationMap_mk, ← L.lift.induces i]
    apply congrArg L.lift.marking
    apply Subtype.ext
    exact MvPolynomial.eval₂Hom_C _ _ _)
  rw [h]

end ChosenLift

private theorem infMk_surjective : Function.Surjective p.infMk :=
  Ideal.Quotient.mk_surjective (I := p.Q ^ 2)

@[simp] theorem infMap_infMk (r : p.extension.Ring) : p.infMap (p.infMk r) = p.ringHom r :=
  rfl

private theorem fst_of_trivialMap_eq_zero (x : p.Trivial N) (h : p.trivialMap x = 0) :
    ∃ q : p.Q, x.fst = p.infMk q := by
  obtain ⟨r, hr⟩ := p.infMk_surjective x.fst
  have hz : p.ringHom r = 0 := by
    rw [← p.infMap_infMk, hr]
    exact h
  exact ⟨⟨r, hz⟩, hr.symm⟩

private theorem cotangent_mk_smul (r : p.extension.Ring) (q : p.Q) :
    Cotangent.mk (r • q) = p.ringHom r • Cotangent.mk q := by
  rw [map_smul]
  exact (algebraMap_smul p.extension.Ring r (Cotangent.mk q)).symm

/-- The ideal of elements (q, -ρ(q)) in the trivial square-zero extension. -/
def graphIdeal (ρ : p.Conormal →ₗ[B] N) : Ideal (p.Trivial N) where
  carrier := {x | p.GraphMember ρ x}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩
    · change (0 : p.InfRing) = p.infMk 0
      rw [map_zero]
    · change (0 : N) = -ρ (Cotangent.mk (0 : p.Q))
      rw [map_zero, map_zero, neg_zero]
  add_mem' := by
    rintro x y ⟨q, hq, hq'⟩ ⟨r, hr, hr'⟩
    refine ⟨q + r, ?_, ?_⟩
    · change x.fst + y.fst = p.infMk (q.val + r.val)
      rw [hq, hr, map_add]
    · change x.snd + y.snd = -ρ (Cotangent.mk (q + r))
      rw [hq', hr', map_add, map_add, neg_add]
  smul_mem' := by
    rintro x y ⟨q, hq, hq'⟩
    obtain ⟨r, hr⟩ := p.infMk_surjective x.fst
    refine ⟨r • q, ?_, ?_⟩
    · change x.fst * y.fst = p.infMk (r * q.val)
      rw [← hr, hq, map_mul]
    · change p.infMap x.fst • y.snd + p.infMap y.fst • x.snd =
        -ρ (Cotangent.mk (r • q))
      rw [← hr, hq, hq', p.infMap_infMk, p.infMap_infMk,
        show p.ringHom q.val = 0 from q.property,
        zero_smul, add_zero, p.cotangent_mk_smul, map_smul, smul_neg]

theorem mem_graphIdeal (ρ : p.Conormal →ₗ[B] N) (x : p.Trivial N) :
    x ∈ p.graphIdeal ρ ↔ p.GraphMember ρ x := Iff.rfl

private theorem graphIdeal_le_ker (ρ : p.Conormal →ₗ[B] N) :
    p.graphIdeal ρ ≤ RingHom.ker (p.trivialMap (N := N)) := by
  rintro x ⟨q, hq, _⟩
  change p.infMap x.fst = 0
  rw [hq, p.infMap_infMk]
  exact q.property

/-- The quotient by the graph ideal. -/
abbrev GraphRing (ρ : p.Conormal →ₗ[B] N) := p.Trivial N ⧸ p.graphIdeal ρ

/-- The canonical map from the trivial extension to the graph quotient. -/
abbrev graphMk (ρ : p.Conormal →ₗ[B] N) : p.Trivial N →+* p.GraphRing ρ :=
  Ideal.Quotient.mk _

/-- The graph quotient reduces to B by projecting to the first coordinate and reducing. -/
def graphMap (ρ : p.Conormal →ₗ[B] N) : p.GraphRing ρ →+* B :=
  Ideal.Quotient.lift _ p.trivialMap (fun _ hx => p.graphIdeal_le_ker ρ hx)

private theorem graphMap_surjective (ρ : p.Conormal →ₗ[B] N) :
    Function.Surjective (p.graphMap ρ) := by
  intro b
  have hs : Function.Surjective p.ringHom := p.surjective
  obtain ⟨r, hr⟩ := hs b
  exact ⟨p.graphMk ρ (p.trivialMk r), hr⟩

private theorem graphMk_eq_inr (ρ : p.Conormal →ₗ[B] N) (x : p.Trivial N)
    (q : p.Q) (hq : x.fst = p.infMk q) :
    p.graphMk ρ x = p.graphMk ρ (inr (ρ (Cotangent.mk q) + x.snd)) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
  refine ⟨q, ?_, ?_⟩
  · change x.fst - 0 = p.infMk q
    rw [sub_zero, hq]
  · change x.snd - (ρ (Cotangent.mk q) + x.snd) = -ρ (Cotangent.mk q)
    abel

private def graphKernelInr (ρ : p.Conormal →ₗ[B] N) (a : N) :
    RingHom.ker (p.graphMap ρ) :=
  ⟨p.graphMk ρ (inr a), p.infMap.map_zero⟩

private theorem graphKernelInr_surjective (ρ : p.Conormal →ₗ[B] N) :
    Function.Surjective (p.graphKernelInr ρ) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := p.graphIdeal ρ) x
  obtain ⟨q, hq⟩ := p.fst_of_trivialMap_eq_zero y hx
  exact ⟨ρ (Cotangent.mk q) + y.snd, Subtype.ext (p.graphMk_eq_inr ρ y q hq).symm⟩

private theorem graphKernelInr_injective (ρ : p.Conormal →ₗ[B] N) :
    Function.Injective (p.graphKernelInr ρ) := by
  intro a b hab
  have h : p.graphMk ρ (inr a) = p.graphMk ρ (inr b) := congrArg Subtype.val hab
  obtain ⟨q, hq, ha⟩ := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h
  change (0 : p.InfRing) - 0 = p.infMk q at hq
  have hq' : Cotangent.mk q = 0 := by
    apply (Cotangent.mk_eq_zero_iff q).2
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hq.symm.trans (sub_zero _)
  change a - b = -ρ (Cotangent.mk q) at ha
  rw [hq', map_zero, neg_zero, sub_eq_zero] at ha
  exact ha

private theorem graphMap_squareZero (ρ : p.Conormal →ₗ[B] N) :
    RingHom.ker (p.graphMap ρ) ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨a, ha⟩ := p.graphKernelInr_surjective ρ ⟨x, hx⟩
  obtain ⟨b, hb⟩ := p.graphKernelInr_surjective ρ ⟨y, hy⟩
  change x * y = 0
  have ha' : p.graphMk ρ (inr a) = x := congrArg Subtype.val ha
  have hb' : p.graphMk ρ (inr b) = y := congrArg Subtype.val hb
  rw [← ha', ← hb']
  rw [← map_mul, inr_mul_inr, map_zero]

private def graphMarking (ρ : p.Conormal →ₗ[B] N) :
    letI := kernelModule (p.graphMap ρ) (p.graphMap_surjective ρ) (p.graphMap_squareZero ρ)
    RingHom.ker (p.graphMap ρ) ≃ₗ[B] N := by
  letI := kernelModule (p.graphMap ρ) (p.graphMap_surjective ρ) (p.graphMap_squareZero ρ)
  let g : N →ₗ[B] RingHom.ker (p.graphMap ρ) :=
    { toFun := p.graphKernelInr ρ
      map_add' := fun a b => Subtype.ext (by
        change p.graphMk ρ (inr (a + b)) = p.graphMk ρ (inr a) + p.graphMk ρ (inr b)
        rw [inr_add, map_add])
      map_smul' := by
        intro b a
        obtain ⟨x, rfl⟩ := p.graphMap_surjective ρ b
        change p.graphKernelInr ρ (p.graphMap ρ x • a) = p.graphMap ρ x • p.graphKernelInr ρ a
        rw [kernelModule_smul (p.graphMap ρ) (p.graphMap_surjective ρ) (p.graphMap_squareZero ρ)]
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := p.graphIdeal ρ) x
        apply Subtype.ext
        change p.graphMk ρ (inr (p.infMap y.fst • a)) = p.graphMk ρ y * p.graphMk ρ (inr a)
        rw [← map_mul]
        congr 1
        exact (TrivSqZeroExt.ext (by simp) (by
          rw [snd_mul]
          change p.infMap y.fst • a = p.infMap y.fst • a + p.infMap 0 • y.snd
          rw [map_zero, zero_smul, add_zero])) }
  exact (LinearEquiv.ofBijective g
    ⟨p.graphKernelInr_injective ρ, p.graphKernelInr_surjective ρ⟩).symm

theorem graphMarking_mk (ρ : p.Conormal →ₗ[B] N) (x : p.Trivial N)
    (q : p.Q) (hq : x.fst = p.infMk q) :
    p.graphMarking ρ ⟨p.graphMk ρ x, by
      change p.infMap x.fst = 0
      rw [hq, p.infMap_infMk]
      exact q.property⟩ = ρ (Cotangent.mk q) + x.snd := by
  apply (p.graphMarking ρ).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact Subtype.ext (p.graphMk_eq_inr ρ x q hq)

private def graphBase (ρ : p.Conormal →ₗ[B] N) : A' →+* p.GraphRing ρ :=
  (p.graphMk ρ).comp (p.trivialMk.comp MvPolynomial.C)

instance graphAlgebra (ρ : p.Conormal →ₗ[B] N) : Algebra A' (p.GraphRing ρ) :=
  (p.graphBase ρ).toAlgebra

/-- Construct the marked lift by quotienting the trivial extension by the graph. -/
def ofRelationMaps (ρ : p.RelationMaps c) : p.ChosenLift.{u,v,w,t,n,max u t n} c where
  lift :=
    { Ring := p.GraphRing ρ.1
      map := p.graphMap ρ.1
      over := p.over
      surjective := p.graphMap_surjective ρ.1
      squareZero := p.graphMap_squareZero ρ.1
      marking := p.graphMarking ρ.1
      induces := fun i => by
        let q : p.Q := ⟨(p.constant i).val, p.IP_le_Q (p.constant i).property⟩
        change p.graphMarking ρ.1 ⟨p.graphMk ρ.1 (p.trivialMk q.val), _⟩ = c i
        rw [p.graphMarking_mk ρ.1 (p.trivialMk q.val) q rfl]
        change ρ.1 (p.toConormal (p.constant i)) + 0 = c i
        rw [add_zero, ρ.2, p.prescribed_C] }
  variableLifts i := p.graphMk ρ.1 (p.trivialMk (MvPolynomial.X i))
  overVariable _ := rfl


namespace ChosenLift

variable {p} (L : p.ChosenLift.{u,v,w,t,n,l} c)

private theorem evaluate_kills_square : p.Q ^ 2 ≤ RingHom.ker L.evaluate := by
  rw [pow_two]
  refine Ideal.mul_le.mpr fun q hq r hr => ?_
  change L.evaluate (q * r) = 0
  rw [map_mul]
  exact L.ker_mul_eq_zero (L.evaluateKer ⟨q, hq⟩) (L.evaluateKer ⟨r, hr⟩)

/-- Evaluation of the variables factors through the square of the relation ideal. -/
def evaluateInf : p.InfRing →+* L.lift.Ring :=
  Ideal.Quotient.lift _ L.evaluate (fun _ h => L.evaluate_kills_square h)

@[simp] theorem evaluateInf_mk (r : p.extension.Ring) :
    L.evaluateInf (p.infMk r) = L.evaluate r := rfl

theorem map_evaluateInf (r : p.InfRing) :
    L.lift.map (L.evaluateInf r) = p.infMap r := by
  obtain ⟨q, rfl⟩ := p.infMk_surjective r
  rw [L.evaluateInf_mk, L.map_evaluate, p.infMap_infMk]

/-- Inclusion of N into the underlying ring of the marked lift. -/
abbrev includeKernel (a : N) : L.lift.Ring := (L.lift.marking.symm a).val

private theorem includeKernel_zero : L.includeKernel (0 : N) = 0 :=
  congrArg Subtype.val (map_zero L.lift.marking.symm)

private theorem includeKernel_add (a b : N) :
    L.includeKernel (a + b) = L.includeKernel a + L.includeKernel b :=
  congrArg Subtype.val (map_add L.lift.marking.symm a b)

private theorem includeKernel_smul (r : p.InfRing) (a : N) :
    L.includeKernel (p.infMap r • a) = L.evaluateInf r * L.includeKernel a := by
  rw [← L.map_evaluateInf r]
  exact congrArg Subtype.val
    ((L.lift.marking.symm.map_smul (L.lift.map (L.evaluateInf r)) a).trans
      (L.lift.map_smul (L.evaluateInf r) (L.lift.marking.symm a)))

/-- The map from the trivial extension induced by evaluation and the kernel marking. -/
def evaluateTrivial : p.Trivial N →+* L.lift.Ring where
  toFun x := L.evaluateInf x.fst + L.includeKernel x.snd
  map_one' := by
    change L.evaluateInf 1 + L.includeKernel 0 = 1
    rw [map_one, L.includeKernel_zero, add_zero]
  map_zero' := by
    change L.evaluateInf 0 + L.includeKernel 0 = 0
    rw [map_zero, L.includeKernel_zero, add_zero]
  map_add' x y := by
    change L.evaluateInf (x.fst + y.fst) + L.includeKernel (x.snd + y.snd) = _
    rw [map_add L.evaluateInf, L.includeKernel_add]
    abel
  map_mul' x y := by
    change L.evaluateInf (x.fst * y.fst) +
      L.includeKernel (p.infMap x.fst • y.snd + p.infMap y.fst • x.snd) = _
    rw [map_mul L.evaluateInf, L.includeKernel_add, L.includeKernel_smul, L.includeKernel_smul,
      add_mul, mul_add, mul_add,
      L.ker_mul_eq_zero (L.lift.marking.symm x.snd) (L.lift.marking.symm y.snd),
      add_zero, mul_comm (L.includeKernel x.snd)]
    abel

theorem evaluateTrivial_apply (x : p.Trivial N) :
    L.evaluateTrivial x = L.evaluateInf x.fst + L.includeKernel x.snd := rfl

@[simp] theorem evaluateTrivial_inr (a : N) :
    L.evaluateTrivial (inr a) = L.includeKernel a := by
  rw [L.evaluateTrivial_apply, fst_inr, snd_inr, map_zero, zero_add]

@[simp] theorem evaluateTrivial_mk (r : p.extension.Ring) :
    L.evaluateTrivial (p.trivialMk r) = L.evaluate r := by
  change L.evaluateInf (p.infMk r) + L.includeKernel 0 = L.evaluate r
  rw [L.evaluateInf_mk, L.includeKernel_zero, add_zero]

theorem map_evaluateTrivial (x : p.Trivial N) :
    L.lift.map (L.evaluateTrivial x) = p.trivialMap x := by
  rw [L.evaluateTrivial_apply, map_add, L.map_evaluateInf,
    show L.lift.map (L.includeKernel x.snd) = 0 from (L.lift.marking.symm x.snd).property,
    add_zero]
  rfl

theorem evaluateTrivial_surjective : Function.Surjective L.evaluateTrivial := by
  intro z
  have hs : Function.Surjective p.ringHom := p.surjective
  obtain ⟨q, hq⟩ := hs (L.lift.map z)
  have h : L.lift.map (z - L.evaluate q) = 0 := by
    rw [map_sub, L.map_evaluate, hq, sub_self]
  let a := L.lift.marking ⟨z - L.evaluate q, h⟩
  refine ⟨p.trivialMk q + inr a, ?_⟩
  rw [map_add, L.evaluateTrivial_mk, L.evaluateTrivial_inr]
  have ha : L.includeKernel a = z - L.evaluate q :=
    congrArg Subtype.val (L.lift.marking.symm_apply_apply ⟨z - L.evaluate q, h⟩)
  rw [ha, add_sub_cancel]

theorem evaluateTrivial_ker : RingHom.ker L.evaluateTrivial = p.graphIdeal L.relationMap := by
  ext x
  change L.evaluateTrivial x = 0 ↔ p.GraphMember L.relationMap x
  have hiff (q : p.Q) (hq : x.fst = p.infMk q) :
      L.evaluateTrivial x = 0 ↔ x.snd = -L.relationMap (Cotangent.mk q) := by
    rw [L.evaluateTrivial_apply, hq, L.evaluateInf_mk, L.relationMap_mk]
    change ((L.evaluateKer q).val + (L.lift.marking.symm x.snd).val = 0) ↔ _
    rw [add_eq_zero_iff_eq_neg']
    constructor
    · intro h
      have hs : L.lift.marking.symm x.snd = -L.evaluateKer q := Subtype.ext h
      rw [← L.lift.marking.apply_symm_apply x.snd, hs, map_neg]
    · intro h
      rw [h, map_neg, L.lift.marking.symm_apply_apply]
      rfl
  constructor
  · intro hx
    have h0 : p.trivialMap x = 0 := by rw [← L.map_evaluateTrivial, hx, map_zero]
    obtain ⟨q, hq⟩ := p.fst_of_trivialMap_eq_zero x h0
    exact ⟨q, hq, (hiff q hq).mp hx⟩
  · rintro ⟨q, hq, h⟩
    exact (hiff q hq).mpr h

private def fromGraphRing : p.GraphRing L.relationMap ≃+* L.lift.Ring :=
  (Ideal.quotEquivOfEq L.evaluateTrivial_ker.symm).trans
    (L.evaluateTrivial.quotientKerEquivOfSurjective L.evaluateTrivial_surjective)

private theorem fromGraphRing_mk (x : p.Trivial N) :
    L.fromGraphRing (p.graphMk L.relationMap x) = L.evaluateTrivial x := rfl

/-- The graph model reconstructs the given marked lift with its chosen variables. -/
def fromGraph : (p.ofRelationMaps L.toRelationMaps).Iso L := by
  let F : (p.ofRelationMaps L.toRelationMaps).lift.Ring ≃ₐ[A'] L.lift.Ring :=
    AlgEquiv.ofRingEquiv (f := L.fromGraphRing) (by
      intro a
      change L.fromGraphRing (p.graphMk _ (p.trivialMk (p.polynomialEquiv (MvPolynomial.C a)))) = _
      rw [L.fromGraphRing_mk, L.evaluateTrivial_mk]
      exact MvPolynomial.eval₂Hom_C _ _ _)
  refine
    { equiv := F
      over := ?_
      marked := ?_
      mapVariables := ?_ }
  · intro y
    change L.lift.map (L.fromGraphRing y) = p.graphMap L.relationMap y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := p.graphIdeal L.relationMap) y
    rw [L.fromGraphRing_mk, L.map_evaluateTrivial]
    rfl
  · intro y
    obtain ⟨a, ha⟩ := p.graphKernelInr_surjective L.relationMap y
    change p.graphKernelInr L.relationMap a = y at ha
    subst y
    apply L.lift.marking.symm.injective
    rw [L.lift.marking.symm_apply_apply]
    apply Subtype.ext
    change L.fromGraphRing (p.graphMk _ (inr a)) =
      L.includeKernel (p.graphMarking _ (p.graphKernelInr _ a))
    rw [L.fromGraphRing_mk, L.evaluateTrivial_inr]
    congr 1
    exact (p.graphMarking L.relationMap).apply_symm_apply a |>.symm
  · intro i
    change L.fromGraphRing (p.graphMk _ (p.trivialMk (p.polynomialEquiv (MvPolynomial.X i)))) = _
    rw [L.fromGraphRing_mk, L.evaluateTrivial_mk]
    exact MvPolynomial.eval₂Hom_X' _ _ _

end ChosenLift

theorem evaluate_ofRelationMaps (ρ : p.RelationMaps c) (x : p.extension.Ring) :
    (p.ofRelationMaps ρ).evaluate x = p.graphMk ρ.1 (p.trivialMk x) := by
  have h : (p.ofRelationMaps ρ).evaluate = (p.graphMk ρ.1).comp p.trivialMk := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) = _
      rw [MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i) = _
      rw [MvPolynomial.eval₂Hom_X']
      rfl
  exact DFunLike.congr_fun h x

theorem toRelationMaps_ofRelationMaps (ρ : p.RelationMaps c) :
    (p.ofRelationMaps ρ).toRelationMaps = ρ := by
  apply Subtype.ext
  ext x
  obtain ⟨q, rfl⟩ := Cotangent.mk_surjective (P := p.extension) x
  change (p.ofRelationMaps ρ).relationMap (Cotangent.mk q) = ρ.1 (Cotangent.mk q)
  rw [ChosenLift.relationMap_mk]
  have h : (p.ofRelationMaps ρ).evaluateKer q =
      ⟨p.graphMk ρ.1 (p.trivialMk q.val), q.property⟩ :=
    Subtype.ext (p.evaluate_ofRelationMaps ρ q.val)
  rw [h]
  change p.graphMarking ρ.1 _ = _
  exact (p.graphMarking_mk ρ.1 (p.trivialMk q.val) q rfl).trans (add_zero _)


namespace ChosenLift

variable {p}

theorem realizes_toRelationMaps (L : p.ChosenLift.{u,v,w,t,n,l} c) :
    L.Realizes L.toRelationMaps := L.relationMap_mk

theorem relationMaps_unique (L : p.ChosenLift.{u,v,w,t,n,l} c)
    (ρ : p.RelationMaps c) (h : L.Realizes ρ) : ρ = L.toRelationMaps := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨q, rfl⟩ := Cotangent.mk_surjective (P := p.extension) x
  exact (h q).trans (L.relationMap_mk q).symm

theorem Iso.toRelationMaps_eq {L : p.ChosenLift.{u,v,w,t,n,l} c}
    {M : p.ChosenLift.{u,v,w,t,n,m} c} (f : L.Iso M) :
    L.toRelationMaps = M.toRelationMaps := by
  have heval : f.equiv.toRingHom.comp L.evaluate = M.evaluate := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change f.equiv (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, AlgEquiv.commutes]
    · intro i
      change f.equiv (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      exact f.mapVariables i
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨q, rfl⟩ := Cotangent.mk_surjective (P := p.extension) x
  have hker : L.lift.mapKer f.equiv f.over (L.evaluateKer q) = M.evaluateKer q :=
    Subtype.ext (DFunLike.congr_fun heval q.val)
  exact (f.marked (L.evaluateKer q)).symm.trans (congrArg M.lift.marking hker)

end ChosenLift

/-- A lift can be equipped with chosen variable lifts using only its surjectivity. -/
def chooseVariables (L : Lift.{u,v,w,n,l} e c) : p.ChosenLift.{u,v,w,t,n,l} c where
  lift := L
  variableLifts i := Classical.choose (L.surjective (p.map (MvPolynomial.X i)))
  overVariable i := Classical.choose_spec (L.surjective (p.map (MvPolynomial.X i)))

/-- Evaluation and the graph construction are inverse on isomorphism classes. -/
def chosenLiftEquiv : ChosenLift.Classes.{u,v,w,t,n,max u t n} p c ≃ p.RelationMaps c where
  toFun := Quotient.lift ChosenLift.toRelationMaps (fun _ _ ⟨f⟩ => f.toRelationMaps_eq)
  invFun ρ := Quotient.mk _ (p.ofRelationMaps ρ)
  left_inv := Quotient.ind fun L => Quotient.sound ⟨L.fromGraph⟩
  right_inv := p.toRelationMaps_ofRelationMaps

open Specs.CommutativeAlgebraNotes.SquareZeroLiftGraph

theorem conormalCokernel : conormalCokernelType.{u,v,w,t} := by
  intro A' A B σ _ _ _ _ e p
  exact ⟨p.conormalReduction_surjective, p.conormalReduction_ker, p.conormalQuotientEquiv,
    p.conormalQuotientEquiv_mk⟩

theorem evaluation : evaluationType.{u,v,w,t,n,l} := by
  intro A' A B σ N _ _ _ _ _ _ e p c L
  exact ⟨L.toRelationMaps, L.realizes_toRelationMaps, L.relationMaps_unique⟩

theorem graphConstruction : graphConstructionType.{u,v,w,t,n} := by
  intro A' A B σ N _ _ _ _ _ _ e p c ρ
  refine ⟨p.graphIdeal ρ.val, p.ofRelationMaps ρ, RingEquiv.refl _, p.mem_graphIdeal ρ.val,
    fun _ => rfl, fun _ => rfl, ?_, fun _ => rfl, ?_⟩
  · exact (congrArg (p.ofRelationMaps ρ).Realizes (p.toRelationMaps_ofRelationMaps ρ)).mp
      (p.ofRelationMaps ρ).realizes_toRelationMaps
  · intro x q hq
    exact p.graphMarking_mk ρ.val x q hq

theorem comparison : comparisonType.{u,v,w,t,n,l} := by
  intro A' A B σ N _ _ _ _ _ _ e p c L ρ h
  have hρ := L.relationMaps_unique ρ h
  subst ρ
  refine ⟨L.evaluateTrivial, L.evaluateTrivial_surjective, L.evaluateTrivial_mk,
    L.evaluateTrivial_inr, L.map_evaluateTrivial, ?_⟩
  intro x
  rw [L.evaluateTrivial_ker]
  exact p.mem_graphIdeal L.relationMap x

theorem correspondence : correspondenceType.{u,v,w,t,n} := by
  intro A' A B σ N _ _ _ _ _ _ e p c
  exact ⟨p.chosenLiftEquiv, fun L => L.realizes_toRelationMaps⟩

theorem isomorphism : isomorphismType.{u,v,w,t,n,l,m} := by
  intro A' A B σ N _ _ _ _ _ _ e p c L M ρ τ hρ hτ
  rw [L.relationMaps_unique ρ hρ, M.relationMaps_unique τ hτ]
  constructor
  · rintro ⟨f⟩
    exact f.toRelationMaps_eq
  · intro h
    have f := L.fromGraph.symm
    rw [h] at f
    exact ⟨f.trans M.fromGraph⟩

end CommutativeAlgebraNotes.SquareZeroLift.Presentation
