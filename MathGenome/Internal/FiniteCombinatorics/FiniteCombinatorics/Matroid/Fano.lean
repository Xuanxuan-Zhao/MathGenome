import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ScalarExtension
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Fano
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-! The Fano characteristic criterion, paper.tex W74. -/
namespace FiniteCombinatorics.Matroid
open Set
open scoped TensorProduct
universe u w

def fanoMatroid : _root_.Matroid FanoPoint :=
  vectorMatroid (ZMod 2) univ finite_univ fanoColumns

theorem fanoColumnsComplete : Expected.fanoColumnsComplete := by
  constructor
  · change ∀ a b, fanoColumns a = fanoColumns b → a = b
    decide +kernel
  · ext x
    change (∃ i, fanoColumns i = x) ↔ x ≠ 0
    revert x
    decide +kernel

/-- Sufficiency uses the actual prime-field embedding and tensor extension. -/
theorem fanoRepresentableOfCharTwo : Expected.fanoRepresentableOfCharTwo := by
  intro K _ hK
  let : CharP K 2 := ringChar.of_eq hK
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let : Algebra (ZMod 2) K := ι.toAlgebra
  refine ⟨K ⊗[ZMod 2] (Fin 3 → ZMod 2), inferInstance, inferInstance,
    (fun e => (1 : K) ⊗ₜ[ZMod 2] fanoColumns e), ?_⟩
  exact scalarExtensionRepresents (ZMod 2) K Expected.fanoMatroid fanoColumns
    (vectorRepresents (ZMod 2) univ finite_univ fanoColumns)

private theorem three_coefficients {K : Type u} [Field K] {V : Type w}
    [AddCommGroup V] [Module K V] {a b c : V}
    (hi : LinearIndependent K ![a,b,c])
    {x y z x' y' z' : K}
    (he : x • a + y • b + z • c = x' • a + y' • b + z' • c) :
    x = x' ∧ y = y' ∧ z = z' := by
  have h := hi.fintypeLinearCombination_injective
    (show Fintype.linearCombination K ![a,b,c] ![x,y,z] =
      Fintype.linearCombination K ![a,b,c] ![x',y',z'] from by
      simpa [Fintype.linearCombination_apply, Fin.sum_univ_three, add_assoc] using he)
  exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩

private theorem line_coefficients {K : Type u} [Field K] {V : Type w}
    [AddCommGroup V] [Module K V] (v : Fin 7 → V) {i j k : Fin 7}
    (hpair : ∀ i j, i ≠ j → LinearIndepOn K v {i,j})
    (hik : i ≠ k) (hjk : j ≠ k)
    (hd : ¬ LinearIndepOn K v {k,i,j}) :
    ∃ x y : K, x ≠ 0 ∧ y ≠ 0 ∧ v k = x • v i + y • v j := by
  have hij : i ≠ j := by
    intro e
    subst j
    apply hd
    simpa [Set.pair_comm] using hpair k i hik.symm
  have hmem : v k ∈ Submodule.span K (v '' ({i,j} : Set (Fin 7))) := by
    by_contra hn
    exact hd ((hpair i j hij).insert hn)
  rw [Set.image_pair, Submodule.mem_span_pair] at hmem
  obtain ⟨x,y,he⟩ := hmem
  refine ⟨x,y,?_,?_,he.symm⟩
  · intro hx
    have hz : v k ∈ Submodule.span K (v '' ({j} : Set (Fin 7))) := by
      rw [Set.image_singleton, Submodule.mem_span_singleton]
      exact ⟨y, by simpa [hx] using he⟩
    exact ((hpair k j hjk.symm).notMem_span_of_insert
      (by simpa using hjk.symm)) hz
  · intro hy
    have hz : v k ∈ Submodule.span K (v '' ({i} : Set (Fin 7))) := by
      rw [Set.image_singleton, Submodule.mem_span_singleton]
      exact ⟨x, by simpa [hy] using he⟩
    exact ((hpair k i hik.symm).notMem_span_of_insert
      (by simpa using hik.symm)) hz

private theorem fano_pairs : ∀ i j : Fin 7, i ≠ j →
    LinearIndepOn (ZMod 2) fanoColumns {i,j} := by
  intro i j hij
  have hn (k : Fin 7) : fanoColumns k ≠ 0 := by
    have := congrArg (fun s => fanoColumns k ∈ s) fanoColumnsComplete.2
    exact (eq_iff_iff.mp this).mp (mem_range_self k)
  rw [linearIndepOn_pair_iff fanoColumns hij (hn i)]
  intro c
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide +kernel
  rcases hc with rfl | rfl
  · simpa using (hn j).symm
  · simpa using (fun h => hij (fanoColumnsComplete.1 h))

private theorem fano_axes : LinearIndepOn (ZMod 2) fanoColumns {0,1,2} := by
  suffices LinearIndepOn (ZMod 2) fanoColumns
      (({0,1,2} : Finset (Fin 7)) : Set (Fin 7)) by simpa using this
  rw [linearIndepOn_finset_iff]
  intro f he i hi
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  simp [fanoColumns] at h0 h1 h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> assumption

private theorem fano_lines : ∀ (i j k : Fin 7),
    (i,j,k) ∈ ([(0,1,3),(0,2,4),(1,2,5),(3,2,6),(4,1,6),(5,0,6),(4,5,3)] :
      List (Fin 7 × Fin 7 × Fin 7)) →
    ¬ LinearIndepOn (ZMod 2) fanoColumns {k,i,j} := by
  intro i j k hl
  have hx : k ≠ i ∧ k ≠ j ∧ fanoColumns k = fanoColumns i + fanoColumns j := by
    revert i j k
    decide +kernel
  intro hi
  apply hi.notMem_span (by simp : k ∈ ({k,i,j} : Set (Fin 7)))
  have hmem : fanoColumns k ∈ Submodule.span (ZMod 2)
      (fanoColumns '' ({i,j} : Set (Fin 7))) := by
    rw [Set.image_pair, Submodule.mem_span_pair]
    exact ⟨1,1,by simpa using hx.2.2.symm⟩
  simpa [hx.1, hx.2.1, Ne.symm hx.1, Ne.symm hx.2.1] using hmem

/-- The obstruction is proved directly in an arbitrary ambient vector space.
No assumption about its dimension, coordinates or characteristic is needed. -/
private theorem fano_incidence_obstruction {K : Type u} [Field K] {V : Type w}
    [AddCommGroup V] [Module K V] (v : Fin 7 → V)
    (hpair : ∀ i j, i ≠ j → LinearIndepOn K v {i,j})
    (hbase : LinearIndepOn K v {0,1,2})
    (hline : ∀ (i j k : Fin 7),
      (i,j,k) ∈ ([(0,1,3),(0,2,4),(1,2,5),(3,2,6),(4,1,6),(5,0,6),(4,5,3)] :
        List (Fin 7 × Fin 7 × Fin 7)) → ¬ LinearIndepOn K v {k,i,j}) :
    ringChar K = 2 := by
  let e : Fin 3 → ({0,1,2} : Set (Fin 7)) := fun i =>
    ⟨Fin.castLE (by decide) i, by fin_cases i <;> simp⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun k => k.val.val) hij)
  have hb : LinearIndependent K ![v 0,v 1,v 2] := by
    convert hbase.linearIndependent.comp e he using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨x,y,hx,hy,hd⟩ := line_coefficients v hpair (by decide : (0:Fin 7) ≠ 3)
    (by decide : (1:Fin 7) ≠ 3) (hline 0 1 3 (by simp))
  obtain ⟨z,w,hz,hw,hf⟩ := line_coefficients v hpair (by decide : (0:Fin 7) ≠ 4)
    (by decide : (2:Fin 7) ≠ 4) (hline 0 2 4 (by simp))
  obtain ⟨u,t,hu,ht,hg⟩ := line_coefficients v hpair (by decide : (1:Fin 7) ≠ 5)
    (by decide : (2:Fin 7) ≠ 5) (hline 1 2 5 (by simp))
  obtain ⟨p,q,hp,hq,hhd⟩ := line_coefficients v hpair (by decide : (3:Fin 7) ≠ 6)
    (by decide : (2:Fin 7) ≠ 6) (hline 3 2 6 (by simp))
  obtain ⟨r,s,hr,hs,hhf⟩ := line_coefficients v hpair (by decide : (4:Fin 7) ≠ 6)
    (by decide : (1:Fin 7) ≠ 6) (hline 4 1 6 (by simp))
  obtain ⟨l,k,hl,hk,hhg⟩ := line_coefficients v hpair (by decide : (5:Fin 7) ≠ 6)
    (by decide : (0:Fin 7) ≠ 6) (hline 5 0 6 (by simp))
  obtain ⟨m,n,hm,hn,hdfg⟩ := line_coefficients v hpair (by decide : (4:Fin 7) ≠ 3)
    (by decide : (5:Fin 7) ≠ 3) (hline 4 5 3 (by simp))
  have h₁ : p*x = r*z ∧ p*y = s ∧ q = r*w := by
    apply three_coefficients hb
    calc
      _ = p • v 3 + q • v 2 := by rw [hd]; module
      _ = r • v 4 + s • v 1 := hhd.symm.trans hhf
      _ = _ := by rw [hf]; module
  have h₂ : p*x = k ∧ p*y = l*u ∧ q = l*t := by
    apply three_coefficients hb
    calc
      _ = p • v 3 + q • v 2 := by rw [hd]; module
      _ = l • v 5 + k • v 0 := hhd.symm.trans hhg
      _ = _ := by rw [hg]; module
  have h₃ : x = m*z ∧ y = n*u ∧ (0:K) = m*w+n*t := by
    apply three_coefficients hb
    calc
      _ = v 3 := by simpa using hd.symm
      _ = m • v 4 + n • v 5 := hdfg
      _ = _ := by rw [hf,hg]; module
  have hpm : p*m = r := by
    apply mul_right_cancel₀ hz
    calc
      (p*m)*z = p*x := by rw [h₃.1]; ring
      _ = r*z := h₁.1
  have hpn : p*n = l := by
    apply mul_right_cancel₀ hu
    calc
      (p*n)*u = p*y := by rw [h₃.2.1]; ring
      _ = l*u := h₂.2.1
  have hmt : m*w = n*t := by
    apply mul_left_cancel₀ hp
    calc
      p*(m*w) = r*w := by rw [← hpm]; ring
      _ = l*t := h₁.2.2.symm.trans h₂.2.2
      _ = p*(n*t) := by rw [← hpn]; ring
  have htwo : (2:K) = 0 := by
    have hv : (2:K) * (m*w) = 0 := by
      linear_combination -h₃.2.2 + hmt
    exact (mul_eq_zero.mp hv).resolve_right (mul_ne_zero hm hw)
  exact CharP.ringChar_of_prime_eq_zero (by decide) htwo

theorem fanoRepresentationCharTwo : Expected.fanoRepresentationCharTwo := by
  intro K _ V _ _ v hv
  have htransfer (I : Set FanoPoint) :
      LinearIndepOn (ZMod 2) fanoColumns I ↔ LinearIndepOn K v I := by
    have hI := hv I
    change (I ⊆ univ ∧ LinearIndepOn (ZMod 2) fanoColumns I) ↔
      I ⊆ univ ∧ LinearIndepOn K v I at hI
    simpa using hI
  apply fano_incidence_obstruction v
  · intro i j hij
    exact (htransfer {i,j}).mp (fano_pairs i j hij)
  · exact (htransfer {0,1,2}).mp fano_axes
  · intro i j k hijk
    exact fun hi => fano_lines i j k hijk ((htransfer {k,i,j}).mpr hi)

theorem fanoRepresentableIff : Expected.fanoRepresentableIff := by
  intro K _
  constructor
  · rintro ⟨V, _, _, v, hv⟩
    exact fanoRepresentationCharTwo K v hv
  · exact fanoRepresentableOfCharTwo K

end FiniteCombinatorics.Matroid
