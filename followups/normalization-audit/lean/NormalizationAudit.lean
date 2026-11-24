import PEqualNP.MetaComplexity.Helpers.CoverCircuitList
import PEqualNP.Defs.MetaComplexityLgpMono

namespace Research.NormalizationAudit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverCircuit

theorem binary_commutes (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Bool) : op.eval [a,b] = op.eval [b,a] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> rfl

theorem binary_idempotent (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a : Bool) : op.eval [a,a] = a := by
  rcases hop with rfl | rfl <;> cases a <;> rfl

def copyPad (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [C.output, C.output]⟩], n + C.gates.length⟩

theorem copyPad_size (n : ℕ) (C : Circuit) :
    (copyPad n C).size = C.size + 1 := by simp [copyPad, Circuit.size]

theorem copyPad_mono (n : ℕ) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (copyPad n C) := by
  intro g hg
  simp only [copyPad, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact h g hg
  · simp

theorem copyPad_eval (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (copyPad n C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  simp only [Circuit.eval, wires_eq, copyPad, run_append, run_singleton]
  have hl : (run C.gates (List.ofFn x)).length = n + C.gates.length := by
    rw [run_length, List.length_ofFn]
  rw [← hl, getD_snoc_length]
  simp [GateOp.eval]

theorem copyPad_last (n : ℕ) (C : Circuit) :
    (copyPad n C).output + 1 = n + (copyPad n C).size := by
  simp [copyPad, Circuit.size]
  omega

theorem copyPad_suffix (n : ℕ) (C : Circuit) (h : C.output + 1 = n + C.size) :
    (copyPad n C).gates = C.gates ++
      [⟨GateOp.and, [n + C.size - 1, n + C.size - 1]⟩] := by
  have ho : C.output = n + C.size - 1 := by omega
  simp only [copyPad, ho]

def padCopies (n : ℕ) : ℕ → Circuit → Circuit
  | 0, C => C
  | k + 1, C => copyPad n (padCopies n k C)

theorem padCopies_spec (n k : ℕ) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (padCopies n k C) ∧ (padCopies n k C).size = C.size + k ∧
    ∀ x : Fin n → Bool, (padCopies n k C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  induction k with
  | zero => exact ⟨h, by simp [padCopies], fun _ => rfl⟩
  | succ k ih =>
    refine ⟨copyPad_mono n _ ih.1, ?_, ?_⟩
    · change (copyPad n (padCopies n k C)).size = _
      rw [copyPad_size, ih.2.1]
      omega
    · intro x
      change (copyPad n (padCopies n k C)).eval _ = _
      rw [copyPad_eval, ih.2.2 x]

theorem pad_to_budget (n s : ℕ) (C : Circuit) (h : Monotone2 C) (hs : C.size ≤ s) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = s ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨hm, hsize, heval⟩ := padCopies_spec n (s - C.size) C h
  exact ⟨padCopies n (s - C.size) C, hm, by omega, heval⟩

def singleEdge : Circuit := ⟨[⟨GateOp.and, [0,1]⟩], 3⟩

theorem singleEdge_spec : Monotone2 singleEdge ∧ singleEdge.size = 1 ∧
    ∀ x : Fin 3 → Bool, singleEdge.eval (List.ofFn x) = (x 0 && x 1) := by
  refine ⟨by simp [Monotone2, singleEdge], rfl, ?_⟩
  intro x
  simp [singleEdge, Circuit.eval, Circuit.wires, GateOp.eval,
    List.ofFn_succ]

theorem three_reads_impossible (a b : ℕ) :
    ¬ (∀ v : Fin 3, v.val = a ∨ v.val = b) := by
  intro h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Fin.val_zero, Fin.val_one] at h0 h1 h2
  omega

theorem one_gate_all_reads_impossible :
    ¬ ∃ a b : ℕ, ∀ v : Fin 3, v.val = a ∨ v.val = b := by
  rintro ⟨a, b, h⟩
  exact three_reads_impossible a b h

def IsEssential {n : ℕ} (f : (Fin n → Bool) → Bool) (v : Fin n) : Prop :=
  ∃ x y : Fin n → Bool, (∀ u, u ≠ v → x u = y u) ∧ f x ≠ f y

def graphFn {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : Bool :=
  decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

theorem graph_singleton_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : graphFn G (fun u => decide (u = v)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨a, b, hab, ha, hb⟩ := of_decide_eq_true h
  have hav : a = v := of_decide_eq_true ha
  have hbv : b = v := of_decide_eq_true hb
  exact G.ne_of_adj hab (hav.trans hbv.symm)

theorem graph_vertex_essential {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (hvw : G.Adj v w) : IsEssential (graphFn G) v := by
  refine ⟨(fun u => decide (u = w)), (fun u => decide (u = v ∨ u = w)), ?_, ?_⟩
  · intro u huv
    simp [huv]
  · have h0 := graph_singleton_false G w
    have h1 : graphFn G (fun u => decide (u = v ∨ u = w)) = true := by
      simp only [graphFn, decide_eq_true_eq]
      exact ⟨v, w, hvw, by simp, by simp⟩
    rw [h0, h1]
    decide

theorem no_isolates_all_essential {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hne : ∀ v, ∃ w, G.Adj v w) :
    ∀ v, IsEssential (graphFn G) v := by
  intro v
  obtain ⟨w, hw⟩ := hne v
  exact graph_vertex_essential G v w hw

theorem graph_not_projection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : ¬ ∀ x : Fin n → Bool, graphFn G x = x v := by
  intro h
  have hs := h (fun u => decide (u = v))
  rw [graph_singleton_false] at hs
  simp at hs

end Research.NormalizationAudit

#print axioms Research.NormalizationAudit.pad_to_budget
#print axioms Research.NormalizationAudit.singleEdge_spec
#print axioms Research.NormalizationAudit.one_gate_all_reads_impossible
#print axioms Research.NormalizationAudit.no_isolates_all_essential
