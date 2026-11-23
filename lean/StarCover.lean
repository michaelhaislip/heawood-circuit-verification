import PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph
import PEqualNP.Defs.MetaComplexityLgpMono

namespace Research.StarCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverCircuit

theorem cover_monotone (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) :
    Monotone2 (coverCircuit n edges cover) := by
  intro g hg
  obtain ⟨hop, hlen⟩ := gates_ops n edges cover g hg
  refine ⟨?_, by omega⟩
  rcases hop with h | h <;> simp [h]

theorem cover_correct (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
    (hE : ∀ e ∈ edges, e.1 < n ∧ e.2 < n)
    (hT : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover) (x : Fin n → Bool) :
    (coverCircuit n edges cover).eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  have h := congrFun (circuitFun_eq n edges cover hE hT) x
  change (coverCircuit n edges cover).eval (List.ofFn x) = _ at h
  rw [h, decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases huv with huv | hvu
    · exact ⟨u, v, huv, hu, hv⟩
    · exact ⟨v, u, hvu, hv, hu⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨u, v, Or.inl huv, hu, hv⟩

theorem cover_exact_active (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
    (hne : edges ≠ []) (hT : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover) :
    (coverCircuit n edges cover).size + 1 =
      edges.length + (blocks edges cover).length := by
  have hf : edges.filter (fun e => cover.any (fun c => isEnd c e)) = edges := by
    apply List.filter_eq_self.mpr
    intro e he
    rcases hT e he with h | h
    · exact List.any_eq_true.mpr ⟨e.1, h, by simp [isEnd]⟩
    · exact List.any_eq_true.mpr ⟨e.2, h, by simp [isEnd]⟩
  have hs : ((blocks edges cover).map (fun b => b.2.length)).sum = edges.length := by
    rw [sum_blocks, hf]
  have hb : blocks edges cover ≠ [] := by
    intro hb
    have hz : edges.length = 0 := by simpa [hb] using hs.symm
    exact hne (List.length_eq_zero_iff.mp hz)
  rw [size_blocks n edges cover hb, hs]

theorem star_cover_spec (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
    (hne : edges ≠ []) (hE : ∀ e ∈ edges, e.1 < n ∧ e.2 < n)
    (hT : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover) :
    Monotone2 (coverCircuit n edges cover) ∧
    (coverCircuit n edges cover).size = edges.length + (blocks edges cover).length - 1 ∧
    (coverCircuit n edges cover).size + 1 ≤ edges.length + cover.length ∧
    ∀ x : Fin n → Bool,
      (coverCircuit n edges cover).eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  refine ⟨cover_monotone n edges cover, ?_, size_le n edges cover hne,
    cover_correct n edges cover hE hT⟩
  have h := cover_exact_active n edges cover hne hT
  omega

theorem graph_cover_upper (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hne : ∃ u v, G.Adj u v)
    (hT : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ G.edgeFinset.card + T.card ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  refine ⟨coverCircuit n (graph_edges n G) (graph_cover T), cover_monotone _ _ _, ?_, ?_⟩
  · have h := size_le n (graph_edges n G) (graph_cover T) (graph_edges_ne_nil n G hne)
    simpa only [graph_edges_length, graph_cover_length] using h
  · intro x
    have h := congrFun (circuitFun_eq_graph n _ _ G (graph_hG n G)
      (graph_hE n G) (graph_hT n G T hT)) x
    change (coverCircuit n (graph_edges n G) (graph_cover T)).eval (List.ofFn x) = _ at h
    rw [h, decide_eq_true_eq]

def heawoodEdges : List (ℕ × ℕ) :=
  [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
    (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
    (6,8),(6,9),(6,11)]

def heawoodCover : List ℕ := List.range 7

def heawoodCircuit : Circuit := coverCircuit 14 heawoodEdges heawoodCover

theorem heawood_endpoints : ∀ e ∈ heawoodEdges, e.1 < 14 ∧ e.2 < 14 := by
  have h : heawoodEdges.all (fun e => decide (e.1 < 14 ∧ e.2 < 14)) = true := by decide
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

theorem heawood_cover : ∀ e ∈ heawoodEdges,
    e.1 ∈ heawoodCover ∨ e.2 ∈ heawoodCover := by
  have h : heawoodEdges.all (fun e => decide
      (e.1 ∈ heawoodCover ∨ e.2 ∈ heawoodCover)) = true := by decide
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

theorem heawood_counts : heawoodEdges.length = 21 ∧
    (blocks heawoodEdges heawoodCover).length = 7 := by decide

theorem heawood_size : heawoodCircuit.size = 27 := by
  have h := cover_exact_active 14 heawoodEdges heawoodCover (by decide) heawood_cover
  change heawoodCircuit.size + 1 = _ at h
  rw [heawood_counts.1, heawood_counts.2] at h
  omega

theorem heawood_correct : Monotone2 heawoodCircuit ∧ heawoodCircuit.size = 27 ∧
    ∀ x : Fin 14 → Bool, heawoodCircuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 14, (u.val, v.val) ∈ heawoodEdges ∧ x u = true ∧ x v = true := by
  exact ⟨cover_monotone _ _ _, heawood_size,
    cover_correct 14 heawoodEdges heawoodCover heawood_endpoints heawood_cover⟩

theorem empty_graph (n : ℕ) (x : Fin n → Bool) :
    Monotone2 (coverCircuit n [] []) ∧ (coverCircuit n [] []).size = 0 ∧
      (coverCircuit n [] []).eval (List.ofFn x) = false := by
  refine ⟨cover_monotone _ _ _, rfl, ?_⟩
  change (List.ofFn x).getD n false = false
  simp [List.getD_eq_getElem?_getD]

theorem star_example :
    (coverCircuit 4 [(0,1),(0,2),(0,3)] [0]).size = 3 := by rfl

theorem path_example :
    (coverCircuit 4 [(0,1),(1,2),(2,3)] [1,2]).size = 4 := by rfl

theorem triangle_example :
    (coverCircuit 3 [(0,1),(0,2),(1,2)] [0,1]).size = 4 := by rfl

theorem redundant_cover_example :
    (blocks [(0,1),(0,2),(0,3)] [0,0,1,2,3]).length = 1 ∧
    (coverCircuit 4 [(0,1),(0,2),(0,3)] [0,0,1,2,3]).size = 3 := by
  exact ⟨rfl, rfl⟩

end Research.StarCover

#print axioms Research.StarCover.star_cover_spec
#print axioms Research.StarCover.graph_cover_upper
#print axioms Research.StarCover.heawood_correct
