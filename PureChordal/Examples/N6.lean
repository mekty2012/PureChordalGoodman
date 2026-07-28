import PureChordal.ChromaticFactorization

namespace PureChordal.Examples.G6_1

def bags : Fin 2 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | _ => {3, 4, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 2, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 2 → Fin 2
  | i => match i.1 with
    | 0 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 3 2 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_1
namespace PureChordal.Examples.G6_2

def bags : Fin 3 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | 1 => {0, 1, 3}
    | _ => {0, 4, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 3, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 3 → Fin 3
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 3 3 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_2
namespace PureChordal.Examples.G6_3

def bags : Fin 3 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | 1 => {1, 2, 5}
    | _ => {0, 3, 4}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 3, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 3 → Fin 3
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 3 3 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_3
namespace PureChordal.Examples.G6_4

def bags : Fin 4 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | 1 => {0, 1, 3}
    | 2 => {0, 1, 4}
    | _ => {0, 1, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 4, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 4 → Fin 4
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 3 4 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_4
namespace PureChordal.Examples.G6_5

def bags : Fin 4 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | 1 => {0, 1, 3}
    | 2 => {0, 1, 4}
    | _ => {0, 2, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 4, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 4 → Fin 4
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 3 4 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_5
namespace PureChordal.Examples.G6_6

def bags : Fin 4 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | 1 => {0, 1, 3}
    | 2 => {0, 2, 4}
    | _ => {0, 3, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 4, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 4 → Fin 4
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | _ => 1

def decomp : PureCliqueTreeDecomp graph 3 4 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_6
namespace PureChordal.Examples.G6_7

def bags : Fin 4 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | 1 => {0, 1, 3}
    | 2 => {0, 2, 4}
    | _ => {1, 2, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 4, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 4 → Fin 4
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 3 4 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_7
namespace PureChordal.Examples.G6_8

def bags : Fin 4 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | 1 => {0, 1, 3}
    | 2 => {0, 2, 4}
    | _ => {1, 3, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 4, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 4 → Fin 4
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | _ => 1

def decomp : PureCliqueTreeDecomp graph 3 4 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_8
namespace PureChordal.Examples.G6_9

def bags : Fin 2 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2, 3}
    | _ => {0, 1, 4, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 2, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 2 → Fin 2
  | i => match i.1 with
    | 0 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 4 2 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 4 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_9
namespace PureChordal.Examples.G6_10

def bags : Fin 3 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2, 3}
    | 1 => {0, 1, 2, 4}
    | _ => {0, 1, 2, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 3, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 3 → Fin 3
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 4 3 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 4 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_10
namespace PureChordal.Examples.G6_11

def bags : Fin 3 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2, 3}
    | 1 => {0, 1, 2, 4}
    | _ => {0, 1, 3, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 3, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 3 → Fin 3
  | i => match i.1 with
    | 0 => 0
    | 1 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 4 3 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 4 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_11
namespace PureChordal.Examples.G6_12

def bags : Fin 2 → Finset (Fin 6)
  | i => match i.1 with
    | 0 => {0, 1, 2, 3, 4}
    | _ => {0, 1, 2, 3, 5}

def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 2, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

def parent : Fin 2 → Fin 2
  | i => match i.1 with
    | 0 => 0
    | _ => 0

def decomp : PureCliqueTreeDecomp graph 5 2 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 5 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G6_12
