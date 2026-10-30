import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair02_12
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link01 4) (link link07 2) Data02.matrix Data12.matrix
def finish := crossMapFinish link01 link07 hole 4 2
def table0 : Point → Point := anchorTable hole hole 2
def table1 : Point → Point := put table0 0 4
def table2 : Point → Point := put table1 1 5
def table3 : Point → Point := put table2 2 6
def table4 : Point → Point := put table3 3 7
def table5 : Point → Point := put table2 2 7
def table6 : Point → Point := put table5 3 6
def table7 : Point → Point := put table0 0 5
def table8 : Point → Point := put table7 1 4
def table9 : Point → Point := put table8 2 6
def table10 : Point → Point := put table9 3 7
def table11 : Point → Point := put table8 2 7
def table12 : Point → Point := put table11 3 6

theorem bound12 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [0,1,3,8,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound11 : ∀ f ∈ assignSearch step finish [3,5,6,7,8,9,10,11] [0,1,3,6,8,9,10,11] table11, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,8,9,10,11] [0,1,3,6,8,9,10,11] [6] table11 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound12

theorem bound10 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [0,1,3,8,9,10,11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound9 : ∀ f ∈ assignSearch step finish [3,5,6,7,8,9,10,11] [0,1,3,7,8,9,10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,8,9,10,11] [0,1,3,7,8,9,10,11] [7] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [2,3,5,6,7,8,9,10,11] [0,1,3,6,7,8,9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,6,7,8,9,10,11] [0,1,3,6,7,8,9,10,11] [6,7] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound9
    · exact bound11

theorem bound7 : ∀ f ∈ assignSearch step finish [1,2,3,5,6,7,8,9,10,11] [0,1,3,4,6,7,8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,5,6,7,8,9,10,11] [0,1,3,4,6,7,8,9,10,11] [4] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [0,1,3,8,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound5 : ∀ f ∈ assignSearch step finish [3,5,6,7,8,9,10,11] [0,1,3,6,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,8,9,10,11] [0,1,3,6,8,9,10,11] [6] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [0,1,3,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound3 : ∀ f ∈ assignSearch step finish [3,5,6,7,8,9,10,11] [0,1,3,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,8,9,10,11] [0,1,3,7,8,9,10,11] [7] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ f ∈ assignSearch step finish [2,3,5,6,7,8,9,10,11] [0,1,3,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,6,7,8,9,10,11] [0,1,3,6,7,8,9,10,11] [6,7] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound5

theorem bound1 : ∀ f ∈ assignSearch step finish [1,2,3,5,6,7,8,9,10,11] [0,1,3,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,5,6,7,8,9,10,11] [0,1,3,5,6,7,8,9,10,11] [5] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [0,1,2,3,5,6,7,8,9,10,11] [0,1,3,4,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,2,3,5,6,7,8,9,10,11] [0,1,3,4,5,6,7,8,9,10,11] [4,5] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound7

theorem complete (e : Equiv.Perm Point) (he : e hole = 2) (hc : e (4 : Point) = hole)
    (hs : transport e (link link01 4) = link link07 2) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link01 link07 hole 4 2 [0,1,2,3,5,6,7,8,9,10,11]
    (by decide +kernel) (by decide +kernel) Data02.matrix Data12.matrix
    Data02.matrix_checked Data12.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link01 link07 hole 4 hole 2 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link01 link07 hole 4 hole 2 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair02_12
