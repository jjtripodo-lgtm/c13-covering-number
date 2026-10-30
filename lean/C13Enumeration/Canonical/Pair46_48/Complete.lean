import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair46_48
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link43 4) (link link47 5) Data46.matrix Data48.matrix
def finish := crossMapFinish link43 link47 hole 4 5
def table0 : Point → Point := anchorTable hole hole 5
def table1 : Point → Point := put table0 6 6
def table2 : Point → Point := put table1 7 7
def table3 : Point → Point := put table2 0 0
def table4 : Point → Point := put table2 0 10
def table5 : Point → Point := put table4 1 2
def table6 : Point → Point := put table5 10 0
def table7 : Point → Point := put table6 2 9
def table8 : Point → Point := put table7 3 8
def table9 : Point → Point := put table0 6 7
def table10 : Point → Point := put table9 7 6
def table11 : Point → Point := put table10 0 0
def table12 : Point → Point := put table10 0 10
def table13 : Point → Point := put table12 1 2

theorem bound13 : ∀ f ∈ assignSearch step finish [10,2,3,5,8,9,11] [0,1,3,4,8,9,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [2,3,5,8,9,11] [0,1,3,4,8,9,11] [] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound12 : ∀ f ∈ assignSearch step finish [1,10,2,3,5,8,9,11] [0,1,2,3,4,8,9,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [10,2,3,5,8,9,11] [0,1,2,3,4,8,9,11] [2] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound13

theorem bound11 : ∀ f ∈ assignSearch step finish [1,10,2,3,5,8,9,11] [1,2,3,4,8,9,10,11] table11, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [10,2,3,5,8,9,11] [1,2,3,4,8,9,10,11] [] table11 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound10 : ∀ f ∈ assignSearch step finish [0,1,10,2,3,5,8,9,11] [0,1,2,3,4,8,9,10,11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,10,2,3,5,8,9,11] [0,1,2,3,4,8,9,10,11] [0,10] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound11
    · exact bound12

theorem bound9 : ∀ f ∈ assignSearch step finish [7,0,1,10,2,3,5,8,9,11] [0,1,2,3,4,6,8,9,10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,1,10,2,3,5,8,9,11] [0,1,2,3,4,6,8,9,10,11] [6] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [5,8,9,11] [1,3,4,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [8,9,11] [1,3,4,11] [] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound7 : ∀ f ∈ assignSearch step finish [3,5,8,9,11] [1,3,4,8,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,8,9,11] [1,3,4,8,11] [8] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [2,3,5,8,9,11] [1,3,4,8,9,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,8,9,11] [1,3,4,8,9,11] [9] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [10,2,3,5,8,9,11] [0,1,3,4,8,9,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [2,3,5,8,9,11] [0,1,3,4,8,9,11] [0] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [1,10,2,3,5,8,9,11] [0,1,2,3,4,8,9,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [10,2,3,5,8,9,11] [0,1,2,3,4,8,9,11] [2] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [1,10,2,3,5,8,9,11] [1,2,3,4,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [10,2,3,5,8,9,11] [1,2,3,4,8,9,10,11] [] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound2 : ∀ f ∈ assignSearch step finish [0,1,10,2,3,5,8,9,11] [0,1,2,3,4,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,10,2,3,5,8,9,11] [0,1,2,3,4,8,9,10,11] [0,10] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound4

theorem bound1 : ∀ f ∈ assignSearch step finish [7,0,1,10,2,3,5,8,9,11] [0,1,2,3,4,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,1,10,2,3,5,8,9,11] [0,1,2,3,4,7,8,9,10,11] [7] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [6,7,0,1,10,2,3,5,8,9,11] [0,1,2,3,4,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,1,10,2,3,5,8,9,11] [0,1,2,3,4,6,7,8,9,10,11] [6,7] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound9

theorem complete (e : Equiv.Perm Point) (he : e hole = 5) (hc : e (4 : Point) = hole)
    (hs : transport e (link link43 4) = link link47 5) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link43 link47 hole 4 5 [6,7,0,1,10,2,3,5,8,9,11]
    (by decide +kernel) (by decide +kernel) Data46.matrix Data48.matrix
    Data46.matrix_checked Data48.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link43 link47 hole 4 hole 5 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link43 link47 hole 4 hole 5 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair46_48
