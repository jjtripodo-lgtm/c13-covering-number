import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair47_47
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := [![0,1,2,3,12,5,6,7,8,9,10,11,4]]
def step := starStep (link link46 4) (link link46 4) Data47.matrix Data47.matrix
def finish := crossMapFinish link46 link46 hole 4 4
def table0 : Point → Point := anchorTable hole hole 4
def table1 : Point → Point := put table0 6 6
def table2 : Point → Point := put table1 7 7
def table3 : Point → Point := put table2 0 0
def table4 : Point → Point := put table3 2 2
def table5 : Point → Point := put table4 10 10
def table6 : Point → Point := put table5 1 1
def table7 : Point → Point := put table6 3 3
def table8 : Point → Point := put table7 5 5
def table9 : Point → Point := put table8 8 8
def table10 : Point → Point := put table9 9 9
def table11 : Point → Point := put table10 11 11
def table12 : Point → Point := put table2 0 10
def table13 : Point → Point := put table0 6 7
def table14 : Point → Point := put table13 7 6
def table15 : Point → Point := put table14 0 0
def table16 : Point → Point := put table14 0 10

theorem bound16 : ∀ f ∈ assignSearch step finish [2,10,1,3,5,8,9,11] [0,1,2,3,5,8,9,11] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [10,1,3,5,8,9,11] [0,1,2,3,5,8,9,11] [] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound15 : ∀ f ∈ assignSearch step finish [2,10,1,3,5,8,9,11] [1,2,3,5,8,9,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [10,1,3,5,8,9,11] [1,2,3,5,8,9,10,11] [] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound14 : ∀ f ∈ assignSearch step finish [0,2,10,1,3,5,8,9,11] [0,1,2,3,5,8,9,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [2,10,1,3,5,8,9,11] [0,1,2,3,5,8,9,10,11] [0,10] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound15
    · exact bound16

theorem bound13 : ∀ f ∈ assignSearch step finish [7,0,2,10,1,3,5,8,9,11] [0,1,2,3,5,6,8,9,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,2,10,1,3,5,8,9,11] [0,1,2,3,5,6,8,9,10,11] [6] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ f ∈ assignSearch step finish [2,10,1,3,5,8,9,11] [0,1,2,3,5,8,9,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [10,1,3,5,8,9,11] [0,1,2,3,5,8,9,11] [] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound11 : ∀ f ∈ assignSearch step finish [] [] table11, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound10 : ∀ f ∈ assignSearch step finish [11] [11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound11

theorem bound9 : ∀ f ∈ assignSearch step finish [9,11] [9,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [9,11] [9] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [8,9,11] [8,9,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [8,9,11] [8] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound9

theorem bound7 : ∀ f ∈ assignSearch step finish [5,8,9,11] [5,8,9,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [8,9,11] [5,8,9,11] [5] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [3,5,8,9,11] [3,5,8,9,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,8,9,11] [3,5,8,9,11] [3] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [1,3,5,8,9,11] [1,3,5,8,9,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,5,8,9,11] [1,3,5,8,9,11] [1] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [10,1,3,5,8,9,11] [1,3,5,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [1,3,5,8,9,11] [1,3,5,8,9,10,11] [10] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [2,10,1,3,5,8,9,11] [1,2,3,5,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [10,1,3,5,8,9,11] [1,2,3,5,8,9,10,11] [2] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ f ∈ assignSearch step finish [0,2,10,1,3,5,8,9,11] [0,1,2,3,5,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [2,10,1,3,5,8,9,11] [0,1,2,3,5,8,9,10,11] [0,10] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound12

theorem bound1 : ∀ f ∈ assignSearch step finish [7,0,2,10,1,3,5,8,9,11] [0,1,2,3,5,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,2,10,1,3,5,8,9,11] [0,1,2,3,5,7,8,9,10,11] [7] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [6,7,0,2,10,1,3,5,8,9,11] [0,1,2,3,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,2,10,1,3,5,8,9,11] [0,1,2,3,5,6,7,8,9,10,11] [6,7] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound13

theorem complete (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (4 : Point) = hole)
    (hs : transport e (link link46 4) = link link46 4) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link46 link46 hole 4 4 [6,7,0,2,10,1,3,5,8,9,11]
    (by decide +kernel) (by decide +kernel) Data47.matrix Data47.matrix
    Data47.matrix_checked Data47.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link46 link46 hole 4 hole 4 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link46 link46 hole 4 hole 4 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair47_47
