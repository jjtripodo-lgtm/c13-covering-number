import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair17_15
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link09 4) (link link08 5) Data17.matrix Data15.matrix
def finish := crossMapFinish link09 link08 hole 4 5
def table0 : Point → Point := anchorTable hole hole 5
def table1 : Point → Point := put table0 0 0
def table2 : Point → Point := put table1 1 1
def table3 : Point → Point := put table2 2 2
def table4 : Point → Point := put table3 3 3
def table5 : Point → Point := put table4 5 4
def table6 : Point → Point := put table2 2 3
def table7 : Point → Point := put table6 3 2
def table8 : Point → Point := put table7 5 4
def table9 : Point → Point := put table1 1 2
def table10 : Point → Point := put table9 2 1
def table11 : Point → Point := put table10 3 3
def table12 : Point → Point := put table9 2 3
def table13 : Point → Point := put table12 3 1
def table14 : Point → Point := put table1 1 3
def table15 : Point → Point := put table14 2 1
def table16 : Point → Point := put table15 3 2
def table17 : Point → Point := put table14 2 2
def table18 : Point → Point := put table17 3 1
def table19 : Point → Point := put table1 1 8

theorem bound19 : ∀ f ∈ assignSearch step finish [2,3,5,10,6,7,8,9,11] [1,2,3,4,6,7,9,10,11] table19, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,10,6,7,8,9,11] [1,2,3,4,6,7,9,10,11] [] table19 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound18 : ∀ f ∈ assignSearch step finish [5,10,6,7,8,9,11] [4,6,7,8,9,10,11] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [10,6,7,8,9,11] [4,6,7,8,9,10,11] [] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound17 : ∀ f ∈ assignSearch step finish [3,5,10,6,7,8,9,11] [1,4,6,7,8,9,10,11] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,10,6,7,8,9,11] [1,4,6,7,8,9,10,11] [1] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [5,10,6,7,8,9,11] [4,6,7,8,9,10,11] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [10,6,7,8,9,11] [4,6,7,8,9,10,11] [] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound15 : ∀ f ∈ assignSearch step finish [3,5,10,6,7,8,9,11] [2,4,6,7,8,9,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,10,6,7,8,9,11] [2,4,6,7,8,9,10,11] [2] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ f ∈ assignSearch step finish [2,3,5,10,6,7,8,9,11] [1,2,4,6,7,8,9,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,10,6,7,8,9,11] [1,2,4,6,7,8,9,10,11] [1,2] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound15
    · exact bound17

theorem bound13 : ∀ f ∈ assignSearch step finish [5,10,6,7,8,9,11] [4,6,7,8,9,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [10,6,7,8,9,11] [4,6,7,8,9,10,11] [] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound12 : ∀ f ∈ assignSearch step finish [3,5,10,6,7,8,9,11] [1,4,6,7,8,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,10,6,7,8,9,11] [1,4,6,7,8,9,10,11] [1] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound13

theorem bound11 : ∀ f ∈ assignSearch step finish [5,10,6,7,8,9,11] [4,6,7,8,9,10,11] table11, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [10,6,7,8,9,11] [4,6,7,8,9,10,11] [] table11 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound10 : ∀ f ∈ assignSearch step finish [3,5,10,6,7,8,9,11] [3,4,6,7,8,9,10,11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,10,6,7,8,9,11] [3,4,6,7,8,9,10,11] [3] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound11

theorem bound9 : ∀ f ∈ assignSearch step finish [2,3,5,10,6,7,8,9,11] [1,3,4,6,7,8,9,10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,10,6,7,8,9,11] [1,3,4,6,7,8,9,10,11] [1,3] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound10
    · exact bound12

theorem bound8 : ∀ f ∈ assignSearch step finish [10,6,7,8,9,11] [6,7,8,9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [6,7,8,9,11] [6,7,8,9,10,11] [] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound7 : ∀ f ∈ assignSearch step finish [5,10,6,7,8,9,11] [4,6,7,8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [10,6,7,8,9,11] [4,6,7,8,9,10,11] [4] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [3,5,10,6,7,8,9,11] [2,4,6,7,8,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,10,6,7,8,9,11] [2,4,6,7,8,9,10,11] [2] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [10,6,7,8,9,11] [6,7,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [6,7,8,9,11] [6,7,8,9,10,11] [] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound4 : ∀ f ∈ assignSearch step finish [5,10,6,7,8,9,11] [4,6,7,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [10,6,7,8,9,11] [4,6,7,8,9,10,11] [4] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [3,5,10,6,7,8,9,11] [3,4,6,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,10,6,7,8,9,11] [3,4,6,7,8,9,10,11] [3] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ f ∈ assignSearch step finish [2,3,5,10,6,7,8,9,11] [2,3,4,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,10,6,7,8,9,11] [2,3,4,6,7,8,9,10,11] [2,3] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound6

theorem bound1 : ∀ f ∈ assignSearch step finish [1,2,3,5,10,6,7,8,9,11] [1,2,3,4,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,5,10,6,7,8,9,11] [1,2,3,4,6,7,8,9,10,11] [1,2,3,8] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound2
    · exact bound9
    · exact bound14
    · exact bound19

theorem bound0 : ∀ f ∈ assignSearch step finish [0,1,2,3,5,10,6,7,8,9,11] [0,1,2,3,4,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,2,3,5,10,6,7,8,9,11] [0,1,2,3,4,6,7,8,9,10,11] [0] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound1

theorem complete (e : Equiv.Perm Point) (he : e hole = 5) (hc : e (4 : Point) = hole)
    (hs : transport e (link link09 4) = link link08 5) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link09 link08 hole 4 5 [0,1,2,3,5,10,6,7,8,9,11]
    (by decide +kernel) (by decide +kernel) Data17.matrix Data15.matrix
    Data17.matrix_checked Data15.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link09 link08 hole 4 hole 5 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link09 link08 hole 4 hole 5 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair17_15
