import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair37_37
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := [![0,1,2,3,4,12,6,7,8,9,10,11,5]]
def step := starStep (link link33 5) (link link33 5) Data37.matrix Data37.matrix
def finish := crossMapFinish link33 link33 hole 5 5
def table0 : Point → Point := anchorTable hole hole 5
def table1 : Point → Point := put table0 6 6
def table2 : Point → Point := put table1 7 7
def table3 : Point → Point := put table2 0 0
def table4 : Point → Point := put table3 2 2
def table5 : Point → Point := put table4 8 8
def table6 : Point → Point := put table5 1 1
def table7 : Point → Point := put table6 3 3
def table8 : Point → Point := put table7 4 4
def table9 : Point → Point := put table8 9 9
def table10 : Point → Point := put table9 10 10
def table11 : Point → Point := put table10 11 11
def table12 : Point → Point := put table2 0 8
def table13 : Point → Point := put table0 6 7
def table14 : Point → Point := put table13 7 6
def table15 : Point → Point := put table14 0 0
def table16 : Point → Point := put table14 0 8
def table17 : Point → Point := put table16 2 2
def table18 : Point → Point := put table17 8 0
def table19 : Point → Point := put table18 1 9
def table20 : Point → Point := put table19 3 10

theorem bound20 : ∀ f ∈ assignSearch step finish [4,9,10,11] [1,3,4,11] table20, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [9,10,11] [1,3,4,11] [] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound19 : ∀ f ∈ assignSearch step finish [3,4,9,10,11] [1,3,4,10,11] table19, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,9,10,11] [1,3,4,10,11] [10] table19 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound20

theorem bound18 : ∀ f ∈ assignSearch step finish [1,3,4,9,10,11] [1,3,4,9,10,11] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,4,9,10,11] [1,3,4,9,10,11] [9] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ f ∈ assignSearch step finish [8,1,3,4,9,10,11] [0,1,3,4,9,10,11] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,3,4,9,10,11] [0,1,3,4,9,10,11] [0] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [2,8,1,3,4,9,10,11] [0,1,2,3,4,9,10,11] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [8,1,3,4,9,10,11] [0,1,2,3,4,9,10,11] [2] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound17

theorem bound15 : ∀ f ∈ assignSearch step finish [2,8,1,3,4,9,10,11] [1,2,3,4,8,9,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [8,1,3,4,9,10,11] [1,2,3,4,8,9,10,11] [] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound14 : ∀ f ∈ assignSearch step finish [0,2,8,1,3,4,9,10,11] [0,1,2,3,4,8,9,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [2,8,1,3,4,9,10,11] [0,1,2,3,4,8,9,10,11] [0,8] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound15
    · exact bound16

theorem bound13 : ∀ f ∈ assignSearch step finish [7,0,2,8,1,3,4,9,10,11] [0,1,2,3,4,6,8,9,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,2,8,1,3,4,9,10,11] [0,1,2,3,4,6,8,9,10,11] [6] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ f ∈ assignSearch step finish [2,8,1,3,4,9,10,11] [0,1,2,3,4,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [8,1,3,4,9,10,11] [0,1,2,3,4,9,10,11] [] table12 ?_ ?_
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

theorem bound9 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound9

theorem bound7 : ∀ f ∈ assignSearch step finish [4,9,10,11] [4,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [9,10,11] [4,9,10,11] [4] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [3,4,9,10,11] [3,4,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,9,10,11] [3,4,9,10,11] [3] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [1,3,4,9,10,11] [1,3,4,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,4,9,10,11] [1,3,4,9,10,11] [1] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [8,1,3,4,9,10,11] [1,3,4,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,3,4,9,10,11] [1,3,4,8,9,10,11] [8] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [2,8,1,3,4,9,10,11] [1,2,3,4,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [8,1,3,4,9,10,11] [1,2,3,4,8,9,10,11] [2] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ f ∈ assignSearch step finish [0,2,8,1,3,4,9,10,11] [0,1,2,3,4,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [2,8,1,3,4,9,10,11] [0,1,2,3,4,8,9,10,11] [0,8] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound12

theorem bound1 : ∀ f ∈ assignSearch step finish [7,0,2,8,1,3,4,9,10,11] [0,1,2,3,4,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,2,8,1,3,4,9,10,11] [0,1,2,3,4,7,8,9,10,11] [7] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [6,7,0,2,8,1,3,4,9,10,11] [0,1,2,3,4,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,2,8,1,3,4,9,10,11] [0,1,2,3,4,6,7,8,9,10,11] [6,7] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound13

theorem complete (e : Equiv.Perm Point) (he : e hole = 5) (hc : e (5 : Point) = hole)
    (hs : transport e (link link33 5) = link link33 5) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link33 link33 hole 5 5 [6,7,0,2,8,1,3,4,9,10,11]
    (by decide +kernel) (by decide +kernel) Data37.matrix Data37.matrix
    Data37.matrix_checked Data37.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link33 link33 hole 5 hole 5 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link33 link33 hole 5 hole 5 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair37_37
