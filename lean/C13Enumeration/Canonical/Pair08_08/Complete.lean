import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair08_08
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := [![0,1,2,3,4,5,12,7,8,9,10,11,6],![0,1,3,2,5,4,12,7,9,8,10,11,6]]
def step := starStep (link link04 6) (link link04 6) Data08.matrix Data08.matrix
def finish := crossMapFinish link04 link04 hole 6 6
def table0 : Point → Point := anchorTable hole hole 6
def table1 : Point → Point := put table0 0 0
def table2 : Point → Point := put table1 1 1
def table3 : Point → Point := put table2 8 8
def table4 : Point → Point := put table3 9 9
def table5 : Point → Point := put table4 10 10
def table6 : Point → Point := put table5 11 11
def table7 : Point → Point := put table6 2 2
def table8 : Point → Point := put table7 3 3
def table9 : Point → Point := put table8 4 4
def table10 : Point → Point := put table9 5 5
def table11 : Point → Point := put table10 7 7
def table12 : Point → Point := put table2 8 9
def table13 : Point → Point := put table12 9 8
def table14 : Point → Point := put table13 10 10
def table15 : Point → Point := put table14 11 11
def table16 : Point → Point := put table15 2 3
def table17 : Point → Point := put table16 3 2
def table18 : Point → Point := put table17 4 5
def table19 : Point → Point := put table18 5 4
def table20 : Point → Point := put table19 7 7
def table21 : Point → Point := put table1 1 8
def table22 : Point → Point := put table21 8 1
def table23 : Point → Point := put table1 1 9
def table24 : Point → Point := put table23 8 1
def table25 : Point → Point := put table1 1 11

theorem bound25 : ∀ f ∈ assignSearch step finish [8,9,10,11,2,3,4,5,7] [1,2,3,4,5,7,8,9,10] table25, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11,2,3,4,5,7] [1,2,3,4,5,7,8,9,10] [] table25 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound24 : ∀ f ∈ assignSearch step finish [9,10,11,2,3,4,5,7] [2,3,4,5,7,8,10,11] table24, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11,2,3,4,5,7] [2,3,4,5,7,8,10,11] [] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound23 : ∀ f ∈ assignSearch step finish [8,9,10,11,2,3,4,5,7] [1,2,3,4,5,7,8,10,11] table23, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11,2,3,4,5,7] [1,2,3,4,5,7,8,10,11] [1] table23 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound24

theorem bound22 : ∀ f ∈ assignSearch step finish [9,10,11,2,3,4,5,7] [2,3,4,5,7,9,10,11] table22, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11,2,3,4,5,7] [2,3,4,5,7,9,10,11] [] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound21 : ∀ f ∈ assignSearch step finish [8,9,10,11,2,3,4,5,7] [1,2,3,4,5,7,9,10,11] table21, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11,2,3,4,5,7] [1,2,3,4,5,7,9,10,11] [1] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound22

theorem bound20 : ∀ f ∈ assignSearch step finish [] [] table20, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound19 : ∀ f ∈ assignSearch step finish [7] [7] table19, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [] [7] [7] table19 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound20

theorem bound18 : ∀ f ∈ assignSearch step finish [5,7] [4,7] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7] [4,7] [4] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ f ∈ assignSearch step finish [4,5,7] [4,5,7] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7] [4,5,7] [5] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [3,4,5,7] [2,4,5,7] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7] [2,4,5,7] [2] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound17

theorem bound15 : ∀ f ∈ assignSearch step finish [2,3,4,5,7] [2,3,4,5,7] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,7] [2,3,4,5,7] [3] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ f ∈ assignSearch step finish [11,2,3,4,5,7] [2,3,4,5,7,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [2,3,4,5,7] [2,3,4,5,7,11] [11] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound15

theorem bound13 : ∀ f ∈ assignSearch step finish [10,11,2,3,4,5,7] [2,3,4,5,7,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,2,3,4,5,7] [2,3,4,5,7,10,11] [10] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ f ∈ assignSearch step finish [9,10,11,2,3,4,5,7] [2,3,4,5,7,8,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11,2,3,4,5,7] [2,3,4,5,7,8,10,11] [8] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound13

theorem bound11 : ∀ f ∈ assignSearch step finish [] [] table11, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound10 : ∀ f ∈ assignSearch step finish [7] [7] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [] [7] [7] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound11

theorem bound9 : ∀ f ∈ assignSearch step finish [5,7] [5,7] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7] [5,7] [5] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [4,5,7] [4,5,7] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7] [4,5,7] [4] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound9

theorem bound7 : ∀ f ∈ assignSearch step finish [3,4,5,7] [3,4,5,7] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7] [3,4,5,7] [3] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [2,3,4,5,7] [2,3,4,5,7] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,7] [2,3,4,5,7] [2] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [11,2,3,4,5,7] [2,3,4,5,7,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [2,3,4,5,7] [2,3,4,5,7,11] [11] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [10,11,2,3,4,5,7] [2,3,4,5,7,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,2,3,4,5,7] [2,3,4,5,7,10,11] [10] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [9,10,11,2,3,4,5,7] [2,3,4,5,7,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11,2,3,4,5,7] [2,3,4,5,7,9,10,11] [9] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ f ∈ assignSearch step finish [8,9,10,11,2,3,4,5,7] [2,3,4,5,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11,2,3,4,5,7] [2,3,4,5,7,8,9,10,11] [8,9] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound12

theorem bound1 : ∀ f ∈ assignSearch step finish [1,8,9,10,11,2,3,4,5,7] [1,2,3,4,5,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,10,11,2,3,4,5,7] [1,2,3,4,5,7,8,9,10,11] [1,8,9,11] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound2
    · exact bound21
    · exact bound23
    · exact bound25

theorem bound0 : ∀ f ∈ assignSearch step finish [0,1,8,9,10,11,2,3,4,5,7] [0,1,2,3,4,5,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,8,9,10,11,2,3,4,5,7] [0,1,2,3,4,5,7,8,9,10,11] [0] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound1

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (6 : Point) = hole)
    (hs : transport e (link link04 6) = link link04 6) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link04 link04 hole 6 6 [0,1,8,9,10,11,2,3,4,5,7]
    (by decide +kernel) (by decide +kernel) Data08.matrix Data08.matrix
    Data08.matrix_checked Data08.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link04 link04 hole 6 hole 6 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link04 link04 hole 6 hole 6 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair08_08
