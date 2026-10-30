import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair39_49
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link36 5) (link link50 4) Data39.matrix Data49.matrix
def finish := crossMapFinish link36 link50 hole 5 4
def table0 : Point → Point := anchorTable hole hole 4
def table1 : Point → Point := put table0 6 6
def table2 : Point → Point := put table1 7 7
def table3 : Point → Point := put table2 0 0
def table4 : Point → Point := put table3 4 5
def table5 : Point → Point := put table2 0 10
def table6 : Point → Point := put table5 4 5
def table7 : Point → Point := put table0 6 7
def table8 : Point → Point := put table7 7 6
def table9 : Point → Point := put table8 0 0
def table10 : Point → Point := put table9 4 5
def table11 : Point → Point := put table8 0 10
def table12 : Point → Point := put table11 4 5

theorem bound12 : ∀ f ∈ assignSearch step finish [8,1,2,3,9,10,11] [0,1,2,3,8,9,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,9,10,11] [0,1,2,3,8,9,11] [] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound11 : ∀ f ∈ assignSearch step finish [4,8,1,2,3,9,10,11] [0,1,2,3,5,8,9,11] table11, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [8,1,2,3,9,10,11] [0,1,2,3,5,8,9,11] [5] table11 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound12

theorem bound10 : ∀ f ∈ assignSearch step finish [8,1,2,3,9,10,11] [1,2,3,8,9,10,11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,9,10,11] [1,2,3,8,9,10,11] [] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound9 : ∀ f ∈ assignSearch step finish [4,8,1,2,3,9,10,11] [1,2,3,5,8,9,10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [8,1,2,3,9,10,11] [1,2,3,5,8,9,10,11] [5] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [0,4,8,1,2,3,9,10,11] [0,1,2,3,5,8,9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [4,8,1,2,3,9,10,11] [0,1,2,3,5,8,9,10,11] [0,10] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound9
    · exact bound11

theorem bound7 : ∀ f ∈ assignSearch step finish [7,0,4,8,1,2,3,9,10,11] [0,1,2,3,5,6,8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,8,1,2,3,9,10,11] [0,1,2,3,5,6,8,9,10,11] [6] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [8,1,2,3,9,10,11] [0,1,2,3,8,9,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,9,10,11] [0,1,2,3,8,9,11] [] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound5 : ∀ f ∈ assignSearch step finish [4,8,1,2,3,9,10,11] [0,1,2,3,5,8,9,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [8,1,2,3,9,10,11] [0,1,2,3,5,8,9,11] [5] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [8,1,2,3,9,10,11] [1,2,3,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,9,10,11] [1,2,3,8,9,10,11] [] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound3 : ∀ f ∈ assignSearch step finish [4,8,1,2,3,9,10,11] [1,2,3,5,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [8,1,2,3,9,10,11] [1,2,3,5,8,9,10,11] [5] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ f ∈ assignSearch step finish [0,4,8,1,2,3,9,10,11] [0,1,2,3,5,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [4,8,1,2,3,9,10,11] [0,1,2,3,5,8,9,10,11] [0,10] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound5

theorem bound1 : ∀ f ∈ assignSearch step finish [7,0,4,8,1,2,3,9,10,11] [0,1,2,3,5,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,8,1,2,3,9,10,11] [0,1,2,3,5,7,8,9,10,11] [7] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [6,7,0,4,8,1,2,3,9,10,11] [0,1,2,3,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,8,1,2,3,9,10,11] [0,1,2,3,5,6,7,8,9,10,11] [6,7] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound7

theorem complete (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (5 : Point) = hole)
    (hs : transport e (link link36 5) = link link50 4) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link36 link50 hole 5 4 [6,7,0,4,8,1,2,3,9,10,11]
    (by decide +kernel) (by decide +kernel) Data39.matrix Data49.matrix
    Data39.matrix_checked Data49.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link36 link50 hole 5 hole 4 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link36 link50 hole 5 hole 4 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair39_49
