import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair20_00
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link15 0) (link link01 0) Data20.matrix Data00.matrix
def finish := crossMapFinish link15 link01 hole 0 0
def table0 : Point → Point := anchorTable hole hole 0
def table1 : Point → Point := put table0 1 2
def table2 : Point → Point := put table1 3 3
def table3 : Point → Point := put table2 2 1
def table4 : Point → Point := put table3 4 4
def table5 : Point → Point := put table3 4 5
def table6 : Point → Point := put table0 1 3
def table7 : Point → Point := put table6 3 2
def table8 : Point → Point := put table7 2 1
def table9 : Point → Point := put table8 4 4
def table10 : Point → Point := put table8 4 5

theorem bound10 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [4,6,7,8,9,10,11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [4,6,7,8,9,10,11] [] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound9 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [5,6,7,8,9,10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [5,6,7,8,9,10,11] [] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound8 : ∀ f ∈ assignSearch step finish [4,5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] [4,5] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound9
    · exact bound10

theorem bound7 : ∀ f ∈ assignSearch step finish [2,4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] [1] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [3,2,4,5,6,7,8,9,10,11] [1,2,4,5,6,7,8,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [2,4,5,6,7,8,9,10,11] [1,2,4,5,6,7,8,9,10,11] [2] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [4,6,7,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [4,6,7,8,9,10,11] [] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound4 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [5,6,7,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [5,6,7,8,9,10,11] [] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound3 : ∀ f ∈ assignSearch step finish [4,5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] [4,5] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound4
    · exact bound5

theorem bound2 : ∀ f ∈ assignSearch step finish [2,4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] [1] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound3

theorem bound1 : ∀ f ∈ assignSearch step finish [3,2,4,5,6,7,8,9,10,11] [1,3,4,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [2,4,5,6,7,8,9,10,11] [1,3,4,5,6,7,8,9,10,11] [3] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [1,3,2,4,5,6,7,8,9,10,11] [1,2,3,4,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,2,4,5,6,7,8,9,10,11] [1,2,3,4,5,6,7,8,9,10,11] [2,3] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound6

theorem complete (e : Equiv.Perm Point) (he : e hole = 0) (hc : e (0 : Point) = hole)
    (hs : transport e (link link15 0) = link link01 0) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link15 link01 hole 0 0 [1,3,2,4,5,6,7,8,9,10,11]
    (by decide +kernel) (by decide +kernel) Data20.matrix Data00.matrix
    Data20.matrix_checked Data00.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link15 link01 hole 0 hole 0 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link15 link01 hole 0 hole 0 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair20_00
