import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair04_09
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link02 2) (link link05 2) Data04.matrix Data09.matrix
def finish := crossMapFinish link02 link05 hole 2 2
def table0 : Point → Point := anchorTable hole hole 2
def table1 : Point → Point := put table0 1 0
def table2 : Point → Point := put table1 3 1
def table3 : Point → Point := put table2 6 6
def table4 : Point → Point := put table2 6 7
def table5 : Point → Point := put table1 3 6
def table6 : Point → Point := put table5 6 1
def table7 : Point → Point := put table5 6 7
def table8 : Point → Point := put table1 3 7
def table9 : Point → Point := put table8 6 1
def table10 : Point → Point := put table8 6 6
def table11 : Point → Point := put table0 1 1
def table12 : Point → Point := put table11 3 0
def table13 : Point → Point := put table12 6 6
def table14 : Point → Point := put table12 6 7
def table15 : Point → Point := put table11 3 6
def table16 : Point → Point := put table15 6 0
def table17 : Point → Point := put table15 6 7
def table18 : Point → Point := put table11 3 7
def table19 : Point → Point := put table18 6 0
def table20 : Point → Point := put table18 6 6
def table21 : Point → Point := put table0 1 6
def table22 : Point → Point := put table21 3 0
def table23 : Point → Point := put table22 6 1
def table24 : Point → Point := put table22 6 7
def table25 : Point → Point := put table21 3 1
def table26 : Point → Point := put table25 6 0
def table27 : Point → Point := put table25 6 7
def table28 : Point → Point := put table21 3 7
def table29 : Point → Point := put table28 6 0
def table30 : Point → Point := put table28 6 1
def table31 : Point → Point := put table0 1 7
def table32 : Point → Point := put table31 3 0
def table33 : Point → Point := put table32 6 1
def table34 : Point → Point := put table32 6 6
def table35 : Point → Point := put table31 3 1
def table36 : Point → Point := put table35 6 0
def table37 : Point → Point := put table35 6 6
def table38 : Point → Point := put table31 3 6
def table39 : Point → Point := put table38 6 0
def table40 : Point → Point := put table38 6 1

theorem bound40 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] table40, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] [] table40 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound39 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] table39, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] [] table39 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound38 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [0,1,3,4,5,8,9,10,11] table38, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [0,1,3,4,5,8,9,10,11] [0,1] table38 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound39
    · exact bound40

theorem bound37 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] table37, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] [] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound36 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] table36, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] [] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound35 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [0,3,4,5,6,8,9,10,11] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [0,3,4,5,6,8,9,10,11] [0,6] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound36
    · exact bound37

theorem bound34 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] table34, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] [] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound33 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] table33, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] [] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound32 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [1,3,4,5,6,8,9,10,11] table32, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [1,3,4,5,6,8,9,10,11] [1,6] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound33
    · exact bound34

theorem bound31 : ∀ f ∈ assignSearch step finish [3,6,7,0,4,5,8,9,10,11] [0,1,3,4,5,6,8,9,10,11] table31, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,0,4,5,8,9,10,11] [0,1,3,4,5,6,8,9,10,11] [0,1,6] table31 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound32
    · exact bound35
    · exact bound38

theorem bound30 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] table30, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] [] table30 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound29 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] table29, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] [] table29 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound28 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [0,1,3,4,5,8,9,10,11] table28, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [0,1,3,4,5,8,9,10,11] [0,1] table28 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound29
    · exact bound30

theorem bound27 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] table27, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] [] table27 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound26 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] table26, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] [] table26 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound25 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [0,3,4,5,7,8,9,10,11] table25, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [0,3,4,5,7,8,9,10,11] [0,7] table25 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound26
    · exact bound27

theorem bound24 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] table24, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] [] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound23 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] table23, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] [] table23 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound22 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [1,3,4,5,7,8,9,10,11] table22, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [1,3,4,5,7,8,9,10,11] [1,7] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound23
    · exact bound24

theorem bound21 : ∀ f ∈ assignSearch step finish [3,6,7,0,4,5,8,9,10,11] [0,1,3,4,5,7,8,9,10,11] table21, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,0,4,5,8,9,10,11] [0,1,3,4,5,7,8,9,10,11] [0,1,7] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound22
    · exact bound25
    · exact bound28

theorem bound20 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] table20, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] [] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound19 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] table19, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] [] table19 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound18 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [0,3,4,5,6,8,9,10,11] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [0,3,4,5,6,8,9,10,11] [0,6] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound19
    · exact bound20

theorem bound17 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [0,3,4,5,8,9,10,11] [] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound16 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] [] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound15 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [0,3,4,5,7,8,9,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [0,3,4,5,7,8,9,10,11] [0,7] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound16
    · exact bound17

theorem bound14 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] [] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound13 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] [] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound12 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [3,4,5,6,7,8,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [3,4,5,6,7,8,9,10,11] [6,7] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound13
    · exact bound14

theorem bound11 : ∀ f ∈ assignSearch step finish [3,6,7,0,4,5,8,9,10,11] [0,3,4,5,6,7,8,9,10,11] table11, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,0,4,5,8,9,10,11] [0,3,4,5,6,7,8,9,10,11] [0,6,7] table11 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound12
    · exact bound15
    · exact bound18

theorem bound10 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] [] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound9 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] [] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound8 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [1,3,4,5,6,8,9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [1,3,4,5,6,8,9,10,11] [1,6] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound9
    · exact bound10

theorem bound7 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [1,3,4,5,8,9,10,11] [] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound6 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] [] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound5 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [1,3,4,5,7,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [1,3,4,5,7,8,9,10,11] [1,7] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound6
    · exact bound7

theorem bound4 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,6,8,9,10,11] [] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound3 : ∀ f ∈ assignSearch step finish [7,0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,4,5,8,9,10,11] [3,4,5,7,8,9,10,11] [] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound2 : ∀ f ∈ assignSearch step finish [6,7,0,4,5,8,9,10,11] [3,4,5,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,4,5,8,9,10,11] [3,4,5,6,7,8,9,10,11] [6,7] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound4

theorem bound1 : ∀ f ∈ assignSearch step finish [3,6,7,0,4,5,8,9,10,11] [1,3,4,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,0,4,5,8,9,10,11] [1,3,4,5,6,7,8,9,10,11] [1,6,7] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound2
    · exact bound5
    · exact bound8

theorem bound0 : ∀ f ∈ assignSearch step finish [1,3,6,7,0,4,5,8,9,10,11] [0,1,3,4,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,6,7,0,4,5,8,9,10,11] [0,1,3,4,5,6,7,8,9,10,11] [0,1,6,7] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound1
    · exact bound11
    · exact bound21
    · exact bound31

theorem complete (e : Equiv.Perm Point) (he : e hole = 2) (hc : e (2 : Point) = hole)
    (hs : transport e (link link02 2) = link link05 2) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link02 link05 hole 2 2 [1,3,6,7,0,4,5,8,9,10,11]
    (by decide +kernel) (by decide +kernel) Data04.matrix Data09.matrix
    Data04.matrix_checked Data09.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link02 link05 hole 2 hole 2 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link02 link05 hole 2 hole 2 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair04_09
