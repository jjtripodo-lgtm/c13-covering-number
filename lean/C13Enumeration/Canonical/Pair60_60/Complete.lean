import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair60_60
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := [![0,1,2,3,4,5,6,7,12,9,10,11,8],![5,4,7,6,1,0,3,2,12,9,10,11,8]]
def step := starStep (link link65 8) (link link65 8) Data60.matrix Data60.matrix
def finish := crossMapFinish link65 link65 hole 8 8
def table0 : Point → Point := anchorTable hole hole 8
def table1 : Point → Point := put table0 9 9
def table2 : Point → Point := put table1 10 10
def table3 : Point → Point := put table2 11 11
def table4 : Point → Point := put table3 1 1
def table5 : Point → Point := put table4 2 2
def table6 : Point → Point := put table5 4 4
def table7 : Point → Point := put table6 7 7
def table8 : Point → Point := put table7 0 0
def table9 : Point → Point := put table8 3 3
def table10 : Point → Point := put table9 5 5
def table11 : Point → Point := put table10 6 6
def table12 : Point → Point := put table3 1 4
def table13 : Point → Point := put table12 2 7
def table14 : Point → Point := put table13 4 1
def table15 : Point → Point := put table14 7 2
def table16 : Point → Point := put table15 0 5
def table17 : Point → Point := put table16 3 6
def table18 : Point → Point := put table17 5 0
def table19 : Point → Point := put table18 6 3
def table20 : Point → Point := put table1 10 11
def table21 : Point → Point := put table20 11 10
def table22 : Point → Point := put table21 1 1
def table23 : Point → Point := put table22 2 7
def table24 : Point → Point := put table23 4 4
def table25 : Point → Point := put table24 7 2
def table26 : Point → Point := put table21 1 4
def table27 : Point → Point := put table26 2 2
def table28 : Point → Point := put table27 4 1
def table29 : Point → Point := put table28 7 7
def table30 : Point → Point := put table0 9 10
def table31 : Point → Point := put table30 10 9
def table32 : Point → Point := put table31 11 11
def table33 : Point → Point := put table32 1 1
def table34 : Point → Point := put table33 2 2
def table35 : Point → Point := put table32 1 4
def table36 : Point → Point := put table35 2 7
def table37 : Point → Point := put table30 10 11
def table38 : Point → Point := put table37 11 9
def table39 : Point → Point := put table38 1 1
def table40 : Point → Point := put table38 1 4
def table41 : Point → Point := put table0 9 11
def table42 : Point → Point := put table41 10 9
def table43 : Point → Point := put table42 11 10
def table44 : Point → Point := put table43 1 1
def table45 : Point → Point := put table44 2 7
def table46 : Point → Point := put table43 1 4
def table47 : Point → Point := put table46 2 2
def table48 : Point → Point := put table41 10 10
def table49 : Point → Point := put table48 11 9
def table50 : Point → Point := put table49 1 1
def table51 : Point → Point := put table49 1 4

theorem bound51 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,1,2,3,5,6,7] table51, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,1,2,3,5,6,7] [] table51 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound50 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,2,3,4,5,6,7] table50, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,2,3,4,5,6,7] [] table50 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound49 : ∀ f ∈ assignSearch step finish [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] table49, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] [1,4] table49 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound50
    · exact bound51

theorem bound48 : ∀ f ∈ assignSearch step finish [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9] table48, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9] [9] table48 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound49

theorem bound47 : ∀ f ∈ assignSearch step finish [4,7,0,3,5,6] [0,1,3,5,6,7] table47, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [7,0,3,5,6] [0,1,3,5,6,7] [] table47 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound46 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,1,2,3,5,6,7] table46, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,1,2,3,5,6,7] [2] table46 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound47

theorem bound45 : ∀ f ∈ assignSearch step finish [4,7,0,3,5,6] [0,2,3,4,5,6] table45, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [7,0,3,5,6] [0,2,3,4,5,6] [] table45 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound44 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,2,3,4,5,6,7] table44, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,2,3,4,5,6,7] [7] table44 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound45

theorem bound43 : ∀ f ∈ assignSearch step finish [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] table43, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] [1,4] table43 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound44
    · exact bound46

theorem bound42 : ∀ f ∈ assignSearch step finish [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,10] table42, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,10] [10] table42 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound43

theorem bound41 : ∀ f ∈ assignSearch step finish [10,11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9,10] table41, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9,10] [9,10] table41 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound42
    · exact bound48

theorem bound40 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,1,2,3,5,6,7] table40, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,1,2,3,5,6,7] [] table40 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound39 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,2,3,4,5,6,7] table39, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,2,3,4,5,6,7] [] table39 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound38 : ∀ f ∈ assignSearch step finish [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] table38, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] [1,4] table38 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound39
    · exact bound40

theorem bound37 : ∀ f ∈ assignSearch step finish [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9] table37, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9] [9] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound38

theorem bound36 : ∀ f ∈ assignSearch step finish [4,7,0,3,5,6] [0,1,2,3,5,6] table36, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [7,0,3,5,6] [0,1,2,3,5,6] [] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound35 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,1,2,3,5,6,7] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,1,2,3,5,6,7] [7] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound36

theorem bound34 : ∀ f ∈ assignSearch step finish [4,7,0,3,5,6] [0,3,4,5,6,7] table34, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [7,0,3,5,6] [0,3,4,5,6,7] [] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound33 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,2,3,4,5,6,7] table33, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,2,3,4,5,6,7] [2] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound34

theorem bound32 : ∀ f ∈ assignSearch step finish [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] table32, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] [1,4] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound33
    · exact bound35

theorem bound31 : ∀ f ∈ assignSearch step finish [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,11] table31, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,11] [11] table31 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound32

theorem bound30 : ∀ f ∈ assignSearch step finish [10,11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9,11] table30, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9,11] [9,11] table30 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound31
    · exact bound37

theorem bound29 : ∀ f ∈ assignSearch step finish [0,3,5,6] [0,3,5,6] table29, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [3,5,6] [0,3,5,6] [] table29 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound28 : ∀ f ∈ assignSearch step finish [7,0,3,5,6] [0,3,5,6,7] table28, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,3,5,6] [0,3,5,6,7] [7] table28 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound29

theorem bound27 : ∀ f ∈ assignSearch step finish [4,7,0,3,5,6] [0,1,3,5,6,7] table27, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [7,0,3,5,6] [0,1,3,5,6,7] [1] table27 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound28

theorem bound26 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,1,2,3,5,6,7] table26, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,1,2,3,5,6,7] [2] table26 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound27

theorem bound25 : ∀ f ∈ assignSearch step finish [0,3,5,6] [0,3,5,6] table25, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [3,5,6] [0,3,5,6] [] table25 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound24 : ∀ f ∈ assignSearch step finish [7,0,3,5,6] [0,2,3,5,6] table24, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,3,5,6] [0,2,3,5,6] [2] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound25

theorem bound23 : ∀ f ∈ assignSearch step finish [4,7,0,3,5,6] [0,2,3,4,5,6] table23, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [7,0,3,5,6] [0,2,3,4,5,6] [4] table23 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound24

theorem bound22 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,2,3,4,5,6,7] table22, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,2,3,4,5,6,7] [7] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound23

theorem bound21 : ∀ f ∈ assignSearch step finish [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] table21, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] [1,4] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound22
    · exact bound26

theorem bound20 : ∀ f ∈ assignSearch step finish [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,10] table20, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,10] [10] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound21

theorem bound19 : ∀ f ∈ assignSearch step finish [] [] table19, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound18 : ∀ f ∈ assignSearch step finish [6] [3] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [] [3] [3] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ f ∈ assignSearch step finish [5,6] [0,3] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6] [0,3] [0] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [3,5,6] [0,3,6] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6] [0,3,6] [6] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound17

theorem bound15 : ∀ f ∈ assignSearch step finish [0,3,5,6] [0,3,5,6] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [3,5,6] [0,3,5,6] [5] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ f ∈ assignSearch step finish [7,0,3,5,6] [0,2,3,5,6] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,3,5,6] [0,2,3,5,6] [2] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound15

theorem bound13 : ∀ f ∈ assignSearch step finish [4,7,0,3,5,6] [0,1,2,3,5,6] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [7,0,3,5,6] [0,1,2,3,5,6] [1] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,1,2,3,5,6,7] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,1,2,3,5,6,7] [7] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound13

theorem bound11 : ∀ f ∈ assignSearch step finish [] [] table11, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound10 : ∀ f ∈ assignSearch step finish [6] [6] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [] [6] [6] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound11

theorem bound9 : ∀ f ∈ assignSearch step finish [5,6] [5,6] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6] [5,6] [5] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [3,5,6] [3,5,6] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6] [3,5,6] [3] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound9

theorem bound7 : ∀ f ∈ assignSearch step finish [0,3,5,6] [0,3,5,6] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [3,5,6] [0,3,5,6] [0] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [7,0,3,5,6] [0,3,5,6,7] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,3,5,6] [0,3,5,6,7] [7] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [4,7,0,3,5,6] [0,3,4,5,6,7] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [7,0,3,5,6] [0,3,4,5,6,7] [4] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [2,4,7,0,3,5,6] [0,2,3,4,5,6,7] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [4,7,0,3,5,6] [0,2,3,4,5,6,7] [2] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7] [1,4] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound4
    · exact bound12

theorem bound2 : ∀ f ∈ assignSearch step finish [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,11] [11] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound3

theorem bound1 : ∀ f ∈ assignSearch step finish [10,11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,10,11] [10,11] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound2
    · exact bound20

theorem bound0 : ∀ f ∈ assignSearch step finish [9,10,11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11,1,2,4,7,0,3,5,6] [0,1,2,3,4,5,6,7,9,10,11] [9,10,11] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound1
    · exact bound30
    · exact bound41

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link65 8) = link link65 8) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link65 link65 hole 8 8 [9,10,11,1,2,4,7,0,3,5,6]
    (by decide +kernel) (by decide +kernel) Data60.matrix Data60.matrix
    Data60.matrix_checked Data60.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link65 link65 hole 8 hole 8 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link65 link65 hole 8 hole 8 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair60_60
