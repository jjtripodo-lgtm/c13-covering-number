import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair18_18
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := [![0,1,12,3,4,5,6,7,8,9,10,11,2],![0,1,12,3,4,5,8,7,6,9,10,11,2],![1,0,12,3,5,4,6,7,8,9,11,10,2],![1,0,12,3,5,4,8,7,6,9,11,10,2]]
def step := starStep (link link10 2) (link link10 2) Data18.matrix Data18.matrix
def finish := crossMapFinish link10 link10 hole 2 2
def table0 : Point → Point := anchorTable hole hole 2
def table1 : Point → Point := put table0 4 4
def table2 : Point → Point := put table1 5 5
def table3 : Point → Point := put table2 6 6
def table4 : Point → Point := put table3 7 7
def table5 : Point → Point := put table4 8 8
def table6 : Point → Point := put table5 0 0
def table7 : Point → Point := put table6 1 1
def table8 : Point → Point := put table7 3 3
def table9 : Point → Point := put table8 9 9
def table10 : Point → Point := put table9 10 10
def table11 : Point → Point := put table10 11 11
def table12 : Point → Point := put table2 6 7
def table13 : Point → Point := put table12 7 6
def table14 : Point → Point := put table12 7 8
def table15 : Point → Point := put table2 6 8
def table16 : Point → Point := put table15 7 7
def table17 : Point → Point := put table16 8 6
def table18 : Point → Point := put table17 0 0
def table19 : Point → Point := put table18 1 1
def table20 : Point → Point := put table19 3 3
def table21 : Point → Point := put table20 9 9
def table22 : Point → Point := put table21 10 10
def table23 : Point → Point := put table22 11 11
def table24 : Point → Point := put table0 4 5
def table25 : Point → Point := put table24 5 4
def table26 : Point → Point := put table25 6 6
def table27 : Point → Point := put table26 7 7
def table28 : Point → Point := put table27 8 8
def table29 : Point → Point := put table28 0 1
def table30 : Point → Point := put table29 1 0
def table31 : Point → Point := put table30 3 3
def table32 : Point → Point := put table31 9 9
def table33 : Point → Point := put table32 10 11
def table34 : Point → Point := put table33 11 10
def table35 : Point → Point := put table25 6 7
def table36 : Point → Point := put table35 7 6
def table37 : Point → Point := put table35 7 8
def table38 : Point → Point := put table25 6 8
def table39 : Point → Point := put table38 7 7
def table40 : Point → Point := put table39 8 6
def table41 : Point → Point := put table40 0 1
def table42 : Point → Point := put table41 1 0
def table43 : Point → Point := put table42 3 3
def table44 : Point → Point := put table43 9 9
def table45 : Point → Point := put table44 10 11
def table46 : Point → Point := put table45 11 10

theorem bound46 : ∀ f ∈ assignSearch step finish [] [] table46, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound45 : ∀ f ∈ assignSearch step finish [11] [10] table45, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table45 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound46

theorem bound44 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table44, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table44 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound45

theorem bound43 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table43, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table43 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound44

theorem bound42 : ∀ f ∈ assignSearch step finish [3,9,10,11] [3,9,10,11] table42, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [3,9,10,11] [3] table42 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound43

theorem bound41 : ∀ f ∈ assignSearch step finish [1,3,9,10,11] [0,3,9,10,11] table41, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,9,10,11] [0,3,9,10,11] [0] table41 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound42

theorem bound40 : ∀ f ∈ assignSearch step finish [0,1,3,9,10,11] [0,1,3,9,10,11] table40, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,3,9,10,11] [0,1,3,9,10,11] [1] table40 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound41

theorem bound39 : ∀ f ∈ assignSearch step finish [8,0,1,3,9,10,11] [0,1,3,6,9,10,11] table39, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [0,1,3,9,10,11] [0,1,3,6,9,10,11] [6] table39 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound40

theorem bound38 : ∀ f ∈ assignSearch step finish [7,8,0,1,3,9,10,11] [0,1,3,6,7,9,10,11] table38, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,0,1,3,9,10,11] [0,1,3,6,7,9,10,11] [7] table38 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound39

theorem bound37 : ∀ f ∈ assignSearch step finish [8,0,1,3,9,10,11] [0,1,3,6,9,10,11] table37, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [0,1,3,9,10,11] [0,1,3,6,9,10,11] [] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound36 : ∀ f ∈ assignSearch step finish [8,0,1,3,9,10,11] [0,1,3,8,9,10,11] table36, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [0,1,3,9,10,11] [0,1,3,8,9,10,11] [] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound35 : ∀ f ∈ assignSearch step finish [7,8,0,1,3,9,10,11] [0,1,3,6,8,9,10,11] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,0,1,3,9,10,11] [0,1,3,6,8,9,10,11] [6,8] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound36
    · exact bound37

theorem bound34 : ∀ f ∈ assignSearch step finish [] [] table34, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound33 : ∀ f ∈ assignSearch step finish [11] [10] table33, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound34

theorem bound32 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table32, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound33

theorem bound31 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table31, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table31 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound32

theorem bound30 : ∀ f ∈ assignSearch step finish [3,9,10,11] [3,9,10,11] table30, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [3,9,10,11] [3] table30 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound31

theorem bound29 : ∀ f ∈ assignSearch step finish [1,3,9,10,11] [0,3,9,10,11] table29, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,9,10,11] [0,3,9,10,11] [0] table29 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound30

theorem bound28 : ∀ f ∈ assignSearch step finish [0,1,3,9,10,11] [0,1,3,9,10,11] table28, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,3,9,10,11] [0,1,3,9,10,11] [1] table28 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound29

theorem bound27 : ∀ f ∈ assignSearch step finish [8,0,1,3,9,10,11] [0,1,3,8,9,10,11] table27, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [0,1,3,9,10,11] [0,1,3,8,9,10,11] [8] table27 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound28

theorem bound26 : ∀ f ∈ assignSearch step finish [7,8,0,1,3,9,10,11] [0,1,3,7,8,9,10,11] table26, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,0,1,3,9,10,11] [0,1,3,7,8,9,10,11] [7] table26 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound27

theorem bound25 : ∀ f ∈ assignSearch step finish [6,7,8,0,1,3,9,10,11] [0,1,3,6,7,8,9,10,11] table25, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,0,1,3,9,10,11] [0,1,3,6,7,8,9,10,11] [6,7,8] table25 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound26
    · exact bound35
    · exact bound38

theorem bound24 : ∀ f ∈ assignSearch step finish [5,6,7,8,0,1,3,9,10,11] [0,1,3,4,6,7,8,9,10,11] table24, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,0,1,3,9,10,11] [0,1,3,4,6,7,8,9,10,11] [4] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound25

theorem bound23 : ∀ f ∈ assignSearch step finish [] [] table23, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound22 : ∀ f ∈ assignSearch step finish [11] [11] table22, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound23

theorem bound21 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table21, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound22

theorem bound20 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table20, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound21

theorem bound19 : ∀ f ∈ assignSearch step finish [3,9,10,11] [3,9,10,11] table19, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [3,9,10,11] [3] table19 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound20

theorem bound18 : ∀ f ∈ assignSearch step finish [1,3,9,10,11] [1,3,9,10,11] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,9,10,11] [1,3,9,10,11] [1] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ f ∈ assignSearch step finish [0,1,3,9,10,11] [0,1,3,9,10,11] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,3,9,10,11] [0,1,3,9,10,11] [0] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [8,0,1,3,9,10,11] [0,1,3,6,9,10,11] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [0,1,3,9,10,11] [0,1,3,6,9,10,11] [6] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound17

theorem bound15 : ∀ f ∈ assignSearch step finish [7,8,0,1,3,9,10,11] [0,1,3,6,7,9,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,0,1,3,9,10,11] [0,1,3,6,7,9,10,11] [7] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ f ∈ assignSearch step finish [8,0,1,3,9,10,11] [0,1,3,6,9,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [0,1,3,9,10,11] [0,1,3,6,9,10,11] [] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound13 : ∀ f ∈ assignSearch step finish [8,0,1,3,9,10,11] [0,1,3,8,9,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [0,1,3,9,10,11] [0,1,3,8,9,10,11] [] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound12 : ∀ f ∈ assignSearch step finish [7,8,0,1,3,9,10,11] [0,1,3,6,8,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,0,1,3,9,10,11] [0,1,3,6,8,9,10,11] [6,8] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound13
    · exact bound14

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

theorem bound7 : ∀ f ∈ assignSearch step finish [3,9,10,11] [3,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [3,9,10,11] [3] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [1,3,9,10,11] [1,3,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [3,9,10,11] [1,3,9,10,11] [1] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [0,1,3,9,10,11] [0,1,3,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,3,9,10,11] [0,1,3,9,10,11] [0] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [8,0,1,3,9,10,11] [0,1,3,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [0,1,3,9,10,11] [0,1,3,8,9,10,11] [8] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [7,8,0,1,3,9,10,11] [0,1,3,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,0,1,3,9,10,11] [0,1,3,7,8,9,10,11] [7] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ f ∈ assignSearch step finish [6,7,8,0,1,3,9,10,11] [0,1,3,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,0,1,3,9,10,11] [0,1,3,6,7,8,9,10,11] [6,7,8] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound3
    · exact bound12
    · exact bound15

theorem bound1 : ∀ f ∈ assignSearch step finish [5,6,7,8,0,1,3,9,10,11] [0,1,3,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,0,1,3,9,10,11] [0,1,3,5,6,7,8,9,10,11] [5] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [4,5,6,7,8,0,1,3,9,10,11] [0,1,3,4,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,8,0,1,3,9,10,11] [0,1,3,4,5,6,7,8,9,10,11] [4,5] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound24

theorem complete (e : Equiv.Perm Point) (he : e hole = 2) (hc : e (2 : Point) = hole)
    (hs : transport e (link link10 2) = link link10 2) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link10 link10 hole 2 2 [4,5,6,7,8,0,1,3,9,10,11]
    (by decide +kernel) (by decide +kernel) Data18.matrix Data18.matrix
    Data18.matrix_checked Data18.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link10 link10 hole 2 hole 2 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link10 link10 hole 2 hole 2 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair18_18
