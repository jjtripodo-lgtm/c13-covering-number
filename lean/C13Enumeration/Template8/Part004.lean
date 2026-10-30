import C13Enumeration.Template8.Part005
namespace C13.Enumeration.Template8
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound79 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table79, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table79 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound80

theorem bound78 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table78, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table78 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound79

theorem bound77 : ∀ f ∈ assignSearch step finish [7,9,10,11] [7,9,10,11] table77, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [7,9,10,11] [7] table77 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound78

theorem bound76 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [6,7,9,10,11] table76, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [6,7,9,10,11] [6] table76 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound77

theorem bound75 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [4,6,7,9,10,11] table75, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [4,6,7,9,10,11] [4] table75 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound76

theorem bound74 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [4,5,6,7,9,10,11] table74, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [4,5,6,7,9,10,11] [5] table74 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound75

theorem bound73 : ∀ f ∈ assignSearch step finish [3,4,5,6,7,9,10,11] [3,4,5,6,7,9,10,11] table73, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,6,7,9,10,11] [3,4,5,6,7,9,10,11] [3,7] table73 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound74
    · exact bound82

theorem bound72 : ∀ f ∈ assignSearch step finish [2,3,4,5,6,7,9,10,11] [2,3,4,5,6,7,9,10,11] table72, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,6,7,9,10,11] [2,3,4,5,6,7,9,10,11] [2,3,6,7] table72 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound73
    · exact bound90
    · exact bound107
    · exact bound124

theorem bound71 : ∀ f ∈ assignSearch step finish [1,2,3,4,5,6,7,9,10,11] [0,2,3,4,5,6,7,9,10,11] table71, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,4,5,6,7,9,10,11] [0,2,3,4,5,6,7,9,10,11] [0] table71 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound72

theorem bound70 : ∀ f ∈ assignSearch step finish [] [] table70, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound69 : ∀ f ∈ assignSearch step finish [11] [10] table69, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table69 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound70

theorem bound68 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table68, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table68 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound69

theorem bound67 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table67, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table67 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound68

theorem bound66 : ∀ f ∈ assignSearch step finish [7,9,10,11] [2,9,10,11] table66, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [2,9,10,11] [2] table66 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound67

theorem bound65 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [2,3,9,10,11] table65, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [2,3,9,10,11] [3] table65 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound66

theorem bound64 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [2,3,5,9,10,11] table64, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [2,3,5,9,10,11] [5] table64 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound65
end C13.Enumeration.Template8
