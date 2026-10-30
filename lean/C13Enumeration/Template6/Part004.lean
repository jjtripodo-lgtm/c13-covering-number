import C13Enumeration.Template6.Part005
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound79 : ∀ f ∈ assignSearch step finish [] [] table79, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound78 : ∀ f ∈ assignSearch step finish [11] [8] table78, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table78 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound79

theorem bound77 : ∀ f ∈ assignSearch step finish [9,11] [3,8] table77, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [3,8] [3] table77 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound78

theorem bound76 : ∀ f ∈ assignSearch step finish [8,9,11] [3,8,11] table76, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [3,8,11] [11] table76 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound77

theorem bound75 : ∀ f ∈ assignSearch step finish [7,8,9,11] [3,4,8,11] table75, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [3,4,8,11] [4] table75 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound76

theorem bound74 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [3,4,5,8,11] table74, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [3,4,5,8,11] [5] table74 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound75

theorem bound73 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [3,4,5,7,8,11] table73, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [3,4,5,7,8,11] [7] table73 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound74

theorem bound72 : ∀ f ∈ assignSearch step finish [] [] table72, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound71 : ∀ f ∈ assignSearch step finish [11] [8] table71, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table71 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound72

theorem bound70 : ∀ f ∈ assignSearch step finish [9,11] [8,9] table70, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,9] [9] table70 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound71

theorem bound69 : ∀ f ∈ assignSearch step finish [8,9,11] [8,9,11] table69, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [8,9,11] [11] table69 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound70

theorem bound68 : ∀ f ∈ assignSearch step finish [7,8,9,11] [4,8,9,11] table68, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [4,8,9,11] [4] table68 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound69

theorem bound67 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [4,5,8,9,11] table67, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [4,5,8,9,11] [5] table67 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound68

theorem bound66 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [4,5,7,8,9,11] table66, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [4,5,7,8,9,11] [7] table66 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound67

theorem bound65 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [3,4,5,7,8,9,11] table65, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [3,4,5,7,8,9,11] [3,9] table65 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound66
    · exact bound73

theorem bound64 : ∀ f ∈ assignSearch step finish [2,3,4,5,7,8,9,11] [1,3,4,5,7,8,9,11] table64, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,7,8,9,11] [1,3,4,5,7,8,9,11] [1,3,9,11] table64 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound65
    · exact bound80
    · exact bound95
    · exact bound110
end C13.Enumeration.Template6
