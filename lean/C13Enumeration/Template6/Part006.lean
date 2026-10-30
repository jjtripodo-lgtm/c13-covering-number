import C13Enumeration.Template6.Part007
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound111 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,4,5,7,8,9] table111, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,4,5,7,8,9] [7] table111 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound112

theorem bound110 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,3,4,5,7,8,9] table110, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,3,4,5,7,8,9] [3,9] table110 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound111
    · exact bound118

theorem bound109 : ∀ f ∈ assignSearch step finish [] [] table109, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound108 : ∀ f ∈ assignSearch step finish [11] [8] table108, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table108 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound109

theorem bound107 : ∀ f ∈ assignSearch step finish [9,11] [1,8] table107, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,8] [1] table107 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound108

theorem bound106 : ∀ f ∈ assignSearch step finish [8,9,11] [1,3,8] table106, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,3,8] [3] table106 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound107

theorem bound105 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,3,4,8] table105, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,3,4,8] [4] table105 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound106

theorem bound104 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,3,4,7,8] table104, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,3,4,7,8] [7] table104 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound105

theorem bound103 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,3,4,5,7,8] table103, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,3,4,5,7,8] [5] table103 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound104

theorem bound102 : ∀ f ∈ assignSearch step finish [] [] table102, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound101 : ∀ f ∈ assignSearch step finish [11] [8] table101, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table101 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound102

theorem bound100 : ∀ f ∈ assignSearch step finish [9,11] [8,11] table100, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,11] [11] table100 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound101

theorem bound99 : ∀ f ∈ assignSearch step finish [8,9,11] [3,8,11] table99, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [3,8,11] [3] table99 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound100

theorem bound98 : ∀ f ∈ assignSearch step finish [7,8,9,11] [3,4,8,11] table98, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [3,4,8,11] [4] table98 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound99

theorem bound97 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [3,4,7,8,11] table97, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [3,4,7,8,11] [7] table97 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound98

theorem bound96 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [3,4,5,7,8,11] table96, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [3,4,5,7,8,11] [5] table96 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound97
end C13.Enumeration.Template6
