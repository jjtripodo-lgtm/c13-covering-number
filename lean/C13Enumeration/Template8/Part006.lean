import C13Enumeration.Template8.Part007
namespace C13.Enumeration.Template8
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound111 : ∀ f ∈ assignSearch step finish [7,9,10,11] [7,9,10,11] table111, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [7,9,10,11] [7] table111 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound112

theorem bound110 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [2,7,9,10,11] table110, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [2,7,9,10,11] [2] table110 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound111

theorem bound109 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [2,4,7,9,10,11] table109, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [2,4,7,9,10,11] [4] table109 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound110

theorem bound108 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [2,4,5,7,9,10,11] table108, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [2,4,5,7,9,10,11] [5] table108 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound109

theorem bound107 : ∀ f ∈ assignSearch step finish [3,4,5,6,7,9,10,11] [2,3,4,5,7,9,10,11] table107, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,6,7,9,10,11] [2,3,4,5,7,9,10,11] [3,7] table107 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound108
    · exact bound116

theorem bound106 : ∀ f ∈ assignSearch step finish [] [] table106, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound105 : ∀ f ∈ assignSearch step finish [11] [11] table105, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table105 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound106

theorem bound104 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table104, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table104 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound105

theorem bound103 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table103, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table103 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound104

theorem bound102 : ∀ f ∈ assignSearch step finish [7,9,10,11] [2,9,10,11] table102, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [2,9,10,11] [2] table102 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound103

theorem bound101 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [2,7,9,10,11] table101, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [2,7,9,10,11] [7] table101 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound102

theorem bound100 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [2,4,7,9,10,11] table100, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [2,4,7,9,10,11] [4] table100 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound101

theorem bound99 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [2,4,5,7,9,10,11] table99, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [2,4,5,7,9,10,11] [5] table99 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound100

theorem bound98 : ∀ f ∈ assignSearch step finish [] [] table98, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound97 : ∀ f ∈ assignSearch step finish [11] [11] table97, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table97 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound98

theorem bound96 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table96, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table96 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound97
end C13.Enumeration.Template8
