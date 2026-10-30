import C13Enumeration.Canonical.Pair51_51.Part004
namespace C13.Enumeration.Canonical.Pair51_51
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound127 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table127, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [9] table127 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound128

theorem bound126 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table126, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [10] table126 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound127

theorem bound125 : ∀ f ∈ assignSearch step finish [7,9,10,11] [7,9,10,11] table125, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [7,9,10,11] [7] table125 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound126

theorem bound124 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,7,9,10,11] table124, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,7,9,10,11] [5] table124 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound125

theorem bound123 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [5,6,7,9,10,11] table123, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [5,6,7,9,10,11] [6,10] table123 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound124
    · exact bound130

theorem bound122 : ∀ f ∈ assignSearch step finish [3,5,6,7,9,10,11] [3,5,6,7,9,10,11] table122, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,9,10,11] [3,5,6,7,9,10,11] [3] table122 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound123

theorem bound121 : ∀ f ∈ assignSearch step finish [2,3,5,6,7,9,10,11] [1,3,5,6,7,9,10,11] table121, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,6,7,9,10,11] [1,3,5,6,7,9,10,11] [1,3] table121 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound122
    · exact bound136

theorem bound120 : ∀ f ∈ assignSearch step finish [] [] table120, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound119 : ∀ f ∈ assignSearch step finish [11] [6] table119, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table119 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound120

theorem bound118 : ∀ f ∈ assignSearch step finish [10,11] [6,7] table118, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,7] [7] table118 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound119

theorem bound117 : ∀ f ∈ assignSearch step finish [9,10,11] [5,6,7] table117, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [5,6,7] [5] table117 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound118

theorem bound116 : ∀ f ∈ assignSearch step finish [7,9,10,11] [5,6,7,10] table116, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [5,6,7,10] [10] table116 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound117

theorem bound115 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,6,7,10,11] table115, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,6,7,10,11] [11] table115 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound116

theorem bound114 : ∀ f ∈ assignSearch step finish [] [] table114, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound113 : ∀ f ∈ assignSearch step finish [11] [10] table113, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table113 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound114

theorem bound112 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table112, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table112 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound113

theorem bound111 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table111, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table111 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound112

theorem bound110 : ∀ f ∈ assignSearch step finish [7,9,10,11] [6,9,10,11] table110, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [6,9,10,11] [6] table110 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound111

theorem bound109 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [6,7,9,10,11] table109, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [6,7,9,10,11] [7] table109 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound110

theorem bound108 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [5,6,7,9,10,11] table108, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [5,6,7,9,10,11] [5,9] table108 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound109
    · exact bound115

theorem bound107 : ∀ f ∈ assignSearch step finish [3,5,6,7,9,10,11] [2,5,6,7,9,10,11] table107, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,9,10,11] [2,5,6,7,9,10,11] [2] table107 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound108

theorem bound106 : ∀ f ∈ assignSearch step finish [] [] table106, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound105 : ∀ f ∈ assignSearch step finish [11] [7] table105, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table105 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound106

theorem bound104 : ∀ f ∈ assignSearch step finish [10,11] [6,7] table104, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,7] [6] table104 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound105

theorem bound103 : ∀ f ∈ assignSearch step finish [9,10,11] [5,6,7] table103, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [5,6,7] [5] table103 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound104

theorem bound102 : ∀ f ∈ assignSearch step finish [7,9,10,11] [5,6,7,11] table102, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [5,6,7,11] [11] table102 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound103

theorem bound101 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,6,7,10,11] table101, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,6,7,10,11] [10] table101 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound102

theorem bound100 : ∀ f ∈ assignSearch step finish [] [] table100, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound99 : ∀ f ∈ assignSearch step finish [11] [11] table99, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table99 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound100

theorem bound98 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table98, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table98 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound99

theorem bound97 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table97, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table97 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound98

theorem bound96 : ∀ f ∈ assignSearch step finish [7,9,10,11] [7,9,10,11] table96, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [7,9,10,11] [7] table96 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound97
end C13.Enumeration.Canonical.Pair51_51
