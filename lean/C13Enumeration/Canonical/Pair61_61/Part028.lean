import C13Enumeration.Canonical.Pair61_61.Data
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound911 : ∀ f ∈ assignSearch step finish [] [] table911, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound910 : ∀ f ∈ assignSearch step finish [11] [9] table910, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table910 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound911

theorem bound909 : ∀ f ∈ assignSearch step finish [10,11] [1,9] table909, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,9] [1] table909 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound910

theorem bound908 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,9] table908, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,9] [2] table908 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound909

theorem bound907 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,3,9] table907, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,3,9] [3] table907 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound908

theorem bound906 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,8,9] table906, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,8,9] [8] table906 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound907

theorem bound905 : ∀ f ∈ assignSearch step finish [] [] table905, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound904 : ∀ f ∈ assignSearch step finish [11] [3] table904, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table904 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound905

theorem bound903 : ∀ f ∈ assignSearch step finish [10,11] [3,8] table903, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,8] [8] table903 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound904

theorem bound902 : ∀ f ∈ assignSearch step finish [9,10,11] [3,7,8] table902, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,7,8] [7] table902 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound903

theorem bound901 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,7,8,9] table901, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,7,8,9] [9] table901 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound902

theorem bound900 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,3,7,8,9] table900, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,3,7,8,9] [1] table900 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound901

theorem bound899 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,7,8,9] table899, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,7,8,9] [2,7] table899 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound900
    · exact bound906

theorem bound898 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,7,8,9] table898, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,7,8,9] [6] table898 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound899

theorem bound897 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,9] table897, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,6,7,8,9] [0] table897 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound898

theorem bound896 : ∀ f ∈ assignSearch step finish [] [] table896, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Canonical.Pair61_61
