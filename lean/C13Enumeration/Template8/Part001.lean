import C13Enumeration.Template8.Part002
namespace C13.Enumeration.Template8
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound31 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [2,7,9,10,11] table31, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [2,7,9,10,11] [7] table31 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound32

theorem bound30 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [2,5,7,9,10,11] table30, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [2,5,7,9,10,11] [5] table30 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound31

theorem bound29 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [2,4,5,7,9,10,11] table29, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [2,4,5,7,9,10,11] [4] table29 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound30

theorem bound28 : ∀ f ∈ assignSearch step finish [] [] table28, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound27 : ∀ f ∈ assignSearch step finish [11] [10] table27, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table27 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound28

theorem bound26 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table26, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table26 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound27

theorem bound25 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table25, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table25 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound26

theorem bound24 : ∀ f ∈ assignSearch step finish [7,9,10,11] [6,9,10,11] table24, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [6,9,10,11] [6] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound25

theorem bound23 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [6,7,9,10,11] table23, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [6,7,9,10,11] [7] table23 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound24

theorem bound22 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [5,6,7,9,10,11] table22, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [5,6,7,9,10,11] [5] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound23

theorem bound21 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [4,5,6,7,9,10,11] table21, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [4,5,6,7,9,10,11] [4] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound22

theorem bound20 : ∀ f ∈ assignSearch step finish [3,4,5,6,7,9,10,11] [2,4,5,6,7,9,10,11] table20, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,6,7,9,10,11] [2,4,5,6,7,9,10,11] [2,6] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound21
    · exact bound29

theorem bound19 : ∀ f ∈ assignSearch step finish [] [] table19, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound18 : ∀ f ∈ assignSearch step finish [11] [11] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound17
end C13.Enumeration.Template8
