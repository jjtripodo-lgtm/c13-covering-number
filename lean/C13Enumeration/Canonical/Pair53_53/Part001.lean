import C13Enumeration.Canonical.Pair53_53.Part002
namespace C13.Enumeration.Canonical.Pair53_53
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound63 : ∀ f ∈ assignSearch step finish [6,7] [2,3] table63, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7] [2,3] [3] table63 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound64

theorem bound62 : ∀ f ∈ assignSearch step finish [3,6,7] [2,3,6] table62, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7] [2,3,6] [6] table62 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound63

theorem bound61 : ∀ f ∈ assignSearch step finish [2,3,6,7] [2,3,6,7] table61, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7] [2,3,6,7] [7] table61 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound62

theorem bound60 : ∀ f ∈ assignSearch step finish [5,2,3,6,7] [1,2,3,6,7] table60, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [2,3,6,7] [1,2,3,6,7] [1] table60 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound61

theorem bound59 : ∀ f ∈ assignSearch step finish [4,5,2,3,6,7] [0,1,2,3,6,7] table59, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,2,3,6,7] [0,1,2,3,6,7] [0] table59 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound60

theorem bound58 : ∀ f ∈ assignSearch step finish [] [] table58, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound57 : ∀ f ∈ assignSearch step finish [7] [6] table57, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [] [6] [6] table57 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound58

theorem bound56 : ∀ f ∈ assignSearch step finish [6,7] [6,7] table56, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7] [6,7] [7] table56 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound57

theorem bound55 : ∀ f ∈ assignSearch step finish [3,6,7] [2,6,7] table55, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7] [2,6,7] [2] table55 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound56

theorem bound54 : ∀ f ∈ assignSearch step finish [2,3,6,7] [2,3,6,7] table54, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7] [2,3,6,7] [3] table54 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound55

theorem bound53 : ∀ f ∈ assignSearch step finish [5,2,3,6,7] [2,3,5,6,7] table53, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [2,3,6,7] [2,3,5,6,7] [5] table53 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound54

theorem bound52 : ∀ f ∈ assignSearch step finish [4,5,2,3,6,7] [0,2,3,5,6,7] table52, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,2,3,6,7] [0,2,3,5,6,7] [0] table52 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound53

theorem bound51 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [0,1,2,3,5,6,7] table51, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [0,1,2,3,5,6,7] [1,5] table51 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound52
    · exact bound59

theorem bound50 : ∀ f ∈ assignSearch step finish [] [] table50, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound49 : ∀ f ∈ assignSearch step finish [7] [2] table49, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [] [2] [2] table49 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound50

theorem bound48 : ∀ f ∈ assignSearch step finish [6,7] [2,3] table48, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7] [2,3] [3] table48 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound49

theorem bound47 : ∀ f ∈ assignSearch step finish [3,6,7] [2,3,6] table47, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7] [2,3,6] [6] table47 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound48

theorem bound46 : ∀ f ∈ assignSearch step finish [2,3,6,7] [2,3,6,7] table46, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7] [2,3,6,7] [7] table46 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound47

theorem bound45 : ∀ f ∈ assignSearch step finish [5,2,3,6,7] [1,2,3,6,7] table45, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [2,3,6,7] [1,2,3,6,7] [1] table45 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound46

theorem bound44 : ∀ f ∈ assignSearch step finish [4,5,2,3,6,7] [1,2,3,4,6,7] table44, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,2,3,6,7] [1,2,3,4,6,7] [4] table44 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound45

theorem bound43 : ∀ f ∈ assignSearch step finish [] [] table43, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound42 : ∀ f ∈ assignSearch step finish [7] [6] table42, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [] [6] [6] table42 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound43

theorem bound41 : ∀ f ∈ assignSearch step finish [6,7] [6,7] table41, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7] [6,7] [7] table41 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound42

theorem bound40 : ∀ f ∈ assignSearch step finish [3,6,7] [2,6,7] table40, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7] [2,6,7] [2] table40 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound41

theorem bound39 : ∀ f ∈ assignSearch step finish [2,3,6,7] [2,3,6,7] table39, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7] [2,3,6,7] [3] table39 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound40

theorem bound38 : ∀ f ∈ assignSearch step finish [5,2,3,6,7] [2,3,5,6,7] table38, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [2,3,6,7] [2,3,5,6,7] [5] table38 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound39

theorem bound37 : ∀ f ∈ assignSearch step finish [4,5,2,3,6,7] [2,3,4,5,6,7] table37, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,2,3,6,7] [2,3,4,5,6,7] [4] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound38

theorem bound36 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [1,2,3,4,5,6,7] table36, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [1,2,3,4,5,6,7] [1,5] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound37
    · exact bound44

theorem bound35 : ∀ f ∈ assignSearch step finish [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] [0,4] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound36
    · exact bound51

theorem bound34 : ∀ f ∈ assignSearch step finish [11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,10] table34, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,10] [10] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound35

theorem bound33 : ∀ f ∈ assignSearch step finish [] [] table33, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound32 : ∀ f ∈ assignSearch step finish [7] [3] table32, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [] [3] [3] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound33
end C13.Enumeration.Canonical.Pair53_53
