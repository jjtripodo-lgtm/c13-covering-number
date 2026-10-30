import C13Enumeration.Canonical.Pair61_61.Part018
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound575 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,7] table575, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,7] [2] table575 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound576

theorem bound574 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,7,11] table574, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,7,11] [11] table574 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound575

theorem bound573 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,7,11] table573, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,7,11] [3] table573 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound574

theorem bound572 : ∀ f ∈ assignSearch step finish [] [] table572, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound571 : ∀ f ∈ assignSearch step finish [11] [11] table571, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table571 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound572

theorem bound570 : ∀ f ∈ assignSearch step finish [10,11] [3,11] table570, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,11] [3] table570 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound571

theorem bound569 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,11] table569, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,11] [9] table569 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound570

theorem bound568 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,3,9,11] table568, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,3,9,11] [0] table568 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound569

theorem bound567 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,3,7,9,11] table567, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,3,7,9,11] [7] table567 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound568

theorem bound566 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,7,9,11] table566, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,7,9,11] [2,9] table566 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound567
    · exact bound573

theorem bound565 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,7,9,10,11] table565, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,7,9,10,11] [10] table565 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound566

theorem bound564 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,2,3,6,7,9,10,11] table564, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,2,3,6,7,9,10,11] [6] table564 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound565

theorem bound563 : ∀ f ∈ assignSearch step finish [] [] table563, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound562 : ∀ f ∈ assignSearch step finish [11] [1] table562, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table562 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound563

theorem bound561 : ∀ f ∈ assignSearch step finish [10,11] [1,6] table561, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,6] [6] table561 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound562

theorem bound560 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,6] table560, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,6] [2] table560 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound561

theorem bound559 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,6,11] table559, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,6,11] [11] table559 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound560

theorem bound558 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,6,11] table558, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,6,11] [3] table558 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound559

theorem bound557 : ∀ f ∈ assignSearch step finish [] [] table557, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound556 : ∀ f ∈ assignSearch step finish [11] [11] table556, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table556 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound557

theorem bound555 : ∀ f ∈ assignSearch step finish [10,11] [3,11] table555, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,11] [3] table555 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound556

theorem bound554 : ∀ f ∈ assignSearch step finish [9,10,11] [3,10,11] table554, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,10,11] [10] table554 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound555

theorem bound553 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,3,10,11] table553, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,3,10,11] [1] table553 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound554

theorem bound552 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,3,6,10,11] table552, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,3,6,10,11] [6] table552 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound553

theorem bound551 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,6,10,11] table551, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,6,10,11] [2,10] table551 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound552
    · exact bound558

theorem bound550 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,9,10,11] table550, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,9,10,11] [9] table550 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound551

theorem bound549 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [1,2,3,6,7,9,10,11] table549, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [1,2,3,6,7,9,10,11] [7] table549 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound550

theorem bound548 : ∀ f ∈ assignSearch step finish [1,2,3,6,7,8,9,10,11] [0,1,2,3,6,7,9,10,11] table548, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,9,10,11] [0,1,3,6,7,11] table548 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound549
    · exact bound564
    · exact bound579
    · exact bound594
    · exact bound609
    · exact bound624

theorem bound547 : ∀ f ∈ assignSearch step finish [] [] table547, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound546 : ∀ f ∈ assignSearch step finish [11] [2] table546, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table546 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound547

theorem bound545 : ∀ f ∈ assignSearch step finish [10,11] [2,6] table545, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,6] [6] table545 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound546

theorem bound544 : ∀ f ∈ assignSearch step finish [9,10,11] [2,6,9] table544, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,6,9] [9] table544 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound545
end C13.Enumeration.Canonical.Pair61_61
