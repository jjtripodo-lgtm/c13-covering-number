import C13Enumeration.Canonical.Pair61_61.Part023
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound735 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,3,7,8] table735, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,3,7,8] [2] table735 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound736

theorem bound734 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,3,7,8,9] table734, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,3,7,8,9] [9] table734 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound735

theorem bound733 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,7,8,9] table733, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,7,8,9] [1,8] table733 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound734
    · exact bound740

theorem bound732 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,7,8,9] table732, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,7,8,9] [6] table732 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound733

theorem bound731 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [1,2,3,6,7,8,9,11] table731, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [1,2,3,6,7,8,9,11] [11] table731 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound732

theorem bound730 : ∀ f ∈ assignSearch step finish [1,2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,9,11] table730, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,9,11] [0,2,3,7,9,11] table730 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound731
    · exact bound746
    · exact bound761
    · exact bound776
    · exact bound791
    · exact bound806

theorem bound729 : ∀ f ∈ assignSearch step finish [] [] table729, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound728 : ∀ f ∈ assignSearch step finish [11] [10] table728, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table728 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound729

theorem bound727 : ∀ f ∈ assignSearch step finish [10,11] [2,10] table727, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,10] [2] table727 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound728

theorem bound726 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,10] table726, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,10] [0] table726 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound727

theorem bound725 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,3,10] table725, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,3,10] [3] table725 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound726

theorem bound724 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,6,10] table724, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,6,10] [6] table724 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound725

theorem bound723 : ∀ f ∈ assignSearch step finish [] [] table723, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound722 : ∀ f ∈ assignSearch step finish [11] [3] table722, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table722 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound723

theorem bound721 : ∀ f ∈ assignSearch step finish [10,11] [3,6] table721, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,6] [6] table721 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound722

theorem bound720 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,8] table720, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,8] [8] table720 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound721

theorem bound719 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,6,8,10] table719, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,6,8,10] [10] table719 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound720

theorem bound718 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,3,6,8,10] table718, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,3,6,8,10] [2] table718 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound719

theorem bound717 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,6,8,10] table717, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,6,8,10] [0,8] table717 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound718
    · exact bound724

theorem bound716 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,6,7,8,10] table716, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,6,7,8,10] [7] table716 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound717

theorem bound715 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,10] table715, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,6,7,8,10] [1] table715 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound716

theorem bound714 : ∀ f ∈ assignSearch step finish [] [] table714, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound713 : ∀ f ∈ assignSearch step finish [11] [11] table713, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table713 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound714

theorem bound712 : ∀ f ∈ assignSearch step finish [10,11] [1,11] table712, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,11] [1] table712 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound713

theorem bound711 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,11] table711, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,11] [0] table711 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound712

theorem bound710 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,3,11] table710, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,3,11] [3] table710 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound711

theorem bound709 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,6,11] table709, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,6,11] [6] table709 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound710

theorem bound708 : ∀ f ∈ assignSearch step finish [] [] table708, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound707 : ∀ f ∈ assignSearch step finish [11] [3] table707, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table707 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound708

theorem bound706 : ∀ f ∈ assignSearch step finish [10,11] [3,6] table706, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,6] [6] table706 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound707

theorem bound705 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,7] table705, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,7] [7] table705 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound706

theorem bound704 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,6,7,11] table704, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,6,7,11] [11] table704 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound705
end C13.Enumeration.Canonical.Pair61_61
