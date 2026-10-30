import C13Enumeration.Canonical.Unique
import C13Enumeration.Canonical.Lookup
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Bounds.Source01
import C13Enumeration.Canonical.Bounds.Source02
import C13Enumeration.Canonical.Bounds.Source03
import C13Enumeration.Canonical.Bounds.Source04
import C13Enumeration.Canonical.Bounds.Source05
import C13Enumeration.Canonical.Bounds.Source06
import C13Enumeration.Canonical.Bounds.Source07
import C13Enumeration.Canonical.Bounds.Source08
import C13Enumeration.Canonical.Bounds.Source09
import C13Enumeration.Canonical.Bounds.Source10
import C13Enumeration.Canonical.Bounds.Source11
import C13Enumeration.Canonical.Bounds.Source12
import C13Enumeration.Canonical.Bounds.Source13
import C13Enumeration.Canonical.Bounds.Source14
import C13Enumeration.Canonical.Bounds.Source15
import C13Enumeration.Canonical.Bounds.Source16
import C13Enumeration.Canonical.Bounds.Source17
import C13Enumeration.Canonical.Bounds.Source18
import C13Enumeration.Canonical.Bounds.Source19
import C13Enumeration.Canonical.Bounds.Source20
import C13Enumeration.Canonical.Bounds.Source21
import C13Enumeration.Canonical.Bounds.Source22
import C13Enumeration.Canonical.Bounds.Source23
import C13Enumeration.Canonical.Bounds.Source24
import C13Enumeration.Canonical.Bounds.Source25
import C13Enumeration.Canonical.Bounds.Source26
import C13Enumeration.Canonical.Bounds.Source27
import C13Enumeration.Canonical.Bounds.Source28
import C13Enumeration.Canonical.Bounds.Source29
import C13Enumeration.Canonical.Bounds.Source30
import C13Enumeration.Canonical.Bounds.Source31
import C13Enumeration.Canonical.Bounds.Source32
import C13Enumeration.Canonical.Bounds.Source33
import C13Enumeration.Canonical.Bounds.Source34
import C13Enumeration.Canonical.Bounds.Source35
import C13Enumeration.Canonical.Bounds.Source36
import C13Enumeration.Canonical.Bounds.Source37
import C13Enumeration.Canonical.Bounds.Source38
import C13Enumeration.Canonical.Bounds.Source39
import C13Enumeration.Canonical.Bounds.Source40
import C13Enumeration.Canonical.Bounds.Source41
import C13Enumeration.Canonical.Bounds.Source42
import C13Enumeration.Canonical.Bounds.Source43
import C13Enumeration.Canonical.Bounds.Source44
import C13Enumeration.Canonical.Bounds.Source45
import C13Enumeration.Canonical.Bounds.Source46
import C13Enumeration.Canonical.Bounds.Source47
import C13Enumeration.Canonical.Bounds.Source48
import C13Enumeration.Canonical.Bounds.Source49
import C13Enumeration.Canonical.Bounds.Source50
import C13Enumeration.Canonical.Bounds.Source51
import C13Enumeration.Canonical.Bounds.Source52
import C13Enumeration.Canonical.Bounds.Source53
import C13Enumeration.Canonical.Bounds.Source54
import C13Enumeration.Canonical.Bounds.Source55
import C13Enumeration.Canonical.Bounds.Source56
import C13Enumeration.Canonical.Bounds.Source57
import C13Enumeration.Canonical.Bounds.Source58
import C13Enumeration.Canonical.Bounds.Source59
import C13Enumeration.Canonical.Bounds.Source60
import C13Enumeration.Canonical.Bounds.Source61
import C13Enumeration.Canonical.Bounds.Source62
import C13Enumeration.Canonical.Bounds.Source63
import C13Enumeration.Canonical.Bounds.Source64
import C13Enumeration.Canonical.Bounds.Source65
import C13Enumeration.Canonical.Bounds.Source66
import C13Enumeration.Canonical.Bounds.Source67
import C13Enumeration.Canonical.Bounds.Source68
namespace C13.Enumeration.Canonical
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def groups : List (List (Record templates)) := [Normalizers.Source01.entries,Normalizers.Source02.entries,Normalizers.Source03.entries,Normalizers.Source04.entries,Normalizers.Source05.entries,Normalizers.Source06.entries,Normalizers.Source07.entries,Normalizers.Source08.entries,Normalizers.Source09.entries,Normalizers.Source10.entries,Normalizers.Source11.entries,Normalizers.Source12.entries,Normalizers.Source13.entries,Normalizers.Source14.entries,Normalizers.Source15.entries,Normalizers.Source16.entries,Normalizers.Source17.entries,Normalizers.Source18.entries,Normalizers.Source19.entries,Normalizers.Source20.entries,Normalizers.Source21.entries,Normalizers.Source22.entries,Normalizers.Source23.entries,Normalizers.Source24.entries,Normalizers.Source25.entries,Normalizers.Source26.entries,Normalizers.Source27.entries,Normalizers.Source28.entries,Normalizers.Source29.entries,Normalizers.Source30.entries,Normalizers.Source31.entries,Normalizers.Source32.entries,Normalizers.Source33.entries,Normalizers.Source34.entries,Normalizers.Source35.entries,Normalizers.Source36.entries,Normalizers.Source37.entries,Normalizers.Source38.entries,Normalizers.Source39.entries,Normalizers.Source40.entries,Normalizers.Source41.entries,Normalizers.Source42.entries,Normalizers.Source43.entries,Normalizers.Source44.entries,Normalizers.Source45.entries,Normalizers.Source46.entries,Normalizers.Source47.entries,Normalizers.Source48.entries,Normalizers.Source49.entries,Normalizers.Source50.entries,Normalizers.Source51.entries,Normalizers.Source52.entries,Normalizers.Source53.entries,Normalizers.Source54.entries,Normalizers.Source55.entries,Normalizers.Source56.entries,Normalizers.Source57.entries,Normalizers.Source58.entries,Normalizers.Source59.entries,Normalizers.Source60.entries,Normalizers.Source61.entries,Normalizers.Source62.entries,Normalizers.Source63.entries,Normalizers.Source64.entries,Normalizers.Source65.entries,Normalizers.Source66.entries,Normalizers.Source67.entries,Normalizers.Source68.entries]
def records : List (Record templates) := groups.flatten

def CoveredFamily (K : Family Point) : Prop :=
  ∀ q : Point, q ≠ hole → ∃ r ∈ records, r.family = K ∧ r.center = q

theorem covered01 : CoveredFamily link01 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source01.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source01.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered02 : CoveredFamily link02 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source02.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source02.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered03 : CoveredFamily link03 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source03.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source03.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered04 : CoveredFamily link04 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source04.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source04.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered05 : CoveredFamily link05 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source05.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source05.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered06 : CoveredFamily link06 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source06.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source06.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered07 : CoveredFamily link07 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source07.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source07.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered08 : CoveredFamily link08 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source08.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source08.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered09 : CoveredFamily link09 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source09.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source09.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered10 : CoveredFamily link10 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source10.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source10.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered11 : CoveredFamily link11 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source11.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source11.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered12 : CoveredFamily link12 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source12.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source12.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered13 : CoveredFamily link13 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source13.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source13.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered14 : CoveredFamily link14 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source14.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source14.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered15 : CoveredFamily link15 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source15.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source15.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered16 : CoveredFamily link16 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source16.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source16.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered17 : CoveredFamily link17 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source17.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source17.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered18 : CoveredFamily link18 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source18.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source18.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered19 : CoveredFamily link19 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source19.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source19.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered20 : CoveredFamily link20 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source20.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source20.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered21 : CoveredFamily link21 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source21.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source21.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered22 : CoveredFamily link22 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source22.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source22.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered23 : CoveredFamily link23 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source23.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source23.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered24 : CoveredFamily link24 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source24.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source24.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered25 : CoveredFamily link25 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source25.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source25.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered26 : CoveredFamily link26 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source26.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source26.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered27 : CoveredFamily link27 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source27.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source27.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered28 : CoveredFamily link28 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source28.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source28.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered29 : CoveredFamily link29 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source29.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source29.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered30 : CoveredFamily link30 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source30.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source30.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered31 : CoveredFamily link31 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source31.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source31.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered32 : CoveredFamily link32 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source32.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source32.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered33 : CoveredFamily link33 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source33.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source33.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered34 : CoveredFamily link34 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source34.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source34.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered35 : CoveredFamily link35 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source35.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source35.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered36 : CoveredFamily link36 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source36.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source36.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered37 : CoveredFamily link37 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source37.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source37.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered38 : CoveredFamily link38 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source38.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source38.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered39 : CoveredFamily link39 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source39.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source39.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered40 : CoveredFamily link40 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source40.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source40.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered41 : CoveredFamily link41 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source41.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source41.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered42 : CoveredFamily link42 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source42.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source42.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered43 : CoveredFamily link43 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source43.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source43.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered44 : CoveredFamily link44 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source44.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source44.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered45 : CoveredFamily link45 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source45.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source45.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered46 : CoveredFamily link46 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source46.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source46.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered47 : CoveredFamily link47 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source47.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source47.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered48 : CoveredFamily link48 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source48.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source48.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered49 : CoveredFamily link49 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source49.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source49.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered50 : CoveredFamily link50 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source50.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source50.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered51 : CoveredFamily link51 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source51.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source51.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered52 : CoveredFamily link52 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source52.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source52.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered53 : CoveredFamily link53 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source53.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source53.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered54 : CoveredFamily link54 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source54.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source54.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered55 : CoveredFamily link55 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source55.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source55.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered56 : CoveredFamily link56 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source56.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source56.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered57 : CoveredFamily link57 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source57.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source57.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered58 : CoveredFamily link58 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source58.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source58.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered59 : CoveredFamily link59 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source59.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source59.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered60 : CoveredFamily link60 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source60.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source60.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered61 : CoveredFamily link61 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source61.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source61.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered62 : CoveredFamily link62 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source62.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source62.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered63 : CoveredFamily link63 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source63.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source63.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered64 : CoveredFamily link64 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source64.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source64.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered65 : CoveredFamily link65 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source65.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source65.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered66 : CoveredFamily link66 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source66.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source66.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered67 : CoveredFamily link67 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source67.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source67.entries,by simp [groups],hr⟩,hf,hc⟩

theorem covered68 : CoveredFamily figure6 := by
  intro q hq
  obtain ⟨r,hr,hf,hc⟩ := Normalizers.Source68.covered q hq
  exact ⟨r,List.mem_flatten.mpr ⟨Normalizers.Source68.entries,by simp [groups],hr⟩,hf,hc⟩

theorem ordinary_covered : ∀ K ∈ ordinaryList, CoveredFamily K := by
  simp only [ordinaryList,List.forall_mem_cons]
  exact ⟨covered01,covered02,covered03,covered04,covered05,covered06,covered07,covered08,covered09,covered10,covered11,covered12,covered13,covered14,covered15,covered16,covered17,covered18,covered19,covered20,covered21,covered22,covered23,covered24,covered25,covered26,covered27,covered28,covered29,covered30,covered31,covered32,covered33,covered34,covered35,covered36,covered37,covered38,covered39,covered40,covered41,covered42,covered43,covered44,covered45,covered46,covered47,covered48,covered49,covered50,covered51,covered52,covered53,covered54,covered55,covered56,covered57,covered58,covered59,covered60,covered61,covered62,covered63,covered64,covered65,covered66,covered67,(by intro K hK; simp at hK)⟩

theorem records_cover : Covers records := by
  intro K hK
  obtain h | h := Finset.mem_insert.mp hK
  · subst K; exact covered68
  · exact ordinary_covered K (List.mem_toFinset.mp h)

theorem source_records_complete : ∀ r ∈ records, SourceComplete domains r := by
  intro r hr
  obtain ⟨part,hpart,hr⟩ := List.mem_flatten.mp hr
  simp only [groups,List.mem_cons,List.not_mem_nil,or_false] at hpart
  rcases hpart with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bounds.Source01.entries_complete r hr
  · exact Bounds.Source02.entries_complete r hr
  · exact Bounds.Source03.entries_complete r hr
  · exact Bounds.Source04.entries_complete r hr
  · exact Bounds.Source05.entries_complete r hr
  · exact Bounds.Source06.entries_complete r hr
  · exact Bounds.Source07.entries_complete r hr
  · exact Bounds.Source08.entries_complete r hr
  · exact Bounds.Source09.entries_complete r hr
  · exact Bounds.Source10.entries_complete r hr
  · exact Bounds.Source11.entries_complete r hr
  · exact Bounds.Source12.entries_complete r hr
  · exact Bounds.Source13.entries_complete r hr
  · exact Bounds.Source14.entries_complete r hr
  · exact Bounds.Source15.entries_complete r hr
  · exact Bounds.Source16.entries_complete r hr
  · exact Bounds.Source17.entries_complete r hr
  · exact Bounds.Source18.entries_complete r hr
  · exact Bounds.Source19.entries_complete r hr
  · exact Bounds.Source20.entries_complete r hr
  · exact Bounds.Source21.entries_complete r hr
  · exact Bounds.Source22.entries_complete r hr
  · exact Bounds.Source23.entries_complete r hr
  · exact Bounds.Source24.entries_complete r hr
  · exact Bounds.Source25.entries_complete r hr
  · exact Bounds.Source26.entries_complete r hr
  · exact Bounds.Source27.entries_complete r hr
  · exact Bounds.Source28.entries_complete r hr
  · exact Bounds.Source29.entries_complete r hr
  · exact Bounds.Source30.entries_complete r hr
  · exact Bounds.Source31.entries_complete r hr
  · exact Bounds.Source32.entries_complete r hr
  · exact Bounds.Source33.entries_complete r hr
  · exact Bounds.Source34.entries_complete r hr
  · exact Bounds.Source35.entries_complete r hr
  · exact Bounds.Source36.entries_complete r hr
  · exact Bounds.Source37.entries_complete r hr
  · exact Bounds.Source38.entries_complete r hr
  · exact Bounds.Source39.entries_complete r hr
  · exact Bounds.Source40.entries_complete r hr
  · exact Bounds.Source41.entries_complete r hr
  · exact Bounds.Source42.entries_complete r hr
  · exact Bounds.Source43.entries_complete r hr
  · exact Bounds.Source44.entries_complete r hr
  · exact Bounds.Source45.entries_complete r hr
  · exact Bounds.Source46.entries_complete r hr
  · exact Bounds.Source47.entries_complete r hr
  · exact Bounds.Source48.entries_complete r hr
  · exact Bounds.Source49.entries_complete r hr
  · exact Bounds.Source50.entries_complete r hr
  · exact Bounds.Source51.entries_complete r hr
  · exact Bounds.Source52.entries_complete r hr
  · exact Bounds.Source53.entries_complete r hr
  · exact Bounds.Source54.entries_complete r hr
  · exact Bounds.Source55.entries_complete r hr
  · exact Bounds.Source56.entries_complete r hr
  · exact Bounds.Source57.entries_complete r hr
  · exact Bounds.Source58.entries_complete r hr
  · exact Bounds.Source59.entries_complete r hr
  · exact Bounds.Source60.entries_complete r hr
  · exact Bounds.Source61.entries_complete r hr
  · exact Bounds.Source62.entries_complete r hr
  · exact Bounds.Source63.entries_complete r hr
  · exact Bounds.Source64.entries_complete r hr
  · exact Bounds.Source65.entries_complete r hr
  · exact Bounds.Source66.entries_complete r hr
  · exact Bounds.Source67.entries_complete r hr
  · exact Bounds.Source68.entries_complete r hr

theorem canonical_complete (j : Fin 62) :
    ∀ P ∈ completeDomain catalog hole (templates j).family hole (templates j).center,
      ∃ p ∈ (domains j).supported.domain.2, RepresentsPencil p P :=
  canonical_domains_complete templates domains records records_cover templates_unique source_records_complete j

/-- One computable catalogue-wide coded-domain lookup; only the selected
normalizer is used to relabel the literal canonical row table. -/
def codedDomains (K : Family Point) (q : Point) : CodedDomain :=
  lookupDomain domains records K q

theorem codedDomain_labels (K : Family Point) (q : Point) :
    (codedDomains K q).supported.domain.1 = q.val :=
  lookupDomain_label domains records K q

theorem all_domains_complete (K : Family Point) (hK : K ∈ catalog)
    (q : Point) (hq : q ≠ hole) :
    ∀ P ∈ completeDomain catalog hole K hole q,
      ∃ p ∈ (codedDomains K q).supported.domain.2, RepresentsPencil p P :=
  lookupDomain_complete domains canonical_complete records records_cover K hK q hq

theorem records_count : records.length = 816 := by decide +kernel

/-- Discharges the complete finite-domain obligation for the pinned catalogue.
It does not supply the global four-point no-join census or published classification. -/
theorem executable_domains_complete : ExecutableDomainsComplete catalog hole
    (fun K q => (codedDomains K q).supported.domain.2) := by
  intro K hK q hq P hP
  exact all_domains_complete K hK q hq P hP
end C13.Enumeration.Canonical
