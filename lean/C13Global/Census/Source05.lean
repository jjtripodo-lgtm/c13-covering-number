import C13Global.Relative.Source05
import C13Global.Bindings.Source05
namespace C13.Global.Source05
open Finset C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem all_foursets (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link05 Q :=
  Relative.Source05.all_foursets alphabet_complete Q hQ
end C13.Global.Source05
