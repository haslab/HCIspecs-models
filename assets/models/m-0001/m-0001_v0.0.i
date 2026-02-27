#importing 
#  importingi1
    
defines
  MaxTemp = 100
  
types
  Temp=0..MaxTemp
  Status={on,off}

## Interactor Main
interactor main
    
  attributes
    [vis] curTemp: Temp
    [vis] curStatus: Status
  actions
    [vis] OnOffBtn
    [vis] IncTemp
    [vis] DecTemp
   
  axioms
    [] curTemp=0
    [] curStatus=off
    curStatus = off -> [OnOffBtn] (curStatus' = on) & keep(curTemp)
    curStatus = on -> [OnOffBtn] (curStatus' = off) & keep(curTemp)
    curStatus = on -> [IncTemp] (curTemp' = curTemp + 1) & keep(curStatus) 
    curStatus = on -> [DecTemp] (curTemp' = curTemp - 1) & keep(curStatus)
    per(IncTemp) -> (curStatus = on & curTemp < 23)
    per(DecTemp) -> curStatus = on & curTemp > 0
    per(OnOffBtn) -> curStatus = off | curStatus = on
  
 test
  AG(!(curTemp=5))
 test
  AG(!(curTemp=5 & curStatus=off))
 test
  AG(!(curStatus=on & curStatus=off))
 test
  AG(!(curStatus=off & curTemp=31))
