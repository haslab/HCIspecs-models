# This model directly derived from the Mathematica model

 defines
  turnKnobRIGHT = (knob=LoZ -> knob'=OFF) & (knob=OFF -> knob'=VAC) & (knob=VAC -> knob'=VDC) & (knob=VDC -> knob'=mV) & (knob=mV -> knob'=Ohm) & (knob=Ohm -> knob'=Cont)
  turnKnobLEFT = (knob=Cont -> knob'=Ohm) & (knob=Ohm -> knob'=mV) & (knob=mV -> knob'=VDC) & (knob=VDC -> knob'=VAC) & (knob=VAC -> knob'=OFF) & (knob=OFF -> knob'=LoZ)
  fixDetails = !hold' & minmax'=normal & range'=auto & (knob'=VAC -> (ac' & keep(light))) & (knob'=OFF -> (keep(ac) & !light')) & (knob'!=VAC -> (!ac' & keep(light)))
  stepMINMAX = (minmax=normal -> minmax'=MAXm) & (minmax=MAXm -> minmax'=MINm) & (minmax=MINm -> minmax'=AVGm) & (minmax=AVGm -> minmax'=Current) & (minmax=Current -> minmax'=normal)
  step4RANGE = (range=auto -> range'=m6) & (range=m6 -> range'=m60) & (range=m60 -> range'=m600) & (range=m600 -> range'=m6)
  step7RANGE = (range=auto -> range'=m60M) & (range=m60M -> range'=m600) & (range=m600 -> range'=m6K) & (range=m6K -> range'=m60K) & (range=m60K -> range'=m600K) & (range=m600K -> range'=m6M) & (range=m6M -> range'=m60M)
  RANGEactiveVACVDC = ((knob=VAC | knob=VDC) & minmax=normal & !hold)
  RANGEactiveOhm = (knob=Ohm & minmax=normal)  
  somestate = (minmax=normal&range=auto&ac&light&hold&knob!=OFF)
  adifferentstate = (minmax!=normal|range!=auto|!ac|!light|!hold)

types
 KnobPositions = {LoZ, OFF, VAC, VDC, mV, Ohm, Cont}
 MinMaxModes = {normal, MAXm, MINm, AVGm, Current}
 RangeModes = {auto, m6, m60, m600, m6K, m60K, m600K, m6M, m60M} # !?

interactor main
 attributes
  [vis] knob: KnobPositions
  [vis] minmax: MinMaxModes
  [vis] range: RangeModes
  [vis] ac: boolean
  [vis] light: boolean
  [vis] hold: boolean
 actions
  pHOLD
  pMINMAX
  pRANGE
  pYELLOW
  pLIGHT
  tRIGHT
  tLEFT
  hMINMAX
  hRANGE
 axioms
  per(tRIGHT) -> knob!=Cont   
  [tRIGHT] (turnKnobRIGHT & fixDetails)
  per(tLEFT) -> knob!=LoZ
  [tLEFT] (turnKnobLEFT & fixDetails)  
  knob=OFF -> [!(tRIGHT|tLEFT)] keep(knob,minmax,range,ac,light,hold)
  knob!=OFF -> [pHOLD] hold'=!hold & keep(knob,minmax,range,ac,light)
  knob!=OFF -> [pLIGHT] light'=!light & keep(knob,minmax,range,ac,hold)
  !(knob in {OFF, LoZ}) -> [pMINMAX] stepMINMAX & keep(knob,range,ac,light,hold)
  knob=LoZ -> [pMINMAX] keep(knob,minmax,range,ac,light,hold)           # need found by t002
  knob!=OFF -> [hMINMAX] minmax'=normal & keep(knob,range,ac,light,hold)
  (knob=mV&minmax=normal&!hold) -> [pYELLOW] ac'=!ac & keep(knob,minmax,range,light,hold)
  !(knob=mV&minmax=normal&!hold) -> [pYELLOW] keep(knob,minmax,range,ac,light,hold)
  RANGEactiveVACVDC -> [pRANGE] (step4RANGE & keep(knob,minmax,ac,light,hold))
  RANGEactiveOhm -> [pRANGE] (step7RANGE & keep(knob,minmax,ac,light,hold)) 
  (!RANGEactiveVACVDC & !RANGEactiveOhm) -> [pRANGE] keep(knob,minmax,range,ac,light,hold)
  knob!=OFF -> [hRANGE] range'=auto & keep(knob,minmax,ac,light,hold)
  [] !ac & !hold & knob=OFF & !light & minmax= normal & range=auto
 test
  AG(knob!=OFF -> AF(knob=OFF))                
 test
  EF(knob=VDC & EX(tLEFT & knob=VDC))         
 test
  !EF(knob!=OFF & AG(knob!=OFF))               
 test
  EF(knob!=OFF & EF(knob=OFF))                 
 test
  AG(knob!=OFF -> (pLIGHT -> light))          
 test
  AG(somestate -> AX(pRANGE -> adifferentstate))  
 test
  AG(somestate -> AX(pYELLOW -> adifferentstate)) 
 
