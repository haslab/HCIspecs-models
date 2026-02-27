/*
# positions
#  main=(100,100)
*/

defines
 MAXCOLD = 15
 MAXHOT = 30
 MAXFANSPEED = 10
 fanspeedpp = (fanspeed<MAXFANSPEED -> fanspeed' = fanspeed+1) &  (fanspeed=MAXFANSPEED -> fanspeed' = fanspeed)
 fanspeedmm = (fanspeed>0 -> fanspeed' = fanspeed -1) &  (fanspeed=0 -> fanspeed' = fanspeed)
 settemppp = (settemp<MAXHOT -> settemp'=settemp+1) &  (settemp=MAXHOT -> settemp'=settemp)
 settempmm = (settemp>MAXCOLD -> settemp'=settemp -1) &  (settemp=MAXCOLD -> settemp'=settemp)
 stepairflow = (airflow=panel -> airflow'=double) & (airflow=double -> airflow'=floor) & (airflow=floor -> airflow'=floorws) & (airflow=floorws -> airflow'=panel)

types
 Temp = MAXCOLD .. MAXHOT
 AirFlow = {panel, double, floor, floorws, wsclear}
 FanSpeed = 0..MAXFANSPEED

interactor main
 attributes
  on: boolean
  [vis] auto, front, ac: boolean
  automem, acmem: boolean
  [vis] airintake: boolean # true: fresh / false: recirc
  airintakemem: boolean
  [vis] settemp: Temp
  [vis] airflow: AirFlow
  airflowmem: AirFlow
  [vis] fanspeed: FanSpeed
 actions
  autokey off modekey fanspeedup fanspeeddown tempup tempdown frontkey ackey
  airintakekey
 axioms
  [autokey] auto' & on' & !front' & keep(airintake, settemp)
  [off] !auto'& !on' & fanspeed'=0 & !ac' & keep(airintake, settemp, front, airflow)
  [modekey] !auto' & !front' & keep(airintake, settemp, on, fanspeed)
  !front -> [modekey] stepairflow & keep(ac)
  [fanspeedup] !auto' & on' & keep(airintake, settemp, front, airflow)
  on -> [fanspeedup] fanspeedpp & keep(ac)
  !on -> [fanspeedup] fanspeed'=1
  [fanspeeddown] !auto' & on' & keep(airintake, settemp, front, airflow, ac)
  (on & auto) -> [fanspeeddown] keep(fanspeed, ac)
  (on & !auto) -> [fanspeeddown] fanspeedmm & keep(ac)
  !on -> [fanspeeddown] fanspeed'=1
  on -> [tempup] settemppp & keep(auto, airintake, on, front, ac)
  !on -> [tempup] keep(auto, airintake, settemp, on, front, airflow, fanspeed, ac)
  on -> [tempdown] settempmm & keep(auto, airintake, on, front, ac)
  !on -> [tempdown] keep(auto, airintake, settemp, on, front, airflow, fanspeed, ac)
  on -> [frontkey] on' & front'=!front & keep(settemp)
  !on -> [frontkey] on' & front' & keep(settemp)
  [frontkey] front' -> (!auto' & !airintake' & ac')
  front <-> airflow=wsclear
  on -> [ackey] ac'=!ac & keep(auto, airintake, settemp, on, front, airflow, fanspeed)
  !on -> [ackey] keep(auto, airintake, settemp, on, front, airflow, fanspeed, ac)
  [airintakekey] airintake'=!airintake & keep(auto, settemp, on, front, airflow, fanspeed, ac)
  []  !auto& !on & fanspeed=0 & !ac
# For the memory we write axioms that are more attribute based than action based (above they are action based)
# airflow
  !front -> [frontkey] airflowmem'=airflow
  front -> [!(frontkey|modekey)] keep(airflowmem)
  front -> [modekey] airflow'=airflowmem
  (on & front) -> [frontkey] airflow'=airflowmem
  (!on & front) -> [frontkey] keep(airflowmem)
# airintake
  !front -> [frontkey] airintakemem'=airintake
  front -> [!(frontkey|airintakekey)] keep(airintakemem)
  front -> [airintakekey] airintakemem'=airintake'
  (on & front) -> [frontkey] airintake'=airintakemem
  (!on & front) -> [frontkey] keep(airintakemem)
# ac
  [ackey] acmem'=ac'
  [!(ackey)] keep(acmem)
  (front & on) -> [modekey] ac'=acmem
  (front & !on) -> [modekey] keep(ac)
  !on -> [fanspeedup|fanspeeddown] ac'=acmem
  [frontkey] !front' -> ac'=acmem
  [autokey] ac'=acmem
# auto
  [autokey|modekey] automem'=auto'
  [!(autokey|modekey|frontkey)] keep(automem)
  !on -> [frontkey] keep(automem)
  on -> [frontkey] automem'=auto
  [frontkey] !front' -> auto'=automem
 test
  AG((airflow = panel & !auto) -> AX(modekey -> !EF(airflow = panel & !auto)))
