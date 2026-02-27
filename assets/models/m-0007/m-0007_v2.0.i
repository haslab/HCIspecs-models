/*
# positions
#  tray=(572,101)
#  screen=(100,100)
#  photocopier=(176,397)
#  main=(100,100)
*/

types
 DoorT = {open, closed}
 ErrorT = {ok, abc, bc, ac, c}
 DisplayT = {idle, copy, errorABC, errorBC, errorAC, errorC, noPaper, doorOpen} #- removed to solve res. prob.
 CapacityT = 0..20

interactor tray
 attributes
  empty: boolean
  openStatus: boolean
 actions
  opent closet uset putPaper takePaper
 axioms
  per(opent) -> !openStatus
  per(closet) -> openStatus
  per(uset) -> !openStatus & !empty
  per(putPaper) -> openStatus
  per(takePaper) -> openStatus & !empty
  [opent|closet] keep(empty)
  [putPaper] !empty'
  [opent] openStatus'
  [closet] !openStatus'
  [uset|putPaper|takePaper] keep(openStatus)

interactor screen
 attributes
  [vis] info: DisplayT
 actions
  setDisplay(DisplayT)
 axioms
  [setDisplay(_m)] info' = _m
  per(setDisplay(_m)) -> info != _m
#  per(setDisplay_idle) -> info != idle
#  per(setDisplay_copy) -> info != copy
#  per(setDisplay_errorABC) -> info != errorABC
#  per(setDisplay_errorBC) -> info != errorBC
#  per(setDisplay_errorAC) -> info != errorAC
#  per(setDisplay_errorC) -> info != errorC
#  per(setDisplay_noPaper) -> info != noPaper
#  per(setDisplay_doorOpen) -> info != doorOpen

interactor photocopier
 aggregates
  tray via tray1
  screen via display
 attributes
  [vis] door: DoorT # visibility added to solve resourcing problem
  [vis] copying: boolean
  error: ErrorT
 actions
  opend close start stop checkA checkB checkC
  jam makecopy
 axioms
  per(opend) -> door=closed
  [opend] door'=open & !copying' & keep(error)
  per(close) -> door=open
  [close] door'=closed & keep(copying, error)
  per(start) -> !copying & door=closed & error=ok
  [start] copying' & keep(door, error)
  per(stop) -> copying
  [stop] !copying' & keep(door, error)
  per(jam) -> copying
  [jam] error' in {abc, bc, ac} & door'=door &  !copying'
  per(makecopy) -> copying
  [makecopy] keep(door,copying,error)
  per(checkA) -> door=open
  error=abc -> [checkA] error'=bc & door'=door & !copying'
  error=ac -> [checkA] error'=c & door'=door & !copying'
  !(error in {abc,ac}) -> [checkA] keep(error, door) & !copying'
  per(checkB) -> door=open
  error=bc -> [checkB] error'=c & door'=door & !copying'
  !(error=bc) -> [checkB] keep(error, door) & !copying'
  per(checkC) -> door=open
  error=c -> [checkC] error'=ok & door'=door & !copying'
  !(error=c) -> [checkC] keep(error, door) & !copying'
# tray coordination
  per(close) -> !tray1.openStatus
  per(start) -> !tray1.empty
  [opend|close|start|stop|checkA|checkB|checkC|jam] keep(tray1.empty,tray1.openStatus)
  [start] keep(tray1.openStatus)
  makecopy <-> tray1.uset
  per(tray1.opent) -> door=open
  per(tray1.closet) -> door=open
  [tray1.opent|tray1.closet] keep(door,copying,error) #,display.info)
  [tray1.putPaper] keep(door,copying,error)
  copying -> !tray1.empty
# display coordination
# display must not go against system state
  display.info=copy -> copying
  display.info=errorABC -> error=abc
  display.info=errorBC -> error=bc
  display.info=errorAC -> error=ac
  display.info=errorC -> error=c
  display.info=noPaper -> tray1.empty
  display.info=doorOpen -> door=open
# display update
  [close] display.info'=idle # this is wrong!!
  [opend] display.info'=doorOpen # this is wrong!!
  [start] display.info'=copy
  [stop] display.info'=idle
  [jam] (error'=abc) -> display.info'=errorABC
  [jam] (error'=bc) -> display.info'=errorBC
  [jam] (error'=ac) -> display.info'=errorAC
  [checkA] (error'=bc) -> display.info'=errorBC
  [checkA] (error'=c) -> display.info'=errorC
  [checkA] (error'=error) -> keep(display.info)
  [checkB] (error'=c) -> display.info'=errorC
  [checkB] (error'=error) -> keep(display.info)
  [checkC] (error'=ok) -> display.info'=idle
  [checkC] (error'=error) -> keep(display.info)
# the display can only change in response to some event on the device
  [display.setDisplay(_m)] (opend' | close' | start' | stop' | checkA' | checkB' | checkC' | jam' | makecopy' | tray1.opent' | tray1.closet' | tray1.uset' | tray1.putPaper' | tray1.takePaper')
# display tray coordination
  [makecopy] tray1.empty' -> display.info=noPaper
  [] door=closed & !copying & error=ok & !(tray1.openStatus) & !(tray1.empty) & display.info = idle #noPaper

interactor main
 aggregates
  photocopier via device
 axioms
  per(device.opend) -> device.display.info in {errorABC, errorBC, errorAC, noPaper}
  per(device.close) -> device.display.info=idle & device.door=open
  per(device.checkA) -> device.display.info in {errorABC, errorAC}
  per(device.start) -> device.display.info=idle & device.door=closed
  per(device.checkB) -> device.display.info=errorBC #{error_bc, error_abc}
  per(device.checkC) -> device.display.info=errorC
  per(device.tray1.opent) -> device.display.info=noPaper
 test
  AG(device.error = abc -> EF(device.error = ok))
