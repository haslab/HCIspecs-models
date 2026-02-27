# ---------------------------------------------------------------
#  MAL Model: emuchartsFCUMAL
#  Author: <author name>
#          <affiliation>
#          <contact>
# ---------------------------------------------------------------

defines
 INTMIN = 0
 INTMAX = 9
 MINhPa = 0
 MAXhPa = 4
 MINinHg = 0
 MAXinHg = 4
 MAXELAPSE = 9
 id = 1
 pt = 2
 dd = 3
 number1 = {blank, zero, one, two, three, four, five, six, seven, eight, nine}
 number2 = {blank, zero, one, two, three, four, five, six, seven, eight, nine}
 pointval = {blank, point}

types
 int = INTMIN..INTMAX
 nat = 0..INTMAX
 character = {blank, zero, one, two, three, four, five, six, seven, eight, nine, point}#, symbol, alpha}
 UnitsType = {hPa, inHg}
 MachineState = { EDITPRESSURE, QNH, STD }
 EntryModeState = { POINTENTERED, POINTNOTENTERED, VALIDATION }
 string = array id .. dd of character
 MsgType = {nomessage, timeout}

interactor FCUDataEntry
 attributes
  datamode: EntryModeState
  decimalDigits: nat
  actualdecimalDigits: nat
  integerDigits: nat
  actualintegerDigits: nat
  newpoint: boolean
  actualpoint: boolean
  units: UnitsType

 actions
  processintKey(nat)
  processclrKey
  processescKey
  processTimeout
  processpointKey
  processOKKey
  updateunits(UnitsType)
  update

 axioms
  [] datamode=POINTNOTENTERED & decimalDigits=0 & integerDigits=0 & !newpoint & units=inHg & actualintegerDigits=0 &
     !actualpoint & actualdecimalDigits=0 

  per(processintKey(_x)) -> datamode in {POINTNOTENTERED, POINTENTERED} 
  datamode=POINTNOTENTERED -> [processintKey(_x)] integerDigits'= _x & 
                                    keep(datamode,decimalDigits,newpoint,actualintegerDigits,actualdecimalDigits,actualpoint,units)             
  datamode=POINTENTERED -> [processintKey(_x)] decimalDigits'=_x &
                                    keep(datamode,integerDigits,newpoint,actualintegerDigits,actualdecimalDigits,actualpoint,units)
  
  per(processclrKey) -> datamode in {POINTENTERED , POINTNOTENTERED}
  [processclrKey] integerDigits'=0 & decimalDigits'=0 & !newpoint' & datamode'=POINTNOTENTERED &
                      actualintegerDigits'=integerDigits & actualdecimalDigits'=decimalDigits & actualpoint'=newpoint &
                      keep(units)
                      
  per(processescKey) -> datamode in {POINTNOTENTERED, POINTENTERED} 
  [processescKey] decimalDigits'= actualdecimalDigits & integerDigits'= actualintegerDigits & newpoint'=actualpoint  &
                         keep(datamode,actualpoint,units,actualdecimalDigits,actualintegerDigits)

  [processTimeout] decimalDigits'=actualdecimalDigits & integerDigits'=actualintegerDigits & newpoint'=actualpoint  &
                         keep(datamode,actualpoint,units,actualdecimalDigits,actualintegerDigits)
                         
# no conversion has taken place here
  per(updateunits(_x)) -> datamode in {POINTNOTENTERED , POINTENTERED}
  [updateunits(_x)] units'=_x & keep(datamode,integerDigits, decimalDigits,newpoint,actualintegerDigits,actualdecimalDigits,actualpoint)

  # Pre-condition vs modal axiom?!
  per(processpointKey) -> datamode=POINTNOTENTERED 
  [processpointKey] (datamode'=POINTENTERED) & newpoint'=true &
                          keep(integerDigits, decimalDigits,actualintegerDigits,actualdecimalDigits,actualpoint, units)
                          
  per(processOKKey) -> datamode in {POINTENTERED, POINTNOTENTERED}
  [processOKKey] datamode'=VALIDATION & actualintegerDigits'=integerDigits & actualdecimalDigits'=decimalDigits &
                 actualpoint'=newpoint & keep(decimalDigits,integerDigits,newpoint,units)

  [update] actualintegerDigits'=integerDigits & actualdecimalDigits'=decimalDigits & actualpoint'=newpoint & 
           keep(datamode,decimalDigits,integerDigits,newpoint,units)

interactor main #emuchartsFCUMAL
 aggregates 
  FCUDataEntry via fcud
 attributes
  st: MachineState
  msg: MsgType
  editboxselected: boolean
  display: string
  elapse: int

 actions
  clickCLR
  clickdigit(character)
  clickeditboxpressure
  clickESC
  clickUnits(UnitsType)
  clickOK
  clickpoint
  clickstdradio
  clickqnhradio
  tick

 axioms
  [] st=STD & editboxselected=FALSE & elapse=MAXELAPSE & msg=nomessage & display[id]=blank & display[pt]=blank & display[dd]=blank

  # Actions mapping
  effect(fcud.processclrKey) <-> (effect(clickCLR) | effect(clickeditboxpressure))
  effect(fcud.processintKey(0)) <-> effect(clickdigit(zero))
  effect(fcud.processintKey(1)) <-> effect(clickdigit(one))
  effect(fcud.processintKey(2)) <-> effect(clickdigit(two))
  effect(fcud.processintKey(3)) <-> effect(clickdigit(three))
  effect(fcud.processintKey(4)) <-> effect(clickdigit(four))
  effect(fcud.processintKey(5)) <-> effect(clickdigit(five))
  effect(fcud.processintKey(6)) <-> effect(clickdigit(six))
  effect(fcud.processintKey(7)) <-> effect(clickdigit(seven))
  effect(fcud.processintKey(8)) <-> effect(clickdigit(eight))
  effect(fcud.processintKey(9)) <-> effect(clickdigit(nine))
  effect(fcud.processescKey) <-> effect(clickESC)
  effect(fcud.updateunits(hPa)) <-> effect(clickUnits(hPa))  
  effect(fcud.updateunits(inHg)) <-> effect(clickUnits(inHg))
  effect(fcud.processOKKey) <-> effect(clickOK)
  effect(fcud.processpointKey) <-> effect(clickpoint)
  effect(fcud.update) <-> (effect(clickstdradio) | effect(clickqnhradio))
  effect(fcud.processTimeout) <-> (effect(tick) & elapse=0)

  # Actions spec.
  per(clickCLR) -> st=EDITPRESSURE
  [clickCLR] display[id]'=blank & display[pt]' = blank & display[dd]' = blank &
             elapse' = MAXELAPSE & keep(msg,st,editboxselected)

  per(clickdigit(_d)) -> st=EDITPRESSURE & _d!=blank
  fcud.newpoint -> [clickdigit(_d)] display[dd]'=_d & elapse'=MAXELAPSE & keep(msg,st,editboxselected,display[pt],display[id])
  !fcud.newpoint -> [clickdigit(_d)] display[id]'=_d & elapse'=MAXELAPSE & keep(msg,st,editboxselected,display[pt],display[dd])
  
  per(clickeditboxpressure) -> (st=QNH & !editboxselected) 
  [clickeditboxpressure] editboxselected' & st'=EDITPRESSURE & elapse'=MAXELAPSE & keep(msg,elapse,display)          
  
  per(clickESC) -> st=EDITPRESSURE 
  [clickESC] st'=QNH & !editboxselected' & keep(msg,elapse, display)

  # this action does not do the recalculations
  per(clickUnits(_u)) -> (st in {QNH, EDITPRESSURE} & fcud.units!=_u) | st=STD  
  [clickUnits(_u)] keep(msg,st,elapse,editboxselected, display)
  
  per(clickOK) -> st=EDITPRESSURE 
  [clickOK] st'=QNH & !editboxselected' & keep(msg,elapse,display)
  
  per(clickpoint) -> st=EDITPRESSURE  
  [clickpoint] display[pt]'=point & elapse'=MAXELAPSE & 
               keep(msg,st, elapse,editboxselected,display[id],display[dd])
        
  per(clickqnhradio) -> st=STD
  [clickqnhradio] st'=QNH & keep(msg,elapse,editboxselected,display)
  
  per(clickstdradio) -> st=QNH 
  [clickstdradio] st'=STD & keep(msg,elapse,editboxselected, display)

  #per(fcud.processTimeout) -> (st=EDITPRESSURE & elapse=0)
  per(tick) -> st=EDITPRESSURE
  elapse=0 -> [tick] st'=QNH & msg'=timeout & keep(elapse,editboxselected, display)
  elapse>0 -> [tick] st'=EDITPRESSURE & elapse'=elapse-1 & keep(msg,editboxselected, display)
  


# ---------------------------------------------------------------
#  MAL model generated using PVSio-web MALPrinter2 ver 01
#  Tool freely available at http://wwwpvsioweborg

# ---------------------------------------------------------------

  [nil] true
 test
  AG(!(display[1] = three & display[2] = point & display[3] = seven & fcud.actualintegerDigits = 3 & fcud.actualpoint & fcud.actualdecimalDigits = 7 & fcud.units = hPa))
 test
  AG(st != EDITPRESSURE -> ((fcud.actualdecimalDigits = fcud.decimalDigits) & (fcud.actualpoint = fcud.newpoint) & (fcud.actualintegerDigits = fcud.integerDigits)))
 test
  AG(display[1] = $character & display[2] = blank & display[3] = blank -> AX(clickeditboxpressure -> AX(clickESC -> display[1] = $character & display[2] = blank & display[3] = blank)))
 test
  AG(st != STD -> AX(EF(st = STD)))
 test
  AG(st = STD -> AX(!clickqnhradio -> st = STD))
 test
  AG(st = QNH -> AX(!(clickstdradio | clickeditboxpressure) -> st = QNH))
 test
  AG(st = EDITPRESSURE -> AX(!(clickESC | clickOK | msg = timeout) -> st = EDITPRESSURE))
 test
  AG(st != STD -> AX(clickstdradio -> st = STD))
 test
  AG(st != QNH -> AX(clickqnhradio -> st = QNH))
