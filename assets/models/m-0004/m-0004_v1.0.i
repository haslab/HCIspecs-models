## 31st March 2012 BBraun two layer model
## Michael Harrison
## EECS, QMUL and Computing Science, Newcastle University
defines
# generic to device
 maxrate=7
 maxinfuse=7
 infusemin=1
 timeout=3
 maxtime=7
# specific to B Braun
 timeout=2
 maxdig=1
 maxdata=3
 maxscale=3
 maxdigindex=3
 maxdispvalue=15
 mcmax=4
 drate=0
 dvtbi=1
 dtime=2
 doptions=3
 dstatus=4
 detime=3
 dvol=4
 dalarmvol=5
## to do with kvo
 timetoempty=2
## to do with activities
 mvolume=6
 mtime=3
 mrate=0

types
# generic to device
#  imode={blank, hold, infuse}
  irates=0..maxrate
  iratesaux=1..maxrate
  ivols=0..maxinfuse
  itimes=0..maxtime
  numeral=0..maxdig
# specific to B Braun
  maxdisptype=0..maxdispvalue
  scaletype=0..maxscale
  datatype=0..maxdata
  menutype=0..mcmax
  alarmtype=0..maxscale
  digital = array 0..maxdigindex of numeral
  dispmode = {disprate, dispvtbi, disptime, mainmenu,
               dispinfusing, dispalarm, dispalarmvol,
               optionsmenu, statusmenu, dispblank}
  emode = {dataentry, confirmmode, scalemode, nullmode}
  phases = {ready, entering, confirmed}
  imid = array drate..dalarmvol of boolean
# there is a bigger range than this
  tgttype = {ttime, tvtbi, trate}
interactor pump
 attributes
  [vis] poweredon: boolean
  [vis] infusingstate: boolean
  [vis] infusionrate: irates
  infusionrateaux: iratesaux
  [vis] volumeinfused: ivols
  [vis] vtbi: ivols
  [vis] time: itimes
  [vis] elapsedtime: itimes
  kvorate: irates
  elapse: itimes
  kvoflag: boolean
 actions
  on
  [vis] start
  [vis] pause
  tick
  resetElapsed
#  clearVolumeinfused
  clearkvoflag
  #zerorate
  maximrate
 # pbsrate
 # mbsrate
#  pirate
#  mdrate
  modvtbi(ivols)
  maxvtbi
#  zerovtbi
#  pbsvtbi
#  mbsvtbi
# pivtbi
#  mdvtbi
#  modhvtbi(ivols)
#  maxhvtbi
#  zerohvtbi
#  pbshvtbi
#  mbshvtbi
#  pihvtbi
#  mdhvtbi
  modtime(itimes)
#  zerotime
#  mbstime
#  pbstime
  maxitime
#  pitime
#  mdtime
# the following is special to bbraun
  modrate(irates)

 axioms
  [] !poweredon & !infusingstate & infusionrate=0 & volumeinfused=0 &
     vtbi=0 & elapse=0 & !kvoflag & elapsedtime=0

  !poweredon -> [on]
             poweredon' & !infusingstate &
             elapse'=0 & !kvoflag' & elapsedtime'=0 &
             volumeinfused'=0 &
             vtbi'=0 & infusionrate'=0
  poweredon -> [on]
              !poweredon &
              keep(infusionrate, volumeinfused, vtbi, kvoflag, elapse, elapsedtime)
  # invariant
  infusionrate>0 -> infusionrateaux=infusionrate
  infusionrate>0 -> time=(vtbi/infusionrateaux)
  infusionrate=0 -> time=0
  # need to understand on and off
  per(start) -> !infusingstate & poweredon & (infusionrate != 0)
  kvoflag & (vtbi!=0) -> [start] infusingstate' & !kvoflag' &
          keep(infusionrate, volumeinfused,
               elapsedtime, vtbi, kvorate, elapse, poweredon)
  kvoflag & (vtbi=0) -> [start]
          keep(infusionrate, volumeinfused, poweredon,
               infusingstate,
               elapsedtime, vtbi, kvorate, kvoflag, elapse)
  !kvoflag & (vtbi=0) -> [start] !infusingstate' &
          keep(infusionrate, volumeinfused, poweredon,
               elapsedtime, vtbi, kvorate, kvoflag, elapse)
  !kvoflag & (vtbi != 0)  ->  [start] infusingstate' &
          keep(infusionrate, volumeinfused, poweredon,
               elapsedtime, vtbi, kvorate, kvoflag, elapse)
## pause
  per(pause) -> infusingstate & poweredon
  [pause] !infusingstate' & (elapse'=0) &
          keep(infusionrate, volumeinfused, poweredon,
               elapsedtime, vtbi, kvoflag, kvorate)

# the generic version of tick
# this currently does not tick when the device is on hold,
# so needs changing
  per(tick) -> poweredon
  infusingstate & (infusionrate < vtbi) ->
       [tick] vtbi'=vtbi - infusionrate &
           volumeinfused'=volumeinfused + infusionrate &
           elapsedtime'=elapsedtime+1 &
           keep(kvorate, kvoflag, infusionrate, infusingstate,
                poweredon)
  infusingstate & (infusionrate >= vtbi) & !kvoflag ->
       [tick] (vtbi'=0) & (volumeinfused' = (volumeinfused + vtbi)) &
               elapsedtime'=elapsedtime+1 &
               ((infusionrate<infusemin) ->
                  (kvorate'=infusionrate)) &
               ((infusionrate>=infusemin) ->
                  (kvorate'=infusemin)) &
               kvoflag' & keep(infusionrate, elapse,
                               infusingstate, poweredon)
  infusingstate & (infusionrate >= vtbi) & kvoflag ->
        [tick] (volumeinfused'=volumeinfused+kvorate) &
               elapsedtime'=elapsedtime+1 &
               keep(infusionrate, infusingstate, poweredon,
                    vtbi, elapse, kvorate, kvoflag)
  !infusingstate & (elapse=timeout) ->
       [tick] elapse'=0 &
              keep(infusingstate, poweredon,
                   infusionrate, volumeinfused,
                   elapsedtime, vtbi, kvoflag, kvorate)
  !infusingstate & (elapse<timeout) ->
       [tick] elapse'=elapse+1 &
              keep(infusingstate, poweredon, infusionrate,
                   volumeinfused,
                   elapsedtime, vtbi, kvoflag, kvorate)
  [resetElapsed] elapse'=0 &
                 keep(infusingstate, poweredon, infusionrate,
                       volumeinfused, vtbi,
                      elapsedtime, kvorate, kvoflag)
  [clearkvoflag] !kvoflag' & elapse'=0 &
                 !infusingstate &
                 keep(infusionrate, poweredon,
                      volumeinfused, vtbi,
                      elapsedtime, kvorate)

  [maxvtbi] (vtbi'=maxinfuse) & elapse'=0 & !kvoflag' &
                  keep(infusingstate, poweredon, infusionrate,
                       volumeinfused, elapsedtime,
                       kvorate)
#  [maxhvtbi] vtbi'=maxinfuse & elapse'=0 & !kvoflag' &
#                  keep(infusionstatus,
#                       volumeinfused, time, elapsedtime,
#                       kvorate)
#  [zerovtbi] vtbi'=0 & elapse'=0 & !kvoflag' &
#                  keep(infusionstatus, infusionrate,
#                       volumeinfused, elapsedtime,
#                       kvorate)
#  [zerohvtbi] vtbi'=0 & elapse'=0 & !kvoflag' & time'=0 &
#              infusionrate'=0 &
#                  keep(infusionstatus,
#                       volumeinfused, elapsedtime,
#                       kvorate)
  [modvtbi(_x)] vtbi'=_x & elapse'=0 & !kvoflag' &
                  keep(infusingstate, poweredon, infusionrate,
                       volumeinfused, elapsedtime,
                       kvorate)
#  [modhvtbi(_x)] vtbi'=_x & elapse'=0 & !kvoflag' &
#                  keep(infusionstatus,
#                       volumeinfused, time, elapsedtime,
#                       kvorate)
#  [pbsvtbi] vtbi'=vtbi + bigstep & elapse'=0 & !kvoflag' &
#                  keep(infusionstatus, infusionrate,
#                       volumeinfused, elapsedtime, kvorate)
#  [pbshvtbi] vtbi'=vtbi + bigstep & elapse'=0 & !kvoflag' &
#                  keep(infusionstatus, time,
#                       volumeinfused, elapsedtime, kvorate)
 # [pivtbi] vtbi'=vtbi + 1 & elapse'=0 & !kvoflag' &
#                 keep(infusionstatus, infusionrate,
#                       volumeinfused, elapsedtime,
#                       kvorate)
#  [pihvtbi] vtbi'=vtbi + 1 & elapse'=0 & !kvoflag' &
#                  keep(infusionstatus, time,
#                       volumeinfused, elapsedtime,
#                       kvorate)
#  [mbsvtbi] vtbi'=vtbi - bigstep & elapse'=0 &
#                  keep(infusionstatus, infusionrate,
#                       volumeinfused, elapsedtime,
#                       kvorate, kvoflag, kvorate)
#  [mbshvtbi] vtbi'=vtbi - bigstep & elapse'=0 &
#                  keep(infusionstatus, time,
#                       volumeinfused, elapsedtime,
#                       kvorate, kvoflag, kvorate)
#  [mdvtbi] vtbi'=vtbi - 1 & elapse'=0 &
#                  keep(infusionstatus, infusionrate,
#                       volumeinfused, elapsedtime,
#                       kvorate, kvoflag)
#  [mdhvtbi] vtbi'=vtbi - 1 & elapse'=0 &
#                  keep(infusionstatus, time,
#                       volumeinfused, elapsedtime,
#                       kvorate, kvoflag)
  [modtime(_x)] time'=_x & elapse'=0 &
                keep(infusingstate, poweredon,
                     volumeinfused, vtbi, elapsedtime,
                     kvorate, kvoflag)
#  [zerotime] time'=0 & elapse'=0 &
#                keep(infusionstatus,
#                     volumeinfused, vtbi, elapsedtime,
#                     kvorate, kvoflag)
  [maxitime] time'=maxtime & elapse'=0 &
                keep(infusingstate, poweredon,
                     volumeinfused, vtbi, elapsedtime,
                     kvorate, kvoflag)
#  [pbstime] time'=time+bigstep & elapse'=0 &
#                keep(infusionstatus,
#                     volumeinfused, vtbi, elapsedtime,
#                     kvorate, kvoflag)
#  [pitime] time'=time+1 & elapse'=0 &
#                keep(infusionstatus,
#                     volumeinfused, vtbi, elapsedtime,
#                     kvorate, kvoflag)
#  [mbstime] time'=time-1 & elapse'=0 &
#                keep(infusionstatus,
#                     volumeinfused, vtbi, elapsedtime,
#                     kvorate, kvoflag)
#  [mdtime] time'=time-1 & elapse'=0 &
#                keep(infusionstatus,
#                     volumeinfused, vtbi, elapsedtime,
#                     kvorate, kvoflag)
#
#  [zerorate] infusionrate'=0 & elapse'=0 &
#                  keep(infusionstatus,
#                       volumeinfused, vtbi, elapsedtime,
#                       kvorate, kvoflag)
  [maximrate] infusionrate'=maxrate & elapse'=0 &
                  keep(infusingstate, poweredon,
                       volumeinfused, vtbi, elapsedtime,
                       kvorate, kvoflag)

#  [pbsrate] infusionrate'=infusionrate + bigstep & elapse'=0 &
#                  keep(infusionstatus,
#                       volumeinfused, vtbi, elapsedtime,
#                       kvorate, kvoflag)
 # [pirate] infusionrate'=infusionrate + 1 & elapse'=0 &
 #                 keep(infusionstatus,
  #                     volumeinfused, vtbi, elapsedtime,
 #                      kvorate, kvoflag)

#  [mbsrate] infusionrate'=infusionrate - bigstep & elapse'=0 &
#                  keep(infusionstatus,
 #                      volumeinfused, vtbi, elapsedtime,
#                       kvorate, kvoflag)
#  [mdrate] infusionrate'=infusionrate - 1 & elapse'=0 &
#                  keep(infusionstatus,
#                       volumeinfused, vtbi, elapsedtime,
#                       kvorate, kvoflag)
  [modrate(_x)] infusionrate'=_x & elapse'=0 &
                  keep(infusingstate, poweredon, vtbi,
                       volumeinfused, elapsedtime,
                       kvorate, kvoflag)


# the following is the specific interactor relating to BBraun
interactor main
 aggregates
  pump via device
 attributes
  [vis] displaymode: dispmode
  prevdm: dispmode
  [vis] displayval: digital
# mode flags
  entrymode: emode
  dispvalue: maxdisptype
  dispscale: scaletype
  dispinfrate: irates
  dispinftime: itimes
  dispinfvtbi: ivols
  [vis] entry: datatype
  [vis] target: tgttype
  [vis] menucursor: menutype
  [vis] alarmvolume: alarmtype
  [vis] disp: imid
  devicevtbi: ivols
# attributes relating to activities
## activity meta-attributes
  phasevtbi: phases
  phaserate: phases
  phasetime: phases
  phaseinfuse: phases
 actions
  [vis] start
  [vis] on
  [vis] up
  [vis] down
  [vis] left
  [vis] right
  [vis] ok
  [vis] clear
  tick
## activities
  entervtbi
  confirmvtbi
  enterrate
  confirmrate
  entertime
  confirmtime
  startinfuse
 axioms
  [] (dispvalue=0) & (displaymode=mainmenu) &
     (entry=maxdata) & (target=tvtbi) & (menucursor=drate) &
     (entrymode=nullmode) &
     (alarmvolume=2) & (prevdm=dispalarm) &
     disp[dvtbi]=true & disp[drate]=true & disp[dtime]=true &
     disp[detime]=false & disp[dvol]=false & disp[dalarmvol]=false  &
     phasevtbi=ready & phasetime=ready & phaserate=ready &
     phaseinfuse=ready
  tick <-> device.tick
  dispvalue = displayval[maxdigindex] + 2*displayval[2] +
              4*displayval[1] + 8*displayval[0]
  dispvalue < maxrate -> dispinfrate=dispvalue
  dispvalue >= maxrate -> dispinfrate=maxrate
  dispvalue < maxtime -> dispinftime=dispvalue
  dispvalue >= maxtime -> dispinftime=maxtime
  dispvalue < maxinfuse -> dispinfvtbi=dispvalue
  dispvalue >= maxinfuse -> dispinfvtbi=maxinfuse
  per(start) -> device.poweredon
  !device.infusingstate -> [start] effect(device.start)
  device.infusingstate -> [start] effect(device.pause)
  device.start -> start
  device.pause -> start
  device.on <-> on
  (entrymode=scalemode) <-> (displaymode=dispalarmvol)
  per(device.clearkvoflag) -> device.infusingstate & device.kvoflag & device.poweredon
 # [device.clearkvoflag] effect(tick)

  [device.resetElapsed] effect(up) | effect(down) | effect(left) |
                        effect(right) | effect(ok) | effect(clear)
  per(device.modrate(_x)) -> (displaymode=disprate) &(entrymode=dataentry)
  [device.modrate(_x)] effect(ok) | effect(start)
  per(device.maximrate) -> (displaymode=disprate) & (entrymode=dataentry)
  [device.maximrate] effect(ok) | effect(start)
  per(device.maxvtbi) -> (displaymode=dispvtbi) & (entrymode=dataentry)
  [device.maxvtbi] effect(ok) | effect(start)
  per(device.modvtbi(_x)) -> (displaymode=dispvtbi) & (entrymode=dataentry)
  [device.modvtbi(_x)] effect(ok) | effect(start)
  per(device.maxitime) -> (displaymode=disptime) & (entrymode=dataentry)
  [device.maxitime] effect(ok) | effect(start)
  per(device.modtime(_x)) -> (displaymode=disptime) & (entrymode=dataentry)
  [device.modtime(_x)] effect(ok) | effect(start)

  # per(tick) -> entrymode != confirmmode
  !device.infusingstate & (device.elapse>=timeout) ->
       [tick] entrymode'=confirmmode & displaymode'=dispalarm &
              prevdm'=displaymode &
              keep(entry, prevdm,
                   dispvalue, target, menucursor, alarmvolume, disp,
                   dispscale, phaserate, phasetime, phasevtbi, phaseinfuse)
  device.infusingstate & device.kvoflag
             ->
       [tick] entrymode'=confirmmode &
              displaymode'=dispalarm &
              prevdm'=displaymode &
              keep(entry,
                   dispvalue, target, menucursor, alarmvolume, disp,
                   dispscale, phaserate, phasetime, phasevtbi, phaseinfuse)

  !device.infusingstate & (device.elapse<timeout) ->
       [tick]
              keep(entrymode, prevdm,
                   displaymode, entry,
                   dispvalue, target, menucursor, alarmvolume, disp,
                   dispscale, phaserate, phasetime, phasevtbi, phaseinfuse)

  device.infusingstate & !device.kvoflag & (device.time <= timetoempty) -> [tick]
                entrymode'=confirmmode & prevdm'=displaymode &
                displaymode'=dispalarm &
                keep(entry,
                     dispvalue, target, menucursor, alarmvolume, disp,
                     dispscale, phaserate, phasetime, phasevtbi, phaseinfuse)

  device.infusingstate & !device.kvoflag & (device.time > timetoempty) -> [tick]
                keep(entry, entrymode, prevdm, displaymode,
                     dispvalue, target, menucursor, alarmvolume, disp,
                     dispscale, phaserate, phasetime, phasevtbi, phaseinfuse)


  !device.poweredon ->
      [on] displaymode'=mainmenu &
           target'= tvtbi &
           menucursor'=drate &
           entrymode'=nullmode &
           prevdm'=dispalarm &
           disp[dvtbi]' & disp[drate]' & disp[dtime]' &
           !disp[detime]' & disp[dvol]' & !disp[dalarmvol]' &
           keep(alarmvolume, target, phaserate, phasetime, phasevtbi, phaseinfuse)
  device.poweredon ->
      [on] displaymode'=dispblank &
           entrymode'=nullmode &
           !disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
           !disp[detime]' & !disp[dvol]' & !disp[dalarmvol]' &
           keep(alarmvolume, target, phaserate, phasetime, phasevtbi, phaseinfuse)
  per(up) -> ((entrymode=dataentry &
             displaymode in {dispvtbi, disprate, disptime}) |
             (displaymode=mainmenu)) & !device.infusingstate & device.poweredon
  entrymode=dataentry -> [up]
        (entry=0 ->  ( (dispvalue+8 >= maxdispvalue
                              -> dispvalue'=maxdispvalue) &
                       (dispvalue+8 < maxdispvalue
                              -> dispvalue'=dispvalue+8)
                      )
         ) &
        (entry=1 ->  ( (dispvalue+4 >= maxdispvalue
                              -> dispvalue'=maxdispvalue) &
                       (dispvalue+4 < maxdispvalue
                              -> dispvalue'=dispvalue+4)
                      )
         ) &
        (entry=2 ->  ( (dispvalue+2 >= maxdispvalue
                              -> dispvalue'=maxdispvalue) &
                       (dispvalue+2 < maxdispvalue
                              -> dispvalue'=dispvalue+2)
                      )
         ) &
        (entry=3 ->  ( (dispvalue+1 >= maxdispvalue
                              -> dispvalue'=maxdispvalue) &
                       (dispvalue+1 < maxdispvalue
                              -> dispvalue'=dispvalue+1)
                      )
         ) &
               effect(device.resetElapsed) &
               keep(displaymode, entry, alarmvolume,
                    target, menucursor, entrymode, prevdm,
                    disp, phaserate, phasetime, phasevtbi, phaseinfuse)

  (displaymode = mainmenu) ->
         [up] ((menucursor=0) -> menucursor'=0) &
              ((menucursor!=0) -> menucursor' = (menucursor - 1)) &
              ((menucursor=doptions)-> (disp[drate]' & disp[dvtbi]' &
                                      disp[dtime]' & !disp[dvol]' &
                                      !disp[dalarmvol]' & !disp[detime]')) &
              ((menucursor!=doptions)->keep(disp)) &
              effect(device.resetElapsed) &
              keep(displaymode, entrymode,
                   target, prevdm,
                   alarmvolume, phaserate, phasetime, phasevtbi, phaseinfuse)

  per(down) ->  ((entrymode=dataentry & displaymode in
                   {dispvtbi, disprate, disptime}) |
               (displaymode=mainmenu)) & !device.infusingstate &
                device.poweredon
  entrymode=dataentry -> [down]
        (entry=0 ->  ( (dispvalue-8 <= 0
                              -> dispvalue'=0) &
                       (dispvalue-8 > 0
                              -> dispvalue'=dispvalue-8)
                      )
         ) &
        (entry=1 ->  ( (dispvalue-4 <= 0
                              -> dispvalue'=0) &
                       (dispvalue-4 > 0
                              -> dispvalue'=dispvalue-4)
                      )
         ) &
        (entry=2 ->  ( (dispvalue-2 <= 0
                              -> dispvalue'=0) &
                       (dispvalue-2 > 0
                              -> dispvalue'=dispvalue-2)
                      )
         ) &
        (entry=3 ->  ( (dispvalue = 0
                              -> dispvalue'=0) &
                       (dispvalue > 0
                              -> dispvalue'=dispvalue-1)
                      )
         ) &
               effect(device.resetElapsed) &
               keep(displaymode, entrymode, entry, alarmvolume,
                    target, menucursor, prevdm,
                    disp, phaserate, phasetime, phasevtbi, phaseinfuse)

  (displaymode = mainmenu) ->
     [down] ((menucursor=mcmax) -> menucursor'=mcmax) &
            ((menucursor!=mcmax) -> (menucursor' = (menucursor+1))) &
            ((menucursor=dtime) -> (!disp[drate]' & !disp[dvtbi]' &
                                      !disp[dtime]' & !disp[dvol]' &
                                      !disp[dalarmvol]' & !disp[detime]')) &
            ((menucursor!=dtime) -> keep(disp)) &
            effect(device.resetElapsed) &
            keep(displaymode, entrymode, prevdm,
                 target, alarmvolume,
                 phaserate, phasetime, phasevtbi, phaseinfuse)

  per(left) -> ( entrymode in {dataentry, scalemode} |
               ((displaymode=optionsmenu) |
                ((displaymode=mainmenu) &
                   ((menucursor = dvtbi) | (menucursor > dtime) |
                   ((menucursor = drate) & (device.vtbi != 0)) |
                   ((menucursor = dtime) & (device.vtbi != 0))
                )  &  entrymode=nullmode
               )
               ) & !device.infusingstate & device.poweredon )

  (displaymode = mainmenu) & (menucursor=drate) &
    (device.vtbi != 0) ->
             [left] entrymode'=dataentry & (displaymode'=disprate) &
                    entry'=maxdigindex &
                    dispvalue'=device.infusionrate &
                    effect(device.resetElapsed) &
                    !disp[dvtbi]' & disp[drate]' & !disp[dtime]' &
                    !disp[detime]' & !disp[dvol]' &
                    !disp[dalarmvol]' &
                    keep(target, alarmvolume, prevdm, phaserate, phasetime, phasevtbi, phaseinfuse)
  (displaymode = mainmenu) & (menucursor=dvtbi) ->
             [left] entrymode'=dataentry & (displaymode'=dispvtbi) &
                    dispvalue'=device.vtbi &
                    effect(device.resetElapsed) &
                    disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
                    !disp[detime]' & !disp[dvol]' &
                    !disp[dalarmvol]' &
                    entry'=maxdigindex &
                    keep(target, alarmvolume, prevdm,
                         phaserate, phasetime, phasevtbi, phaseinfuse)
  (displaymode = mainmenu) & (menucursor=dtime) &
    (device.vtbi != 0) ->
             [left] entrymode'=dataentry & (displaymode'=disptime) &
                    dispvalue'=device.time &
                    entry'=maxdigindex &
                    effect(device.resetElapsed) &
                    !disp[dvtbi]' & !disp[drate]' & disp[dtime]' &
                    !disp[detime]' & !disp[dvol]' &
                    !disp[dalarmvol]' &
                    keep(target, alarmvolume, prevdm,
                         phaserate, phasetime, phasevtbi, phaseinfuse)
   # this is simplified - need to check the simulation
  (displaymode = mainmenu) & (menucursor=doptions) ->
             [left] (displaymode'=optionsmenu) &
                     effect(device.resetElapsed) &
                     !disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
                     !disp[detime]' & !disp[dvol]' &
                     disp[dalarmvol]' &
                       keep(target, alarmvolume, entrymode, prevdm,
                           phaserate, phasetime, phasevtbi, phaseinfuse)
  (displaymode = mainmenu) & (menucursor=dstatus) ->
             [left] (displaymode'=statusmenu) &
                    prevdm'=mainmenu &
                    effect(device.resetElapsed) &
                    !disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
                    disp[detime]' & disp[dvol]' &
                    !disp[dalarmvol]' &
                    keep(target, alarmvolume, prevdm,
                         entrymode,  phaserate, phasetime, phasevtbi, phaseinfuse)
 ### note that there is an assumption that there is only one item in the options menu. This
 ### will need changing as the model develops
  (displaymode = optionsmenu) ->
             [left] displaymode'= dispalarmvol &
                    entrymode'=scalemode &
                    dispscale'=alarmvolume &
                    effect(device.resetElapsed) &
                    !disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
                    !disp[detime]' & !disp[dvol]' &
                    disp[dalarmvol]' &
                    keep(target, alarmvolume, prevdm,
                         phaserate, phasetime, phasevtbi, phaseinfuse)
  displaymode in {disprate, dispvtbi, disptime} -> [left]
                   ((entry>0) -> entry'=(entry - 1)) &
                   ((entry=0) -> keep(entry)) &
                   effect(device.resetElapsed) &
                   keep(displaymode, dispvalue, displayval,
                        target, disp, entrymode, prevdm,
                        alarmvolume,  phaserate, phasetime, phasevtbi, phaseinfuse)
  displaymode=dispalarmvol -> [left]
                   ((dispscale<maxscale) ->
                           dispscale'=(dispscale+1)) &
                   ((dispscale=maxscale) ->
                           keep(dispscale)) &
                   effect(device.resetElapsed) &
                   keep(displaymode, entrymode,
                        target, disp, prevdm,
                        alarmvolume,  phaserate, phasetime, phasevtbi, phaseinfuse)

  per(right) -> (entrymode in {dataentry, scalemode}) &
                 !device.infusingstate & device.poweredon

  entrymode=dataentry -> [right]
                  (entry<maxdigindex -> (entry'=(entry+1))) &
                  (entry=maxdigindex -> keep(entry)) &
                  effect(device.resetElapsed) &
                  keep(displaymode, dispvalue, displayval,
                       target, disp, entrymode, prevdm,
                       alarmvolume, phaserate, phasetime, phasevtbi, phaseinfuse)
  entrymode=scalemode -> [right]
                   ((dispscale>0) ->
                           dispscale'=(dispscale - 1)) &
                   ((dispscale=0) ->
                           keep(dispscale)) &
                   effect(device.resetElapsed) &
                   keep(displaymode, entrymode,
                        target, disp, prevdm,
                        alarmvolume,  phaserate, phasetime, phasevtbi, phaseinfuse)

  per(ok) ->  (displaymode in {dispalarmvol, optionsmenu, disprate, dispvtbi, disptime, dispalarm})
               |
               (
                 (displaymode=mainmenu) &
                    (
                      (menucursor = dvtbi) |
                      (menucursor > dtime) |
                      ((menucursor = drate) & (device.vtbi != 0)) |
                      ((menucursor = dtime) & (device.vtbi != 0))
                     )
                )


  (displaymode = mainmenu) & (menucursor=drate) &
    (device.vtbi != 0) ->
             [ok] (entrymode'=dataentry) & (displaymode'=disprate) &
                  entry'=maxdigindex &
                  !disp[dvtbi]' & disp[drate]' & !disp[dtime]' &
                  !disp[detime]' & !disp[dvol]' &
                  !disp[dalarmvol]' &
                  effect(device.resetElapsed) &
                  dispvalue'=device.infusionrate &
                     keep(target, alarmvolume, prevdm,
                         phaserate, phasetime, phasevtbi, phaseinfuse)
  (displaymode = mainmenu) & (menucursor=dvtbi) ->
             [ok] (entrymode'=dataentry) & (displaymode'=dispvtbi) &
                  dispvalue'=device.vtbi &
                  entry'=maxdigindex &
                  disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
                  !disp[detime]' & !disp[dvol]' &
                  !disp[dalarmvol]' &
                  effect(device.resetElapsed) &
                  keep(target, disp, prevdm,
                       alarmvolume, phaserate, phasetime, phasevtbi, phaseinfuse)
  (displaymode = mainmenu) & (menucursor=dtime) &
    (device.vtbi != 0) ->
               [ok] (entrymode'=dataentry) & (displaymode'=disptime) &
                    dispvalue'=device.time &
                    entry'=maxdigindex &
                    !disp[dvtbi]' & !disp[drate]' & disp[dtime]' &
                    !disp[detime]' & !disp[dvol]' &
                    !disp[dalarmvol]' &
                    effect(device.resetElapsed) &
                    keep(target, alarmvolume, prevdm,
                         phaserate, phasetime, phasevtbi, phaseinfuse)

  # this is simplified - need to check the simulation
  (displaymode = mainmenu) & (menucursor=doptions) ->
             [ok] (displaymode'=optionsmenu) &
                     effect(device.resetElapsed) &
                    !disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
                    !disp[detime]' & !disp[dvol]' &
                    disp[dalarmvol]' &
                      keep(target, entrymode, alarmvolume, prevdm,
                          phaserate, phasetime, phasevtbi, phaseinfuse)
  (displaymode = mainmenu) & (menucursor=dstatus) ->
             [ok] (displaymode'=statusmenu) & (entrymode'=confirmmode) &
                    prevdm'=mainmenu &
                    !disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
                    disp[detime]' & disp[dvol]' &
                    !disp[dalarmvol]' &
                    effect(device.resetElapsed) &
                    keep(target, alarmvolume, prevdm,
                         phaserate, phasetime, phasevtbi, phaseinfuse)
  (displaymode = optionsmenu) ->
             [ok] (displaymode'=dispalarmvol) &
                    dispscale'=alarmvolume &
                    effect(device.resetElapsed) &
                    !disp[dvtbi]' & !disp[drate]' & !disp[dtime]' &
                    !disp[detime]' & !disp[dvol]' &
                    disp[dalarmvol]' &
                      keep(target, alarmvolume, prevdm,
                           phaserate, phasetime, phasevtbi, phaseinfuse)
  (displaymode = disprate) ->
       [ok] displaymode'=mainmenu &
           (dispvalue < maxrate ->
                   effect(device.modrate(dispinfrate))) &
           (dispvalue >= maxrate -> effect(device.maximrate)) &
           menucursor'=drate &
           disp[dvtbi]' & disp[drate]' & disp[dtime]' &
           !disp[detime]' & !disp[dvol]' & !disp[dalarmvol]' &
           entrymode'=nullmode &
           keep(alarmvolume, prevdm,
                target, phaserate, phasetime, phasevtbi, phaseinfuse)

  (displaymode = dispvtbi)  ->
       [ok] displaymode'=mainmenu &
           (dispvalue>=maxinfuse -> effect(device.maxvtbi)) &
           (dispvalue<maxinfuse ->
                    effect(device.modvtbi(dispinfvtbi))) &
           menucursor'=dvtbi &
           entrymode'=nullmode &
           disp[dvtbi]' & disp[drate]' & disp[dtime]' &
           !disp[detime]' & !disp[dvol]' & !disp[dalarmvol]' &
           keep(alarmvolume, prevdm,
                target, phaserate, phasetime, phasevtbi, phaseinfuse)


  (displaymode = disptime) ->
       [ok] displaymode'=mainmenu &
            (dispvalue>=maxtime -> effect(device.maxitime)) &
            (dispvalue<maxtime ->
                  effect(device.modtime(dispinftime))) &
            entrymode'=nullmode &
            menucursor'=dtime &
            disp[dvtbi]' & disp[drate]' & disp[dtime]' &
            !disp[detime]' & !disp[dvol]' & !disp[dalarmvol]' &
            keep(alarmvolume, prevdm,
                 target, phaserate, phasetime, phasevtbi, phaseinfuse)

  (displaymode=dispalarmvol) ->
      [ok] alarmvolume'=dispscale &
           displaymode'=mainmenu &
           menucursor'=dvtbi &
           entrymode'=nullmode &
           disp[dvtbi]' & disp[drate]' & disp[dtime]' &
           !disp[detime]' & !disp[dvol]' & !disp[dalarmvol]' &
           alarmvolume'=dispscale &
           effect(device.resetElapsed) &
           keep(target, prevdm, phaserate, phasetime, phasevtbi, phaseinfuse)

  (displaymode=dispalarm) -> [ok]
            (prevdm in {mainmenu, dispinfusing, optionsmenu, statusmenu, dispblank} ->
                         entrymode'=nullmode) &
             (prevdm in {disprate, dispvtbi, disptime} -> entrymode'=dataentry) &
            (prevdm = dispalarmvol -> entrymode'=scalemode) &
             (prevdm=dispalarm -> entrymode'=confirmmode) &
            displaymode'=prevdm &
            prevdm'=dispalarm &
            effect(device.resetElapsed) &
            keep(alarmvolume,
                 target, entry,
                 menucursor, phaserate, phasetime, phasevtbi, phaseinfuse)

  per(clear) -> entrymode=dataentry & !device.infusingstate &
                device.poweredon
  entrymode=dataentry ->
         [clear] displayval[0]'=0 & displayval[1]'=0 &
                 displayval[2]'=0 &
                 displayval[maxdigindex]'=0 &
                 effect(device.resetElapsed) &
                 keep(entrymode, displaymode, prevdm,
                      entry, target, alarmvolume,
                      disp, phaserate, phasetime, phasevtbi, phaseinfuse)
  per(start) -> displaymode in {mainmenu, dispinfusing} &
               device.poweredon

  (displaymode=mainmenu) & (device.vtbi!=0) ->
      [start] displaymode'=dispinfusing &
            disp[dvtbi]' & disp[drate]' & disp[dtime]' &
            !disp[detime]' & disp[dvol]' & !disp[dalarmvol]' &
            keep(alarmvolume, target, entrymode, prevdm, phaserate, phasetime, phasevtbi, phaseinfuse)

  (displaymode=mainmenu) & (device.vtbi=0) ->
      [start] keep(displaymode, disp, alarmvolume, target, entrymode,
                   menucursor, prevdm, phaserate, phasetime, phasevtbi, phaseinfuse)


  (displaymode=dispinfusing) ->
      [start] displaymode'=mainmenu &
           menucursor'=dvtbi &
           entrymode'=nullmode &
           disp[dvtbi]' & disp[drate]' & disp[dtime]' &
           !disp[detime]' & disp[dvol]' & !disp[dalarmvol]' &
            keep(alarmvolume, target, prevdm, phaserate, phasetime, phasevtbi, phaseinfuse)
## activity description

## in case restarts
  !device.poweredon ->
   [on] phasevtbi'=ready & phaserate'=ready & phasetime'=ready &
         phaseinfuse'=ready

## invariants for the activities

##  (phasevtbi = entering) -> (disp[dvtbi] & (displaymode in {dispvtbi, mainmenu}))
##  ((phasevtbi = confirmed) & (phaseinfuse=ready)) -> mvolume = device.vtbi
##  (phasetime = entering) -> (disp[dtime] & (displaymode in {disptime, mainmenu}))
##  ((phasetime = confirmed) & (phaseinfuse=ready)) -> mtime = device.time
##  (phaserate = entering)  -> (disp[drate] & (displaymode in {disprate, mainmenu}))
##  ((phaserate = confirmed) & (phaseinfuse=ready)) -> mrate = device.infusionrate


  per(entervtbi) -> device.poweredon & (phasevtbi=ready) & (phasetime != entering) &
                    (phaserate != entering) &
                    (displaymode = dispvtbi)
  [entervtbi] phasevtbi'=entering &
              keep(displaymode, prevdm, dispvalue, dispscale, entry, entrymode, target, menucursor,
                   alarmvolume, disp, devicevtbi, phasetime, phaserate, phaseinfuse)
  per(enterrate) -> device.poweredon & (phasevtbi != entering) &
                    (phasetime != entering) & (phaserate = ready) &
                    (displaymode = disprate) & (mrate != 0)
  [enterrate] phaserate'=entering &
              keep(displaymode, prevdm, dispvalue, entrymode, dispscale, entry, target, menucursor,
                   alarmvolume, disp, devicevtbi, phasetime, phasevtbi, phaseinfuse)
  per(entertime) -> device.poweredon & (phasetime=ready) & (phasevtbi != entering) &
                   (phaserate != entering) & (displaymode = disptime) & (mtime != 0)
  [entertime] phasetime'=entering &
              keep(displaymode, prevdm, dispvalue, dispscale, entrymode, entry, target, menucursor,
                   alarmvolume, disp, devicevtbi, phasevtbi, phaserate, phaseinfuse)
  per(confirmvtbi) -> device.poweredon & phasevtbi=entering & mvolume=device.vtbi & disp[dvtbi]
  [confirmvtbi] phasevtbi'=confirmed &
              keep(displaymode, entrymode, prevdm, dispvalue, dispscale, entry, target, menucursor,
                   alarmvolume, disp, devicevtbi, phasetime, phaserate, phaseinfuse)
  per(confirmrate) -> device.poweredon & phaserate=entering & mrate=device.infusionrate &
                      mrate != 0 & disp[drate]
  [confirmrate] phaserate'=confirmed &
               keep(displaymode, entrymode, prevdm, dispvalue, dispscale, entry, target, menucursor,
                   alarmvolume, disp, devicevtbi, phasevtbi, phasetime, phaseinfuse)
  per(confirmtime) -> device.poweredon & (mtime=device.time) & (mtime != 0) &
                      (phasetime=entering) & disp[dtime]
  [confirmtime] phasetime'=confirmed &
              keep(displaymode, entrymode, prevdm, dispvalue, dispscale, entry, target, menucursor,
                   alarmvolume, disp, devicevtbi, phasevtbi, phaserate, phaseinfuse)
  per(startinfuse) -> device.poweredon & (phaseinfuse=ready) & (phasevtbi=confirmed) &
                      (mtime != 0 -> phasetime=confirmed) & (mrate != 0 -> phaserate=confirmed)
  [startinfuse] phaseinfuse'=entering &
              keep(displaymode, entrymode, prevdm, dispvalue, dispscale, entry, target, menucursor,
                   alarmvolume, disp, devicevtbi, phasevtbi, phaserate, phasetime)

 # the following depends on the value of maxdig
  per(left) ->
     ((phasevtbi = entering & entrymode=dataentry & displaymode=dispvtbi) &
          ((entry=maxdigindex -> ((mvolume-dispvalue) >= 2)) &
           (entry=2 -> ((mvolume-dispvalue) >= 4)) &
           (entry=1 -> ((mvolume-dispvalue) >= 8))
          )
     )
     |
     ((entrymode=dataentry & phasetime = entering & displaymode=disptime) &
          ((entry=maxdigindex -> ((mtime-dispvalue) >= 2)) &
           (entry=2 -> ((mtime-dispvalue) >= 4)) &
           (entry=1 -> ((mtime-dispvalue) >= 8))
          )
     )
     |
     ((entrymode=dataentry & phaserate=entering & displaymode=disprate) &
          ((entry=maxdigindex -> ((mrate-dispvalue) >= 2)) &
           (entry=2 -> ((mrate-dispvalue) >= 4)) &
           (entry=1 -> ((mrate-dispvalue) >= 8))
          )
     )
     |
     ((displaymode=mainmenu) & (menucursor=dvtbi) &
        (device.vtbi != mvolume) & (mvolume != 0) & (phasevtbi=ready)
     )
     |
     ((displaymode=mainmenu) & (menucursor=drate) &
      (device.infusionrate != mrate) & (mrate != 0) & (phaserate=ready)
     )
     |
     ((displaymode=mainmenu) & (menucursor=dtime) &
       (device.vtbi != mtime) & (mtime != 0) & (phasetime=ready)
      )
  per(right) -> (phaseinfuse!=entering &
     ( entrymode=dataentry & phasevtbi=entering & displaymode=dispvtbi ->
     ((entry=2 -> ((dispvalue - mvolume) < 2)) &
     (entry=1 -> ((dispvalue - mvolume) < 4)) &
     (entry=0 -> ((dispvalue - mvolume) < 8))
     )
     ) |
     (entrymode=dataentry & phasetime=entering & displaymode=disptime ->
     ((entry=2 -> ((dispvalue - mtime) < 2)) &
     (entry=1 -> ((dispvalue - mtime) < 4)) &
     (entry=0 -> ((dispvalue - mtime) < 8))
     )
     ) |
      (entrymode=dataentry & phaserate=entering & displaymode=disprate ->
     ((entry=2 -> ((dispvalue - mrate) < 2)) &
     (entry=1 -> ((dispvalue - mrate) < 4)) &
     (entry=0 -> ((dispvalue - mrate) < 8))
     )
     ))
  per(down) -> (phaseinfuse != entering &
     ( entrymode=dataentry ->
     ((displaymode=dispvtbi & phasevtbi=entering &
       (entry=3 -> dispvalue-mvolume < 2) &
       (entry=2 -> ((dispvalue-mvolume >= 2) & (dispvalue-mvolume < 4))) &
       (entry=1 -> ((dispvalue-mvolume >= 4) & (dispvalue-mvolume < 8)))) |
      (displaymode=disptime & phasetime=entering &
       (entry=3 -> dispvalue-mtime < 2) &
       (entry=2 -> ((dispvalue-mtime >= 2) & (dispvalue-mtime < 4))) &
       (entry=1 -> ((dispvalue-mtime >= 4) & (dispvalue-mtime < 8)))) |
      (displaymode=disprate & phaserate=entering &
       (entry=3 -> dispvalue-mrate < 2) &
       (entry=2 -> ((dispvalue-mrate >= 2) & (dispvalue-mrate < 4))) &
       (entry=1 -> ((dispvalue-mrate >= 8) & (dispvalue-mrate < 8)))))))
  per(up) -> (phaseinfuse != entering &
    (  entrymode=dataentry ->
     ((displaymode=dispvtbi & phasevtbi=entering &
       (entry=3 -> mvolume-dispvalue < 2) &
       (entry=2 -> ((mvolume-dispvalue >= 2) & (mvolume-dispvalue < 4))) &
       (entry=1 -> ((mvolume-dispvalue >= 4) & (mvolume-dispvalue < 8)))) |
      (displaymode=disptime & phasetime=entering &
       (entry=3 -> mtime-dispvalue < 2) &
       (entry=2 -> ((mtime - dispvalue >= 2) & (mtime-dispvalue < 4))) &
       (entry=1 -> ((mtime - dispvalue >= 4) & (mtime-dispvalue < 8)))) |
      (displaymode=disprate & phaserate=entering &
       (entry=3 -> mrate-dispvalue < 2) &
       (entry=2 -> ((mrate - dispvalue >= 2) & (mrate-dispvalue < 4))) &
       (entry=1 -> ((mrate - dispvalue >= 4) & (mrate-dispvalue < 8)))))))


  per(ok) -> ((displaymode=dispvtbi) & (dispinfvtbi=mvolume))
           | ((displaymode=disprate) & (dispinfrate=mrate))
           | ((displaymode=disptime) & (dispinftime=mtime))
           | ((displaymode=mainmenu) & (menucursor=dvtbi) &
             (device.vtbi != mvolume) & (mvolume != 0) & (phasevtbi=ready))
           | ((displaymode=mainmenu) & (menucursor=drate) &
             (device.infusionrate != mrate) & (mrate != 0) & (phaserate=ready))
           | ((displaymode=mainmenu) & (menucursor=dtime) &
             (device.vtbi != mtime) & (mtime != 0) & (phasetime=ready))

  per(start) -> (displaymode=mainmenu) &
                  (phaseinfuse=entering) &
                disp[dtime] & disp[drate] & disp[dvtbi]

  per(clear) -> ((phaserate=entering) & (displaymode=disprate)) |
                ((phasevtbi=entering) & (displaymode=dispvtbi)) |
                ((phasetime=entering) & (displaymode=disptime))

  [nil] true
## visibility of mode
## consistency of naming and purpose of functions
## consistent behaviour of data entry keys
 test
  AG(displaymode=dispvtbi & device.vtbi=0 & dispinfvtbi=0 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=0 & AX(ok -> device.vtbi=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=1 & dispinfvtbi=1 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=1 & AX(ok -> device.vtbi=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=2 & dispinfvtbi=2 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=2 & AX(ok -> device.vtbi=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=3 & dispinfvtbi=3 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=3 & AX(ok -> device.vtbi=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=4 & dispinfvtbi=4 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=4 & AX(ok -> device.vtbi=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=5 & dispinfvtbi=5 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=5 & AX(ok -> device.vtbi=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=6 & dispinfvtbi=6 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=6 & AX(ok -> device.vtbi=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=0 & dispinfvtbi=0 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=0 & AX(!ok -> device.vtbi=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=1 & dispinfvtbi=1 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=1 & AX(!ok -> device.vtbi=1)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=2 & dispinfvtbi=2 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=2 & AX(!ok -> device.vtbi=2)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=3 & dispinfvtbi=3 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=3 & AX(!ok -> device.vtbi=3)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=4 & dispinfvtbi=4 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=4 & AX(!ok -> device.vtbi=4)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=5 & dispinfvtbi=5 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=5 & AX(!ok -> device.vtbi=5)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=6 & dispinfvtbi=6 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=6 & AX(!ok -> device.vtbi=6)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=0 & dispinfvtbi=0 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=0 & AX(ok -> device.vtbi!=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=1 & dispinfvtbi=1 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=1 & AX(ok -> device.vtbi!=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=2 & dispinfvtbi=2 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=2 & AX(ok -> device.vtbi!=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=3 & dispinfvtbi=3 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=3 & AX(ok -> device.vtbi!=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=4 & dispinfvtbi=4 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=4 & AX(ok -> device.vtbi!=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=5 & dispinfvtbi=5 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=5 & AX(ok -> device.vtbi!=0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=6 & dispinfvtbi=6 -> AX(clear -> (dispinfvtbi=0 & device.vtbi=6 & AX(ok -> device.vtbi!=0)))) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & device.elapse >= timeout -> AX(tick -> displaymode = dispalarm)) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & device.elapse >= timeout & displaymode=mainmenu -> AX(tick -> displaymode = dispalarm & AX(ok -> displaymode=mainmenu))) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=0 -> A[(dispinfrate != 0 & device.infusionrate = 0) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=0 -> A[(dispinfrate != 1 & device.infusionrate = 0) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=0 -> A[(dispinfrate != 2 & device.infusionrate = 0) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=0 -> A[(dispinfrate != 3 & device.infusionrate = 0) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=0 -> A[(dispinfrate != 4 & device.infusionrate = 0) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=0 -> A[(dispinfrate != 5 & device.infusionrate = 0) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=0 -> A[(dispinfrate != 6 & device.infusionrate = 0) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=0 -> A[(dispinfrate != 7 & device.infusionrate = 0) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=1 -> A[(dispinfrate != 0 & device.infusionrate = 1) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=1 -> A[(dispinfrate != 1 & device.infusionrate = 1) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=1 -> A[(dispinfrate != 2 & device.infusionrate = 1) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=1 -> A[(dispinfrate != 3 & device.infusionrate = 1) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=1 -> A[(dispinfrate != 4 & device.infusionrate = 1) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=1 -> A[(dispinfrate != 5 & device.infusionrate = 1) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=1 -> A[(dispinfrate != 6 & device.infusionrate = 1) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=1 -> A[(dispinfrate != 7 & device.infusionrate = 1) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=2 -> A[(dispinfrate != 0 & device.infusionrate = 2) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=2 -> A[(dispinfrate != 1 & device.infusionrate = 2) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=2 -> A[(dispinfrate != 2 & device.infusionrate = 2) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=2 -> A[(dispinfrate != 3 & device.infusionrate = 2) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=2 -> A[(dispinfrate != 4 & device.infusionrate = 2) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=2 -> A[(dispinfrate != 5 & device.infusionrate = 2) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=2 -> A[(dispinfrate != 6 & device.infusionrate = 2) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=2 -> A[(dispinfrate != 7 & device.infusionrate = 2) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=3 -> A[(dispinfrate != 0 & device.infusionrate = 3) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=3 -> A[(dispinfrate != 1 & device.infusionrate = 3) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=3 -> A[(dispinfrate != 2 & device.infusionrate = 3) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=3 -> A[(dispinfrate != 3 & device.infusionrate = 3) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=3 -> A[(dispinfrate != 4 & device.infusionrate = 3) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=3 -> A[(dispinfrate != 5 & device.infusionrate = 3) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=3 -> A[(dispinfrate != 6 & device.infusionrate = 3) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=3 -> A[(dispinfrate != 7 & device.infusionrate = 3) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=4 -> A[(dispinfrate != 0 & device.infusionrate = 4) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=4 -> A[(dispinfrate != 1 & device.infusionrate = 4) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=4 -> A[(dispinfrate != 2 & device.infusionrate = 4) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=4 -> A[(dispinfrate != 3 & device.infusionrate = 4) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=4 -> A[(dispinfrate != 4 & device.infusionrate = 4) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=4 -> A[(dispinfrate != 5 & device.infusionrate = 4) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=4 -> A[(dispinfrate != 6 & device.infusionrate = 4) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=4 -> A[(dispinfrate != 7 & device.infusionrate = 4) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=5 -> A[(dispinfrate != 0 & device.infusionrate = 5) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=5 -> A[(dispinfrate != 1 & device.infusionrate = 5) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=5 -> A[(dispinfrate != 2 & device.infusionrate = 5) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=5 -> A[(dispinfrate != 3 & device.infusionrate = 5) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=5 -> A[(dispinfrate != 4 & device.infusionrate = 5) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=5 -> A[(dispinfrate != 5 & device.infusionrate = 5) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=5 -> A[(dispinfrate != 6 & device.infusionrate = 5) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=5 -> A[(dispinfrate != 7 & device.infusionrate = 5) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=6 -> A[(dispinfrate != 0 & device.infusionrate = 6) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=6 -> A[(dispinfrate != 1 & device.infusionrate = 6) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=6 -> A[(dispinfrate != 2 & device.infusionrate = 6) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=6 -> A[(dispinfrate != 3 & device.infusionrate = 6) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=6 -> A[(dispinfrate != 4 & device.infusionrate = 6) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=6 -> A[(dispinfrate != 5 & device.infusionrate = 6) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=6 -> A[(dispinfrate != 6 & device.infusionrate = 6) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=6 -> A[(dispinfrate != 7 & device.infusionrate = 6) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=7 -> A[(dispinfrate != 0 & device.infusionrate = 7) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=7 -> A[(dispinfrate != 1 & device.infusionrate = 7) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=7 -> A[(dispinfrate != 2 & device.infusionrate = 7) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=7 -> A[(dispinfrate != 3 & device.infusionrate = 7) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=7 -> A[(dispinfrate != 4 & device.infusionrate = 7) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=7 -> A[(dispinfrate != 5 & device.infusionrate = 7) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=7 -> A[(dispinfrate != 6 & device.infusionrate = 7) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.poweredon & displaymode=disprate & entrymode=dataentry & device.infusionrate=7 -> A[(dispinfrate != 7 & device.infusionrate = 7) U ok]) #Not Verified
 test
  AG(!device.infusingstate & device.elapse >= timeout -> AX(tick -> (displaymode = dispalarm))) #Not Verified
 test
  emode = {dataentry )-> AX(tick -> (displaymode = dispalarm & AX(ok -> displaymode = dispblank #Not Verified
 test
  emode = {dataentry)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=disprate ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = disprate)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=dispvtbi ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = dispvtbi)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=disptime ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = disptime)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=mainmenu ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = mainmenu)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=dispalarm ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = dispalarm)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=dispalarmvol ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = dispalarmvol)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=optionsmenu ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = optionsmenu)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=statusmenu ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = statusmenu)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=confirmmode ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = confirmmode)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=scalemode ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = scalemode)))) #Not Verified
 test
  AG(((!device.infusingstate & device.poweredon) & (device.elapse >= timeout) & (displaymode=nullmode ))-> AX(tick -> ((displaymode = dispalarm) & AX(ok -> displaymode = nullmode)))) #Not Verified
 test
  AG((device.infusionrate = 0) & (dispinfrate = 0) -> AX(start -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (dispinfrate = 0) -> AX(on -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (dispinfrate = 0) -> AX(up -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (dispinfrate = 0) -> AX(left -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (dispinfrate = 0) -> AX(right -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (dispinfrate = 0) -> AX(ok -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (dispinfrate = 0) -> AX(clear -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (dispinfrate = 0) -> AX(tick -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 1) & (dispinfrate = 1) -> AX(start -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (dispinfrate = 1) -> AX(on -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (dispinfrate = 1) -> AX(up -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (dispinfrate = 1) -> AX(left -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (dispinfrate = 1) -> AX(right -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (dispinfrate = 1) -> AX(ok -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (dispinfrate = 1) -> AX(clear -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (dispinfrate = 1) -> AX(tick -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 2) & (dispinfrate = 2) -> AX(start -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (dispinfrate = 2) -> AX(on -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (dispinfrate = 2) -> AX(up -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (dispinfrate = 2) -> AX(left -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (dispinfrate = 2) -> AX(right -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (dispinfrate = 2) -> AX(ok -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (dispinfrate = 2) -> AX(clear -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (dispinfrate = 2) -> AX(tick -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 3) & (dispinfrate = 3) -> AX(start -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (dispinfrate = 3) -> AX(on -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (dispinfrate = 3) -> AX(up -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (dispinfrate = 3) -> AX(left -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (dispinfrate = 3) -> AX(right -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (dispinfrate = 3) -> AX(ok -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (dispinfrate = 3) -> AX(clear -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (dispinfrate = 3) -> AX(tick -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 4) & (dispinfrate = 4) -> AX(start -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (dispinfrate = 4) -> AX(on -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (dispinfrate = 4) -> AX(up -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (dispinfrate = 4) -> AX(left -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (dispinfrate = 4) -> AX(right -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (dispinfrate = 4) -> AX(ok -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (dispinfrate = 4) -> AX(clear -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (dispinfrate = 4) -> AX(tick -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 5) & (dispinfrate = 5) -> AX(start -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (dispinfrate = 5) -> AX(on -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (dispinfrate = 5) -> AX(up -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (dispinfrate = 5) -> AX(left -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (dispinfrate = 5) -> AX(right -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (dispinfrate = 5) -> AX(ok -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (dispinfrate = 5) -> AX(clear -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (dispinfrate = 5) -> AX(tick -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 6) & (dispinfrate = 6) -> AX(start -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (dispinfrate = 6) -> AX(on -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (dispinfrate = 6) -> AX(up -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (dispinfrate = 6) -> AX(left -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (dispinfrate = 6) -> AX(right -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (dispinfrate = 6) -> AX(ok -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (dispinfrate = 6) -> AX(clear -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (dispinfrate = 6) -> AX(tick -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 7) & (dispinfrate = 7) -> AX(start -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (dispinfrate = 7) -> AX(on -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (dispinfrate = 7) -> AX(up -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (dispinfrate = 7) -> AX(left -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (dispinfrate = 7) -> AX(right -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (dispinfrate = 7) -> AX(ok -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (dispinfrate = 7) -> AX(clear -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (dispinfrate = 7) -> AX(tick -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 0) & (displaymode=mainmenu) -> AX(start -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (displaymode=mainmenu) -> AX(on -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (displaymode=mainmenu) -> AX(up -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (displaymode=mainmenu) -> AX(left -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (displaymode=mainmenu) -> AX(right -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (displaymode=mainmenu) -> AX(ok -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (displaymode=mainmenu) -> AX(clear -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 0) & (displaymode=mainmenu) -> AX(tick -> device.infusionrate=0)) #Not Verified
 test
  AG((device.infusionrate = 1) & (displaymode=mainmenu) -> AX(start -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (displaymode=mainmenu) -> AX(on -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (displaymode=mainmenu) -> AX(up -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (displaymode=mainmenu) -> AX(left -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (displaymode=mainmenu) -> AX(right -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (displaymode=mainmenu) -> AX(ok -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (displaymode=mainmenu) -> AX(clear -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 1) & (displaymode=mainmenu) -> AX(tick -> device.infusionrate=1)) #Not Verified
 test
  AG((device.infusionrate = 2) & (displaymode=mainmenu) -> AX(start -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (displaymode=mainmenu) -> AX(on -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (displaymode=mainmenu) -> AX(up -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (displaymode=mainmenu) -> AX(left -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (displaymode=mainmenu) -> AX(right -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (displaymode=mainmenu) -> AX(ok -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (displaymode=mainmenu) -> AX(clear -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 2) & (displaymode=mainmenu) -> AX(tick -> device.infusionrate=2)) #Not Verified
 test
  AG((device.infusionrate = 3) & (displaymode=mainmenu) -> AX(start -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (displaymode=mainmenu) -> AX(on -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (displaymode=mainmenu) -> AX(up -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (displaymode=mainmenu) -> AX(left -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (displaymode=mainmenu) -> AX(right -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (displaymode=mainmenu) -> AX(ok -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (displaymode=mainmenu) -> AX(clear -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 3) & (displaymode=mainmenu) -> AX(tick -> device.infusionrate=3)) #Not Verified
 test
  AG((device.infusionrate = 4) & (displaymode=mainmenu) -> AX(start -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (displaymode=mainmenu) -> AX(on -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (displaymode=mainmenu) -> AX(up -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (displaymode=mainmenu) -> AX(left -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (displaymode=mainmenu) -> AX(right -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (displaymode=mainmenu) -> AX(ok -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (displaymode=mainmenu) -> AX(clear -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 4) & (displaymode=mainmenu) -> AX(tick -> device.infusionrate=4)) #Not Verified
 test
  AG((device.infusionrate = 5) & (displaymode=mainmenu) -> AX(start -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (displaymode=mainmenu) -> AX(on -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (displaymode=mainmenu) -> AX(up -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (displaymode=mainmenu) -> AX(left -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (displaymode=mainmenu) -> AX(right -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (displaymode=mainmenu) -> AX(ok -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (displaymode=mainmenu) -> AX(clear -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 5) & (displaymode=mainmenu) -> AX(tick -> device.infusionrate=5)) #Not Verified
 test
  AG((device.infusionrate = 6) & (displaymode=mainmenu) -> AX(start -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (displaymode=mainmenu) -> AX(on -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (displaymode=mainmenu) -> AX(up -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (displaymode=mainmenu) -> AX(left -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (displaymode=mainmenu) -> AX(right -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (displaymode=mainmenu) -> AX(ok -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (displaymode=mainmenu) -> AX(clear -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 6) & (displaymode=mainmenu) -> AX(tick -> device.infusionrate=6)) #Not Verified
 test
  AG((device.infusionrate = 7) & (displaymode=mainmenu) -> AX(start -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (displaymode=mainmenu) -> AX(on -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (displaymode=mainmenu) -> AX(up -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (displaymode=mainmenu) -> AX(left -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (displaymode=mainmenu) -> AX(right -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (displaymode=mainmenu) -> AX(ok -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (displaymode=mainmenu) -> AX(clear -> device.infusionrate=7)) #Not Verified
 test
  AG((device.infusionrate = 7) & (displaymode=mainmenu) -> AX(tick -> device.infusionrate=7)) #Not Verified
 test
  AG((device.vtbi = 0) & (displaymode=mainmenu) -> AX(start -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (displaymode=mainmenu) -> AX(on -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (displaymode=mainmenu) -> AX(up -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (displaymode=mainmenu) -> AX(left -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (displaymode=mainmenu) -> AX(right -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (displaymode=mainmenu) -> AX(ok -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (displaymode=mainmenu) -> AX(clear -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (displaymode=mainmenu) -> AX(tick -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 1) & (displaymode=mainmenu) -> AX(start -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (displaymode=mainmenu) -> AX(on -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (displaymode=mainmenu) -> AX(up -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (displaymode=mainmenu) -> AX(left -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (displaymode=mainmenu) -> AX(right -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (displaymode=mainmenu) -> AX(ok -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (displaymode=mainmenu) -> AX(clear -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (displaymode=mainmenu) -> AX(tick -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 2) & (displaymode=mainmenu) -> AX(start -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (displaymode=mainmenu) -> AX(on -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (displaymode=mainmenu) -> AX(up -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (displaymode=mainmenu) -> AX(left -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (displaymode=mainmenu) -> AX(right -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (displaymode=mainmenu) -> AX(ok -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (displaymode=mainmenu) -> AX(clear -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (displaymode=mainmenu) -> AX(tick -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 3) & (displaymode=mainmenu) -> AX(start -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (displaymode=mainmenu) -> AX(on -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (displaymode=mainmenu) -> AX(up -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (displaymode=mainmenu) -> AX(left -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (displaymode=mainmenu) -> AX(right -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (displaymode=mainmenu) -> AX(ok -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (displaymode=mainmenu) -> AX(clear -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (displaymode=mainmenu) -> AX(tick -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 4) & (displaymode=mainmenu) -> AX(start -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (displaymode=mainmenu) -> AX(on -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (displaymode=mainmenu) -> AX(up -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (displaymode=mainmenu) -> AX(left -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (displaymode=mainmenu) -> AX(right -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (displaymode=mainmenu) -> AX(ok -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (displaymode=mainmenu) -> AX(clear -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (displaymode=mainmenu) -> AX(tick -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 5) & (displaymode=mainmenu) -> AX(start -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (displaymode=mainmenu) -> AX(on -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (displaymode=mainmenu) -> AX(up -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (displaymode=mainmenu) -> AX(left -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (displaymode=mainmenu) -> AX(right -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (displaymode=mainmenu) -> AX(ok -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (displaymode=mainmenu) -> AX(clear -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (displaymode=mainmenu) -> AX(tick -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 6) & (displaymode=mainmenu) -> AX(start -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (displaymode=mainmenu) -> AX(on -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (displaymode=mainmenu) -> AX(up -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (displaymode=mainmenu) -> AX(left -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (displaymode=mainmenu) -> AX(right -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (displaymode=mainmenu) -> AX(ok -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (displaymode=mainmenu) -> AX(clear -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (displaymode=mainmenu) -> AX(tick -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 7) & (displaymode=mainmenu) -> AX(start -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (displaymode=mainmenu) -> AX(on -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (displaymode=mainmenu) -> AX(up -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (displaymode=mainmenu) -> AX(left -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (displaymode=mainmenu) -> AX(right -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (displaymode=mainmenu) -> AX(ok -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (displaymode=mainmenu) -> AX(clear -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (displaymode=mainmenu) -> AX(tick -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 0) & (dispinfvtbi=0) -> AX(start -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (dispinfvtbi=0) -> AX(on -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (dispinfvtbi=0) -> AX(up -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (dispinfvtbi=0) -> AX(left -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (dispinfvtbi=0) -> AX(right -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (dispinfvtbi=0) -> AX(ok -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (dispinfvtbi=0) -> AX(clear -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 0) & (dispinfvtbi=0) -> AX(tick -> device.vtbi=0)) #Not Verified
 test
  AG((device.vtbi = 1) & (dispinfvtbi=1) -> AX(start -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (dispinfvtbi=1) -> AX(on -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (dispinfvtbi=1) -> AX(up -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (dispinfvtbi=1) -> AX(left -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (dispinfvtbi=1) -> AX(right -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (dispinfvtbi=1) -> AX(ok -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (dispinfvtbi=1) -> AX(clear -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 1) & (dispinfvtbi=1) -> AX(tick -> device.vtbi=1)) #Not Verified
 test
  AG((device.vtbi = 2) & (dispinfvtbi=2) -> AX(start -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (dispinfvtbi=2) -> AX(on -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (dispinfvtbi=2) -> AX(up -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (dispinfvtbi=2) -> AX(left -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (dispinfvtbi=2) -> AX(right -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (dispinfvtbi=2) -> AX(ok -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (dispinfvtbi=2) -> AX(clear -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 2) & (dispinfvtbi=2) -> AX(tick -> device.vtbi=2)) #Not Verified
 test
  AG((device.vtbi = 3) & (dispinfvtbi=3) -> AX(start -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (dispinfvtbi=3) -> AX(on -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (dispinfvtbi=3) -> AX(up -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (dispinfvtbi=3) -> AX(left -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (dispinfvtbi=3) -> AX(right -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (dispinfvtbi=3) -> AX(ok -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (dispinfvtbi=3) -> AX(clear -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 3) & (dispinfvtbi=3) -> AX(tick -> device.vtbi=3)) #Not Verified
 test
  AG((device.vtbi = 4) & (dispinfvtbi=4) -> AX(start -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (dispinfvtbi=4) -> AX(on -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (dispinfvtbi=4) -> AX(up -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (dispinfvtbi=4) -> AX(left -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (dispinfvtbi=4) -> AX(right -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (dispinfvtbi=4) -> AX(ok -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (dispinfvtbi=4) -> AX(clear -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 4) & (dispinfvtbi=4) -> AX(tick -> device.vtbi=4)) #Not Verified
 test
  AG((device.vtbi = 5) & (dispinfvtbi=5) -> AX(start -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (dispinfvtbi=5) -> AX(on -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (dispinfvtbi=5) -> AX(up -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (dispinfvtbi=5) -> AX(left -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (dispinfvtbi=5) -> AX(right -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (dispinfvtbi=5) -> AX(ok -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (dispinfvtbi=5) -> AX(clear -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 5) & (dispinfvtbi=5) -> AX(tick -> device.vtbi=5)) #Not Verified
 test
  AG((device.vtbi = 6) & (dispinfvtbi=6) -> AX(start -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (dispinfvtbi=6) -> AX(on -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (dispinfvtbi=6) -> AX(up -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (dispinfvtbi=6) -> AX(left -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (dispinfvtbi=6) -> AX(right -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (dispinfvtbi=6) -> AX(ok -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (dispinfvtbi=6) -> AX(clear -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 6) & (dispinfvtbi=6) -> AX(tick -> device.vtbi=6)) #Not Verified
 test
  AG((device.vtbi = 7) & (dispinfvtbi=7) -> AX(start -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (dispinfvtbi=7) -> AX(on -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (dispinfvtbi=7) -> AX(up -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (dispinfvtbi=7) -> AX(left -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (dispinfvtbi=7) -> AX(right -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (dispinfvtbi=7) -> AX(ok -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (dispinfvtbi=7) -> AX(clear -> device.vtbi=7)) #Not Verified
 test
  AG((device.vtbi = 7) & (dispinfvtbi=7) -> AX(tick -> device.vtbi=7)) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=0 & dispinfvtbi=0 -> AX(clear -> (dispinfvtbi=0 & device.vtbi = 0 & AX(!ok -> device.vtbi = 0)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=1 & dispinfvtbi=1 -> AX(clear -> (dispinfvtbi=0 & device.vtbi = 1 & AX(!ok -> device.vtbi = 1)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=2 & dispinfvtbi=2 -> AX(clear -> (dispinfvtbi=0 & device.vtbi = 2 & AX(!ok -> device.vtbi = 2)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=3 & dispinfvtbi=3 -> AX(clear -> (dispinfvtbi=0 & device.vtbi = 3 & AX(!ok -> device.vtbi = 3)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=4 & dispinfvtbi=4 -> AX(clear -> (dispinfvtbi=0 & device.vtbi = 4 & AX(!ok -> device.vtbi = 4)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=5 & dispinfvtbi=5 -> AX(clear -> (dispinfvtbi=0 & device.vtbi = 5 & AX(!ok -> device.vtbi = 5)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=6 & dispinfvtbi=6 -> AX(clear -> (dispinfvtbi=0 & device.vtbi = 6 & AX(!ok -> device.vtbi = 6)))) #Not Verified
 test
  AG(displaymode=dispvtbi & device.vtbi=7 & dispinfvtbi=7 -> AX(clear -> (dispinfvtbi=0 & device.vtbi = 7 & AX(!ok -> device.vtbi = 7)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=0 & dispinfrate=0 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 0 & AX(ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=1 & dispinfrate=1 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 1 & AX(ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=2 & dispinfrate=2 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 2 & AX(ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=3 & dispinfrate=3 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 3 & AX(ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=4 & dispinfrate=4 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 4 & AX(ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=5 & dispinfrate=5 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 5 & AX(ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=6 & dispinfrate=6 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 6 & AX(ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=7 & dispinfrate=7 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 7 & AX(ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=0 & dispinfrate=0 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 0 & AX(!ok -> device.infusionrate = 0)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=1 & dispinfrate=1 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 1 & AX(!ok -> device.infusionrate = 1)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=2 & dispinfrate=2 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 2 & AX(!ok -> device.infusionrate = 2)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=3 & dispinfrate=3 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 3 & AX(!ok -> device.infusionrate = 3)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=4 & dispinfrate=4 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 4 & AX(!ok -> device.infusionrate = 4)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=5 & dispinfrate=5 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 5 & AX(!ok -> device.infusionrate = 5)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=6 & dispinfrate=6 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 6 & AX(!ok -> device.infusionrate = 6)))) #Not Verified
 test
  AG(displaymode=disprate & device.infusionrate=7 & dispinfrate=7 -> AX(clear -> (dispinfrate=0 & device.infusionrate = 7 & AX(!ok -> device.infusionrate = 7)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=0 & dispinftime=0 -> AX(clear -> (dispinftime=0 & device.time = 0 & AX(ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=1 & dispinftime=1 -> AX(clear -> (dispinftime=0 & device.time = 1 & AX(ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=2 & dispinftime=2 -> AX(clear -> (dispinftime=0 & device.time = 2 & AX(ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=3 & dispinftime=3 -> AX(clear -> (dispinftime=0 & device.time = 3 & AX(ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=4 & dispinftime=4 -> AX(clear -> (dispinftime=0 & device.time = 4 & AX(ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=5 & dispinftime=5 -> AX(clear -> (dispinftime=0 & device.time = 5 & AX(ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=6 & dispinftime=6 -> AX(clear -> (dispinftime=0 & device.time = 6 & AX(ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=7 & dispinftime=7 -> AX(clear -> (dispinftime=0 & device.time = 7 & AX(ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=0 & dispinftime=0 -> AX(clear -> (dispinftime=0 & device.time = 0 & AX(!ok -> device.time = 0)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=1 & dispinftime=1 -> AX(clear -> (dispinftime=0 & device.time = 1 & AX(!ok -> device.time = 1)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=2 & dispinftime=2 -> AX(clear -> (dispinftime=0 & device.time = 2 & AX(!ok -> device.time = 2)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=3 & dispinftime=3 -> AX(clear -> (dispinftime=0 & device.time = 3 & AX(!ok -> device.time = 3)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=4 & dispinftime=4 -> AX(clear -> (dispinftime=0 & device.time = 4 & AX(!ok -> device.time = 4)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=5 & dispinftime=5 -> AX(clear -> (dispinftime=0 & device.time = 5 & AX(!ok -> device.time = 5)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=6 & dispinftime=6 -> AX(clear -> (dispinftime=0 & device.time = 6 & AX(!ok -> device.time = 6)))) #Not Verified
 test
  AG(displaymode=disptime & device.time=7 & dispinftime=7 -> AX(clear -> (dispinftime=0 & device.time = 7 & AX(!ok -> device.time = 7)))) #Not Verified
 test
  AG(device.volumeinfused = 0) #Not Verified
 test
  AG(device.volumeinfused = 2 -> EX(tick)) #Not Verified
 test
  AG(device.volumeinfused = 2 -> AX(tick)) #Not Verified
 test
  AG(device.volumeinfused = 2 -> EX(!tick)) #Not Verified
 test
  AG(device.volumeinfused = 2 -> !EX(!tick)) #Not Verified
 test
  AG(!(((device.vtbi + device.volumeinfused) = mvolume) & device.infusingstate & !device.kvoflag & (device.time <= timetoempty))) #Not Verified
 test
  AG(!(((device.vtbi + device.volumeinfused) = mvolume) & device.infusingstate & !device.kvoflag & (device.time <= timetoempty) & (displaymode=dispalarm))) #Not Verified
 test
  AG(!(((device.vtbi + device.volumeinfused) = mvolume) & device.infusingstate & !device.kvoflag & (device.time = 0) & (displaymode=dispalarm))) #Not Verified
 test
  AG((((device.vtbi + device.volumeinfused) = mvolume) & device.infusingstate & !device.kvoflag & (device.time <= timetoempty) & (displaymode=dispalarm)) -> EX(tick)) #Not Verified
 test
  AG((((device.vtbi + device.volumeinfused) = mvolume) & device.infusingstate & !device.kvoflag & (device.time <= timetoempty) & (displaymode=dispalarm)) -> !EX(tick)) #Not Verified
 test
  AG(phaserate=entering & entrymode=dataentry -> AX(dispinfrate = mrate -> !E[!ok U (phaseinfuse = entering)])) #Not Verified
 test
  AG(phaserate=entering & entrymode=dataentry -> AX(dispinfrate = mrate -> E[!ok U (phaseinfuse = entering)])) #Not Verified
 test
  AG(phasevtbi=entering & entrymode=dataentry -> AX(dispinfvtbi = mvolume -> !E[!ok U (phaserate = entering)])) #Verified True
 test
  AG(phasevtbi=entering & entrymode=dataentry -> AX(dispinfvtbi = mvolume -> E[!ok U (phaserate = entering)])) #Verified False
 test
  AG(device.volumeinfused != mvolume) #Verified False
