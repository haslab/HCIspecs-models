## MAL version of GUM related model for the IFM paper
## Michael Harrison & Rimvydas Ruksenas, QMUL, March 2014

defines
 maxsalience = 3
 ceilingsalience = 3
 nosalience = 0
 strongsalience = 1
 close = true

# A generic pattern for calculating the total salience (totalAct) for the activity Act based on its
# specificity (specAct) and cognitive (cogAct), procedural (procAct) and sensory (sensAct) salience:
#
#   specAct = ...
#   cogAct = ...
#   procAct = ...
#   sensAct = ...
#
# totalAct
#    ((specAct & cogAct & sensAct & procAct) -> totalAct' = strongsalience + strongsalience + strongsalience) &
#    ((specAct & cogAct & sensAct & !procAct) -> totalAct' =  strongsalience + strongsalience) &
#    ((specAct & (cogAct != sensAct) & procAct) -> totalAct' =  strongsalience + strongsalience) &
#    ((specAct & !cogAct & !sensAct & procAct) -> totalAct' =  strongsalience) &
#    ((specAct & (cogAct != sensAct) & !procAct) -> totalAct' =  strongsalience) &
#    ((!specAct & procAct) -> totalAct' =  strongsalience) &
#    ((specAct & !cogAct & !sensAct & !procAct) -> totalAct' = nosalience) &
#    ((!specAct & !procAct) -> totalAct' = nosalience) &

 spec1 = (interleave | (pump = one))
 spec2 = (interleave | (pump = two))
# mem1 salience
 specmem1 = (!close & !mem1completed)
 #cogmem1 = true
 #procmem1 = false
 sensmem1 = close
# mem2 salience
 specmem2 = (!close & !mem2completed)
 #cogmem2 = true
 #procmem2 = false
 sensmem2 = close
# ev1 salience
 specev1 = (!device1.vtbi & (device1.dm = dvtbi) & spec1)
 cogev1 = (close | mem1completed)
 procev1 = (lastactivity = Xmemorise1)
 #sensev1 = true
# ev2 salience
 specev2 = (!device2.vtbi & (device2.dm = dvtbi) & spec2)
 cogev2 = (close | mem2completed)
 procev2 = ((pump=two) & (lastactivity = Xmemorise2))
 #sensev2 = true
# cv1 salience
 speccv1 = (device1.vtbi & (device1.dm = dvtbi) & spec1)
 #cogcv1 = false
 proccv1 = ((lastactivity = Xentervtbi1) & (device1.vtbi | memvtbiset1))
 #senscv1 = true
# cv2 salience
 speccv2 = (device2.vtbi & (device2.dm = dvtbi) & spec2)
 #cogcv2 = false
 proccv2 = ((lastactivity = Xentervtbi2) & (device2.vtbi | memvtbiset2))
 #senscv2 = true
# cht1 salience
 speccht1 = ((!device1.time | !memtimeset1) & spec1)
 #cogcht1 = false
 proccht1 = (lastactivity=Xconfirmvtbi1)
 #senscht1 = true
# cht2 salience
 speccht2 = ((!device2.time | !memtimeset2) & spec2)
 #cogcht2 = false
 proccht2 = (lastactivity=Xconfirmvtbi2)
 #senscht2 = true
# et1 salience
 specet1 = (!device1.time & (device1.dm = dtime) & spec1)
 coget1 = ev1completed
 procet1 = (lastactivity = Xconfirmvtbi1)
 #senset1 = true
# et2 salience
 specet2 = (!device2.time & (device2.dm = dtime) & spec2)
 coget2 = ev2completed
 procet2 = (lastactivity = Xconfirmvtbi2)
 #senset2 = true
# ct1 salience
 specct1 = (device1.time & (device1.dm = dtime) & spec1)
 #cogct1 = false
 procct1 = ((lastactivity = Xentertime1) & (device1.time | memtimeset1))
 #sensct1 = true
# ct2 salience
 specct2 = (device2.time & (device2.dm = dtime) & spec2)
 #cogct2 = false
 procct2 = ((lastactivity = Xentertime2) & (device2.time | memtimeset2))
 #sensct2 = true
# oc1 salience
 specoc1 = ((device1.vtbi | memvtbiset1) & (device1.time | memtimeset1) & (device1.rate | memrateset1) & spec1)
 cogoc1 = et1completed
 prococ1 = (lastactivity = Xconfirmtime1)
 #sensoc1 = false
# oc2 salience
 specoc2 = ((device2.vtbi | memvtbiset2) & (device2.time | memtimeset2) & (device2.rate | memrateset2) & spec2)
 cogoc2 = et2completed
 prococ2 = (lastactivity = Xconfirmtime2)
 #sensoc2 = false
# inf1 salience
 specinf1 = ((device1.dm != dinfusing) & specoc1 & specoc2)
 coginf1 = ((oc1completed & (pump = one)) | inf2completed)
 #procinf1 = false
 #sensinf1 = true
# inf2 salience
 specinf2 = ((device2.dm != dinfusing) & specoc1 & specoc2)
 coginf2 = ((oc2completed & (pump = two)) | inf1completed)
 #procinf2 = false
 #sensinf2 = true


types
 mode = {off, hold, infuse}
 dispmode = {dblank, mainmenu, dvtbi, drate, dtime, dinfusing}
 devicenumber = {one, two}
 salience = nosalience .. maxsalience
 activity = {Xnull, Xmemorise1, Xmemorise2, Xentervtbi1,
             Xentervtbi2, Xconfirmvtbi1,
             Xconfirmvtbi2, Xentertime1, Xentertime2,
             Xchoosetime1, Xchoosetime2,
             Xconfirmtime1, Xconfirmtime2, Xopenclamp1,
             Xopenclamp2, Xstartinfuse1,
             Xstartinfuse2}

interactor device
 attributes
  [vis] dm: dispmode
  m: mode
  vtbi: boolean
  time: boolean
  rate: boolean
  clamp: boolean
 actions
  setup
  enter
#  switchoff
 # choosevtbi
  confirm
 # chooserate
  choosetime
  openclamp
 # closeclamp
  start
  tick

  axioms
  [] dm=dblank & m=off & !vtbi & !time & !rate & clamp
  per(setup) -> m=off
  [setup] m'=hold & dm'=dvtbi & keep(vtbi, time, rate, clamp)

  per(tick) -> m=hold & dm=mainmenu
  [tick] keep(dm, m, vtbi, time, rate, clamp)

#  per(switchoff) -> m=hold
#  [switchoff] m'=off & dm'=dblank & keep(vtbi, time, rate, clamp)

#  per(choosevtbi) -> dm=mainmenu
#  [choosevtbi] dm'=dvtbi & keep(m, vtbi, time, rate, clamp)

  per(enter) -> dm in {dvtbi, dtime, drate}
  dm = dvtbi -> [enter] vtbi' & keep(dm, m, time, rate, clamp)
  dm = drate -> [enter] rate' & keep(m, dm, vtbi, time, clamp)
  dm = dtime -> [enter] time' & keep(m, dm, rate, vtbi, clamp)

  per(confirm) -> dm in {dvtbi, dtime, drate}
  dm = dvtbi -> [confirm] dm'=mainmenu & (rate' = rate | time) &
                              (time' = rate | time) &
                              keep(vtbi, m, clamp)
  dm = drate -> [confirm] dm'=mainmenu & (vtbi'= vtbi | time) &
                              (time'= vtbi | time) &
                               keep(rate, m, clamp)
  dm = dtime -> [confirm] dm'=mainmenu & (vtbi'= vtbi | rate) &
                            rate'= (vtbi | rate) &
                          keep(time, m, clamp)


 # per(chooserate) -> dm=mainmenu
 # [chooserate] dm'=drate & keep(m, vtbi, time, rate, clamp)

  per(choosetime) -> dm=mainmenu
  [choosetime] dm'=dtime & keep(m, vtbi, time, rate, clamp)




  per(openclamp) -> clamp
  [openclamp] !clamp' & keep(m, dm, vtbi, rate, time)

 # per(closeclamp) -> !clamp
 # [closeclamp] clamp' & keep(m, dm, vtbi, rate, time)

  per(start) -> (dm=mainmenu & vtbi & rate & time) | (dm=dinfusing)
  (dm=mainmenu & vtbi & rate & time) -> [start] m'=infuse & dm'=dinfusing &
                                               keep(vtbi, time, rate, clamp)

  dm=dinfusing -> [start] m'=hold & dm'=mainmenu & keep(vtbi, time, rate, clamp)


interactor main
 aggregates
  device via device1
  device via device2
 attributes
  pump: devicenumber
  total: salience
  totalmem1: salience
  mem1completed: boolean
  totalmem2: salience
  mem2completed: boolean
  totalev1: salience
  ev1completed: boolean
  totalev2: salience
  ev2completed: boolean
  totalcv1: salience
  cv1completed: boolean
  totalcv2: salience
  cv2completed: boolean
  totalcht1: salience
  cht1completed: boolean
  totalcht2: salience
  cht2completed: boolean
  totalet1: salience
  et1completed: boolean
  totalet2: salience
  et2completed: boolean
  ct1completed: boolean
  totalct1: salience
  totalct2: salience
  ct2completed: boolean
  totaloc1: salience
  oc1completed: boolean
  totaloc2: salience
  oc2completed: boolean
  totalinf1: salience
  inf1completed: boolean
  totalinf2: salience
  inf2completed: boolean
  done: boolean
  lastactivity: activity
  interleave: boolean
  memvtbiset1: boolean
  memvtbiset2: boolean
  memrateset1: boolean
  memrateset2: boolean
  memtimeset1: boolean
  memtimeset2: boolean

 actions
  Tswitchon1
  Tswitchon2
  Tmemorise1
  Tmemorise2
  Tentervtbi1
  Tentervtbi2
  Tconfirmvtbi1
  Tconfirmvtbi2
  Tentertime1
  Tentertime2
  Tchoosetime1
  Tchoosetime2
  Tconfirmtime1
  Tconfirmtime2
  Topenclamp1
  Topenclamp2
  Tstartinfuse1
  Tstartinfuse2
  dropthrough
  setupround

 axioms
# initialisation
  [] !mem1completed & !mem2completed &
     !ev1completed & !ev2completed &
     !cv1completed & !cv2completed &
     !cht1completed & !cht2completed &
     !et1completed & !et2completed &
     !ct1completed & !ct2completed &
     !oc1completed & !oc2completed &
     !inf1completed & !inf2completed &
     !memvtbiset1 & !memvtbiset2 &
     !memrateset1 & !memrateset2 &
     !memtimeset1 &  !memtimeset2 &
     total=ceilingsalience & interleave &
     lastactivity = Xnull & !done
# axioms for device actions
  [device1.tick] effect(Tmemorise1)
  [device2.tick] effect(Tmemorise2)
  [device1.setup] effect(Tswitchon1)
  [device2.setup] effect(Tswitchon2)
  [device1.enter] effect(Tentervtbi1) | effect(Tentertime1)
  [device2.enter] effect(Tentervtbi2)  | effect(Tentertime2)
  [device1.confirm] effect(Tconfirmvtbi1)  | effect(Tconfirmtime1)
  [device2.confirm] effect(Tconfirmvtbi2)  | effect(Tconfirmtime2)
  [device1.choosetime] effect(Tchoosetime1)
  [device2.choosetime] effect(Tchoosetime2)
  [device1.openclamp] effect(Topenclamp1)
  [device2.openclamp] effect(Topenclamp2)
  [device1.start] effect(Tstartinfuse1)
  [device2.start] effect(Tstartinfuse2)

# this activity sets up the round
  per(setupround) -> done
  [setupround]
# totalmem1
    ((specmem1 & sensmem1) -> totalmem1' =  strongsalience + strongsalience) &
    ((specmem1 & !sensmem1) -> totalmem1' =  strongsalience) &
    ((!specmem1) -> totalmem1' = nosalience) &
# totalmem2
    ((specmem2 & sensmem2) -> totalmem2' =  strongsalience + strongsalience) &
    ((specmem2 & !sensmem2) -> totalmem2' =  strongsalience) &
    ((!specmem2) -> totalmem2' = nosalience) &

# totalev1
    ((specev1 & cogev1 & procev1) -> totalev1' = strongsalience + strongsalience + strongsalience) &
    ((specev1 & (cogev1 != procev1)) -> totalev1' =  strongsalience + strongsalience) &
    ((specev1 & !cogev1 & !procev1) -> totalev1' =  strongsalience) &
    ((!specev1 & procev1) -> totalev1' =  strongsalience) &
    ((!specev1 & !procev1) -> totalev1' = nosalience) &
# totalev2
    ((specev2 & cogev2 & procev2) -> totalev2' = strongsalience + strongsalience + strongsalience) &
    ((specev2 & (cogev2 != procev2)) -> totalev2' =  strongsalience + strongsalience) &
    ((specev2 & !cogev2 & !procev2) -> totalev2' =  strongsalience) &
    ((!specev2 & procev2) -> totalev2' =  strongsalience) &
    ((!specev2 & !procev2) -> totalev2' = nosalience) &

# totalcv1
    ((speccv1 & proccv1) -> totalcv1' =  strongsalience + strongsalience) &
    ((speccv1 != proccv1) -> totalcv1' =  strongsalience) &
    ((!speccv1 & !proccv1) -> totalcv1' = nosalience) &
# totalcv2
    ((speccv2 & proccv2) -> totalcv2' =  strongsalience + strongsalience) &
    ((speccv2 != proccv2) -> totalcv2' =  strongsalience) &
    ((!speccv2 & !proccv2) -> totalcv2' = nosalience) &

# totalcht1
    ((speccht1 & proccht1) -> totalcht1' =  strongsalience + strongsalience) &
    ((speccht1 != proccht1) -> totalcht1' =  strongsalience) &
    ((!speccht1 & !proccht1) -> totalcht1' = nosalience) &
# totalcht2
    ((speccht2 & proccht2) -> totalcht2' =  strongsalience + strongsalience) &
    ((speccht2 != proccht2) -> totalcht2' =  strongsalience) &
    ((!speccht2 & !proccht2) -> totalcht2' = nosalience) &

# totalet1
    ((specet1 & coget1 & procet1) -> totalet1' = strongsalience + strongsalience + strongsalience) &
    ((specet1 & (coget1 != procet1)) -> totalet1' =  strongsalience + strongsalience) &
    ((specet1 & !coget1 & !procet1) -> totalet1' =  strongsalience) &
    ((!specet1 & procet1) -> totalet1' =  strongsalience) &
    ((!specet1 & !procet1) -> totalet1' = nosalience) &
# totalet2
    ((specet2 & coget2 & procet2) -> totalet2' = strongsalience + strongsalience + strongsalience) &
    ((specet2 & (coget2 != procet2)) -> totalet2' =  strongsalience + strongsalience) &
    ((specet2 & !coget2 & !procet2) -> totalet2' =  strongsalience) &
    ((!specet2 & procet2) -> totalet2' =  strongsalience) &
    ((!specet2 & !procet2) -> totalet2' = nosalience) &

# totalct1
    ((specct1 & procct1) -> totalct1' =  strongsalience + strongsalience) &
    ((specct1 != procct1) -> totalct1' =  strongsalience) &
    ((!specct1 & !procct1) -> totalct1' = nosalience) &
# totalct2
    ((specct2 & procct2) -> totalct2' =  strongsalience + strongsalience) &
    ((specct2 != procct2) -> totalct2' =  strongsalience) &
    ((!specct2 & !procct2) -> totalct2' = nosalience) &

# totaloc1
    ((specoc1 & cogoc1 & prococ1) -> totaloc1' =  strongsalience + strongsalience) &
    ((specoc1 & (cogoc1 != prococ1)) -> totaloc1' =  strongsalience) &
    ((!specoc1 & prococ1) -> totaloc1' =  strongsalience) &
    (((!specoc1 | !cogoc1) & !prococ1) -> totaloc1' = nosalience) &
# totaloc2
    ((specoc2 & cogoc2 & prococ2) -> totaloc2' =  strongsalience + strongsalience) &
    ((specoc2 & (cogoc2 != prococ2)) -> totaloc2' =  strongsalience) &
    ((!specoc2 & prococ2) -> totaloc2' =  strongsalience) &
    (((!specoc2 | !cogoc2) & !prococ2) -> totaloc2' = nosalience) &

# totalinf1
    ((specinf1 & coginf1) -> totalinf1' =  strongsalience + strongsalience) &
    ((specinf1 & !coginf1) -> totalinf1' =  strongsalience) &
    ((!specinf1) -> totalinf1' = nosalience) &
# totalinf2
    ((specinf2 & coginf2) -> totalinf2' =  strongsalience + strongsalience) &
    ((specinf2 & !coginf2) -> totalinf2' =  strongsalience) &
    ((!specinf2) -> totalinf2' = nosalience) &

    !done' &
    keep(mem1completed, mem2completed,
         ev1completed, ev2completed,
         cv1completed, cv2completed,
         cht1completed, cht2completed,
         et1completed, et2completed,
         ct1completed, ct2completed,
         oc1completed, oc2completed,
         inf1completed, inf2completed,
         memvtbiset1, memvtbiset2,
         memtimeset1, memtimeset2,
         memrateset1, memrateset2,
         total, pump, lastactivity, interleave)


## axioms for activities
  per(Tswitchon1) -> device1.m = off & !done
  [Tswitchon1] effect(device1.setup) & done' & total'= ceilingsalience &
               keep(mem1completed, mem2completed,
                    ev1completed,
                    ev2completed,  cv1completed,
                    cv2completed,  cht1completed,
                    cht2completed, et1completed, et2completed,
                    ct1completed, ct2completed,
                    oc1completed, oc2completed, inf1completed,
                    inf2completed,
                    memvtbiset1, memvtbiset2,
                    memtimeset1,
                    memtimeset2, memrateset1,
                    memrateset2,
                    lastactivity,
                    pump,
                    interleave)
  per(Tswitchon2) -> device2.m = off & !done
  [Tswitchon2] effect(device2.setup) & done' & total'= ceilingsalience &
               keep(mem1completed, mem2completed,
                    ev1completed,
                    ev2completed, cv1completed,
                    cv2completed,  cht1completed,
                    cht2completed, et1completed, et2completed,
                    ct1completed, ct2completed,
                    oc1completed, oc2completed, inf1completed,
                    inf2completed,
                    memvtbiset1, memvtbiset2,
                    memtimeset1,
                    memtimeset2, memrateset1,
                    memrateset2,
                    lastactivity,
                    pump,
                    interleave)

  per(Tmemorise1) -> (totalmem1 >= total) & !done
  [Tmemorise1] effect(device1.tick) & pump'= one &
               !interleave' &
               total'= ceilingsalience & done' &
               mem1completed' & lastactivity'= Xmemorise1 &
      keep(mem2completed, ev1completed, ev2completed,
           cv1completed, cv2completed,  cht1completed,
           cht2completed, et1completed, et2completed,
           ct1completed, ct2completed,
           oc1completed, oc2completed, inf1completed,
           inf2completed,
           memvtbiset1, memvtbiset2, memtimeset1,
           memtimeset2, memrateset1, memrateset2
           )

  per(Tmemorise2) -> (totalmem2 >= total) & !done & mem1completed
  [Tmemorise2] effect(device2.tick) &
               !interleave' & mem2completed' & done' &
               lastactivity' = Xmemorise2 &
               total'= ceilingsalience & pump'= two &
      keep(mem1completed, ev1completed, ev2completed,
           cv1completed, cv2completed, cht1completed,
           cht2completed, et1completed, et2completed,
           ct1completed, ct2completed,
           oc1completed, oc2completed, inf1completed,
           inf2completed,
           memvtbiset1, memvtbiset2, memtimeset1,
           memtimeset2, memrateset1, memrateset2
           )

  per(Tentervtbi1) -> (totalev1 >= total) & !done & (close | mem1completed)
  [Tentervtbi1] effect(device1.enter) & pump'= one
                & memvtbiset1' & ev1completed' &
                total'= ceilingsalience & done' &
                lastactivity'= Xentervtbi1 &
         keep(mem1completed, mem2completed, ev2completed,
              cv1completed, cv2completed, cht1completed,
              cht2completed, et1completed, et2completed,
              ct1completed, ct2completed,
              oc1completed, oc2completed, inf1completed,
              inf2completed,
              memvtbiset2, memtimeset1, memtimeset2,
              memrateset1,
              memrateset2,
              interleave)

  per(Tentervtbi2) -> (totalev2 >= total) & !done & (close | mem2completed) & ev1completed
  [Tentervtbi2] effect(device2.enter) & pump'= two &
             memvtbiset2' & ev2completed' &
             total'= ceilingsalience & done' &
             lastactivity'= Xentervtbi2 &
     keep(mem1completed, mem2completed, ev1completed,
          cv1completed, cv2completed, cht1completed,
          cht2completed, et1completed, et2completed,
          ct1completed, ct2completed,
          oc1completed, oc2completed,
          inf1completed, inf2completed,
          memvtbiset1, memtimeset1,
          memtimeset2, memrateset1,
          memrateset2,
          interleave)

  per(Tconfirmvtbi1) -> (totalcv1 >= total) & !done
  [Tconfirmvtbi1] effect(device1.confirm) & pump'= one &
                  cv1completed' & done' &
                  total'= ceilingsalience &
                  lastactivity'= Xconfirmvtbi1 &
     keep(mem1completed, mem2completed, ev1completed,
          ev2completed, cv2completed, cht1completed,
          cht2completed, et1completed, et2completed,
          ct1completed, ct2completed,
          oc1completed, oc2completed, inf1completed,
          inf2completed,
          memvtbiset1, memvtbiset2, memtimeset1,
          memtimeset2, memrateset1,
          memrateset2,
          interleave)

  per(Tconfirmvtbi2) -> (totalcv2 >= total) & !done
  [Tconfirmvtbi2] effect(device2.confirm) & pump'= two &
                  cv2completed' & done' &
                  total'= ceilingsalience &
                  lastactivity'= Xconfirmvtbi2 &
        keep(mem1completed, mem2completed, ev1completed,
             ev2completed, cv1completed, cht1completed,
             cht2completed, et1completed, et2completed,
             ct1completed, ct2completed,
             oc1completed, oc2completed, inf1completed,
             inf2completed,
             memvtbiset1, memvtbiset2, memtimeset1,
             memtimeset2, memrateset1,
             memrateset2,
             interleave)

  per(Tchoosetime1) -> (totalcht1 >= total) & !done & (device1.dm = mainmenu)
  [Tchoosetime1]  effect(device1.choosetime) &
                 pump'= one & done' &
                 lastactivity'= Xchoosetime1 &
                 total'= ceilingsalience &
                 cht1completed' &
             keep(mem1completed, mem2completed, ev1completed,
                  ev2completed, cv1completed, cv2completed,
                  cht2completed, et1completed, et2completed,
                  ct1completed, ct2completed,
                  oc1completed, oc2completed,
                  inf1completed, inf2completed,
                  memvtbiset1, memvtbiset2, memtimeset1,
                  memtimeset2, memrateset1,
                  memrateset2,
                  interleave)

  per(Tchoosetime2) -> (totalcht2 >= total) & !done & (device2.dm = mainmenu) & cht1completed
  [Tchoosetime2]  effect(device2.choosetime) &
                 pump'= two & done' &
                 cht2completed' & lastactivity'= Xchoosetime2 &
                 total'= ceilingsalience &
             keep(mem1completed, mem2completed, ev1completed,
                  ev2completed,
                  cv1completed, cv2completed, cht1completed,
                  et1completed, et2completed,  ct1completed, ct2completed,
                  oc1completed, oc2completed, inf1completed, inf2completed,
                  memvtbiset1, memvtbiset2, memtimeset1,
                  memtimeset2, memrateset1, memrateset2,
                  interleave)

  per(Tentertime1) -> (totalet1 >= total) & !done & (close | mem1completed)
  [Tentertime1] effect(device1.enter) &
                memtimeset1' &
                pump'= one & done' & total'= ceilingsalience &
                lastactivity'= Xentertime1 &
                et1completed' &
                keep(mem1completed, mem2completed,
                     ev1completed, ev2completed,
                     cv1completed, cv2completed, cht1completed,
                     cht2completed, et2completed,
                     ct1completed, ct2completed,
                     oc1completed, oc2completed, inf1completed, inf2completed,
                     memvtbiset1, memvtbiset2,
                     memtimeset2, memrateset1,
                     memrateset2,
                     interleave)

  per(Tentertime2) -> (totalet2 >= total) & !done & (close | mem2completed) & et1completed
  [Tentertime2] effect(device2.enter) &
                memtimeset2' &
                pump'= two & done' & total'= ceilingsalience &
                et2completed' & lastactivity'= Xentertime2 &
                keep(mem1completed, mem2completed, ev1completed,
                ev2completed, cv1completed, cv2completed,
                cht1completed,
                cht2completed, et1completed, ct1completed, ct2completed,
                oc1completed, oc2completed, inf1completed, inf2completed,
                memvtbiset1, memvtbiset2, memtimeset1,
                memrateset1, memrateset2,
                interleave)

  per(Tconfirmtime1) -> (totalct1 >= total) & !done
  [Tconfirmtime1] effect(device1.confirm) & pump'= one &
                ct1completed' & done' & lastactivity'= Xconfirmtime1 &
                total'= ceilingsalience &
                keep(mem1completed, mem2completed, ev1completed, ev2completed,
                     cv1completed, cv2completed, cht1completed,
                     cht2completed, et1completed, et2completed,  ct2completed,
                     oc1completed, oc2completed, inf1completed, inf2completed,
                     memvtbiset1, memvtbiset2, memtimeset1,
                     memtimeset2, interleave, memrateset1, memrateset2)

  per(Tconfirmtime2) -> (totalct2 >= total) & !done
  [Tconfirmtime2] effect(device2.confirm) & pump'= two &
                  ct2completed' & done' & lastactivity'= Xconfirmtime2 &
                  total'= ceilingsalience &
                  keep(mem1completed, mem2completed, ev1completed, ev2completed,
                       cv1completed, cv2completed, cht1completed,
                       cht2completed, et1completed, et2completed,  ct1completed,
                       oc1completed, oc2completed, inf1completed, inf2completed,
                       memvtbiset1, memvtbiset2, memtimeset1, memtimeset2,
                       interleave, memrateset1, memrateset2)

  per(Topenclamp1) -> (totaloc1 >= total) & !done & device1.clamp
  [Topenclamp1] effect(device1.openclamp) & pump'= one &
                oc1completed' & done' & lastactivity'= Xopenclamp1 &
                total'= ceilingsalience &
                keep(mem1completed, mem2completed, ev1completed, ev2completed,
                     cv1completed, cv2completed, cht1completed,
                     cht2completed, et1completed, et2completed,
                     ct1completed, ct2completed,
                     oc2completed, inf1completed, inf2completed,
                     memvtbiset1, memvtbiset2, memtimeset1, memtimeset2, memrateset1,
                     memrateset2, interleave)

  per(Topenclamp2) -> (totaloc2 >= total) & !done & device2.clamp
  [Topenclamp2] effect(device2.openclamp) & pump'= two &
                oc2completed' & done' & lastactivity'= Xopenclamp2 &
                total'= ceilingsalience &
                keep(mem1completed, mem2completed, ev1completed, ev2completed,
                     cv1completed, cv2completed, cht1completed,
                     cht2completed, et1completed, et2completed,
                     ct1completed, ct2completed,
                     oc1completed, inf1completed, inf2completed,
                     memvtbiset1, memvtbiset2, memtimeset1, memtimeset2, memrateset1,
                     memrateset2, interleave)

  per(Tstartinfuse1) -> (totalinf1 >= total) & !done
  [Tstartinfuse1] effect(device1.start) & pump'= one &
                inf1completed' & done' & lastactivity'= Xstartinfuse1 &
                total'= ceilingsalience &
                keep(mem1completed, mem2completed, ev1completed, ev2completed,
                     cv1completed, cv2completed, cht1completed,
                     cht2completed, et1completed, et2completed,
                     ct1completed, ct2completed,
                     oc1completed, oc2completed, inf2completed,
                     memvtbiset1, memvtbiset2,
                     memtimeset1, memtimeset2, memrateset1,
                     memrateset2, interleave)

  per(Tstartinfuse2) -> (totalinf2 >= total) & !done
  [Tstartinfuse2] effect(device2.start) & pump'= two &
                inf2completed' & done' & lastactivity'= Xstartinfuse2 &
                total'= ceilingsalience &
                keep(mem1completed, mem2completed, ev1completed, ev2completed,
                     cv1completed, cv2completed, cht1completed,
                     cht2completed, et1completed, et2completed,
                     ct1completed, ct2completed,
                     oc1completed, oc2completed, inf1completed,
                     memvtbiset1, memvtbiset2, memtimeset1,
                     memtimeset2, memrateset1,
                     memrateset2, interleave)

  per(dropthrough) -> ((totalmem1<total) | mem1completed) &
                      ((totalmem2<total) | mem2completed)  &
                      ((totalev1<total) | ev1completed) &
                      ((totalev2<total) | ev2completed) &
                      ((totalcv1< total) | cv1completed) &
                      ((totalcv2<total) | cv2completed) &
                      ((totalcht1<total) | cht1completed) &
                      ((totalcht2<total) | cht2completed) &
                      ((totalet1<total) | et1completed) &
                      ((totalet2<total) | et2completed) &
                      ((totalct1<total) | ct1completed) &
                      ((totalct2 <total) | ct2completed) &
                      ((totaloc1 < total) | oc1completed) &
                      ((totaloc2 < total) | oc2completed) &
                      ((totalinf1 < total) | inf1completed) &
                      ((totalinf2 < total) | inf2completed) &
                     !done & (device1.m != off) & (device2.m != off)
  [dropthrough] (total > 1 -> total'= total-1) & (total = 1 -> keep(total)) &
                keep(mem1completed, mem2completed, ev1completed,
                     ev2completed,
                     cv1completed, cv2completed,  cht1completed,
                     cht2completed, et1completed, et2completed,
                     ct1completed, ct2completed,
                     oc1completed, oc2completed, inf1completed, inf2completed,
                     totalmem1, totalmem2, totalev1, totalev2,
                     totalcv1, totalcv2, totalcht1, totalcht2,
                     totalet1, totalet2, totalct1, totalct2,
                     totaloc1, totaloc2, totalinf1, totalinf2,
                     memvtbiset1, memvtbiset2, memtimeset1,
                     memtimeset2,
                     interleave, done, memrateset1, memrateset2,
                     lastactivity)

  per(nil) -> false





















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































 test
  AG(!inf1completed)
 test
  AG(!mem1completed)
 test
  AG(csmem1 != 0)
 test
  AG(csmem1 = 0)
 test
  AG(psmem1 = 0)
 test
  AG(totalmem1 = 0)
 test
  AG(csmem1!=weaksalience)
 test
  AG(csmem1=weaksalience)
 test
  AG(!mem2completed)
 test
  AG(!(totalmem1 >= total))
 test
  AG(!dropthrough)
 test
  AG(csmem1=0)
 test
  AG((device1.m=hold) -> (totalmem1<weaksalience))
 test
  AG(totalmem1=0)
 test
  AG((device2.m=hold) -> (totalmem2<total))
 test
  AG(Tmemorise2 -> AG(!Tswitchon1))
 test
  AG(device1.m=hold -> totalmem1<total)
 test
  AG(totalev1<total)
 test
  AG(Tmemorise1 -> AG(!Tentervtbi1))
 test
  AG(pump=two)
 test
  AG(totalmem2<total)
 test
  AG(!(totalmem2>=total & device2.m=hold & mem1completed))
 test
  AG(!(cht1completed & cht2completed))
 test
  AG(!Tentertime2)
 test
  AG(!Tconfirmtime1)
 test
  AG(!Tconfirmtime2)
 test
  AG(!Topenclamp1)
 test
  AG(totaloc1 != ceilingsalience & !done)
 test
  AG(!(totaloc1 = ceilingsalience & !done & !(device1.m=off)))
 test
  AG(!(totaloc1 = ceilingsalience & device1.m != off))
 test
  AG(Tconfirmtime1 -> AX(!setupround))
 test
  AG(!ct1completed)
 test
  AG(!ct2completed)
 test
  AG(!et2completed)
 test
  AG(!et1completed)
 test
  AG(et1completed -> AX(!setupround))
 test
  AG(ct1completed -> AX(!setupround))
 test
  AG(!Topenclamp2)
 test
  AG(!Tstartinfuse1)
 test
  AG(!(inf1completed & inf2completed))
 test
  AF(device2.dm=dinfusing)
 test
  AG(!(device2.dm=dinfusing))
 test
  AG(!Tmemorise1)
 test
  AG(!Tswitchon1)
 test
  AG(!Tentervtbi1)
 test
  AG(!Tentertime1)
 test
  AG(!Tentervtbi2)
 test
  AG(!Tchoosetime1)
 test
  AG(!Tchoosetime2)
 test
  AG(!Tconfirmvtbi1)
 test
  AG(!Tconfirmvtbi2)
 test
  AG(!Tswitchon2)
 test
  AG(!Tmemorise2)
 test
  AG((device1.dm=dinfusing) -> !device1.clamp)
 test
  AG((device2.dm=dinfusing) -> !device2.clamp)
 test
  AF((device1.dm=dinfusing) & (device2.dm=dinfusing))
 test
  AG(!Tstartinfuse2)
 test
  AG(!inf2completed)
 test
  AG(lastactivity = Xentervtbi1 -> AX(Tconfirmvtbi1))
 test
  AG(lastactivity = Xentervtbi2 -> AX(Tconfirmvtbi2))
 test
  AG(lastactivity = Xentertime1 -> AX(Tconfirmtime1))
 test
  AG(lastactivity = Xentertime2 -> AX(Tconfirmtime2))
 test
  AG(Tstartinfuse1 -> cv1completed & ct1completed & oc1completed)
 test
  AG(Tstartinfuse2 -> cv2completed & ct2completed & oc2completed)
 test
  AG(Tconfirmvtbi1 -> ev1completed & !et1completed & !oc1completed)
 test
  AG(Tconfirmvtbi1 -> ev1completed & !et1completed)
 test
  AG(Tconfirmvtbi2 -> ev2completed & !et2completed)
