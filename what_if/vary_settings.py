#
"""
	Scan APS logfile and extract relevant items
    to compare original SMB analysis vs. the determine_basal.py
"""
#	Version INIT		Started	08.Dec.2019			Author	Gerhard Zellermann
#   - adapted from scanAPSlog.py

import sys
import os
#mport curses
import glob
from email.utils import formatdate
import datetime
from datetime import timezone
import time
import json
import zipfile
from decimal import *
import binascii
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from matplotlib.animation import FFMpegWriter
from matplotlib.backends.backend_pdf import PdfPages

import determine_basal as detSMB
from determine_basal import my_ce_file 


def hole(sLine, Ab, Auf, Zu):
    #E extrahiere Substring ab der Stelle "ab"
    #E	beginnend mit dem Zeichen "Auf" bis zum Zeichen "Zu"
    #E	wobei Level gezählt werden wie in "...[xxx[yy]]..."
    offsetAnf = 0
    offsetEnd = 0
    Anf_pos = sLine[Ab:].find(Auf) + Ab
    #if sLine.find('[Intent')<3: print('hole gerufen mit:' , Auf, ' an Stelle', str(Anf_pos), 'in '+sLine)
    while Anf_pos>=0:
        End_pos = sLine[Anf_pos+offsetEnd+1:].find(Zu) + Anf_pos+offsetEnd+1
        #if sLine.find('[Intent')<3: print(str(Anf_pos)+':'+  Auf+', '+ str(End_pos)+':'+  Zu, 'in '+sLine[Anf_pos+offsetEnd+1:])
        if End_pos == Anf_pos+offsetEnd+1*0:    break
        Zw_Anf = sLine[Anf_pos+offsetAnf+1:End_pos].find(Auf) + Anf_pos+offsetAnf+1
        #if sLine.find('[Intent')<3: print ('suche  2. Vorkommen von '+Auf+' in '+sLine[Anf_pos+offsetAnf+1:End_pos])
        #if sLine.find('[Intent')<3: print (str(Zw_Anf), str(offsetAnf), str(offsetEnd))
        if Zw_Anf==Anf_pos+offsetAnf:   #+1  or  Zw_Anf>End_pos:
            return sLine[Anf_pos:End_pos+1]
            break
        offsetAnf = Zw_Anf  - Anf_pos
        offsetEnd = End_pos - Anf_pos #+ 1
        #wdhl = input('any key')
    return ''

def GetStr(Curly, Ab, Key):
    #E extrahiere Substring für Flag "Key" ab der Stelle Ab

    wo	= Curly[Ab:].find('"' + Key +'"') + Ab
    if wo < Ab:
        Found = ''
    else:
        bis		= Curly[wo+len(Key)+4:].find('"') + wo+len(Key)+4
        Found	= Curly[wo+len(Key)+4:bis]
        #print (str(wo), str(bis))
    return Found 

def GetValStr(Curly, Ab, Key):
    #E extrahiere Number as String für Flag "Key" ab der Stelle Ab

    wo	= Curly[Ab:].find('"' + Key +'"') + Ab
    if wo < Ab:
        Found = ''
    else:
        bis		= Curly[wo+len(Key)+3:].find(',') + wo+len(Key)+3
        Found	= Curly[wo+len(Key)+3:bis]
        #print (str(wo), str(bis))
    return Found 

def GetUnquotedStr(Curly, Ab, Key):
    #E extract unquoted String für Flag "Key" ab der Stelle Ab up to next COMMA

    wo	= Curly[Ab:].find(Key) + Ab
    if wo < Ab:
        Found = ''
    else:
        bis		= Curly[wo+len(Key)+0:].find(',') + wo+len(Key)+0
        Found	= Curly[wo+len(Key)+0:bis]
        #print (str(wo), str(bis))
    return Found 

def printBool(treat, key, log):
    if 'isSMB' in treat:        isSMB = treat[key]
    else:                       isSMB = False
    log.write('  ' + (key+'   ')[:5] + '=' + str(isSMB) + '\n')

def printStr(treat, key, log):
    if key in treat:
        myStr = treat[key]
        wo = myStr.find('\n')
        if wo>0:
            myEnd = myStr[wo+1:]                    # \n counts as 1 character !!
            myStr = myStr[:wo] + ' --> ' + myEnd    # Announcements often take 2 lines
    else:
        myStr = ''
    log.write('  ' + (key+'         ')[:10] + '=' + myStr + '\n')

def printVal(treat, key, log):
    log.write('  ' + (key+'    ')[:6] + '=' + str(treat[key]) + '\n')

def getReason(reason, keyword, ending, dezi):
    wo_key = reason.find(keyword)
    #print (wo_key, reason + '\n')
    if wo_key < 0:
        #print (keyword , 'nicht gefunden')
        return ''
    else:
        wo_com = reason[wo_key+len(keyword)+1:].find(ending) + wo_key+len(keyword)+1
        #print (reason[wo_key:])
        key_str = reason[wo_key+len(keyword):wo_com]
        #print ('complete-->', keyword, '['+key_str+']')
        #key_str = key_str[:-1]
        #print ('  capped-->', keyword, '['+key_str+']')
        return key_str

def basalFromReason(smb, lcount):
    #print(str(smb))
    suggest = smb['openaps']['suggested']
    if 'rate' in suggest :
        rateReq = suggest['rate']
    elif 'TempBasalAbsoluteRate' in  smb['pump']['extended']:
        rateReq = smb['pump']['extended']['TempBasalAbsoluteRate']
    else:
        rateReq = 0         # zero if not explicitely listed
    #print('rateReq in row '+str(lcount)+' from "suggest.json" is ['+str(rateReq)+']')

    return str(rateReq)

def basalFromReasonOnlyold(reason, lcount):
    # the method below is very difficult and still incomplete
    # obviously various programmers followed differnet logic how to declare the new rate    
    if reason.find('no temp required')>1 :
        tempReq = '0'
        tempSource = "no temp required"
    else :
        tempReq = getReason(reason, 'maxSafeBasal:',       ',', 3)
        tempSource = "maxSafeBasal:...,"
    if  tempReq == '':
        tempReq = getReason(reason, 'temp',    '~<', 3)
        tempSource = "temp...~<"
    if  tempReq == '':
        tempReq = getReason(reason, 'temp',    '>~', 3)
        tempSource = "temp...>~"
    if  tempReq == '':
        tempReq = getReason(reason, '<',       'U', 3)
        tempSource = "<...U"
    if  tempReq == '':
        tempReq = getReason(reason, '~ req',   'U', 3)
        tempSource = "~ req...U"
    if  tempReq == '':
        tempReq = getReason(reason, 'temp of', 'U', 3)
        tempSource = "temp of...U"
    if  tempReq == '':
        tempReq = getReason(reason, 'temp',    '<', 3)
        tempSource = "temp...<"
    if tempReq != '':   tempReq = str(round(eval(tempReq),4))
    else : tempReq = '0'
    print('tempReq in row '+str(lcount)+' from "'+tempSource+'" is ['+tempReq+']')
    
    return tempReq

def basalFromReasonOnly(reason, lcount):
    # the method below is very difficult and still incomplete
    # obviously various programmers followed differnet logic how to declare the new rate    
    if reason.find('no temp required')>1 :
        tempReq = '0'
        tempSource = "no temp required"
    else :
        tempReq = getReason(reason, 'maxSafeBasal:',       ',', 3)
        tempSource = "maxSafeBasal:...,"
    if  tempReq == '':
        tempReq = getReason(reason, 'temp',    '~<', 3)
        tempSource = "temp...~<"
    if  tempReq == '':
        tempReq = getReason(reason, 'temp',    '>~', 3)
        tempSource = "temp...>~"
    if  tempReq == '':
        tempReq = getReason(reason, 'm low temp of', 'U', 3)        # near source row 1049
        tempSource = "m low temp of...U"
    if  tempReq == '':
        tempReq = getReason(reason, 'temp of', 'U', 3)
        tempSource = "temp of...U"
    if  tempReq == '':
        tempReq = getReason(reason, 'setting',       'U', 3)
        tempSource = "setting...U"
    if  tempReq == '':
        tempReq = getReason(reason, '<',       'U', 3)
        tempSource = "<...U"
    if  tempReq == '':
        tempReq = getReason(reason, '~ req',   'U', 3)
        tempSource = "~ req...U"
    if  tempReq == '':
        tempReq = getReason(reason, 'temp',    '<', 3)
        tempSource = "temp...<"
    #print('tempReq in row '+str(lcount)+' from "'+tempSource+'" is ['+tempReq+']')
    if tempReq != '':   tempReq = str(round(eval(tempReq),4))
    else : tempReq = '0'
    #print('tempReq in row '+str(lcount)+' from "'+tempSource+'" is ['+tempReq+']')
    
    return tempReq

def basalFromEmulation(returned, lcount):
    #returned = json.loads(reason)
    if 'rate' in returned:
        tempReq = returned['rate']              # soecific basal rate requested
    else:
        tempReq = currenttemp['rate']           # no change, keep current basal rate
    return str(round(tempReq,4))

def setVariant():
    # set the what-if scenario
    global autosens_data
    global glucose_status
    global bg
    global currenttemp
    global iob_data
    global meal_data
    global profile

    ####################################################################################################################################
    # additional parameters collected here
    # these need an according modification in "determine_basal.py"
    new_parameter = {}
    # first, do the AAPS standard assignments           ### variations are set in the <variant>.dat file
    new_parameter['maxDeltaRatio'] = 0.2                ### additional parameter; AAPS is fix at 0.2
    new_parameter['SMBRatio'] = 0.5                     ### additional parameter; AAPS is fix at 0.5; I use 0.6 as no other rig interferes
    new_parameter['maxBolusIOBUsual'] = True            ### additional parameter; AAPS is fix at True, but my basal is too low
    new_parameter['maxBolusIOBRatio'] = 1               ### additional parameter; AAPS is fix at 1, but my basal is too low
    new_parameter['maxBolusTargetRatio'] = 1.001        ### additional parameter; AAPS is fix at 1, bit i saw rounding problems otherwise
    new_parameter['insulinCapBelowTarget'] = False      ### additional parameter; AAPS is fix at False; enable capping below target
    
    ####################################################################################################################################
    # read the variations and apply them
    fn = varLabel + '.dat'
    var = open(fn, 'r')
    for zeile in var:
        # get array name
        woEndArray  = zeile.find(' ')
        myArray     = zeile[:woEndArray]
        zeile = zeile[woEndArray:]                                              # remaining stuff to be parsed
        while zeile[0] == ' ':        zeile = zeile[1:]                         # truncate leading BLANKS
        woEndItem   = zeile.find(' ')
        myItem      = zeile[:woEndItem]
        zeile = zeile[woEndItem:]                                               # remaining stuff to be parsed
        while zeile[0] == ' ':        zeile = zeile[1:]                         # truncate leading BLANKS
        woEndVal    = zeile.find('###')
        if woEndVal < 0 :   woEndVal = len(zeile)                               # no trailing comment
        myVal       = zeile[:woEndVal]
        while myVal[-1] == ' ' :    myVal = myVal[:-1]                          # truncate trailing BLANKS
        #print('['+myArray+'], ['+myItem+'], ['+myVal+']')
        validRow = False
        
        logmsg = 'appended new entry to'
        if   myArray == 'autosens_data' :
             if myItem in autosens_data :
                logmsg = 'edited old value of '+str(autosens_data[myItem])+' in'
             autosens_data[myItem] = eval(myVal)
             validRow = True
        elif myArray == 'glucose_status' :
             if myItem in glucose_status :
                logmsg = 'edited old value of '+str(glucose_status[myItem])+' in'
             glucose_status[myItem] = eval(myVal)
             validRow = True
        elif myArray == 'currenttemp' :
             if myItem in currenttemp :
                logmsg = 'edited old value of '+str(currenttemp[myItem])+' in'
             currenttemp[myItem] = eval(myVal)
             validRow = True
        elif myArray == 'iob_data' :
             if myItem in iob_data :
                logmsg = 'edited old value of '+str(iob_data[myItem])+' in'
             iob_data[myItem] = eval(myVal)
             validRow = True
        elif myArray == 'meal_data' :
             if myItem in meal_data :
                logmsg = 'edited old value of '+str(meal_data[myItem])+' in'
             meal_data[myItem] = eval(myVal)
             validRow = True
        elif myArray == 'profile' :
             if myItem in profile :
                logmsg = 'edited old value of '+str(profile[myItem])+' in'
             profile[myItem] = eval(myVal)
             validRow = True
        elif myArray == 'new_parameter' :
             if myItem in new_parameter :
                logmsg = 'edited old value of '+str(new_parameter[myItem])+' in'
             new_parameter[myItem] = eval(myVal)
             validRow = True
 
        if validRow:    varlog.write(logmsg+' '+myArray+' with '+myItem+'='+str(eval(myVal))+'\n')
        else:           varlog.write('not actioned: ['+myArray+'], ['+myItem+'], ['+myVal+']'+'\n')
        
    ####################################################################################################################################
    # final clean up
    profile['new_parameter'] = new_parameter                        ### use profile as piggyback to get parameters into determine_basal
    bg[-1] = glucose_status['glucose']                              ### just in case it got changed 
    global emulTarLow
    global emulTarHig
    emulTarLow[-1] = profile['min_bg']                              ### please do not touch
    emulTarHig[-1] = profile['max_bg']                              ### please do not touch

def getOrigPred(predBGs):
    Fcasts = {}
    for BGs in predBGs:
        Fcasts[BGs] = predBGs[BGs]
    #print ('orig preds --> '+str(Fcasts))
    return Fcasts

def TreatLoop(Curly, log, lcount):
    global SMBreason
    global loop_mills
    global loop_label
    global origInsReq
    global origSMB
    global emulSMB
    global origMaxBolus
    global emulMaxBolus
    global origBasal
    global lastBasal
    global Pred
    global FlowChart                                    # not used, for compatibilty with vary_settings_flow.py
    smb = json.loads(Curly)
    if 'openaps' in smb:                                # otherwise unknown source of entry
        suggest = smb['openaps']['suggested']
        reason = suggest['reason']
        if 'insulinReq' in suggest:
            log.write('\n========== DELTA in row ' + str(lcount) + ' SMB ==========\n')
            log.write('  created at= ' + smb['created_at'] + '\n')
            #printStr(smb, 'created_at', log)
            log.write(SMBreason['script'])               # the script debug section
            #printVal(suggest, 'bg', log)
            cob = round(suggest['COB'], 1)
            #log.write('  COB   =' + str(cob) + '\n')
            iob = round(suggest['IOB'], 1)
            key = 'insulinReq'
            ins_Req = suggest[key]
            #log.write('  ' + (key+'    ')[:6] + '=' + str(insReq) + '\n')
            if ins_Req > 0.0:                            # can be empty string; was >0.2 before
                mySMB  = getReason(reason, 'Microbolusing', 'U',  1)
                maxBol = getReason(reason, 'maxBolus',      '. ', 1)
                if len(maxBol) > 5 :
                    maxBol = getReason(reason, 'maxBolus',  '; ', 1)
            else:
                mySMB  = '0'
                maxBol = '0'
        else:
            ins_Req = 0
            mySMB  = '0'
            maxBol = '0'
        if mySMB == '' :    mySMB = '0'
        if maxBol== '' :    maxBol= '0'
        origSMB.append(eval(mySMB))
        origMaxBolus.append(eval(maxBol))
        log.write('---------- Reason --------------------------\n' + str(reason) + '\n')
        #thisTime = int(round(time.time() * 1000))                  # use as now() or the emulated execution tiume
        stmp = suggest['deliverAt']
        thisTime = ConvertSTRINGooDate(stmp)
        loop_mills.append(round(thisTime/1000, 1) )                 # from millis to secs
        loop_label.append(stmp[11:19] + stmp[-1])                   # include seconds to distinguish entries
        #print('len loop_mills='+str(len(loop_mills))+'; len labels='+str(len(loop_label)))
        tempReq = basalFromReason(smb, lcount)
        origBasal.append(round(eval(tempReq), 4))
        
        # now we can set the remaining iob data section
        last_temp = {}
        last_temp['typeof'] = 'dummy'                       # may be anything
        last_temp['date']   = thisTime - SMBreason['lastTempAge'] *60*1000   # copy from original logfile
        last_temp['rate']   = currenttemp['rate']
        last_temp['duration'] = currenttemp['duration']
        iob_data['lastTemp']= last_temp
        lastBasal.append(currenttemp['rate'])
        
        log = open(ce_file, 'a')
        log.write('\n========== '+varLabel+' loop in row ' + str(lcount) +' ==========\n')
        log.write('  created at= ' + stmp[:-5]+stmp[-1] +'\n')
        log.write('---------- Script Debug --------------------\n')
        log.close()
        #tempBasalFunctions = set_tempBasalFunctions()   # look up in profile
        reservoir = 47                                  # currently fixed
        tempBasalFunctionsDummy = ''                    # is handled inside determine_basal as import
        origInsReq.append(ins_Req)
        varlog.write('\nloop execution in row='+str(lcount)+' at= ' + smb['created_at'] + '\n')
        setVariant()
        Fcasts = getOrigPred(suggest['predBGs'])
        Flows  = []
        reT = detSMB.determine_basal(glucose_status, currenttemp, iob_data, profile, autosens_data, meal_data, tempBasalFunctionsDummy, True, reservoir, thisTime, Fcasts, Flows)  # last argument for compatibilty with future version
        reason = echo_rT(reT)                           # overwrite the original reason
        maxBolStr = getReason(reason, 'maxBolus', '. ', 1)
        if len(maxBolStr) > 5 :
            maxBolStr = getReason(reason, 'maxBolus',  '; ', 1)
        if maxBolStr == '' :     maxBolStr = '0'
        emulMaxBolus.append(eval(maxBolStr))
        mySMBstr = getReason(reason, 'Microbolusing', 'U',  1)
        if mySMBstr == '' :     mySMBstr = '0'
        emulSMB.append(eval(mySMBstr))

        if reason.find('COB: 0,') == 0: 
            Fcasts['COBpredBGs'] = []                   # clear array if COB=0
        Pred[round(thisTime/1000,1)] = Fcasts

        #next loop execution
        SMBreason = {}                                  # clear for next debug list
        SMBreason['script'] = '---------- Script Debug --------------------\n'

def PrepareSMB(zeile, log, lcount):
    # collect SMB detail echos before actual, compacted loop protocol comes
    global SMBreason
    key_str = '[LoggerCallback.jsFunction_log():39]'
    what_anf = zeile.find(key_str)
    what = zeile[what_anf+len(key_str)+2:]
    SMBreason['script'] += what
    if what.find('SMB enabled')==0:
        SMBreason['rowON'] = lcount
        SMBreason['whyON'] = what[:-1]
    elif what.find('disabling SMB')>0:
        SMBreason['rowOFF'] = lcount
        SMBreason['whyOFF'] = what[:-1]
    elif what.find('maxBolus: ')>0:
        SMBreason['maxSMB'] = what[-4:-1]
    elif what.find('gz maximSMB: from ')==0:
        SMBreason['maxBolus'] = what[:-1]
    elif what.find('currenttemp:')==0:                  # unclear source of TempAge, but should be the same in emulation
        wo_anf = what.find('lastTempAge:')
        wo_end = what.find(' m tempModulus:')
        SMBreason['lastTempAge'] = eval(what[wo_anf+13:wo_end])

def featured(Option):
    # check whethter this feature was in the option list passed from OO.odb
    # or if ALL option were enabled
    # otherwise FALSE
    OK = 'All' in doit  or Option in doit
    if '-'+Option in doit:        OK = False            # explicitly excluded
    return OK

def get_glucose_status(lcount, st) :                    # key = 80
    Curly = st[16:]
    global glucose_status
    global bg
    glucose_status = json.loads(Curly)
    glucose_status['row'] = lcount
    if len(bg)==len(loop_mills) :
        bg.append(glucose_status['glucose'])            # start next iteration
    else:
        bg[-1] = (glucose_status['glucose'])            # overwrite as last loop was not finished
    #print ('\nbg data found in row '+str(lcount)+', total count='+str(len(bg)))
    pass

def get_iob_data(lcount, st, log) :                     # key = 81
    Curly = st[16:-1]                                   # drop the <CRLF>
    global iob_data
    iob_array = json.loads(Curly)
    iob_data = {}
    iob_data['typeof']  = 'dummy'                       # may be anything
    # get first record as current iob
    rec_0 = iob_array[0]
    for ele in rec_0 :
        if ele != 'iobWithZeroTemp':        iob_data[ele] = rec_0[ele]
    iob_data['iobArray']= iob_array
    #print ('preliminary iob data json -->       '+str(lcount) +' : '+ str(iob_data))
    #for ele in iob_array:
    #    log.write(str(ele)+':'+'\n')
    #print ('iob data found in row '+str(lcount)+', total count='+str(len(iob_data)))
    pass

def get_currenttemp(lcount, st) :                       # key = 82
    Curly = st[16:]
    global currenttemp
    currenttemp = json.loads(Curly)
    currenttemp["typeof"] ="dummy"                      # may be anything
    currenttemp["row"] = lcount
    #print ('currenttemp json -->    '+str(currenttemp))
    pass

def get_profile(lcount, st) :                           # key = 83
    Curly = st[16:]
    global profile
    global origTarLow
    global origTarHig
    global emulTarLow
    global emulTarHig
    profile = json.loads(Curly)
    profile['maxDeltaRatio'] = 0.2                                              ### additional parameter; define standard
    profile['row'] = lcount
    # unknown source, use apparent default:
    profile['remainingCarbsFraction'] = 1
    #profile['temptargetSet'] = True                    # historical logfiles say FALSE             !!!!!!!!!!!!!!!!
    profile['sensitivity_raises_target'] = False        # missing from historical logfiles          !!!!!!!!!!!!!!!!
    if len(origTarLow)==len(loop_mills) :               # start next iteration
        origTarLow.append(profile['min_bg'])
        emulTarLow.append(origTarLow[-1])
        origTarHig.append(profile['max_bg'])
        emulTarHig.append(origTarHig[-1])
    else:                                               # overwrite as last loop was not finished
        origTarLow[-1] = profile['min_bg']
        emulTarLow[-1] = origTarLow[-1]
        origTarHig[-1] = profile['max_bg']
        emulTarHig[-1] = origTarHig[-1]
    #print ('master profile json in row '+str(lcount)+' --> '+str(profile))
    #print ('target data found in row '+str(lcount)+', total count origTarLow='+str(len(origTarLow)))
    #print ('target data found in row '+str(lcount)+', total count emulTarLow='+str(len(origTarLow)))
    pass

def get_meal_data(lcount, st) :                         # key = 84
    Curly = st[16:]
    global meal_data
    meal_data = json.loads(Curly)
    meal_data['row'] = lcount
    # use fixed settings for the time being ...
    meal_data['bwCarbs'] = False                        # bolus wizzard carbs
    meal_data['bwFound'] = False                        # bolus wizzard used ?
    #print ('meal data json -->      '+str(meal_data))
    pass

def get_autosens_data(lcount, st) :                     # key = 86
    Curly = st[16:]
    global autosens_data
    autosens_data = json.loads(Curly)
    autosens_data['typeof'] = 'dummy'                   # may be anything
    autosens_data['row'] = lcount
    #print ('autosens data json -->  '+str(autosens_data))
    pass

def ConvertSTRINGooDate(stmp) :
    # stmp is datetime string incl millis, i.e. like "2019-05-22T12:06:48.091Z"
    if stmp < "2019-10-27T03:00:00.000Z":
        dlst = 3600                                 #    dlst period summer 2019
    elif stmp < "2020-03-29T02:00:00.000Z":
        dlst = 0                                    # no dlst period winter 2019/20
    else:
        dlst = 3600                                 #    dlst period summer 2020
    MSJahr		= eval(    stmp[ 0:4])
    MSMonat		= eval('1'+stmp[ 5:7]) -100
    MSTag		= eval('1'+stmp[ 8:10])-100
    MSStunde	= eval('1'+stmp[11:13])-100
    MSMinute	= eval('1'+stmp[14:16])-100
    MSSekunde	= eval('1'+stmp[17:19])-100
    MSmillis    = eval('1'+stmp[20:23])-1000
    #print ('millis aus '+stmp+' = '+str(MSmillis))
    NumericDate= datetime.datetime(MSJahr, MSMonat, MSTag, MSStunde, MSMinute, MSSekunde, MSmillis*1000)
    #imestamp = NumericDate.replace(tzinfo=timezone.utc).timestamp() + 3600 # 1h MEZ offset
    timestamp = int( (NumericDate.timestamp() + 3600 + dlst) * 1000 )       # 1h MEZ offset
    #print("Eingang: " + stmp + "\nAusgang: " + str(timestamp) )
    return timestamp

def scanLogfile(fn):
    global SMBreason
    global xyf
    global varlog
    SMBreason = {}
    SMBreason['script'] = '---------- Script Debug --------------------\n'
    entriesSGV = {}
    found_SGV = 0
    xyf = open(fn + '.' + varLabel + '.tab', 'w')
    varlog = open(fn + '.' + varLabel + '.log', 'w')
    varlog.write('Echo of what-if definitions actioned for variant '+varLabel+' created on '+formatdate(localtime=True) + '\n')
    log = open(fn + '.orig.txt', 'w')
    log.write('AAPS scan from AAPS Logfile for SMB comparison created on ' + formatdate(localtime=True) + '\n')
    log.write('FILE='+fn + '\n')
    dataType_offset = 1                         #################### used for V2.6.1
    global lcount
    lcount  = 0
    lf = open(fn, 'r')
    notEOF = True                               # needed because "for zeile in lf" does not work with AAPS 2.5
    
    while notEOF:                               # needed because "for zeile in lf" does not work with AAPS 2.5
        try:                                    # needed because "for zeile in lf" does not work with AAPS 2.5
            zeile = lf.readline()               # needed because "for zeile in lf" does not work with AAPS 2.5
            if zeile == '':                     # needed because "for zeile in lf" does not work with AAPS 2.5
                notEOF = False                  # needed because "for zeile in lf" does not work with AAPS 2.5
                break                           # needed because "for zeile in lf" does not work with AAPS 2.5
            lcount +=  1
            if len(zeile)>13:
                headerKey = zeile[2] + zeile[5] + zeile[8] + zeile[12]
                if headerKey == '::. ':
                    sLine = zeile[13:]
                    Action = hole(sLine, 0, '[', ']')
                    sOffset = len(Action)
                    Block2 = hole(sLine, 1+sOffset, '[', ']')
                    if Block2 == '[DataService.onHandleIntent():54]' \
                    or Block2 == '[DataService.onHandleIntent():55]':       # token :54 added for AAPS version 2.5
                        pass
                    elif Block2[:-3] == '[DetermineBasalAdapterSMBJS.invoke():':  # various input items for loop
                        dataStr = sLine[sLine.find(']: ')+3:]
                        dataType = eval(Block2[len(Block2)-3:-1])           # extract last 2 digits as type key
                        if   dataType == 79 :                               # start counter in V2.5.1 only
                            dataType_offset = 0                             #################### used for V2.5.1
                        elif dataType == dataType_offset+80 :               get_glucose_status(lcount, dataStr)
                        elif dataType == dataType_offset+81 :               get_iob_data(lcount, dataStr, log)
                        elif dataType == dataType_offset+82 :               get_currenttemp(lcount, dataStr)
                        elif dataType == dataType_offset+83 :               get_profile(lcount, dataStr)
                        elif dataType == dataType_offset+84 :               get_meal_data(lcount, dataStr)
                        elif dataType == dataType_offset+86 :               get_autosens_data(lcount, dataStr)
                    elif Block2 == '[LoggerCallback.jsFunction_log():39]':  # script debug info from console.error
                        PrepareSMB(sLine, log, lcount)   
                    elif Block2 == '[DbLogger.dbAdd():29]':                 ################## flag for V2.5.1
                        Curly =  hole(sLine, 1+sOffset+len(Block2), '{', '}')
                        if Curly.find('{"device":"openaps:')==0:   TreatLoop(Curly, log, lcount)
                elif zeile.find('data:{"device":"openaps:') == 0 :          ################## flag for V2.6.1
                    Curly =  hole(zeile, 5, '{', '}')
                    #print('calling TreatLoop in row '+str(lcount)+' with\n'+Curly)
                    if Curly.find('{"device":"openaps:')==0:   TreatLoop(Curly, log, lcount)
        except UnicodeDecodeError:              # needed because "for zeile in lf" does not work with AAPS 2.5 containg non-ASCII codes
            lcount +=  1                        # skip this line, it contains non-ASCII characters!
            
    lf.close()
    log.write('ENDE\n')
    log.close()
    varlog.close()

def echo_rT(reT):                                       # echo the unusual SMB result
    global emulInsReq
    global emulBasal
    log = open(ce_file, 'a')
    #log.write ('\nreT --> '+str(reT)+'\n')
    
    if 'error' in reT :
        print ('returned "error" with ...\n  ' + reT['error'])
        reason = reT['error']
    elif 'setTempBasal' in reT:                        # normal finish
        sub_names = ['rate', 'duration', 'profile', 'rT', 'currenttemp']
        ele = reT['setTempBasal']
        reason = ele[3]['reason']
        log.write('---------- Reason --------------------------\n' + str(reason) + '\n')
        emulInsReq.append(ele[3]['insulinReq'])
        emulBasal.append(max(0,ele[0]))
    elif 'reason' in reT:                               # normal finish
        reason = reT['reason']
        log.write('---------- Reason --------------------------\n' + str(reason) + '\n')
        emulInsReq.append(reT['insulinReq'])
        tempReq = basalFromEmulation(reT, lcount)
        emulBasal.append(eval(tempReq))
    else :
        print ('returned "unexpected content" with ...\n  ' + str(reT))
        reason = str(reT)

    log.close()
    return reason

def BGValPlot(ax2, BGcount, BGtype, BGlevel, BGedge, BGcol):
    BGarrow = dict(arrowstyle='-', fc=BGcol, ec=BGcol, linestyle='dotted')
    posBG   = (BGlevel, BGedge+2000+400*BGcount)                        # vertical position of BG name
    posLine = (BGlevel, BGedge+   0)                                    # vertical pos of fcast block
    ax2.annotate(BGtype, xy=posLine, xytext=posBG, ha='center',
                        arrowprops=BGarrow, color=BGcol)

def XYplots(loopCount) :
    # ---   ensure that last loop was finished  -------------
    if len(loop_mills) < len(bg)            :   bg.pop()
    if len(loop_mills) < len(origTarLow)    :   origTarLow.pop()
    if len(loop_mills) < len(origTarHig)    :   origTarHig.pop()
    if len(loop_mills) < len(origInsReq)    :   origInsReq.pop()
    if len(loop_mills) < len(origMaxBolus)  :   origMaxBolus.pop()
    if len(loop_mills) < len(origSMB)       :   origSMB.pop()
    if len(loop_mills) < len(origBasal)     :   origBasal.pop()
    
    if len(loop_mills) < len(emulTarLow)    :   emulTarLow.pop()
    if len(loop_mills) < len(emulTarHig)    :   emulTarHig.pop()
    if len(loop_mills) < len(emulInsReq)    :   emulInsReq.pop()
    if len(loop_mills) < len(emulMaxBolus)  :   emulMaxBolus.pop()
    if len(loop_mills) < len(emulSMB)       :   emulSMB.pop()
    if len(loop_mills) < len(emulBasal)     :   emulBasal.pop()
    # ---   plot the comparisons    -------------------------
    if loopCount <= 30 :                                                                # step size for y-axis (time)
        yStep = 3       # every 15 minutes
    else :
        yStep = 6       # every 30 minutes#
    yTicks = []
    yLabels= []
    
    for i in range(0, loopCount, yStep) :                                               # the time labels
        yTicks.append(loop_mills[i])
        yLabels.append(loop_label[i])
    if loop_mills[-1] != yTicks[-1]:
        yTicks.append(loop_mills[-1])                                            # last tick could be missed out
        yLabels.append(loop_label[-1])
    if featured('pred'):                                                                # extend time axis for predictions
        for i in range(30, 241, 30):
            yTicks.append(loop_mills[-1]+i*60)                                   # append 4 hours
            yLabels.append('+'+str(i)+'mins')
        maxframes = len(loop_mills)
    else:
        maxframes = 1
    thickness = (loop_mills[-1]-loop_mills[0])/loopCount/4

    plt.rcParams['savefig.dpi'] = 200
    plt.rcParams['figure.figsize'] = (9, 12)                                            # h,w in inches
    plt.rcParams['figure.dpi'] = 200
    plt.rcParams['legend.fontsize'] = 'small'
    plt.rcParams['legend.facecolor'] = 'grey'
    plt.rcParams['font.size'] = 8
    colFav = {'bg':'red', 'ZT':'cyan', 'IOB':'blue', 'COB':'orange', 'UAM':'brown'}

    pdfFile = fn + '.' + varLabel + '.pdf'
    pdfCleared = False
    while True:                                                                         # wait if old pdf is still loaded in pdf viewer
        try:
            os.remove(pdfFile)
            if pdfCleared:    print('continuing ...')
            break
        except PermissionError:
            asleep = 10
            print('Your graphics file seems blocked by other process. Checking again in '+str(asleep)+' sec.'+chr(7)) # sometimes I can hear that BELL
            time.sleep(asleep)
            pdfCleared=True
        except FileNotFoundError:
            break

    with PdfPages(pdfFile) as pdf:
        for iFrame in range(0, maxframes):                                              # the loop instances
            fig, ax1 = plt.subplots()                                                   # holds insulin values
            fig.suptitle('Compare original "' + fn + '" vs emulation case "' + varLabel + '"')
            if featured('insReq') or featured('maxBolus') or featured('SMB') or featured('basal') : # annotate the insulin axis
                ax1.xaxis.label.set_color('blue')
                ax1.tick_params(axis='x', colors='blue')
                ax1.set_xticks([-1, 0.0, 1.0, 2.0, 4.0])
                ax1.set_xticklabels(['-1.0', '0.0', '1.0', '2.0', '4.0'])
                ax1.set_xlabel('insulin')
                ax1.set_xlim(-1, 6)
            else :
                ax1.set_xticks([0,1])
                ax1.set_xticklabels(['',''])                                            # dummy axis labels
            ax1.set_ylim(loop_mills[-1]+thickness*2, loop_mills[0]-thickness*2)         # add thickness*2 so markers fit into plot frame
            ax1.set_yticks(yTicks)
            ax1.set_yticklabels(yLabels)
            
            ax2 = ax1.twiny()                                                           # holds bg and target graphs
            if featured('bg') or featured('target') or featured('pred') :               # annotate the bg axis
                ax2.set_xlim(-150, 250)                                                 # reserve (-150,0) space for insulin graphs
                ax2.set_xlabel('                   glucose')
                ax2.xaxis.label.set_color('red')
                ax2.tick_params(axis='x', colors='red')
                ax2.set_xticks([0, 50, 100, 150, 200, 250])                             # don't show negative labels
                ax2.set_xticklabels(['0', '50', '100', '150', '200', '250'])
            else :
                ax2.set_xticks([0,1])
                ax2.set_xticklabels(['',''])                                            # dummy axis labels
            if featured('pred') :                                                       # set scale of y-axis (time)
                ax2.set_ylim(loop_mills[-1]+thickness*2+48*5*60, loop_mills[0]-thickness*2)
            else : 
                ax2.set_ylim(loop_mills[-1]+thickness*2, loop_mills[0]-thickness*2)

            if featured('bg') or featured('target') or featured('pred') :               # group of bg plots
                if featured('target') :                                                 # plot targets
                    ax2.plot(emulTarHig, loop_mills, linestyle='None',   marker='o', color='black',  label='target high, emulated')
                    ax2.plot(emulTarLow, loop_mills, linestyle='None',   marker='o', color='black',  label='target  low, emulated')
                    ax2.plot(origTarHig, loop_mills, linestyle='dashed', marker='.', color='yellow', label='target high, original')
                    ax2.plot(origTarLow, loop_mills, linestyle='dashed', marker='.', color='yellow', label='target  low, original')

                if featured('bg') :                                                     # plot bg
                    ax2.plot(bg,         loop_mills, linestyle='solid',  marker='o', color='red',    label='blood glucose')
        
                if featured('pred') :                                                   # plot the predictions
                    thisTime = loop_mills[iFrame]
                    loopCount = 48+1
                    fcastmills = []
                    for lp in range(loopCount):
                        fcastmills.append(round(thisTime/1.000 + lp*5*60, 1 ))          # from millis to secs
                    bbox_props = dict(boxstyle='larrow', fc='grey')                     # slider with time label
                    ax2.text(-143, fcastmills[0], loop_label[iFrame], va='center', size=8, bbox=bbox_props)
                    #ax2.plot([-999,999], [fcastmills[0],fcastmills[0]], linestyle='dotted', color='grey', lw=0.5)             # time line
                    ax2.fill_between([-150,250], fcastmills[0]-2*thickness, fcastmills[-1]+2*thickness, fc='grey', alpha=0.6)  # time window
                    Fcasts = Pred[thisTime]
                    Levels = Fcasts['Levels']

                    #print (str(loop_label[iFrame]), str(Levels))
                    if 'minPredBG'    in Levels:
                        BGValPlot(ax2,-1, 'minPredBG',    Levels['minPredBG'],    fcastmills[-1], colFav['bg'])
                    if 'minZTGuardBG' in Levels:
                        BGValPlot(ax2, 1, 'minZTGuardBG', Levels['minZTGuardBG'], fcastmills[-1], colFav['ZT'])
                    if 'minIOBPredBG' in Levels:
                        BGValPlot(ax2, 2, 'minIOBPredBG', Levels['minIOBPredBG'], fcastmills[-1], colFav['IOB'])
                    if 'minCOBPredBG' in Levels:
                        BGValPlot(ax2, 3, 'minCOBPredBG', Levels['minCOBPredBG'], fcastmills[-1], colFav['COB'])
                    if 'minUAMPredBG' in Levels:
                        BGValPlot(ax2, 4, 'minUAMPredBG', Levels['minUAMPredBG'], fcastmills[-1], colFav['UAM'])
                    if 'avgPredBG'    in Levels:
                        BGValPlot(ax2, 0, 'avgPredBG',    Levels['avgPredBG'],    fcastmills[-1], 'black')
                    if 'naive_eventualBG'    in Levels:
                        BGValPlot(ax2,-2, 'naive_eventualBG', Levels['naive_eventualBG'], fcastmills[-1], 'purple')
                    if 'eventualBG'    in Levels:
                        BGValPlot(ax2,-3, 'eventualBG', Levels['eventualBG'], fcastmills[-1], 'green')
                    
                    if 'SMBoff' in Levels:
                        SMBmsg = 'SMB disabled: ' + Levels['SMBoff']
                        threshold = Levels['value']
                        label = Levels['type']
                        SMBsource = Levels['source']
                        couleur = colFav[SMBsource]
                        minGuardBG = Levels['minGuardBG1']                                  # get main/only contributioon
                        SMBarrow = dict(arrowstyle='<|-|>', fc=couleur, ec=couleur)
                        if label == 'maxDelta' :
                            Tmin = thisTime - 3*5*60
                            Tmax = thisTime + 3*5*60
                            posText = (minGuardBG+5, thisTime)
                            posArrow= (threshold, thisTime)
                        else:                                                               # why SMB is disabled
                            Tmin = fcastmills[0]
                            Tmax = fcastmills[-1]
                            when_mills = Levels['timePos']
                            if minGuardBG < -150 :                                          # off screen location supresses all
                                minGuardBG = -130
                                SMBarrow = dict(arrowstyle='<|-', fc=couleur, ec=couleur)
                                ax2.plot([-150,-130], [fcastmills[when_mills],fcastmills[when_mills]], linestyle='dotted', color=couleur)
                            #print(str(iFrame), str(len(fcastmills)), str(fcastmills[-1]), str(Levels))
                            posText = (threshold+5, fcastmills[when_mills])
                            posArrow= (minGuardBG,  fcastmills[when_mills])
                        ax2.plot([threshold,threshold], [Tmin,Tmax], linestyle='dashed', color='grey', label=label)
                        if not 'source2' in Levels:                                         # single source
                            ax2.annotate(SMBmsg, xy=posArrow, xytext=posText, va='center',
                                            arrowprops=SMBarrow )                           # no alignment option: va='center') )
                        else:                                                               # blended minGuard case !
                            SMBsource2  = Levels['source2']
                            minGuardBG2 = Levels['minGuardBG2']
                            hub_bg   = Levels['minGuardBG']                                 # bg position of hub for "balance"
                            couleur2 = colFav[SMBsource2]
                            when_mills2 = Levels['timePos2']
                            share2 = (minGuardBG2-hub_bg)/(minGuardBG2-minGuardBG)          # fraction of BG2
                            hub_mills = fcastmills[when_mills2]+(fcastmills[when_mills]-fcastmills[when_mills2])*share2   # time of hub for "balance"
                            posText = (threshold+5, hub_mills)
                            posArrow= (hub_bg,  hub_mills)
                            ax2.annotate(SMBmsg, xy=posArrow, xytext=posText, va='center',
                                            arrowprops=SMBarrow )                           # no alignment option: va='center') )
                            ax2.plot((hub_bg,minGuardBG2), (hub_mills,fcastmills[when_mills2]),
                                linestyle='dotted',  marker='o', color=couleur2)            # plozt the lever arm of lesser contribution
                            ax2.plot((hub_bg,minGuardBG), (hub_mills,fcastmills[when_mills]), 
                                linestyle='dotted',  marker='o', color=couleur)             # plot the lever arm of lesser contribution
                    else:
                        SMBsource = ''
                        ax2.plot([0,0], [0,0], linestyle='dashed', color='grey', label='...')# inactive, i.e. off screen; placeholder for legend
    
                    if 'COB' in Fcasts:                                                 # assume same logic as in original
                        origCOB = Fcasts['COB']                                             # the initial array before cleanup
                        initCOB = Fcasts['COBinitBGs']                                      # the initial array before cleanup
                        predCOB = Fcasts['COBpredBGs']                                      # is empty if COB=0
                        ax2.plot(origCOB, fcastmills[:len(origCOB)], linestyle='solid',            color=colFav['COB'], label='predCOB, original')
                        ax2.plot(initCOB, fcastmills[:len(initCOB)], linestyle='None', marker='.', color=colFav['COB'], fillstyle='none')
                        ax2.plot(predCOB, fcastmills[:len(predCOB)], linestyle='None', marker='.', color=colFav['COB'], label='predCOB, emulated')
                    else:
                        ax2.plot([0,0], [0,0],                       linestyle='none',             color=colFav['COB'], label='no COB active') # inactive
                    
                    if 'UAM' in Fcasts or 'UAM'==SMBsource:                             # same logic as in original or minGuard source
                        origUAM = Fcasts['UAM']                                             # the initial array before cleanup
                        initUAM = Fcasts['UAMinitBGs']                                      # the initial array before cleanup
                        predUAM = Fcasts['UAMpredBGs']
                        ax2.plot(origUAM, fcastmills[:len(origUAM)], linestyle='solid',            color=colFav['UAM'], label='predUAM, original')
                        ax2.plot(initUAM, fcastmills[:len(initUAM)], linestyle='None', marker='.', color=colFav['UAM'], fillstyle='none')
                        ax2.plot(predUAM, fcastmills[:len(predUAM)], linestyle='None', marker='.', color=colFav['UAM'], label='predUAM, emulated')
                    else:
                        ax2.plot([0,0], [0,0],                       linestyle='none',             color=colFav['UAM'], label='no UAM active') # inactive
        
                    if 'IOB' in Fcasts:                                                 # assume same logic as in original
                        origIOB = Fcasts['IOB']                                             # the initial array before cleanup
                        initIOB = Fcasts['IOBinitBGs']                                      # the initial array before cleanup
                        predIOB = Fcasts['IOBpredBGs']
                        ax2.plot(origIOB, fcastmills[:len(origIOB)], linestyle='solid',            color=colFav['IOB'], label='predIOB, original')
                        ax2.plot(initIOB, fcastmills[:len(initIOB)], linestyle='None', marker='.', color=colFav['IOB'], fillstyle='none')
                        ax2.plot(predIOB, fcastmills[:len(predIOB)], linestyle='None', marker='.', color=colFav['IOB'], label='predIOB, emulated')
                    else:
                        ax2.plot([0,0], [0,0],                       linestyle='none',             color=colFav['IOB'], label='no IOB active') # inactive
    
                    if 'ZT' in Fcasts:                                                  # assume same logic as in original
                        origZT = Fcasts['ZT']                                               # from the orig loop
                        initZT = Fcasts['ZTinitBGs']                                        # the initial array before cleanup
                        predZT = Fcasts['ZTpredBGs']
                        ax2.plot(origZT,  fcastmills[:len(origZT)],  linestyle='solid',            color=colFav['ZT'],  label='predZT, original')
                        ax2.plot(initZT,  fcastmills[:len(initZT)],  linestyle='None', marker='.', color=colFav['ZT'],  fillstyle='none')
                        ax2.plot(predZT,  fcastmills[:len(predZT)],  linestyle='None', marker='.', Color=colFav['ZT'],  label='predZT, emulated')
                    else:
                        ax2.plot([0,0], [0,0],                       linestyle='none',             color=colFav['ZT'],  label='no ZT  active') # inactive
                    
                ax2.legend(loc='lower right')

            if featured('insReq') or featured('maxBolus') or featured('SMB') or featured('basal') : # group of insulin plots
                if featured('insReq') :
                    ax1.plot(emulInsReq, loop_mills, linestyle='None',  marker='o', color='red',   label='insulin Req, emulated')
                    ax1.plot(origInsReq, loop_mills, linestyle='solid', marker='.', color='orange',label='insulin Req, original')
                if featured('maxBolus') :
                    ax1.plot(emulMaxBolus,loop_mills,linestyle='None',  marker='o', color='green', label='maxBolus, emulated')
                    ax1.plot(origMaxBolus,loop_mills,linestyle='solid',             color='green', label='maxBolus, orig')
                if featured('SMB') :
                    ax1.plot(emulSMB,    loop_mills, linestyle='None',  marker='o', color='black', label='SMB, emulated')
                    ax1.plot(origSMB,    loop_mills, linestyle='solid', marker='.', color='yellow',label='SMB, original')
                if featured('basal') :
                    ax1.barh(y=loop_mills, height=thickness*2, width=emulBasal,     color='white', label='tempBasal, emulated', edgecolor='blue')
                    ax1.barh(y=loop_mills, height=thickness  , width=origBasal,     color='blue',  label='tempBasal, original')

                ax1.plot([0,0], [loop_mills[0],loop_mills[-1]], linestyle='dotted', color='black')  # grid line for insulin=0                
                if featured('pred') :                                                       # where to place the insulin legend
                    ax1.legend(loc='lower left')
                else :
                    ax1.legend(loc='upper right')
            
            pdf.savefig()
            if not featured('pred'):            plt.show()
            plt.close()                         # end of current page
        #pdf.close()                            # not needed due to "with ..." method triggered above
        pass

####    start of main   #########################
    
myseek= sys.argv[1] #+ '\\'
myfile = ''
arg2 = sys.argv[2]                              # the feature list what to plot
arg2 = arg2.replace('_', ' ')                   # get rid of the UNDERSCOREs
doit = arg2.split('/')
varLabel = sys.argv[3]                          # the variant label
if varLabel[len(varLabel)-4:] == '.dat' :       # drop the tail coming from DOS type ahead
    varLabel = varLabel[:-4]

loop_mills  = []
loop_label  = []
bg          = []
origTarLow  = []
emulTarLow  = []
origTarHig  = []
emulTarHig  = []

origInsReq  = []
emulInsReq  = []
origSMB     = []
emulSMB     = []
origMaxBolus= []
emulMaxBolus= []
origBasal   = []
emulBasal   = []
lastBasal   = []

Pred        = {}                                # holds all loop predictions

logListe = glob.glob(myseek+myfile, recursive=False)
for fn in logListe:
    ce_file = fn + '.' + varLabel + '.txt'
    cel = open(ce_file, 'w')
    cel.write('AAPS scan from ' + varLabel + ' for SMB comparison created on ' + formatdate(localtime=True) + '\n')
    cel.write('FILE='+fn + '\n')
    cel.close()
    my_ce_file(ce_file)                                 # exports name to determine_basal.py
    scanLogfile(fn)
    
loopCount = len(loop_mills)
if loopCount == 0 :
    print ('no such logfile: "'+myseek+'"')
    sys.exit()

# ---   print the comparisons    -------------------------
head= "                                  ------target------    insulin Req     -maxBolus-     ---SMB---     ---tmpBasal---\n" \
    + "id    time    --UNIXtime--   bg     orig      emul      orig   emul      orig emul     orig emul       orig    emul"
print('\n' + head)
xyf.write(head + '\n')

origBasalint = 0.0
emulBasalint = 0.0
origSMBsum = 0.0
emulSMBsum = 0.0
for i in range(loopCount) :
    tabz= f'{i:>2} {loop_label[i]} {loop_mills[i]:>13} {bg[i]:>4}  {origTarLow[i]:>4}-{origTarHig[i]:>3}  {emulTarLow[i]:>4}-{emulTarHig[i]:>3} ' \
        + f'{origInsReq[i]:>8} {emulInsReq[i]:>6} ' \
        + f'{origMaxBolus[i]:>9} {emulMaxBolus[i]:>4} {origSMB[i]:>8} {emulSMB[i]:>4} ' \
        + f'{origBasal[i]:>10} {emulBasal[i]:>7}' 
    print(tabz)
    origSMBsum += origSMB[i]
    emulSMBsum += emulSMB[i]
    if i==loopCount-1:                    # last time step
        fraction = 5 / 60               # next 5 min per hour
    else:
        fraction = (loop_mills[i+1] - loop_mills[i]) / 3600
    #print (str(fraction*60))
    origBasalint += origBasal[i]*fraction
    emulBasalint += emulBasal[i]*fraction        
    xyf.write(tabz + '\n')

sepLine = ''
for i in range(115):
    sepLine += '-'
tabz = 'Totals:'+f'{round(origSMBsum,1):>84} {round(emulSMBsum,1):>4} {round(origBasalint,2):>10} {round(emulBasalint,2):>7}'
print(sepLine + '\n' + tabz)
xyf.write(sepLine + '\n' + tabz + '\n')
xyf.close()

XYplots(loopCount)

sys.exit()
