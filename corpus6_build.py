#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Sep  5 21:05:01 2020
all roots-kwn,kyf,hayth,kol,+proper names(even proper names that have roots also is like roots)
@author: asus
"""
"from copy import copy"
from os import makedirs as os_makedirs
from os.path import exists as os_exist
def createFolder(directory):
    try:
        if not os_exist(directory):
            os_makedirs(directory)
    except OSError:
        print ('Error: Creating directory. ' +  directory)
cs = 2   
moslemLs = ['m~usolimap', 'musolima`t', 'musolim', '>asolama' , '<isola`m']
a=open('./quranic-corpus-morphology-0.4.txt','r')
ac = a.readlines()
a.close()
oldch = 1
oldsv = 1
chtxt = ''
lem = []
roots = []
PNs100 = []
uniNPN = []
c = open('./uniLm.txt','r')
accept0 = c.readlines()
accept = []
c.close()
for s in accept0:
    accept.append(s[:-2])
alphab = []
delL = []
mrych = []
slmroot = []
jnnFamily  = []
"noR = []"
if cs ==1:
    createFolder('./q_RsomeL')    
    "from copy import copy"
    for i in range(58,128276):
        acc = ac[i].split('\t')
        "del \n:"   
        acc[3] = acc[3][0:-1]
        acch = acc[0].split(':')
        if int(acch[0][1:]) == oldch+1:
            for chr0 in chtxt:
                if chr0 not in alphab:
                    alphab.append(chr0)
            b = open('./q_RsomeL/q_RsomeL_'+str(oldch)+'.txt','w')
            if oldch not in [1,9]:
                chtxt = 'smw Alh rHm rHm \n'+chtxt
            b.write(chtxt)
            b.close()
            oldch += 1
            oldsv = 1
            chtxt = ''
        if int(acch[1]) == oldsv+1:
            chtxt += '\n'
            oldsv +=1
        "hasRoot?"
        if (acc[3].find('ROOT:') > -1):
            chtxt += acc[3][acc[3].find('ROOT:')+5:].split('|')[0]+' '
            if acc[3][acc[3].find('ROOT:')+5:].split('|')[0] not in roots:
                roots.append(acc[3][acc[3].find('ROOT:')+5:].split('|')[0])
            """if acc[2] == 'INTG':
                if acc[3][acc[3].find('ROOT:')+5:].split('|')[0] not in rootscheck:
                    rootscheck.append(acc[3][acc[3].find('ROOT:')+5:].split('|')[0])
                    print(acc)"""
        else:
            "hasLem?"
            if acc[3].find('LEM:') > -1:
                lemCand = acc[3][acc[3].find('LEM:')+4:].split('|')[0]
                """if lemCand == 'maroyam':
                    mrych.append(acch[0][1:])"""
                if lemCand in accept:
                    if lemCand == '*aA ':
                        lemCand = '*uw '
                    else:
                        if lemCand == 'ladaY ':
                            lemCand = 'laday '
                        """else:
                            if lemCand == 'l~aEal~ ':
                                lemCand = 'laEal~ '"""
                    """if lemCand == 'yawoma}i* ':
                        lemCand = 'ywm '"""
                    chtxt += lemCand+' '
                    if lemCand+' ' not in lem:
                        lem.append(lemCand+' ')
                else:
                    if lemCand+' ' not in delL:
                        delL.append(lemCand+' ')
                """else:
                    chtxt += acc[1]+' '
                    if acc[1] not in nolem:
                        nolem.append(acc[1])
                    if acc[2] != 'PRON':
                        if acc[1] not in notPron:
                            notPron.append(acc[1])
                            print acc"""
        b = open('./q_RsomeL/q_RsomeL_'+str(oldch)+'.txt','w')
        b.write('smw Alh rHm rHm \n'+chtxt)
        b.close()
        b =open('./q_RsomeL/uniqlems.txt','w')
        for i in lem:
            b.write(i+'\n')
        b.close()
        b =open('./q_RsomeL/not_considered.txt','w')
        for i in delL:
            b.write(i+'\n')
        b.close()
        b =open('./q_RsomeL/uniqueRoots.txt','w')
        for i in roots:
            b.write(i+'\n')
        b.close()
        b =open('./q_RsomeL/alphabet.txt','w')
        for i in alphab:
            b.write(i+'\n')
        b.close()
else:
    if cs == 2:
        createFolder('./q_PNR-spKaAn-4')    
        for i in range(58,128276):
            acc = ac[i].split('\t')
            "del \n:"   
            acc[3] = acc[3][0:-1]
            acch = acc[0].split(':')
            if int(acch[0][1:]) == oldch+1:
                for chr0 in chtxt:
                    if chr0 not in alphab:
                        alphab.append(chr0)
                b = open('./q_PNR-spKaAn-4/q_PNR-spKaAn-4_'+str(oldch)+'.txt','w')
                if oldch not in [1,9]:
                    chtxt = 'smw {ll~ah rHm rHm \n'+chtxt
                b.write(chtxt)
                b.close()
                oldch += 1
                oldsv = 1
                chtxt = ''
            if int(acch[1]) == oldsv+1:
                chtxt += '\n'
                oldsv +=1
            "is proper names:"
            """if acc[3].find('ROOT:jnn') >-1:
                jnnlem = acc[3][acc[3].find('LEM:')+4:].split('|')[0]
                if jnnlem not in jnnFamily: 
                    jnnFamily.append(jnnlem)"""
            ln = acc[3].find('POS:PN')
            if ln !=-1:
                lm = acc[3].find('LEM:')
                if lm != -1:
                    lemCand0 = acc[3][lm+4:lm+acc[3][lm:].find('|')]
                    "merge the lemma {ll~ahum~a with the lemma '{ll~ah'"
                    if lemCand0.find('{ll~ahum~a') != -1: lemCand0 = '{ll~ah'
                    "pn Islam family"
                    if lemCand0 in moslemLs:
                        lemCand0 = '<isola`m'
                    "root $Tn is special for pn $Tn family "
                    if acc[3].find('ROOT:') > -1:
                        if acc[3].find('ROOT:$Tn')>-1:
                            lemCand0 = '$Tn'
                    "huwd"
                    if acc[3].find('ROOT:hwd') > -1:
                        if acc[3].find('LEM:huwd|') > -1:
                            lemCand0 = 'huwd'
                        else:
                            lemCand0 = 'hwd'
                    if acc[3].find('yahuwdiy~')>-1:
                        lemCand0 = 'hwd'
                    "'ja`hiliy~ap2'"
                    if acc[3].find('LEM:ja`hiliy~ap2')>-1:
                        lemCand0 = 'jhl'
                    if lemCand0+' ' not in lem:
                        lem.append(lemCand0+' ')
                    if lemCand0 not in PNs100:
                        PNs100.append(lemCand0)
                    chtxt += lemCand0+' '
                """"else:"
                    "print('Error! noLem:',acc)"""
            else:         
                "hasRoot?"
                if (acc[3].find('SP:kaAn') > -1):
                    continue
                if (acc[3][acc[3].find('ROOT:')+5:].split('|')[0] in ['kyf','Hyv']):
                    continue
                if acc[3].find('ROOT:kll')>-1:  
                    if acc[3].find('LEM:kala`lap')>-1:
                        print('kll')
                    else:
                        if acc[3].find('LEM:kal~|ROOT:kll')>-1:
                            print('kll')
                        else:
                            if (acc[3].find('LEM:kul~amaA|') | acc[3].find('LEM:kul~|')) == 0:
                                print('Error in Kul',acc)
                            else:
                                continue
                if acc[3].find('LEM:>an~aY`|ROOT:Any')>-1:
                    continue
                if (acc[3].find('ROOT:') > -1):
                    lemCand1 = acc[3][acc[3].find('ROOT:')+5:].split('|')[0]+' '
                    if acc[3][acc[3].find('ROOT:')+5:].split('|')[0] == 'slm':
                        slmL = acc[3][acc[3].find('LEM:')+4:].split('|')[0]
                        if slmL not in slmroot:
                            slmroot.append(slmL)
                        if slmL in moslemLs:
                            lemCand1 = '<isola`m ' 
                    if acc[0].find('(7:156:10:1)') > -1:
                        lemCand1 = 'hwd2 '
                    chtxt += lemCand1
                    if acc[3][acc[3].find('ROOT:')+5:].split('|')[0] not in roots:
                        roots.append(acc[3][acc[3].find('ROOT:')+5:].split('|')[0])
                    lmx = acc[3].find('LEM:')
                    if lmx>-1:
                        if acc[3][lmx+4:].split('|')[0] in PNs100:
                            if acc[3][lmx+4:].split('|')[0]  not in uniNPN:
                                uniNPN.append(acc[3][lmx+4:].split('|')[0])
                            "print('also noun(root):',acc[3][lmx+4:].split('|')[0],'\n',acc)"
                    """
                    if acc[2] == 'INTG':
                        if acc[3][acc[3].find('ROOT:')+5:].split('|')[0] not in rootscheck:
                            rootscheck.append(acc[3][acc[3].find('ROOT:')+5:].split('|')[0])
                            print(acc)
                    """
                    """
                else:
                    if acc[3].find('LEM:') > -1:
                        lemCand = acc[3][acc[3].find('LEM:')+4:].split('|')[0]
                        if lemCand not in noR:
                            if acc[3].find('POS:PN') <0:
                                noR.append(lemCand)"""
                else:
                    
                    "hasLem?"
                    if acc[3].find('LEM:') > -1:
                        lemCand = acc[3][acc[3].find('LEM:')+4:].split('|')[0]
                        if lemCand in accept:
                            if lemCand == '*aA':
                                lemCand = '*uw'
                            else:
                                if lemCand == 'ladaY':
                                    lemCand = 'laday'
                            """if lemCand == 'yawoma}i*':
                                lemCand = 'ywm'"""
                            chtxt += lemCand+' '
                            if lemCand+' ' not in lem:
                                lem.append(lemCand+' ')
                        else:
                            if lemCand+' ' not in delL:
                                delL.append(lemCand+' ')
                        if lemCand in PNs100:
                            print('also noun(lem):',lemCand,acc)
        b = open('./q_PNR-spKaAn-4/q_PNR-spKaAn-4_'+str(oldch)+'.txt','w')
        b.write('smw {ll~ah rHm rHm \n'+chtxt)
        b.close()
        b =open('./q_PNR-spKaAn-4/uniqlems.txt','w')
        for i in lem:
            b.write(i+'\n')
        b.close()
        b =open('./q_PNR-spKaAn-4/uniqueRoots.txt','w')
        for i in roots:
            b.write(i+'\n')
        b.close()
        b =open('./q_PNR-spKaAn-4/alphabet.txt','w')
        for i in alphab:
            b.write(i+'\n')
        b.close()
    
"""
    if acc[3].find('Root')>-1:
        "has root:"
        """
        
        
