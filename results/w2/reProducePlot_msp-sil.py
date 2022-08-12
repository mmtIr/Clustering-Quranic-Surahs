#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Oct  4 14:18:33 2020

@author: asus
Reproduce minimum support-silhouette score plot
"""
from bidi.algorithm import get_display
from arabic_reshaper import reshape as ar_reshape
import matplotlib.pyplot as plt

def make_farsi_text(text_to_be_reshaped):
    "..text_to_be_reshaped = unicode(text_to_be_reshaped, errors='replace')"
    "reshaped_text = arabic_reshaper.reshape(text_to_be_reshaped)"
    reshaped_text = ar_reshape(text_to_be_reshaped)
    farsi_text = get_display(reshaped_text)
    return farsi_text

def corr(idxx,arr):
    out=[]
    for ix in idxx:
        if len(arr[ix]) > 3:
            tmp=(arr[ix])[1:-2].split(',')
            out.append(list(map(float,tmp)))
        else:
            out.append([])
    return out

my_wCns = [2,3,4,5,6,7,8,9]
fig = plt.figure(figsize=(20,10))
for ws in my_wCns:
    f= open('w'+str(ws)+'/msp-sil_w'+str(ws)+'.txt','r')
    fc=f.readlines()
    f.close()   
    m = corr([1,3,6,8],fc)
    if m[0] != []:
        plt.plot(m[0],m[1],label = 'WS= '+str(ws),marker='o')
    if m[2] != []:
        plt.plot(m[2],m[3],label = 'WS= '+str(ws)+'_PCA',marker='x',linestyle='--')

plt.legend(loc= 'upper left')
plt.grid(axis=u'both')
plt.xlim([0,60])
plt.ylim([-1,1])
plt.xlabel(make_farsi_text(('کمینه پشتیبان')))
plt.ylabel('silhouette score')
plt.savefig('./all14.png')
plt.close('all')
    
