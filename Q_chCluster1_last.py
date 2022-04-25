# -*- coding: utf-8 -*-.
"""

NOTE! implement 'text categorization as a graph classification problem',François Rousseau et al ACL 2015 
      but 
      instead of SVM it uses clustering,
      does'nt reduce to main-Core,
      uses closed frequent subgraphs instead of frequent subgraphs and
      ran on Quran preprocessed text.

This program does these steps:
1.extracts graph of input documents
2.produce compatible format for gspan in QjR_graphs_w.. .txt to run gSpan
3.uses closed frequent subgraphs as features to build text vectors.
4.run clustering on vectors.

NOTE! using sklearn function, Silhouette Coefficient is only defined if number of labels is 2 <= n_labels <= n_samples - 1.
"""
from __future__ import division

from time import time
from igraph import Graph
from igraph import plot

from numpy import asarray as np_asarray
from numpy import array as np_array
from numpy import shape as np_shape
from numpy import reshape as np_reshape
from numpy import zeros as np_zeros
from numpy import zeros_like as np_zeros_like
from numpy import where as np_where
from numpy import delete as np_delete
from numpy import linspace as np_linspace
from numpy import sum as np_sum
from numpy import abs, array_equal,mod,floor,sqrt,var,mean
from numpy import arange as np_arange
from numpy import dot as np_dot
from numpy import argsort as np_argsort

from sklearn import cluster
from sklearn.metrics import silhouette_score,silhouette_samples
from sklearn.decomposition import PCA,TruncatedSVD
from sklearn.preprocessing import StandardScaler

import matplotlib.cm as cm
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

from bidi.algorithm import get_display
from arabic_reshaper import reshape as ar_reshape

from scipy.cluster.hierarchy import dendrogram, linkage,fcluster
from scipy.cluster.hierarchy import fclusterdata
"from scipy.optimize import curve_fit"
from scipy.sparse import issparse

from itertools import chain

from copy import copy as c_copy

from os import makedirs as os_makedirs
from os.path import exists as os_exist

import sys

from rpy2 import robjects
from rpy2.robjects.packages import importr
import rpy2.robjects.numpy2ri
GlPth = './results/'
"-----------------------------------------------------------------------------"
def createFolder(directory):
    try:
        if not os_exist(directory):
            os_makedirs(directory)
    except OSError:
        print ('Error: Creating directory. ' +  directory)
"-----------------------------------------------------------------------------"
def m_dist(v1,v2):
    "common subgraphs related to possible common subgraphs that depends on less length chapter"
    if min(np_sum(v1),np_sum(v2)) == 0:
        if (len(v1) != 1) and (len(v2) != 1):
            print('NOTE! min(sum(v1),sum(v2))=0',v1,v2,np_sum(v1),np_sum(v2))
        return 0.000000000001
    return abs(1-(np_dot(v1,v2)/min(np_sum(v1),np_sum(v2))))
"-----------------------------------------------------------------------------"
def m_dists(inD): 
    "calculate distance matrix for inD [n_samples*n_samples array] according self defined m_dist function"
    outDst = []
    for inDi1 in range(0,len(inD)):
        outDst0 = []
        for inDi2 in range(0,len(inD)):
            outDst0.append(m_dist(inD[inDi1],inD[inDi2]))
        outDst.append(outDst0)
    return np_asarray(outDst)
"-----------------------------------------------------------------------------"
def eqWh(cur_wh,new_wh):
    if cur_wh == new_wh:
        return True
    return False
"-----------------------------------------------------------------------------"
def delSubSubs_pure(spR,newSub,gSubGraphs,gSubGraphs_l,gSubGraphs_v,SubSubSp,gSubGraphs_wh,newSub_wh):
    outSubGraphs = c_copy(gSubGraphs)
    outSubGraphs_l = c_copy(gSubGraphs_l)
    outSubGraphs_v = c_copy(gSubGraphs_v)
    outSubGraphs_wh = c_copy(gSubGraphs_wh)
    out_add = 1
    ssp1 = set(gSubGraphs.keys())
    ssp2 = spR & ssp1
    for sssp in ssp2:
        curSg_sp = gSubGraphs[sssp]
        curSg_sp_l = gSubGraphs_l[sssp]
        curSg_sp_v = gSubGraphs_v[sssp]
        curSg_sp_wh = gSubGraphs_wh[sssp]
        csl = len(curSg_sp)
        cssp_i = 0
        while cssp_i < csl:
            if not curSg_sp:
                csl = 0
                continue
            curGS = curSg_sp[cssp_i]
            if len(curGS) < len(newSub):
                mn_sg = set(curGS)
                mx_sg = set(newSub)
                if not mn_sg.difference(mx_sg):
                    if eqWh(curSg_sp_wh[cssp_i],newSub_wh):
                        "mn is subgraph of mx so delete mn"
                        curSg_sp.pop(cssp_i)
                        curSg_sp_l.pop(cssp_i)
                        curSg_sp_v.pop(cssp_i)
                        curSg_sp_wh.pop(cssp_i)
                else:
                    cssp_i += 1
            else:
                mx_sg = set(curGS)
                mn_sg = set(newSub)
                if not mn_sg.difference(mx_sg):
                    if eqWh(curSg_sp_wh[cssp_i],newSub_wh):
                        print("subgraph file length order!!!")
                        out_add = 0
                cssp_i += 1
            csl = len(curSg_sp)
        outSubGraphs[sssp] = c_copy(curSg_sp)
        outSubGraphs_l[sssp] = c_copy(curSg_sp_l)
        outSubGraphs_v[sssp] = c_copy(curSg_sp_v)
        outSubGraphs_wh[sssp] = c_copy(curSg_sp_wh)
    return [outSubGraphs,outSubGraphs_l,outSubGraphs_v,outSubGraphs_wh],out_add
"-----------------------------------------------------------------------------"
def readSubGrs_pure(inputFileName,node_lbls,subFilePath,SubSubSp):
    nodelblLess = node_lbls
    f = open(inputFileName,'r')
    fc = f.readlines()
    f_ = open(subFilePath+'closedSubs.txt','w')
    v_nodes = []
    e_edges = []
    e_edges_l = []
    wh_list1 = []
    g_subGraphs = dict()
    g_subGraphs_l = dict()
    g_subGraphs_v = dict()
    g_subGraphs_wh = dict()
    sp1 = 0
    "max ignorable difference of subgraph of subgraph supprorts"
    f_.write('اختلاف پشتیبان قابل قبول برای زیرگراف زیرگرافها '+str(SubSubSp)+'\n')
    for fc_line in fc:
        fc_line = fc_line.replace('\n','')
        fc_lt = fc_line.split(' ')
        g_k = g_subGraphs.keys()
        new_add = 1
        if fc_lt[0] == 't':
            if fc_lt[2] != '0':
                e_edges = list(e_edges)
                e_edges_l = list(e_edges_l)
                wh_list1.sort()
                "del subgraphs of this subgraphs:"
                if g_subGraphs != {}:
                    m_1 = max(0,sp1-SubSubSp)
                    m_2 = min(sp1+SubSubSp,max(g_k))                
                    gTmp, new_add = delSubSubs_pure(set(range(m_1,m_2+1)),e_edges,g_subGraphs,g_subGraphs_l,g_subGraphs_v,SubSubSp,g_subGraphs_wh,wh_list1)
                    [g_subGraphs,g_subGraphs_l,g_subGraphs_v,g_subGraphs_wh] = c_copy(gTmp)                  
                    g_k = g_subGraphs.keys()
                if new_add == 1:
                    if sp1 in g_k:
                        g_subGraphs[sp1].append(e_edges)
                        g_subGraphs_l[sp1].append(e_edges_l)
                        g_subGraphs_v[sp1].append(list(set(chain(*e_edges))))
                        g_subGraphs_wh[sp1].append(wh_list1)
                    else:
                        g_subGraphs[sp1]=[e_edges]
                        g_subGraphs_l[sp1]=[e_edges_l]
                        g_subGraphs_v[sp1]=[list(set(chain(*e_edges)))]
                        g_subGraphs_wh[sp1]=[wh_list1]
            v_nodes = []
            e_edges = []
            e_edges_l = []
            wh_list1 = []
            sp1 = int(fc_lt[4])
        else:
            if fc_lt[0] == 'v':
                v_nodes.append(int(fc_lt[2]))
            else:
                if fc_lt[0] == 'e':
                    if v_nodes[int(fc_lt[1])] > v_nodes[int(fc_lt[2])]:
                        sv_min = v_nodes[int(fc_lt[2])]
                        sv_max = v_nodes[int(fc_lt[1])]
                    else:
                        sv_max = v_nodes[int(fc_lt[2])]
                        sv_min = v_nodes[int(fc_lt[1])]                        
                    e_edges.append((sv_min,sv_max))
                    e_edges_l.append((node_lbls[sv_min],node_lbls[sv_max]))
                else:
                    if fc_lt[0] == 'x':
                        fc_lt = fc_lt[1:-1]
                        wh_list1 = list(map(int,fc_lt))
    if g_subGraphs:
        e_edges = list(e_edges)
        e_edges_l = list(e_edges_l)
        wh_list1.sort()
        m_1 = max(0,sp1-SubSubSp)
        m_2 = min(sp1+SubSubSp,max(g_k))
        gTmp,new_add = delSubSubs_pure(set(range(m_1,m_2+1)),e_edges,g_subGraphs,g_subGraphs_l,g_subGraphs_v,SubSubSp,g_subGraphs_wh,wh_list1)
        [g_subGraphs,g_subGraphs_l,g_subGraphs_v,g_subGraphs_wh] = c_copy(gTmp)        
        g_k = g_subGraphs.keys()
        if new_add == 1:
            if sp1 in g_k:
                g_subGraphs[sp1].append(e_edges)
                g_subGraphs_l[sp1].append(e_edges_l)
                g_subGraphs_v[sp1].append(list(set(chain(*e_edges))))
                g_subGraphs_wh[sp1].append(wh_list1)            
            else:
                g_subGraphs[sp1]=[e_edges]
                g_subGraphs_l[sp1]=[e_edges_l]
                g_subGraphs_v[sp1]=[list(set(chain(*e_edges)))]
                g_subGraphs_wh[sp1]=[wh_list1]
    "delete keys with [] value from dict"
    out_subGraphs = []
    out_subGraphs_l = []
    out_subGraphs_v = []
    out_subGraphs2 = []
    out_subGraphs_v2 = []
    out_subGraphs_wh = []
    for dci in g_subGraphs.keys():
        if not g_subGraphs.get(dci):
            g_subGraphs.pop(dci)
            g_subGraphs_l.pop(dci)
            g_subGraphs_v.pop(dci)
            g_subGraphs_wh.pop(dci)
        else:
            f_.write('sp:'+str(dci)+'\n')
            f_.write(str(g_subGraphs_l[dci])+'\n')                        
            out_subGraphs.extend(g_subGraphs[dci])
            out_subGraphs_l.extend(g_subGraphs_l[dci])
            out_subGraphs_v.extend(g_subGraphs_v[dci])
            out_subGraphs_wh.extend(g_subGraphs_wh[dci])
    "add remained non frequent nodes:"
    nlbn = len(node_lbls)
    out_subGraphs_v0 = list(set(chain(*out_subGraphs_v)))
    if len(out_subGraphs_v0)!=nlbn:
        v_abs = list(set(range(0,nlbn)).difference(out_subGraphs_v0))

    f_.close()
    f.close()
    for v_i in out_subGraphs_l:
        v_ii = []
        for (vv_i1,vv_i2) in v_i:
            v_ii.append((nodelblLess.index(vv_i1),nodelblLess.index(vv_i2)))
        out_subGraphs2.append(v_ii)
        out_subGraphs_v2.append(list(set(chain(*v_ii))))
    nlbn = len(nodelblLess)
    out_subGraphs_v0 = list(set(chain(*out_subGraphs_v2)))
    v_abs = list(set(range(0,nlbn)).difference(out_subGraphs_v0))
    return out_subGraphs_l,out_subGraphs2,out_subGraphs_v2,v_abs,out_subGraphs_wh
"-----------------------------------------------------------------------------"
def delSubSubs_close(spR,newSub,gSubGraphs,gSubGraphs_l,gSubGraphs_v,SubSubSp,gSubGraphs_wh):
    outSubGraphs = c_copy(gSubGraphs)
    outSubGraphs_l = c_copy(gSubGraphs_l)
    outSubGraphs_v = c_copy(gSubGraphs_v)
    outSubGraphs_wh = c_copy(gSubGraphs_wh)
    out_add = 1
    ssp1 = set(gSubGraphs.keys())
    ssp2 = spR & ssp1
    for sssp in ssp2:
        curSg_sp = gSubGraphs[sssp]
        curSg_sp_l = gSubGraphs_l[sssp]
        curSg_sp_v = gSubGraphs_v[sssp]
        curSg_sp_wh = gSubGraphs_wh[sssp]        
        csl = len(curSg_sp)
        cssp_i = 0
        while cssp_i < csl:
            if not curSg_sp:
                csl = 0
                continue
            curGS = curSg_sp[cssp_i]
            if len(curGS) < len(newSub):
                mn_sg = set(curGS)
                mx_sg = set(newSub)
                if not mn_sg.difference(mx_sg):
                    "mn is subgraph of mx so delete mn"
                    curSg_sp.pop(cssp_i)
                    curSg_sp_l.pop(cssp_i)
                    curSg_sp_v.pop(cssp_i)
                    curSg_sp_wh.pop(cssp_i)
                else:
                    cssp_i += 1
            else:
                mx_sg = set(curGS)
                mn_sg = set(newSub)
                if not mn_sg.difference(mx_sg):
                    out_add = 0
                cssp_i += 1
            csl = len(curSg_sp)
        outSubGraphs[sssp] = c_copy(curSg_sp)
        outSubGraphs_l[sssp] = c_copy(curSg_sp_l)
        outSubGraphs_v[sssp] = c_copy(curSg_sp_v)
        outSubGraphs_wh[sssp] = c_copy(curSg_sp_wh)
    return [outSubGraphs,outSubGraphs_l,outSubGraphs_v,outSubGraphs_wh],out_add
"-----------------------------------------------------------------------------"
def readSubGrs_closed(inputFileName,node_lbls,subFilePath,SubSubSp):
    nodelblLess = node_lbls  
    f = open(inputFileName,'r')
    fc = f.readlines()
    f_ = open(subFilePath+'closedSubs.txt','w')
    v_nodes = []
    e_edges = []
    e_edges_l = []
    wh_list1 = []
    g_subGraphs = dict()
    g_subGraphs_l = dict()
    g_subGraphs_v = dict()
    g_subGraphs_wh = dict()
    sp1 = 0
    "max ignorable difference of subgraph of subgraph supprorts"
    "SubSubSp = 0"
    f_.write('اختلاف پشتیبان قابل قبول برای زیرگراف زیرگرافها '+str(SubSubSp)+'\n')
    for fc_line in fc:
        fc_line = fc_line.replace('\n','')
        fc_lt = fc_line.split(' ')
        g_k = g_subGraphs.keys()
        new_add = 1
        if fc_lt[0] == 't':
            if fc_lt[2] != '0':
                e_edges = list(e_edges)
                e_edges_l = list(e_edges_l)
                wh_list1.sort()
                "del subgraphs of this subgraphs:"
                if g_subGraphs != {}:
                    m_1 = max(0,sp1-SubSubSp)
                    m_2 = min(sp1+SubSubSp,max(g_k))                
                    gTmp, new_add = delSubSubs_close(set(range(m_1,m_2+1)),e_edges,g_subGraphs,g_subGraphs_l,g_subGraphs_v,SubSubSp,g_subGraphs_wh)
                    [g_subGraphs,g_subGraphs_l,g_subGraphs_v,g_subGraphs_wh] = c_copy(gTmp)                    
                    """g_subGraphs = gTmp[0]
                    g_subGraphs_l = gTmp[1]
                    g_subGraphs_v = gTmp[2]
                    g_subGraphs_wh = gTmp[3] """                   
                    g_k = g_subGraphs.keys()
                if new_add == 1:
                    if sp1 in g_k:
                        g_subGraphs[sp1].append(e_edges)
                        g_subGraphs_l[sp1].append(e_edges_l)
                        g_subGraphs_v[sp1].append(list(set(chain(*e_edges))))
                        g_subGraphs_wh[sp1].append(wh_list1)
                    else:
                        g_subGraphs[sp1]=[e_edges]
                        g_subGraphs_l[sp1]=[e_edges_l]
                        g_subGraphs_v[sp1]=[list(set(chain(*e_edges)))]
                        g_subGraphs_wh[sp1]=[wh_list1]
            v_nodes = []
            e_edges = []
            e_edges_l = []
            wh_list1 = []
            sp1 = int(fc_lt[4])
        else:
            if fc_lt[0] == 'v':
                v_nodes.append(int(fc_lt[2]))
            else:
                if fc_lt[0] == 'e':
                    if v_nodes[int(fc_lt[1])] > v_nodes[int(fc_lt[2])]:
                        sv_min = v_nodes[int(fc_lt[2])]
                        sv_max = v_nodes[int(fc_lt[1])]
                    else:
                        sv_max = v_nodes[int(fc_lt[2])]
                        sv_min = v_nodes[int(fc_lt[1])]                        
                    e_edges.append((sv_min,sv_max))
                    e_edges_l.append((node_lbls[sv_min],node_lbls[sv_max]))
                else:
                    if fc_lt[0] == 'x':
                        fc_lt = fc_lt[1:-1]
                        wh_list1 = list(map(int,fc_lt))
    if g_subGraphs:
        e_edges = list(set(e_edges))
        e_edges_l = list(set(e_edges_l))
        wh_list1.sort()
        m_1 = max(0,sp1-SubSubSp)
        m_2 = min(sp1+SubSubSp,max(g_k))
        gTmp,new_add = delSubSubs_close(set(range(m_1,m_2+1)),e_edges,g_subGraphs,g_subGraphs_l,g_subGraphs_v,SubSubSp,g_subGraphs_wh)
        [g_subGraphs,g_subGraphs_l,g_subGraphs_v,g_subGraphs_wh] = c_copy(gTmp)        
        g_k = g_subGraphs.keys()
        if new_add == 1:
            if sp1 in g_k:
                g_subGraphs[sp1].append(e_edges)
                g_subGraphs_l[sp1].append(e_edges_l)
                g_subGraphs_v[sp1].append(list(set(chain(*e_edges))))
                g_subGraphs_wh[sp1].append(wh_list1)            
            else:
                g_subGraphs[sp1]=[e_edges]
                g_subGraphs_l[sp1]=[e_edges_l]
                g_subGraphs_v[sp1]=[list(set(chain(*e_edges)))]
                g_subGraphs_wh[sp1]=[wh_list1]
    "delete keys with [] value from dict"
    out_subGraphs = []
    out_subGraphs_l = []
    out_subGraphs_v = []
    out_subGraphs2 = []
    out_subGraphs_v2 = []
    out_subGraphs_wh = []
    for dci in g_subGraphs.keys():
        if not g_subGraphs.get(dci):
            g_subGraphs.pop(dci)
            g_subGraphs_l.pop(dci)
            g_subGraphs_v.pop(dci)
            g_subGraphs_wh.pop(dci)
        else:
            f_.write('sp:'+str(dci)+'\n')
            f_.write(str(g_subGraphs_l[dci])+'\n')                        
            out_subGraphs.extend(g_subGraphs[dci])
            out_subGraphs_l.extend(g_subGraphs_l[dci])
            out_subGraphs_v.extend(g_subGraphs_v[dci])
            out_subGraphs_wh.extend(g_subGraphs_wh[dci])
    "add remained non frequent nodes:"
    nlbn = len(node_lbls)
    out_subGraphs_v0 = list(set(chain(*out_subGraphs_v)))
    if len(out_subGraphs_v0)!=nlbn:
        v_abs = list(set(range(0,nlbn)).difference(out_subGraphs_v0))
    f_.close()
    f.close()
    for v_i in out_subGraphs_l:
        v_ii = []
        for (vv_i1,vv_i2) in v_i:
            v_ii.append((nodelblLess.index(vv_i1),nodelblLess.index(vv_i2)))
        out_subGraphs2.append(v_ii)
        out_subGraphs_v2.append(list(set(chain(*v_ii))))
    nlbn = len(nodelblLess)
    out_subGraphs_v0 = list(set(chain(*out_subGraphs_v2)))
    v_abs = list(set(range(0,nlbn)).difference(out_subGraphs_v0))
    return out_subGraphs_l,out_subGraphs2,out_subGraphs_v2,v_abs,out_subGraphs_wh
"-----------------------------------------------------------------------------"
def ch_subCount(subG_Es,ch_Vslbls,ch_Es,ch_W,unqlbls):
    sb_eW = []
    for (sb_e1,sb_e2) in subG_Es:
        sb_eW.append(ch_W[ch_Es.index((min(ch_Vslbls.index(unqlbls[sb_e1]),ch_Vslbls.index(unqlbls[sb_e2])),max(ch_Vslbls.index(unqlbls[sb_e1]),ch_Vslbls.index(unqlbls[sb_e2]))))])
    return min(sb_eW)
"-----------------------------------------------------------------------------"
def RanGs_pure(fn100,unqLbl,maxZCh,window,ch_n,SubSubSpj,ch_Grs):
    GcNodes,GcNodes_int,GcVrtxLst,v_absent,sfWhs = readSubGrs_pure(fn100+'.fp',unqLbl,GlPth+'w'+str(window)+'/',SubSubSpj)  
    f1d = open('./results/w'+str(window)+'/Pfeatures.txt','w')
    for f1di in range(0,len(GcNodes)) :
        f1d.write(str(GcNodes[f1di])+'\n')
    for f1di in range(0,len(GcNodes_int)) :
        f1d.write(str(GcNodes_int[f1di])+'\n')
    for f1di in range(0,len(GcVrtxLst)) :
        f1d.write(str(GcVrtxLst[f1di])+'\n')
    for f1di in range(0,len(sfWhs)) :
        f1d.write(str(sfWhs[f1di])+'\n')
    f1d.close()
    outRan = dict()
    sfVSecs = np_zeros((ch_n,len(GcNodes)),dtype=int)
    for sfv_i in range(0,len(sfWhs)):
        for sfv_x in sfWhs[sfv_i]:
            sfVSecs[sfv_x][sfv_i] = ch_subCount(GcNodes_int[sfv_i],ch_Grs[sfv_x].vs['label'],ch_Grs[sfv_x].get_edgelist(),ch_Grs[sfv_x].es['weight'],unqLbl)
    outRan = sfVSecs/np_sum(sfVSecs,0)
    """if max(sum(sfVSecs)) >= 114-maxZCh:
        mFr = np_where(sum(sfVSecs) == max(sum(sfVSecs)))[0]        
        for mfCnt in range(0,len(mFr)):
            "indices correction"
            grffe =[]
            grffa = sorted(list(set(GcVrtxLst[mfCnt])))
            for oldee in GcNodes_int[mfCnt]:
                grffe.append((grffa.index(oldee[0]),grffa.index(oldee[1])))
            grff = Graph(grffe)
            grff.vs['label'] = np_asarray(unqLbl)[GcVrtxLst[mfCnt]]
            chpff = plot(grff)
            chpff.save('./results/mostFreq'+str(mfCnt)+'_'+str(window)+'_raw.png')
            plt.close()            
        plt.figure()
        plt.title(make_farsi_text(('پرتکرارترین ویژگی قبل از برداری سازی (نماینده‌ی حذف)')))
        plt.savefig('./results/mostFreq'+str(mfCnt)+'_raw.png')"""
    return outRan
"-----------------------------------------------------------------------------"
def RanGs(fn100,unqLbl,maxZCh,window,ch_n,SubSubSpj,ch_Grs):
    GcNodes,GcNodes_int,GcVrtxLst,v_absent,sfWhs = readSubGrs_pure(fn100+'.fp',unqLbl,GlPth+'w'+str(window)+'/',SubSubSpj)  
    f1d = open('./results/w'+str(window)+'/Pfeatures.txt','w')
    for f1di in range(0,len(GcNodes)) :
        f1d.write(str(GcNodes[f1di])+'\n')
    for f1di in range(0,len(GcNodes_int)) :
        f1d.write(str(GcNodes_int[f1di])+'\n')
    for f1di in range(0,len(GcVrtxLst)) :
        f1d.write(str(GcVrtxLst[f1di])+'\n')
    outRan = dict()
    outRan['numOfFeatures'] = len(GcNodes)
    sfVSecs = np_zeros((outRan['numOfFeatures'],ch_n),dtype=int)
    for sfv_i in range(0,len(sfWhs)):
        for sfv_x in sfWhs[sfv_i]:
            sfVSecs[sfv_i][sfv_x] = True
    outRan['sfVSecs'] = sfVSecs
    for f1di in range(0,len(sfWhs)) :
        f1d.write(str(sfWhs[f1di])+'\n')   
    f1d.close()
    """if max(sum(sfVSecs)) >= 114-maxZCh:
        mFr = np_where(sum(sfVSecs) == max(sum(sfVSecs)))[0]        
        for mfCnt in range(0,len(mFr)):
            "indices correction"
            grffe =[]
            grffa = sorted(list(set(GcVrtxLst[mfCnt])))
            for oldee in GcNodes_int[mfCnt]:
                grffe.append((grffa.index(oldee[0]),grffa.index(oldee[1])))
            grff = Graph(grffe)
            grff.vs['label'] = np_asarray(unqLbl)[GcVrtxLst[mfCnt]]
            chpff = plot(grff)
            chpff.save('./results/mostFreq'+str(mfCnt)+'_'+str(window)+'_raw.png')
            plt.close()            
        plt.figure()
        plt.title(make_farsi_text(('پرتکرارترین ویژگی قبل از برداری سازی (نماینده‌ی حذف)')))
        plt.savefig('./results/mostFreq'+str(mfCnt)+'_raw.png')"""
    return outRan
"-----------------------------------------------------------------------------"
def mCheck(gsRes_p,RanGsRes):
    if len(gsRes_p.graphs) != 114:
        print('size of .graphs', len(gsRes_p.graphs))
    else:
        print ('.graphs checked: True')
    if np_shape(gsRes_p.sfVSecs)[0] != RanGsRes['numOfFeatures']:
        print('.frequent_subgraphs_obj: False')
        print (np_shape(gsRes_p.sfVSecs)[0],'is not equal to',RanGsRes['numOfFeatures'])
    else:
        print('.frequent_subgraphs_obj: True')     
        m100=0
        if sum(sum(gsRes_p.sfVSecs))!=np_sum(RanGsRes['sfVSecs']):
            print ('.frequent_sfVsecs: False')
            m100 = 1
        if not m100:
            print('.frequent_subgraphs_obj: True')                
    return
"-----------------------------------------------------------------------------"
def read_docs2(fName,nb):
    d_cs = []
    for nb1 in range(0,nb):
        ss = './'+fName+'/'+fName+'_'+str(nb1+1)+'.txt'
        d_c = ''
        with  open(ss,'r') as f_C:
            for line in f_C:
                d_c = d_c + line[0:-1]
        d_cs.append(d_c)
    return d_cs
"-----------------------------------------------------------------------------"
def m_wordAdjMat2(ws,txtList,wState,dState):
    
    """ws = windowsize, txtList = text nodes in list format,
       wState = w means weighted and unw means unweighted
       dState = d means directed , und means undirected"""
    "without reflexive edge"
    d_TLen = len(txtList)
    k = 0
    cdd = 0
    d_adj = []
    uniCnt = 0
    uniLst = []
    d_weight = []
    
    for word in txtList:
        if k > d_TLen-2:
            break
        a = k
        b = min(d_TLen-1,k+ws-1)
        if word not in uniLst:
            uniLst.append(word)
            r_idx = uniCnt
            uniCnt = uniCnt+1
        else:
            r_idx = uniLst.index(word)
        for l in range(a,b+1):
            if not l == k:
                if txtList[l] not in uniLst:
                    uniLst.append(txtList[l])
                    uniCnt = uniCnt+1
                c_idx = uniLst.index(txtList[l])
                if (wState == 'w') & (dState == 'd'):
                    tw = (r_idx,c_idx)
                    if r_idx != c_idx:
                        if tw not in d_adj:
                            d_adj.append(tw)
                            d_weight.append(1)
                        else:
                            e_idx = d_adj.index(tw)
                            d_weight[e_idx] = d_weight[e_idx]+1
                    cdd = cdd+1
                else:
                    if (wState == 'w') & (dState == 'und'):
                        if r_idx != c_idx:                        
                            if ((r_idx,c_idx) not in d_adj) & ((c_idx,r_idx) not in d_adj):
                                d_adj.append((r_idx,c_idx))
                                d_weight.append(1)
                            else:
                                if (r_idx,c_idx) in d_adj:
                                    e_idx = d_adj.index((r_idx,c_idx))
                                    d_weight[e_idx] = d_weight[e_idx]+1
                                else:
                                    e_idx = d_adj.index((c_idx,r_idx))
                                    d_weight[e_idx] = d_weight[e_idx]+1
                        cdd = cdd+1
                    else:
                        if (wState == 'unw') & (dState == 'd'):
                            tw = (r_idx,c_idx)
                            if r_idx != c_idx:
                                if tw not in d_adj:
                                    d_adj.append(tw)
                            cdd = cdd+1
                        else:
                            if (wState == 'unw') & (dState == 'und'):
                                if r_idx != c_idx:
                                    if((r_idx,c_idx) not in d_adj) & ((c_idx,r_idx) not in d_adj):
                                        d_adj.append((r_idx,c_idx))
                                        cdd = cdd+1
                            else:
                                print('error! check again input args!')

        k = k+1
    return [d_adj,uniLst,d_weight]
"-----------------------------------------------------------------------------"
def gsInputForm_byIdx(iCores,f,gsb_lbls):
    for cCnt in range(0,len(iCores)):
        grstr = 't # '+str(cCnt)+' \n' 
        f.write(grstr)
        cg = iCores[cCnt]
        vl = cg.vs['label']
        for vlCnt in range(0,len(vl)):
            grstr = 'v '+str(vlCnt)+' '+str(gsb_lbls.index(vl[vlCnt]))+'\n'
            f.write(grstr)
        el = cg.es
        for edg in el:
            grstr = 'e '+str(edg.tuple[0])+' '+str(edg.tuple[1])+' 1'+'\n'            
            f.write(grstr)            
    f.write('t # -1')
"-----------------------------------------------------------------------------" 
def make_farsi_text(text_to_be_reshaped):
    "..text_to_be_reshaped = unicode(text_to_be_reshaped, errors='replace')"
    reshaped_text = ar_reshape(text_to_be_reshaped)
    farsi_text = get_display(reshaped_text)
    return farsi_text
"-----------------------------------------------------------------------------"
def make_farsi_text2(txtArr_to_reshaped):
    farsi_text = []
    for tArr in range(0,len(txtArr_to_reshaped)):
        farsi_text.append(get_display(ar_reshape(txtArr_to_reshaped[tArr])))
    return farsi_text 
"-----------------------------------------------------------------------------"
def get_SovarNames2(s_fileName,list1):
    "شماره سور را با لیست می گیرد و لیست نام را بر میگرداند"    
    s_names = []
    s_namesCnt = 0
    with open(s_fileName,'r') as svName:
        for s_svl in svName:
            if s_namesCnt in list1:
                "delete odd \n:"
                s_svl = str(s_svl).replace('\n','')
                s_names.append(s_svl)
            s_namesCnt = s_namesCnt+1
    return s_names,s_namesCnt
"-----------------------------------------------------------------------------"
def del0_twice_Chaps_normal(inReshapedMat,chn,chvDel,pltNum):
    """delete chapters that according vectors has been zero 
       and also those chapters that are same as an existing chapter but 
       they will be add in last results. in addition features that are common 
       between all chapters.
    """  
    "...................."
    "delete zero vectors:"
    cleanedList = c_copy(inReshapedMat)
    cleanedList1,chv1,rmF0 = del0s_commons_normal(cleanedList,chvDel,chn)
    cleanedList = c_copy(cleanedList1)
    chv0 = c_copy(chv1)
    if len(chv0) != 0:
        print('support is too high, some chapters has zero vector!')
        print ('سوره‌های(*نسبت به حذف اولیه)',chv0)
        print ('کنار گذاشته شده اند')
    if len(rmF0) != 0:
        print ('feature',rmF0,' has been deleted')
    "...................."
    "delete duplicates"
    sameChs = []
    sameChKey = []
    "according to sameChKey elements count real makki madani membering"
    sameChMkMd = []
    cleanedList = []
    blackL = []
    m_mkd = []
    with open('Makki_Madani01.txt','r') as kd01:
        for line in kd01:
            m_mkd.append(int(line.replace('\n','')))
    chvId = list(set(range(0,len(chv0)+np_shape(cleanedList1)[0])).difference(chv0))
    chv0 = np_asarray(chv0)    
    for chTst1 in range(0,np_shape(cleanedList1)[0]):
        same2V = []
        for chTst2 in range(chTst1+1,np_shape(cleanedList1)[0]):
            if array_equal(cleanedList1[chTst1,:],cleanedList1[chTst2,:]):
                blackL.append(chTst2)
                same2V.append(chvId[chTst2])
        if chTst1 not in blackL:
            cleanedList.append(cleanedList1[chTst1,:])            
        br = 0
        sCh = -1
        for sCh in same2V:
            for sChc in sameChs:
                if sCh in sChc:
                    br = 1
                    break
            if br:
                break
        if br:
            sChc = sChc.union(same2V)
        else:
            if sCh != -1:
                sameChs.append(set(same2V))
                sameChKey.append(chTst1)
                mkmdC = [0,0]
                for samesc in sameChs[-1]:
                    mkmdC[m_mkd[samesc]] += 1
                sameChMkMd.append(mkmdC)
    "...................."    
    chv0 = list(chv0)
    chv0.sort()
    return cleanedList,chv0,sameChKey,sameChs,sameChMkMd
"-----------------------------------------------------------------------------"
"-----------------------------------------------------------------------------"
def del0_twice_Chaps_bin(inReshapedMat,chn,chvDel,pltNum):
    """delete chapters that according vectors has been zero 
       and also those chapters that are same as an existing chapter but 
       they will be add in last results. in addition features that are common 
       between all chapters.
    """
    "...................."
    "delete zero vectors:"
    cleanedList = c_copy(inReshapedMat)
    cleanedList1,chv1,rmF0 = del0s_commons(cleanedList,chvDel,chn)
    cleanedList = c_copy(cleanedList1)
    chv0 = c_copy(chv1)
    if len(chv0) != 0:
        print('support is too high, some chapters has zero vector!')
        print ('سوره‌های(*نسبت به حذف اولیه)',chv0)
        print ('کنار گذاشته شده اند')
    if len(rmF0) != 0:
        print ('feature',rmF0,' has been deleted')
        "...................."  
    "...................."
    "delete duplicates"
    sameChs = []
    sameChKey = []
    "according to sameChKey elements count real makki madani membering"
    sameChMkMd = []
    cleanedList = []
    blackL = []
    m_mkd = []
    with open('Makki_Madani01.txt','r') as kd01:
        for line in kd01:
            m_mkd.append(int(line.replace('\n','')))
    chvId = list(set(range(0,len(chv0)+np_shape(cleanedList1)[0])).difference(chv0))
    chv0 = np_asarray(chv0)    
    for chTst1 in range(0,np_shape(cleanedList1)[0]):
        same2V = []
        for chTst2 in range(chTst1+1,np_shape(cleanedList1)[0]):
            if array_equal(cleanedList1[chTst1,:],cleanedList1[chTst2,:]):
                blackL.append(chTst2)
                same2V.append(chvId[chTst2])

        if chTst1 not in blackL:
            cleanedList.append(cleanedList1[chTst1,:])            
        br = 0
        sCh = -1
        for sCh in same2V:
            for sChc in sameChs:
                if sCh in sChc:
                    br = 1
                    break
            if br:
                break
        if br:
            sChc = sChc.union(same2V)
        else:
            if sCh != -1:
                sameChs.append(set(same2V))
                sameChKey.append(chTst1)
                mkmdC = [0,0]
                for samesc in sameChs[-1]:
                    mkmdC[m_mkd[samesc]] += 1
                sameChMkMd.append(mkmdC)
    "sameChKey = list(set(sameChKey))"
    "...................."    
    chv0 = list(chv0)
    chv0.sort()
    return cleanedList,chv0,sameChKey,sameChs,sameChMkMd
"-----------------------------------------------------------------------------"
def del0s_commons_normal(inArr,delCs,presentCs):
    chvC = 0
    chv00 = c_copy(delCs)
    rm00 = []
    "deleting zeros should be first then delete common features, deleting features may be cause to zero vectors then again ..."
    TLp = 1
    cleanedList01 = c_copy(inArr)
    while(TLp):
        "...................."
        "delete zero vectors:"    
        rng_Idx = set(range(0,np_shape(cleanedList01)[0]+len(chv00)))
        chvNw = list(rng_Idx.difference(set(chv00)))            
        chvNw.sort()
        chvC = 0
        if np_shape(cleanedList01)[1] == 0:
            break
        chv0 = []
        for chv in cleanedList01.tolist():            
            if chv == (np_zeros(len(chv),dtype=int)).tolist():
                chv0.append(chvC)
                chv00.append(chvNw[chvC])
            chvC = chvC + 1
        cleanedList00 = np_delete(cleanedList01,chv0,axis=0)
        "check no 0 in matrix:"
        """for p00 in cleanedList.tolist():
            if((cleanedList.any(axis=1)).sum(0) != len(cleanedList)):
                clc00 = 0
            else:
                clc00=1
                break"""    
        "delete odd features(all zero or all one in all vectors)"
        rm_features = []
        if np_shape(cleanedList00)[0] in (cleanedList00>0).sum(0):
            for com_200 in np_where(((cleanedList00>0).sum(0) == np_shape(cleanedList00)[0]))[0]:
                if(len(np_where((cleanedList00[:,com_200]-cleanedList00[0,com_200]) !=0)[0])<1):
                    print("one feature is odd:",com_200,np_where((cleanedList00[:,com_200]-cleanedList00[0,com_200]) !=0)[0])
                    print("so deleted.")
                    return
                    rm_features.append(com_200)
        if 0 in cleanedList00.sum(0):
            print ("Error! there is a frequent subgraph in no chapter!!!!")
            return
        if len(rm_features)>0:
            rm0Idx = list(set(range(0,np_shape(cleanedList00)[1]+len(rm00))).difference(rm00))            
            rm0Idx.sort()
            for rm0 in rm_features:
                rm00.append(rm0Idx[rm0])
            rm00.sort()
            cleanedList01 = np_delete(cleanedList00,rm_features,axis=1)
        else:            
            cleanedList01 = c_copy(cleanedList00)
        "check no 0 vec in matrix:"
        if 0 not in cleanedList01.sum(1):
            TLp = 0
    if cleanedList01.tolist() == []:
        print("There is no available vectors!")
        return
    chv00.sort()
    return cleanedList01,chv00,rm00
"-----------------------------------------------------------------------------"
def cluster_show_write(inData1,cluster_res,frName,algName,prmStr1,dlChs,plot_Nb,chps,dsMetric,same_k,same_c,same_c_mkd,msp,preFNum,preSubFr,preSubFr_ch):
    svNm = []
    svNm2 = []
    svNm3 = []
    svGL = []
    grNb = []
    svlCn = 0
    y_lower = 0
    sh_jump = 1
    xt1 = []
    yt1 = []
    ch_fNums = (np_sum(np_asarray(inData1)>0,1))
    sh_sv = c_copy(dlChs)
    sh_sv.extend(list(chain(*np_asarray(same_c))))
    svN = []
    svN3 = []
    with open('nameSovar_c.txt','r') as svName:
        for svl in svName:
            svNm.append(svl)
            if svlCn not in sh_sv:
                svNm3.append(svl)
                svN3.append(svl[0:-1])
                svN.append(svlCn)
            else:
                if frName.find('PCA') != -1:
                    if svlCn in preSubFr_ch:
                        preSubFr_ch.remove(svlCn)
                        preSubFr.pop(svlCn)
            svlCn = svlCn+1
    svNm2 = np_asarray(svNm3)
    "save plot of feature distribution"
    if frName.find('PCA') == -1:
        plt.figure(figsize=(55,10))
        plt.rc('font',family = 'Dejavu Sans',size = 5)
        plt.grid()
        plt.xlabel(make_farsi_text('نام سوره'))
        plt.ylabel(make_farsi_text('تعداد ویژگی'))
        "plt.ylim([0,preFNum])"    
        plt.xticks(range(1,len(svNm3)+1),make_farsi_text2(svNm3))
        plt.bar(range(1,len(svNm3)+1),ch_fNums, width = 0.2, color='black')
        plt.savefig(frName+'_res'+str(plot_Nb)+'_msp'+str(msp)+'ch_features3.png')
        plt.close()
               
        plt.figure(figsize=(55,10))
        plt.grid()
        plt.rc('font',family = 'DejaVu Sans',size = 10)
        plt.xlabel(make_farsi_text(('شماره سوره')))
        plt.ylabel(make_farsi_text(('تعداد ویژگی')))
        plt.ylim([0,preFNum])                
        plt.xticks(range(1,len(svNm3)+1),svN)
        plt.bar(range(1,len(svNm3)+1),ch_fNums, width = 0.2, color = 'black')
        plt.savefig(frName+'_res'+str(plot_Nb)+'_msp'+str(msp)+'ch_Nfeatures4.png')        
        plt.close()    

    frsName = open(frName+'_res'+str(plot_Nb)+'_msp'+str(msp)+'_f'+str(np_shape(inData1)[1])+'.txt','w')
    frsName.write('****************************************************')
    frsName.write('پارامترها')
    if(algName=='dbscan'):
        frsName.write('\ndbscan'+prmStr1+'\t'+'eps:'+str(cluster_res[2][0])+'\t min_sample:'+str(cluster_res[2][1])+'\n')
        lbls = cluster_res[1].labels_
        core_samples_mask = np_zeros_like(cluster_res[1], dtype=bool)
        core_samples_mask[cluster_res[1].core_sample_indices_] = 1
    elif(algName == 'spectral'):
        frsName.write('\nSpectral: '+prmStr1+'\t'+'#cluster:'+str(cluster_res[2][0])+'\t distance method:'+str(cluster_res[2][1])+'\n')    
        lbls = cluster_res[1]
    elif (algName == 'Hierarchical'):
        lbls = np_asarray(cluster_res[1])  
        frsName.write('\n Hierarchical: \t'+'\t #clusters ='+str(len(set(lbls)))+'\n')                     
    unique_labels = set(lbls)
    colors = [plt.cm.Spectral(each) for each in np_linspace(0, 1, len(unique_labels))]
    if dsMetric == 'self':
        cq0_s = silhouette_samples(inData1,lbls, metric=m_dist)
    else:
        cq0_s = silhouette_samples(inData1,lbls, metric=dsMetric)
    plt.close('all')
    fArch1 = open(frName+'_res'+str(plot_Nb)+'silhouette_analyse_msp'+str(msp)+'_f'+str(np_shape(inData1)[1])+'.txt','w')
    fg1 = plt.figure(figsize=(10,15))
    fig1 = fg1.gca()    
    fg2 = plt.figure(figsize=(10,15))
    plt.rc('font',family = 'Dejavu Sans',size = 6)
    fig2 = fg2.gca()
    # Number of clusters in labels, ignoring noise if present.
    n_clusters_ = len(set(lbls)) - (1 if -1 in lbls else 0)
    clusters_KD = KDmatching_new(lbls,dlChs,chps,same_c)
    clusters_KD_maxRate = np_asarray(list(map(max,clusters_KD)))/np_asarray(list(map(sum,clusters_KD)))
    clusters_KD_maxRate_var  = sqrt(var(clusters_KD_maxRate))
    clusters_KD_maxRate_mean = mean(clusters_KD_maxRate)
    for k, col in zip(unique_labels, colors):    
        svG = ''
        if k == -1:
            # Black used for noise.
            col = [0, 0, 0, 1]
        class_member_mask = (lbls == k)
        if(algName=='dbscan'):
            print('Note! dbscan part is incomplete')
            return
            bb = (np_array(class_member_mask) & np_array(core_samples_mask))                    
            xy1 =(np_where(bb==True))
            fig2.plot(lbls[bb].tolist(), xy1[0].tolist(), 'o', markerfacecolor=tuple(col),
                markeredgecolor='k', markersize=7)    
            cc = (np_array(class_member_mask) & np_array(~core_samples_mask))
            xy2 =(np_where(cc==True))
            fig2.plot( lbls[cc].tolist(),xy2[0].tolist(), 'o', markerfacecolor=tuple(col),
                 markeredgecolor='k', markersize=3)
        elif(algName == 'spectral'):
            print('Note! dbscan part is incomplete')
            return
            xy1 =np_where(class_member_mask==True)
            fig2.plot(lbls[class_member_mask].tolist(),xy1[0].tolist(), 'o', markerfacecolor=tuple(col),
                     markeredgecolor='k', markersize=9)
        elif (algName == 'Hierarchical'):
            xy1 =np_where(lbls==k)
            if not(xy1[0].tolist == []):
                fig2.plot(lbls[class_member_mask],xy1[0].tolist(), 'o', markerfacecolor=tuple(col),
                     markeredgecolor='k', markersize=9)
                ith_clusterSamps = cq0_s[np_where(lbls==k)[0]]
                ith_clusterSamps.sort()                
                y_upper = y_lower + len(ith_clusterSamps)
                color = cm.nipy_spectral(float(k) / n_clusters_)
                fig1.fill_betweenx(np_arange(y_lower, y_upper),
                          0, ith_clusterSamps,
                          facecolor=color, edgecolor=color, alpha=0.7)
                "cluster"                
                fig1.text(0.5, y_lower + 0.5 * len(ith_clusterSamps), str(k))   
                fig1.plot([-1.1,-1,0,1],4*[y_lower-0.005],color="black", linestyle="--")
                "ave silhouette_samples for each cluster"
                fig1.scatter([sum(ith_clusterSamps)/len(ith_clusterSamps)],[y_lower+((len(ith_clusterSamps)-1)/2)],marker='o',color='black')
                stSvc = "["
                for stSv in svNm2[class_member_mask]:
                    stSvc += str(stSv[0:-1])+', '
                fArch1.write('y_lower,y_upper,len(ith_clusterSamps),ytickI,k:\t'+str(y_lower)+' , '+str(y_upper)+' , '+str(len(ith_clusterSamps))+' , '+str(k)+' , '+stSvc[:-1]+']\nith_clusterSamps:\n'+str(ith_clusterSamps)+'\ncluster mean silhouette:'+str(sum(ith_clusterSamps)/len(ith_clusterSamps))+'\n')        
                xt1.extend(range(y_lower,y_upper))
                yt1.extend(make_farsi_text2(svNm2[class_member_mask]))                
                y_lower = y_upper + sh_jump
        frsName.write('گروه'+str(k)+', تعداد سوره‌های مکی-تعداد سوره‌های مدنی:'+str(clusters_KD[k-1])+'\n')
        clCnt = 0
        ch_fNums_k = ch_fNums[class_member_mask]
        cls_mask = np_where(lbls == k)[0]
        for ch in svNm2[class_member_mask]:
            if frName.find('PCA') == -1:            
                ch_ = '(' + str(ch_fNums_k[clCnt])+')' + ch
            else:
                ch_ = '(' + str(preSubFr[cls_mask[clCnt]])+')'+ ch
            frsName.write(ch_)
            svG = svG+ch_+' '
            clCnt = clCnt+1
        grNb.append(clCnt)
        svGL.append(svG)
        frsName.write('--------------------------------------\n')
    "********makki madani matching*************"    
    mk_match = 'بیش از دو دسته داریم'
    if n_clusters_ == 2:
        a00,a11,mk_match,mkTrue,mkReal,mdTrue,mdReal = Mk_Matching1(lbls,dlChs,chps,same_k,same_c,same_c_mkd)
        frsName.write(str(cluster_res[4])+'\t , تطبیق مکی-مدنی = '+str(mk_match)+' سوره('+str(mk_match/(114-len(sh_sv)))+')')    
    else:
        frsName.write(str(cluster_res[4])+'\t , تطبیق مکی-مدنی = '+str(mk_match))
    "******************************************"
    frsName.write('--------------------------------------\n')
    frsName.write('یکدستی خوشه‌ها از نظر مکی-مدنی‌بودن: میانگین '+str(clusters_KD_maxRate_mean)+', واریانس:'+str(clusters_KD_maxRate_var))
    frsName.write('تعداد خوشه‌ها که نهایتا گروه‌بندی جاری به دلیل بالاتر بودن مقدار معیار نیمرخ در آن انتخاب شده است. \t امتیاز\n')
    for clsS in cluster_res[0]:
        frsName.write(str(clsS[0])+'\t'+str(clsS[1])+'\n')
    frsName.write('\n سوره‌های با بردار یکسان: \n')
    svNm = np_asarray(svNm)
    for clsS in range(0,len(same_k)):
        clsScs = ''
        frsName.write('*'+svNm[same_k[clsS]]+' با \n')
        for clsSc in svNm[list(same_c[clsS])] :
            clsScs += clsSc[0:-1]+' , '
        frsName.write(clsScs+'\n')
    frsName.close()
    plt.xlim([-1,n_clusters_ +1])
    plt.rc('font',family = 'Dejavu Sans',size = 7)
    plt.yticks(range(0,len(chps)),make_farsi_text2(svNm3))
    plt.title(make_farsi_text(('')))
    plt.xlabel(make_farsi_text(('خوشه')))  
    plt.grid(True)
    plt.savefig(frName+'1_res'+str(plot_Nb)+'_msp'+str(msp)+'_f'+str(np_shape(inData1)[1])+'.png')
    plt.close()
    
    # The vertical line for average silhouette score of all the values
    plt.rc('font',family = 'Dejavu Sans',size = 7)
    fig1.axvline(x=cluster_res[4], color="red", linestyle="--")
    plt.title(make_farsi_text('تحلیل silhouette'))
    plt.xlim([-1.1,1.1])    
    plt.ylim([0,len(chps)-len(sh_sv)+sh_jump*n_clusters_])
    plt.ylabel(make_farsi_text('نقاط'))
    plt.xlabel(make_farsi_text('silhouette'))
    plt.yticks(xt1,yt1)    
    plt.savefig(frName+'_res'+str(plot_Nb)+'silhouette_analyse_msp'+str(msp)+'_f'+str(np_shape(inData1)[1])+'.png')
    plt.close()
    
    fArch1.write('ylim:\n'+str([0,len(chps)-len(sh_sv)+sh_jump*n_clusters_]))    
    fArch1.write(' cq0:'+str(cluster_res[4])+'\nyticks:\ny:\n'+str(xt1)+'\n')    
    fArch1.close()
    plt.figure(figsize=(10,15))
    plt.hist(lbls,color = 'lightskyblue')
    plt.rc('font',family = 'Dejavu Sans',size = 6)
    plt.xlim([-1,n_clusters_ +1])
    for txCnt in range(0,len(grNb)):
        plt.text(txCnt+1,0,make_farsi_text(svGL[txCnt]))
    plt.title(algName)
    plt.grid(True)
    plt.savefig(frName+'2_res'+str(plot_Nb)+'_msp'+str(msp)+'_f'+str(np_shape(inData1)[1])+'.png')
    plt.close('all')
    "because of self difined dist metric in hierarchical clustering dendrogram drawing part has been deleted"
    if (algName == 'Hierarchical') and ((cluster_res[2])[0] != ''):
        plt.figure(figsize=(40,15))
        plt.rc('font',family = 'Dejavu Sans',size = 15)
        plt.xlabel(make_farsi_text(('سوره')))
        plt.ylabel(make_farsi_text(('فاصله')))        
        dendrogram(
            cluster_res[2],
            labels = make_farsi_text2(svNm3),
            leaf_rotation = 90.,  # rotates the x axis labels
            leaf_font_size = 15.,  # font size for the x axis labels
            distance_sort = True            
            )
        plt.title('n_clusters: '+str(cluster_res[3])+', score: '+ str(cluster_res[4]))
        plt.savefig(frName+'_res'+str(plot_Nb)+'_dendrogram_msp'+str(msp)+'_f'+str(np_shape(inData1)[1])+'.png')
        plt.close('all')
    """plt.figure()
    plt.pie(grNb,labels =make_farsi_text2(svGL))
    plt.show()"""
    return list(ch_fNums),svN,svN3
"-----------------------------------------------------------------------------"
def calcSbgFr(inData1, dlChs, same_c):

    svlCn = 0
    ch_fNums = list(np_sum(np_asarray(inData1)>0,1))
    sh_sv = c_copy(dlChs)
    sh_sv.extend(list(chain(*np_asarray(same_c))))
    svN = []
    svN3 = []
    with open('nameSovar_c.txt','r') as svName:
        for svl in svName:
            if svlCn not in sh_sv:
                svN.append(svlCn)
                svN3.append(svl[0:-1])
            svlCn = svlCn+1
    return ch_fNums,svN,svN3
"-----------------------------------------------------------------------------"
def cluster_show_write_Test(inData1,frName,dlChs,same_c,msp,preSubFr,preSubFr_ch,typePrm0,typePrm1):
    "clear Dendrogram"
    svNm = []
    svNm3 = []
    svlCn = 0
    sh_sv = c_copy(dlChs)
    sh_sv.extend(list(chain(*np_asarray(same_c))))
    svN = []
    with open('nameSovar_c.txt','r') as svName:
        for svl in svName:
            svNm.append(svl)
            if svlCn not in sh_sv:
                svNm3.append(svl[0:-1])
                svN.append(svlCn)
            else:
                if svlCn in preSubFr_ch:
                    preSubFr_ch.remove(svlCn)
                    preSubFr.pop(svlCn)
            svlCn = svlCn+1
    frName = frName+ '_TextDendro_msp'+str(msp)+'.txt'
    frFile  = open(frName,"w")
    mdl = linkage(inData1, method=typePrm0[1],metric=typePrm1)
    for idxss in range(2,114):
        lbls = fcluster(mdl,idxss,criterion='maxclust')
        lbls = lbls.transpose()
        if(len(set(lbls)) == idxss): 
            "write"
            frFile.write(str(idxss)+':\n')
            for lblIdx in set(lbls):
                nHc = np_where(lbls==lblIdx)[0]
                for ClsMem in nHc:
                    frFile.write(svNm3[ClsMem]+'('+str(preSubFr[ClsMem])+'), ')
                frFile.write('\n')
            frFile.write("-----------\n")
    frFile.close()
    return
"-----------------------------------------------------------------------------"
def cluster_gs00_normal(inData,clusterType,fResName,prmStr,typePrm0,typePrm1,distMt):
    """ inData: n*d list contains all input sample (train & Test)
        output: achived model and write result to file """
    if clusterType == 'dbscan':
        print('Note! dbscan part is incomplete')
        return
        mdl = cluster.DBSCAN(eps=typePrm0, min_samples=typePrm1).fit(inData)
        lbls = mdl.labels_
    elif clusterType == 'spectral':
        print('Note! spectral part is incomplete')
        return
        mdl = cluster.SpectralClustering(
        n_clusters = typePrm0, eigen_solver='arpack',
        affinity=typePrm1).fit_predict(inData)
        lbls = mdl
    elif clusterType == 'AffintyPropagation':
        print('Note! AffintyPropagation part is incomplete')
        return
        mdl = cluster.AffinityPropagation(preference=typePrm0).fit(inData)
        lbls = mdl.labels_
        n_clusters = len(mdl.cluster_centers_indices_)
    elif clusterType == 'Hierarchical':
        if typePrm1 == 'self':
            if distMt != 'self':
                print('Error! metric for silhouette and clustering distance should be same')
                return
            cq = []
            cq2 = -20
            n_clusters = -2
            mdl_o = []
            inDt = np_reshape(np_asarray(list(map(int,(np_asarray(inData)>0).ravel()))),(np_shape(inData)[0],np_shape(inData)[1]))
            for idxss in range(2,20):
                lbls = fclusterdata(inDt,t=idxss,criterion='maxclust',metric=m_dist)
                lbls = lbls.transpose()
                lbls = lbls.tolist()
                if(len(set(lbls)) == idxss):
                    dataDistMat = m_dists(inDt)
                    cqq = silhouette_score(dataDistMat,lbls, metric='precomputed')
                    """if cqq == 'nan':
                        print('nn',cqq)
                        f= open('./inData.txt','w')
                        for line in inData:   
                            f.write(str(line)+'\n')                            
                        f.close()
                        return 
                    else:
                        if cqq!=-1000:
                            print(cqq)
                            f= open('./inData.txt','w')
                            for line in inData:   
                                f.write(str(line)+'\n')                            
                            f.close()
                            return"""          
                    """if (cqq>1) or (cqq<-1):
                        print('inData,lbls',inData,lbls)
                        print('Error! out of range cqq for above inData,lbls. cqq=',cqq)
                        return"""
                    cq.append([idxss,cqq])
                    if cqq>=cq2:
                        cq2 = c_copy(cqq)
                        n_clusters = c_copy(idxss)
                        mdl_o = c_copy(lbls)
                else:
                    cq.append([idxss,-100*len(set(lbls))]) 
            if len(mdl_o) == 0:
                "all in one cluster"
                mdl_o = (np_shape(inData)[0])*[1]
                n_clusters = 1
            if cq2 == -20:
                print (cq)
                return [cq,[],[''],0,-20]
            return [cq,mdl_o,[''],n_clusters,cq2]
        else:
            mdl = linkage(inData, method=typePrm0[1],metric=typePrm1)
            zz = mdl
            cq = []
            cq2 = -20
            n_clusters = -2
            mdl_o = []
            for idxss in range(2,20):
                lbls = fcluster(mdl,idxss,criterion='maxclust')
                lbls = lbls.transpose()
                lbls = lbls.tolist()
                if(len(set(lbls)) == idxss): 
                    cqq = silhouette_score(inData,lbls, metric=distMt)  
                    if cqq>1:
                        print('Error! there is silhouette_score more than 1!',cqq)
                        return
                    elif cqq<-1:
                        print('Error! there is silhouette_score less than -1!',cqq)
                        return
                    cq.append([idxss,cqq])
                    """if cqq == 'nan':
                        print('nn',cqq)
                        f= open('./inData.txt','w')
                        for line in inData:   
                            f.write(str(line)+'\n')                            
                        f.close()
                        return 
                    else:
                        if cqq>100:
                            print(cqq)
                            f= open('./inData.txt','w')
                            for line in inData:   
                                f.write(str(line)+'\n')                            
                            f.close()
                            return"""
                    """if (cqq>1) or (cqq<-1):
                        print('inData,lbls',inData,lbls)
                        print('Error! out of range cqq for above inData,lbls. cqq=',cqq)
                        return"""
                    if cqq >= cq2:
                        cq2 = c_copy(cqq)
                        n_clusters = c_copy(idxss)
                        mdl_o = c_copy(lbls)
                else:
                    cq.append([idxss,-100*len(set(lbls))])        
            if len(mdl_o) == 0:
                "all in one cluster"
                mdl_o = (np_shape(inData)[0])*[1]
                n_clusters = 1
            if n_clusters == -2:
                if cq2 == 1:
                    print("-----------ERROR!",cq) 
            return [cq,mdl_o,zz,n_clusters,cq2]
    if typePrm1 == 'self':
        if distMt != 'self':
            print('Error! metric for silhouette and clustering distance should be same')
            return
        dataDistMat = m_dists(np_reshape(np_asarray(list(map(int,(np_asarray(inData)>0).ravel()))),(np_shape(inData)[0],np_shape(inData)[1])))
        cq = silhouette_score(dataDistMat,lbls, metric='precomputed')
    else:
        cq = silhouette_score(inData,lbls, metric= distMt)
    return [cq,mdl]
"-----------------------------------------------------------------------------"
def cluster_gs00_bin(inData,clusterType,fResName,prmStr,typePrm0,typePrm1,distMt):
    if clusterType == 'dbscan':
        print('Note! dbscan part is incomplete')
        return
        mdl = cluster.DBSCAN(eps=typePrm0, min_samples=typePrm1).fit(inData)
        lbls = mdl.labels_
    elif clusterType == 'spectral':
        print('Note! spectral part is incomplete')
        return
        mdl = cluster.SpectralClustering(
        n_clusters=typePrm0, eigen_solver='arpack',
        affinity=typePrm1).fit_predict(inData)
        lbls = mdl
    elif clusterType == 'AffintyPropagation':
        print('Note! AffintyPropagation part is incomplete')
        return
        mdl = cluster.AffinityPropagation(preference=typePrm0).fit(inData)
        lbls = mdl.labels_
        n_clusters = len(mdl.cluster_centers_indices_)
    elif clusterType == 'Hierarchical':
        if typePrm1 == 'self':
            if distMt != 'self':
                print('Error! metric for silhouette and clustering distance should be same')
                return
            cq = []
            cq2 = -20
            n_clusters = -2
            mdl_o = []
            for idxss in range(2,20):
                lbls = fclusterdata(inData,t=idxss,criterion='maxclust',metric=m_dist)
                lbls = lbls.transpose()
                lbls = lbls.tolist()
                if(len(set(lbls)) == idxss):
                    dataDistMat = m_dists(inData)
                    cqq = silhouette_score(dataDistMat,lbls, metric='precomputed')
                    """if cqq == 'nan':
                        print('nn',cqq)
                        f= open('./inData.txt','w')
                        for line in inData:   
                            f.write(str(line)+'\n')                            
                        f.close()
                        return 
                    else:
                        if cqq!=-1000:
                            print(cqq)
                            f= open('./inData.txt','w')
                            for line in inData:   
                                f.write(str(line)+'\n')                            
                            f.close()
                            return"""          
                    """if (cqq>1) or (cqq<-1):
                        print('inData,lbls',inData,lbls)
                        print('Error! out of range cqq for above inData,lbls. cqq=',cqq)
                        return"""
                    cq.append([idxss,cqq])
                    if cqq>=cq2:
                        cq2 = c_copy(cqq)
                        n_clusters = c_copy(idxss)
                        mdl_o = c_copy(lbls)
                else:
                    cq.append([idxss,-100*len(set(lbls))])        
            if len(mdl_o) == 0:
                "all in one cluster"
                mdl_o = (np_shape(inData)[0])*[1]
                n_clusters = 1
            return [cq,mdl_o,[''],n_clusters,cq2]
        else:
            mdl = linkage(inData, method=typePrm0[1],metric=typePrm1)
            zz = mdl
            cq = []
            cq2 = -20
            n_clusters = -2
            mdl_o = []
            for idxss in range(2,20):
                lbls = fcluster(mdl,idxss,criterion='maxclust')
                lbls = lbls.transpose()
                lbls = lbls.tolist()
                if(len(set(lbls)) == idxss): 
                    cqq = silhouette_score(inData,lbls, metric=distMt)  
                    if cqq>1:
                        print('Error! there is silhouette_score more than 1!',cqq)
                        return
                    elif cqq<-1:
                        print('Error! there is silhouette_score less than -1!',cqq)
                        return
                    cq.append([idxss,cqq])
                    """if cqq == 'nan':
                        print('nn',cqq)
                        f= open('./inData.txt','w')
                        for line in inData:   
                            f.write(str(line)+'\n')                            
                        f.close()
                        return 
                    else:
                        if cqq>100:
                            print(cqq)
                            f= open('./inData.txt','w')
                            for line in inData:   
                                f.write(str(line)+'\n')                            
                            f.close()
                            return"""
                    """if (cqq>1) or (cqq<-1):
                        print('inData,lbls',inData,lbls)
                        print('Error! out of range cqq for above inData,lbls. cqq=',cqq)
                        return"""
                    if cqq>=cq2:
                        cq2 = c_copy(cqq)
                        n_clusters = c_copy(idxss)
                        mdl_o = c_copy(lbls)
                else:
                    "n_clusters = -2"
                    cq.append([idxss,-100*len(set(lbls))])        
            if len(mdl_o) == 0:
                "all in one cluster"
                mdl_o = (np_shape(inData)[0])*[1]
                n_clusters = 1
            return [cq,mdl_o,zz,n_clusters,cq2]
    if typePrm1 == 'self':
        if distMt != 'self':
            print('Error! metric for silhouette and clustering distance should be same')
            return
        dataDistMat = m_dists(inData)
        cq = silhouette_score(dataDistMat,lbls, metric='precomputed')
    else:
        cq = silhouette_score(inData,lbls, metric= distMt)
    return [cq,mdl]
"-----------------------------------------------------------------------------"
def gtb_setInits(dsNumber,w,wgh_state):
    "[trFile ad,window size,direction state,is Undirection,weight state,min supp]"
    dstbl = []  
    "1:just lemma from Quran source file+moghattaeh"
    dstbl.append(['q_justLem','','und',True,wgh_state,'','QjL_graphs_w'+str(w)+'.txt','QjLmodel','resTbl_QjL_w'+str(w)+'.txt','QjL_subGraphs_w'+str(w)+'.txt'])    
    "2:lemma if exist othewise the segment from Quran source file"
    dstbl.append(['q_Lem','','und',True,wgh_state,'','QLS_graphs_w'+str(w)+'.txt','QLSmodel','resTbl_QLS_w'+str(w)+'.txt','QLS_subGraphs_w'+str(w)+'.txt'])
    "3:just ROOT from Quran source file+some lemmas and some roots ommited,file in addition to chapters contain list of roots and lemmas"
    dstbl.append(['q_PNR-spKaAn-4','','und',True,wgh_state,'',GlPth+'w'+str(w)+'/QjR_graphs_w'+str(w)+'.txt','QjRmodel','resTbl_QjR_w'+str(w)+'.txt',GlPth+'w'+str(w)+'/QjR_subGraphs_w'+str(w)+'.txt'])
    "4:test"
    dstbl.append(['test','','und',True,wgh_state,'',GlPth+'w'+str(w)+'/QjR_graphs_w'+str(w)+'.txt','QjRmodel','resTbl_QjR_'+str(w)+'.txt',GlPth+'w'+str(w)+'/QjR_subGraphs_'+str(w)+'.txt']) 
    return dstbl[dsNumber-1]
"-----------------------------------------------------------------------------"
def writeGsRes2File(SortedGsRes,w_fileName,edNbLimit):
    "SortedGres:[[sorted subgraphs],[#edges],[index in frequent_subgraphs_obj],[support]"
    """write the graph with #edges higher than edNbLimit as text in file"""
    fsfn = open(w_fileName,'w')
    sgSubs = SortedGsRes[0]
    sgsNb = SortedGsRes[1] 
    sgsSp = SortedGsRes[2]
    "*********"
    "sgsSp = SortedGsRes[3]"
    "*********"
    edL = len(sgsNb)
    for edNIdx in range(len(sgsNb)-1,-1,-1):
        if(edNbLimit > sgsNb[edNIdx]):
            edL = edNIdx + 1
            break
    if edL == len(sgsNb):
        print('edge length limit is higher than max support of subgraphs' )    
        return
    subgIdx = 0
    for subg in sgSubs[edL:]:
        fsfn.write('t # '+str(subgIdx)+'\n')
        for vid in subg.vertices:
            fsfn.write('v '+str(vid)+' '+str(subg.vertices[vid].vlb)+'\n')
        for frm in subg.vertices:
            edges = subg.vertices[frm].edges
            for to in edges:
                if subg.is_undirected:
                    if frm < to:
                        fsfn.write('e '+str(frm)+' '+str(to)+' '+str(edges[to].elb)+'\n')
                else:
                    fsfn.write('e '+str(frm)+' '+str(to)+' '+str(edges[to].elb)+'\n')
        
        fsfn.write('\nSupport:'+str(sgsSp[subgIdx]))
        fsfn.write('\n-----------------\n') 
        subgIdx = subgIdx+1
    fsfn.close()
    return
"-----------------------------------------------------------------------------"
def KDmatching_new(cResult,omitedChaps,chapsC0,chpaSame):
    if(len(cResult)!=(len(chapsC0)-len(omitedChaps)-np_sum(list(map(len,chpaSame))))):
        print ('error in input args!!!!!!')
        print ('result labels:',len(cResult),cResult)
        print ('len deleted chaps+sames',(len(chapsC0)-len(omitedChaps)-np_sum(list(map(len,chpaSame)))),len(chapsC0),len(omitedChaps))
        print ('ommited pre,zero chapters,same chaps',chapsC0,omitedChaps,chpaSame)
        return
    mk01 = open('Makki_Madani01.txt','r')
    m_ch_o = mk01.readlines()
    mk01.close()
    chpsCnt = 0
    chapsC = list(set(chapsC0).difference(set(omitedChaps).union(set(chain(*chpaSame)))))
    chapsC.sort()
    cResult_KD = []
    for m in range(0,max(cResult)):
        cResult_KD.append([0,0])
    for mkmd_i in range(0,114):
        if mkmd_i in chapsC:    
            if int(m_ch_o[mkmd_i].replace('\n','')) == 0:
                (cResult_KD[cResult[chpsCnt]-1])[0] += 1    
            else:
                (cResult_KD[cResult[chpsCnt]-1])[1] += 1    
            chpsCnt +=1
    return cResult_KD
"-----------------------------------------------------------------------------"
def Mk_Matching1(cResult,omitedChaps,chapsC0,chpaSame_k,chpaSame,chpaSame_mkmd):
    if(len(cResult)!=(len(chapsC0)-len(omitedChaps)-np_sum(list(map(len,chpaSame))))):
        print ('error in input args!!!!!!')
        print ('result labels:',len(cResult),cResult)
        print ('len deleted chaps+sames',(len(chapsC0)-len(omitedChaps)-np_sum(list(map(len,chpaSame)))),len(chapsC0),len(omitedChaps))
        print ('ommited pre,zero chapters,same chaps',chapsC0,omitedChaps,chpaSame)
        return
    mk01 = open('Makki_Madani01.txt','r')
    m_ch_o = mk01.readlines()
    mk01.close()
    mk1_sum = 0
    md1_sum = 0
    mk2_sum = 0
    md2_sum = 0
    omMk = 0
    omMd = 0
    chpsCnt = 0
    chapsC = list(set(chapsC0).difference(set(omitedChaps).union(set(chain(*chpaSame)))))
    chapsC.sort()
    for mkmd_i in range(0,114):
        if mkmd_i in chapsC:
            if mkmd_i in chpaSame_k:
                sms = chpaSame_mkmd[chpaSame_k.index(mkmd_i)]
                omMk += sms[0]
                omMd += sms[1]
            else:
                sms=[0,0]
            if int(m_ch_o[mkmd_i].replace('\n','')) == 0:
                omMk += 1
                if (cResult[chpsCnt] == 1):
                    "match"
                    mk1_sum += 1 + sms[0]
                    md2_sum += sms[1]
                else:
                    if (cResult[chpsCnt] != 2):
                        print('Error! in makki-madani calc')
                        return
                    mk2_sum += 1 + sms[0]
                    md1_sum += sms[1]
            else:
                if int(m_ch_o[mkmd_i].replace('\n','')) != 1:
                    print ('Error! in makki-madani calc')
                    return
                omMd += 1
                if (cResult[chpsCnt] == 2):  
                    md1_sum += 1 + sms[1]
                    mk2_sum += sms[0]
                else:
                    if (cResult[chpsCnt] != 1):
                        print ('Error! in makki-madani calc')
                        return
                    md2_sum += 1 + sms[1]
                    mk1_sum += sms[0]
            chpsCnt += 1
    if mk1_sum+md1_sum > mk2_sum+md2_sum:
        mk_sum = mk1_sum
        md_sum = md1_sum
    else:
        mk_sum = mk2_sum
        md_sum = md2_sum
    if omMk == 0:
        print ('0 omMk wrong makki-madani result!')
        omMk = 1
    if  omMd == 0:
        print ('0 omMd wrong makki-madani result!')
        omMd = 1
    return mk_sum/(omMk), md_sum/(omMd), mk_sum+md_sum,mk_sum,omMk,md_sum,omMd
"-----------------------------------------------------------------------------"
def minSp_delOddFeatures_bin(in_vecs,f_min_supp):
    if type(in_vecs)==int:
        return in_vecs
    FSupp = in_vecs.sum(0)
    oddSupp = (FSupp<f_min_supp)
    IsOddCnt = 0
    oddIdx=[]
    "remove odd cols"
    for osEl in oddSupp:
        if(osEl == True):
            oddIdx.append(IsOddCnt)
        IsOddCnt = IsOddCnt+1
    out_vecs = np_delete(in_vecs,oddIdx,axis=1)
    out_vecs = out_vecs.tolist()
    return np_asarray(out_vecs)
"-----------------------------------------------------------------------------"
def minSp_delOddFeatures_normal(in_vecs,f_min_supp):
    if type(in_vecs)==int:
        return in_vecs
    FSupp = (in_vecs>0).sum(0)
    oddSupp = (FSupp<f_min_supp)
    IsOddCnt = 0
    oddIdx=[]
    "remove odd cols"
    for osEl in oddSupp:
        if(osEl == True):
            oddIdx.append(IsOddCnt)
        IsOddCnt = IsOddCnt+1
    out_vecs = np_delete(in_vecs,oddIdx,axis=1)
    return out_vecs
"-----------------------------------------------------------------------------"
def main_QchCluster_opt0(clusterAlg,clPrm1,dn,wSt,wSize,min_sup,mx_z,writeGr,chNb,SubSub_Diff):   
    "data set number: 1:Q1 2:Q2 3:Q3"
    gtb_ints = gtb_setInits(dn,wSize,wSt)
    docs_c = read_docs2(gtb_ints[0],chNb)
    "*****set initial parameters:*********"
    wSize = int(round(wSize))   
    dirSt = gtb_ints[2]
    "is undirected or not in boolean"
    wghSt = gtb_ints[4]
    "*************************************"
    docs_adj = []
    docs_ndNames = []
    tr_cr = []
    uniqLbls = []
    """
    ch_lengths = []
    plt.figure(figsize=(24,7))
    """
    "caseSt = ['Lem','LemW','Root']"
    "resPth1 = './results/chGraphs/'+str(caseSt[dn-1])+'/w'+str(wSize)"
    """visual_style = {}
    visual_style["vertex_size"] = 40
    "drl,kk,circle,fr,lgl,random,rt"
    visual_style["layout"] = 'rt'
    visual_style["bbox"] = (700, 700)
    visual_style["margin"] = 100"""
    for i in range(0,len(docs_c)):
        d_txt = docs_c[i]
        d_txtT = d_txt.split(' ')
        if d_txtT[-1] == '':
            print('Error1')
        dLL = list(map(len,d_txtT))
        if -1 in dLL:
            print('Error2',d_txtT[dLL.index(0)])
            return
        if 0 in dLL:
            print('Error2',d_txtT[dLL.index(0)])
            return
        if 1 in dLL:
            print('Error2',d_txtT[dLL.index(0)])
            return
        """
        ch_lengths.append(len(d_txtT))
        plt.text(i+0.5,len(d_txtT)+6,str(len(d_txtT)),size=7,color='black')
        """     
        tmp0 = m_wordAdjMat2(wSize,d_txtT,wghSt,dirSt)
        docs_adj.append(tmp0[0])
        docs_ndNames.append(tmp0[1])
        for trm in tmp0[1]:
            if trm not in uniqLbls:
                uniqLbls.append(trm)
        "1.extract graph of input documents:" 
        g = Graph(tmp0[0])
        "g.vs['label'] = tmp0[1]"
        g.vs['label'] = tmp0[1]
        if(wghSt == 'w'):
            g.es['weight']=tmp0[2]
            "g.es['label']=tmp0[2]"
        if(dirSt == 'd'):
            g.to_directed()
        """
        "visualize chapters graphs:"
        "if (i == 8) | (i>50):"
        "plt.rc('font',family = 'B Nazanin',size = 20)"
        if i in [112,102,109,86,8]:
            visual_style["vertex_label"] = make_farsi_text2(arbRoot(g.vs["label"],False))
            visual_style["vertex_label"][1] = make_farsi_text2(['*اله'])[0]
            print (visual_style["vertex_label"][1])
            visual_style["edge_label"] = g.es['weight']
            visual_style["vertex_color"] = "light blue"            
            chGp = plot(g,**visual_style)
            strResFig= resPath3+'/ch'+str(i+1)+'*_'+str(len(tmp0[1]))+'nodes'+str(len(tmp0[0]))+'edges.png'
            chGp.save(strResFig)
        """
        "**************************"        
        tr_cr.append(g)
    """
    "plot of chapter lengths:"
    plt.title('length of chapters')
    plt.xlabel('chapter number')
    plt.ylabel('number of roots')
    plt.xlim([0,115])
    plt.grid(axis=u'both')
    plt.bar(range(1,115),ch_lengths,color='blue',width=0.1)
    plt.savefig('./result97/chapters_Len.png')
    plt.close()
    """
    "3.reform graphs to compatible format to gspan code result in kcores.txt and run gSpan:"    
    if writeGr == 1:
        tr_crFile = open(gtb_ints[6],'w')
        gsInputForm_byIdx(tr_cr,tr_crFile,uniqLbls)
        tr_crFile.close()
    "run gSpan:"
    g_vecs = RanGs_pure(gtb_ints[6],uniqLbls,mx_z,wSize,chNb,SubSub_Diff,tr_cr)
    fLen = (np_shape(g_vecs))[1]
    if(fLen == 0):
        print ('support is too high!')
        return [-2],-2
    svNm = []
    with open('nameSovar_c.txt','r') as svName:
        for svl in svName:
            svNm.append(svl)
    plt.figure(figsize=(55,10))
    plt.grid()
    plt.rc('font',family = 'Dejavu Sans',size = 3)
    plt.xlabel(make_farsi_text('نام سوره'))
    plt.ylabel(make_farsi_text('تعداد ویژگی'))
    plt.xticks(range(1,chNb+1),make_farsi_text2(svNm))
    plt.bar(range(1,chNb+1),np_sum(g_vecs>0,1), width = 0.2, color='black')
    plt.savefig(clPrm1+'ch_features1_w'+str(wSize)+'.png')
    plt.close()
    fplt = open(clPrm1+'ch_features1_w'+str(wSize)+'.txt','w')
    ss_vv = ''
    for fpltc in svNm:
        ss_vv += fpltc+' '
    fplt.write(ss_vv+'\n')
    for fpltc in np_sum(g_vecs>0,1):
        fplt.write(str(fpltc)+' ')
    fplt.close()
    plt.figure(figsize=(55,10))
    plt.grid()
    plt.rc('font',family = 'DejaVu Sans',size = 10)
    plt.xlabel(make_farsi_text(('شماره سوره')))
    plt.ylabel(make_farsi_text(('تعداد ویژگی')))
    plt.xticks(range(1,chNb+1),range(1,chNb+1))
    plt.bar(range(1,chNb+1),np_sum(g_vecs>1,1), width = 0.2, color = 'black')
    plt.savefig(clPrm1+'ch_Nfeatures2_w'+str(wSize)+'.png')
    plt.close()
    prmS = 'window size:'+str(gtb_ints[1])+'min support:'+str(min_sup)+'%min support:'+str(gtb_ints[5])
    "write results in file:"
    fV = open(clPrm1+'OriginalInVecs.txt','w')
    for fVc in g_vecs.tolist():
        fVw = ''
        for fVcc in fVc:
            fVw += str(fVcc)+' '
        fV.write(fVw[0:-1]+'\n')
    fV.close()
    return [np_asarray(['compatible change']),gtb_ints[8],prmS],g_vecs
"-----------------------------------------------------------------------------"
def run_plot97_pre(my_wCnt,distCr,clsPrm,my_spCnt,sPth,max0Chap,writePriem,chapter_nm0,clusterMetr,clusterMetr_pca,my_dn,my_wSt,PCA_FN,mkMd_sufficient,PCAjp,sp_jp,dlSubGr_Diff,StdScl_F,dec_alg,minMxRMean,minMxRVar,tst_case):
    "!!!!!!!jump in dim cnt=-1 & max0Chap=10 has been changed"
    "برای اندازه پنجره‌های متفاوت بعد از حذف بردارهای صفر نمودارهای کمینه پشتیبان-کیفیت خوشه‌بندی به ازای هر روش و نیز با اعمال PCA و بدون آن تولید می‌شود. در پایان نیز مشخصات بهترین نتایج هم از نظر درصد و هم در صورت دوخوشه ای بودن تطابق با مکی-مدنی نوشته می‌شود تا بعد نمودار سلسله مراتبی مربوط به آن تولید و نتیجه از نظر معنایی مطالعه شود.‌"    
    my_labels = []

    if tst_case[0].find('test') != -1:
        cnt_plot = tst_case[2] - 1
        # code can be used after some changes for general compares (exa: a clustering with 3 and one with 4 clusters could be compared in 3-3 or 4-4 clusters by change cutt-off threshold of one of clustering)
        # but here beacause calcDiff_cls just can compare two clusters we need two clusters for all best clustering
        #so we add two if is not in tst_case[3]
        tst_clusters = c_copy(tst_case[3])
        if 2 not in tst_clusters:
            tst_clusters.insert(0,2)
        for myl in range(0,len(tst_clusters)):
            my_labels.append([])
    else:
        cnt_plot = 0
    cnt_vecFile = 0
    maxSil_pca = [-2,[],-2,[],2,[]]
    maxSil  = [-2,[],-2,[],2,[]]
    AlgN = 'Hierarchical'
    "['clustering method','clustering dist method','clustering dist',quality measure,dist in quality measure]"
    my_Prms = [AlgN,clsPrm,distCr,'silhouette']
    dim_acc_ = []
    pcaF_acc_ = []
    qual_acc_ = []
    

    plt.close('all')
    if StdScl_F > 1:
        print('Error! standard scaling flag should be 0 or 1')
        return
    elif StdScl_F < 0:
        print('Error! standard scaling flag should be 0 or 1')
        return
    "Report:"
    my_fRep0 = open(sPth+'report_opt_noPCA.txt','a')
    my_fRep4 = open(sPth+'report_opt_noPCA_all.txt','a')
    my_fRep1 = open(sPth+'report_opt_PCA.txt','a')
    my_fRep3 = open(sPth+'report_opt_PCA_all.txt','a')
    my_fRep2 = open(GlPth+'report_opt_MakkiMadani.txt','a')
    my_fRep0.write('plot#\t#clusters\ttype\twindowSize\t#chapter\t#feature\tminSupport\tQualityMeasure\t#True(Mk+Md)\t#mkTrue/#realMk\tmdTrue/realMd\t#realMK-#realMD in each cluster\tdelChapters\tsameChapters\n')
    my_fRep4.write('plot#\t#clusters\ttype\twindowSize\t#chapter\t#feature\tminSupport\tQualityMeasure\t#True(Mk+Md)\t#mkTrue/#realMk\tmdTrue/realMd\t#realMK-#realMD in each cluster\tdelChapters\tsameChapters\n')
    my_fRep1.write('plot#\t#clusters\ttype\twindowSize\t#chapter\tPCA dim\t#feature\tminSupport\tQualityMeasure\t#True(Mk+Md)\t#mkTrue\t#mdTrue\t#mkTrue/#realMk\#tmdTrue/#realMd\t#realMK-#realMD in each cluster\tdelChapters\tsameChapters\n')
    my_fRep3.write('plot#\t#clusters\ttype\twindowSize\t#chapter\tPCA dim\t#feature\tminSupport\tQualityMeasure\t#True(Mk+Md)\t#mkTrue\t#mdTrue\t#mkTrue/#realMk\#tmdTrue/#realMd\t#realMK-#realMD in each cluster\tdelChapters\tsameChapters\n')
    my_fRep2.write('plot#\tPCA \t #clusters\t type \t windowSize\t#chapter\t#feature\tminSupport\tQualityMeasure\t#true(Mk+Md)\t#trueMk/#realMk\t#trueMd/#realMd\t#trueMk\t#realMk\t#trueMd\t#realMd\t#realMK-#realMD in each cluster\tdelChapters\tsameChapters\nlabels\nInput surahs\n')
    "my_fRep45 = open(sPth+'report_opt_eigenvalues.txt','a')"
    my_caseSt=['Lem','LemW','Root','test']
    "spJp = [5,7,8,8,9,8,7,5,9]" 
    my_w_scores1 = []
    my_w_minSp1 = []
    my_w_scores2 = []
    my_w_minSp2 = []
    m_ft,m_ftArr = main_QchCluster_opt0('Hierarchical',sPth,my_dn,my_wSt,my_wCnt,my_spCnt,max0Chap,writePriem,len(chapter_nm0),dlSubGr_Diff)    
    """  
    "*****************************"    
    "read vectors from file:"
    ss3 = sPth+'InputVecs.txt'
    my_fRep3 = open(ss3,'r')
    m_ftArr = []
    for line in my_fRep3:
        line = line[:-1]
        m_ftArr.append(np_asarray(map(int,line.split(' '))))
    my_fRep3.close()
    m_ft = [np_asarray(m_ftArr),'resTbl_QjR.txt','window size:'+str('')+'min support:'+str(my_spCnt)]
    m_ftArr = np_asarray(m_ftArr)
    "afn = np_shape(m_ftArr)"
    "******************************"
    """
    "plot histogram of distance of vector pairs:"
    "compute distance matrix:"
    "DistMtCalc(distCr,m_ftArr,my_wCnt,afn[1],afn[0],'')"
    "******************************"
    plt.figure()
    plt.rc('font',family = 'Dejavu Sans',size = 7)
    pltTxLc=[]
    if (type(m_ftArr)==int):
        print ('no feature extracted')
    else:      
        best_mm = []
        my_if = []
        my_if = m_ft
        my_fRep0.write('----------gSapn->clustering----------\n')
        my_fRep4.write('----------gSapn->clustering----------\n*In all over Quran considered number of makki surahs is 86 and for madani surahs is 28\n')
        my_fRep1.write('---------gSapn->PCA->clustering---------\n')
        my_fRep2.write('-------------------------\n')
        my_fRep3.write('---------gSapn->PCA->clustering---------\n*In all over Quran considered number of makki surahs is 86 and for madani surahs is 28\n')
        "my_fRep45.write('*********\n window size = '+str(my_wCnt)+', \t min support= '+str(my_spCnt)+'\n')"      
        my_if.extend([my_Prms[0],my_Prms[1],clusterMetr])
        noPCA_dim = []
        chapter_nm = c_copy(chapter_nm0)
        max_my_spCnt = 114
        if tst_case[0].find('test') != -1:
            max_my_spCnt = tst_case[4]+1
            my_spCnt = tst_case[4]
        for my_spCntt in range(my_spCnt,max_my_spCnt,sp_jp):
            if(type(my_if[0])==int):
                break
            print ('sp:',my_spCntt,'\n')
            my_features = minSp_delOddFeatures_normal(m_ftArr,my_spCntt)
            "my_features = minSp_delOddFeatures_bin(m_ftArr,my_spCntt)"
            "print 'after del less than sp\n',my_features[0],np_shape(my_features)"
            featur_Nb = np_shape(my_features)
            "delete zero vectors and also report & remove common features between remained vector"
            if featur_Nb[1] < 1:
                print ('just few features so breaked')
                break
            my_features,my_0Chs,same_key,same_ch,same_mkMd = del0_twice_Chaps_normal(my_features,len(chapter_nm),[],cnt_vecFile)
            "my_features,my_0Chs,same_key,same_ch,same_mkMd = del0_twice_Chaps_bin(my_features,len(chapter_nm),[],cnt_vecFile)"
            featur_Nb = np_shape(my_features)            
            if featur_Nb[1] < 1:
                print ('just few features so breaked')
                break
            my_0Chs_in = c_copy(my_0Chs)
            my_0Chs_in.extend(list(chain(*same_ch)))
            my_0Chs_in.sort()
            "............................."           
            "write results in file:"
            fV = open(sPth+'clusteringInVecs_msp'+str(my_spCntt)+'.txt','w')
            for fVc in my_features:
                fVw = ''
                for fVcc in fVc:
                    fVw += str(fVcc)+' '
                fV.write(fVw[0:-1]+'\n')
            fV.close()
            "............................."            
            cnt_vecFile += 1
            zc = c_copy(len(my_0Chs))
            if zc > max0Chap:
                print ('zero vectors is more than limit')
                break
            "///////////"
            if my_features == []:
                print ('just few features so breaked')
                break
            else:
                if my_features[0].tolist() == []:
                    print ('just few features so breaked')                   
                    break
            if my_spCntt == my_spCnt:
                preF_Nb = c_copy(featur_Nb[1])
            "******************************"
            "plot histogram of distance of vector pairs:"
            "compute distance matrix:"
            "DistMtCalc(distCr,my_features,my_wCnt,featur_Nb[1],featur_Nb[0],str(my_spCntt))"
            "******************************" 
            my_res1 = cluster_gs00_normal(my_features,my_if[3],my_if[1],my_if[2],my_if[4],clusterMetr,distCr[0])
            cnt_plot += 1
            if maxSil[0] == my_res1[4]:
                maxSil[1].append(cnt_plot)
            elif maxSil[0] < my_res1[4]:
                maxSil[0], maxSil[1] = my_res1[4],[cnt_plot]          
            [mk1,md1,my_mmScore,mkTrue,mkReal,mdTrue,mdReal] = 7*['_']
            zeroChs0, _ = get_SovarNames2('nameSovar_c.txt',my_0Chs)
            strtmp=''
            for z_cnt in range(0,len(zeroChs0)):
                strtmp = str(zeroChs0[z_cnt])+', '+strtmp
            strtmp += ' ,same chaps: '
            for z_cnt in range(0,len(same_key)):
                strtmp += str(same_key[z_cnt])+', '+str(same_ch) 
            if my_res1[3] > 1:
                clusters_KD = KDmatching_new(my_res1[1],my_0Chs,chapter_nm,same_ch)
                clusters_KD_maxRate = np_asarray(list(map(max,clusters_KD)))/np_asarray(list(map(sum,clusters_KD)))
                clusters_KD_maxRate_var  = sqrt(var(clusters_KD_maxRate))
                clusters_KD_maxRate_mean = mean(clusters_KD_maxRate)
                if maxSil[2] == clusters_KD_maxRate_mean:
                    maxSil[3].append(cnt_plot)
                elif maxSil[2] < clusters_KD_maxRate_mean:
                    maxSil[2],maxSil[3]= clusters_KD_maxRate_mean,[cnt_plot]   
                if maxSil[4] == clusters_KD_maxRate_var:
                    maxSil[5].append(cnt_plot)
                elif maxSil[4] > clusters_KD_maxRate_var:
                    maxSil[4],maxSil[5]= clusters_KD_maxRate_var,[cnt_plot]  
                if my_res1[3] == 2:
                    mk1,md1,my_mmScore,mkTrue,mkReal,mdTrue,mdReal = Mk_Matching1(my_res1[1],my_0Chs,chapter_nm,same_key,same_ch,same_mkMd)                
                    if (my_mmScore/(114-zc) >= mkMd_sufficient) | (clusters_KD_maxRate_mean > minMxRMean) | (clusters_KD_maxRate_var < minMxRVar):
                        best_mm.append([cnt_plot,my_mmScore,my_spCntt,my_res1[4]])
                        if (clusters_KD_maxRate_mean > minMxRMean) | (clusters_KD_maxRate_var < minMxRVar):
                            "unified clusters according makki madani"
                            my_fRep2.write('**')
                        my_fRep2.write(str(cnt_plot)+'\tno \t'+str(my_res1[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(featur_Nb[0])+'\t'+str(featur_Nb[1])+'\t'+str(my_spCntt)+'\t'+str(my_res1[4])+'\t'+str(my_mmScore)+'\t'+str(mk1)+'\t'+str(md1)+'\t'+str(mkTrue)+'\t'+str(mkReal)+'\t'+str(mdTrue)+'\t'+str(mdReal)+'\t'+str(clusters_KD)+'\t'+str(clusters_KD_maxRate_mean)+'\t'+str(clusters_KD_maxRate_var)+'\t'+str(my_0Chs)+'\n')
                        my_fRep2.write(str(my_res1[1])+'\n')
                        my_fRep2.write(str(chapter_nm)+'\n-----------------------------\n')
                else:
                    if (clusters_KD_maxRate_mean > minMxRMean) | (clusters_KD_maxRate_var < minMxRVar):
                        "unified clusters according makki madani"
                        best_mm.append([cnt_plot,-1,my_spCntt,my_res1[4]])
                        my_fRep2.write('**'+str(cnt_plot)+'\tno \t'+str(my_res1[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(featur_Nb[0])+'\t'+str(featur_Nb[1])+'\t'+str(my_spCntt)+'\t'+str(my_res1[4])+'\t'+'_\t_\t_\t_\t_\t_\t_\t'+str(clusters_KD)+'\t'+str(clusters_KD_maxRate_mean)+'\t'+str(clusters_KD_maxRate_var)+'\t'+str(my_0Chs)+'\n')
                        my_fRep2.write(str(my_res1[1])+'\n')
                        my_fRep2.write(str(chapter_nm)+'\n-----------------------------\n')
                preSbg_fr,preSbg_frIdx,preSbg_frName = cluster_show_write(my_features,my_res1,sPth,AlgN,'',my_0Chs,cnt_plot,chapter_nm0,distCr[0],same_key,same_ch,same_mkMd,my_spCntt,preF_Nb,[],[])
                my_w_scores1.append(my_res1[4])
                my_w_minSp1.append(my_spCntt)
                plt.text(my_spCntt,my_res1[4]+0.01,str(my_res1[3])+'_'+str(featur_Nb[1]))
                noPCA_dim.append(featur_Nb[1])            
                my_fRep0.write(str(cnt_plot)+'\t'+str(my_res1[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(featur_Nb[0])+'\t'+str(featur_Nb[1])+'\t'+str(my_spCntt)+'\t'+str(my_res1[4])+'\t'+str(my_mmScore)+'\t'+str(mkTrue)+'\t'+str(mdTrue)+'\t'+str(mk1)+'\t'+str(md1)+'\t'+str(clusters_KD)+'\t'+str(clusters_KD_maxRate_mean)+'\t'+str(clusters_KD_maxRate_var)+'\t'+strtmp+'\n')
                my_fRep4.write(str(cnt_plot)+'\t'+str(my_res1[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(featur_Nb[0])+'\t'+str(featur_Nb[1])+'\t'+str(my_spCntt)+'\t'+str(my_res1[4])+'\t'+str(my_mmScore)+'\t'+str(mkTrue)+'\t'+str(mdTrue)+'\t'+str(mk1)+'\t'+str(md1)+'\t'+str(clusters_KD)+'\t'+str(clusters_KD_maxRate_mean)+'\t'+str(clusters_KD_maxRate_var)+'\t'+strtmp+'\n')
            else:
                my_fRep4.write(str(cnt_plot)+'\t'+str(my_res1[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(featur_Nb[0])+'\t'+str(featur_Nb[1])+'\t'+str(my_spCntt)+'\t'+str(my_res1[4])+'\t'+str(my_mmScore)+'\t'+str(mkTrue)+'\t'+str(mdTrue)+'\t'+str(mk1)+'\t'+str(md1)+'\t_.._\t'+strtmp+'\n')
                preSbg_fr,preSbg_frIdx,preSbg_frName = calcSbgFr(my_features,my_0Chs,same_ch)
            "#clusters_#dimensions=#features"
            "plt.text(my_spCntt,my_res1[4]+0.01,str(my_res1[3])+'_'+str(featur_Nb[1]))"
            "plt.text(my_spCntt-0.025,0.06,str(zc),color='green')"               
            "strtmp =''"
            if (featur_Nb[1] > PCA_FN) and (PCAYN == 'Y'):
                "perform PCA"
                my_fRep3.write('............\n')
                my_pca = 'k'
                "to choose good n_dim"
                "b_my_res2L = 0"
                b_dim = 0
                b_my_res2clN = 0 
                b_my_res2 = -1
                b_0Chs = []
                b_cnt_plot = -1
                dec2 = min(featur_Nb[1],featur_Nb[0])-1
                "print '**',np_shape(my_features)"
                pcaF_acc = []
                dim_acc = []
                qual_acc = []
                if tst_case[0].find('test') != -1:
                    endDim = tst_case[1]-1
                    dimCnt = tst_case[1]
                else:
                    endDim = 1
                    dimCnt = dec2
                if clusterMetr_pca.find('cosine') == -1:
                    endDim = 0
                PCAjp_1 = c_copy(PCAjp)
                while dimCnt> endDim:
                    if dimCnt > featur_Nb[1]:
                        dimCnt = c_copy(featur_Nb[1])
                    print('dim: ',dimCnt)
                    """???????scale of binary???
                    my_features_s = StandardScaler().fit_transform(my_features)"""
                    if StdScl_F == 1:
                        my_features_s = StandardScaler().fit_transform(my_features)
                    elif dec_alg.find('LPCA') == -1:
                        my_features_s = c_copy(my_features)
                    if dec_alg.find('LPCA') == -1:
                        if  issparse(my_features_s):
                            print('Sparse!!!!!!!!so if you tried PCA, TruncatedSVD is going to perform instead!!!!')
                            my_fRep3.write('\nSparse!!! so TruncatedSVD has been performed')                     
                            my_pca = TruncatedSVD(n_components=dimCnt)
                            c0 = my_pca.fit_transform(my_features_s)                                                                                                                                                                                                                                                                                                                                                                                                  
                        else:
                            if dec_alg.find('PCA') != -1:
                                print ('PCA',len(my_features_s))
                                my_pca = PCA(n_components=dimCnt, svd_solver='auto')
                                my_pca.fit(my_features_s)
                                if dimCnt == dec2:
                                    f_plt0 = plt.figure()
                                    plt.rc('font',family = 'Dejavu Sans',size = 8)
                                    f_plt = f_plt0.gca()
                                    f_plt.plot(my_pca.explained_variance_,marker='o')
                                    plt.grid(axis=u'both')
                                    plt.xlabel('eigen number')
                                    plt.ylabel('eigen value')
                                    plt.savefig(sPth+'dim'+str(dimCnt)+'_msp'+str(my_spCntt)+'_w'+str(my_wCnt)+'eigens.png')                        
                                    plt.close()
                                """if dimCnt ==114-zc:
                                    my_eigVals = my_pca.explained_variance_"""
                                c0 = my_pca.transform(my_features_s)
                            elif dec_alg.find('TruncatedSVD') != -1:
                                print('TruncatedSVD')
                                my_pca = TruncatedSVD(n_components=dimCnt)
                                c0 = my_pca.fit_transform(my_features_s)
                            else:
                                print(dec_alg,'invalid dimentionality reduction algorithm')
                    else:
                        "LPCA:"
                        my_features = np_asarray(my_features)
                        nr,nc = my_features.shape
                        X = robjects.r.matrix(my_features, nrow=nr, ncol=nc)
                        """robjects.r.assign("B", X)"""
                        "x = r_mat(r_c(0,0,1,1,0,1,1,1,1,1,0,0,0,1,1), nrow = 3)"
                        "r_lpca = r_logisticPCA.logisticPCA(X,k=2, m=4)"
                        r_lpca = r_logisticPCA.cv_lpca(X, ks = dimCnt, ms = robjects.r.seq(1, 10, by = 1))
                        "print(r_logisticPCA.predict_lpca(r_lpca))"
                        "print(r_logisticPCA.predict_lpca(r_lpca,r_mat(r_c(0,0,1,1,0), nrow = 1)))"
                        "print(r_logisticPCA.predict_lpca(r_lpca,X))"
                        c0 = (np_asarray(list(r_logisticPCA.predict_lpca(r_lpca))).reshape(dimCnt,nr)).transpose()
                        "print(list(r_logisticPCA.predict_lpca(r_lpca)))"
                        fV = open(sPth+'InVecs_msp'+str(my_spCntt)+'.txt','w')
                        for fVc in c0:
                            fVw = ''
                            for fVcc in fVc:
                                fVw += str(fVcc)+' '
                            fV.write(fVw[0:-1]+'\n')
                        fV.write('nrow:'+str(nr)+'ncol:'+str(nc))
                        fV.close()
                        my_features = list(my_features)                            
                    "c,my_0Chs_pca0,same_key2,same_ch2,same_mkMd2 = del0_twice_Chaps(c0,len(chapter_nm0),my_0Chs_in,cnt_vecFile)"
                    if not len(c0):
                        print('just few features so breaked')
                        break
                    else:
                        if c0[0].tolist() == []:
                            print ('just few features so breaked')                    
                            break
                    cnt_vecFile += 1
                    "my_res2 = cluster_gs00_bin(c0,my_if[3],my_if[1],my_if[2],my_if[4],clusterMetr_pca,distCr[1])"
                    my_res2 = cluster_gs00_normal(c0,my_if[3],my_if[1],my_if[2],my_if[4],clusterMetr_pca,distCr[1])                    
                    """if type(my_res2[1]) == list:
                        my_labels.append([lbl_conv(my_res2[1],my_0Chs,same_ch),my_res2[4]])
                    else:
                        my_labels.append([lbl_conv(my_res2[1].labels_,my_0Chs,same_ch),my_res2[4]])
                    """
                    if tst_case[0].find('test') != -1:
                        my_labels[tst_clusters.index(my_res2[3])] =[lbl_conv(np_asarray(my_res2[1]),my_0Chs,same_ch,same_key),my_res2[4]]
                        for clRange in tst_clusters:
                            if clRange == my_res2[3]:
                                "my_labels.append([[],-100])"
                                continue
                            mdl = linkage(c0, method=my_if[4][1],metric=clusterMetr_pca)
                            lbls2 = fcluster(mdl,clRange,criterion='maxclust')
                            lbls2 = lbls2.transpose()
                            "lbls2 = lbls2.tolist() "
                            cq_2 = silhouette_score(c0,lbls2, metric=clusterMetr_pca) 
                            my_labels[tst_clusters.index(clRange)] = [lbl_conv(lbls2,my_0Chs,same_ch,same_key),cq_2]
                        "(tst_case[3])[tst_case[3].index(my_res2[3])] -= 0.5 # to manage same number of clusters"

                    if maxSil_pca[0] == my_res2[4]:
                        maxSil_pca[1].append(cnt_plot)
                    elif maxSil_pca[0] < my_res2[4]:
                        maxSil_pca[0], maxSil_pca[1] = my_res2[4],[cnt_plot]
                    [mk1,md1,my_mmScore,mkTrue,mkReal,mdTrue,mdReal] = 7*['_']
                    if my_res2[3] > 1:
                        clusters_KD = KDmatching_new(my_res2[1],my_0Chs,chapter_nm0,same_ch)
                        clusters_KD_maxRate = np_asarray(list(map(max,clusters_KD)))/np_asarray(list(map(sum,clusters_KD)))
                        clusters_KD_maxRate_var  = sqrt(var(clusters_KD_maxRate))
                        clusters_KD_maxRate_mean = mean(clusters_KD_maxRate)
                        cluster_show_write(c0,my_res2,sPth+'PCA_',AlgN,'',my_0Chs,cnt_plot,chapter_nm0,distCr[1],same_key,same_ch,same_mkMd,my_spCntt,preF_Nb,preSbg_fr,preSbg_frIdx)
                        if maxSil_pca[2] == clusters_KD_maxRate_mean:
                            maxSil_pca[3].append(cnt_plot)
                        elif maxSil_pca[2] < clusters_KD_maxRate_mean:
                            maxSil_pca[2],maxSil_pca[3]= clusters_KD_maxRate_mean,[cnt_plot]   
                        if maxSil_pca[4] == clusters_KD_maxRate_var:
                            maxSil_pca[5].append(cnt_plot)
                        elif maxSil_pca[4] > clusters_KD_maxRate_var:
                            maxSil_pca[4],maxSil_pca[5]= clusters_KD_maxRate_var,[cnt_plot]
                        if my_res2[3] == 2:
                            mk1,md1,my_mmScore,mkTrue,mkReal,mdTrue,mdReal = Mk_Matching1(my_res2[1],my_0Chs,chapter_nm0,same_key,same_ch,same_mkMd)
                        """else:
                            mk1,md1,my_mmScore,mkTrue,mkReal,mdTrue,mdReal = 0,0,0,0,0,0,0"""
                        if (my_res2[4] > b_my_res2):
                            b_my_res2 = c_copy(my_res2[4])
                            b_my_res2clN = c_copy(my_res2[3])
                            "b_my_res2L = c_copy(my_res2[1])"
                            b_chNum = c_copy(np_shape(c0)[0])
                            b_pcaDim = dimCnt
                            b_dim = c_copy(np_shape(c0)[1])
                            b_0Chs = c_copy(my_0Chs)
                            "b_chapter_nm = c_copy(chapter_nm0)"
                            b_cnt_plot = cnt_plot
                            b_my_mmScore = my_mmScore
                            "mk,md,mkscore"                            
                            b_mks=[mk1,md1,my_mmScore,mkTrue,mkReal,mdTrue,mdReal]
                        pcaF_acc.append(np_shape(c0)[1])
                        dim_acc.append(dimCnt)
                        qual_acc.append(my_res2[4])
                        zeroChs0,_ = get_SovarNames2('nameSovar_c.txt',my_0Chs)
                        my_fRep3.write(str(cnt_plot)+'\t'+str(my_res2[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(np_shape(c0)[0])+'\t'+str(dimCnt)+'\t'+str(np_shape(c0)[1])+'\t'+str(my_spCntt)+'\t'+str(my_res2[4])+'\t'+str(my_mmScore)+'\t'+str(mkTrue)+'\t'+str(mdTrue)+'\t'+str(mk1)+'\t'+str(md1)+'\t'+str(clusters_KD)+'\t'+str(clusters_KD_maxRate_mean)+'\t'+str(clusters_KD_maxRate_var)+'\t'+strtmp+'\n')
                    else:
                        zeroChs0,_ = get_SovarNames2('nameSovar_c.txt',my_0Chs)                
                        my_fRep3.write(str(cnt_plot)+'\t'+str(my_res2[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(np_shape(c0)[0])+'\t'+str(dimCnt)+'\t'+str(np_shape(c0)[1])+'\t'+str(my_spCntt)+'\t'+str(my_res2[4])+'\t'+str(my_mmScore)+'\t'+str(mkTrue)+'\t'+str(mdTrue)+'\t'+str(mk1)+'\t'+str(md1)+'\t_..._\t'+strtmp+'\n')                    

                    
                    """strtmp=''        
                    for z_cnt in range(0,len(zeroChs0)):
                        strtmp = str(zeroChs0[z_cnt])+', '+strtmp
                        "strtmp = str(unicode(zeroChs0[z_cnt]))+', '+strtmp"   """
                    if my_res2[3] == 2:
                        "87% of 114 chapters is 100"
                        "_,_,my_mmScore,mkTrue,mkReal,mdTrue,mdReal = Mk_Matching1(b_my_res2L,b_0Chs,b_chapter_nm,same_key,same_ch,same_mkMd)"
                        if (my_mmScore/(114-zc) >= mkMd_sufficient) | (clusters_KD_maxRate_mean > minMxRMean) | (clusters_KD_maxRate_var < minMxRVar):
                            if (clusters_KD_maxRate_mean > minMxRMean) | (clusters_KD_maxRate_var < minMxRVar):
                                my_fRep2.write('**')
                            if b_my_mmScore == my_mmScore:
                                my_fRep2.write(str(cnt_plot)+'*\tyes\t'+str(my_res2[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(np_shape(c0)[0])+'\t'+str(dimCnt)+'\t'+str(np_shape(c0)[1])+'\t'+str(my_spCntt)+'\t'+str(my_res2[4])+'\t'+str(my_mmScore)+'\t'+str(mkTrue)+'\t'+str(mkReal)+'\t'+str(mdTrue)+'\t'+str(mdReal)+'\t'+str(mk1)+'\t'+str(md1)+'\t'+str(clusters_KD)+'\t'+str(clusters_KD_maxRate_mean)+'\t'+str(clusters_KD_maxRate_var)+'\t'+strtmp+'\n')
                            else:
                                my_fRep2.write(str(cnt_plot)+'\tyes\t'+str(my_res2[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(np_shape(c0)[0])+'\t'+str(dimCnt)+'\t'+str(np_shape(c0)[1])+'\t'+str(my_spCntt)+'\t'+str(my_res2[4])+'\t'+str(my_mmScore)+'\t'+str(mkTrue)+'\t'+str(mkReal)+'\t'+str(mdTrue)+'\t'+str(mdReal)+'\t'+str(mk1)+'\t'+str(md1)+'\t'+str(clusters_KD)+'\t'+str(clusters_KD_maxRate_mean)+'\t'+str(clusters_KD_maxRate_var)+'\t'+strtmp+'\n')
                            my_fRep2.write(str(my_res2[1])+'\n')
                            my_fRep2.write(str(chapter_nm)+'\n')
                    elif my_res2[3]>1:
                        if(clusters_KD_maxRate_mean > minMxRMean) | (clusters_KD_maxRate_var < minMxRVar):
                            my_fRep2.write('**'+str(cnt_plot)+'\tyes\t'+str(my_res2[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(np_shape(c0)[0])+'\t'+str(dimCnt)+'\t'+str(np_shape(c0)[1])+'\t'+str(my_spCntt)+'\t'+str(my_res2[4])+'\t_\t_\t_\t_\t_\t_\t_\t'+str(clusters_KD)+'\t'+str(clusters_KD_maxRate_mean)+'\t'+str(clusters_KD_maxRate_var)+'\t'+strtmp+'\n')
                    """if my_res2[3] ==2:

                    else:
                        my_fRep3.write(str(cnt_plot)+'\t'+str(my_res2[3])+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(np_shape(c0)[0])+'\t'+str(dimCnt)+'\t'+str(np_shape(c0)[1])+'\t'+str(my_spCntt)+'\t'+str(my_res2[4])+'\t_\t_\t_'+strtmp+'\n') """                  
                    "strtmp=''  "                  
                    cnt_plot += 1
                    if (PCAjp_1 > 1) & (dimCnt - PCAjp_1 < 10) & (tst_case[0].find('test') == -1):
                        dimCnt = 10
                        PCAjp_1 = 1
                    else:
                        dimCnt -= PCAjp_1
                if tst_case[0].find('test') != -1:
                    cluster_show_write_Test(c0,sPth+'PCA_',my_0Chs,same_ch,my_spCntt,preSbg_fr,preSbg_frIdx,my_if[4],clusterMetr_pca)
                pcaF_acc_.append(pcaF_acc)
                dim_acc_.append(dim_acc)
                qual_acc_.append(qual_acc)
                if(b_my_res2clN > 1):
                    my_w_scores2.append(b_my_res2)
                    my_w_minSp2.append(my_spCntt)
                    "plt.text(my_spCntt,b_my_res2+0.01,str(b_my_res2clN)+'_'+str(b_dim))"
                    if b_my_res2clN == 2:
                        "87% of 114 chapters is 100"
                        "_,_,my_mmScore,mkTrue,mkReal,mdTrue,mdReal = Mk_Matching1(b_my_res2L,b_0Chs,b_chapter_nm,same_key,same_ch,same_mkMd)"
                        if b_my_mmScore/(114-zc)>=mkMd_sufficient:
                            best_mm.append([b_cnt_plot,b_mks[2],my_spCntt,b_my_res2,b_dim])
                    txXL, txYL=  my_spCntt, b_my_res2+0.03
                    exCn = 0
                    while exCn != 1:
                        for (aX,aY) in pltTxLc:
                            if aX == txXL:
                                if abs(aY-txYL) < 0.07:
                                    txYL = txYL +0.14
                                    break
                        exCn = 1
                    "#clusters_#dimensions"
                    "plt.text(txXL,txYL,str(b_my_res2clN)+'_'+str(b_dim))"
                    pltTxLc.append((txXL,txYL))
                    zeroChs0,_ = get_SovarNames2('nameSovar_c.txt',b_0Chs)                
                    """strtmp=''        
                    for z_cnt in range(0,len(zeroChs0)):
                        strtmp = str(zeroChs0[z_cnt])+', '+strtmp
                        "strtmp = str(unicode(zeroChs0[z_cnt]))+', '+strtmp" """
                    my_fRep1.write(str(b_cnt_plot)+'\t'+str(b_my_res2clN)+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(b_chNum)+'\t'+str(b_pcaDim)+'\t'+str(b_dim)+'\t'+str(my_spCntt)+'\t'+str(b_my_res2)+'\t'+str(b_mks[2])+'\t'+str(b_mks[0])+'\t'+str(b_mks[1])+'\t'+strtmp+'\n')
                    "strtmp=''"
                elif b_my_res2clN == 1:
                    zeroChs0,_ = get_SovarNames2('nameSovar_c.txt',b_0Chs)                
                    """strtmp=''       
                    for z_cnt in range(0,len(zeroChs0)):
                        "strtmp = str(unicode(zeroChs0[z_cnt]))+', '+strtmp"
                        strtmp = str(zeroChs0[z_cnt])+', '+strtmp"""
                    my_fRep1.write(str(b_cnt_plot)+'\t'+str(b_my_res2clN)+'\t'+str(my_caseSt[my_dn-1])+'\t'+str(my_wCnt)+'\t'+str(b_chNum)+'\t'+str(b_pcaDim)+'\t'+str(b_dim)+'\t'+str(my_spCntt)+'\t'+str(b_my_res2)+'\t'+strtmp+'\n')
                    my_fRep1.write('\n NOTE! clustering caused united case!\n')
            """else:
                print('number of features,sp:',featur_Nb[1],my_spCntt)"""

        my_fRep0.close()
        my_fRep1.close()
        """my_fRep2.write('\n************\nbest in both makki-madani matching & silhouette score was:\n#plot,#(TrueMk+TureMd),sp,silhouette score,dimension(if pca)\n'+str(best_mm))
        for best_mmc in best_mm:
            my_fRep2.write(str(best_mm))"""
        my_fRep2.close()
        "my_fRep45.write(str(my_eigVals))"
        "my_fRep45.close()"
        plt.rc('font',family = 'Dejavu Sans',size = 9)
        plt.xlabel(make_farsi_text(('کمینه پشتیبان')))
        plt.ylabel(make_farsi_text(('مقدار'))+'silhouette')
        my_Prms_d=my_Prms[1]
        plt.title(my_Prms[0]+make_farsi_text(('پارامترهای خوشه‌بندی'))+':\n'+my_Prms_d[1]+'/dist at noPCA_PCA: '+str(distCr[0])+','+str(distCr[1])+'/'+str(my_wCnt)+':'+make_farsi_text(('اندازه پنجره'))+'/'+str(PCA_FN)+':'+make_farsi_text(('محدودیت اعمال PCA')))
        "+'/'+str(max0Chap)+':'+make_farsi_text(('حداکثر تعداد مجاز سوره‌ی حذف‌شده')))"
        plt.plot(my_w_minSp1,my_w_scores1, label = 'gSpan + clustering',marker='o',color='blue' )
        plt.plot(my_w_minSp2,my_w_scores2, label = 'gSpan+ PCA + clustering',marker='x',color='green',linestyle='--')
        plt.legend(loc='lower right')
        plt.grid(axis=u'both')
        plt.ylim([-2,1])
        plt.savefig(sPth+'msp-sil_w'+str(my_wCnt)+'.png')        
        plt.close('all')
        
        fig = plt.figure(figsize=(20,10))
        plt.rc('font',family = 'Dejavu Sans',size = 8)
        ax = fig.gca(projection='3d')
        ax.plot(my_w_minSp1,noPCA_dim,my_w_scores1,marker='o')
        ax.legend()
        ax.set_xlim([0,60])
        "ax.set_ylim([0,max_f])"
        ax.set_zlim([-1.05,1.05])
        ax.set_xlabel(make_farsi_text(('کمینه پشتیبان')))
        ax.set_zlabel(make_farsi_text(('مقدار silhouette')))
        ax.set_ylabel(make_farsi_text(('تعداد ویژگی')))
        plt.savefig(GlPth+'msp-sil-f_w'+str(my_wCnt)+'.png')
        plt.close()

        fArch1 = open(sPth+'msp-sil_w'+str(my_wCnt)+'.txt','w')
        fArch1.write('my_w_minSp1:\n'+str(my_w_minSp1)+'\nmy_w_scores1:\n'+str(my_w_scores1)+'\ndimensions:'+str(noPCA_dim)+'\nmy_w_minSp2:\n'+str(my_w_minSp2)+'\nmy_w_scores2:\n'+str(my_w_scores2)+'\n')        
        "fArch1.write(make_farsi_text(('مقدار معیار ۱۰- به معنای عدم خوشه‌بندی در محدوده‌ی مجاز تعداد خوشه است.'))+'\n')"
        fArch1.close()    
        if PCAYN == 'Y':
            "to investigate quality metric change for min min support:"
            fArch1 = open(sPth+'score change_w'+str(my_wCnt)+'.txt','w')
            plt.figure(figsize=(20,15)) 
            plt.rc('font',family = 'Dejavu Sans',size = 7)
            plt.legend()
            plt.title(my_Prms[3]+' '+make_farsi_text(('تغییر مقدار silhouette'))+'\n'+my_Prms[0]+'/'+make_farsi_text(('پارامترهای خوشه‌بندی'))+':'+my_Prms_d[0]+','+my_Prms_d[1]+'/dist at noPCA_PCA: '+str(distCr[0])+'_'+str(distCr[1])+'_'+make_farsi_text(('اندازه پنجره'))+': '+str(my_wCnt))
            for iPlt in range(0,len(pcaF_acc_)):
                pca_s = np_argsort(pcaF_acc_[iPlt])
                pcaF_acc = np_asarray(pcaF_acc_[iPlt])
                qual_acc = np_asarray(qual_acc_[iPlt])
                dim_acc = np_asarray(dim_acc_[iPlt])
                "print 5,floor(len(pcaF_acc_)/5)+((mod(len(pcaF_acc_),5)!=0)*1)"
                plt.subplot(5,floor(len(pcaF_acc_)/5)+((mod(len(pcaF_acc_),5)!=0)*1),iPlt+1)
                plt.grid(axis=u'both')                
                plt.ylabel(my_Prms[3])
                plt.ylim([-1.01,1.01])
                plt.title('sp:'+str(my_spCnt+iPlt*sp_jp))
                plt.plot(pcaF_acc[pca_s],qual_acc[pca_s],marker='o',label = 'gSpan->PCA->hierarchcal clustering' )            
                fArch1.write('sp:'+str(my_spCnt+iPlt*sp_jp)+'\nfeature_acc:\n'+str(pcaF_acc[pca_s])+'\nqual_acc:\n'+str(qual_acc[pca_s])+'\nPCAdim_acc:\n'+str(dim_acc[pca_s])+'\n')            
            plt.xlabel(make_farsi_text(('تعداد ویژگی')))
            plt.savefig(sPth+'score change_w'+str(my_wCnt)+'.png')        
            plt.close()
            fArch1.close()
            """fig = plt.figure(figsize=(20,10))
            ax = fig.gca(projection='3d')
            ax.plot(pcaF_acc[pca_s],qual_acc[pca_s],dim_acc[pca_s],marker='o',label = 'gSpan->PCA->hierarchcal clustering' )
            ax.legend()
            ax.grid(axis=u'both')
            ax.set_ylim([-1.05,1.05])
            ax.set_xlabel(make_farsi_text(('تعداد ویژگی')))
            ax.set_ylabel(make_farsi_text(('مقدار silhouette')))
            ax.set_zlabel(make_farsi_text(('تعداد بعد PCA قبل از حذف بردارهای صفر و مشترک‌ها')))
            plt.title(my_Prms[3]+' '+make_farsi_text(('تغییر مقدار silhouette'))+'\n'+my_Prms[0]+'/'+make_farsi_text(('پارامترهای خوشه‌بندی'))+':'+my_Prms_d[0]+','+my_Prms_d[1]+'/dist at noPCA_PCA: '+str(distCr[0])+str(distCr[1])+'_'+make_farsi_text(('اندازه پنجره'))+': '+str(my_wCnt))
            plt.savefig(GlPth+'d3score change_w'+str(my_wCnt)+'.png')
            plt.close()
            """
        """*********!!!!!!!!!!!!!!!!!!!!!!********
        "plot top eigen values:"
        plt.figure()
        plt.ylabel('value')
        plt.xlabel('index of sorted eigenvalues')
        "my_pca_nc = np_shape(my_eigVals)"

        xdata = range(0,my_pca_nc[0])
        plt.title('top eigen values of covariance matrix of data')
        "in marron 2009 i=1:d"        
        plt.xlim([1,115])
        plt.scatter(xdata,my_eigVals,marker='o',color='green',label='eigen values')
        plt.grid(axis=u'both')
        xdata = np_asarray(xdata)
        popt1, _ = curve_fit(fitF1, xdata, my_eigVals)
        plt.plot(xdata, fitF1(xdata, *popt1), 'r-',label='fit: C=%5.3f' % (popt1))
        popt2, _ = curve_fit(fitF2, xdata, my_eigVals)
        plt.plot(xdata, fitF2(xdata, *popt2), 'b-',label='fit: beta=%5.3f' % (popt2))
        plt.legend()
        plt.savefig(sPth+'eigenValues_w'+str(my_wCnt)+'.png')
        plt.close()  
        *****************!!!!!!!!!!!!!************
        """
        
        """        
        "show best result clusters:"
        best_all_mk
        best_all_noPCA = my_w_scores1.index(max(my_w_scores1))
        best_all_PCA = my_w_scores2.index(max(my_w_scores2))
        """
    print('maximum achived [silhouette score,makkimadani cluster Unifity_mean, makki.._var is' ,maxSil,maxSil_pca)
    my_fRep4.write('\n************\nMaximum achived silhouette score for noPCA is: '+str(maxSil[0])+' in plot(s) number(s) '+str(maxSil[1])+'\nmaximum achived max rate mean for clusters is: '+str(maxSil[2])+' in plot(s) number(s)'+str(maxSil[3])+'\nminimum achived max rate variance for clusters is: '+str(maxSil[4])+' in plot(s) number(s)'+str(maxSil[5]))
    my_fRep4.close()   
    my_fRep3.write('\n************\nMaximum achived silhouette score for PCA is: '+str(maxSil_pca[0])+' in plot(s) number(s)'+str(maxSil_pca[1])+'\nmaximum achived max rate mean for clusters is: '+str(maxSil_pca[2])+' in plot(s) number(s)'+str(maxSil_pca[3])+'\nminimum achived max rate variance for clusters is: '+str(maxSil_pca[4])+' in plot(s) number(s)'+str(maxSil_pca[5]))   
    my_fRep3.close()
    return my_w_minSp1,my_w_scores1,my_w_minSp2,my_w_scores2,my_labels,[preSbg_fr,preSbg_frName]
"-----------------------------------------------------------------------------"
def fitF1(x, c):
    "Exponential decrease: eps fails if c>1"
    return (c **(-1 * x))
def fitF2(x,beta):
    return x**(-beta)
def calcEps(eigenVs,dNb):
    "calculate eps & epsK:"
    e_epsK = 0
    for k_i in range(0,10):
        e_epsKu = 0
        e_epsKd = 0
        for s_i in range(k_i,dNb):
            e_epsKu = e_epsKu+(eigenVs[s_i]*eigenVs[s_i])
            e_epsKd =e_epsKd+eigenVs[s_i]
        e_epsK = e_epsKu/(e_epsKd**2)
        if e_epsK>(100/dNb):
            print ('epsK condition',k_i,e_epsK,1/dNb)
            break
"-----------------------------------------------------------------------------"
def plot_ChLength(Adr):
    fName = open('114VerseNum','r')
    vnList = []
    for cnt_ch in range(0,114):
        ff = fName.readline()
        vnList.append(int(ff.replace('\n','')))
    fName.close()
    plt.figure()
    plt.bar(range(1,115),vnList,width = 0.1,color = 'black')  
    "plt.title('length of chapters')"
    plt.xlabel(make_farsi_text(('شماره سوره')))
    plt.ylabel('تعداد آیه')
    plt.savefig(Adr+'/ch_Len.png')
    plt.close()
    return
"-----------------------------------------------------------------------------"
def arbRoot(inRoots,rCase):
    f = open('./lemCoding','r')
    "rCase: False=ord True=reverse"
    rC1 = []
    rC2 = []
    outRoots = []
    for rci in range(0,53):
        [rootCodes0, rootCodes1] = (f.readline()).split('\t')
        rC1.append(rootCodes0)
        rC2.append(rootCodes1[0])
    f.close()
    if rCase:
        for wrd in inRoots:
            wrdt = ''
            for chi in range(len(wrd)-1,-1,-1):
               wrdt += rC1[rC2.index(wrd[chi])]+' '
            outRoots.append(wrdt[0:-1])
    else:
        for wrd in inRoots:
            wrdt = ''
            for chi in range(0,len(wrd)):
               wrdt += rC1[rC2.index(wrd[chi])]
            outRoots.append(wrdt)
    return outRoots
"-----------------------------------------------------------------------------"
def calcDiff_cls(a99,b99):
    a99 = list(map(set,a99))
    b99 = list(map(set,b99))
    outLbs = []
    "case1 cl1==cl1,cl2==cl2"
    alla99 = a99[0].union(a99[1])
    allb99 = b99[1].union(b99[0])
    nonCom = (alla99.union(allb99)).difference(alla99.intersection(allb99))
    outLbl1 = ((a99[0].difference(b99[0])).union(b99[0].difference(a99[0]))).difference(nonCom)
    outLbl2 = ((a99[1].difference(b99[0])).union(b99[0].difference(a99[1]))).difference(nonCom)
    if len(outLbl1) > len(outLbl2):
        outLbs = [outLbl2,nonCom]
    elif len(outLbl1) < len(outLbl2):
        outLbs = [outLbl1,nonCom]
    else:
        outLbs = [outLbl1,outLbl2,nonCom]
    return outLbs
"-----------------------------------------------------------------------------"
def lbl_conv(HClusteingRes,dlChs,same_c,same_k):
    outLbl = []
    sh_sv = c_copy(dlChs)
    sh_sv.extend(list(chain(*np_asarray(same_c))))
    svlCn = 0
    svNm3 = []
    svNm4 = []
    with open('nameSovar_c.txt','r') as svName:
        for svl in svName:
            if svlCn not in sh_sv:
                svNm3.append(svl[:-1])
            svNm4.append(svl[:-1])
            svlCn = svlCn+1
    svNm3 = np_asarray(svNm3)
    svNm4 = np_asarray(svNm4)

    for k_l in set(HClusteingRes):
        nHc = np_where(HClusteingRes==k_l)[0]
        #add same chapters:
        addCandidate = list(svNm3[nHc])
        for cand in addCandidate:
            if cand in svNm4[same_k]:# add same chapters in it's group
                addCandidate.extend(list(svNm4[list(same_c[list(svNm4[same_k]).index(cand)])]))
        outLbl.append(addCandidate)
    return outLbl
"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"

"Mk_Matching([0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,0,0,1,1,1,1,0,1,0,1,0,1,1,1,0,0,0,0,0,1,1,1,1,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,0,0,1,1,1,1,0,1,0,1,0,1,1,1,0,0,0,0,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,0,1]) "    
"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
"        set parameters:       "
"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
t1 = time()
print("Never use a window size less than which .fp has been made based on!!!!!!!!")
"Case = test for test best results and otherwise it's main run"
Tcase = 'test'
allStr = ''
clsPrm = ['','average']
clsDsMetric = 'self'
clsDsMetric_pca = 'cosine'
"SubSubSp:"
DelSubGr_Diff = 0
"standard scaling flag:1-> do before PCA"
StdScaling_F = 1
"fDecAlg = a member of {'LPCA','PCA'} that is acronyms of logistic PCA ,PCA"
fDecAlg = 'PCA'
" mean and variance of makki madani unifity between clusters:"
minMxR_Mean = 0.5
minMxR_Var = 0.5
nDiff = []
nDiff_abs = []
uniqChaps_ = []
uniqChaps_abs = []
uniqChaps_nummbs = []
if fDecAlg == 'LPCA':
    rpy2.robjects.numpy2ri.activate()
    r_logisticPCA = importr("logisticPCA")
    rplot = importr("ggplot2")
    r_mat = robjects.r("matrix")
    r_c  = robjects.r("c")
    if StdScaling_F != 0:
        print('StdScaling_F should be zero because this is binary case & binary vectors shouldnt be prescaled')
        sys.exit()
if clsDsMetric_pca == 'self':
    print('distace metric after pca could not be self by current self defined criteria')
else:
    max_my_spCnt = 114
    "window sizes:"
    my_wCns = [2,3,4,5,6,7,8,9]
    i_minSp0 =  [11,19, 23, 27, 31, 33, 35, 37]
    if Tcase.find('test') != -1:
        "minimum support value for the best of each window size"
        i_minSp1 = [11,24,23,32,51,48,50,42]
        "number of features after PCA for best of each window size"
        f = [2,2,2,2,2,2,2,2]
        "plot number for the best of each window size"
        pltNm = [19,38,19,40,89,77,41,41]
        "number of clusters in best results:"
        cls_Rng = [8,14,9,4,2,5,2,2]
        cls_Rng2 = sorted(list(set(cls_Rng)))
    fop = open(GlPth+'report_opt_MakkiMadani'+allStr+'.txt','w')
    fop.close()
    distCriteria = [clsDsMetric,clsDsMetric_pca]
    mxZeroChap = 112
    writeChGrs = 1
    px0 = []
    CorpN = 3
    wghState = 'w'
    chN = np_asarray(range(0,114))
    chN = list(chN)
    "also decrease dimension?"
    PCAYN = 'Y'
    PCAFN = 20
    PCAJump = 10
    spJump = 5
    correct_mkMd = 0.65
    for ijk in range(0,len(my_wCns)):
        if (wghState != 'w'):
            if fDecAlg.find('LPCA') == -1:
                if StdScaling_F:
                    print("Error !!! standard scaling in binary mod!!!!")
                    break
        if Tcase.find('test') != -1:   
            test_Prms = [Tcase,f[ijk],pltNm[ijk],cls_Rng2,i_minSp1[ijk]]
        else:
            test_Prms = ['']
        my_wCnt = my_wCns[ijk] 
        i_minSp = i_minSp0[ijk]
        resPath3 = GlPth+'w'+str(my_wCnt)+'/'
        clsPrm[0] = resPath3
        createFolder(resPath3[0:-1])
        px1,py1,px2,py2,lbls_cmp,fsg_fr = run_plot97_pre(my_wCnt,distCriteria,clsPrm,i_minSp,resPath3,
                                         mxZeroChap,writeChGrs,chN,clsDsMetric,
                                         clsDsMetric_pca,CorpN,wghState,PCAFN,correct_mkMd,PCAJump,spJump,DelSubGr_Diff,StdScaling_F,fDecAlg,minMxR_Mean,minMxR_Var,test_Prms)
        px0.append([px1,py1,px2,py2,lbls_cmp,fsg_fr])
    fop = open(GlPth+'allDatas'+allStr+'.txt','w')
    if Tcase.find('test') != -1:
        "1: between two clustering with 6 , 3 number of clusters,compare clustering in their cut-off for 2 clusters"
        fopCmp1 = open(GlPth+'bestCompares1'+allStr+'.txt','w')
        "2: between 6 , 3 -> compare clustering in their cut-off for 6 clusters"
        fopCmp2 = open(GlPth+'bestCompares2'+allStr+'.txt','w')
    plt.figure(figsize=(20,10))
    plt.rc('font',family = 'Dejavu Sans',size = 10)
    for my_wCnt in range(0,len(my_wCns)):
        "plt.plot(px0[my_wCnt][2],px0[my_wCnt][3],label='ws='+str(my_wCns[my_wCnt])+'_PCA')" 
        fop.write('\n****\nws='+str(my_wCns[my_wCnt])+'\n'+str(px0[my_wCnt][0])+'\n'+str(px0[my_wCnt][1])+'\n'+str(px0[my_wCnt][2])+'\n'+str(px0[my_wCnt][3])+'\n')
        if Tcase.find('test') != -1:
            plt.plot(px0[my_wCnt][0],px0[my_wCnt][1],label='ws='+str(my_wCns[my_wCnt]),marker = 'o')
            lowLidx = 0
            "fopCmp1.write('***********************\nws = '+str(my_wCns[my_wCnt])+'\n')"
            """for clsn in px0[my_wCnt][4]:  
                fopCmp1.write(str(clsn)+'\n')"""
            fopCmp1.write('..........\n')
            fopCmp2.write('..................................Difference by other #ws\t#cls\tsurahs in each clusters\n')
            for wsCmp in range(my_wCnt+1,len(my_wCns)):
                x1 = (px0[my_wCnt][4])[lowLidx]
                fopCmp1.write('ws= '+str(my_wCns[my_wCnt])+' ,score= '+str(x1[1])+'\n')
                for arr_ in x1[0]:
                    fopCmp1.write(str(arr_)+'\n')
                x1 = (px0[wsCmp][4])[lowLidx]
                fopCmp1.write('ws= '+str(my_wCns[wsCmp])+' ,score= '+str(x1[1])+'\n')
                for arr_ in x1[0]:
                    fopCmp1.write(str(arr_)+'\n')    
                dff_cls = calcDiff_cls((px0[my_wCnt][4])[lowLidx][0],(px0[wsCmp][4])[lowLidx][0])
                fopCmp1.write('diff(different,just in one cluster):\n')
                nDff = 0
                for dff_clsI in range(0,len(dff_cls)-1):
                    for dff_clsName in dff_cls[dff_clsI]:
                        fopCmp1.write(dff_clsName+'('+str((px0[my_wCnt][5][0])[px0[my_wCnt][5][1].index(dff_clsName)])+', '+str((px0[wsCmp][5][0])[px0[wsCmp][5][1].index(dff_clsName)])+'),')
                        if dff_clsName not in uniqChaps_:
                            uniqChaps_.append(dff_clsName)
                        nDff += 1
                        if (px0[my_wCnt][5][0])[px0[my_wCnt][5][1].index(dff_clsName)] not in uniqChaps_nummbs:
                            uniqChaps_nummbs.append((px0[my_wCnt][5][0])[px0[my_wCnt][5][1].index(dff_clsName)])
                        if  (px0[wsCmp][5][0])[px0[wsCmp][5][1].index(dff_clsName)] not in uniqChaps_nummbs:
                            uniqChaps_nummbs.append((px0[wsCmp][5][0])[px0[wsCmp][5][1].index(dff_clsName)])
                    fopCmp1.write('\n')
                for dff_clsName in dff_cls[dff_clsI+1]:
                    if dff_clsName in px0[my_wCnt][5][1]:
                        fopCmp1.write(dff_clsName+'('+str((px0[my_wCnt][5][0])[px0[my_wCnt][5][1].index(dff_clsName)])+'), ')
                    else:
                        fopCmp1.write(dff_clsName+'('+str((px0[wsCmp][5][0])[px0[wsCmp][5][1].index(dff_clsName)])+'), ')                         
                    if dff_clsName not in uniqChaps_abs:
                        uniqChaps_abs.append(dff_clsName)
                fopCmp1.write('\n')
                if len(dff_cls) > 2:
                    fopCmp1.write('*2 kind of clustering had equal worth\n')
                print(max(cls_Rng[wsCmp],cls_Rng[my_wCnt]),cls_Rng[wsCmp],cls_Rng[my_wCnt])
                if 2 in cls_Rng2:
                    present = cls_Rng2.index(max(cls_Rng[wsCmp],cls_Rng[my_wCnt]))
                else:
                    present = cls_Rng2.index(max(cls_Rng[wsCmp],cls_Rng[my_wCnt])) + 1                    
                fopCmp2.write('ws= '+str(my_wCns[my_wCnt])+', #clusters:'+str(cls_Rng[my_wCnt])+'\n')
                for fopc00 in (px0[my_wCnt][4])[present][0]:
                    fopCmp2.write(str(fopc00)+'\n')
                fopCmp2.write('\nws= '+str(my_wCns[wsCmp])+' #clusters:'+str(cls_Rng[wsCmp])+'\n')
                for fopc00 in (px0[wsCmp][4])[present][0]:
                    fopCmp2.write(str(fopc00)+'\n')               
                nDiff.append([my_wCnt+2,wsCmp+2,nDff])
                nDiff_abs.append([my_wCnt+2,wsCmp+2,len(dff_cls[dff_clsI+1])])
    if Tcase.find('test') != -1:
        fopCmp2.close()
        fopCmp1.write('number of Different chaps: ws1\tws2\t#chapters\n')
        for Diff in nDiff:
            fopCmp1.write(str(Diff)+'\n')
        fopCmp1.write('number of Different absent chaps: ws1\tws2\t#chapters\n')
        for Diff in nDiff_abs:
            fopCmp1.write(str(Diff)+'\n')
        fopCmp1.write('Different chaps among all\n')
        for Diff in uniqChaps_:
            fopCmp1.write(str(Diff)+'، ')
        fopCmp1.write(str(len(uniqChaps_))+'\n')
        fopCmp1.write('Different absent chaps among all\n')
        for Diff in uniqChaps_abs:
            fopCmp1.write(str(Diff)+'، ')
        fopCmp1.write(str(len(uniqChaps_abs))+'\n')
        fopCmp1.close()
    plt.grid(axis=u'both')
    plt.legend()
    plt.ylim([-1.05,1.05])
    plt.xlim([0,60])
    plt.xlabel(make_farsi_text(('کمینه پشتیبان')))
    plt.ylabel(make_farsi_text(('مقدار silhouette')))
    plt.savefig(GlPth+'all0_'+allStr+'.png')
    plt.close('all')

    fig = plt.figure(figsize=(20,10))
    for my_wCnt in range(0,len(my_wCns)):
        plt.plot(px0[my_wCnt][0],px0[my_wCnt][1],label = 'WS= '+str(my_wCns[my_wCnt]),marker='o')
        plt.plot(px0[my_wCnt][2],px0[my_wCnt][3],label = 'WS= '+str(my_wCns[my_wCnt])+'_PCA',marker='x',linestyle='--') 
    plt.legend(loc= 'upper left')
    plt.grid(axis=u'both')
    plt.xlim([0,60])
    plt.ylim([-1.05,1.05])
    plt.xlabel(make_farsi_text(('کمینه پشتیبان')))
    plt.ylabel('silhouette score')
    plt.savefig(GlPth+'all1_'+allStr+'.png')
    plt.close('all')
    
    plt_s2 = 0
    fig = plt.figure(figsize=(20,10))
    ax = fig.gca(projection='3d')
    for my_wCnt in range(0,len(my_wCns)):
        ax.plot(px0[my_wCnt][0],len(px0[my_wCnt][0])*[my_wCns[my_wCnt]],px0[my_wCnt][1],label = 'WS= '+str(my_wCns[my_wCnt]),marker = 'o')
        ax.plot(px0[my_wCnt][2],len(px0[my_wCnt][2])*[my_wCns[my_wCnt]],px0[my_wCnt][3],label = 'WS= '+str(my_wCns[my_wCnt])+'_PCA',marker = 'x') 
        if (len(px0[my_wCnt][1]) != 0) & (len(px0[my_wCnt][3]) != 0):                
            if max(max(px0[my_wCnt][1]),max(px0[my_wCnt][3])) > 1:
                print('NOTE! error in silhouette score,it is more than 1!!!!!',px0[my_wCnt][1],px0[my_wCnt][3])
            if min(min(px0[my_wCnt][1]),min(px0[my_wCnt][3])) < -1:
                print ('NOTE! error in silhouette score,it is less than 1!!!!!',px0[my_wCnt][1],px0[my_wCnt][3])
    ax.legend()
    ax.set_xlabel(make_farsi_text(('کمینه پشتیبان')))
    ax.set_zlabel(make_farsi_text(('مقدار silhouette')))
    ax.set_ylabel(make_farsi_text(('اندازه پنجره')))
    ax.set_xlim([0,60])
    ax.set_zlim([-1.05,1.05])
    ax.set_ylim([0,my_wCns[-1]+1])
    plt.grid(axis=u'both')
    plt.savefig(GlPth+'all2_'+allStr+'.png')
    plt.close('all')
    
    fig = plt.figure(figsize=(20,10))
    ax = fig.gca(projection='3d')
    for my_wCnt in range(0,len(my_wCns)):
        ax.plot(px0[my_wCnt][0],len(px0[my_wCnt][0])*[my_wCns[my_wCnt]],px0[my_wCnt][1],label = 'WS= '+str(my_wCns[my_wCnt]),marker='o')
    ax.legend()
    ax.set_xlabel(make_farsi_text(('کمینه پشتیبان')))
    ax.set_zlabel(make_farsi_text(('مقدار silhouette')))
    ax.set_ylabel(make_farsi_text(('اندازه پنجره')))
    ax.set_xlim([0,60])
    ax.set_zlim([-1.05,1.05])
    ax.set_ylim([0,my_wCns[-1]+1])
    plt.grid(axis=u'both')
    plt.savefig(GlPth+'all3_'+allStr+'.png')
    plt.close()

print ((time()-t1)/60)
