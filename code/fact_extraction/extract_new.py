from calendar import c
import code
import copy
import re
import sys
from pathlib import Path
from tkinter import NO

from numpy import add, fix
from requests import get
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))
import os
import json
from slither.slither import Slither
from tqdm import tqdm
from memory_profiler import profile
from slither.core.cfg.node import Node
from extract_facts import get_node_facts
from alias_analysis.variable_extraction import get_variable_dict
from configs import *
from utils.code_fact import functionSignature,functionFacts
import subprocess
import pickle
from itertools import combinations
from util import find_most_similar_function,split_fact_str,compare_equal_logical,equal_temp
import spacy
nlp=spacy.load('en_core_web_md')
def get_solc_version(verison):
    files=os.listdir(source_path)
    for file in files:
        if file.startswith(verison):
            return file
def node_range(node):
    start = node.source_mapping.start
    length = node.source_mapping.length
    return (start, start + length)

def get_context(node, code_file):
    node_source_file=code_file[node.source_mapping.start:node.source_mapping.start+node.source_mapping.length]
    node_source_file=node_source_file.decode('utf-8')
    return node_source_file

def get_code_line(node, code_file):
    code_line=node.source_mapping.lines
    code_file=code_file.decode('utf-8').split('\n')
    codes=[]
    for line in code_line:
        codes.append(code_file[line-1].strip(" "))
    if str(node)=="ENTRY_POINT":
        codes=codes[:1]
    return codes
# 函数用于检查两个范围是否重叠
def ranges_overlap(range1, range2):
    return max(range1[0], range2[0]) < min(range1[1], range2[1])


def find_compared_version(node,cmp_contracts,cmp_file,node_lines):
    for contract in cmp_contracts:
        if contract.name!=node.function.contract.name:
            continue
        for function in contract.functions_and_modifiers:
            if function.canonical_name!=node.function.canonical_name or function.signature_str!=node.function.signature_str:
                continue
            code_lines=get_code_line(function, cmp_file)
            for node_line in node_lines:
                if node_line not in code_lines:
                    return True
    return False
    
def additional_check(node,add_del_code,file):
    code_line=node.source_mapping.lines
    if str(node)=='ENTRY_POINT':
        return True
    code_file=file.decode('utf-8').split('\n')
    before_line=code_file[code_line[0]-2] if code_line[0]-2>=0 else '================================='
    before_line=before_line.strip(" ")
    after_line=code_file[code_line[-1]] if code_line[-1]<len(code_file) else '================================='
    after_line=after_line.strip(" ")
    add_del_code=add_del_code.split('\n')
    add_del_code=[x[1:] if len(x)>0 and (x[0]=='+' or x[0]=='-') else x for x in add_del_code  ]
    add_del_code=[x.strip(" ") for x in add_del_code]
    if before_line in add_del_code and after_line in add_del_code:
        return True
    return False
# @profile
def get_target_nodes(codes,verison_num,is_buggy=False,compared_version=None):
    verison=get_solc_version(verison_num)
    or_source_path=os.path.join(source_path,verison)
    path=or_source_path
    opz_slither = Slither(path)
    contracts = opz_slither.contracts
    ## Compared_version
    cmp_verison=get_solc_version(compared_version)
    cmp_source_path=os.path.join(source_path,cmp_verison)
    cmp_path=cmp_source_path
    opz_cmp = Slither(cmp_path)
    cmp_contracts = opz_cmp.contracts
    target_node={}
    with open(or_source_path, 'rb') as file:
        code_file = file.read()
    with open(cmp_source_path, 'rb') as file:
        cmp_file = file.read()
    map_node={}
    all_codes={}
    for fix_desc in codes:
        if fix_desc not in target_node:
            target_node[fix_desc]={}
        for code,code_name in codes[fix_desc]:
            if code_name not in all_codes:
                all_codes[code_name]=code
            else:
                all_codes[code_name]+='\n'+code
            copyed_code=copy.deepcopy(code)
            if code_name not in target_node[fix_desc]:
                target_node[fix_desc][code_name]=[]
            for contract in contracts:
                if contract.name!=code_name and not (verison_num=='4.9.3' and contract.name=='ERC1967Upgrade' and code_name=='ERC1967Utils'):
                    continue
                for function in contract.functions_and_modifiers:
                    if function.name.startswith('$') or 'ConstructorConstantVariables' in function.name or 'ConstructorVariables' in function.name or contract.name not in function.canonical_name:
                        continue
                    if contract.name not in function.canonical_name:
                        continue
                    if function.name=='_disableInitializers':
                        continue
                    for node in function.nodes:
                        if str(node).startswith('END') or str(node).startswith('INLINE ASM'):
                            continue
                        code_lines=get_code_line(node, code_file)          
                        flag=False
                        for code_line in code_lines:
                            # flag2=False
                            if code_line == '':
                                continue
                            if len(code_line)==1 and not code_line[0].isalnum():
                                continue
                            if len(code_line)==2 and not code_line[0].isalnum() and not code_line[1].isalnum():
                                continue
                            splits=code.split(code_line)
                            label='-' if is_buggy else '+'
                            for split in splits:
                                if split!=code and len(split.strip(" "))>0 and (split.strip(" ")[-1])==label:
                                    copyed_code=copyed_code.replace(label,' ',1)
                                    flag=True
                                    break
                            # if flag2:
                            #     flag=True
                            #     break
                        if flag and additional_check(node,code,code_file):
                            map_node[node]=code_lines
                            target_node[fix_desc][code_name].append(node)
            # ll='-' if is_buggy else '+'
            # if ll in copyed_code:
            #     copyed_code=copyed_code.split('\n')
            #     flag=False
            #     for line in copyed_code:
            #         if line.startswith(ll) and (line.strip(' ')!='' and '*' not in line and '//' not in line):
            #             flag=True
            #             break
            #     if flag:
            #         print('---------------------------------')
            #         print(fix_desc)
            #         print(code_name)
            #         print(code)
        new_target_node={}
        for key in target_node[fix_desc]:
            all_c=copy.deepcopy(all_codes[key])
            targets=target_node[fix_desc]
            targets[key].sort(key=lambda n: node_range(n)[1] - node_range(n)[0], reverse=True)
            max_nodes = []
            # 遍历所有节点并筛选
            same_code_nodes={}
            for node in targets[key]:
                if str(node)=="ENTRY_POINT":
                    max_nodes.append(node)
                    continue
                if str(node)== 'INLINE ASM':
                    continue
                node_start, node_end = node_range(node)
                # 检查当前节点是否与已记录的节点重叠
                node_code='\n'.join(map_node[node])
                if node_code in same_code_nodes:
                    same_code_nodes[node_code].append(node)
                else:
                    same_code_nodes[node_code]=[node]
                overlap = False
                for existing_node in max_nodes:
                    if str(existing_node)=="ENTRY_POINT":
                        continue
                    existing_start, existing_end = node_range(existing_node)
                    if ranges_overlap((node_start, node_end), (existing_start, existing_end)) or (map_node[node]==map_node[existing_node] and all_c.count(map_node[node][0])==1):
                        overlap = True
                        break
                # 如果没有重叠，添加当前节点
                if not overlap:
                    max_nodes.append(node)
            for code_key in same_code_nodes:
                if len(same_code_nodes[code_key])>1:
                    remove_nodes=[]
                    for node in same_code_nodes[code_key]:
                        if str(node)=="ENTRY_POINT":
                            continue
                        if not find_compared_version(node,cmp_contracts,cmp_file,map_node[node]):
                            remove_nodes.append(node)
                    if len(remove_nodes)==len(same_code_nodes[code_key]):
                        continue
                    else:
                        for node in remove_nodes:
                            if node in max_nodes:
                                max_nodes.remove(node)
            max_nodes.sort(key=lambda n: node_range(n)[0])
            new_target_node[key] = max_nodes
        target_node[fix_desc]=new_target_node
    return target_node,code_file

def get_codes(file_path):
    with open(file_path, 'r') as f:
        versions=json.load(f)
    res={}
    for version in versions:
        for fix_desc in versions[version]:
            for url in versions[version][fix_desc]:
                for codes in url:
                    try:
                        for code in url[codes]:
                            if url[codes][code][0]==True:
                                #process code
                                if version not in res:
                                    res[version]={}
                                if fix_desc not in res[version]:
                                    res[version][fix_desc]=[]
                                res[version][fix_desc].append((code,url[codes][code][1]))
                    except Exception as e:
                        print(e)
                        print(codes)
                        print(url)
                        print(fix_desc)
                        exit()
    return res

def category_by_function(target_nodes):
    target_node_by_function = {}
    for code in target_nodes:
        target_node_by_function[code] = {}
        for node in target_nodes[code]:
            function_str = node.function.signature_str
            if function_str not in target_node_by_function[code]:
                target_node_by_function[code][function_str] = [node]
            else:
                target_node_by_function[code][function_str].append(node)
    return target_node_by_function

# @profile
##change 
def find_functions_containing_nodes(target_nodes: list[Node]):
    node_to_function = {node: set() for node in target_nodes}
    contracts=set()
    for node in target_nodes:
        contracts.add(node.function.contract)
    for contract in contracts:
        for function in contract.functions_and_modifiers:
            function_nodes=set(function.all_nodes())
            for node in target_nodes:
                if node in function_nodes:
                    node_to_function[node].add(function)
    return node_to_function

def map_functions_to_nodes(node_to_functions):
    function_to_nodes = {}
    for node, functions in node_to_functions.items():
        for func in functions:
            if func not in function_to_nodes:
                function_to_nodes[func] = set()
            function_to_nodes[func].add(node)
    return function_to_nodes

def find_exact_set_cover(list_nodes, dic):
    """
    找到最小的函数集合，使得它们恰好覆盖所有的节点，且各函数之间的节点不重叠。
    
    :param list_nodes: 需要覆盖的节点列表
    :param dic: 函数到节点的映射字典，格式为 {func: [nodes]}
    :return: 最小函数集合（精确覆盖解）或 None 如果不存在
    """
    total_nodes = set(list_nodes)
    functions = list(dic.keys())
    n = len(functions)
    functions.sort(key=lambda f: len(f.all_nodes()))
    # 从1个函数开始尝试，逐步增加集合大小
    min_set=[]
    min_len=float('inf')
    for r in range(1, n+1):
        for subset in combinations(functions, r):
            covered_nodes = set()
            overlap = False
            for func in subset:
                nodes = set(dic[func])
                covered_nodes |= nodes
            if not overlap and total_nodes.issubset(covered_nodes):
                subset=set(subset)
                len_subset=0
                for func in subset:
                    len_subset+=len(func.all_nodes())
                if len_subset<min_len:
                    min_set=subset
                    min_len=len_subset
    return min_set
def find_entry_function(nodes: list[Node]):
    node_to_functions = find_functions_containing_nodes(nodes)
    function_to_nodes = map_functions_to_nodes(node_to_functions)
    minimal_covers = find_exact_set_cover(nodes,function_to_nodes)
    res={}
    for cover in minimal_covers:
        nodes_covered = function_to_nodes[cover]
        res[cover]=[]
        for node in cover.all_nodes():
            if node in nodes_covered:
                res[cover].append(node)
    return res
# @profile
def judge_not_in(function_signature,vars_dic):
    if function_signature not in vars_dic:
        return True
    return False
# @profile
def get_add_del_code(code_list):
    add_codes=[]
    del_codes=[]
    for key in code_list:
        change_code_pairs=code_list[key]
        add_code=[]
        del_code=[]
        for change_code in change_code_pairs:
            codes=change_code[0]
            codes=codes.split('\n')
            for code in codes:
                if code.startswith('+'):
                    add_code.append(code[1:].strip(" "))
                elif code.startswith('-'):
                    del_code.append(code[1:].strip(" "))
        add_code='\n'.join(add_code)
        del_code='\n'.join(del_code)
        add_codes.append(add_code)
        del_codes.append(del_code)
    return add_codes,del_codes
def judge_pairs(nodes_old,nodes_new,add_codes,del_codes,code_file_new,code_file_old,entry_function_old,entry_function_new):
    if entry_function_new.canonical_name==entry_function_old.canonical_name and entry_function_new.signature_str==entry_function_old.signature_str:
        return True
    old_pos=set()
    for node_old in nodes_old:
        code_old=get_code_line(node_old,code_file_old)
        code_old='\n'.join(code_old)
        code_old=[code_old]
        for del_code in del_codes:
            for cc in code_old:
                if cc in del_code:
                    old_pos.add(del_codes.index(del_code))
    old_pos=list(old_pos)
    old_pos.sort()
    new_pos=set()
    for node_new in nodes_new:
        code_new=get_code_line(node_new,code_file_new)
        code_new='\n'.join(code_new)
        if code_new=='_;' or code_new=='throw;':
            continue
        code_new=[code_new]
        for add_code in add_codes:
            for cc in code_new:
                if cc in add_code:
                    new_pos.add(add_codes.index(add_code))
    new_pos=list(new_pos)
    new_pos.sort()
    if old_pos==new_pos:
        return True
    return False
def main():
    codes=get_codes('./pairs.json')
    res=[]
    for version in tqdm(version_pairs):
        # if version!='3.0.0':
        #     continue
        # print('Processing version:',version)
        new_version=version
        old_version=version_pairs[version]
        if new_version not in codes:
            continue
        code_list=codes[new_version]
        add_code,del_code=get_add_del_code(code_list)
        target_nodes_old,code_file_old=get_target_nodes(code_list,old_version,is_buggy=True,compared_version=new_version)
        target_nodes_new,code_file_new=get_target_nodes(code_list,new_version,is_buggy=False,compared_version=old_version)
        target_nodes={}
        vars_dic_new={}
        vars_dic_old={}
        for desc in target_nodes_old:
            for key in target_nodes_old[desc]:
                if desc not in target_nodes:
                    target_nodes[desc]={}
                if key in target_nodes_new[desc]:
                    target_nodes[desc][key]={'new':target_nodes_new[desc][key],'old':target_nodes_old[desc][key]}
                else:
                    target_nodes[desc][key]={'new':[],'old':target_nodes_old[desc][key]}
        for desc in (target_nodes):
            for key in target_nodes[desc]:
                nodes_old=target_nodes[desc][key]['old']
                if nodes_old!=[]:
                    entry_functions_old=find_entry_function(nodes_old)
                    # if len(entry_functions_old)>1:
                    #     print(desc)
                    #     print(key)
                else:
                    # print(f"{version_pairs[version]}: {desc} : {key}")
                    temp_old=functionFacts()
                    temp_old.function_facts=[]
                    temp_old.function_signature.version=old_version
                    entry_functions_old={}
                nodes_new=target_nodes[desc][key]['new']
                if nodes_new!=[]:
                    entry_functions_new=find_entry_function(nodes_new)
                else:
                    # print(f"{version}: {desc} : {key}")
                    temp_new=functionFacts()
                    temp_new.function_facts=[]
                    temp_new.function_signature.version=new_version
                    entry_functions_new={}
                for entry_function_old in entry_functions_old:
                    if old_version=='4.4.2' and key=='ERC1967Upgrade' and entry_function_old.name!='_upgradeToAndCallSecure':
                        continue
                    function_signature = functionSignature()
                    function_signature.get_signature_in_func(entry_function_old)
                    function_signature.version=old_version
                    if judge_not_in(function_signature,vars_dic_old):
                        vars_dic_old[function_signature]=get_variable_dict(entry_function_old,code_file_old)
                    temp_old=get_node_facts(entry_function_old,entry_functions_old[entry_function_old],vars_dic_old[function_signature],code_file_old)
                    temp_old.function_signature.version=old_version
                    entry_function_new_found=None
                    entry_functions_new_list=list(entry_functions_new.keys())
                    entry_functions_new_list.sort(key=lambda x:sort_function_by_func_name(x,entry_function_old.name),reverse=True)
                    for entry_function_new in entry_functions_new_list:
                        entry_function_new_found=entry_function_new
                        if not judge_pairs(entry_functions_old[entry_function_old],entry_functions_new[entry_function_new],add_code,del_code,code_file_new,code_file_old,entry_function_old,entry_function_new):
                            continue
                        function_signature = functionSignature()
                        function_signature.get_signature_in_func(entry_function_new)
                        function_signature.version=new_version
                        if judge_not_in(function_signature,vars_dic_new):
                            vars_dic_new[function_signature]=get_variable_dict(entry_function_new,code_file_new)
                        temp_new=get_node_facts(entry_function_new,entry_functions_new[entry_function_new],vars_dic_new[function_signature],code_file_new)
                        temp_new.function_signature.version=new_version
                        break
                    if temp_new.function_facts!=[] or temp_old.function_facts!=[]:
                        res.append([temp_new,temp_old])
                        old_reachable_from_funcs=entry_function_old.reachable_from_functions if entry_function_old!=None else []
                        new_reachable_from_funcs=entry_function_new_found.reachable_from_functions if entry_function_new_found!=None else []
                        for old_reachable_from_func in old_reachable_from_funcs:
                            temp_old_copy=copy.deepcopy(temp_old)
                            temp_old_copy.function_signature.get_signature_in_func(old_reachable_from_func)
                            if new_reachable_from_funcs==[]:
                                res.append([temp_new,temp_old_copy])
                            for new_reachable_from_func in new_reachable_from_funcs:
                                temp_new_copy=copy.deepcopy(temp_new) 
                                temp_new_copy.function_signature.get_signature_in_func(new_reachable_from_func)
                                if temp_new_copy.function_signature.function_name==temp_old_copy.function_signature.function_name:
                                    res.append([temp_new_copy,temp_old_copy])
                temp_new=functionFacts()
                temp_new.function_facts=[]
                temp_new.function_signature.version=new_version
                temp_old=functionFacts()
                temp_old.function_facts=[]
                temp_old.function_signature.version=old_version
    pickle.dump(res,open(os.path.join(inter_path,'res5.pkl'),'wb'))
    with open(os.path.join(inter_path,'res5.json'),'w') as f:
        json.dump(res,f,indent=4,default=lambda x:x.to_dict())
def split_by_uppercase(s):
    if s.islower():
        return [s]
    return re.findall(r'[A-Z][a-z]+|[A-Z]+\d+|[A-Z]+(?=[A-Z]|$)', s)
def sort_function_by_func_name(functionA,target_name):
    func_name=functionA.name
    func_name=func_name.replace('_','')
    func_name=func_name[0].upper() + func_name[1:]
    func_name=split_by_uppercase(func_name)
    func_name=[x.lower() for x in func_name]
    func_name=[x.split('_') for x in func_name]
    func_name=[x for y in func_name for x in y]
    func_name=' '.join(func_name)
    function_name=nlp(func_name)
    target_name=target_name.replace('_','')
    target_name=target_name[0].upper() + target_name[1:]
    target_name=split_by_uppercase(target_name)
    target_name=[x.lower() for x in target_name]
    target_name=[x.split('_') for x in target_name]
    target_name=[x for y in target_name for x in y]
    target_name=' '.join(target_name)
    target_name=nlp(target_name)
    return function_name.similarity(target_name)
if __name__=='__main__':
    main()      
pass