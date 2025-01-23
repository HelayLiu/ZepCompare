
import sys
from pathlib import Path
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))
import os
import json
from slither.slither import Slither
from tqdm import tqdm
from slither.core.declarations.function_contract import FunctionContract
from slither.core.declarations.modifier import Modifier
from slither.slithir.operations import InternalCall,LowLevelCall,HighLevelCall
from function_match_context import function_iterate,find_most_similar_function_by_context,change_facts_structure
from function_match_signature import get_facts,get_filtered_facts
from function_match_context import change_facts_structure as change_facts_structure_context
from function_match_signature import change_facts_structure as change_facts_structure_signature
from extract_check import process_node,get_node_facts
from simliarity_comparsion import compare_checks_with_facts
from alias_analysis.variable_extraction import get_variable_dict
from utils.code_fact import functionSignature,functionFacts,singleFact
import pickle
from configs import *
import subprocess
import time
import glob
import argparse
from packaging.version import Version
def process_contracts_context(contract,facts_dic,alias_dic):
    res={}
    nodes=function_iterate(contract)
    for node_context in tqdm(nodes.keys()):
        node=nodes[node_context]
        sta=time.time()
        fs=find_most_similar_function_by_context(node_context,facts_dic.keys())
        print(time.time()-sta)
        if fs is None:
            continue
        func_sign=functionSignature()
        func_sign.get_signature_in_func(node.function)
        checks=process_node([node],alias_dic[func_sign])
        temp=compare_checks_with_facts(checks,facts_dic[fs].function_facts)
        res[node]=temp
    return res

def process_alias_context(contracts):
    alias_dic={}
    for contract in contracts:
        for function in contract.functions_and_modifiers:
            if function.name.startswith('$') or 'ConstructorConstantVariables' in function.name:
                continue
            func_sign=functionSignature()
            func_sign.get_signature_in_func(function)
            if func_sign not in alias_dic:
                alias_dic[func_sign]=get_variable_dict(function)
    return alias_dic
def get_function_nodes(function:FunctionContract,level=0):
    nodes=[]
    if level>5:
        return nodes
    for node in function.nodes:
        # for ir in node.irs:
        #     if 
        nodes.append(node)
        for ir in node.irs:
            if isinstance(ir,(InternalCall,LowLevelCall,HighLevelCall)):
                if hasattr(ir,'function') and isinstance(ir.function,FunctionContract):
                    nodes.extend(get_function_nodes(ir.function,level+1))
                if hasattr(ir,'function') and isinstance(ir.function,Modifier):
                    nodes=get_function_nodes(ir.function,level+1)+nodes
        
    
    return nodes
def process_contracts_signature(contracts,all_facts,code_file=None):
    res={}
    file_path=None
    for contract in contracts:
        if contract.name.startswith('$'):
            continue
        if contract.contract_kind=='interface':
            continue
        if code_file is None or file_path!=contract.source_mapping.filename.absolute:
            file_path=contract.source_mapping.filename.absolute
            with open(file_path, 'rb') as file:
                code_file = file.read()
        for function in contract.functions_and_modifiers:
            if function.name.startswith('$') or 'ConstructorConstantVariables' in function.name or 'ConstructorVariables' in function.name or contract.name not in function.canonical_name:
                continue
            if contract.name not in function.canonical_name:
                continue
            facts=get_facts(function,all_facts)
            if facts==[]:
                continue
            var_dic=get_variable_dict(function,code_file)
            nodes=get_function_nodes(function,0)
            # for fact in facts:
            checks=get_node_facts(function,nodes,var_dic,code_file)
            temp=compare_checks_with_facts(checks,facts)
            if temp!=[]:
                res[function]=temp
    return res
def output(res:dict):
    out={}
    if isinstance(res,list):
        for sub_res in res:
            out.update(output(sub_res))
    else:
        for key in res.keys():
            can_name=key.canonical_name
            line=f'({key.source_mapping.lines[0]}-{key.source_mapping.lines[-1]})'
            key_str=f'{can_name} {line}'
            fact_strs=[]
            for fact in res[key]:
                fact_strs.append(f'BUG FACTS : {str(fact[1]) if not isinstance(fact[1],list) else str(fact[1][0])}\nFIX FACTS : {str(fact[0]) if not isinstance(fact[0],list) else str(fact[0][0])}')
            out[key_str]=fact_strs
    return out

def get_all_facts(facts_dic):
    all_facts=[]
    for key in facts_dic.keys():
        all_facts.extend(facts_dic[key])
    return all_facts
def get_func_name(facts:list[tuple[functionFacts,functionFacts]]):
    func_name=set()
    for fact in facts:
        name=fact[1].function_signature.function_name
        contract=fact[1].function_signature.contract_name
        version=fact[1].function_signature.version
        func_name.add(f'{version} - {contract} - {name}')
        # func_name.add(fact[1].function_signature.function_name)
    func_name=list(func_name)
    func_name.sort(reverse=True)
        # func_name.add(fact[0].function_signature.function_name)
    return func_name
def get_max_version(versions):

    sorted_versions = sorted(versions, key=lambda v: Version(v), reverse=True)
    return sorted_versions[0] if len(sorted_versions) > 0 else '0.8.0'
if __name__=='__main__':
    
    with open(os.path.join(inter_path,'res4.pkl'),'rb') as f:
        facts_dic=pickle.load(f)

        ## signature based
        facts_signature=change_facts_structure_signature(facts_dic)
    
    # func_names='\n'.join(get_func_name(facts_dic))
    # with open('func_name.txt','w') as f:
    #     f.write(func_names)
    parser = argparse.ArgumentParser(description="Process a given path.")
    parser.add_argument('-p','--path', type=str, help='The path to be processed')
    args = parser.parse_args()
    scan_path=args.path
    if scan_path==None:
        print('Please input the path')
        scan_path='./ZepCompareCode/voliation_detection/test_cases/0.8.2/test4.sol'
    versions=set()
    test=False
    if scan_path.endswith('.sol') or test:
        try:
            solc_version=scan_path.split('/')[-2]
            if not solc_version.startswith('0.'):
                raise Exception
        except:
            solc_version='0.8.12'
        subprocess.run(['solc-select','use',solc_version])
        slither_instance=slither(scan_path)
        all_contracts=slither_instance.contracts
        for comp_unit in slither_instance.compilation_units:
            versions.add(comp_unit.solc_version)
    else:
        all_contracts=[]
        globbed_filenames = glob.glob(scan_path, recursive=True)
        filenames = glob.glob(os.path.join(scan_path, "*.json"))
        if not filenames:
            filenames = globbed_filenames
        for filename in filenames:
            slither_instance=slither(filename, ast_format='--ast-compact-json')
            all_contracts.extend(slither_instance.contracts)
            for comp_unit in slither_instance.compilation_units:
                versions.add(comp_unit.solc_version)
    version=get_max_version(versions)
    facts_signature=get_filtered_facts(facts_signature,version)
    res=process_contracts_signature(all_contracts,facts_signature)
    out=output(res)
    chain=scan_path.split('/')[-4]
    address=scan_path.split('/')[-3]
    if chain=='home':
        chain='SmartBugs'
        address=scan_path.split('/')[-1].split('.')[0]
    save_path=os.path.join(result_path,chain,address)
    os.makedirs(save_path,exist_ok=True)
    with open(os.path.join(save_path,'res_str.json'),'w') as f:
        json.dump(out,f)
