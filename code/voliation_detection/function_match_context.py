from utils.code_fact import functionSignature,functionFacts
from slither.core.declarations.function_contract import FunctionContract
from slither.core.declarations.contract import Contract
from simliarity_comparsion import string_similarity
import ssdeep
def find_target_statement(function:FunctionContract) -> list:
    if not isinstance(function, FunctionContract):
        return []
    target_statement=[]
    for node in function.all_nodes():
        if node.contains_require_or_assert():
            target_statement.append(node)
        if hasattr(node,'type') and hasattr(node.type,'name') and node.type.name == 'EXPRESSION' and 'revert' in str(node):
            target_statement.append((node.fathers,node))
    return target_statement

def function_iterate(contracts:list[Contract]):
    functions=[]
    for contract in contracts:
        if contract.name.startswith('$'):
            continue
        if contract.contract_kind!='contract':
            continue
        for function in contract.functions_and_modifiers:
            if function.name.startswith('$') or function.name=='slitherConstructorConstantVariables' or contract.name not in function.canonical_name:
                continue
            if contract.name not in function.canonical_name:
                continue
            functions.append(function)
    nodes_list=[]
    for function in functions:
        nodes_list.extend(find_target_statement(function))
    nodes_with_context={}
    for node in nodes_list:
        nodes_with_context[get_context(node)]=node
    return nodes_with_context
def get_context(nodes)->str:
    context=''
    stsm_list=get_stsm_list(nodes)
    if len(stsm_list)==0:
        return context
    function=stsm_list[0].function
    context+=str(function.signature_str)
    for node in function.all_nodes():
        if node in stsm_list:
            continue
        else:
            context+=str(node)
    context=context.replace('\n','')
    context=context.replace(' ','')
    return context
def get_stsm_list(node_list):
    stsm_list=[]
    if type(node_list)!=list and type(node_list)!=tuple:
        return [node_list]
    for node in node_list:
        if type(node)==list:
            stsm_list+=get_stsm_list(node)
        else:
            stsm_list.append(node)
    return stsm_list


def change_facts_structure(facts:list[tuple[functionFacts,functionFacts]]):
    dict_res={}
    
    for fact in facts:
        ## facts[0] is bug facts, facts[1] is fix facts
        for single_fact in fact[0].function_facts:
            bug_context=single_fact.context
            corrsponding_fix_fact=None
            max_similarity=0
            for single_fact_fix in fact[1].function_facts:
                corrsponding_fix_fact=single_fact_fix
                fix_context=single_fact_fix.context
                sim=string_similarity(bug_context,fix_context)
                if sim>max_similarity:
                    corrsponding_fix_fact=single_fact_fix
                    max_similarity=sim

            if corrsponding_fix_fact is not None:
                fact[1].function_facts.remove(corrsponding_fix_fact)
                dict_res[bug_context]=[single_fact,corrsponding_fix_fact]
        if len(fact[1].function_facts)>0:
            for single_fact in fact[1].function_facts:
                dict_res[single_fact.context]=[None,single_fact]
    return dict_res

def find_most_similar_function_by_context(context:str, facts:dict):
    max_similarity=0
    max_context=None
    context_hash=ssdeep.hash(context)
    for key in facts:
        key_hash=ssdeep.hash(key)
        sim=string_similarity(context_hash,key_hash)
        if sim>0.8 and sim>max_similarity:
            max_similarity=sim
            max_context=key
    return max_context