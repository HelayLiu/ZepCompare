from utils.code_fact import functionSignature
from utils.all_type import operationType
import pickle
def list_equal(list1,list2):
    if len(list1)!=len(list2):
        return False
    for item in list1:
        if item not in list2:
            return False
    for item in list2:
        if item not in list1:
            return False
    return True

def find_most_similar_function(target_func_sign:functionSignature, func_sign_list:list[functionSignature]):
    prim_res_func_sign=[]
    for func_sign in func_sign_list:
        if func_sign.contract_name==target_func_sign.contract_name and func_sign.function_name==target_func_sign.function_name:
            prim_res_func_sign.append(func_sign)
    if len(prim_res_func_sign)==0:
        return None
    elif len(prim_res_func_sign)==1:
        return prim_res_func_sign[0]
    else:
        max_similar=0
        max_similar_func_sign=prim_res_func_sign[0]
        for func_sign in prim_res_func_sign:
            similar=0
            if len(target_func_sign.emit_event)==len(func_sign.emit_event):
                similar+=1
            for item in target_func_sign.emit_event:
                if item in func_sign.emit_event:
                    similar+=1
            if len(target_func_sign.params_type)==len(func_sign.params_type):
                similar+=1
            for item in target_func_sign.params_type:
                if item in func_sign.params_type:
                    similar+=1
            if len(target_func_sign.return_type)==len(func_sign.return_type):
                similar+=1
            for item in target_func_sign.return_type:
                if item in func_sign.return_type:
                    similar+=1
            if len(target_func_sign.constant_state_read)==len(func_sign.constant_state_read):
                similar+=1
            for item in target_func_sign.constant_state_read:
                if item in func_sign.constant_state_read:
                    similar+=1
            if len(target_func_sign.constant_state_write)==len(func_sign.constant_state_write):
                similar+=1
            for item in target_func_sign.constant_state_write:
                if item in func_sign.constant_state_write:
                    similar+=1
            if similar>max_similar:
                max_similar=similar
                max_similar_func_sign=func_sign
        return max_similar_func_sign
    
def read_pickle_slither_res(path):
    opz_slither = pickle.load(open(path,'rb'))
    return opz_slither

def split_fact_str(fact_str:str):
    logical_op=[]
    variables=[]
    for typs in operationType:
        if typs.value in fact_str:
            logical_op.append(typs.value)
            fact_str=fact_str.replace(typs.value,' ')
    variables=fact_str.split(' ')
    if logical_op==[]:
        return None,None
    else:
        return logical_op,variables
def compare_equal_logical(logical_op_af:list,logical_op_bf:list,split_fact_str_af:list,split_fact_str_bf:list):
    if len(logical_op_af)!=len(logical_op_bf):
        return False
    if len(split_fact_str_af)!=len(split_fact_str_bf):
        return False
    for fact_str in split_fact_str_af:
        if fact_str not in split_fact_str_bf:
            return False
    for fact_str in split_fact_str_bf:
        if fact_str not in split_fact_str_af:
            return False
    for op in logical_op_af:
        if (find_equal_op(op) not in logical_op_bf) and (op not in logical_op_bf):
            return False
    for op in logical_op_bf:
        if (find_equal_op(op) not in logical_op_af) and (op not in logical_op_af):
            return False
    return True

def find_equal_op(op:str):
    match op:
        case '==':
            return '!='
        case '!=':
            return '=='
        case '>':
            return '<='
        case '>=':
            return '<'
        case '<':
            return '>='
        case '<=':
            return '>'
        case '&&':
            return '||'
        case '||':
            return '&&'
        
def equal_temp(str1:str,str2:str):
    if 'delegate_asm_0' in str1 and 'delegate_asm_0' in str2 and 'switch_expr_' in str1 and 'switch_expr_' in str2 and '== 0' in str1 and '== 0' in str2:
        return True
    return False