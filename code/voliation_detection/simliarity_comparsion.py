


import copy
from utils.code_fact import binaryOperationFacts, singleFact, factsType
from utils.all_type import *
from configs import *
import numpy as np
import re
from collections import deque, defaultdict
can_change_lr_op=[operationType.ADD,operationType.EQ,operationType.NEQ,operationType.BITWISEAND,operationType.AND,operationType.OR,operationType.BITWISEOR,operationType.BITWISEXOR,operationType.MULTIPLY]
def compare_checks_with_facts(checks:list[singleFact],facts:list[singleFact]):
    checks=checks.function_facts
    res=[]
    for fact in facts:
        if len(fact[1].function_facts)==0:
            continue
        flag=compare_checks_with_facts_call_function(checks,fact[1].function_facts)
        if flag and not compare_checks_with_facts_call_function(checks,fact[0].function_facts):
            res.append(fact)
    return res
def compare_checks_with_facts_call_function(checks:list[singleFact],facts:list[singleFact]):
    if len(facts)==0:
        return False
    it=iter(checks)
    cou=0
    for vul_fact in facts:
        copy_it=copy.deepcopy(it)
        flag=False
        if isinstance(vul_fact,list):
            #first check the call function
            for check in it:
                if match_func(check,vul_fact[0]):
                    flag=True
                    break
            if flag==False:
                #second check the content
                content_check_res=compare_checks_with_facts_call_function(checks,vul_fact[1])
                if content_check_res:
                    continue
                else:
                    return False
            else:
                continue
        else:
            for check in it:
                if match_func(check,vul_fact):
                    flag=True
                    cou+=1
                    break
        if flag==False and not (vul_fact.fact_type==factsType.NEW_VARIABLE and len(facts)!=1) and not (vul_fact.fact_type==factsType.RETURN and len(facts)!=1):
            return False
        if flag==False:
            it=copy_it
    if cou!=0:
        return True
    else:
        return False

def judge_fix(checks,facts):

    for fact in facts:
        flag=False
        for check in checks:
            if match_func(check,fact):
                flag=True
                break
        if flag==False:
            return False
    return True

 
def has_in(list1,var):
    for i in list1:
        if match_func(i,var):
            return True
    return False

def match_func(check, fact):
    if check.fact_type!=fact.fact_type:
        if check.fact_type==factsType.REQUIRE and fact.fact_type==factsType.REVERT:
            fact.fact=convert_revert_to_require(fact.fact)
        elif check.fact_type==factsType.REVERT and fact.fact_type==factsType.REQUIRE:
            check.fact=convert_revert_to_require(check.fact)
        else:
            return False
    binary_fact_A=check.fact
    binary_fact_B=fact.fact
    if isinstance(binary_fact_A, binaryOperationFacts) and isinstance(binary_fact_B, binaryOperationFacts):
        return compare_binary_operation_facts(binary_fact_A,binary_fact_B)
    return False

def judge_sub_facts(check:binaryOperationFacts,fact:binaryOperationFacts):
    simliarity_factor=0
    if check==None and fact==None:
        return True
    if isinstance(check, str):
        if isinstance(fact, str):
            if string_similarity(check,fact)>threshold:
                return True
            else:
                return False
        else:
            if isinstance(fact,list):
                for fact_sub in fact:
                    if compare_binary_operation_facts(check,fact_sub.left_operand):
                        return True
                return False
            return compare_binary_operation_facts(check,fact.left_operand)
    if isinstance(fact, str):
        if isinstance(check, str):
            if string_similarity(check,fact)>threshold:
                return True
            else:
                return False
        else:
            if isinstance(check,list):
                for check_sub in check:
                    if compare_binary_operation_facts(check_sub.left_operand,fact):
                        return True
                return False
            return compare_binary_operation_facts(check.left_operand,fact)    
    if isinstance(check.left_operand, list) and isinstance(fact.left_operand, list):
        for check_left_operand in check.left_operand:
            for fact_left_operand in fact.left_operand:
                if compare_binary_operation_facts(check_left_operand,fact_left_operand):
                    simliarity_factor+=1
                    break
            if simliarity_factor>0:
                break
    elif isinstance(check.left_operand, list) and not isinstance(fact.left_operand, list):
        for check_left_operand in check.left_operand:
            if compare_binary_operation_facts(check_left_operand,fact.left_operand):
                simliarity_factor+=1
                break
    elif not isinstance(check.left_operand, list) and isinstance(fact.left_operand, list):
        for fact_left_operand in fact.left_operand:
            if compare_binary_operation_facts(check.left_operand,fact_left_operand):
                simliarity_factor+=1
                break
    else:
        if compare_binary_operation_facts(check.left_operand,fact.left_operand):
            simliarity_factor+=1
    flag=False
    if isinstance(check.right_operand, list) and isinstance(fact.right_operand, list):
        for check_right_operand in check.right_operand:
            for fact_right_operand in fact.right_operand:
                if compare_binary_operation_facts(check_right_operand,fact_right_operand):
                    simliarity_factor+=1
                    flag=True
                    break
            if flag:
                break
    elif isinstance(check.right_operand, list) and not isinstance(fact.right_operand, list):
        for check_right_operand in check.right_operand:
            if compare_binary_operation_facts(check_right_operand,fact.right_operand):
                simliarity_factor+=1
                break
    elif not isinstance(check.right_operand, list) and isinstance(fact.right_operand, list):
        for fact_right_operand in fact.right_operand:
            if compare_binary_operation_facts(check.right_operand,fact_right_operand):
                simliarity_factor+=1
                break
    else:
        if compare_binary_operation_facts(check.right_operand,fact.right_operand):
            simliarity_factor+=1
    if simliarity_factor>1:#
        return True
    return False
def judge_sub_facts_equal(check:binaryOperationFacts,fact:binaryOperationFacts):
    simliarity_factor=0
    if isinstance(check.left_operand, list) and isinstance(fact.right_operand, list):
        for check_left_operand in check.left_operand:
            for fact_right_operand in fact.right_operand:
                if compare_binary_operation_facts(check_left_operand,fact_right_operand):
                    simliarity_factor+=1
                    break
            if simliarity_factor>0:
                break
    elif isinstance(check.left_operand, list) and not isinstance(fact.right_operand, list):
        for check_left_operand in check.left_operand:
            if compare_binary_operation_facts(check_left_operand,fact.right_operand):
                simliarity_factor+=1
                break
    elif not isinstance(check.left_operand, list) and isinstance(fact.right_operand, list):
        for fact_right_operand in fact.right_operand:
            if compare_binary_operation_facts(check.left_operand,fact_right_operand):
                simliarity_factor+=1
                break
    else:
        if compare_binary_operation_facts(check.left_operand,fact.right_operand):
            simliarity_factor+=1
    flag=False
    if isinstance(check.right_operand, list) and isinstance(fact.left_operand, list):
        for check_right_operand in check.right_operand:
            for fact_left_operand in fact.left_operand:
                if compare_binary_operation_facts(check_right_operand,fact_left_operand):
                    simliarity_factor+=1
                    flag=True
                    break
            if flag:
                break
    elif isinstance(check.right_operand, list) and not isinstance(fact.left_operand, list):
        for check_right_operand in check.right_operand:
            if compare_binary_operation_facts(check_right_operand,fact.left_operand):
                simliarity_factor+=1
                break
    elif not isinstance(check.right_operand, list) and isinstance(fact.left_operand, list):
        for fact_left_operand in fact.left_operand:
            if compare_binary_operation_facts(check.right_operand,fact_left_operand):
                simliarity_factor+=1
                break
    else:
        if compare_binary_operation_facts(check.right_operand,fact.left_operand):
            simliarity_factor+=1
    if simliarity_factor>1:
        return True
    return False
def compare_binary_operation_facts(check:binaryOperationFacts,fact:binaryOperationFacts):
    simliarity_factor=0
    if check==None and fact==None:
        return True
    if check==None and fact!=None:
        return False
    if check!=None and fact==None:
        return False
    if isinstance(check, str):
        if isinstance(fact, str):
            if string_similarity(check,fact)>threshold:
                return True
            else:
                return False
        else:
            if isinstance(fact,list):
                for fact_sub in fact:
                    if compare_binary_operation_facts(check,fact_sub.left_operand):
                        return True
                return False
            return compare_binary_operation_facts(check,fact.left_operand)
    if isinstance(fact, str):
        if isinstance(check, str):
            if string_similarity(check,fact)>threshold:
                return True
            else:
                return False
        else:
            if isinstance(check,list):
                for check_sub in check:
                    if compare_binary_operation_facts(check_sub.left_operand,fact):
                        return True
                return False
            return compare_binary_operation_facts(check.left_operand,fact)
    if isinstance(check,list) and isinstance(fact,list):
        for cc in check:
            for ff in fact:
                if compare_binary_operation_facts(cc,ff):
                    return True
        return False
    elif isinstance(check,list):
        for cc in check:
            if compare_binary_operation_facts(cc,fact):
                return True
        return False
    elif isinstance(fact,list):
        for ff in fact:
            if compare_binary_operation_facts(check,ff):
                return True
        return False  
    match check.operator:
        case  operationType.FUNCTIONCALL:
            if fact.operator!=check.operator:
                return compare_binary_operation_facts(check.left_operand,fact) or compare_binary_operation_facts(check,fact.left_operand)
            else:
                return compare_binary_operation_facts(check.left_operand,fact.left_operand)
        case operationType.TYPECONVERSION:
            if check.operator!=fact.operator:
                return False
            else:
                simliarity_factor+=1
            simliarity_factor+=judge_sub_facts(check,fact)
            if simliarity_factor>=2:
                return True
            else:
                return False
        case operationType.VARIABLE | operationType.LITERAL:
            if check.operator!=fact.operator:
                return compare_binary_operation_facts(check,fact.left_operand) or compare_binary_operation_facts(check.left_operand,fact)
            else:
                if isinstance(check.left_operand, list) and isinstance(fact.left_operand, list):
                    for check_left_operand in check.left_operand:
                        for fact_left_operand in fact.left_operand:
                            if judge_sub_facts(check_left_operand,fact_left_operand):
                                return True
                elif isinstance(check.left_operand, list) and not isinstance(fact.left_operand, list):
                    for check_left_operand in check.left_operand:
                        if judge_sub_facts(check_left_operand,fact.left_operand):
                            return True
                elif not isinstance(check.left_operand, list) and isinstance(fact.left_operand, list):
                    for fact_left_operand in fact.left_operand:
                        if judge_sub_facts(check.left_operand,fact_left_operand):
                            return True
                else:
                    if judge_sub_facts(check.left_operand,fact.left_operand):
                        return True
                return False
        case _:
            if check.operator==fact.operator:
                simliarity_factor+=1
                simliarity_factor+=judge_sub_facts(check,fact)
                if simliarity_factor>=2:
                    return True
                else:
                    simliarity_factor=1
                    simliarity_factor+=judge_sub_facts_equal(check,fact)
                    if check.operator not in can_change_lr_op:
                        simliarity_factor-=1
                    if simliarity_factor>=2:
                        return True
                    else:
                        return False
            else:
                if check.operator in can_change_lr_op:
                    return False
                else:
                    match check.operator:
                        case operationType.GT:
                            simliarity_factor+=(1 if fact.operator==operationType.LT or fact.operator==operationType.LTE else 0)       
                        case operationType.LT:
                            simliarity_factor+=(1 if fact.operator==operationType.GT or fact.operator==operationType.GTE else 0)
                        case operationType.GTE:
                            simliarity_factor+=(1 if fact.operator==operationType.LT or fact.operator==operationType.LTE else 0)
                        case operationType.LTE:
                            simliarity_factor+=(1 if fact.operator==operationType.GT or fact.operator==operationType.GTE else 0)
                        case _:
                            return False
                    simliarity_factor+=judge_sub_facts_equal(check,fact)
                    if simliarity_factor>=2:
                        return True
                    else:
                        return False

    
def convert_revert_to_require(fact:binaryOperationFacts):
    new_fact=binaryOperationFacts()
    match fact.operator:
        case operationType.NOT:
            new_fact=fact.left_operand
        case operationType.AND:
            new_fact.operator=operationType.OR
            new_fact.left_operand=convert_revert_to_require(fact.left_operand)
            new_fact.right_operand=convert_revert_to_require(fact.right_operand)
        case operationType.OR:
            new_fact.operator=operationType.AND
            new_fact.left_operand=convert_revert_to_require(fact.left_operand)
            new_fact.right_operand=convert_revert_to_require(fact.right_operand)
        case operationType.EQ:
            new_fact.operator=operationType.NEQ
            new_fact.left_operand=fact.left_operand
            new_fact.right_operand=fact.right_operand
        case operationType.NEQ:
            new_fact.operator=operationType.EQ
            new_fact.left_operand=fact.left_operand
            new_fact.right_operand=fact.right_operand
        case operationType.GT:
            new_fact.operator=operationType.LTE
            new_fact.left_operand=fact.left_operand
            new_fact.right_operand=fact.right_operand
        case operationType.LT:
            new_fact.operator=operationType.GTE
            new_fact.left_operand=fact.left_operand
            new_fact.right_operand=fact.right_operand
        case operationType.GTE:
            new_fact.operator=operationType.LT
            new_fact.left_operand=fact.left_operand
            new_fact.right_operand=fact.right_operand
        case operationType.LTE:
            new_fact.operator=operationType.GT
            new_fact.left_operand=fact.left_operand
            new_fact.right_operand=fact.right_operand
        case _:
            new_fact.operator=operationType.NOT
            new_fact.left_operand=fact
    return new_fact

def edit_distance(s1, s2):
    s1=s1.lower()
    s2=s2.lower()
    m, n = len(s1), len(s2)
    
    # Create a table to store results of subproblems
    dp = np.zeros((m+1, n+1), dtype=int)
    
    # Fill the table in bottom up manner
    for i in range(m+1):
        for j in range(n+1):
            
            # If first string is empty, insert all characters of second string
            if i == 0:
                dp[i][j] = j
                
            # If second string is empty, remove all characters of first string
            elif j == 0:
                dp[i][j] = i
                
            # If last characters are the same, ignore them and get the value for the remaining string
            elif s1[i-1] == s2[j-1]:
                dp[i][j] = dp[i-1][j-1]
                
            # If last characters are not the same, consider all possibilities and get the minimum
            else:
                dp[i][j] = 1 + min(dp[i][j-1],       # Insert
                                   dp[i-1][j],       # Remove
                                   dp[i-1][j-1])     # Replace
                
    return dp[m][n]

def normalized_edit_distance(s1, s2):
    raw_distance = edit_distance(s1, s2)
    max_length = max(len(s1), len(s2))
    if max_length == 0:
        print(f"Warning: Both strings are empty: {s1}, {s2}")
        return 0
    return raw_distance / max_length

def judge_hex(s1:str,s2:str):
    if s1.startswith('0x'):
        try:
            s1=int(s1, 16)
        except:
            return False
    if s2.startswith('0x'):
        try:
            s2=int(s2, 16)
        except:
            return False
    if s1==s2:
        return True
    return False

def string_similarity(s1, s2):
    if len(s1)==1 or len(s2)==1 or s1.isnumeric() or s2.isnumeric():
        if s1==s2 or judge_hex(s1,s2):
            return 1
        else:
            return 0
    # Check if one string is a substring of the other
    # if (s1 in s2 or s2 in s1) and len(s1)>1 and len(s2)>1:
    #     return 1.0
    s1=s1.split('_')
    s1=[x for x in s1 if x!='']
    S1=''
    for s in s1:
        tmps=s[0].upper()+s[1:]
        S1+=tmps
    S1=split_by_uppercase(S1)
    S1=[x.lower() for x in S1]
    s2=s2.split('_')
    s2=[x for x in s2 if x!='']
    S2=''
    for s in s2:
        tmps=s[0].upper()+s[1:]
        S2+=tmps
    S2=split_by_uppercase(S2)
    min_length=min(len(S1),len(S2))
    lcs,dp=lcs_length(S1,S2)
    if min_length==lcs:
        return 1
    else:
        return 0



def lcs_length(A, B):
    m, n = len(A), len(B)
    # 初始化 DP 表
    dp = [[0]*(n+1) for _ in range(m+1)]
    
    # 填充 DP 表
    for i in range(1, m+1):
        for j in range(1, n+1):
            if 1- normalized_edit_distance(A[i-1], B[j-1]) > threshold:
                dp[i][j] = dp[i-1][j-1] + 1
            else:
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
    
    return dp[m][n], dp
def split_by_uppercase(s):
    if s.islower():
        return [s]
    return re.findall(r'[A-Z][a-z]+|[A-Z]+\d+|[A-Z]+(?=[A-Z]|$)', s)