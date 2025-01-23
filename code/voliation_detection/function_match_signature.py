from utils.code_fact import functionSignature,functionFacts
from slither.core.declarations.function_contract import FunctionContract
import spacy
import re
import warnings
import copy
import nltk
from nltk.corpus import words
nltk.download('words')
word_list = set([w.lower() for w in words.words()])
warnings.filterwarnings("ignore", message=r"\[W007\]", category=UserWarning)
warnings.filterwarnings("ignore", message=r"\[W008\]", category=UserWarning)
nlp=spacy.load('en_core_web_md')
def split_by_uppercase(s):
    if s.islower():
        return [s]
    return re.findall(r'[A-Z][a-z]+|[A-Z]+\d+|[A-Z]+(?=[A-Z]|$)', s)
def further_function_match(primary_target:FunctionContract,target_signature:functionSignature):
    primary_target_signature=functionSignature()
    primary_target_signature.get_signature_in_func(primary_target)
    # if primary_target_signature.is_subset(target_signature) or target_signature.is_subset(primary_target_signature):
    if target_signature.is_subset(primary_target_signature):
        return True
    else:
        return False

def function_match(need_match:FunctionContract,match_list:list[functionSignature]):
    target_signatures=[]
    for target_signature in match_list:
        if further_function_match(need_match,target_signature[1].function_signature):
            target_signatures.append(target_signature)
    return target_signatures
def change_facts_structure(facts:list[tuple[functionFacts,functionFacts]]):
    dict_res={}
    for fact in facts:
        func_name=fact[1].function_signature.function_name
        if func_name=='':
            continue
        func_name=func_name.replace('_','')
        func_name=func_name[0].upper() + func_name[1:]
        # function_name=function_name.replace('_','')
        func_name=split_by_uppercase(func_name)
        func_name=[x.lower() for x in func_name]
        func_name=[x.split('_') for x in func_name]
        func_name=[x for y in func_name for x in y]
        func_name=' '.join(func_name)
        if func_name=='multicall':
            func_name='multi call'
        function_name=nlp(func_name)
        if function_name not in dict_res.keys():
            dict_res[function_name]=[]
        dict_res[function_name].append(fact)
        
    return dict_res
def get_filtered_facts(facts_dic:dict,version:str):
    larger_version=jugde_large(version)
    if larger_version:
        for facts_func in facts_dic.keys():
            if facts_func.text!='transfer from' and facts_func.text!='transfer':
                continue
            temp=copy.deepcopy(facts_dic[facts_func])
            for fact in facts_dic[facts_func]:
                if fact[1].function_signature.contract_name=='StandardToken' or fact[1].function_signature.contract_name=='BasicToken':
                    temp=[]
            facts_dic[facts_func]=temp
    facts_dic = {key: value for key, value in facts_dic.items() if value != []}
    return facts_dic

def word_segmentation(s, word_list):
    # 动态规划表，用于存储每个位置的最优分割方案
    dp = [None] * (len(s) + 1)
    dp[0] = []

    for i in range(1, len(s) + 1):
        for j in range(i):
            word = s[j:i]
            if word in word_list:
                if dp[j] is not None:
                    dp[i] = dp[j] + [word]
                    break

    return dp[-1] if dp[-1] is not None else [s]
def get_facts(function:FunctionContract,facts_dic:dict):
    # require name must be the same as the function name
    func_name=function.name
    func_name=func_name.replace('_','')
    func_name=func_name[0].upper() + func_name[1:]
    func_name=split_by_uppercase(func_name)
    func_name=[x.lower() for x in func_name]
    func_name=[x.split('_') for x in func_name]
    func_name_list=[x for y in func_name for x in y]
    func_name_str=' '.join(func_name_list)
    func_name_str=func_name_str.strip()
    func_name=nlp(func_name_str)
    if func_name.has_vector==False:
        result=[]
        for word in func_name_list:
            result.extend(word_segmentation(word, word_list))
        result=[x for x in result if len(x)>1]
        word_str=' '.join(result)
        word_str=word_str.strip()
        func_name=nlp(word_str)
    primary_targets=[]
    for facts_func in facts_dic.keys():
        if round(func_name.similarity(facts_func),2)>=0.7:
            primary_targets.extend(facts_dic[facts_func])
    return function_match(function,primary_targets)
def jugde_large(version):
    try:
        mid=version.split('.')[1]
        if int(mid)>=5:
            return True
        else:
            return False
    except:
        return False