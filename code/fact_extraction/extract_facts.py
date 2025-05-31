from ast import mod
from hmac import new
from multiprocessing import process
from operator import ge
import re
from turtle import left
from typing import final
from slither.core.declarations import FunctionContract
from utils.code_fact import functionFacts, singleFact, functionSignature,factsType, binaryOperationFacts
from utils.all_type import translate_op_type
from slither.core.expressions.binary_operation import BinaryOperation
from slither.core.expressions.call_expression import CallExpression
from slither.core.expressions.type_conversion import TypeConversion
from slither.core.expressions.unary_operation import UnaryOperation
from slither.core.expressions.literal import Literal
from slither.core.expressions.identifier import Identifier
from slither.core.expressions.index_access import IndexAccess
from slither.core.expressions.member_access import MemberAccess
from slither.slithir.variables.temporary import TemporaryVariable
from slither.core.expressions.tuple_expression import TupleExpression
from slither.slithir.variables.reference import ReferenceVariable
from slither.slithir.variables.local_variable import LocalVariable
from slither.core.declarations.function_contract import FunctionContract
from slither.core.cfg.node import Node
from slither.core.expressions.assignment_operation import AssignmentOperation
from memory_profiler import profile
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
def get_function_facts(function:FunctionContract,var_dic:dict,pairs_diff:dict)->functionFacts:
    stmts=find_target_statement(function,pairs_diff)
    result=functionFacts()
    result.function_signature.get_signature_in_func(function)
    result.function_facts=process_statement(stmts,var_dic)
    return result

# @profile
def get_node_facts(function:FunctionContract,node_list: list[Node],var_dic:dict,code_file='',funtion_sig=None)->list[singleFact]:
    result=functionFacts()
    result.function_signature=functionSignature()
    result.function_signature.get_signature_in_func(function)
    result.function_facts=process_node(node_list,var_dic,code_file)
    return result

def process_node_sub(node,code_file):
    node_type=node.type.name
    if node_type=='IF_LOOP' or node_type=='IFLOOP':
        node_type='IF'
    elif node_type=='OTHER_ENTRYPOINT' or node_type=='ENTRYPOINT' or node_type.startswith('END') or  node_type.startswith('START') or node_type=='PLACEHOLDER':
        return None
    fact_type=factsType(node_type)
    if fact_type==factsType.EXPRESSION:
        if ' revert ' in str(node).lower():
            primary_fact = process_revert_facts(node,code_file)
        elif node.contains_require_or_assert():
            primary_fact = process_require_facts(node,code_file)
        elif hasattr(node,'expression') and node.expression is not None and isinstance(node.expression,CallExpression):
            primary_fact,function_content = process_caller(node.expression,code_file,True)
            part_facts=singleFact(factsType.CALLEXPRESSION,str(primary_fact),primary_fact,'None')
            if function_content!=None and len(function_content)>0:
                final_fact=[part_facts,function_content]
            else:
                final_fact=part_facts
            return final_fact
        else:
            primary_fact= process_expression(node.expression,code_file)
    elif fact_type==factsType.VARIABLE:
        if node.expression is None:
            primary_fact = process_expression(node.sons[0].expression,code_file) if len(node.sons)>0 else process_expression(node.variable_declaration,code_file)
        else:
            primary_fact = process_expression(node.expression,code_file)
    else:
        primary_fact = process_expression(node.expression,code_file)
    if primary_fact is None:
        return None
    if isinstance(primary_fact,binaryOperationFacts):
        final_fact=singleFact(fact_type,str(primary_fact),primary_fact,'None')
    else:
        final_fact=primary_fact
    return final_fact

def process_node(target_nodes:list[Node],alias_dic:dict,code_file='')->list[singleFact]:
    facts_list=[]
    target_nodes.sort(key=lambda x:x.source_mapping.start)
    for node in target_nodes:
        if node.type.name=='ENTRYPOINT':
            
            binary_fact=binaryOperationFacts()
            binary_fact.operator=translate_op_type('OTHER')
            binary_fact.left_operand='0' if (node.function.visibility=='public' or node.function.visibility=='external') and (node.function.modifiers==None or len(node.function.modifiers)==0)  else '1'
            binary_fact.left_operand_str=str(node.function.visibility)+','+','.join(str(modifier) for modifier in node.function.modifiers)
            binary_fact.right_operand=node.function.name
            binary_fact.right_operand_str=node.function.name
            final_fact=singleFact(factsType.FUNCTION_ENTRY,str(binary_fact),binary_fact,'None')
            context=get_context(node)
            final_fact.context=context
            facts_list.append(final_fact)
            continue
        primary_fact=process_node_sub(node,code_file)
        if primary_fact is None:
            continue
        if isinstance(primary_fact,singleFact):
            extend_fact = extend_alias(primary_fact.fact,alias_dic)
            extend_fact=delete_facts_canonical_name(extend_fact)
            final_fact=singleFact(primary_fact.fact_type,str(extend_fact),extend_fact,primary_fact.extra_info)
            context=get_context(node)
            final_fact.context=context
        else:
            extend_fact = extend_alias(primary_fact[0].fact,alias_dic)
            extend_fact=delete_facts_canonical_name(extend_fact)
            final_fact1=singleFact(primary_fact[0].fact_type,str(extend_fact),extend_fact,primary_fact[0].extra_info)
            context=get_context(node)
            final_fact1.context=context
            func_content=[]
            for sub in primary_fact[1]:
                func_content.append(sub_process_fact(sub,alias_dic,context))
            final_fact=[final_fact1,func_content]
        facts_list.append(final_fact)
    return facts_list

def sub_process_fact(fact,alias_dic,context):
    if isinstance(fact,list):
        new_fact=[]
        for sub in fact:
            new_fact.append(sub_process_fact(sub,alias_dic,context))
        return new_fact
    if isinstance(fact,singleFact):
        extend_fact=extend_alias(fact.fact,alias_dic)
        extend_fact=delete_facts_canonical_name(extend_fact)
        final_fact=singleFact(fact.fact_type,str(extend_fact),extend_fact,fact.extra_info)
        final_fact.context=context
        return final_fact
def delete_facts_canonical_name(binary_fact):
    if isinstance(binary_fact,list):
        new_fact=[]
        for sub in binary_fact:
            new_fact.append(delete_facts_canonical_name(sub))
        binary_fact=new_fact
    if isinstance(binary_fact,set):
        new_fact=set()
        for sub in binary_fact:
            new_fact.add(delete_facts_canonical_name(sub))
        binary_fact=new_fact
    if isinstance(binary_fact,singleFact):
        binary_fact.fact=delete_facts_canonical_name(binary_fact.fact)
    if isinstance(binary_fact,binaryOperationFacts):
        if isinstance(binary_fact.left_operand,list):
            new_left=[]
            for sub in binary_fact.left_operand:
                new_left.append(delete_facts_canonical_name(sub))
            binary_fact.left_operand=new_left
        if isinstance(binary_fact.left_operand,set):
            new_left=set()
            for sub in binary_fact.left_operand:
                new_left.add(delete_facts_canonical_name(sub))
            binary_fact.left_operand=new_left
        if isinstance(binary_fact.right_operand,list):
            new_right=[]
            for sub in binary_fact.right_operand:
                new_right.append(delete_facts_canonical_name(sub))
            binary_fact.right_operand=new_right
        if isinstance(binary_fact.right_operand,set):
            new_right=set()
            for sub in binary_fact.right_operand:
                new_right.add(delete_facts_canonical_name(sub))
            binary_fact.right_operand=new_right
        if isinstance(binary_fact.left_operand,binaryOperationFacts):
            binary_fact.left_operand=delete_facts_canonical_name(binary_fact.left_operand)
        if isinstance(binary_fact.right_operand,binaryOperationFacts):
            binary_fact.right_operand=delete_facts_canonical_name(binary_fact.right_operand)
        if isinstance(binary_fact.left_operand,str):
            binary_fact.left_operand=binary_fact.left_operand.split('@@@')[-1]
        if isinstance(binary_fact.right_operand,str):
            binary_fact.right_operand=binary_fact.right_operand.split('@@@')[-1]
    return binary_fact

def find_target_statement(function:FunctionContract,pairs_diff:dict) -> list:
    if not isinstance(function, FunctionContract):
        return []
    target_statement=[]
    for node in function.all_nodes():
        flag=False
        for st in pairs_diff['adds']:
            if node.source_mapping.content in st:
                target_statement.append(node)
                flag=True
                break
        if flag:
            continue
        for st in pairs_diff['dels']:
            if node.source_mapping.content in st:
                target_statement.append(node)
    return target_statement

def process_require_facts(node,code_file=''):
    if not hasattr(node,'expression') or node.expression is None:
        return None
    facts_res=singleFact()
    facts_res.fact_type = factsType.REQUIRE
    requireArguments = node.expression.arguments
    condition = requireArguments[0]
    errorMsg = None 
    if len(requireArguments)>1:
        errorMsg = requireArguments[1]
    facts_res.fact_str=str(condition)
    facts_res.extra_info=str(errorMsg)
    facts_res.fact= process_expression(condition,code_file)
    return facts_res

def process_revert_facts(node,code_file=''):
    expression_tuple = (node.fathers,node)
    if_statement = [stsm for stsm in expression_tuple[0] if 'IF' in str(stsm)]
    if len(if_statement)==0:
        return None
    if_statement = if_statement[0]
    if not hasattr(if_statement,'expression') or if_statement.expression is None:
        return None
    facts_res=singleFact()
    facts_res.fact_type = factsType.REVERT
    exp = if_statement.expression
    errorMsg = str(node)
    if errorMsg.startswith('EXPRESSION revert(string)(') and errorMsg.endswith(')'):
        errorMsg = errorMsg.split('EXPRESSION revert(string)(')[1]
        errorMsg = errorMsg[:-1] 
    facts_res.fact_str=str(exp)
    facts_res.extra_info=errorMsg
    facts_res.fact= process_expression(exp,code_file)
    return facts_res


def process_expression(expression,code_file)->binaryOperationFacts:
    result = binaryOperationFacts()
    if expression is None:
        return None
    if isinstance(expression, BinaryOperation):
        opType = translate_op_type(str(expression.type))
        result.operator = opType
        result.left_operand = process_expression(expression.expression_left,code_file)
        result.left_operand_str = can_name(expression.expression_left)
        result.right_operand = process_expression(expression.expression_right,code_file)
        result.right_operand_str = can_name(expression.expression_right)
    elif isinstance(expression, Literal):
        opType = translate_op_type("literal")
        result.operator = opType
        result.left_operand = can_name(expression)
        result.left_operand_str = can_name(expression)
        result.right_operand = None
        result.right_operand_str = None
    elif isinstance(expression, TypeConversion):
        opType = translate_op_type("typeConversion")
        result.operator = opType
        result.left_operand = process_expression(expression.expression,code_file)
        result.left_operand_str = can_name(expression.expression)
        result.right_operand = None
        result.right_operand_str = None
    elif isinstance(expression, CallExpression):
        opType = translate_op_type("functionCall")
        result.operator = opType
        result.left_operand,_ = process_caller(expression,code_file)
        result.left_operand_str = can_name(expression)
        result.right_operand = None
        result.right_operand_str = None
    elif isinstance(expression, UnaryOperation):
        opType = translate_op_type(str(expression.type)) 
        exp = expression.expression
        result.operator = opType
        result.left_operand = process_expression(exp,code_file)
        result.left_operand_str = can_name(exp)
        result.right_operand = None
        result.right_operand_str = None
    elif isinstance(expression, Identifier):
        result.operator = translate_op_type("variable")
        result.left_operand = process_expression(expression.value,code_file)
        result.left_operand_str = can_name(expression.value)
        result.right_operand = None
        result.right_operand_str = None
    elif isinstance(expression, IndexAccess):
        result.operator = translate_op_type("indexAccess")
        result.left_operand = process_expression(expression.expression_left,code_file)
        result.left_operand_str = can_name(expression.expression_left)
        result.right_operand = process_expression(expression.expression_right,code_file)
        result.right_operand_str = can_name(expression.expression_right)
    elif isinstance(expression, MemberAccess):
        result.operator = translate_op_type("memberAccess")
        result.left_operand = process_expression(expression.member_name,code_file)
        result.left_operand_str = can_name(expression.member_name)
        result.right_operand = process_expression(expression.expression,code_file)
        result.right_operand_str = can_name(expression.expression)
    elif isinstance(expression, TupleExpression):
        result.operator = translate_op_type("tupleExpression")
        result.left_operand = process_expression(expression.expressions[0],code_file)
        result.left_operand_str = can_name(expression.expressions[0])
        result.right_operand = process_expression(expression.expressions[1],code_file) if len(expression.expressions)>1 else None
        result.right_operand_str = can_name(expression.expressions[1]) if len(expression.expressions)>1 else None
    elif isinstance(expression, ReferenceVariable):
        result.operator = translate_op_type("variable")
        result.left_operand = get_variable_code(expression,code_file)
        result.left_operand_str = get_variable_code(expression,code_file)
        result.right_operand = None
        result.right_operand_str = None
    elif isinstance(expression, TemporaryVariable):
        result.operator = translate_op_type("variable")
        result.left_operand = get_variable_code(expression,code_file)
        result.left_operand_str = get_variable_code(expression,code_file)
        result.right_operand = None
        result.right_operand_str =None
    elif isinstance(expression, LocalVariable):
        result.operator = translate_op_type("variable")
        can=can_name(expression)
        variable_name=get_variable_code(expression,code_file)
        flag_can=False
        if len(can.split('@@@')[-1]) < len(variable_name.split('@@@')[-1]): 
            flag_can=True
        result.left_operand =  can if flag_can else variable_name
        result.left_operand_str =  can if flag_can else variable_name
        result.right_operand = None
        result.right_operand_str = None
    elif isinstance(expression, AssignmentOperation):
        result.operator = translate_op_type("assignmentOperation")
        result.left_operand = process_expression(expression.expression_left,code_file)
        result.left_operand_str = can_name(expression.expression_left)
        result.right_operand = process_expression(expression.expression_right,code_file)
        result.right_operand_str = can_name(expression.expression_right)
    else:
        result.operator = translate_op_type("variable")
        can=can_name(expression)
        variable_name=get_variable_code(expression,code_file)
        flag_can=False
        if len(can.split('@@@')[-1]) < len(variable_name.split('@@@')[-1]): 
            flag_can=True
        result.left_operand = can if flag_can else variable_name
        result.left_operand_str = can if flag_can else variable_name
        result.right_operand = None
        result.right_operand_str = None
    return result

def get_variable_code(node, code_file):
    if not hasattr(node, "source_mapping") or node.source_mapping is None:
        return str(node)
    node_source_file=code_file[node.source_mapping.start:node.source_mapping.start+node.source_mapping.length]
    node_source_file=node_source_file.decode('utf-8')
    if node_source_file=='':
        return str(node)
    if hasattr(node,'function'):
        contract_name=node.function.contract.name
        function_name=node.function.name
        argu_sign=node.function.signature[1]
        argu_sign=','.join(argu_sign)
        can_name=contract_name+'@@@'+function_name+'('+argu_sign+')'+'@@@'+node_source_file
    else:
        can_name=node_source_file
    return can_name

def process_caller(expression:CallExpression,code_file,get_callee_inter=False)->binaryOperationFacts:
    called=expression.called
    result=binaryOperationFacts()
    result.operator=translate_op_type('functionCall')
    result.left_operand=process_expression(called,code_file)
    result.left_operand_str=can_name(called)
    result.right_operand=set()
    # result.right_operand_str=None
    for arg in expression.arguments:
        result.right_operand.add(process_expression(arg,code_file))
    if len(result.right_operand)==0:
        result.right_operand=None
    result.right_operand_str=str(result.right_operand)
    if not isinstance(called,FunctionContract) and not (hasattr(called,'value') and isinstance(called.value,FunctionContract)):
        return result,[]
    if hasattr(called,'value') and isinstance(called.value,FunctionContract):
        called=called.value
    flag=True
    return_node=None
    for node in called.nodes:
        strnode=str(node)
        if strnode.startswith('RETURN'):
            return_node=node
            break
        if strnode.startswith('ENTRY_POINT') or strnode.startswith('RETURN'):
            continue
        else:
            flag=False
            break
    function_content=[]
    result.left_operand=[result.left_operand]
    if flag and len(called.return_values)==1:
        
        return_value=called.return_values[0]
        if not(isinstance(return_value,ReferenceVariable) or isinstance(return_value,TemporaryVariable)):
            result.left_operand.append(process_expression(return_value,code_file)) 
        else:
            result.left_operand.append(process_expression(return_node.expression,code_file))
        
    else:
        if get_callee_inter:
            for node in called.nodes:
                if str(node).startswith('ENTRY_POINT') or str(node).startswith('RETURN'):
                    continue
                node_process=process_node_sub(node,code_file)
                if node_process!=None:
                    function_content.append(node_process)
                # result.left_operand.append(function_content)
    if len(result.left_operand)==1:
        result.left_operand=result.left_operand[0]
    return result,function_content
    


def extend_alias(fact,alias_dic:dict)->binaryOperationFacts:
    if isinstance(fact,list):
        new_fact=[]
        for sub in fact:
            new_fact.append(extend_alias(sub,alias_dic))
        fact=new_fact
    if isinstance(fact,set):
        new_fact=set()
        for sub in fact:
            new_fact.add(extend_alias(sub,alias_dic))
        fact=new_fact
    if isinstance(fact,singleFact):
        fact.fact=extend_alias(fact.fact,alias_dic)
    if isinstance(fact,binaryOperationFacts):
        if isinstance(fact.left_operand,list):
            new_left=[]
            for sub in fact.left_operand:
                if isinstance(sub,binaryOperationFacts):
                    new_left.append(extend_alias(sub,alias_dic))
                else:
                    new_left.extend(extend_alias(sub,alias_dic))
            fact.left_operand=new_left
        elif isinstance(fact.left_operand,set):
            new_left=set()
            for sub in fact.left_operand:
                if isinstance(sub,binaryOperationFacts):
                    new_left.add(extend_alias(sub,alias_dic))
                else:
                    new_left.update(extend_alias(sub,alias_dic))
            fact.left_operand=new_left
        else:
            if fact.left_operand in alias_dic:
                # if fact.left_operand in alias_dic[fact.left_operand]:
                fact.left_operand = alias_dic[fact.left_operand]
                # else:
                #     fact.left_operand = alias_dic[fact.left_operand] + [fact.left_operand]
            else:
                if isinstance(fact.left_operand,binaryOperationFacts):
                    fact.left_operand = extend_alias(fact.left_operand,alias_dic)
                else:
                    fact.left_operand = fact.left_operand# add str
        if isinstance(fact.right_operand,list):
            new_right=[]
            for sub in fact.right_operand:
                if isinstance(sub,binaryOperationFacts):
                    new_right.append(extend_alias(sub,alias_dic))
                else:
                    new_right.extend(extend_alias(sub,alias_dic))
            fact.right_operand=new_right
        elif isinstance(fact.right_operand,set):
            new_right=set()
            for sub in fact.right_operand:
                if isinstance(sub,binaryOperationFacts):
                    new_right.add(extend_alias(sub,alias_dic))
                else:
                    new_right.update(extend_alias(sub,alias_dic))
            fact.right_operand=new_right
        else:
            if fact.right_operand in alias_dic:
                # if fact.right_operand in alias_dic[fact.right_operand]:
                fact.right_operand = alias_dic[fact.right_operand]
                # else:
                #     fact.right_operand = alias_dic[fact.right_operand] + [fact.right_operand]
            else:
                if isinstance(fact.right_operand,binaryOperationFacts):
                    fact.right_operand = extend_alias(fact.right_operand,alias_dic)
                else:
                    fact.right_operand = fact.right_operand
    return fact


def process_statement(target_statement:list,alias_dic:dict)->list[singleFact]:
    facts_list=[]
    for statement in target_statement:
        if isinstance(statement,tuple):
            primary_fact = process_revert_facts(statement)
            if primary_fact is None:
                continue
            extend_fact = extend_alias(primary_fact.fact,alias_dic)
            final_fact=singleFact(primary_fact.fact_type,primary_fact.fact_str,extend_fact,primary_fact.extra_info)
            context=get_context(statement)
            final_fact.context=context
            facts_list.append(final_fact)
        ## temp process
        # else:
        #     primary_fact = process_require(statement)
        #     extend_fact = extend_alias(primary_fact.fact,alias_dic)
        #     context=get_context(statement)
        #     final_fact=singleFact(primary_fact.fact_type,primary_fact.fact_str,extend_fact,primary_fact.extra_info)
        #     final_fact.context=context
        #     facts_list.append(final_fact)
    return facts_list



def can_name(expression,function=None):
    if hasattr(expression,'canonical_name'):
        # if hasattr(expression,'ssa_name'):
        #     return expression.canonical_name.split('.')[0]+'.'+expression.canonical_name.split('.')[1]+'.'+expression.ssa_name
        # else:
        temp=expression.canonical_name
        name=temp.split('.')[-1]
        if name.startswith('switch_expr_'):
            temp=temp.replace(name,'switch_expr')
        temp=temp.replace('.','@@@')
        return temp
    elif function != None:
        contract_name=function.contract.name
        function_name=function.name
        argu_sign=function.signature[1]
        argu_sign=','.join(argu_sign)
        exp=str(expression)
        if exp.startswith('switch_expr_'):
            exp='switch_expr'
        can_name=contract_name+'@@@'+function_name+'('+argu_sign+')'+'@@@'+exp
        return can_name
    else:
        if str(expression).startswith('switch_expr_'):
            expression='switch_expr'
        return str(expression)