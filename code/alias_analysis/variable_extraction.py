
from utils.all_type import translate_op_type
from utils.code_fact import binaryOperationFacts
from slither.core.declarations import FunctionContract
from slither.core.expressions.literal import Literal
from slither.core.expressions.identifier import Identifier
from slither.core.expressions.index_access import IndexAccess
from slither.core.expressions.member_access import MemberAccess
from slither.core.expressions.binary_operation import BinaryOperation
from slither.core.expressions.call_expression import CallExpression
from slither.core.expressions.type_conversion import TypeConversion
from slither.core.expressions.unary_operation import UnaryOperation
from slither.core.expressions.assignment_operation import AssignmentOperation
from slither.core.declarations.function_contract import FunctionContract
from slither.slithir.variables.temporary import TemporaryVariable
from slither.slithir.variables.reference import ReferenceVariable
from slither.core.expressions.tuple_expression import TupleExpression
from slither.slithir.variables.local_variable import LocalVariable
from configs import *
from memory_profiler import profile
from slither.core.declarations.modifier import Modifier
import copy
# @profile
def get_variable_dict(function:FunctionContract,code_file=None):
    lists=variable_in_call_chain(function,code_file)
    res=convert2dict(lists)
    return res

def judge_literal(var:BinaryOperation):
    if var.operator=='literal':
        return True
    return False

def variable_in_call_chain(function:FunctionContract,code_file=None):
    if not isinstance(function,FunctionContract) and not isinstance(function,Modifier):
        return []
    vars_list = []
    if function.nodes==None or len(function.nodes)==0:
        return []
    for node in function.all_nodes():
        
        if not hasattr(node,'type') or not hasattr(node.type,'name') or (node.type.name!='EXPRESSION' and not (node.type.name=='VARIABLE' and hasattr(node,'expression'))):
            continue
        expression=node.expression
        if isinstance(expression,AssignmentOperation):
            left=process_expression(expression.expression_left,code_file)
            right=process_expression(expression.expression_right,code_file)
            if not (judge_literal(left) and judge_literal(right)):
                vars_list.append([left,right])
        elif isinstance(expression,CallExpression):
            if hasattr(expression,'called') and isinstance(expression.called,FunctionContract):
                for i in range(len(expression.arguments)):
                    temp1=binaryOperationFacts()
                    temp1.operator=translate_op_type('variable')
                    temp1.left_operand=can_name(expression.called.parameters[i],function)
                    temp1.left_operand_str=can_name(expression.called.parameters[i],function)
                    temp2=binaryOperationFacts()
                    temp2.operator=translate_op_type('variable')
                    temp2.left_operand=can_name(expression.arguments[i],function)
                    temp2.left_operand_str=can_name(expression.arguments[i],function)
                    # if not (judge_literal(temp1) and judge_literal(temp2)):
                    vars_list.append([temp1,temp2])
            elif hasattr(expression,'called') and hasattr(expression.called,'value') and isinstance(expression.called.value,FunctionContract):
                for i in range(len(expression.arguments)):
                    temp1=binaryOperationFacts()
                    temp1.operator=translate_op_type('variable')
                    temp1.left_operand=can_name(expression.called.value.parameters[i],function)
                    temp1.left_operand_str=can_name(expression.called.value.parameters[i],function)
                    temp2=binaryOperationFacts()
                    temp2.operator=translate_op_type('variable')
                    temp2.left_operand=can_name(expression.arguments[i],function)
                    temp2.left_operand_str=can_name(expression.arguments[i],function)
                    # if not (judge_literal(temp1) and judge_literal(temp2)):
                    vars_list.append([temp1,temp2])
    return vars_list

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
    node_source_file=node_source_file.decode('utf-8',errors='replace')
    if node_source_file=='':
        return str(node)
    if hasattr(node,'function'):
        if hasattr(node.function,'contract'):
            contract_name=node.function.contract.name
        else:
            contract_name='unknown'
        function_name=node.function.name
        argu_sign=node.function.signature[1]
        argu_sign=','.join(argu_sign)
        can_name=contract_name+'@@@'+function_name+'('+argu_sign+')'+'@@@'+node_source_file
    else:
        can_name=node_source_file
    return can_name




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

def process_caller(expression:CallExpression,code_file)->binaryOperationFacts:
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
    if len(result.left_operand)==1:
        result.left_operand=result.left_operand[0]
    return result,function_content
    
def convert2dict(lists)->dict:
    res={}
    for vars in lists:
        for var in vars:
            if var in res:
                res[var].extend(vars)
            else:
                res[var]=copy.deepcopy(vars)
    for var in res:
        res[var]=list(set(res[var]))
    return res