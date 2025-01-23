import json
import hashlib
from re import S
from utils.all_type import operationType, factsType
from slither.core.declarations import FunctionContract,Event
import ssdeep
from memory_profiler import profile
def judge_sub_string(str1:str, str2:list):
    str1=str1.replace('_','')
    if len(str1)==1:
        return False
    for item in str2:
        item1=item.replace('_','')
        if str1 in item1 or item1 in str1:
            return True
    return False
class functionSignature:        
    def __init__(self, contract_name:str=str(), function_name:str=str(), params_type:list[str]=[], return_type:list[str]=[], emit_event:list[str]=[], constant_state_read:list[str]=[], constant_state_write:list[str]=[],version:str=str(), is_public:int=0):
        self.contract_name = contract_name
        self.function_name = function_name
        self.params_type = params_type
        self.return_type = return_type
        self.emit_event = emit_event
        self.constant_state_read = constant_state_read
        self.constant_state_write = constant_state_write
        self.is_public = is_public
        self.version = version
        
    def __str__(self):
        return json.dumps(self.__dict__)
    
    def caculate_hash(self):
        return hashlib.sha256(json.dumps(self.__dict__).encode('utf-8')).hexdigest()
    
    # msg.sender 
    # @profile
    def get_signature_in_func(self, function:FunctionContract):
        self.function_name = function.name
        self.contract_name = function.contract.name
        self.params_type = function.signature[1]
        self.return_type = function.signature[2]
        self.emit_event = []
        self.constant_state_write = []
        constant_write_name = set()
        self.constant_state_read = []
        constant_read_name = set()
        self.is_public = 1 if function.visibility == 'public' or function.visibility == 'external' else 0
        for node in function.all_nodes():
            if len(node.calls_as_expression)>0:
                for call in node.calls_as_expression:
                    if hasattr(call, 'called') and hasattr(call.called,'value') and isinstance(call.called.value, Event):
                        self.emit_event.append(call.called.value.name)
            if node.state_variables_read:
                for read in node.state_variables_read:
                    signature_str=read.signature_str
                    type_name=read.signature[1]+read.signature[2]
                    type_name='@'.join(type_name)
                    if signature_str not in constant_read_name:
                        constant_read_name.add(signature_str)
                        self.constant_state_read.append(type_name)
            if node.state_variables_written:
                for write in node.state_variables_written:
                    signature_str=write.signature_str
                    type_name=write.signature[1]+write.signature[2]
                    type_name='@'.join(type_name)
                    if signature_str not in constant_write_name:
                        constant_write_name.add(signature_str)
                        self.constant_state_write.append(type_name)
            if node.solidity_variables_read:
                for read in node.solidity_variables_read:
                    name=read.name
                    if name not in self.constant_state_read:
                        self.constant_state_read.append(name)
    def __eq__(self, __value: object) -> bool:
        if isinstance(__value, functionSignature):
            return self.function_name == __value.function_name and self.params_type == __value.params_type and self.return_type == __value.return_type and self.emit_event == __value.emit_event and self.constant_state_read == __value.constant_state_read and self.constant_state_write == __value.constant_state_write and self.contract_name == __value.contract_name and self.version == __value.version and self.is_public == __value.is_public
        else:
            return False
    def __hash__(self) -> int:
        temp_str = self.function_name + str(self.params_type) + str(self.return_type) + str(self.emit_event) + str(self.constant_state_read) + str(self.constant_state_write) + self.contract_name + self.version + str(self.is_public)
        return hash(temp_str)
    
    def is_subset(self, __value: object) -> bool:
        if isinstance(__value, functionSignature):
            # true_name = self.function_name.replace('_', '')
            # __value_name = __value.function_name.replace('_', '')
            # if self.function_name != __value.function_name and true_name!=__value_name:
            #     return False
            # if len(self.params_type) != len(__value.params_type):
            #     return False
            # else:
            if self.function_name=='constructor' or __value.function_name=='constructor':
                if len(self.params_type) != len(__value.params_type):
                    return False
                if len(self.return_type) != len(__value.return_type):
                    return False
                if len(self.constant_state_read) != len(__value.constant_state_read):
                    return False
                if len(self.constant_state_write) != len(__value.constant_state_write):
                    return False
                if len(self.emit_event) != len(__value.emit_event):
                    return False
            for param in self.params_type:
                if param not in __value.params_type and not judge_sub_string(param, __value.params_type):
                    return False
            # if len(self.return_type) != len(__value.return_type):
            #     return False
            # else:
            for ret in self.return_type:
                if ret not in __value.return_type and not judge_sub_string(ret, __value.return_type):
                    return False
            if len(self.emit_event) > len(__value.emit_event):
                return False
            else:
                for event in self.emit_event:
                    if event not in __value.emit_event and not judge_sub_string(event, __value.emit_event):
                        return False
            if len(self.constant_state_read) > len(__value.constant_state_read):
                return False
            else:
                for read in self.constant_state_read:
                    if read not in __value.constant_state_read and not judge_sub_string(read, __value.constant_state_read):
                        return False
            if len(self.constant_state_write) > len(__value.constant_state_write):
                return False
            else:
                for write in self.constant_state_write:
                    if write not in __value.constant_state_write and not judge_sub_string(write, __value.constant_state_write):
                        return False
            # if self.is_public != __value.is_public:
            #     return False
            return True
        else:
            return False

    def to_dict(self):
        return {
            "contract_name":self.contract_name,
            "function_name":self.function_name,
            "params_type":self.params_type,
            "return_type":self.return_type,
            "emit_event":self.emit_event,
            "constant_state_read":self.constant_state_read,
            "constant_state_write":self.constant_state_write,
            "is_public":self.is_public,
            "version":self.version
        }   

class binaryOperationFacts:
    def __init__(self, operator:operationType=operationType("none"), left_operand:"binaryOperationFacts"=None, right_operand:"binaryOperationFacts"=None):
        self.operator = operator
        self.left_operand = left_operand
        if left_operand is not None:
            self.left_operand_str = str(left_operand)
        else:
            self.left_operand_str = None
        self.right_operand = right_operand
        if right_operand is not None:
            self.right_operand_str = str(right_operand)
        else:
            self.right_operand_str = None
        
        
    
    def __eq__(self, __value: object) -> bool:
        if isinstance(__value, binaryOperationFacts):
            return self.operator == __value.operator and self.left_operand == __value.left_operand and self.right_operand == __value.right_operand
        else:
            return False
    def __hash__(self) -> int:
        return hash(self.operator) + hash(str(self.left_operand)) + hash(str(self.right_operand))

    def __str__(self):
        if self.left_operand is None or isinstance(self.left_operand, str):
            left_operand=self.left_operand
        elif isinstance(self.left_operand, binaryOperationFacts):
            left_operand=str(self.left_operand)
        else:
            left_operand=[]
            for item in self.left_operand:
                if isinstance(item,set) or isinstance(item,list):
                    left_operand.append([str(it) if it !=None else 'None' for it in item])
                else:
                    left_operand.append(str(item))
        if self.right_operand is None or isinstance(self.right_operand, str):
            right_operand=self.right_operand
        elif isinstance(self.right_operand, binaryOperationFacts):
            right_operand=str(self.right_operand)
        else:
            right_operand=[]
            for item in self.right_operand:
                if isinstance(item,set) or isinstance(item,list):
                    right_operand.append([str(it) if it !=None else 'None' for it in item])
                else:
                    right_operand.append(str(item))
        return f"{self.operator.value}({left_operand},{right_operand})"
    def to_dict(self):

        if self.left_operand is None or isinstance(self.left_operand, str):
            left_operand=self.left_operand
        elif isinstance(self.left_operand, binaryOperationFacts):
            left_operand=self.left_operand.to_dict()
        else:
            left_operand=[]
            for item in self.left_operand:
                if isinstance(item,set) or isinstance(item,list):
                    left_operand.append([it.to_dict() if it !=None else 'None' for it in item])
                else:
                    left_operand.append(item.to_dict())
        if self.right_operand is None or isinstance(self.right_operand, str):
            right_operand=self.right_operand
        elif isinstance(self.right_operand, binaryOperationFacts):
            right_operand=self.right_operand.to_dict()
        else:
            right_operand=[]
            for item in self.right_operand:
                if isinstance(item,set) or isinstance(item,list):
                    right_operand.append([it.to_dict() if it !=None else 'None' for it in item])
                else:
                    right_operand.append(item.to_dict())
        return {
            "operator":self.operator.value,
            "left_operand":left_operand,
            "left_operand_str":self.left_operand_str,
            "right_operand":right_operand,
            "right_operand_str":self.right_operand_str
        }   
    
class singleFact:

        
    def __init__(self, fact_type:factsType= factsType("none"),fact_str:str=str(), fact:binaryOperationFacts=binaryOperationFacts(), extra_info=None):
        self.fact_type = fact_type
        self.fact_str = fact_str
        self.fact = fact
        self.extra_info = extra_info
        self.context=None
    
    def __str__(self):
        return f"{self.fact_type.value}:({str(self.fact)})"
    def to_dict(self):
        return {
            "fact_type":self.fact_type.value,
            "fact_str":self.fact_str,
            "fact":self.fact.to_dict(),
            "extra_info":self.extra_info,
            "context":ssdeep.hash(self.context) if self.context!=None else None
        }
class functionFacts:
    
    def __init__(self, function_signature:functionSignature=functionSignature(), function_facts:list[singleFact]=list[singleFact()]):
        self.function_signature = function_signature
        self.function_facts = function_facts
    
    
    def get_function_signature(self):
        return self.function_signature
    def to_dict(self):
        dict_facts=[]
        for fact in self.function_facts:
            if isinstance(fact,singleFact):
                dict_facts.append(fact.to_dict())
            else:
                for sub_fact in fact:
                    dict_facts.append(sub_fact)
        return {
            "function_signature":self.function_signature.to_dict(),
            "function_facts":dict_facts
        }
    def __str__(self):
        function_name=self.function_signature.function_name
        contract_name=self.function_signature.contract_name
        version=self.function_signature.version
        key=contract_name+'_'+function_name+'@'+version
        fact_strs=[]
        for fact in self.function_facts:
            fact_strs.append(str(fact))
        return key+':\n'+'\n'.join(fact_strs)
