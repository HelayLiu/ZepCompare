from enum import Enum
class operationType(Enum):
    NONE="none"
    FUNCTIONCALL = "functionCall"
    VARIABLE = "variable"
    LITERAL = "literal"
    TYPECONVERSION="typeConversion"
    INDEXACCESS="indexAccess"
    MEMBERACCESS="memberAccess"
    LOCALVARIABLE="localVariable"
    TUPLEEXPRESSION="tupleExpression"
    TEMVARIABLE="temVariable"
    REFVARIABLE="refVariable"
    ASSIGNMENTOPERATION="assignmentOperation"
    OTHER="other"
    ADDADD="++"
    SUBSUB="--"
    EQ = "=="
    NEQ = "!="
    GT = ">"
    GTE = ">="
    LT = "<"
    LTE = "<="
    AND = "&&"
    OR = "||"
    NOT = "!"
    ADD = "+"
    SUB = "-"
    MULTIPLY = "*"
    DIVIDE = "/"
    MOD = "%"
    RM = ">>"
    LM = "<<"
    POWER = "**"
    BITWISEAND = "&"
    BITWISEOR = "|"
    BITWISEXOR = "^"
    BITWISENOT = "~"
    def __str__(self):
        if self == operationType.EQ:
            return "EQ"
        elif self == operationType.NEQ:
            return "NEQ"
        elif self == operationType.GT:
            return "GT"
        elif self == operationType.GTE:
            return "GTE"
        elif self == operationType.LT:
            return "LT"
        elif self == operationType.LTE:
            return "LTE"
        elif self == operationType.AND:
            return "AND"
        elif self == operationType.OR:
            return "OR"
        elif self == operationType.NOT:
            return "NOT"
        elif self == operationType.ADD:
            return "ADD"
        elif self == operationType.SUB:
            return "SUB"
        elif self == operationType.MULTIPLY:
            return "MULTIPLY"
        elif self == operationType.DIVIDE:
            return "DIVIDE"
        elif self == operationType.MOD:
            return "MOD"
        elif self == operationType.RM:
            return "RM"
        elif self == operationType.LM:
            return "LM"
        elif self == operationType.POWER:
            return "POWER"
        elif self == operationType.BITWISEAND:
            return "BITWISEAND"
        elif self == operationType.BITWISEOR:
            return "BITWISEOR"
        elif self == operationType.BITWISEXOR:
            return "BITWISEXOR"
        elif self == operationType.BITWISENOT:
            return "BITWISENOT"
        elif self == operationType.FUNCTIONCALL:
            return "FUNCTIONCALL"
        elif self == operationType.VARIABLE:
            return "VARIABLE"
        elif self == operationType.LITERAL:
            return "LITERAL"
        elif self == operationType.TYPECONVERSION:
            return "TYPECONVERSION"
        elif self == operationType.INDEXACCESS:
            return "INDEXACCESS"
        elif self == operationType.MEMBERACCESS:
            return "MEMBERACCESS"
        elif self == operationType.NONE:
            return "NONE"
        elif self == operationType.ADDADD:
            return "ADDADD"
        elif self == operationType.SUBSUB:
            return "SUBSUB"
        elif self == operationType.LOCALVARIABLE:
            return "LOCALVARIABLE"
        elif self == operationType.TUPLEEXPRESSION:
            return "TUPLEEXPRESSION"
        elif self == operationType.TEMVARIABLE:
            return "TEMVARIABLE"
        elif self == operationType.REFVARIABLE:
            return "REFVARIABLE"
        elif self == operationType.ASSIGNMENTOPERATION:
            return "ASSIGNMENTOPERATION"
        elif self == operationType.OTHER:
            return "OTHER"
        
        else:
            print(self)
            assert False
    def __repr__(self):
        return self.value
    def __eq__(self, other):
        if isinstance(other, operationType):
            return self.value == other.value
        elif isinstance(other, str):
            return self.value == other
        else:
            return False
    def __hash__(self):
        return hash(self.value)
def translate_op_type(op_type):
    if op_type == operationType.EQ:
        return operationType.EQ
    elif op_type == operationType.NEQ:
        return operationType.NEQ
    elif op_type == operationType.GT:
        return operationType.GT
    elif op_type == operationType.GTE:
        return  operationType.GTE
    elif op_type == operationType.LT:
        return operationType.LT
    elif op_type == operationType.LTE:
        return operationType.LTE
    elif op_type == operationType.AND:
        return operationType.AND
    elif op_type == operationType.OR:
        return operationType.OR
    elif op_type == operationType.NOT:
        return operationType.NOT
    elif op_type == operationType.ADD:
        return operationType.ADD
    elif op_type == operationType.SUB:
        return operationType.SUB
    elif op_type == operationType.MULTIPLY:
        return operationType.MULTIPLY
    elif op_type == operationType.DIVIDE:
        return operationType.DIVIDE
    elif op_type == operationType.MOD:
        return operationType.MOD
    elif op_type == operationType.RM:
        return operationType.RM
    elif op_type == operationType.LM:
        return operationType.LM
    elif op_type == operationType.POWER:
        return operationType.POWER
    elif op_type == operationType.BITWISEAND:
        return operationType.BITWISEAND
    elif op_type == operationType.BITWISEOR:
        return operationType.BITWISEOR
    elif op_type == operationType.BITWISEXOR:
        return operationType.BITWISEXOR
    elif op_type == operationType.BITWISENOT:
        return operationType.BITWISENOT
    elif op_type == operationType.FUNCTIONCALL:
        return operationType.FUNCTIONCALL
    elif op_type == operationType.VARIABLE:
        return operationType.VARIABLE
    elif op_type == operationType.LITERAL:
        return operationType.LITERAL
    elif op_type == operationType.TYPECONVERSION:
        return operationType.TYPECONVERSION
    elif op_type == operationType.INDEXACCESS:
        return operationType.INDEXACCESS
    elif op_type == operationType.MEMBERACCESS:
        return operationType.MEMBERACCESS
    elif op_type == operationType.NONE:
        return operationType.NONE
    elif op_type == operationType.ADDADD:
        return operationType.ADDADD
    elif op_type == operationType.SUBSUB:
        return operationType.SUBSUB
    elif op_type == operationType.LOCALVARIABLE:
        return operationType.LOCALVARIABLE
    elif op_type == operationType.TUPLEEXPRESSION:
        return operationType.TUPLEEXPRESSION
    elif op_type == operationType.TEMVARIABLE:
        return operationType.TEMVARIABLE
    elif op_type == operationType.REFVARIABLE:
        return operationType.REFVARIABLE
    elif op_type == operationType.ASSIGNMENTOPERATION:
        return operationType.ASSIGNMENTOPERATION
    elif op_type == operationType.OTHER:
        return operationType.OTHER
    else:
        return operationType.OTHER
class factsType(Enum):
    NONE="none"
    REQUIRE = "REQUIRE"
    REVERT = "REVERT"
    RETURN = "RETURN"
    VARIABLE = "VARIABLE"
    EXPRESSION = "EXPRESSION" #include revert and require
    CALLEXPRESSION = "CALLEXPRESSION"
    IF = "IF"
    NEW_VARIABLE="NEW VARIABLE"
    THROW="THROW"
    BREAK="BREAK"
    CATCH="CATCH"
    TRY="TRY"
    CONTINUE="CONTINUE"
    OTHER="OTHER"
    FUNCTION_ENTRY="FUNCTION_ENTRY"
    ASSEMBLY="ASSEMBLY"
    PLACEHOLDER="PLACEHOLDER"
    def __str__(self):
        return self.value
    def __repr__(self):
        return self.value
    def __eq__(self, other):
        if isinstance(other, factsType):
            return self.value == other.value
        elif isinstance(other, str):
            return self.value == other
        else:
            return False