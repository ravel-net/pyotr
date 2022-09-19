import re

class SelectedAttribute:
    def __init__(self, attribute_str, databases={}, array_operators=[], arithmatic_operators=[]):
        self._databases = databases
        self._array_operators = array_operators
        self._arithmatic_operators = arithmatic_operators
        self._has_alias = " as " in attribute_str
        self._alias = None

        '''
        # type: 1 - normal attribute(t1.c0), 
                'normal':NormalAttribute
        # 2 - array attribute(array[t1.n0, ...]), 
                'array': ArrayAttribute
        # 3 - array operation attribute(c1 || c2, c1 @> c2),
                'operator': string
                'operands': [NormalAttribute, ArrayAttribute]
        # 4 - arithmatic operation attribute(1*3+c3-c4)
                'function': ArithmaticAttribute
        # 5 - array element arribute(t1.c0[0])
                'array_elem': ArrayElementAttribute

        # default normal attribute
        '''
        self._attribute = {'type': 1} 

        attribute_part = None
        if self._has_alias:
            parts = attribute_str.split(" as ")
            self._alias = parts[1].strip()
            attribute_part = parts[0].strip()
            self._process_attribute_part(attribute_part)
        else:
            self._alias = str(attribute_str)
            self._process_attribute_part(attribute_str)
        

    def __str__(self):
        if self._has_alias:
            return "{} as {}".format(self.AttributePart, self._alias)
        else:
            return self.AttributePart
    
    @property
    def table(self): # only works for type 1
        if self._attribute['type'] == 1: 
            return self._attribute['normal'].table
        else:
            return ""
    
    @property
    def attribute(self): # only works for type 1
        if self._attribute['type'] == 1:
            return self._attribute['normal'].attribute
        else:
            return ""
    
    @property
    def AttributePart(self):
        if self._attribute['type'] == 1:
            return str(self._attribute['normal'])
        elif self._attribute['type'] == 2:
            return str(self._attribute['array'])
        elif self._attribute['type'] == 3:
            return str(self._attribute['operator']).join(self._attribute['operands'])
        elif self._attribute['type'] == 4:
            return str(self._attribute['function'])
        elif self._attribute['type'] == 5:
            return str(self._attribute['array_elem'])

    @property
    def AttributeName(self):
        # get attibute
        
        if self._has_alias:
            return str(self._alias)
        else:
            return self.AttributePart

    def concatenation(self, simple_attr_mapping):
        if self._attribute['type'] == 2: # assume ArrayAttribute need to be concatenation when converting to SQL
            return self._attribute['array'].concatenation(simple_attr_mapping)

    def _process_attribute_part(self, attribute_part):
        # for array_operator_attribute
        for array_op in self._array_operators:
            if array_op in attribute_part:
                # print(3)
                self._attribute['type'] = 3
                self._process_array_operator_attribute(attribute_part)
                return
        
        # for arithmatic operation attribute
        for arithmatic_opr in self._arithmatic_operators:
            if arithmatic_opr in attribute_part:
                # print(4)
                self._attribute['type'] = 4
                self._attribute['function'] = ArithmaticAttribute(attribute_part)
                return
        
        # for array attribute
        if attribute_part.lower().startswith('array'):
            # print(2)
            self._attribute['type'] = 2
            self._attribute['array'] = ArrayAttribute(attribute_part)
            return
        
        if '[' in attribute_part and ']' in attribute_part and 'array' not in attribute_part.lower():
            self._attribute['type'] = 5
            self._attribute['array_elem'] = ArrayElementAttribute(attribute_part)

        # for nomal attribute
        self._attribute['type'] = 1
        self._attribute['normal'] = NormalAttribute(attribute_part)
        
    def _process_array_operator_attribute(self, attribute_part, operator):
        self._attribute['operator'] = operator
        self._attribute['operands'] = []
        items = attribute_part.split(operator)

        for item in items:
            item = item.strip()
            if item.startswith('array'):
                self._attribute['operands'].append(ArrayAttribute(item))
            else:
                self._attribute['operands'].append(NormalAttribute(item))

    # def _concatenation_opr(self, attribute_part):
    #     self._attribute['operator'] = '||'
    #     self._attribute['operands'] = []
    #     items = attribute_part.split("||")

    #     for item in items:
    #         item = item.strip()
    #         if item.startswith('array'):
    #             self._attribute['operands'].append(ArrayAttribute(item))
    #         else:
    #             self._attribute['operands'].append(NormalAttribute(item))

    # def _implication_opr(self, attribute_part, operator):
    #     self._attribute['operator'] = operator
    #     self._attribute['operands'] = []
    #     for opd in attribute_part.split(operator):
    #         opd = opd.strip()

    #         if opd.startswith('array'):
    #             self._attribute['operands'].append(ArrayAttribute(opd))
    #         else:
    #             self._attribute['operands'].append(NormalAttribute(opd))

class NormalAttribute:
    def __init__(self, normal_attribute_str):
        self._specify_table = '.' in normal_attribute_str
        self.table = None
        self.attribute = None # can be constant and variable

        if self._specify_table:
            parts = normal_attribute_str.split('.')
            self.table = parts[0].strip()
            self.attribute = parts[1].strip()
        else:
            self.attribute = normal_attribute_str

    def __str__(self):
        if self._specify_table:
            return "{}.{}".format(self.table, self.attribute)
        else:
            return self.attribute

class ArithmaticAttribute:
    """
    Assume no parenthesis in arithmatic function
    """
    def __init__(self, attribute_str, operators=[]):
        self._operators = operators
        self._operands = []
        self._operator_after_operands = {}
        begin_pos = 0
        for i in range(len(attribute_str)):
            opr = attribute_str[i]
            if opr in self._operators:
                self._operands.append(SelectedAttribute(attribute_str[begin_pos:i].strip()))
                begin_pos = i + 1

                opr_after_jth_operand = len(self._operands)-1
                self._operator_after_operands[opr_after_jth_operand] = opr # zero-based numbering
    
    def __str__(self) -> str:
        string = ""
        for j in range(len(self._operands)-1):
            string += self._operands[j]
            string += self._operator_after_operands[j]
        string += self._operands[-1]
        return string
   
class ArrayAttribute:
    def __init__(self, array_str):
        self.items = []

        patern = re.compile(r'array\[(.*)\]', re.I)
        items_str = re.findall(patern, array_str)[0].strip()
        
        for attr in items_str.split(","):
            attr = attr.strip()
            self.items.append(SelectedAttribute(attr))

    def __str__(self):
        item_strs = []
        for item in self.items:
            item_strs.append(str(item))
        return "ARRAY[{}]".format(', '.join(item_strs))

    def concatenation(self, simple_attr_mapping):
        item_strs = []
        for item in self.items:
            # print("\nitem-------------", item._has_alias)
            # print("item", item.AttributeName)
            name = item.AttributeName
            if name in simple_attr_mapping:
                name = simple_attr_mapping[name].AttributeName
            item_strs.append(name)
        return "'[' || {} || ']'".format(', '.join(item_strs))

class ArrayElementAttribute(NormalAttribute):
    # Assume 1-D Array
    def __init__(self, array_element_str):

        patern = re.compile(r'(.*?)\[(.*)\]', re.I)
        (array_name_str, idx) = re.findall(patern, array_element_str)[0]
        self.index = idx

        super().__init__(array_name_str)

    def __str__(self):
        return "{}[{}]".format(super().__str__(), self.index)

    # def concatenation(self, simple_attr_mapping):
    #     item_strs = []
    #     for item in self.items:
    #         # print("\nitem-------------", item._has_alias)
    #         # print("item", item.AttributeName)
    #         name = item.AttributeName
    #         if name in simple_attr_mapping:
    #             name = simple_attr_mapping[name].AttributeName
    #         item_strs.append(name)
    #     return "'[' || {} || ']'".format(', '.join(item_strs))
