# https://www.openjml.org/tutorial/Expressions
from jml_parser import JMLUnparser
from lark import Lark, Tree, Token

class JML2JavaTranspiler(JMLUnparser):

    # TODO: Some binary operators are interpreted differently in JML and Java

    def __init__(self):
        super().__init__()
        self.variable_i = 0
        self.indention = 0
        self.indention_ws = "    "

    def new_variable(self, name):
        return f'__{name}_{self.variable_i}__'

    def start(self, node, bracketing=False):
        # start:
        return self.expr(node.children[0], bracketing)

    # TODO: use for(int i; true; ++i) if (!condition) break else code; to compute dynamic loop conditions inline
    def expr_quantifier_kind(self, node, unary_op, quantifier, init, bounds, condition):
        lower_bounds = bounds
        variable_types  = "int"  # TODO init
        variables = "i"  # TODO init

        if quantifier.lower() == "forall":
            jforall, result_variable = self.expr_quantifier_forall(variable_types, variables, lower_bounds, bounds, condition)
            return jforall
        elif quantifier.lower() == "exists":
            jexists, result_variable = self.expr_quantifier_exists(variable_types, variables, lower_bounds, bounds, condition)
            return jexists
        elif quantifier.lower() == "choose":
            jchoose, result_variable = self.expr_quantifier_choose(variable_types, variables, lower_bounds, bounds, condition)
            return jchoose
        elif quantifier.lower() == "max":
            jmax, result_variable = self.expr_quantifier_max(variable_types, variables, lower_bounds, bounds, condition)
            return jmax
        elif quantifier.lower() == "min":
            jmin, result_variable = self.expr_quantifier_max(variable_types, variables, lower_bounds, bounds, condition)
            return jmin
        elif quantifier.lower() == "sum":
            sum, result_variable = self.expr_quantifier_sum(variable_types, variables, lower_bounds, bounds, condition, False)  # TODO is floating point?
            return sum
        elif quantifier.lower() == "product":
            jproduct, result_variable = self.expr_quantifier_product(variable_types, variables, lower_bounds, bounds, condition, False)  # TODO is floating point?
            return jproduct
        elif quantifier.lower() == "num_of":
            jnum_of, result_variable = self.expr_quantifier_num_of(variable_types, variables, lower_bounds, bounds, condition)
            return jnum_of

    # \forall int i; 0 <= i < a.length; a[i] == 2*i
    def expr_quantifier_forall(self, variable_types, variables, lower_bounds, bounds, condition):
        result_variable = self.new_variable("result")
        jforall = self.t_statement(f'boolean {result_variable} = true')
        for idx, variable in enumerate(variables):
            for_init = f"{variable_types[idx]} {variable} = {lower_bounds[idx]}"
            for_condition = f"{result_variable} && ({bounds})"
            for_increment = f"++{variable}"
            jforall += self.t_for_i(for_init, for_condition, for_increment)
        jforall += self.t_if(f'!({condition})')
        jforall += self.t_statement(f'{result_variable} = false')
        jforall += self.t_close_block()
        for variable in variables:
            jforall += self.t_close_block()
        return jforall, result_variable
    
    # \exists int i; 0 <= i < a.length; a[i] == 0
    def expr_quantifier_exists(self, variable_types, variables, lower_bounds, bounds, condition):
        result_variable = self.new_variable('result')
        jexists = self.t_statement(f'boolean {result_variable} = false')
        for idx, variable in enumerate(variables):
            for_init = f'{variable_types[idx]} {variable} = {lower_bounds[idx]}'
            for_condition = f"!{result_variable} && ({bounds})"
            for_increment = f"++{variable}"
            jexists += self.t_for_i(for_init, for_condition, for_increment)
        jexists += self.t_if(f'{condition}')
        jexists += self.t_statement(f'{result_variable} = true')
        jexists += self.t_close_block()
        for variable in variables:
            jexists += self.t_close_block()
        return jexists, result_variable

    #\choose int i; 0 <= i < a.length; a[i] == 0
    def expr_quantifier_choose(self, variable_types, variables, lower_bounds, bounds, condition, selection):
        result_variable = self.new_variable('result')
        found_variable = self.new_variable("found")
        jchoose = self.t_statement(f'Object {result_variable} = null')
        jchoose = self.t_statement(f'boolean {found_variable} = false')
        for idx, variable in enumerate(variables):
            for_init = f'{variable_types[idx]} {variable} = {lower_bounds[idx]}'
            for_condition = f'!{found_variable} && ({bounds})'
            for_increment = f"++{variable}"
            jchoose += self.t_for_i(for_init, for_condition, for_increment)
        jchoose += self.t_if(f'{condition}')
        jchoose += self.t_statement(f'{found_variable} = true')
        jchoose += self.t_statement(f'{result_variable} = {selection}')
        jchoose += self.t_close_block()
        for variable in variables:
            jchoose += self.t_close_block()
        jchoose += self.t_if(f'!{found_variable}')
        jchoose += self.t_statement('throw new NotWellDefined()')
        jchoose += self.t_close_block()
        return jchoose, result_variable

    def expr_quantifier_minmax(self, operator, variable_types, variables, lower_bounds, bounds, expr_value):
        result_variable = self.new_variable('result')
        jminmax = self.t_statement(f'Object {result_variable} = null')
        for idx, variable in enumerate(variables):
            for_init = f'{variable_types[idx]} {variable} = {lower_bounds[idx]}'
            for_condition = bounds
            for_increment = f"++{variable}"
            jminmax += self.t_for_i(for_init, for_condition, for_increment)
        jminmax += self.t_if(f"({result_variable} == null || {expr_value} {operator} {result_variable})")
        jminmax += self.t_statement(f'{result_variable} = {expr_value}')
        jminmax += self.t_close_block()
        for variable in variables:
            jminmax += self.t_close_block()
        jminmax += self.t_if(f'{result_variable} == null')
        jminmax += self.t_statement('throw new NotWellDefined()')
        jminmax += self.t_close_block()
        return jminmax, result_variable

    # \max int i; 0 <= i < a.length; a[i]
    def expr_quantifier_max(self, variable_types, variables, lower_bounds, bounds, expr_value):
        return self.expr_quantifier_minmax(">", variable_types, variables, lower_bounds, bounds, expr_value)

    # \min int i; 0 <= i < a.length; a[i]
    def expr_quantifier_min(self, variable_types, variables, lower_bounds, bounds, expr_value):
        return self.expr_quantifier_min("<", variable_types, variables, lower_bounds, bounds, expr_value)

    def expr_quantifier_accumulate(self, operator, variable_types, variables, lower_bounds, bounds, expr_value, float):
        result_variable = self.new_variable('result')
        if float:
            jacc = self.t_statement(f'BigDecimal {result_variable} = 0')
        else:
            jacc = self.t_statement(f'BigInteger {result_variable} = 0')
        for idx, variable in enumerate(variables):
            for_init = f'{variable_types[idx]} {variable} = {lower_bounds[idx]}'
            for_condition = bounds
            for_increment = f"++{variable}"
            jacc += self.t_for_i(for_init, for_condition, for_increment)
        jacc += self.t_statement(f'{result_variable} = {result_variable}.{operator}({expr_value})')
        for variable in variables:
            jacc += self.t_close_block()
        return jacc, result_variable

    # \sum int i; 0 <= i < a.length; a[i]
    def expr_quantifier_sum(self, variable_types, variables, lower_bounds, bounds, expr_value, float):
        return self.expr_quantifier_accumulate("add", variable_types, variables, lower_bounds, bounds, expr_value, float)

    # \product int i; 0 <= i < a.length; a[i]
    def expr_quantifier_product(self, variable_types, variables, lower_bounds, bounds, expr_value, float):
        return self.expr_quantifier_accumulate("add", variable_types, variables, lower_bounds, bounds, expr_value, float)

    # \num_of int i; 0 <= i < a.length;
    # 12.5.1.3: This operation yields the number of values for which R(x) ∧ V(x) is true.
    def expr_quantifier_num_of(self, variable_types, variables, lower_bounds, bounds, condition):
        result_variable = self.new_variable('result')
        jnum_of = self.t_statement(f'BigInteger {result_variable} = 0')
        for idx, variable in enumerate(variables):
            for_init = f'{variable_types[idx]} {variable} = {lower_bounds[idx]}'
            for_condition = bounds
            for_increment = f"++{variable}"
            jnum_of += self.t_for_i(for_init, for_condition, for_increment)
        jnum_of += self.t_if(f"({condition})")
        jnum_of += self.t_statement(f'{result_variable} = {result_variable}.add(BigInteger.ONE)')
        jnum_of += self.t_close_block()
        for variable in variables:
            jnum_of += self.t_close_block()
        return jnum_of, result_variable
    
    def index(self, node):
        # TODO if type of collection/not array: use get()

        # index: ("[" expr "]")*
        return "[" + "][".join([self.expr(child) for child in node.children]) + "]"
    
    def jml_field_kind(self, node, jml_field_name, index):
         # TODO
         return f"__{jml_field_name}__(){index}"
    
    def jml_method_kind(self, node, jml_method_name, args):
        return f"__{jml_method_name}__({args})"

    def jml_method_type(self, node):
        # TODO: .class
        # jml_method_type: "\\type" "(" type ")"
        return f"{self.type(node.children[0])}.getClass()"  # \type() with argument (see Java .class)

    # TODO: Add to parser!
    def jml_method_elemtype(self):
        return "getClass(a[0])"

    # TODO: Add to parser!
    def jml_method_nonnullelements():
        return "a != null"

    ##### Template Helpers #####

    # template helper   
    def t_statement(self, code):
        return self.ws(code + ';')

    # template helper
    def t_open_block(self, code_before=''):
        return self.ws(f'{code_before} {{', la=+1)

    # template helper
    def t_close_block(self):
        return self.ws('}', lb=-1)

    # template helper
    def t_if(self, condition):
        return self.t_open_block(f'if ({condition})')
    
    # template helper
    def t_for_i(self, init, condition, increment):
        return self.t_open_block(f'for ({init}; {condition}; {increment})')
    
    # whitespace helper
    def ws(self, code, lb=0, la=0, n=True):
        """
        lb: increase/decrease nesting level before code by lb
        la: increase/decrease nesting level after code by la
        n: append new line
        """
        self.indention += lb
        indent = self.indention * self.indention_ws 
        self.indention += la

        if code == '':
            return code
        else:
            newline = '\n' if n else ''
            return '\n'.join(indent + line for line in code.splitlines()) + newline

# \\forall int i; 0 <= i && i < argv.length; argv[i] != null)
transpiler = JML2JavaTranspiler()

from jml_parser import jml_grammar

jml_spec = "\\forall int i; 0 <= i && i < argv.length; argv[i] != null;"

parser = Lark(jml_grammar, start="start")
print(jml_spec)
tree = parser.parse(jml_spec)
print(tree.pretty())  # Print parsed tree structure

# Unparse the parsed tree
unparser = JMLUnparser()
output = unparser.unparse(tree, bracketing=True)
print("Unparsed output:", output)

# Transpile JML to Java
transpiler = JML2JavaTranspiler()
output = transpiler.unparse(tree)
print(f"Transpiled output:\n{output}")
