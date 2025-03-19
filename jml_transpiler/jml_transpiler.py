# https://www.openjml.org/tutorial/Expressions
from jml_parser import JMLUnparser

class JML2JavaTranspiler(JMLUnparser):

    # TODO: Some binary operators are interpreted differently in Java and JML

    def __init__(self):
        super().__init__()

    def expr_quantifier_kind(self, node, unary_op, quantifier, init, bounds, condition):
        lower_bounds = lower_bounds
        variable_types  = "int"  # TODO init
        variables = "i"  # TODO init

        if quantifier.lower() == "forall":
            self.expr_quantifier_forall(variable_types, variables, lower_bounds, bounds, condition)
        elif quantifier.lower() == "exists":
            self.expr_quantifier_exists(variable_types, variables, lower_bounds, bounds, condition)
        elif quantifier.lower() == "choose":
            self.expr_quantifier_choose(variable_types, variables, lower_bounds, bounds, condition)
        elif quantifier.lower() == "max":
            self.expr_quantifier_max(variable_types, variables, lower_bounds, bounds, condition)
        elif quantifier.lower() == "product":
            self.expr_quantifier_product(variable_types, variables, lower_bounds, bounds, condition)
        elif quantifier.lower() == "num_of":
            self.expr_quantifier_num_of(variable_types, variables, lower_bounds, bounds, condition)

    # \forall int i; 0 <= i < a.length; a[i] == 2*i
    def expr_quantifier_forall(self, variable_types, variables, lower_bounds, bounds, condition):
        jforall = "";
        for idx, variable in enumerate(variables):
            jforall += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
        jforall += f"if (!{condition}) {{return false;}}"
        for variable in variables:
            jforall += "}"
        jforall += "return true;"
        return jforall

    # \exists int i; 0 <= i < a.length; a[i] == 0
    def expr_quantifier_exists(self, variable_types, variables, lower_bounds, bounds, condition):
        jexists = "";
        for idx, variable in enumerate(variables):
            jexists += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
        jexists += f"if ({condition}) {{return true;}}"
        for variable in variables:
            jexists += "}"
        jexists += "return false;"
        return jexists

    #\choose int i; 0 <= i < a.length; a[i] == 0
    def expr_quantifier_choose(self, variable_types, variables, lower_bounds, bounds, condition):
        jchoose = "";
        for idx, variable in enumerate(variables):
            jchoose += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
        jchoose += f"if ({condition}) {{return {variable};}}"
        for variable in variables:
            jchoose += "}"
        jchoose += "throw new NotWellDefined();"
        return jchoose

    # \max int i; 0 <= i < a.length; a[i]
    def expr_quantifier_max(self, variable_types, variables, lower_bounds, bounds, expr_value):
        jchoose = "var max = null;";
        for idx, variable in enumerate(variables):
            jchoose += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
        jchoose += f"if (max == null || {expr_value} > max) {{max = {expr_value};}}"
        for variable in variables:
            jchoose += "}"
        jchoose += "if (max != null) {{ return max; }} else {{ throw new NotWellDefined(); }}"
        return jchoose

    # \min int i; 0 <= i < a.length; a[i]
    def expr_quantifier_min(self, variable_types, variables, lower_bounds, bounds, expr_value):
        jchoose = "var min = null;";
        for idx, variable in enumerate(variables):
            jchoose += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
        jchoose += f"if (min == null || {expr_value} < min) {{min = {expr_value};}}"
        for variable in variables:
            jchoose += "}"
        jchoose += "if (min != null) {{ return min; }} else {{ throw new NotWellDefined(); }}"
        return jchoose

    # \sum int i; 0 <= i < a.length; a[i]
    def expr_quantifier_sum(self, variable_types, variables, lower_bounds, bounds, expr_value):
        jsum = "var sum = 0;";
        for idx, variable in enumerate(variables):
            jsum += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
        jsum += f"sum += {expr_value};"
        for variable in variables:
            jsum += "}"
        jsum += "return sum;"
        return jsum

    # \product int i; 0 <= i < a.length; a[i]
    def expr_quantifier_product(self, variable_types, variables, lower_bounds, bounds, expr_value):
        jproduct = "var product = 0;";
        for idx, variable in enumerate(variables):
            jproduct += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
        jproduct += f"product *= {expr_value};"
        for variable in variables:
            jproduct += "}"
        jproduct += "return product;"
        return jproduct

    # \num_of int i; 0 <= i < a.length;
    def expr_quantifier_num_of(self, variable_types, variables, lower_bounds, bounds, condition):
        jnumof = "var num_of = 0";
        for idx, variable in enumerate(variables):
            jnumof += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
        jnumof += f"if ({condition}) {{++num_of;}}"
        for variable in variables:
            jnumof += "}"
        jnumof += "num_of;"
        return jnumof
    
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

# \\forall int i; 0 <= i && i < argv.length; argv[i] != null)
transpiler = JML2JavaTranspiler()
print(transpiler.expr_quantifier_forall(["i"], [0], "0 <= i && i < argv.length", "argv[i] != null"))