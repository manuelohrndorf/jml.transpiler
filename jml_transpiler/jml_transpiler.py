# https://www.openjml.org/tutorial/Expressions

# \forall int i; 0 <= i < a.length; a[i] == 2*i
def expr_forall(variable_types, variables, lower_bounds, bounds, condition):
    jforall = "";
    for idx, variable in enumerate(variables):
        jforall += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
    jforall += f"if (!{condition}) {{return false;}}"
    for variable in variables:
        jforall += "}"
    jforall += "return true;"
    return jforall

# \exists int i; 0 <= i < a.length; a[i] == 0
def expr_exists(variable_types, variables, lower_bounds, bounds, condition):
    jexists = "";
    for idx, variable in enumerate(variables):
        jexists += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
    jexists += f"if ({condition}) {{return true;}}"
    for variable in variables:
        jexists += "}"
    jexists += "return false;"
    return jexists

#\choose int i; 0 <= i < a.length; a[i] == 0
def expr_choose(variable_types, variables, lower_bounds, bounds, condition):
    jchoose = "";
    for idx, variable in enumerate(variables):
        jchoose += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
    jchoose += f"if ({condition}) {{return {variable};}}"
    for variable in variables:
        jchoose += "}"
    jchoose += "throw new NotWellDefined();"
    return jchoose

# \max int i; 0 <= i < a.length; a[i]
def expr_max(variable_types, variables, lower_bounds, bounds, expr_value):
    jchoose = "var max = null;";
    for idx, variable in enumerate(variables):
        jchoose += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
    jchoose += f"if (max == null || {expr_value} > max) {{max = {expr_value};}}"
    for variable in variables:
        jchoose += "}"
    jchoose += "if (max != null) {{ return max; }} else {{ throw new NotWellDefined(); }}"
    return jchoose

# \min int i; 0 <= i < a.length; a[i]
def expr_min(variable_types, variables, lower_bounds, bounds, expr_value):
    jchoose = "var min = null;";
    for idx, variable in enumerate(variables):
        jchoose += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
    jchoose += f"if (min == null || {expr_value} < min) {{min = {expr_value};}}"
    for variable in variables:
        jchoose += "}"
    jchoose += "if (min != null) {{ return min; }} else {{ throw new NotWellDefined(); }}"
    return jchoose

# \sum int i; 0 <= i < a.length; a[i]
def expr_sum(variable_types, variables, lower_bounds, bounds, expr_value):
    jsum = "var sum = 0;";
    for idx, variable in enumerate(variables):
        jsum += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
    jsum += f"sum += {expr_value};"
    for variable in variables:
        jsum += "}"
    jsum += "return sum;"
    return jsum

# \product int i; 0 <= i < a.length; a[i]
def expr_product(variable_types, variables, lower_bounds, bounds, expr_value):
    jproduct = "var product = 0;";
    for idx, variable in enumerate(variables):
        jproduct += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
    jproduct += f"product *= {expr_value};"
    for variable in variables:
        jproduct += "}"
    jproduct += "return product;"
    return jproduct

# \num_of int i; 0 <= i < a.length;
def expr_num_of(variable_types, variables, lower_bounds, bounds, condition):
    jnumof = "var num_of = 0";
    for idx, variable in enumerate(variables):
        jnumof += f"for ({variable_types[idx]} {variable} = {lower_bounds[idx]}; {bounds}; ++{variable}) {{"
    jnumof += f"if ({condition}) {{++num_of;}}"
    for variable in variables:
        jnumof += "}"
    jnumof += "num_of;"
    return jnumof

def index():
    return "[]"

def jml_method_old():
    return "old()"

def jml_method_typeof():
    return "getClass()"

def jml_method_elemtype():
    return "getClass(a[0])"

def jml_method_nonnullelements():
    return "a != null"

def jml_method_type():
    return "class"

# \\forall int i; 0 <= i && i < argv.length; argv[i] != null)
print(expr_forall(["i"], [0], "0 <= i && i < argv.length", "argv[i] != null"))