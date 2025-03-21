from lark import Lark, Tree, Token

jml_grammar = r"""

%import common.WS
%ignore WS

// entry point
start: expr ";"

// expressions: literal, identifier, field/method access, parentheses, logical/arithmetic opertions, type casts
expr: 
    | expr_if 
    | expr_quantifier
    | expr_infix
expr_infix: expr_prefix (BINARY_OP expr_prefix)* (BINARY_OP (expr_if | expr_quantifier))?
expr_prefix: (UNARY_OP | expr_type_cast)? expr_atom
expr_type_cast: "(" type ")"
expr_atom: ID | literal | access | expr_op_quantifier | expr_parentheses
expr_parentheses: "(" expr ")"

// JML if (a ? b : c): right-associative ternary
expr_if: expr  "?" expr  ":" expr_if
    | expr "?" expr  ":" expr
// TODO: Compare to Open JML: expr_if: expr  "?" expr  ":" expr

// JML \quantifier a; b; c: right-associative ternary
expr_quantifier: UNARY_OP? "\\" JML_QUANTIFIER var_decl ";" (expr?  ";")? expr

// JML \quantifier(a; b; c)
expr_op_quantifier: UNARY_OP? "\\" JML_QUANTIFIER "(" var_decl ";" (expr?  ";")? expr ")"

JML_QUANTIFIER: "forall" | "exists" | "choose" | "num_of" | "sum" | "product" | "max" | "min"
var_decl: type ID

// field or method call
access: field | jml_field | method | jml_method | jml_method_type

field: ID index?
index: ("[" expr "]")*

method: ID "(" args? ")"
args: expr ("," expr)*

// JML field or method call
jml_field: "\\" JML_FIELD_NAME index?
JML_FIELD_NAME: "result"

jml_method: "\\" JML_METHOD_NAME "(" args? ")"
JML_METHOD_NAME: "old" | "typeof" | "elemtype" | "nonnullelements"

jml_method_type: "\\type" "(" type ")"

// java.util.LinkedList<String, Integer>[]
type: FULL_QUALIFIED_NAME type_generic? type_array?
type_generic: "<" type? ("," type)* ">"
type_array: "[]"*

// fully qualified type names
FULL_QUALIFIED_NAME: /[a-zA-Z$_][a-zA-Z0-9$_]*(\.[a-zA-Z$_][a-zA-Z0-9$_]*)*/

// identifier names
ID: /[a-zA-Z$_][a-zA-Z0-9$_]*/

// operators for JML and Java
BINARY_OP: "." | "&&" | "&" | "||" | "|" | "<==" | "==>" | "<==>" | "<=!=>" | "==" | "!=" | "<" | "<=" | ">" | ">=" | "+" | "-" | "*" | "/" | "%" | "^" | "<<" | ">>" | ">>>" | "<:" | "<:=" | "<#" | "<#="
UNARY_OP: "!" | "~" | "-"

// numbers, strings, character literals
literal: NULL
       | BOOLEAN
       | INTEGER
       | BINARY_INTEGER
       | OCTAL_INTEGER
       | HEX_INTEGER
       | FLOAT_LITERAL
       | LONG_LITERAL
       | CHAR_LITERAL
       | STRING_LITERAL

NULL: "null"
BOOLEAN: "true" | "false"
INTEGER: /[+-]?\d{1,3}(_\d{3})*/
BINARY_INTEGER: /[+-]?0[bB][01]+/
OCTAL_INTEGER: /[+-]?0[0-7]+/
HEX_INTEGER: /[+-]?0[xX][0-9a-fA-F]+/
FLOAT_LITERAL: /[+-]?\d+(\.\d+)?([eE][+-]?\d+)?[fF]?/
LONG_LITERAL: /[+-]?\d+[lL]/
CHAR_LITERAL: /'[^\']'/
STRING_LITERAL: /"(\\"|\\\\|[^"])*"/

"""


## Example JML Specification with Method Calls ##


### BASIC ###

jml_spec_basic_001= r"""
a;
"""
jml_spec_basic_002 = r"""
foo("H\\al\"lo", -5.0, null, true, false, 42.3, -5.0f, 1_000_000, \result[0], \result, \type(Z));
"""

### JML ###

jml_spec_jml_001 = r"""
foo(\result[0], \result, \old(a));
"""

### TYPES ###

jml_spec_types_001 = r"""
\type(java.util.LinkedList<String, Integer>[]);
"""
jml_spec_types_002 = r"""
foo(\typeof(a));
"""
jml_spec_types_003 = r"""
\elemtype(\type(int[]));
"""
jml_spec_types_004 = r"""
foo((T) x.y);
"""
jml_spec_types_005 = r"""
((T) x).y;
"""

### INFIX ###

jml_spec_infix_001 = r"""
-a - -b;
"""
jml_spec_infix_002 = r"""
-a[x] - -b;
"""
# ((a + b) + c);
jml_spec_infix_003 = r"""
a + b + c;
"""
jml_spec_infix_004 = r"""
foo();
"""
jml_spec_infix_005 = r"""
z.t().x.foo();
"""


### IF ###
# TODO: Compare to Open JML

# a ? b : (c + d + e);
jml_spec_if_001 = r"""
a ? b : c + d + e;
"""
# a == (b ? (c == d) : (e == f == g));
jml_spec_if_002 = r"""
a == b ? c == d : e == f == g;
"""
# a ? b : (c ? d : e);
# NOT (a ? b : c) ? d : e;
jml_spec_if_003 = r"""
a ? b : c ? d : e;
"""
# a ? b : (c ? d : (e + f + g));
# NOT (a ? b : c) ? d : (e + f + g);
jml_spec_if_004 = r"""
a ? b : c ? d : e + f + g;
"""


### QUANTIFIER EXPRESSION ###

jml_spec_quantifier_001 = r"""
\forall T a; b; c;
"""
jml_spec_quantifier_002 = r"""
!\forall T a; b; c;
"""
jml_spec_quantifier_003 = r"""
 a == !\forall T a; b; c;
"""
# \forall T a; b; (\forall T c; d; e + f + g);
jml_spec_quantifier_004 = r"""
\forall T a; b; \forall T c; d; e + f + g;
"""
# \forall T a; (\forall T b; c; d + e + f); (g + h + i);
jml_spec_quantifier_005 = r"""
\forall T a; \forall T b; c; d + e + f; g + h + i;
"""

### QUANTIFIER OPERATION ###

jml_spec_quantifier_op_003 = r"""
\forall(T a; b; c ? d : e);
"""
# \forall(T a; (b + 2 + 3); ((c + 2 + 3) ? (x + 2 + 3) : (y + 2 + 3)));
jml_spec_quantifier_op_002 = r"""
\forall(T a; b + 2 + 3; c + 2 + 3 ? x + 2 + 3 : y + 2 + 3);
"""

### IF, QUANTIFIER ###
# TODO: Compare to Open JML

# (\forall T a; b; c) ? x : y;
jml_spec_if_quantifier_001 = r"""
\forall T a; b; c ? x : y;
"""
# x ? (\forall T a; b; c) : y;
jml_spec_if_quantifier_002 = r"""
x ? \forall T a; b; c : y;
"""
# x ? y : (\forall T a; b; c);
jml_spec_if_quantifier_003 = r"""
x ? y : \forall T a; b; c;
"""
# (a == \forall T a; b; c) ? x : y;
jml_spec_if_quantifier_004 = r"""
a == \forall T a; b; c ? x : y;
"""
# (b == a == \forall T a; b; c + d) ? x : y
jml_spec_if_quantifier_005 = r"""
b == a == \forall T a; b; c + d ? x : y;
"""
# (\forall T a; ( b ? c : d); e) ? f : g;
jml_spec_if_quantifier_006 = r"""
\forall T a; b ? c : d; e ? f : g;
"""
# ((((f == g) == h) == (\forall T a; b; c)) ? x : (y == s);
jml_spec_if_quantifier_007 = r"""
f == g == h == \forall T a; b; c ? x : y == s;
"""
# a ? b : (\forall T c; (d + e); (f + g + h));
jml_spec_if_quantifier_008 = r"""
a ? b : \forall T c; d + e; f + g + h;
"""
# a ? (\forall T b; (c + d); (e + f + g)) : (h + i + j);
jml_spec_if_quantifier_009 = r"""
a ? \forall T b; c + d; e + f + g : h + i + j;
"""
# (\forall T a; (b + 2 + 3); c) ? x : (y + 2 + 3);
jml_spec_if_quantifier_010 = r"""
\forall T a; b + 2 + 3; c ? x : y + 2 + 3;
"""
# (\forall T a; (b + 2 + 3); (c + 2 + 3)) ? (x + 2 + 3) : (y + 2 + 3);
jml_spec=\
jml_spec_if_quantifier_011 = r"""
\forall T a; b + 2 + 3; c + 2 + 3 ? x + 2 + 3 : y + 2 + 3;
"""


# Define the Unparser visitor
class JMLUnparser:

    def __init__(self):
        super().__init__()

    def unparse(self, tree, bracketing=False):
        return self.start(tree, bracketing)

    def start(self, node, bracketing=False):
        # start: expr ";"
        return self.expr(node.children[0], bracketing) + ";"

    def expr(self, node, bracketing=False):
        # expr: 
        # | expr_if 
        # | expr_quantifier
        # | expr_infix
        if node.children:
            expr = node.children[0]
            type = expr.data.value
            expr_code = ""

            if type == 'expr_if':
                expr_code = self.expr_if(expr)
            elif type == 'expr_quantifier':
                expr_code = self.expr_quantifier(expr)
            elif type == 'expr_infix':
                expr_code = self.expr_infix(expr)

            #return expr_code
            if bracketing:
                return f" ( {expr_code} ) "
            else:
                return f"{expr_code}"
        return ""  # e.g. foo() with empty args->expr

    def expr_infix(self, node):
        # expr_infix: expr_prefix (BINARY_OP expr_prefix)* (BINARY_OP (expr_if | expr_quantifier))?
        return "".join([self.expr_infix_segment(child) for child in node.children])

    def expr_infix_segment(self, child):
        if isinstance(child, Token):
            bin_op = child.value
            if bin_op == ".":
                return bin_op
            else:
                return f" {bin_op} "
        else:
            type = child.data.value
            if type == 'expr_prefix':
                return self.expr_prefix(child)
            elif type == 'expr_if':
                return self.expr_if(child)
            elif type == 'expr_quantifier':
                return self.expr_quantifier(child)

    def expr_prefix(self, node):
        # expr_prefix: (UNARY_OP | expr_type_cast)? expr_atom
        if len(node.children) == 2:
            if isinstance(node.children[0], Tree) and node.children[0].data.value == 'expr_type_cast':
                prefix = self.expr_type_cast(node.children[0])
            else:
                prefix = node.children[0].value
            return f"{prefix}{self.expr_atom(node.children[1])}"
        else:
            return self.expr_atom(node.children[0]) 

    def expr_type_cast(self, node):
        # expr_type_cast: "(" type ")"
        return f"({self.type(node.children[0])})"

    def expr_atom(self, node):
        # expr_atom: ID | literal | access | expr_op_quantifier | expr_parentheses
        expr_atom = node.children[0]

        if isinstance(node.children[0], Token):
            return self.expr_if(expr_atom)
        else:
            type = expr_atom.data.value
            if type == 'literal':
                return self.literal(expr_atom)
            elif type == 'access':
                return self.access(expr_atom)
            elif type == 'expr_op_quantifier':
                return self.expr_op_quantifier(expr_atom)
            elif type == 'expr_parentheses':
                return self.expr_parentheses(expr_atom)
    
    def expr_parentheses(self, node): 
        # expr_parentheses: "(" expr ")"
        return f"({self.expr(node.children[0])})"

    def expr_if(self, node):
        # // JML if (a ? b : c): right-associative ternary
        # expr_if: expr  "?" expr  ":" expr_if
        # | expr "?" expr  ":" expr
        condition = self.expr(node.children[0])
        if_branch = self.expr(node.children[1])
        if node.children[2].data.value == 'expr_if':
            else_branch = self.expr_if(node.children[2])
        else:
            else_branch = self.expr(node.children[2])
        return f"{condition} ? {if_branch} : {else_branch}"

    def expr_op_quantifier(self, node):
        # // JML \quantifier(a; b; c)
        # expr_op_quantifier: UNARY_OP? "\\" JML_QUANTIFIER "(" var_decl ";" (expr?  ";")? expr ")"
        return self.expr_quantifier(node)

    def expr_quantifier(self, node):
        # // JML \quantifier a; b; c: right-associative ternary
        # expr_quantifier: UNARY_OP? "\\" JML_QUANTIFIER var_decl ";" (expr?  ";")? expr
        offset = 0
        if isinstance(node.children[1], Token):  # are the first two nodes tokens?
            unary_op = node.children[0].value
            offset = 1
        else:
            unary_op = ""
        quantifier = node.children[0 + offset].value
        init = self.var_decl(node.children[1 + offset])
        bounds = self.expr(node.children[2 + offset])
        condition = self.expr(node.children[3 + offset])

        return self.expr_quantifier_kind(node, unary_op, quantifier, init, bounds, condition)
        
    def expr_quantifier_kind(self, node, unary_op, quantifier, init, bounds, condition):
        if node.data.value == 'expr_op_quantifier':
            return f"{unary_op}\\{quantifier}({init}; {bounds}; {condition})"  # \forall() with variables and expression
        else:
            return f"{unary_op}\\{quantifier} {init}; {bounds}; {condition}"  # \forall with variables and expression

        
    def var_decl(self, node):
        # var_decl: type ID
        type = self.type(node.children[0])
        variable = node.children[1].value  # T t
        return f"{type} {variable}"

    def access(self, node):
        # // field or method call
        # access: field | jml_field | method | jml_method | jml_method_type
        call = node.children[0]
        type = call.data.value

        if type == 'field':
            return self.field(call)
        elif type == 'jml_field':
            return self.jml_field(call)
        elif type == 'method':
            return self.method(call) 
        elif type == 'jml_method':
            return self.jml_method(call)
        elif type == 'jml_method_type':
            return self.jml_method_type(call)

    def field(self, node):
        # field: ID index?
        # Optional array index
        if len(node.children) == 2:
            field_name = node.children[0].value
            array_index = self.index(node.children[1])
            return f"{field_name}{array_index}"
        else:
            return node.children[0].value  # Field is simply an identifier

    def index(self, node):
        # index: ("[" expr "]")*
        return "[" + "][".join([self.expr(child) for child in node.children]) + "]"

    def method(self, node):
        # method: ID "(" args? ")"
        method_name = node.children[0].value
        args = self.args(node.children[1]) if len(node.children) > 1 else ""
        return f"{method_name}({args})"  # Method call with args
    
    def args(self, node):
        # args: expr ("," expr)*
        return ", ".join([self.expr(child) for child in node.children])  # Argument list

    def jml_field(self, node):
        # // JML field or method call
        # jml_field: "\\" JML_FIELD_NAME index?
        jml_field_name = node.children[0].value
        index = ""

        # Optional array index
        if len(node.children) == 2:
            index_expr = self.index(node.children[1])
            index = f"[{index_expr}]"
        
        return self.jml_field_kind(node, jml_field_name, index)
    
    def jml_field_kind(self, node, jml_field_name, index):
        return f"\\{jml_field_name}{index}"

    def jml_method(self, node):
        # jml_method: "\\" JML_METHOD_NAME "(" args? ")"
        jml_method_name = node.children[0].value
        args = ""

        if len(node.children) == 2:
            # Optional arguments
            args = self.args(node.children[1])
        
        return self.jml_method_kind(node, jml_method_name, args)
    
    def jml_method_kind(self, node, jml_method_name, args):
        return f"\\{jml_method_name}({args})"

    def jml_method_type(self, node):
        # jml_method_type: "\\type" "(" type ")"
        return f"\\type({self.type(node.children[0])})"  # \type() with argument (see Java .class)
    
    def type(self, node):
        # // java.util.LinkedList<String, Integer>[]
        # type: FULL_QUALIFIED_NAME type_generic? type_array?
        type = node.children[0].value
        if len(node.children) == 3:
            type_generic = self.type_generic(node.children[1])
            return f"{type}<{type_generic}>[]"
        elif len(node.children) == 2:
            if node.children[1].data.value == 'type_generic':
                type_generic = self.type_generic(node.children[1])
                return f"{type}<{type_generic}>"
            elif node.children[1].data.value == 'type_array':
                return f"{type}[]"
        return type

    def type_generic(self, node):
        # type_generic: "<" type? ("," type)* ">"
        return ", ".join([self.type(child) for child in node.children])  # Type list

    def type_array(self, node):
        # type_array: "[]"*
        return "[" + "][".join(["" for child in node.children]) + "]"

    def literal(self, node):
        # // numbers, strings, character literals
        # literal: NULL
        #    | BOOLEAN
        #    | INTEGER
        #    | BINARY_INTEGER
        #    | OCTAL_INTEGER
        #    | HEX_INTEGER
        #    | FLOAT_LITERAL
        #    | LONG_LITERAL
        #    | CHAR_LITERAL
        #    | STRING_LITERAL
        return node.children[0].value  # Literal value (e.g., 42, "test")


parser = Lark(jml_grammar, start="start")
print(jml_spec)
tree = parser.parse(jml_spec)
print(tree.pretty())  # Print parsed tree structure

# Unparse the parsed tree
unparser = JMLUnparser()
output = unparser.unparse(tree)

print("Unparsed output:", output)