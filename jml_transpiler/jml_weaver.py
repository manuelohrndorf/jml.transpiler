import os
import re
import sys


def erase_text(line, inside_textblock, inside_multiline_comment):
    """
    Determine if a line contains a comment or string. Removes the comment or string from that line.
    """

    found = False
    replacement = ' '

    #replacement = '#'  # for debugging
    #raw_line = line    # for debugging
    
    # Check if the text block ends on this line
    if inside_textblock:
        match = re.search(r'(?<!\\)"""', line)
        if match:
            line = replacement * match.end() + line[match.end():]  # code after
            inside_textblock = False
            found = True
            # can be followed by a comment
        else:
            line = replacement * len(line)
            line = line[:-1] + "\n"
            return found, line, inside_textblock, inside_multiline_comment
    
    # Check if the multiline comment ends on this line
    elif inside_multiline_comment:
        match = re.search(r'\*/', line) 
        if match:
            line = replacement * match.end() + line[match.end():]  # code after
            inside_multiline_comment = False
            found = True
            # can be followed by more comments
        else:
            line = replacement * len(line)
            line = line[:-1] + "\n"
            return found, line, inside_textblock, inside_multiline_comment
    
    if not inside_textblock and not inside_multiline_comment:
        # Check for strings
        line = re.sub(r'(?<!\\)"(.*?)"', lambda match: replacement * len(match.group()), line)

        # Check for multi-line comments opened and closed within the line
        line = re.sub(r"/\*.*?\*/", lambda match: replacement * len(match.group()), line)

        # Check for a start of a multi-line comment, single-line, or text block (cannot be closed on the same line)
        match = re.search(r'(?<!\\)(/\*|//|""")', line)
        if match:
            matched_text = match.group() 
            inside_textblock = True if matched_text.startswith('"""') else False
            inside_multiline_comment = True if matched_text.startswith('/*') else False
            start = match.start()
            line = line[:start] + replacement * (len(line) - start)
            line = line[:-1] + "\n"

    return found, line, inside_textblock, inside_multiline_comment


def extract_return_type_and_method_name(method_declaration):
    """
    Extract the return type and method name from a Java method declaration.
    """
    # Regular expression to capture the return type and method name
    pattern = r'(\S+)\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*\('  # Return type followed by method name before '('
    
    match = re.search(pattern, method_declaration)
    
    if match:
        return match.group(1), match.group(2)  # Return return type and method name
    else:
        return None, None  # No match found


def extract_method_parameters(parameter_declaration_list):
    """
    Extract parameter names from a Java method declaration.
    """
    # Split the parameters by comma and strip spaces
    parameter_declarations = parameter_declaration_list.split(',')
    
    # Extract the parameter names (last part of each parameter, which comes after the type)
    parameters = []

    for parameter_declaration in parameter_declarations:
        # Split by spaces and get the last part (the parameter name)
        parameter_declaration = parameter_declaration.strip()
        if parameter_declaration:  # To avoid empty strings in case of trailing commas or spaces
            parameter = parameter_declaration.split()
            parameters.append(parameter)
    
    return parameters


def extract_method_declaration(line, method_declaration_lines):
    """
    Extract the method name and its parameters (type, name pairs).
    """
    if '{' in line:
        method_declaration_lines.append(line.strip())
        method_declaration = ''.join(method_declaration_lines).strip()
        body_start = method_declaration.find('{') 
        parameter_start = method_declaration.find('(') 
        parameter_end = method_declaration.find(')')
        if parameter_start > -1 and parameter_end > -1 and parameter_start < parameter_end and parameter_end < body_start:
            method_type, method_name = extract_return_type_and_method_name(method_declaration)
            if method_name is not None:
                params = extract_method_parameters(method_declaration[parameter_start + 1:parameter_end])
                return method_type, method_name, params
    else:
        method_declaration_lines.append(line.strip())
        return False


def transpile_conditions(java_file):
    """
    Searches for requires and ensures annotations, then extracts the method and inserts the evaluation code.
    """
    jml_comment_pattern = re.compile(r'\s*//@\s*(requires|ensures)\s*(.*)')
    class_name = os.path.splitext(os.path.basename(java_file))[0]
    
    with open(java_file, 'r', encoding='utf-8') as file:
        lines = file.readlines()

    requires_comments = []
    ensures_comments = []

    inside_textblock = False
    inside_multiline_comment = False
    inside_annotated_method = False
    
    method_declaration_lines = []
    method_lines = []
    method_type = None
    method_name = None
    method_params = []
    method_nesting_level = 0

    lines_gen = []
    
    for i, line in enumerate(lines):
        lines_gen.append(line) 

        # Check if line contains //@ requires or //@ ensures
        if not inside_annotated_method and not inside_textblock and not inside_multiline_comment:
            jml_comment_match = jml_comment_pattern.match(line)
            if jml_comment_match:
                comment_type, comment_body = jml_comment_match.groups()
                if comment_type == "requires":
                    requires_comments.append(comment_body)
                    continue
                elif comment_type == "ensures":
                    ensures_comments.append(comment_body)
                    continue

        # Check if the line contains comments or strings
        found, line, inside_textblock, inside_multiline_comment = erase_text(line, inside_textblock, inside_multiline_comment)
        #lines_extended.extend(line)  # for debugging
        
        # Only search after annotations  
        if requires_comments or ensures_comments:

            if not inside_annotated_method:
                    method = extract_method_declaration(line, method_declaration_lines)
                    if method:
                        inside_annotated_method = True
                        method_type, method_name, method_params = method
                        method_nesting_level = 0

            if inside_annotated_method: 
                # collect method body
                method_lines.append(line)

                # Check for end of method body
                for i, char in enumerate(line):
                    if char == '{':
                        method_nesting_level += 1
                    elif char == '}':
                        method_nesting_level -= 1

                        # If nesting level goes back to 0, we found the closing brace
                        if method_nesting_level == 0:
                            method_lines[-1] = line[:i + 1]
                            method_lines_gen = insert_conditions(class_name, requires_comments, ensures_comments, method_type, method_name, method_params, method_lines, lines_gen[-len(method_lines):])
                            lines_gen[-len(method_lines):] = method_lines_gen
                            
                            requires_comments = []
                            ensures_comments = []
                            inside_annotated_method = False
                            method_declaration_lines = []
                            method_lines = []

    return class_name, lines_gen


def insert_conditions(class_name, requires_comments, ensures_comments, method_type, method_name, method_params, method_lines, method_lines_orig):
    """
    Inserts the requires and ensures code into a given method and transpile the JML code.
    """
    if requires_comments:
        method_lines_orig = insert_requires(class_name, method_name, method_params, method_lines, method_lines_orig)
    
    if ensures_comments:
        method_lines_orig, returns_value = insert_ensures(class_name, method_name, method_lines, method_lines_orig)

    if requires_comments:
        method_lines_orig.append(transpile_requires(class_name, requires_comments, ensures_comments, method_name, method_params))

    if ensures_comments:  
        method_lines_orig.append(transpile_ensures(class_name, ensures_comments, method_type, method_name, returns_value))

    return method_lines_orig


def insert_requires(class_name, method_name, params, method_lines, method_lines_orig):
    """ 
    Insert code to check required preconditions
    """
    assert len(method_lines) == len(method_lines_orig)
    params_code = ', '.join([param[1] for param in params])
    hook_code = 'Object[] $$$$$old$$$$$ = ' + method_name + '$$$$$requires(' + params_code + ');'
    body_start = method_lines[0].find('{')
    line_orig = method_lines_orig[0]
    code_gen = line_orig[:body_start + 1] + '\n' + hook_code + '\n' + line_orig[body_start + 1:]
    
    # NOTE: Always modify both...
    method_lines_orig[0] = code_gen
    method_lines[0] = code_gen
    return method_lines_orig


def insert_ensures(class_name, method_name, method_lines, method_lines_orig):
    """ 
    Insert code to check ensured postconditions 
    """
    method_code = ''.join(method_lines)
    method_code_orig = ''.join(method_lines_orig)

    # Erase anonymous classes: new Runnable() {...return...}
    anonymous_classes_pattern = re.compile(r'new\s+\w+\(\)\s*\{')
    method_code = erase_with_nesting(method_code, anonymous_classes_pattern)

    # Erase lambdas (with braces): x -> { return x * x; }
    lambdas_pattern = re.compile(r'\w+\s*->\s*\{')
    method_code = erase_with_nesting(method_code, lambdas_pattern)

    # Search for return statements:
    # Match void return;
    return_void_pattern = re.compile(r"\breturn\s*;", re.DOTALL)
    match = re.search(return_void_pattern, method_code)
    if match:
        hook_code = method_name + '$$$$$ensures($$$$$old$$$$$);'
        # NOTE: Always modify both...
        method_code_orig = method_code_orig[:match.start()] + '\n' + hook_code + '\n' + method_code_orig[match.start():]
        method_code = method_code[:match.start()] + '\n' + hook_code + '\n' + method_code[match.start():]

    # Match " return " or " return("
    return_pattern = re.compile(r"\breturn\s|\breturn\(")
    return_nesting_level = 0
    returns_value = False

    for match in re.finditer(return_pattern, method_code):
        for i, char in enumerate(method_code[match.end():]):
            if char == '{':
                return_nesting_level += 1
            elif char == '}':
                return_nesting_level -= 1
            elif return_nesting_level == 0 and char == ';':
                # If nesting level goes back to 0, and statement is closed by ';', we found the end of the return statement
                returns_value = True
                return_statement = method_code_orig[match.end():match.end() + i]
                hook_code = method_name + '$$$$$ensures($$$$$old$$$$$, ' + return_statement + ')'
                # NOTE: Always modify both...
                start = match.end()
                end = match.end() + i
                method_code_orig = method_code_orig[:start] + hook_code + method_code_orig[end:]
                method_code = method_code[:start] + hook_code + method_code[end:]
                break

    # Ensures on last line for void methods
    # NOTE: In principle, that may be already handled, e.g., if ... return; else ... return;.
    #       However, this would require control flow analysis, so we always check at the end of void methods.
    if not returns_value:
        hook_code = method_name + '$$$$$ensures($$$$$old$$$$$);'
        # NOTE: Always modify both...
        body_end = method_code.rfind('}')
        method_code_orig = method_code_orig[:body_end - 1] + '\n' + hook_code + '\n' + method_code_orig[body_end:]
        method_code = method_code[:body_end - 1] + '\n' + hook_code + '\n' + method_code[body_end:]

    return [method_code_orig], returns_value


def erase_with_nesting(method_code, pattern):
    nesting_level = 0

    for match in re.finditer(pattern, method_code):
        for i, char in enumerate(method_code[match.end() - 1:]):
            if char == '{':
                nesting_level += 1
            elif char == '}':
                nesting_level -= 1
            elif nesting_level == 0:
                start = match.end()
                end = match.end() + i - 2
                method_code = method_code[:start] + ' ' * (end - start) + method_code[end:]
                break
    return method_code


def transpile_requires(class_name, requires_comments, ensures_comments, method_name, params):
    """ 
    Process the //@ requires JML comment to generate the corresponding Java code 
    """
    params_code = ", ".join(" ".join(sublist) for sublist in params)
    method = f'\nprivate Object[] = {method_name}$$$$$requires({params_code}) {{return null;}}\n'
    return method


def transpile_ensures(class_name, ensures_comments, method_type, method_name, returns_value):
    """ 
    Process the //@ ensures JML comment to generate the corresponding Java code
    """
    if returns_value:
        method = f'\nprivate {method_type} {method_name} $$$$$ensures($$$$$old$$$$$, {method_type} result) {{}}\n'
    else:
        method = f'\nprivate void {method_name}$$$$$ensures($$$$$old$$$$$) {{}}\n'
    return method


if __name__ == "__main__":
    java_file = "./AbstractBoardGame.java"
    try:
        class_name, lines_gen = transpile_conditions(java_file)
        print(''.join(lines_gen))

        with open(java_file + '.java', 'w', encoding='utf-8') as file:
            file.writelines(lines_gen)
        
        print(f"File '{java_file}' modified successfully.")
    except FileNotFoundError:
        print(f"Error: File '{java_file}' not found.")
        sys.exit(1)
