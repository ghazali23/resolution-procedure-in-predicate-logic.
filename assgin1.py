#   ∀  ,∃
# Name : Aiman Motea
#Id 20210783
# Name: Ahmed Mohammed 
# Id 20210791
def eliminate_implication(formula):
    while "→" in formula:
        index = formula.find("→")
        f_index = index - 1
        if formula[index - 1].isalpha():
            f_index = index - 1
        elif formula[index - 2].isalpha():
            f_index = index - 2
        s_index = index + 1
        if formula[index + 1].isalpha():
            s_index = index + 1
        elif formula[index + 2].isalpha():
            s_index = index + 2

        while f_index >= 0 and formula[f_index].isalpha():
            f_index -= 1
        while s_index < len(formula) and formula[s_index].isalpha():
            s_index += 1

        formula = formula[:f_index + 1] + "~" + formula[f_index + 1:index] + " ∨ " + formula[index + 2:s_index] + formula[s_index:]

    return formula


#test_cases = "p(x)→ q"


#result = eliminate_implication(test_cases)
#print(result)


def move_negation_inward(formula):
    while "~(" in formula:
        start_index = formula.find("~(")
        end = start_index + 1
        count = 1
        while count != 0 and end < len(formula):
            end += 1
            if formula[end] == "(":
                count += 1
            elif formula[end] == ")":
                count -= 1
        exp = formula[start_index + 2:end]
        if "∧" in exp:
            conj = exp.split("∧")
            n_expr = "∨".join(["~(" + conj.strip() + ")" for conj in conj])
        elif "∨" in exp:
            disjunctions = exp.split("∨")
            n_expr = "∧".join(["~(" + disj.strip() + ")" for disj in disjunctions])
        else:
            n_expr = "~" + exp.strip()

        formula = formula[:start_index] + n_expr + formula[end + 1:]
    formula = formula.replace("~~", " ")
    return formula

#test_cases = "~( p(x) v q)"


#result = move_negation_inward(test_cases)
#print(result)







def move_quantifiers_to_left(formula):
    quantifiers = ''
    remaining_formula = formula
    while '∀' in remaining_formula or '∃' in remaining_formula:
        if '∀' in remaining_formula:
            index = remaining_formula.index('∀')
            quantifiers += '∀'
            quantifiers += remaining_formula[index+1]

            remaining_formula = remaining_formula[:index + 1] + '' + remaining_formula[index + 2:]
            remaining_formula = remaining_formula[:index] + remaining_formula[index+1:]
        elif '∃' in remaining_formula:
            index = remaining_formula.index('∃')
            quantifiers += '∃'
            quantifiers += remaining_formula[index+1]

            remaining_formula = remaining_formula[:index + 1] + ' ' + remaining_formula[index + 2:]
            remaining_formula = remaining_formula[:index] + remaining_formula[index+1:]
        else:
            break
    #print("move_quantifiers test" , quantifiers + remaining_formula)
    return quantifiers + remaining_formula

# Example usage:
#formula = "∃x ∀y (p(x) => ∀y q(y))"
#quantified_formula = move_quantifiers_to_left(formula)
#print("Quantified Formula:", quantified_formula)





def skolemization(formula):
    skolemized_formula = formula
    i = 0
    v="a"
    while i < len(skolemized_formula):
        if skolemized_formula[i] == '∃':
            var_start = i + 1
            var_end = var_start
            while skolemized_formula[var_end].isalnum():
                var_end += 1
            variable = skolemized_formula[var_start:var_end]
            # Replace the existential quantifier with Skolem function
            skolemized_formula = skolemized_formula[:i] + skolemized_formula[var_end:].replace(variable, 'f(' + v + ')', 1)
            v = chr(ord(v) + 1)

        i += 1
    return skolemized_formula

# Examples:
#formula1 = "∃x ∃y p(y)  p(x)"

#formula2 = "forall x ∃y p(x,y)"
#skolemized1 = skolemization(formula1)
#skolemized2 = skolemization(formula2)
#print("Skolemized formula 1:", skolemized1)  # Output: p(a)
#print("Skolemized formula 2:", skolemized2)  # Output: forall x p(x, f(a))



def eliminate_universal_quantifiers(formula):
    new_formula = ''
    i = 0
    while i < len(formula):
        if formula[i] == '∀':
            new_formula += ''
            i+=1
        else:
            new_formula += formula[i]
        i += 1
    return new_formula


def Turn_into_clauses(formula):
    formula = formula.split('∧')
    formula = [clause.replace('∨', ',') for clause in formula]
    return formula


def convert_to_CNF(formula):
    formula = eliminate_implication(formula)
    print("Step 1: Eliminate Implication:", formula)

    formula = move_negation_inward(formula)
    print("Step 2: Move Negation Inward & step 3: Remove Double Negation:", formula)

   # formula = standardize_variable_scope(formula)
    #print("Step 4: Standardize Variable Scope:", formula)


    formula = move_quantifiers_to_left(formula)
    print("Step 5: Prenex Form:", formula)


    formula = skolemization(formula)
    print("Step 6: Skolemization:", formula)

    cnf = eliminate_universal_quantifiers(formula)
    print("Step 7: Eliminate Universal Quantifiers:", cnf)


    return cnf

# Example usage:
formula = "∀x (p(x)→ q(x))) ∧ ∃y q ∨ r(y)"
cnf = convert_to_CNF(formula)
print("CNF Form:", cnf)

clauses =  Turn_into_clauses(cnf)
print("Step 9: Turn Conjunctions into Clauses:", clauses)




