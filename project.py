
def pretty_tt(table, variables):
    """Pretty print the truth table
        Args:
            table [][bool]: The truth table values
            variables [str]: The variables that appear in the formula
    """

    full_str = ""

    # Check how long our column should be
    # Length of 'False' is 5
    max_column_widths = [max(5, len(variable)) for variable in variables]
    # Length of 'Result' is 6
    max_column_widths.append(6)

    separator = "+"
    for i, width in enumerate(max_column_widths):
        if i == len(max_column_widths) - 1:
            separator += "+"
        separator += width * "-"
        separator += "+"

    full_str += separator + "\n"

    header = "|"
    for i, variable in enumerate(variables):
        header += variable.ljust(max_column_widths[i])
        header += "|"

    header += "|"
    header += "Result|"

    full_str += header + "\n"

    full_str += separator + "\n"

    # Print the rows containing the truth values
    for row in table:
        row_str = "|"
        for i, val in enumerate(row):
            if i == len(row) - 1:
                row_str += "|"

            row_str += str(val).ljust(max_column_widths[i])
            row_str += "|"
        full_str += row_str + "\n"

    full_str += separator + "\n"
    return full_str

def generate_assignment(size):
    # For i in range 2 ** len(variables)
    # convert the number to binary, and cut the leading 0b
    # then zero fill till we get the full variable length
    # Convert each value from string to int and then to bool,
    #  because string to bool doesn't work directly
    return [[bool(int(x)) for x in bin(i)[2:].zfill(size)]
                       for i in range(2 ** size)]


class Formula:
    def __init__(self):
        pass

    def modus_ponens(self, a, b):
        """Applies the Modus Ponens rule to two logical propositions

        Args:
            a (?): The antecedent proposition
            b (?): The consequent proposition
        Returns:
            bool: The result of applying Modus Ponens
        """
        pass

    def is_axiom1(self):
        """Checks if the given formula is constructed using Axiom 1

        Returns:
            bool: True if the formula is constructed with Axiom 1,
                False otherwise
        """
        pass

    def is_axiom2(self):
        """Checks if the given formula is constructed using Axiom 2

        Returns:
            bool: True if the formula is constructed with Axiom 2,
                False otherwise
        """
        pass

    def is_axiom3(self):
        """Checks if the given formula is constructed using Axiom 3

        Returns:
            bool: True if the formula is constructed with Axiom 3,
                False otherwise
        """
        pass

    def is_axiom(self):
        """???
        """
        pass

    def is_equal(self, formula):
        """Checks if the given formula is equal to the formula

        Args:
            formula (Formula): The Formula to check against

        Returns:
            bool: true if the formula is equal and false otherwise
        """
        return self.to_string() == formula.to_string()

    def get_tt(self, pretty=False, assignments=None):
        """Generate and print a truth tabel for the formula

        Args:
            pretty_print=False (bool): Turn on for less
                performance but better readability

            assignments=None (List[Dict[str][bool]]): 
                A list of assignments to evaluate,
                only to be used for equivalenz checking.

        """

        # List of [variable_assignments | truth value]
        table = []

        if assignments == None:
            # We always order variables before working with them
            variables = sorted(self.get_variables())

            # For i in range 2 ** len(variables)
            # convert the number to binary, and cut the leading 0b
            # then zero fill till we get the full variable length
            # Convert each value from string to int and then to bool,
            #  because string to bool doesn't work directly
            assignments = generate_assignment(len(variables))

            for assignment in assignments:
                # Zip our variables and assignment together as dictionary
                assignment_dict = dict(zip(variables, assignment))
                # Calculate the evaluation using our assignment
                evaluation = self.evaluate(assignment_dict)
                # Add the evaluation and assignment to our table
                table.append(assignment + [evaluation])
        else:
            variables = list(assignments[0].keys())

            for i, assignment in enumerate(assignments):
                evaluation = self.evaluate(assignment)
                table.append(list(assignments[i].values()) + [evaluation])

        if pretty:
            return pretty_tt(table, variables)
        else:
            full_str = ""
            for row in table:
                full_str += str(row) + "\n"

            return full_str

    def is_equivalent(self, other):
        # Naive implemntation, by just comparing the tt generated by get_tt
        # doesn't work if one formula has one or more variables more
        
        # So we grab the union of the variables of both formulas
        # and generate the truth tabel for that

        variables = self.get_variables().union(other.get_variables())
        assignments = generate_assignment(len(variables))
        # I feel like here I should have to cast every variables element to string
        # but Python is fine with this, so why not
        assignments = [dict(zip(variables, assignment)) for assignment in assignments]

        # We could just compare the entire table, but I think it is better to just compare the resulting 
        # evaluations, since the rest should per definition already be the same
        
        tt1 = self.get_tt(assignments=assignments)
        tt2 = self.get_tt(assignments=assignments)

        for i in  range(2** len(variables)):
            if tt1[i][-1] != tt2[i][-1]:
                return False

        return True


class Variable(Formula):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.to_string()

    def to_string(self):
        """Returns the variable as a readable string

        Returns:
            str: variable
        """
        return self.name

    def evaluate(self, d):
        """Returns the assignment of a variable

        Args:
            d (dict): dictionary with the assigments for the varibales

        Returns:
            bool: assigment for the variable true or false
        """
        return d[self.name]

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            Set[str]: The variables as a set
        """
        return {self.name}


class Implies(Formula):
    def __init__(self, form1, form2):
        self.form1 = form1
        self.form2 = form2

    def __str__(self):
        return self.to_string()

    def to_string(self):
        """Returns the formula to the left of the implies arrow

        Returns:
            str: The formula on the left side of the implies arrow
        """
        return f"({self.form1} -> {self.form2})"

    def get_left(self):
        """Returns the formula to the left of the implies arrow (->)

        Returns:
            Formula: The formula on the left side of the implies arrow
        """
        return self.form1

    def get_right(self):
        """Returns the formula to the right oft the implies arrow (->)

        Returns:
            Formula: The formula on the right side of the implies arrow
        """
        return self.form2

    def evaluate(self, d):
        """Evaluates the boolean result of a logical formula,
            containing an implies (->) operation

        Args:
            d (dict): dictionary with the assigments for the varibales

        Returns:
            bool: The result of the formula. true or false
        """
        return not self.form1.evaluate(d) or self.form2.evaluate(d)

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            Set[str]: The variables as a set
        """
        return self.form1.get_variables().union(self.form2.get_variables())


class Not(Formula):
    def __init__(self, form):
        self.form = form

    def __str__(self):
        return self.to_string()

    def to_string(self):
        """Returns the formula with an "not" symbole

        Returns:
            str: The formula with an "not" symbole
        """
        return f"~({self.form})"

    def get_form(self):
        """Returns the formula without the negation

        Returns:
            Formula: The formula without negation
        """
        return self.form

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            Set[str]: The variables as a set
        """
        return self.form.get_variables()

    def evaluate(self, d):
        """Returns the negation of the given formula

        Args:
            d (dict): dictionary with the assigments for the varibales

        Returns:
            bool: negation of the formula
        """
        return not self.form.evaluate(d)


class And(Formula):
    def __init__(self, form1, form2):
        self.form1 = form1
        self.form2 = form2

    def __str__(self):
        return self.to_string()

    def to_string(self):
        return f"({self.form1} /\\ {self.form2})"

    def get_left(self):
        return self.form1

    def get_right(self):
        return self.form2

    def evaluate(self, d):
        """Evaluates the boolean result of a logical formula containin_g
            an And (/\\) operation

        Args:
            d (dict): dictionary with the assigments for the varibales

        Returns:
            bool: The result of the formula. true or false
        """
        return self.form1.evaluate(d) and self.form2.evaluate(d)

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            Set[str]: The variables as a set
        """
        return self.form1.get_variables().union(self.form2.get_variables())


class Or(Formula):
    def __init__(self, form1, form2):
        self.form1 = form1
        self.form2 = form2

    def __str__(self):
        return self.to_string()

    def to_string(self):
        return f"({self.form1} \\/ {self.form2})"

    def get_left(self):
        return self.form1

    def get_right(self):
        return self.form2

    def evaluate(self, d):
        """Evaluates the boolean result of a logical formula,
            containing an Or (\\/) operation

        Args:
            d (dict): dictionary with the assigments for the varibales

        Returns:
            bool: The result of the formula. true or false
        """
        return self.form1.evaluate(d) or self.form2.evaluate(d)

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            Set[str]: The variables as a set
        """
        return self.form1.get_variables().union(self.form2.get_variables())


class Proof:
    def __init__(self, assumptions, proof):
        self.assumptions = assumptions
        self.proof = proof

    def verify(self):
        """Returns an true if the proof is correct and
            false if its not correct

        Returns:
            bool: true if its correct and false if its not correct
        """
        pass


def test_case_1():
    # This test case should return False
    a = Variable("a")
    b = Variable("b")
    test = Proof([a, b], [a, b, Implies(a, b)])
    return test.verify()


def test_case_2():
    # This test case should return True
    a = Variable("a")
    b = Variable("b")
    assumptions = [a, b]
    proof = [a, b, Implies(a, Implies(b, a))]
    test = Proof(assumptions, proof)
    return test.verify()


print("Test case1: ", test_case_1())
print("Test case2: ", test_case_2())

a, b, c = Variable("afoobar"), Variable("bc"), Variable("cd")
print(Implies(a, And(Not(b), c)).get_tt(pretty=True))


a, b, c = Variable("afoobar"), Variable("bc"), Variable("cd")
variable_list = [str(a), str(b), str(c)]
assignments = generate_assignment(3)
assignments = [dict(zip(variable_list, assignment)) for assignment in assignments]
formula1 = Or(a, b)
print(formula1)
print(formula1.get_tt(pretty=True, assignments=assignments))
formula2 = Or(a, Or(b, And(c, Not(c))))
print(formula2)
print(Or(a, Or(b, And(c, Not(c)))).get_tt(pretty=True, assignments=assignments))

print(formula1.is_equivalent(formula2))
