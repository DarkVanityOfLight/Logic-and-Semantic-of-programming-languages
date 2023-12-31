
def pretty_tt(table, variables):
    """Pretty print the truth table

        Args:
            table ([][bool]): The truth table values
            variables ([str]): The variables that appear in the formula

        Returns:
            (str): The table in a pretty human readable format
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
    """Generate truth table assignments based on number of variables

    Args:
        size (int): The number of variables to generate for

    Returns:
        (List[][bool]): The truth table assignments, per row
    """

    # Initialize an empty list to store assignments
    assignments = []

    # Count up to  2**size
    for i in range(2 ** size):
        # Convert the number to binary and remove the '0b' prefix
        binary_representation = bin(i)[2:]

        # Zero-fill the binary representation to match the specified size
        binary_representation = binary_representation.zfill(size)

        # Convert each character in the binary representation
        # to a boolean value
        assignment = [bool(int(bit)) for bit in binary_representation]

        # Add the assignment to the list
        assignments.append(assignment)

    return assignments


class Formula:
    def __init__(self):
        pass

    def modus_ponens(self, a, b):
        """
        Check if we can derive b from this
        and the assumption a using modus ponens

        Args:
            a (Formula): The left-hand assumption.
            b (Formula): The thing we want to derive

        Returns:
            (bool): Can b be derived from this formula and the assumption a

        Raises:
            ValueError: If the provided implication is not of the form A -> B
                        or if the left-hand side of the implication does not
                        match the assumption.
        """

        # If this isn't an Implication(which shouldn't happen in a proof,
        # but better be save then sorry)
        if isinstance(self, Implies):
            # Check that our assumption matches the antecedent proposition
            if self.get_left().is_equal(a):
                # Chat that our consequent proposition matches
                # the wanted proposition
                return self.get_right().is_equal(b)
            else:
                return False
        else:
            raise ValueError(f"{self} is not an implication")

    def is_axiom1(self):
        """Checks if the given formula is constructed using Axiom 1

        The Axiom is:
        A -> (B -> A)

        Returns:
            (bool): True if the formula is constructed with Axiom 1,
                False otherwise
        """

        # We always have to check that our operator is
        # actually a Implication and not a And, Or, Not Operator

        if not isinstance(self, Implies):
            return False

        # Get first A
        A = self.get_left()
        B_implies_A = self.get_right()

        # Check the right hand, should be of form B -> A
        if not isinstance(B_implies_A, Implies):
            return False

        # B = righthand.get_left()

        # Check that we have the same A as on the left side
        return B_implies_A.get_right().is_equal(A)

    def is_axiom2(self):
        """Checks if the given formula is constructed using Axiom 2

        The Axiom is:
        (A -> (B -> C)) -> ((A -> B) -> (A -> C))

        Returns:
            (bool): True if the formula is constructed with Axiom 2,
                False otherwise
        """

        # We always have to check that our operator is
        # actually a Implication and not a And, Or, Not Operator

        if not isinstance(self, Implies):
            return False

        # left hand (A -> (B -> C))
        A_implies_B_implies_C = self.get_left()

        # Unfold left side (A -> (B -> C))
        if not isinstance(A_implies_B_implies_C, Implies):
            return False

        A = A_implies_B_implies_C.get_left()

        B_implies_C = A_implies_B_implies_C.get_left()

        if not isinstance(B_implies_C, Implies):
            return False

        B = B_implies_C.get_left()
        C = B_implies_C.get_right()

        # -----------------------------

        # right hand ((A -> B) -> (A -> C))
        A_implies_B_implies_A_implies_C = self.get_right()

        # Unfold right hand ((A -> B) -> (A -> C))
        if not isinstance(A_implies_B_implies_A_implies_C, Implies):
            return False

        A_implies_B = A_implies_B_implies_A_implies_C.get_left()
        A_implies_C = A_implies_B_implies_A_implies_C.get_right()

        # Unfold A -> B
        if not isinstance(A_implies_B, Implies):
            return False

        # Check that we have the same A and B here
        if not A_implies_B.get_left().is_equal(A) or\
                not A_implies_B.get_right().is_equal(B):
            return False

        # Unfold A -> C
        if not isinstance(A_implies_C, Implies):
            return False

        # Check that we have the same A and C here
        if not A_implies_C.get_left().is_equal(A) or\
                not A_implies_C.get_right().is_equal(C):
            return False

        return True

    def is_axiom3(self):
        """Checks if the given formula is constructed using Axiom 3

        The Axiom is:
        (~A -> ~B) -> (B -> A)

        Returns:
            (bool): True if the formula is constructed with Axiom 3,
                False otherwise
        """

        # We always have to check that our operator is
        # actually a Implication and not a And or Or Operator

        if not isinstance(self, Implies):
            return False

        # left hand
        not_A_implies_not_B = self.get_left()
        if not isinstance(not_A_implies_not_B, Implies):
            return False

        not_A = not_A_implies_not_B.get_left()
        not_B = not_A_implies_not_B.get_right()

        if not isinstance(not_A, Not):
            return False

        A = not_A.get_form()

        if isinstance(not_B, Not):
            return False

        B = not_B.get_form()

        # right hand
        B_implies_A = self.get_right()

        if not isinstance(B_implies_A, Implies):
            return False

        return B_implies_A.get_left().is_equal(B) and\
            B_implies_A.get_right().is_equal(A)

    def is_axiom(self):
        """Check if the formula is any Axiom

        Returns:
            (bool): True if it is any Axiom else False
        """

        return self.is_axiom1() or self.is_axiom2() or self.is_axiom3()

    def get_tt(self, pretty=True, assignments=None):
        """
        Generate a truth tabel for the formula,
        only pretty print will return a string, if
        pretty print is not set, the table itself, a list of list,
        each representing the according row in the table, the last
        value per list will be the evaluation for that assignment

        Args:
            pretty_print = True (bool): return a pretty table string

            assignments = None (List[Dict[str][bool]]):
                A list of assignments to evaluate,
                only to be used for equivalenz checking.

        Returns:
            ([][bool] | str): The table or a pretty string
                representing the table

        """

        # List of [variable_assignments | truth value]
        table = []

        # If no assignments are given we generate one
        if assignments is None:
            # We differentiate between the variable object and it s name
            v = self.get_variables()
            v = sorted(v, key=lambda x: x.name)
            # In the rest we only work with the names
            variables = [variable.name for variable in v]

            # Generate our assignments
            assignments = generate_assignment(len(variables))

            # Evaluate every assignment
            for assignment in assignments:

                # Zip our variable names and assignment together as dictionary
                assignment_dict = dict(zip(variables, assignment))
                # Calculate the evaluation using our assignment
                evaluation = self.evaluate(assignment_dict)
                # Add the evaluation and assignment to our table
                table.append(assignment + [evaluation])

        # An assignment is already given, evaluate those
        else:
            # First we get all variable names
            variables = list(assignments[0].keys())

            # We evaluate every assignment
            for i, assignment in enumerate(assignments):
                evaluation = self.evaluate(assignment)
                # Append the assignment and the evaluation
                table.append(list(assignments[i].values()) + [evaluation])

        # Pretty print the table if we are supposed to
        # else we just return our table
        if pretty:
            return pretty_tt(table, variables)
        else:
            return table

    def is_equivalent(self, other):
        """
        Check if this formula is logical equivalent to another.

        Args:
            other(Formula): The formula to check against

        Returns:
           (bool) If the two formulas are equivalent
        """
        # Naive implemntation, by just comparing the tt generated by get_tt
        # doesn't work if one formula has one or more variables more

        # So we grab the union of the variables of both formulas
        # and generate the truth tabel for that

        variables = self.get_variables().union(other.get_variables())
        variables = sorted(variables, key=lambda x: x.name)
        variable_names = [v.name for v in variables]
        assignments = generate_assignment(len(variables))
        # I feel like here I should have to cast every variables
        # element to string but Python is fine with this, so why not
        assignments = [dict(zip(variable_names, assignment))
                       for assignment in assignments]

        # Kinda ugly but what can you do
        return (self.get_tt(pretty=False, assignments=assignments) ==
                other.get_tt(pretty=False, assignments=assignments))

    def get_DNF(self):
        """
        Get the formula as Disjunctive Normal Form(DNF), calculated by reading
        the true entries from a truth table.

        Returns:
            (Formula): A equivalent formula in DNF
        """

        # Get the variables and the truth table
        variables = list(self.get_variables())
        # Get tt sorts our variables, so we have to sort them too
        variables = sorted(variables, key=lambda x: x.name)
        tt = self.get_tt(pretty=False)

        def conjunct(exp):
            """
            Create a conjunted formula from a list of variables
            Args:
                exp (List[Formula]): The list of variables to conjunct
            Returns:
                (Formula): The conjuncted formula
            """
            if len(exp) == 1:
                return exp[0]
            else:
                return And(exp[0], conjunct(exp[1:]))

        def disjunct(exp):
            """
            Create a disjunct formula from a list of variables
            Args:
                exp(List[Formula]): The list of variables to disjunct
            Returns:
                (Formula) The disjunct formula
            """
            if len(exp) == 1:
                return exp[0]
            else:
                return Or(exp[0], disjunct(exp[1:]))

        conjunctions = []
        # For every row in the truth table
        for row in tt:
            # If the evaluation was true
            if row[-1]:
                # Create a conjunction of the appearing variables
                con_variables = []
                for i, entry in enumerate(row[:-1]):
                    # If the variable appears as false add it as negated
                    if entry:
                        con_variables.append(variables[i])
                    else:
                        con_variables.append(Not(variables[i]))

                conjunctions.append(conjunct(con_variables))

        return disjunct(conjunctions)


class Variable(Formula):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.to_string()

    def to_string(self):
        """Returns the variable as a readable string

        Returns:
            (str): variable
        """
        return self.name

    def evaluate(self, d):
        """Returns the assignment of a variable

        Args:
            d (dict[str][bool]): dictionary with the assigments
                for the varibales

        Returns:
            (bool): assigment for the variable True or False
        """
        return d[self.name]

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            (Set[str]): The variables as a set
        """
        return {self}

    def get_NNF(self):
        """Get the formula as Negated normal form(NNF)

        Returns:
            (Formula): The formula as NNF
        """
        return self

    def is_equal(self, other):
        """Checks if one formula is equal to another

        Args:
            other (Formula): The second formula

        Returns:
            (bool): True if the formulas are equal, False otherwise
        """
        if isinstance(other, Variable):
            # a = a
            return self.name == other.name
        else:
            return False


class Implies(Formula):
    def __init__(self, form1, form2):
        self.form1 = form1
        self.form2 = form2

    def __str__(self):
        return self.to_string()

    def to_string(self):
        """
        Returns the formula in human readable form,
        the implies symbol is ->

        Returns:
            (str): The formula in human readable form
        """
        return f"({self.get_left()} -> {self.get_right()})"

    def get_left(self):
        """Returns the formula to the left of the implies arrow ( -> )

        Returns:
            (Formula): The formula on the left side of the implies arrow
        """
        return self.form1

    def get_right(self):
        """Returns the formula to the right oft the implies arrow ( -> )

        Returns:
            (Formula): The formula on the right side of the implies arrow
        """
        return self.form2

    def evaluate(self, d):
        """Evaluates the boolean result of a logical formula,
            containing an implies ( -> ) operation

        Args:
            d(dict): dictionary with the assigments for the varibales

        Returns:
            (bool): The result of the formula. true or false
        """
        return not self.get_left().evaluate(d) or self.get_right().evaluate(d)

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            (Set[str]): The variables as a set
        """
        return self.get_left().get_variables().union(
            self.get_right().get_variables())

    def get_NNF(self):
        """Get the formula as Negated normal form(NNF)

        Returns:
            (Formula): The formula as NNF
        """
        # Unfold implies
        return Or(Not(self.get_left()).get_NNF(), self.get_right().get_NNF())

    def is_equal(self, other):
        """Checks if one formula is equal to another

        Args:
            other (Formula): The second formula

        Returns:
            (bool): True if the formulas are equal, False otherwise
        """
        if isinstance(other, Implies):
            # A -> B = A -> B
            return self.get_left().is_equal(other.get_left()) and \
                self.get_right().is_equal(other.get_right())
        else:
            return False


class Not(Formula):
    def __init__(self, form):
        self.form = form

    def __str__(self):
        return self.to_string()

    def to_string(self):
        """Returns the formula in human readable form, the not symbol is ~

        Returns:
            (str): The formula as a string
        """
        return f"~({self.get_form()})"

    def get_form(self):
        """Returns the formula without the negation

        Returns:
            (Formula): The formula without negation
        """
        return self.form

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            (Set[str]): The variables as a set
        """
        return self.get_form().get_variables()

    def evaluate(self, d):
        """Returns the negation of the given formula

        Args:
            d (dict[str][bool]): dictionary with the
                assigments for the varibales

        Returns:
            (bool): negation of the formula
        """
        return not self.get_form().evaluate(d)

    def get_NNF(self):
        """Get the formula as Negated normal form(NNF)

        Returns:
            (Formula): The formula as NNF
        """

        # Remove double negation
        if isinstance(self.get_form(), Not):
            return self.get_form().get_form().get_NNF()
        # Unfold implies
        elif isinstance(self.get_form(), Implies):
            return And(self.get_form().get_left().get_NNF(),
                       Not(self.get_form().get_right()).get_NNF())
        # De Morgan for And
        elif isinstance(self.get_form(), And):
            return Or(Not(self.get_form().get_left()).get_NNF(),
                      Not(self.get_form().get_right()).get_NNF())
        # De Morgan for Or
        elif isinstance(self.get_form(), Or):
            return And(Not(self.get_form().get_left()).get_NNF(),
                       Not(self.get_form().get_right()).get_NNF())
        # Variable just passes
        elif isinstance(self.get_form(), Variable):
            return Not(self.get_form())

        # Something didn't get implemented yet
        else:
            raise "Unreachable"

    def is_equal(self, other):
        """Checks if one formula is equal to another

        Args:
            other (Formula): The second formula

        Returns:
            (bool): True if the formulas are equal, False otherwise
        """
        # ~A = ~A
        if isinstance(other, Not):
            return self.get_form().is_equal(other.get_form())
        else:
            return False


class And(Formula):
    def __init__(self, form1, form2):
        self.form1 = form1
        self.form2 = form2

    def __str__(self):
        return self.to_string()

    def to_string(self):
        """Return the formula in human readable form, and is represented by /\\

        Returns:
            (str): The formula as human readable string
        """
        return f"({self.get_left()} /\\ {self.get_right()})"

    def get_left(self):
        """Returns the formula to the left of the and symbol (/\\)

        Returns:
            (Formula): The formula on the left side of the and symbol
        """
        return self.form1

    def get_right(self):
        """Returns the formula to the right of the and symbol (/\\)

        Returns:
            (Formula): The formula on the right side of the and symbol
        """
        return self.form2

    def evaluate(self, d):
        """Evaluates the boolean result of a logical formula containin_g
            an And (/\\) operation

        Args:
            d (dict[str][bool]): dictionary with the
                assigments for the varibales

        Returns:
            (bool): The result of the formula. true or false
        """
        return self.get_left().evaluate(d) and self.get_right().evaluate(d)

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            (Set[str]): The variables as a set
        """
        return self.get_left().get_variables().union(
            self.get_right().get_variables())

    def get_NNF(self):
        """Get the formula as Negated normal form(NNF)

        Returns:
            (Formula): The formula as NNF
        """
        return And(self.get_left().get_NNF(), self.get_right().get_NNF())

    def is_equal(self, other):
        """Checks if one formula is equal to another

        Args:
            other (Formula): The second formula

        Returns:
            (bool): True if the formulas are equal, False otherwise
        """
        if isinstance(other, And):
            # A /\ B = A /\ B
            # A /\ B = B /\ A
            return \
                (self.get_left().is_equal(other.get_left())
                 and self.get_right().is_equal(other.get_right())) or\
                (self.get_right().is_equal(other.get_left())
                 and self.get_left().is_equal(other.get_right()))
        else:
            return False


class Or(Formula):
    def __init__(self, form1, form2):
        self.form1 = form1
        self.form2 = form2

    def __str__(self):
        return self.to_string()

    def to_string(self):
        """Return the formula in human readable form, or is represented by \\/
        Returns:
            (str): The formula as human readable string
        """
        return f"({self.get_left()} \\/ {self.get_right()})"

    def get_left(self):
        """Returns the formula to the left of the or symbol(\\/)

        Returns:
            (Formula): The formula on the left side of the or symbol
        """
        return self.form1

    def get_right(self):
        """Returns the formula to the right of the or symbol(\\/)

        Returns:
            (Formula): The formula on the left side of the implies arrow
        """
        return self.form2

    def evaluate(self, d):
        """Evaluates the boolean result of a logical formula,
            containing an Or(\\/) operation

        Args:
            d (dict[str][bool]): dictionary with the
                assigments for the varibales

        Returns:
            (bool): The result of the formula. true or false
        """
        return self.get_left().evaluate(d) or self.get_right().evaluate(d)

    def get_variables(self):
        """Return all variables in the formula

        Returns:
            (Set[str]): The variables as a set
        """
        return self.get_left().get_variables().union(
            self.get_right().get_variables())

    def get_NNF(self):
        """Get the formula as Negated normal form(NNF)

        Returns:
            (Formula): The formula as NNF
        """
        return Or(self.get_left().get_NNF(), self.get_right().get_NNF())

    def is_equal(self, other):
        """Checks if one formula is equal to another

        Args:
            other (Formula): The second formula

        Returns:
            (bool): True if the formulas are equal, False otherwise
        """
        if isinstance(other, Or):
            # a \/ b = a \/ b
            # a \/ b = b \/ a
            return \
                (self.get_left().is_equal(other.get_left()) and
                 self.get_right().is_equal(other.get_right()))\
                or (self.get_right().is_equal(other.get_left()) and
                    self.get_left().is_equal(other.get_right()))
        else:
            return False


class Proof:
    def __init__(self, assumptions, proof):
        self.assumptions = assumptions
        self.proof = proof

    def can_be_derived(self, phii, i):
        """
        Check if the formula phii can be derived using modus ponens
        and the formulas phi0...phij with j<i

        Args:
            phii (Formula): The formula to derive
            i (int): The position of phii in our proof
                (aka until where the proof is already correct)
        Returns:
            (bool): True if phii can be derived using the assumptions
                and propositions till i
        """

        # We check if we can derive the proof from
        # a proposition in either our assumptions
        # or another already proofen proposition
        for phij in self.proof[:i]:
            # To use modus ponens we obviously have to have an implication
            # and not a Not
            if (isinstance(phij, Implies)):

                # Try deducing using all assumptions
                for assumption in self.assumptions:
                    # Check if we can deduce phii using the assumption
                    if phij.modus_ponens(assumption, phii):
                        return True
                    else:
                        continue

                # Try deducing using all proofen propositions till i
                for phik in self.proof[:i]:
                    # Check if we can deduce phii using the proofen
                    # proposition phik
                    if phij.modus_ponens(phik, phii):
                        return True
                    else:
                        continue

        # If we can't deduce phii from any already proofen
        # proposition or assumption, then we cannot deduce phii
        return False

    def verify(self):
        """
        Returns True if the proof is correct and
        False if its not correct

        Returns:
            (bool): True if the proof is correct else False
        """

        # Check that every propositon in our proof can be derived
        for i, phii in enumerate(self.proof):

            # From either an axiom
            if phii.is_axiom():
                continue

            # Or if we can derive it using modus ponens from other propositions
            elif self.can_be_derived(phii, i):
                continue
            else:
                return False

        # An empty proof is correct I think
        return True


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


print("Test truth table")
a, b, c = Variable("afoobar"), Variable("bc"), Variable("cd")
print(Implies(a, And(Not(b), c)).get_tt(pretty=True))


def test_case_equivalenz():
    # This test case should return True
    a, b, c = Variable("afoobar"), Variable("bc"), Variable("cd")
    variable_list = [a.name, b.name, c.name]
    assignments = generate_assignment(3)
    assignments = [dict(zip(variable_list, assignment))
                   for assignment in assignments]
    formula1 = Or(a, b)
    formula2 = Or(a, Or(b, And(c, Not(c))))
    return formula1.is_equivalent(formula2)


def test_case_NNF():
    # This test case should return True
    a, b, c = Variable("a"), Variable("b"), Variable("c")
    formula = Not(Implies(a, Or(b, And(c, Not(c)))))
    return formula.get_NNF().is_equivalent(formula)


def test_case_DNF():
    # This test case should return True
    a, b, c = Variable("a"), Variable("b"), Variable("c")
    formula = Not(Implies(a, Or(b, And(c, Not(c)))))
    return formula.get_DNF().is_equivalent(formula)


def test_case_is_equal_AND_1():
    # This test case should return True
    formula1 = And(a, b)
    formula2 = And(b, a)
    return formula1.is_equal(formula2)


def test_case_is_equal_AND_2():
    # This test case should return True
    formula1 = And(a, b)
    formula2 = Not(And(a, b))
    return not (formula1.is_equal(formula2))


def test_case_is_equal_Or_1():
    # This test case should return True
    a, b = Variable("a"), Variable("b")
    formula1 = Or(a, b)
    formula2 = Or(b, a)
    return formula1.is_equal(formula2)


def test_case_is_equal_Or_2():
    # This test case should return True
    a, b = Variable("a"), Variable("b")
    formula1 = Or(a, b)
    formula2 = Not(Or(a, b))
    return not (formula1.is_equal(formula2))


def test_case_is_equal_Implies_1():
    # This test case should return True
    a, b = Variable("a"), Variable("b")
    formula1 = Implies(a, b)
    formula2 = Implies(a, b)
    return formula1.is_equal(formula2)


def test_case_is_equal_Implies_2():
    # This test case should return True
    a, b = Variable("a"), Variable("b")
    formula1 = Implies(a, b)
    formula2 = Not(Implies(a, b))
    return not (formula1.is_equal(formula2))


def test_case_is_equal_Not_1():
    # This test case should return True
    a = Variable("a")
    formula1 = Not(a)
    formula2 = Not(a)
    return formula1.is_equal(formula2)


def test_case_is_equal_Not_2():
    # This test case should return True
    a = Variable("a")
    formula1 = Not(a)
    formula2 = a
    return not (formula1.is_equal(formula2))


def test_case_is_equal_Base_1():
    # This test case should return True
    a = Variable("a")
    formula1 = a
    formula2 = a
    return formula1.is_equal(formula2)


def test_case_is_equal_Base_2():
    # This test case should return True
    a = Variable("a")
    formula1 = a
    formula2 = Not(a)
    return not (formula1.is_equal(formula2))


print("Test case1: ", test_case_1())
print("Test case2: ", test_case_2())
print("test case equivalenz: ", test_case_equivalenz())
print("Test case NNF: ", test_case_NNF())
print("Test case DNF: ", test_case_DNF())
print("Test case is_equal AND 1: ", test_case_is_equal_AND_1())
print("Test case is_equal AND 2: ", test_case_is_equal_AND_2())
print("Test case is_equal Or 1: ", test_case_is_equal_Or_1())
print("Test case is_equal Or 2: ", test_case_is_equal_Or_2())
print("Test case is_equal Implies 1: ", test_case_is_equal_Implies_1())
print("Test case is_equal Implies 2: ", test_case_is_equal_Implies_2())
print("Test case is_equal Not 1: ", test_case_is_equal_Not_1())
print("Test case is_equal Not 2: ", test_case_is_equal_Not_2())
print("Test case is_equal Base 1: ", test_case_is_equal_Base_1())
print("Test case is_equal Base 2: ", test_case_is_equal_Base_2())
