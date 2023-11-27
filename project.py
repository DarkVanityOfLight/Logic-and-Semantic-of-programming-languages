class Formula:
	def __init__(self):
		pass

	def modus_ponens(self,a,b):
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
			bool: True if the formula is constructed with Axiom 1, False otherwise
		"""
		pass
		
	def is_axiom2(self):
		"""Checks if the given formula is constructed using Axiom 2

		Returns:
			bool: True if the formula is constructed with Axiom 2, False otherwise
		"""
		pass
		
	def is_axiom3(self):
		"""Checks if the given formula is constructed using Axiom 3

		Returns:
			bool: True if the formula is constructed with Axiom 3, False otherwise
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


class Variable(Formula):
	def __init__(self,name):
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
	def __init__(self,form1, form2):
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
		"""Evaluates the boolean result of a logical formula containing an implies (->) operation

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
	def __init__(self,form1, form2):
		self.form1 = form1
		self.form2 = form2
		
	def __str__(self):
		return self.to_string()
	
	def to_string(self):
		return f"({self.form1} /\ {self.form2})"
		
	def get_left(self):
		return self.form1
		
	def get_right(self):
		return self.form2
	
	def evaluate(self, d):
		"""Evaluates the boolean result of a logical formula containing an And (/\) operation

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
	def __init__(self,form1, form2):
		self.form1 = form1
		self.form2 = form2
		
	def __str__(self):
		return self.to_string()
	
	def to_string(self):
		return f"({self.form1} \/ {self.form2})"
		
	def get_left(self):
		return self.form1
		
	def get_right(self):
		return self.form2
	
	def evaluate(self, d):
		"""Evaluates the boolean result of a logical formula containing an Or (\/) operation

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
		"""Returns an true if the proof is correct and an false if its not correct

		Returns:
			bool: true if its correct and false if its not correct
		"""
		pass


def test_case_1():
	# This test case should return False
	a = Variable("a")
	b = Variable("b")
	test = Proof([a,b],[a,b, Implies(a,b)])
	return test.verify()

def test_case_2():
	# This test case should return True	
	a = Variable("a")
	b = Variable("b")
	assumptions = [a,b]
	proof = [a,b, Implies(a,Implies(b,a))]
	test = Proof(assumptions,proof)
	return test.verify()

print("Test case1: ", test_case_1())
print("Test case2: ", test_case_2())
