class Formula:
	def __init__(self):
		pass

	def modus_ponens(self,a,b):
		pass

	def is_axiom1(self):
		pass
		
	def is_axiom2(self):
		pass
		
	def is_axiom3(self):
		pass
		
	def is_axiom(self):
		pass
		
	def is_equal(self, formula):
		pass


class Variable(Formula):
	def __init__(self,name):
		self.name = name
		
	def __str__(self):
		return self.to_string()
	
	def to_string(self):
		pass
		

class Implies(Formula):
	def __init__(self,form1, form2):
		self.form1 = form1
		self.form2 = form2
		
	def __str__(self):
		return self.to_string()
	
	def to_string(self):
		pass
		
	def get_left(self):
		pass
		
	def get_right(self):
		pass
	
				
class Not(Formula):
	def __init__(self, form):
		self.form = form
	
	def __str__(self):
		return self.to_string()
	
	def to_string(self):
		pass
	
	def get_form(self):
		pass


class Proof:
	def __init__(self, assumptions, proof):
		self.assumptions = assumptions
		self.proof = proof
		
	def verify(self):
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
