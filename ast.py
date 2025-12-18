'''
Ackermann Set Theory
'''

class AstClass:
    def __init__(self):
        pass

class AstSet:
    def __init__(self):
        pass


'''
case complement:
original USR r
r' = C(r)

want to check if s matches r' in nondeterministic linear space
can arbitrarily pick valuation (variable assignment) assume its correct,
WTS that this assignment is bounded in length
kn for some fixed constant k picked before s is picked.

ideas:

pick some USR t s.t. t\subseteq C(r)

This language is consistent, so it has a countable model, i.e. it is satisfiable in
a structure whose domain is either finite or countably infinite


assume that it is NOT arbitrary length, then you can pick some max length m for variable
assignments to string variables w where everything above length will evaluate to something
not in the USR r'


'''