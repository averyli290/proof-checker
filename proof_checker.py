'''
Docstring for proof_checker

syntax ideas:

use boxes from section 2.1 of https://plato.stanford.edu/entries/natural-deduction/#Intr,
effectively natural deduction

on the right is either ASSUMPTION
or it is a rule of TFL or FOL with lines specifying what to reference

The typically rules of inference include these:

∧-Introduction: a conjunction may be inferred from its two conjuncts
∧-Elimination: a conjunct may be inferred from a conjunction.
∨-Introduction: a disjunction may be inferred from either disjunct.
→-Elimination: B may be inferred from the two premises A and (A→B) (MP)
¬-Elimination: an arbitrary formula, B, may be inferred from a pair of contradictory premises, A and ¬A.


There are also what Jaśkowski calls rules of supposition, in which conclusions are inferred, not from earlier formulas, but from the presence of one or more subproofs of a specified kind. Typically (described in Fitch-style terminology) these include:
This is done when the ASSUMPTION is written in a subproof, and then there is following line in the subproof.
The ASSUMPTIONS are at the top of the subproofs

→-Introduction: (A → B) may be asserted after a subproof having A as its hypothesis and and B as a line.
∨-Elimination: an arbitrary formula C may be asserted after three items: a disjunction, (A ∨ B), a subproof,
                having A as its hypothesis, with C as a line, and a subproof, having B as its hypothesis, with C as a line.
¬-Introduction: a negation, ¬A , may be asserted after a subproof, with A as its hypothesis, containing a pair
                of contradictory formulas, B and ¬B , as lines.

'''


from enum import Enum

class Term:
    '''
    Every variable v_i is a term of L
        – Every constant symbol of L is a term of L
        – If f is an n-place function symbol of L, and t1, ..., tn areterms of L, then f(t1,..., tn) is a term of L (no function symbols yet)
        – Nothing else is a term of L.
    '''
    def __init__(self):
        pass

    def is_constant(self):
        return isinstance(self, Constant)

    def is_variable(self):
        return isinstance(self, Variable)

class Constant(Term):
    '''
    Depends on your language L, but for now there are no constants.
    '''
    def __init__(self, value):
        self.value = value
    
    def __repr__(self):
        return str(self.value)
    
    def __str__(self):
        return self.__repr__()

class Variable(Term):
    '''
    Depends on your language L, for now represented by v_0, v_1, ... with infinitely many indices
    '''
    def __init__(self, idx):
        self.idx = idx
    
    def __eq__(self, other_var):
        return self.idx == other_var.idx

    def __repr__(self):
        return f"v_{self.idx}"

    def __str__(self, ):
        return self.__repr__()

class Op(Enum):
    '''
    – The Propositional Connectives: →, ∧, ∨, ¬, ⊥
    – The Quantifiers: ∀, ∃
    – The Identity Predicate: =
    '''
    IMPLIES = 1
    AND = 2
    OR = 3
    NOT = 4
    BOTTOM = 5
    FORALL = 6
    EXISTS = 7
    EQ = 8
    
    def is_binary(op):
        return (op == Op.IMPLIES or 
                op == Op.AND or 
                op == Op.OR or 
                op == Op.EQ)

    def is_unary(op):
        return op == Op.NOT

    def is_quantifier(op):
        return op == Op.FORALL or op == Op.EXISTS

class Formula:
    '''
    We define the set of formulas Frm(L) of L inductively as follows:
        – ⊥ is an atomic formula.
        – If R is an n-place predicate letter of L, and t1, . . . , tn are terms of L, then R(t1, . . . , tn) is an atomic formula. (Skipping for now)
        – If t1 and t2 are terms of L (and = is in L) then = (t1, t2) is an atomic formula.
        – If A and B are formulas then:
        * ¬A is a formula
        * (A ∧ B) is a formula
        * (A ∨ B) is a formula
        * (A → B) is a formula
        – If A is a formula, and x is a variable then
        * ∃xA is a formula
        * ∀xA is a formula
        – Nothing else is a formula.
    '''
    def __init__(self, op=None, left=None, right=None, idx=-1):
        self.op = op
        self.left = left
        self.right = right
        self.idx = idx
        self.validate_formula()
    
    def validate_formula(self):
        '''
        Checks if formula is actually valid
            - e.g. if op is Op.AND, that self.left and self.right are both Formula
            - e.g. if op is Op.NOT, that self.left is a Formula and self.right is None
            - e.g. if op is Op.EXISTS, that self.left is a Variable and self.right is Formula
        '''
        is_valid = False
        if self.op is None:
            if self.idx > -1:
                is_valid = isinstance(self, FormulaVar) and self.op is None and self.left is None and self.right is None
            else:
                raise ValueError(f"Formula variable {self} must have an Formula Variable index > -1")
        else:
            if Op.is_binary(self.op):
                is_valid = isinstance(self.left, Formula) and isinstance(self.right, Formula)
            elif Op.is_unary(self.op):
                is_valid = isinstance(self.left, Formula) and self.right is None
            elif Op.is_quantifier(self.op):
                is_valid = isinstance(self.left, Variable) and isinstance(self.right, Formula)
            else:
                raise RuntimeError(f"Unknown type for operator value of with value {self.op}")

        try:
            assert(is_valid)
        except AssertionError:
            raise AssertionError(f"Formula of value {str(self)} is not a valid formula")
    
    def __eq__(self, other):
        '''
        Check if two formluas are the "same" for ¬-Elimination
        '''
        return ((self.op == other.op) and
                (self.left == other.left) and
                (self.right == other.right) and
                (self.idx == other.idx))
    
    def __str__(self):
        return f"{str(self.op)}({str(self.left)},{str(self.right)})"

class FormulaVar(Formula):
    '''
    Not to be confused with variables used in terms, which lie in the actual domain
    These are variables which themselves are formulas, which can be understood as 0-ary predicates if so desired
    This workaround is used mostly because this is a proof assistant and we want to be able to refernce arbitrary
    formulas
    '''
    def __init__(self, idx=0):
        super().__init__(op=None, left=None, right=None, idx=idx)
    
    def __eq__(self, other):
        '''
        Two variables are equal if they have the same index
        
        :param self: Description
        :param other: Description
        '''
        return self.idx == other.idx
    
    def __str__(self):
        return f"FormulaVar({self.idx})"

class Rule(Enum):
    '''
    Inference Rule
    ∧-Introduction: a conjunction may be inferred from its two conjuncts
    ∧-Elimination: a conjunct may be inferred from a conjunction.
    ∨-Introduction: a disjunction may be inferred from either disjunct.
    →-Elimination: B may be inferred from the two premises A and (A→B) (MP)
    ¬-Elimination: an arbitrary formula, B, may be inferred from a pair of contradictory premises, A and ¬A.

    Supposition Rules
    →-Introduction: (A → B) may be asserted after a subproof having A as its hypothesis and and B as a line.
    ∨-Elimination: an arbitrary formula C may be asserted after three items: a disjunction, (A ∨ B), a subproof,
                    having A as its hypothesis, with C as a line, and a subproof, having B as its hypothesis, with C as a line.
    ¬-Introduction: a negation, ¬A , may be asserted after a subproof, with A as its hypothesis, containing a pair
                    of contradictory formulas, B and ¬B , as lines.
    '''
    AND_INTR = 1
    AND_ELIM = 2
    OR_INTR = 3
    IMP_ELIM = 4
    NOT_ELIM = 5

    IMP_INTR = 6
    OR_ELIM = 7
    NOT_INTR = 8

class Proof:
    def __init__(self, hypotheses):
        self.hypotheses = hypotheses                        # List of initial assumptions
        self.proof_lines = [None] + hypotheses              # Proof in lines as list of Formulas, 1-indexed
    
    def deduce(self, formula, rule, line_num_a=-1, line_num_b=-1):
        '''
        Attempt to deduce the given formula given the rule supplied
        
        :param self: Description
        :param formula: Description
        :param rule: Description
        :param line_a: Description
        :param line_b: Description
        '''
        is_valid = False
        proof_line_a = None if line_num_a == -1 else self.proof_lines[line_num_a]
        proof_line_b = None if line_num_b == -1 else self.proof_lines[line_num_b]
        print(proof_line_a)
        print(proof_line_b)
        match rule:
            # Inference Rules
            case Rule.AND_INTR:
                if (formula.op == Op.AND and proof_line_a == formula.left and proof_line_b == formula.right):
                    is_valid = True
            case Rule.AND_ELIM:
                if (proof_line_a.op == Op.AND and (proof_line_a.left == formula or proof_line_a.right == formula)):
                    is_valid = True
            case Rule.OR_INTR:
                if (formula.op == Op.OR and proof_line_a == formula.left or proof_line_a == formula.right):
                    is_valid = True
            case Rule.IMP_ELIM:
                if (proof_line_b.op == Op.IMPLIES and proof_line_b.left == proof_line_a and proof_line_b.right == formula):
                    is_valid = True
            case Rule.NOT_ELIM:
                if proof_line_a == Formula(Op.NOT, proof_line_b) or proof_line_b == Formula(Op.NOT, proof_line_a):
                    is_valid = True

            # Supposition Rules
            case Rule.IMP_INTR:
                pass
            case Rule.OR_ELIM:
                pass
            case Rule.NOT_INT:
                pass
            case _:
                raise ValueError(f"Rule {rule} does not have a matching rule.")

        if is_valid:
            self.proof_lines.append(formula)
        else:
            raise AssertionError(f"Formula {formula} could not be deduced from the following lines:\n{proof_line_a}\n{proof_line_b}")





if __name__ == "__main__":
    # formula = Formula(Op.NOT, FormulaVar(1), FormulaVar(2))
    formula = Formula(Op.AND, FormulaVar(1), FormulaVar(2))
    p = Proof(hypotheses=[formula])
    p.deduce(formula=FormulaVar(1), rule=Rule.AND_ELIM, line_num_a=1)
    p.deduce(formula=Formula(Op.AND, FormulaVar(1), formula), rule=Rule.AND_INTR, line_num_a=2, line_num_b=1)
    # p.deduce(formula=Formula(Op.AND, FormulaVar(1), formula), rule=Rule.AND_INTR, line_num_a=1, line_num_b=2)