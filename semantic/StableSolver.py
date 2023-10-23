import z3

from utils import Argument
from . import SemanticHelper


class StableSolver:
    def __init__(self, AF: dict[str, Argument.Argument]) -> None:
        '''
        @AF ->        Argumentation Framework
        '''
        self.AF = AF
        self.solution = list()
        self.solver = z3.Solver()
        self.setRulesStable()



    def setRulesStable(self):
        ''' Sets the rules for stable check. Formula is in the Readme'''
        
        cf_clause = True # conflict free part
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():

            if not a.is_singleton:
                continue
            
            # check if b exists
            if len(a.defends) == 0:
                continue

            cf_clause_inner = True

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if b.is_singleton:
                    cf_clause_inner = z3.And(cf_clause_inner, z3.Not(z3.And(a.z3_value, b.z3_value)))

            cf_clause = z3.And(cf_clause, cf_clause_inner)

        
        middle_clause = True # middle part of the formula
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():
            # check if b exists
            if len(a.defends) == 0:
                self.solver.add(z3.Or(a.z3_value, False))
                continue
            
            middle_clause_inner = False

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                middle_clause_inner = z3.Or(middle_clause_inner, b.z3_value)


            middle_clause = z3.And(middle_clause, z3.Or(a.z3_value, middle_clause_inner))

        
        right_clause = True # right part of the formula
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():

            # check if b exists
            if len(a.defends) == 0:
                self.solver.add(z3.Implies(z3.And(a.z3_value, True), True))
                continue

            right_clause_inner = True

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                right_clause_inner = z3.And(right_clause_inner, z3.Not(b.z3_value))

            
            right_right_clause = True
            # get c:(a, c)∈R
            c: Argument.Argument
            for c in a.attacks:
                c = self.AF[c]

                if not c.is_singleton:
                    continue

                right_right_clause = z3.And(right_right_clause, z3.Not(c.z3_value))

            right_clause = z3.And(right_clause, z3.Implies(z3.And(a.z3_value, right_clause_inner), right_right_clause))

        # Add the final clause to the solver 
        self.solver.add(z3.And(z3.And(cf_clause, middle_clause), right_clause))
        




    def computeSets(self, solution_amount: int=-1, algorithm: str="BFS"):
        return SemanticHelper.computeSets(self, solution_amount, algorithm)


    def verifySet(self, verify_set: list):
        return SemanticHelper.verifySet(self, verify_set)